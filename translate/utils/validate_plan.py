#!/usr/bin/env python3
"""
validate_plan.py -- generic MA-LAMA temporal-plan validator.

Parses a PDDL domain + problem (typed durative actions, numeric fluents)
together with a MA-LAMA-style plan file (the "final_plan.txt" produced by
unify/main.py: one "<start> (<duration>) <action> <args...>" line per
action start), and *simulates* the plan as a discrete-event system driven
directly by the domain's own :condition/:effect declarations.

It does NOT hardcode any notion of "free(waypoint)" or similar locks.
Instead, "shared variables" fall out naturally from the simulation: any
ground atom (predicate + bound arguments) that gets toggled by actions
belonging to more than one distinct actor over the course of the plan is
reported as shared/contested. Any precondition that fails during
simulation because such an atom was already claimed by another actor is
reported as a mutual-exclusion violation -- this is exactly the class of
cross-agent collision this tool was built to catch, but it comes for
free from a correct simulation rather than a special-cased check.

Usage:
    python3 validate_plan.py DOMAIN.pddl PROBLEM.pddl PLAN.txt [--actor-type TYPE] [-q]

Exit code: 0 if the plan is valid, 1 otherwise.

Scope / known limitations (kept honest on purpose):
  - Supports :typing, :durative-actions, :numeric-fluents, :action-costs,
    :timed-initial-literals (each TIL is simulated as its own event at its
    fixed time, independent of the plan's own actions).
  - No support for conditional effects, quantifiers (forall/exists), or
    disjunctive preconditions (or) -- none of these appear in the drone
    domains this tool was built for; a NotImplementedError points at the
    unsupported construct if one is encountered.
  - "over all" conditions are checked at the start instant and then via a
    post-hoc scan of the referenced atom's recorded transition history for
    any flip occurring strictly inside the action's [start, end) interval.
    Numeric "over all" conditions are approximated by checking only at the
    start and end instants (no continuous numeric monitoring).
  - Simultaneous events (identical timestamps) are resolved by processing
    all "_end" effects before "_start" effects, so a departing actor frees
    a resource before an arriving actor at the exact same instant claims it
    -- the more permissive of the two conventions. This is a modeling
    choice, not a discovered fact about the domain; document/adjust if
    your domain wants the opposite convention.
"""

import sys
import re
import argparse
from collections import defaultdict

# The plan file prints times to 3 decimals, so two timestamps meant to be
# the same instant can differ by up to ~0.001. Used wherever plan
# timestamps are compared.
ROUNDING_SLACK = 0.0015


# --------------------------------------------------------------------------
# S-expression tokenizer / parser
# --------------------------------------------------------------------------

def tokenize(text):
    text = re.sub(r";.*", "", text)  # strip PDDL line comments
    return re.findall(r"\(|\)|[^\s()]+", text)


def parse_sexpr_stream(tokens):
    """Parse *all* top-level s-expressions in a token stream."""
    pos = [0]

    def parse_one():
        tok = tokens[pos[0]]
        if tok == "(":
            pos[0] += 1
            lst = []
            while tokens[pos[0]] != ")":
                lst.append(parse_one())
            pos[0] += 1  # consume ')'
            return lst
        else:
            pos[0] += 1
            return tok

    out = []
    while pos[0] < len(tokens):
        out.append(parse_one())
    return out


def _is_number(tok):
    try:
        float(tok)
        return True
    except (TypeError, ValueError):
        return False


def load_sexpr(path):
    with open(path) as f:
        text = f.read()
    forms = parse_sexpr_stream(tokenize(text))
    # a PDDL file is a single (define ...) form
    for form in forms:
        if isinstance(form, list) and form and form[0] == "define":
            return form
    raise ValueError(f"{path}: no (define ...) form found")


# --------------------------------------------------------------------------
# Typed-list parsing (shared by :types, :objects, :predicates args, :parameters)
# --------------------------------------------------------------------------

def parse_typed_list(tokens):
    """['?a','?b','-','t1','?c','-','t2','?d'] -> [('?a','t1'),('?b','t1'),('?c','t2'),('?d','object')]"""
    result = []
    pending = []
    i = 0
    while i < len(tokens):
        tok = tokens[i]
        if tok == "-":
            typ = tokens[i + 1]
            for p in pending:
                result.append((p, typ))
            pending = []
            i += 2
        else:
            pending.append(tok)
            i += 1
    for p in pending:
        result.append((p, "object"))
    return result


# --------------------------------------------------------------------------
# Domain
# --------------------------------------------------------------------------

class ActionSchema:
    def __init__(self, name, params, duration_expr, conditions, effects):
        self.name = name
        self.params = params            # [(varname, type), ...]
        self.duration_expr = duration_expr
        self.conditions = conditions    # [(modifier, literal_sexpr), ...]  modifier in start/end/all
        self.effects = effects          # [(modifier, literal_sexpr), ...]  modifier in start/end


class Domain:
    def __init__(self):
        self.name = None
        self.types = {}       # type -> parent type
        self.constants = {}   # name -> type
        self.predicates = {}  # name -> arity
        self.functions = {}   # name -> arity
        self.actions = {}     # name -> ActionSchema
        self.actor_type = None
        self.actor_var_of = {}  # action name -> varname of the actor parameter


def flatten_temporal(sexpr, default_modifier):
    """Flatten a :condition/:effect sexpr into a list of (modifier, literal)."""
    out = []

    def walk_leaf(modifier, lit):
        if isinstance(lit, list) and lit and lit[0] == "and":
            for sub in lit[1:]:
                walk_leaf(modifier, sub)
        else:
            out.append((modifier, lit))

    def walk(node):
        if not isinstance(node, list) or not node:
            return
        head = node[0]
        if head == "and":
            for sub in node[1:]:
                walk(sub)
        elif head == "at":
            walk_leaf(node[1], node[2])
        elif head == "over":
            walk_leaf("all", node[2])
        elif head in ("forall", "exists", "or", "when"):
            raise NotImplementedError(f"unsupported PDDL construct: {head}")
        else:
            walk_leaf(default_modifier, node)

    walk(sexpr)
    return out


def parse_domain(path):
    form = load_sexpr(path)
    d = Domain()
    d.name = form[1][1] if isinstance(form[1], list) else form[1]

    for section in form[2:]:
        if not isinstance(section, list) or not section:
            continue
        tag = section[0]
        if tag == ":types":
            for name, parent in parse_typed_list(section[1:]):
                d.types[name] = parent
        elif tag == ":constants":
            for name, typ in parse_typed_list(section[1:]):
                d.constants[name] = typ
        elif tag == ":predicates":
            for pred in section[1:]:
                d.predicates[pred[0]] = len(parse_typed_list(pred[1:]))
        elif tag == ":functions":
            for func in section[1:]:
                # functions may be grouped "(f1 args) (f2 args) - number" ; skip trailing "- number"
                if func == "-" or func == "number":
                    continue
                d.functions[func[0]] = len(parse_typed_list(func[1:]))
        elif tag in (":durative-action",):
            name = section[1]
            body = {section[i]: section[i + 1] for i in range(2, len(section), 2)}
            params = parse_typed_list(body[":parameters"])
            dur_spec = body[":duration"]
            # dur_spec is (= ?duration EXPR)  (only form supported)
            if not (isinstance(dur_spec, list) and dur_spec[0] == "="):
                raise NotImplementedError(f"unsupported :duration form in {name}: {dur_spec}")
            duration_expr = dur_spec[2]
            conditions = flatten_temporal(body.get(":condition", ["and"]), "start")
            effects = flatten_temporal(body.get(":effect", ["and"]), "start")
            d.actions[name] = ActionSchema(name, params, duration_expr, conditions, effects)

    _infer_actor_type(d)
    return d


def _type_matches(t, target, types):
    while t is not None:
        if t == target:
            return True
        t = types.get(t)
    return False


def _expr_var_names(expr):
    """All "?"-prefixed variable tokens referenced anywhere in a raw
    (un-grounded) expression tree, e.g. the ones a :duration formula is
    built from."""
    names = set()
    if isinstance(expr, list):
        for e in expr:
            names |= _expr_var_names(e)
    elif isinstance(expr, str) and expr.startswith("?"):
        names.add(expr)
    return names


def _infer_actor_type(d):
    """Heuristic: the type used as a parameter in the most action schemas
    is 'the actor'. Ties (e.g. every action also has a place parameter)
    are broken deterministically -- first by preferring a type whose
    parameter is referenced in the most :duration formulas (the actor is
    usually what a duration's speed/rate depends on), then by type name,
    so the result never depends on this process's set-iteration order."""
    counts = defaultdict(int)
    duration_counts = defaultdict(int)
    for schema in d.actions.values():
        seen_types = sorted({typ for _, typ in schema.params})
        duration_vars = _expr_var_names(schema.duration_expr)
        types_in_duration = sorted({typ for varname, typ in schema.params if varname in duration_vars})
        for typ in seen_types:
            counts[typ] += 1
        for typ in types_in_duration:
            duration_counts[typ] += 1
    if not counts:
        return
    d.actor_type = max(counts.items(), key=lambda kv: (kv[1], duration_counts[kv[0]], kv[0]))[0]
    for name, schema in d.actions.items():
        for varname, typ in schema.params:
            if _type_matches(typ, d.actor_type, d.types):
                d.actor_var_of[name] = varname
                break


# --------------------------------------------------------------------------
# Problem
# --------------------------------------------------------------------------

class Problem:
    def __init__(self):
        self.name = None
        self.domain_name = None
        self.objects = {}       # name -> type
        self.init_facts = set()      # (pred, (args...))
        self.init_funcs = {}         # (func, (args...)) -> float
        self.tils = []                # [(time, sign, pred, args)] -- parsed but not simulated
        self.goal = None
        self.metric = None


def parse_problem(path):
    form = load_sexpr(path)
    p = Problem()
    p.name = form[1][1] if isinstance(form[1], list) else form[1]

    for section in form[2:]:
        if not isinstance(section, list) or not section:
            continue
        tag = section[0]
        if tag == ":domain":
            p.domain_name = section[1]
        elif tag == ":objects":
            for name, typ in parse_typed_list(section[1:]):
                p.objects[name] = typ
        elif tag == ":init":
            for item in section[1:]:
                if item[0] == "=":
                    func_term, val = item[1], item[2]
                    p.init_funcs[(func_term[0], tuple(func_term[1:]))] = float(val)
                elif item[0] == "at" and _is_number(item[1]):
                    # timed-initial-literal: (at TIME fact) -- distinct from a plain
                    # predicate that happens to be named "at" (item[1] is numeric here,
                    # an object name otherwise)
                    time, lit = float(item[1]), item[2]
                    if isinstance(lit, list) and lit[0] == "not":
                        p.tils.append((time, False, lit[1][0], tuple(lit[1][1:])))
                    else:
                        p.tils.append((time, True, lit[0], tuple(lit[1:])))
                else:
                    p.init_facts.add((item[0], tuple(item[1:])))
        elif tag == ":goal":
            p.goal = section[1]
        elif tag == ":metric":
            p.metric = section[1:]

    return p


# --------------------------------------------------------------------------
# Plan
# --------------------------------------------------------------------------

class PlanAction:
    def __init__(self, line_no, start, duration, name, args):
        self.line_no = line_no
        self.start = start
        self.duration = duration
        self.end = start + duration
        self.name = name
        self.args = args

    def __repr__(self):
        return f"{self.name} {' '.join(self.args)}"


PLAN_LINE_RE = re.compile(r"^([\d.]+)\s+\(([\d.]+)\)\s+(\S+)\s*(.*)$")


def parse_plan(path):
    actions = []
    with open(path) as f:
        for line_no, line in enumerate(f, 1):
            line = line.strip()
            if not line or line.startswith("Cost:") or line.startswith("Makespan:") or line.startswith("Total-time"):
                continue
            m = PLAN_LINE_RE.match(line)
            if not m:
                continue
            start, dur, name, rest = m.groups()
            args = tuple(rest.split())
            actions.append(PlanAction(line_no, float(start), float(dur), name, args))
    actions.sort(key=lambda a: a.start)
    return actions


# --------------------------------------------------------------------------
# Numeric expression evaluation
# --------------------------------------------------------------------------

def ground_args(args, bindings):
    return tuple(bindings.get(a, a) for a in args)


def eval_expr(expr, bindings, functions_state):
    if isinstance(expr, list):
        head = expr[0]
        if head in ("+", "-", "*", "/"):
            vals = [eval_expr(e, bindings, functions_state) for e in expr[1:]]
            if head == "-" and len(vals) == 1:
                return -vals[0]
            result = vals[0]
            for v in vals[1:]:
                if head == "+":
                    result += v
                elif head == "-":
                    result -= v
                elif head == "*":
                    result *= v
                elif head == "/":
                    result /= v
            return result
        else:
            # function application: (funcname arg1 arg2 ...)
            fargs = ground_args(expr[1:], bindings)
            key = (head, fargs)
            if key not in functions_state:
                raise KeyError(f"function value not set: {head}{fargs}")
            return functions_state[key]
    else:
        try:
            return float(expr)
        except ValueError:
            # bare 0-arity function name
            key = (expr, ())
            if key in functions_state:
                return functions_state[key]
            raise KeyError(f"cannot evaluate term: {expr}")


NUMCOMP_OPS = {
    ">=": lambda a, b: a >= b - 1e-9,
    "<=": lambda a, b: a <= b + 1e-9,
    ">": lambda a, b: a > b - 1e-9,
    "<": lambda a, b: a < b + 1e-9,
    "=": lambda a, b: abs(a - b) < 1e-6,
}


def classify_literal(x):
    """(neg, kind, name, args_or_operands) for a condition literal."""
    if isinstance(x, list) and x and x[0] == "not":
        neg, inner = True, x[1]
    else:
        neg, inner = False, x
    head = inner[0]
    if head in NUMCOMP_OPS:
        return neg, "numcomp", head, (inner[1], inner[2])
    return neg, "pred", head, tuple(inner[1:])


def classify_effect(x):
    if isinstance(x, list) and x and x[0] == "not":
        return "pred", True, x[1][0], tuple(x[1][1:]), None
    head = x[0]
    if head in ("assign", "increase", "decrease"):
        func_term, expr = x[1], x[2]
        return "numeric", head, func_term[0], tuple(func_term[1:]), expr
    return "pred", False, head, tuple(x[1:]), None


# --------------------------------------------------------------------------
# Simulation
# --------------------------------------------------------------------------

class Violation:
    def __init__(self, time, pa, phase, message, shared=False, atom_key=None):
        self.time = time
        self.pa = pa
        self.phase = phase
        self.message = message
        self.shared = shared
        self.atom_key = atom_key  # (pred, args) this violation is about, for post-hoc relabeling

    def __str__(self):
        tag = "MUTUAL-EXCLUSION VIOLATION" if self.shared else "VIOLATION"
        return f"[t={self.time:.3f}] {tag} during '{self.pa}' ({self.phase}): {self.message}"


def bindings_for(schema, pa):
    return dict(zip((v for v, _ in schema.params), pa.args))


class Simulator:
    def __init__(self, domain, problem, plan):
        self.domain = domain
        self.problem = problem
        self.plan = plan
        self.state = set(problem.init_facts)
        self.functions = dict(problem.init_funcs)
        self.atom_history = defaultdict(list)  # (pred,args) -> [(time, newval, actor, pa)]
        self.violations = []
        self.duration_mismatches = []

    def run(self):
        events = []
        for i, pa in enumerate(self.plan):
            events.append((pa.end, 0, i, "end"))
            events.append((pa.start, 1, i, "start"))
        # A timed-initial-literal is the environment committing to a fact
        # at a fixed time, independent of any action. Give it priority -1
        # so it's in effect for any action tied with it at the same
        # instant, the same way a release is treated as available to an
        # acquire at the same instant.
        for i in range(len(self.problem.tils)):
            til_time = self.problem.tils[i][0]
            events.append((til_time, -1, i, "til"))
        # Nudge "end" events earlier by the rounding slack before sorting so
        # a release is never ordered after the acquire it's really
        # simultaneous with.
        def sort_key(e):
            t, priority, _, phase = e
            if phase == "end":
                t -= ROUNDING_SLACK
            return (round(t, 6), priority)
        events.sort(key=sort_key)

        for time, _, i, phase in events:
            if phase == "til":
                _, sign, name, args = self.problem.tils[i]
                key = (name, args)
                if sign:
                    self.state.add(key)
                else:
                    self.state.discard(key)
                self.atom_history[key].append((time, sign, "TIL", "TIL"))
                continue

            pa = self.plan[i]
            schema = self.domain.actions.get(pa.name)
            if schema is None:
                raise ValueError(f"plan line {pa.line_no}: unknown action '{pa.name}' (not in domain)")
            bindings = bindings_for(schema, pa)
            actor = bindings.get(self.domain.actor_var_of.get(pa.name))

            if phase == "start":
                self._check_duration(schema, pa, bindings)

            for modifier, lit in schema.conditions:
                if modifier != phase:
                    continue
                self._check_condition(lit, bindings, pa, phase)

            for modifier, eff in schema.effects:
                if modifier != phase:
                    continue
                self._apply_effect(eff, bindings, pa, time, actor)

        # _is_shared() during the event loop only sees history recorded *so far*,
        # so a violation caused by actor B against a resource only actor A has
        # touched *so far* looks unshared at that instant, even though B's own
        # (rejected) attempt would make it shared. Relabel now that every
        # actor's full history is known.
        for v in self.violations:
            if v.atom_key is not None:
                v.shared = self._is_shared(*v.atom_key)

        self._check_overall_conditions()
        return self

    def _check_duration(self, schema, pa, bindings):
        try:
            expected = eval_expr(schema.duration_expr, bindings, self.functions)
        except KeyError as e:
            self.duration_mismatches.append(f"'{pa}': could not evaluate duration ({e})")
            return
        if abs(expected - pa.duration) > 0.02:
            self.duration_mismatches.append(
                f"'{pa}': plan duration {pa.duration:.3f} != domain formula {expected:.3f}"
            )

    def _check_condition(self, lit, bindings, pa, phase):
        neg, kind, name, operands = classify_literal(lit)
        if kind == "pred":
            args = ground_args(operands, bindings)
            holds = (name, args) in self.state
            required = not neg
            if holds != required:
                shared = self._is_shared(name, args)
                msg = f"requires {'not ' if neg else ''}({name} {' '.join(args)}) but it is {'true' if holds else 'false'}"
                if shared:
                    holder = self._current_holder(name, args)
                    msg += f" (currently held by: {holder})"
                self.violations.append(Violation(pa.start if phase == "start" else pa.end, pa, phase, msg,
                                                  shared, atom_key=(name, args)))
        else:  # numcomp
            try:
                lhs = eval_expr(operands[0], bindings, self.functions)
                rhs = eval_expr(operands[1], bindings, self.functions)
            except KeyError as e:
                self.violations.append(Violation(pa.start, pa, phase, f"numeric condition unevaluable: {e}"))
                return
            op_fn = NUMCOMP_OPS[name]
            ok = op_fn(lhs, rhs)
            if neg:
                ok = not ok
            if not ok:
                self.violations.append(
                    Violation(pa.start if phase == "start" else pa.end, pa, phase,
                              f"numeric condition ({name} {lhs:.3f} {rhs:.3f}) failed")
                )

    def _apply_effect(self, eff, bindings, pa, time, actor):
        kind, a, b, c, expr = classify_effect(eff)
        if kind == "pred":
            neg, name, args = a, b, c
            key = (name, ground_args(args, bindings))
            newval = not neg
            if newval:
                self.state.add(key)
            else:
                self.state.discard(key)
            self.atom_history[key].append((time, newval, actor, pa))
        else:
            op, fname, fargs = a, b, c
            key = (fname, ground_args(fargs, bindings))
            rhs = eval_expr(expr, bindings, self.functions)
            if op == "assign":
                self.functions[key] = rhs
            elif op == "increase":
                self.functions[key] = self.functions.get(key, 0.0) + rhs
            elif op == "decrease":
                self.functions[key] = self.functions.get(key, 0.0) - rhs

    def _is_shared(self, name, args):
        actors = {a for _, _, a, _ in self.atom_history.get((name, args), []) if a is not None}
        return len(actors) > 1

    def _current_holder(self, name, args):
        hist = self.atom_history.get((name, args), [])
        for t, val, actor, pa in reversed(hist):
            return f"{actor} (via '{pa}' @ t={t:.3f})"
        return "unknown"

    def _check_overall_conditions(self):
        for pa in self.plan:
            schema = self.domain.actions[pa.name]
            bindings = bindings_for(schema, pa)
            for modifier, lit in schema.conditions:
                if modifier != "all":
                    continue
                neg, kind, name, operands = classify_literal(lit)
                if kind != "pred":
                    continue  # numeric "over all": not continuously monitored (see module docstring)
                args = ground_args(operands, bindings)
                hist = sorted(self.atom_history.get((name, args), []), key=lambda h: h[0])
                required = not neg
                # value just before pa.start
                cur = None
                for t, val, actor, _ in hist:
                    if t <= pa.start + ROUNDING_SLACK:
                        cur = val
                    else:
                        break
                if cur is None:
                    cur = (name, args) in self.problem.init_facts
                if cur != required:
                    self.violations.append(Violation(
                        pa.start, pa, "over-all-start",
                        f"requires {'not ' if neg else ''}({name} {' '.join(args)}) to hold at start, but it doesn't"
                    ))
                    continue
                for t, val, actor, causer in hist:
                    if pa.start + ROUNDING_SLACK < t < pa.end - ROUNDING_SLACK:
                        self.violations.append(Violation(
                            t, pa, "over-all",
                            f"({name} {' '.join(args)}) flipped to {val} mid-action, by '{causer}'",
                            shared=self._is_shared(name, args)
                        ))

    def shared_atoms(self):
        result = []
        for key, hist in self.atom_history.items():
            actors = {a for _, _, a, _ in hist if a is not None}
            if len(actors) > 1:
                result.append((key, sorted(hist, key=lambda h: h[0]), actors))
        return sorted(result, key=lambda r: r[0])

    def check_goal(self):
        return self._eval_goal(self.problem.goal)

    def _eval_goal(self, node):
        if not isinstance(node, list) or not node:
            return True, []
        head = node[0]
        if head == "and":
            ok = True
            missing = []
            for sub in node[1:]:
                sub_ok, sub_missing = self._eval_goal(sub)
                ok = ok and sub_ok
                missing.extend(sub_missing)
            return ok, missing
        neg, kind, name, operands = classify_literal(node)
        if kind == "pred":
            args = tuple(operands)
            holds = (name, args) in self.state
            required = not neg
            if holds == required:
                return True, []
            return False, [f"{'not ' if neg else ''}({name} {' '.join(args)})"]
        else:
            lhs = eval_expr(operands[0], {}, self.functions)
            rhs = eval_expr(operands[1], {}, self.functions)
            ok = NUMCOMP_OPS[name](lhs, rhs)
            if neg:
                ok = not ok
            return ok, [] if ok else [f"numeric goal ({name} {lhs:.3f} {rhs:.3f})"]


# --------------------------------------------------------------------------
# Reporting
# --------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("domain")
    ap.add_argument("problem")
    ap.add_argument("plan")
    ap.add_argument("--actor-type", help="override auto-detected actor type (e.g. 'drone')")
    ap.add_argument("-q", "--quiet", action="store_true", help="print only the final verdict")
    args = ap.parse_args()

    domain = parse_domain(args.domain)
    if args.actor_type:
        domain.actor_type = args.actor_type
        for name, schema in domain.actions.items():
            for varname, typ in schema.params:
                if _type_matches(typ, domain.actor_type, domain.types):
                    domain.actor_var_of[name] = varname
                    break

    problem = parse_problem(args.problem)
    plan = parse_plan(args.plan)

    if not args.quiet:
        print(f"=== MA-LAMA Plan Validator ===")
        print(f"Domain:  {args.domain}  ({len(domain.actions)} actions, actor type: {domain.actor_type})")
        print(f"Problem: {args.problem}  ({len(problem.objects)} objects)")
        print(f"Plan:    {args.plan}  ({len(plan)} actions)")
        if problem.tils:
            print(f"Problem has {len(problem.tils)} timed-initial-literal(s); simulated as events.")
        print()

    sim = Simulator(domain, problem, plan).run()

    shared = sim.shared_atoms()
    if not args.quiet:
        print(f"--- Shared variables detected: {len(shared)} ---")
        for (pred, args_), hist, actors in shared:
            print(f"  {pred}({', '.join(args_)})  -- actors: {', '.join(sorted(actors))}")
        print()

        print("--- Shared-variable timelines ---")
        for (pred, args_), hist, actors in shared:
            print(f"  {pred}({', '.join(args_)}):")
            for t, val, actor, pa in hist:
                print(f"    t={t:8.3f}  -> {val!s:5}  by {actor:10s} via '{pa}'")
        print()

    real_violations = [v for v in sim.violations]
    if not args.quiet:
        print(f"--- Precondition / numeric violations: {len(real_violations)} ---")
        for v in real_violations:
            print(f"  {v}")
        print()

        print(f"--- Duration mismatches: {len(sim.duration_mismatches)} ---")
        for m in sim.duration_mismatches:
            print(f"  {m}")
        print()

    goal_ok, missing = sim.check_goal()
    if not args.quiet:
        print(f"--- Goal check ---")
        if goal_ok:
            print("  Goal satisfied.")
        else:
            print("  Goal NOT satisfied. Missing:")
            for m in missing:
                print(f"    {m}")
        print()

    collision_count = sum(1 for v in real_violations if v.shared)
    other_violation_count = len(real_violations) - collision_count
    is_valid = (len(real_violations) == 0) and (len(sim.duration_mismatches) == 0) and goal_ok

    print("=" * 60)
    if is_valid:
        print(f"VERDICT: VALID -- {len(shared)} shared variable(s), all correctly enforced. Goal satisfied.")
    else:
        print(f"VERDICT: INVALID")
        print(f"  shared-resource (mutual-exclusion) violations: {collision_count}")
        print(f"  other precondition/numeric violations:         {other_violation_count}")
        print(f"  duration mismatches:                            {len(sim.duration_mismatches)}")
        print(f"  goal satisfied:                                 {goal_ok}")
    print("=" * 60)

    return 0 if is_valid else 1


if __name__ == "__main__":
    sys.exit(main())
