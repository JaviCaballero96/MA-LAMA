#! /usr/bin/env python
# -*- coding: latin-1 -*-


from collections import deque, defaultdict
import itertools
import time

import invariants
import pddl
import timers


class BalanceChecker(object):
    def __init__(self, task, reachable_action_params):
        self.predicates_to_add_actions = defaultdict(set)
        self.action_name_to_heavy_action = {}
        for act in task.actions:
            action = self.add_inequality_preconds(act, reachable_action_params)
            too_heavy_effects = []
            create_heavy_act = False
            heavy_act = action
            for eff in action.effects:
                too_heavy_effects.append(eff)
                if not isinstance(eff, pddl.effects.CostEffect):
                    if eff.parameters:  # universal effect
                        create_heavy_act = True
                        too_heavy_effects.append(eff.copy())
                    if not eff.literal.negated:
                        predicate = eff.literal.predicate
                        self.predicates_to_add_actions[predicate].add(action)
            if create_heavy_act:
                heavy_act = pddl.Action(action.name, action.parameters,
                                        action.precondition, too_heavy_effects,
                                        action.cost)
            # heavy_act: duplicated universal effects and assigned unique names
            # to all quantified variables (implicitly in constructor)
            self.action_name_to_heavy_action[action.name] = heavy_act

    def get_threats(self, predicate):
        return self.predicates_to_add_actions.get(predicate, set())

    def get_heavy_action(self, action_name):
        return self.action_name_to_heavy_action[action_name]

    def add_inequality_preconds(self, action, reachable_action_params):
        if reachable_action_params is None or len(action.parameters) < 2:
            return action
        inequal_params = []
        combs = itertools.combinations(list(range(len(action.parameters))), 2)
        for pos1, pos2 in combs:
            inequality = True
            for params in reachable_action_params[action.name]:
                if params[pos1] == params[pos2]:
                    inequality = False
                    break
            if inequality:
                inequal_params.append((pos1, pos2))

        if inequal_params:
            precond_parts = list(action.precondition.parts)
            for pos1, pos2 in inequal_params:
                param1 = action.parameters[pos1].name
                param2 = action.parameters[pos2].name
                new_cond = pddl.NegatedAtom("=", (param1, param2))
                precond_parts.append(new_cond)
            precond = action.precondition.change_parts(precond_parts)
            return pddl.Action(action.name, action.parameters, precond,
                               action.effects, action.cost)
        else:
            return action


def get_fluents(task):
    fluent_names = set()
    for action in task.actions:
        for eff in action.effects:
            if not isinstance(eff, pddl.effects.CostEffect):
                fluent_names.add(eff.literal.predicate)
    return [pred for pred in task.predicates if pred.name in fluent_names]


def get_fluents_funcs(task):
    fluent_functions = set()
    for action in task.actions:
        for eff in action.effects:
            if isinstance(eff, pddl.effects.CostEffect):
                fluent_functions.add(eff.effect.fluent.symbol)
    return [func for func in task.functions if func.name in fluent_functions]


def get_initial_invariants(task):
    pred_list = get_fluents(task)
    for predicate in pred_list:
        all_args = list(range(len(predicate.arguments)))
        for omitted_arg in [-1] + all_args:
            order = [i for i in all_args if i != omitted_arg]
            part = invariants.InvariantPart(predicate.name, order, omitted_arg)
            yield invariants.Invariant((part,))


def get_initial_funcs(task):
    func_list = get_fluents_funcs(task)
    for function in func_list:
        all_args = list(range(len(function.arguments)))
        for omitted_arg in [-1] + all_args:
            order = [i for i in all_args if i != omitted_arg]
            part = invariants.InvariantPart(function.name, order, omitted_arg)
            yield invariants.Invariant((part,))


# Input file might be grounded, beware of too many invariant candidates
MAX_CANDIDATES = 100000
MAX_TIME = 300


def find_invariants(task, reachable_action_params):
    pred_candidates = deque(get_initial_invariants(task))
    func_candidates = deque(get_initial_funcs(task))
    print(len(pred_candidates), "initial candidates")
    seen_candidates = set(pred_candidates)

    balance_checker = BalanceChecker(task, reachable_action_params)

    def enqueue_func(invariant):
        if len(seen_candidates) < MAX_CANDIDATES and invariant not in seen_candidates:
            pred_candidates.append(invariant)
            seen_candidates.add(invariant)

    start_time = time.process_time()
    while pred_candidates:
        candidate = pred_candidates.popleft()
        if time.process_time() - start_time > MAX_TIME:
            print("Time limit reached, aborting invariant generation")
            return
        if candidate.check_balance(balance_checker, enqueue_func):
            yield candidate
    print("Invariants search end")


def useful_groups(invariants, initial_facts):
    predicate_to_invariants = defaultdict(list)
    for invariant in invariants:
        for predicate in invariant.predicates:
            predicate_to_invariants[predicate].append(invariant)

    nonempty_groups = set()
    overcrowded_groups = set()
    for atom in initial_facts:
        if isinstance(atom, pddl.Assign):
            continue
        for invariant in predicate_to_invariants.get(atom.predicate, ()):
            group_key = (invariant, tuple(invariant.get_parameters(atom)))
            if group_key not in nonempty_groups:
                nonempty_groups.add(group_key)
            else:
                overcrowded_groups.add(group_key)
    useful_groups = nonempty_groups - overcrowded_groups
    for (invariant, parameters) in useful_groups:
        yield [part.instantiate(parameters) for part in invariant.parts]


def get_groups(task, reachable_action_params=None):
    with timers.timing("Finding invariants"):
        invariants = list(find_invariants(task, reachable_action_params))
        invariants_f = remove_free_invariant(invariants)
    with timers.timing("Checking invariant weight"):
        result = list(useful_groups(invariants_f, task.init))
    return result


def remove_free_invariant(invariants):
    invariants_f = []
    for inv in invariants:
        append = True
        for pred in inv.predicates:
            if pred == "free_agent":
                append = False
                continue
        if append:
            invariants_f.append(inv)
    return invariants_f


if __name__ == "__main__":
    import pddl

    print("Parsing...")
    task = pddl.open()
    print("Finding invariants...")
    for invariant in find_invariants(task):
        print(invariant)
    print("Finding fact groups...")
    groups = get_groups(task)
    for group in groups:
        print("[%s]" % ", ".join(map(str, group)))
