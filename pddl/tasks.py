import pddl.functions
from . import actions
from . import durative_actions
from . import axioms
from . import conditions
from . import predicates
from . import pddl_types
from . import functions
from . import f_expression


class Task(object):
    FUNCTION_SYMBOLS = dict()

    def __init__(self, domain_name, task_name, requirements, temp_task,
                 types, objects, predicates, functions, init, init_temp, goal, actions, axioms, metric, modules):
        self.domain_name = domain_name
        self.task_name = task_name
        self.requirements = requirements
        self.temp_task = temp_task
        self.types = types
        self.objects = objects
        self.predicates = predicates
        self.functions = functions
        self.init = init
        self.init_temp = init_temp
        self.goal = goal
        self.actions = actions
        self.axioms = axioms
        self.axiom_counter = 0
        self.metric = metric
        self.modules = modules

    def add_axiom(self, parameters, condition):
        name = "new-axiom@%d" % self.axiom_counter
        self.axiom_counter += 1
        axiom = axioms.Axiom(name, parameters, condition)
        self.predicates.append(predicates.Predicate(name, parameters))
        self.axioms.append(axiom)
        return axiom

    def parse(domain_pddl, task_pddl):
        domain_name, requirements, temp_task, types, constants, predicates, modules, functions, actions, axioms \
            = parse_domain(domain_pddl)
        task_name, task_domain_name, objects, init, init_temp, goal, use_metric = parse_task(task_pddl)

        assert domain_name == task_domain_name
        objects = constants + objects
        init += [conditions.Atom("=", (obj.name, obj.name)) for obj in objects]
        return Task(domain_name, task_name, requirements, temp_task, types, objects,
                    predicates, functions, init, init_temp, goal, actions, axioms, use_metric, modules)

    parse = staticmethod(parse)

    def dump(self):
        print("Problem %s: %s [%s]" % (self.domain_name, self.task_name,
                                       self.requirements))
        print("Types:")
        for type in self.types:
            print("  %s" % type)
        print("Objects:")
        for obj in self.objects:
            print("  %s" % obj)
        print("Predicates:")
        for pred in self.predicates:
            print("  %s" % pred)
        print("Functions:")
        for func in self.functions:
            print("  %s" % func)
        print("Init:")
        for fact in self.init:
            print("  %s" % fact)
        print("Goal:")
        self.goal.dump()
        print("Actions:")
        for action in self.actions:
            action.dump()
        if self.axioms:
            print("Axioms:")
            for axiom in self.axioms:
                axiom.dump()


class Requirements(object):
    def __init__(self, requirements):
        self.requirements = requirements
        for req in requirements:
            assert req in (
                ":strips", ":adl", ":typing", ":negation", ":equality",
                ":negative-preconditions", ":disjunctive-preconditions",
                ":quantified-preconditions", ":conditional-effects",
                ":derived-predicates", ":action-costs", ":requirements",
                ":fluents", ":durative-actions", ":preferences", ":constraints",
                ":numeric-fluents", ":timed-initial-literals", ":external-functions"), req

    def __str__(self):
        return ", ".join(self.requirements)


def parse_domain(domain_pddl):
    iterator = iter(domain_pddl)

    assert next(iterator) == "define"
    domain_line = next(iterator)
    assert domain_line[0] == "domain" and len(domain_line) == 2
    yield domain_line[1]

    opt_requirements = next(iterator)
    if opt_requirements[0] == ":requirements":
        yield Requirements(opt_requirements[1:])
        opt_types = next(iterator)
    else:
        yield Requirements([":strips"])
        opt_types = opt_requirements

    temp_task = False
    if ":durative-actions" in opt_requirements:
        temp_task = True
    yield temp_task

    the_types = [pddl_types.Type("object")]
    if opt_types[0] == ":types":
        the_types.extend(pddl_types.parse_typed_list(opt_types[1:],
                                                     constructor=pddl_types.Type))
        opt_constants = next(iterator)
    else:
        opt_constants = opt_types
    pddl_types.set_supertypes(the_types)
    # for type in the_types:
    #   print repr(type), type.supertype_names
    yield the_types

    if opt_constants[0] == ":constants":
        yield pddl_types.parse_typed_list(opt_constants[1:])
        pred = next(iterator)
    else:
        yield []
        pred = opt_constants

    assert pred[0] == ":predicates"

    the_predicates = [predicates.Predicate.parse(entry) for entry in pred[1:]] + [predicates.Predicate("=",
                                                                                                       [
                                                                                                           pddl_types.TypedObject(
                                                                                                               "?x",
                                                                                                               "object"),
                                                                                                           pddl_types.TypedObject(
                                                                                                               "?y",
                                                                                                               "object")])]

    yield the_predicates

    modules = []
    opt_modules = next(iterator)
    if opt_modules[0] == ":modules":
        print("Reading modules...")

        for module_elem in opt_modules[1:]:
            assert module_elem[0] == ":module"
            module = []

            module.append(module_elem[1])
            module.append([])
            for func_elem in module_elem[2:]:
                assert func_elem[0] == ":function"
                module[1].append(pddl.functions.Function.parse(func_elem[1]))

            modules.append(module)

        yield modules
        opt_functions = next(iterator)
    else:
        yield []
        opt_functions = opt_modules

    if opt_functions[0] == ":functions":
        the_functions = pddl_types.parse_typed_list(opt_functions[1:],
                                                    constructor=functions.Function.parse_typed, functions=True)
        if temp_task:
            # add total-time function
            total_time_func = functions.Function.parse_typed(["total-time"], "number")
            the_functions.append(total_time_func)
        for function in the_functions:
            Task.FUNCTION_SYMBOLS[function.name] = function.type
        yield the_functions
        first_durative_action = next(iterator)
        # first_action = next(iterator)
    else:
        yield []
        first_durative_action = opt_functions
        # first_action = opt_functions

    entries = [first_durative_action] + [entry for entry in iterator]
    the_axioms = []
    the_durative_actions = []
    the_actions = []
    if temp_task:
        for entry in entries:
            if entry[0] == ":derived":
                axiom = axioms.Axiom.parse(entry)
                the_axioms.append(axiom)
            else:
                durative_action = durative_actions.DurativeAction.parse(entry)
                the_durative_actions.append(durative_action)
        yield the_durative_actions
    else:
        for entry in entries:
            if entry[0] == ":derived":
                axiom = axioms.Axiom.parse(entry)
                the_axioms.append(axiom)
            else:
                action = actions.Action.parse(entry)
                the_actions.append(action)
        yield the_actions
    yield the_axioms

    # entries = [first_action] + [entry for entry in iterator]
    # the_axioms = []
    # the_actions = []
    # for entry in entries:
    #    if entry[0] == ":derived":
    #        axiom = axioms.Axiom.parse(entry)
    #        the_axioms.append(axiom)
    #    else:
    #        action = actions.Action.parse(entry)
    #        the_actions.append(action)
    # yield the_actions
    # yield the_axioms


def parse_task(task_pddl):
    iterator = iter(task_pddl)

    assert next(iterator) == "define"
    problem_line = next(iterator)
    assert problem_line[0] == "problem" and len(problem_line) == 2
    yield problem_line[1]
    domain_line = next(iterator)
    assert domain_line[0] == ":domain" and len(domain_line) == 2
    yield domain_line[1]

    objects_opt = next(iterator)
    if objects_opt[0] == ":objects":
        yield pddl_types.parse_typed_list(objects_opt[1:])
        init = next(iterator)
    else:
        yield []
        init = objects_opt

    assert init[0] == ":init"
    initial = []
    initial_temp = []
    for fact in init[1:]:
        if fact[0] == "=":
            try:
                initial.append(f_expression.parse_assignment(fact))
            except ValueError as e:
                raise SystemExit("Error in initial state specification\n" +
                                 "Reason: %s." % e)
        else:
            if fact[0] == "at":
                if fact[2][0] == "not":
                    initial_temp.append(conditions.NegatedAtom(fact[2][1][0], fact[2][1][1:]))
                else:
                    initial_temp.append(conditions.Atom(fact[2][0], fact[2][1:]))
                initial_temp[-1].at = fact[1]
            else:
                initial.append(conditions.Atom(fact[0], fact[1:]))
                initial[-1].at = 0

    # Append initial state of free_agent()
    # initial.append(conditions.Atom("free_agent", []))

    initial.append(f_expression.parse_assignment(["=", "total-time", "0"]))
    yield initial
    yield initial_temp

    goal = next(iterator)
    assert goal[0] == ":goal" and len(goal) == 2
    goal_aux = conditions.parse_condition(goal[1])
    yield goal_aux[0]

    metric = []
    for entry in iterator:
        if entry[0] == ":metric":
            metric.append(entry[1])
            if entry[2][0] == "total-cost":
                # metric = "total-cost"
                metric.append(f_expression.parse_expression(entry[2][:]))
            elif entry[2][0] == "+":
                for pne in entry[2][1:]:
                    metric.append(f_expression.parse_expression(pne))
            elif len(entry[0]) != "+":
                metric.append(f_expression.parse_expression(entry[2][:]))
            else:
                metric.append(entry[2][0])
    yield metric

    for entry in iterator:
        assert False, entry
