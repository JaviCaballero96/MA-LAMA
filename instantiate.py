#! /usr/bin/env python
# -*- coding: latin-1 -*-


from collections import defaultdict

import build_model
import pddl_to_prolog
import pddl
import timers


def get_fluent_facts(task, model):
    fluent_predicates = set()
    fluent_functions = set()
    fluent_functions_aux = set()
    for action in task.actions:
        for effect in action.effects:
            if isinstance(effect, pddl.effects.CostEffect):
                fluent_functions_aux.add(effect.effect.fluent.symbol)
            else:
                fluent_predicates.add(effect.literal.predicate)
    for axiom in task.axioms:
        fluent_predicates.add(axiom.name)

    for function in model:
        if isinstance(function.predicate, pddl.f_expression.Increase):
            if function.predicate.fluent.symbol in fluent_functions_aux:
                fluent_functions.add(function)

    return set([fact for fact in model
                if fact.predicate in fluent_predicates]), fluent_functions


def get_objects_by_type(typed_objects, types):
    result = defaultdict(list)
    supertypes = {}
    for type in types:
        supertypes[type.name] = type.supertype_names
    for obj in typed_objects:
        result[obj.type].append(obj.name)
        for type in supertypes[obj.type]:
            result[type].append(obj.name)
    return result


def instantiate(task, model):
    # TODO interactions between functions are still working a basic level
    # In order for it to work in a domain such as the rechargable
    # battery one, deeper analysis have to be carreid out

    relaxed_reachable = False
    fluent_facts, fluents_functions_aux = get_fluent_facts(task, model)
    init_facts = set(task.init)
    fluents_functions = intantiate_func_args(fluents_functions_aux)

    type_to_objects = get_objects_by_type(task.objects, task.types)

    instantiated_actions = []
    instantiated_axioms = []
    reachable_action_parameters = defaultdict(list)
    for atom in model:
        if isinstance(atom.predicate, pddl.Action):
            action = atom.predicate
            parameters = action.parameters
            inst_parameters = atom.args[:len(parameters)]
            reachable_action_parameters[action.name].append(inst_parameters)
            if isinstance(action.precondition, pddl.ExistentialCondition):
                parameters = list(parameters)
                parameters += action.precondition.parameters
            variable_mapping = dict([(par.name, arg)
                                     for par, arg in zip(parameters, atom.args)])
            inst_action = action.instantiate(variable_mapping, init_facts,
                                             fluent_facts, type_to_objects, task.metric)
            if inst_action:
                instantiated_actions.append(inst_action)
        elif isinstance(atom.predicate, pddl.Axiom):
            axiom = atom.predicate
            parameters = axiom.parameters
            if isinstance(axiom.condition, pddl.ExistentialCondition):
                parameters = list(parameters)
                parameters += axiom.condition.parameters
            variable_mapping = dict([(par.name, arg)
                                     for par, arg in zip(parameters, atom.args)])
            inst_axiom = axiom.instantiate(variable_mapping, init_facts, fluent_facts)
            if inst_axiom:
                instantiated_axioms.append(inst_axiom)
        elif atom.predicate == "@goal-reachable":
            relaxed_reachable = True

    return (relaxed_reachable, fluent_facts, fluents_functions, instantiated_actions,
            instantiated_axioms, reachable_action_parameters)


def intantiate_func_args(functions):
    new_functions = set()
    for func in functions:
        fluent = func.predicate.fluent
        expression = func.predicate.expression

        new_fluent = pddl.f_expression.PrimitiveNumericExpression(fluent.symbol,
                                                                  [pddl.conditions.Variable(func.args[int(arg.name)])
                                                                   for arg in fluent.args])
        new_expression = get_new_expression(expression, func.args)

        new_functions.add(pddl.Atom(pddl.f_expression.Increase(new_fluent, new_expression), func.args))
    return new_functions


def get_new_expression(old_expression, atom_args):
    if old_expression.symbol == "*" or old_expression.symbol == "/" or old_expression.symbol == "-" or old_expression.\
            symbol == "+":
        func_term_1 = get_new_expression(pddl.f_expression.PrimitiveNumericExpression(old_expression.args[0].name,
                                                                                      old_expression.args[0].args),
                                         atom_args)
        func_term_2 = get_new_expression(pddl.f_expression.PrimitiveNumericExpression(old_expression.args[1].name,
                                                                                      old_expression.args[1].args),
                                         atom_args)
        return pddl.f_expression.PrimitiveNumericExpression(
            old_expression.symbol,
            [func_term_1, func_term_2])

    else:
        return pddl.f_expression.PrimitiveNumericExpression(
            old_expression.symbol,
            [pddl.conditions.Variable(atom_args[int(arg.name)])
             for arg in old_expression.args])


def explore(task):
    prog = pddl_to_prolog.translate(task)
    model = build_model.compute_model(prog)
    with timers.timing("Completing instantiation"):
        return instantiate(task, model)


if __name__ == "__main__":
    import pddl

    task = pddl.open()
    relaxed_reachable, atoms, actions, axioms = explore(task)
    print("goal relaxed reachable: %s" % relaxed_reachable)
    print("%d atoms:" % len(atoms))
    for atom in atoms:
        print(" ", atom)
    print()
    print("%d actions:" % len(actions))
    for action in actions:
        action.dump()
        print()
    print()
    print("%d axioms:" % len(axioms))
    for axiom in axioms:
        axiom.dump()
        print()
