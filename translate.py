#! /usr/bin/env python
# -*- coding: utf-8 -*-


from collections import defaultdict
from copy import deepcopy

import axiom_rules
import fact_groups
import instantiate
import pddl
import sas_tasks
import simplify
import timers
import snap_actions
import graphs
import os

# TODO: The translator may generate trivial derived variables which are always true,
# for example if there ia a derived predicate in the input that only depends on
# (non-derived) variables which are detected as always true.
# Such a situation was encountered in the PSR-STRIPS-DerivedPredicates domain.
# Such "always-true" variables should best be compiled away, but it is
# not clear what the best place to do this should be. Similar
# simplifications might be possible elsewhere, for example if a
# derived variable is synonymous with another variable (derived or
# non-derived).

ALLOW_CONFLICTING_EFFECTS = True
USE_PARTIAL_ENCODING = False
DETECT_UNREACHABLE = True
SIMPLIFIED_CASUAL_GRAPH = True

## Setting the following variable to True can cause a severe
## performance penalty due to weaker relevance analysis (see issue7).
ADD_IMPLIED_PRECONDITIONS = False

removed_implied_effect_counter = 0
simplified_effect_condition_counter = 0
added_implied_precondition_counter = 0


def strips_to_sas_dictionary(groups, assert_partial):
    dictionary = {}
    func_aux_dictionary = {}
    for var_no, group in enumerate(groups):
        for val_no, atom in enumerate(group):
            dictionary.setdefault(atom, []).append((var_no, val_no))
            if isinstance(atom.predicate, pddl.f_expression.Increase) or \
                    isinstance(atom.predicate, pddl.f_expression.Decrease) or \
                    isinstance(atom.predicate, pddl.f_expression.Assign) or \
                    isinstance(atom.predicate, pddl.f_expression.GreaterThan) or \
                    isinstance(atom.predicate, pddl.f_expression.LessThan):
                func_aux_dictionary[atom.predicate.__class__.__name__ + " " + str(atom.predicate.fluent)
                                    + " " + str(atom.predicate.expression)] = atom
    if assert_partial:
        assert all(len(sas_pairs) == 1
                   for sas_pairs in dictionary.values())
    return [len(group) + 1 for group in groups], dictionary, func_aux_dictionary


def translate_strips_conditions_aux(conditions, dictionary, ranges):
    condition = {}
    for fact in conditions:
        if fact.negated:
            # we handle negative conditions later, because then we
            # can recognize when the negative condition is already
            # ensured by a positive condition
            continue
        for var, val in dictionary.get(fact, ()):
            # The default () here is a bit of a hack. For goals (but
            # only for goals!), we can get static facts here. They
            # cannot be statically false (that would have been
            # detected earlier), and hence they are statically true
            # and don't need to be translated.
            # TODO: This would not be necessary if we dealt with goals
            # in the same way we deal with operator preconditions etc.,
            # where static facts disappear during grounding. So change
            # this when the goal code is refactored (also below). (**)
            if (condition.get(var) is not None and
                    val not in condition.get(var)):
                # Conflicting conditions on this variable: Operator invalid.
                return None
            condition[var] = set([val])

    def number_of_values(var_vals_pair):
        var, vals = var_vals_pair
        return len(vals)

    for fact in conditions:
        if fact.negated:
            ## Note  Here we use a different solution than in Sec. 10.6.4
            ##       of the thesis. Compare the last sentences of the third
            ##       paragraph of the section.
            ##       We could do what is written there. As a test case,
            ##       consider Airport ADL tasks with only one airport, where
            ##       (occupied ?x) variables are encoded in a single variable,
            ##       and conditions like (not (occupied ?x)) do occur in
            ##       preconditions.
            ##       However, here we avoid introducing new derived predicates
            ##       by treat the negative precondition as a disjunctive precondition
            ##       and expanding it by "multiplying out" the possibilities.
            ##       This can lead to an exponential blow-up so it would be nice
            ##       to choose the behaviour as an option.
            done = False
            new_condition = {}
            atom = pddl.Atom(fact.predicate, fact.args)  # force positive
            for var, val in dictionary.get(atom, ()):
                # see comment (**) above
                poss_vals = set(range(ranges[var]))
                poss_vals.remove(val)

                if condition.get(var) is None:
                    assert new_condition.get(var) is None
                    new_condition[var] = poss_vals
                else:
                    # constrain existing condition on var
                    prev_possible_vals = condition.get(var)
                    done = True
                    prev_possible_vals.intersection_update(poss_vals)
                    if len(prev_possible_vals) == 0:
                        # Conflicting conditions on this variable:
                        # Operator invalid.
                        return None

            if not done and len(new_condition) != 0:
                # we did not enforce the negative condition by constraining
                # an existing condition on one of the variables representing
                # this atom. So we need to introduce a new condition:
                # We can select any from new_condition and currently prefer the
                # smalles one.
                candidates = sorted(new_condition.items(), key=number_of_values)
                var, vals = candidates[0]
                condition[var] = vals

        def multiply_out(condition):  # destroys the input
            sorted_conds = sorted(condition.items(), key=number_of_values)

            flat_conds = [{}]
            for var, vals in sorted_conds:
                if len(vals) == 1:
                    for cond in flat_conds:
                        cond[var] = vals.pop()  # destroys the input here
                else:
                    new_conds = []
                    for cond in flat_conds:
                        for val in vals:
                            new_cond = deepcopy(cond)
                            new_cond[var] = val
                            new_conds.append(new_cond)
                    flat_conds = new_conds
            return flat_conds

    return multiply_out(condition)


def translate_strips_conditions(conditions, dictionary, ranges,
                                mutex_dict, mutex_ranges):
    if not conditions:
        return [{}]  # Quick exit for common case.

    # Check if the condition violates any mutexes.
    if translate_strips_conditions_aux(
            conditions, mutex_dict, mutex_ranges) is None:
        return None

    return translate_strips_conditions_aux(conditions, dictionary, ranges)


def translate_strips_operator(operator, dictionary, ranges, mutex_dict, mutex_ranges, implied_facts,
                              aux_func_strips_to_sas, groups):
    conditions = translate_strips_conditions(operator.precondition, dictionary, ranges, mutex_dict, mutex_ranges)
    if conditions is None:
        return []
    sas_operators = []
    for condition in conditions:
        op = translate_strips_operator_aux(operator, dictionary, ranges,
                                           mutex_dict, mutex_ranges,
                                           implied_facts, condition, aux_func_strips_to_sas, groups)
        sas_operators.append(op)
    return sas_operators


def translate_strips_operator_aux(operator, dictionary, ranges, mutex_dict,
                                  mutex_ranges, implied_facts, condition, aux_func_strips_to_sas, groups):
    # NOTE: This function does not really deal with the intricacies of properly
    # encoding delete effects for grouped propositions in the presence of
    # conditional effects. It should work ok but will bail out in more
    # complicated cases even though a conflict does not necessarily exist.
    possible_add_conflict = False

    effect = {}

    for conditions, fact in operator.add_effects:
        eff_condition_list = translate_strips_conditions(conditions, dictionary,
                                                         ranges, mutex_dict,
                                                         mutex_ranges)
        if eff_condition_list is None:  # Impossible condition for this effect.
            continue
        eff_condition = [list(eff_cond.items())
                         for eff_cond in eff_condition_list]
        for var, val in dictionary[fact]:
            if condition.get(var) == val:
                # Effect implied by precondition.
                global removed_implied_effect_counter
                removed_implied_effect_counter += 1
                # print "Skipping effect of %s..." % operator.name
                continue
            effect_pair = effect.get(var)
            if not effect_pair:
                effect[var] = (val, eff_condition)
            else:
                other_val, eff_conditions = effect_pair
                # Don't flag conflict just yet... the operator might be invalid
                # because of conflicting add/delete effects (see pipesworld).
                if other_val != val:
                    possible_add_conflict = True
                eff_conditions.extend(eff_condition)

    for conditions, fact in operator.func_effects:
        eff_condition_list = translate_strips_conditions(conditions, dictionary,
                                                         ranges, mutex_dict,
                                                         mutex_ranges)
        if eff_condition_list is None:  # Impossible condition for this effect.
            continue
        eff_condition = [list(eff_cond.items())
                         for eff_cond in eff_condition_list]

        op_f = 0
        if isinstance(fact.expression, pddl.f_expression.PrimitiveNumericExpression):
            fact_exp = str(get_new_expresison(fact.expression))
            value = fact.expression.value
            if isinstance(fact, pddl.f_expression.Increase):
                op_f = -2
            elif isinstance(fact, pddl.f_expression.Decrease):
                op_f = -3
            elif isinstance(fact, pddl.f_expression.Assign):
                op_f = -4
            elif isinstance(fact, pddl.f_expression.GreaterThan):
                op_f = -5
            elif isinstance(fact, pddl.f_expression.LessThan):
                op_f = -6
        else:
            fact_exp = str(fact.expression.fluent)
            value = fact.expression.expression.value
            if isinstance(fact, pddl.f_expression.Increase):
                op_f = -2
            elif isinstance(fact, pddl.f_expression.Decrease):
                op_f = -3
            elif isinstance(fact, pddl.f_expression.Assign):
                op_f = -4
            elif isinstance(fact, pddl.f_expression.GreaterThan):
                op_f = -5
            elif isinstance(fact, pddl.f_expression.LessThan):
                op_f = -6
        fact_fluent = str(fact.fluent.fluent)
        fact_str = fact.__class__.__name__ + " " + fact_fluent + " " + fact_exp
        new_atom = aux_func_strips_to_sas[fact_str]
        # new_fluent = pddl.f_expression.PrimitiveNumericExpression(fact.fluent.fluent.symbol,
        #                                                          [pddl.conditions.Variable(arg.name) for arg in
        #                                                           fact.fluent.fluent.args])
        # new_expression = get_new_expresison(fact.expression)
        # new_increase = pddl.f_expression.Increase(new_fluent, new_expression)
        # new_atom = pddl.Atom(new_increase, fact.parameters)
        # bool1 = new_atom.args == func_bat_lit[0].args
        # bool2 = new_atom.predicate == func_bat_lit[0].predicate
        # bool4 = new_atom.__class__ == func_bat_lit[0].__class__
        # bool5 = new_atom.args == func_bat_lit[1].args
        # bool6 = new_atom.predicate == func_bat_lit[1].predicate
        # bool8 = new_atom.__class__ == func_bat_lit[1].__class__
        for var, val in dictionary[new_atom]:
            effect_pair = effect.get(var)
            if not effect_pair:
                effect[var] = ([value, var, val, op_f], eff_condition)
            else:
                if isinstance(effect_pair[0], list):
                    effect_pair[0].append(fact.expression.expression.value)

    for conditions, fact in operator.del_effects:
        eff_condition_list = translate_strips_conditions(conditions, dictionary, ranges, mutex_dict, mutex_ranges)
        if eff_condition_list is None:
            continue
        eff_condition = [list(eff_cond.items())
                         for eff_cond in eff_condition_list]
        for var, val in dictionary[fact]:
            none_of_those = ranges[var] - 1

            other_val, eff_conditions = effect.setdefault(var, (none_of_those, []))

            if other_val != none_of_those:
                # Look for matching add effect; ignore this del effect if found.
                for cond in eff_condition:
                    assert cond in eff_conditions or [] in eff_conditions, \
                        "Add effect with uncertain del effect partner?"
                if other_val == val:
                    if ALLOW_CONFLICTING_EFFECTS:
                        # Conflicting ADD and DEL effect. This is *only* allowed if
                        # this is also a precondition, in which case there is *no*
                        # effect (the ADD takes precedence). We delete the add effect here.
                        if condition.get(var) != val:
                            # HACK HACK HACK!
                            # There used to be an assertion here that actually
                            # forbid this, but this was wrong in Pipesworld-notankage
                            # (e.g. task 01). The thing is, it *is* possible for
                            # an operator with proven (with the given invariants)
                            # inconsistent preconditions to actually end up here if
                            # the inconsistency of the preconditions is not obvious at
                            # the SAS+ encoding level.
                            #
                            # Example: Pipes-Notank-01, operator
                            # (pop-unitarypipe s12 b4 a1 a2 b4 lco lco).
                            # This has precondition last(b4, s12) and on(b4, a2) which
                            # is inconsistent because b4 can only be in one place.
                            # However, the chosen encoding encodes *what is last in s12*
                            # separately, and so the precondition translates to
                            # "last(s12) = b4 and on(b4) = a2", which does not look
                            # inconsistent at first glance.
                            #
                            # Something reasonable to do here would be to make a
                            # decent check that the precondition is indeed inconsistent
                            # (using *all* mutexes), but that seems tough with this
                            # convoluted code, so we just warn and reject the operator.
                            print("Warning: %s rejected. Cross your fingers." % (
                                operator.name))
                            return None
                            assert False

                        assert eff_conditions == [[]]
                        del effect[var]
                    else:
                        assert not eff_condition[0] and not eff_conditions[0], "Uncertain conflict"
                        return None  # Definite conflict otherwise.
            else:  # no add effect on this variable
                if condition.get(var) != val:
                    if var in condition:
                        ## HACK HACK HACK! There is a precondition on the variable for
                        ## this delete effect on another value, so there is no need to
                        ## represent the delete effect. Right? Right???
                        del effect[var]
                        continue
                    for index, cond in enumerate(eff_condition_list):
                        if cond.get(var) != val:
                            # Need a guard for this delete effect.
                            assert (var not in condition and
                                    var not in eff_condition[index]), "Oops?"
                            eff_condition[index].append((var, val))
                eff_conditions.extend(eff_condition)

    if possible_add_conflict:
        operator.dump()

    assert not possible_add_conflict, "Conflicting add effects?"

    # assert eff_condition != other_condition, "Duplicate effect"
    # assert eff_condition and other_condition, "Dominated conditional effect"

    if ADD_IMPLIED_PRECONDITIONS:
        implied_precondition = set()
        for fact in condition.items():
            implied_precondition.update(implied_facts[fact])

    pre_post = []
    for var, (post, eff_condition_lists) in effect.items():
        pre = condition.pop(var, -1)
        if isinstance(post, list):
            pre = post[3]
            post = post[:-1]
            # post = post[0]
        else:
            if ranges[var] == 2:
                # Apply simplifications for binary variables.
                if prune_stupid_effect_conditions(var, post, eff_condition_lists):
                    global simplified_effect_condition_counter
                    simplified_effect_condition_counter += 1
                if (ADD_IMPLIED_PRECONDITIONS and
                        pre == -1 and (var, 1 - post) in implied_precondition):
                    global added_implied_precondition_counter
                    added_implied_precondition_counter += 1
                    pre = 1 - post
                    # print "Added precondition (%d = %d) to %s" % (
                    #     var, pre, operator.name)
        for eff_condition in eff_condition_lists:
            pre_post.append((var, pre, post, eff_condition))
    prevail = list(condition.items())

    return sas_tasks.SASOperator(operator.name, prevail, pre_post, operator.cost)


def get_new_expresison(expression):
    if isinstance(expression, pddl.f_expression.Assign):
        if expression.fluent.symbol == "*" or expression.fluent.symbol == "/" or expression.fluent.symbol == "-" \
                or expression.fluent.symbol == "+":
            param1 = get_new_expresison(pddl.f_expression.PrimitiveNumericExpression(expression.fluent.args[0].name,
                                                                                     expression.fluent.args[0].args))
            param2 = get_new_expresison(pddl.f_expression.PrimitiveNumericExpression(expression.fluent.args[1].name,
                                                                                     expression.fluent.args[1].args))
            return pddl.f_expression.PrimitiveNumericExpression(expression.fluent.symbol, [param1, param2])
        else:
            return pddl.f_expression.PrimitiveNumericExpression(expression.fluent.symbol,
                                                                expression.fluent.args)
    elif isinstance(expression, pddl.f_expression.PrimitiveNumericExpression):
        if expression.symbol == "*" or expression.symbol == "/" or expression.symbol == "-" \
                or expression.symbol == "+":
            param1 = get_new_expresison(pddl.f_expression.PrimitiveNumericExpression(expression.args[0].fluent.symbol,
                                                                                     expression.args[0].fluent.args))
            param2 = get_new_expresison(pddl.f_expression.PrimitiveNumericExpression(expression.args[1].fluent.symbol,
                                                                                     expression.args[1].fluent.args))
            return pddl.f_expression.PrimitiveNumericExpression(expression.symbol, [param1, param2])
        else:
            return pddl.f_expression.PrimitiveNumericExpression(expression.symbol,
                                                                expression.args)
    else:
        return expression


def prune_stupid_effect_conditions(var, val, conditions):
    ## (IF <conditions> THEN <var> := <val>) is a conditional effect.
    ## <var> is guaranteed to be a binary variable.
    ## <conditions> is in DNF representation (list of lists).
    ##
    ## We simplify <conditions> by applying two rules:
    ## 1. Conditions of the form "var = dualval" where var is the
    ##    effect variable and dualval != val can be omitted.
    ##    (If var != dualval, then var == val because it is binary,
    ##    which mesans that in such situations the effect is a no-op.)
    ## 2. If conditions contains any empty list, it is equivalent
    ##    to True and we can remove all other disjuncts.
    ##
    ## returns True when anything was changed
    if conditions == [[]]:
        return False  ## Quick exit for common case.
    assert val in [0, 1]
    dual_fact = (var, 1 - val)
    simplified = False
    for condition in conditions:
        # Apply rule 1.
        while dual_fact in condition:
            # print "*** Removing dual condition"
            simplified = True
            condition.remove(dual_fact)
        # Apply rule 2.
        if not condition:
            conditions[:] = [[]]
            simplified = True
            break
    return simplified


def translate_strips_axiom(axiom, dictionary, ranges, mutex_dict, mutex_ranges):
    conditions = translate_strips_conditions(axiom.condition, dictionary, ranges, mutex_dict, mutex_ranges)
    if conditions is None:
        return []
    if axiom.effect.negated:
        [(var, _)] = dictionary[axiom.effect.positive()]
        effect = (var, ranges[var] - 1)
    else:
        [effect] = dictionary[axiom.effect]
    axioms = []
    for condition in conditions:
        axioms.append(sas_tasks.SASAxiom(list(condition.items()), effect))
    return axioms


def translate_strips_operators(actions, strips_to_sas, ranges, mutex_dict, mutex_ranges, implied_facts,
                               aux_func_strips_to_sas, groups):
    result = []
    for action in actions:
        sas_ops = translate_strips_operator(action, strips_to_sas, ranges, mutex_dict, mutex_ranges, implied_facts,
                                            aux_func_strips_to_sas, groups)
        result.extend(sas_ops)
    return result


def duplicate_funct_effects(operators):
    for op in operators:
        if op.name.split(" ")[0][-3:] == "end":
            name1 = op.name.split(" ")[0].split("_")[:-1][1:] + op.name.split(" ")[1:]
            for n_var_no, n_pre_spec, n_post, n_cond in op.pre_post:
                if n_pre_spec == -2 or n_pre_spec == -3 or n_pre_spec == -4:
                    for op2 in operators:
                        if op2.name.split(" ")[0][-5:] == "start":
                            name2 = op2.name.split(" ")[0].split("_")[:-1][1:] + op2.name.split(" ")[1:]
                            if name1 == name2:
                                op2.pre_post.append([n_var_no, n_pre_spec, n_post, n_cond])


def translate_strips_axioms(axioms, strips_to_sas, ranges, mutex_dict, mutex_ranges):
    result = []
    for axiom in axioms:
        sas_axioms = translate_strips_axiom(axiom, strips_to_sas, ranges, mutex_dict, mutex_ranges)
        result.extend(sas_axioms)
    return result


def translate_task(strips_to_sas, ranges, mutex_dict, mutex_ranges, init, goals,
                   actions, axioms, metric, implied_facts, aux_func_strips_to_sas, groups):
    with timers.timing("Processing axioms", block=True):
        axioms, axiom_init, axiom_layer_dict = axiom_rules.handle_axioms(
            actions, axioms, goals)
    init = init + axiom_init
    # axioms.sort(key=lambda axiom: axiom.name)
    # for axiom in axioms:
    #  axiom.dump()

    init_values = [rang - 1 for rang in ranges]
    # Closed World Assumption: Initialize to "range - 1" == Nothing.
    for fact in init:
        pair = strips_to_sas.get(fact)
        pairs = strips_to_sas.get(fact, [])  # empty for static init facts
        for var, val in pairs:
            assert init_values[var] == ranges[var] - 1, "Inconsistent init facts!"
            init_values[var] = val
    init = sas_tasks.SASInit(init_values)

    goal_dict_list = translate_strips_conditions(goals, strips_to_sas, ranges, mutex_dict, mutex_ranges)
    assert len(goal_dict_list) == 1, "Negative goal not supported"
    ## we could substitute the negative goal literal in
    ## normalize.substitute_complicated_goal, using an axiom. We currently
    ## don't do this, because we don't run into this assertion, if the
    ## negative goal is part of finite domain variable with only two
    ## values, which is most of the time the case, and hence refrain from
    ## introducing axioms (that are not supported by all heuristics)
    goal_pairs = list(goal_dict_list[0].items())
    goal = sas_tasks.SASGoal(goal_pairs)

    operators = translate_strips_operators(actions, strips_to_sas, ranges, mutex_dict, mutex_ranges, implied_facts,
                                           aux_func_strips_to_sas, groups)
    duplicate_funct_effects(operators)
    axioms = translate_strips_axioms(axioms, strips_to_sas, ranges, mutex_dict, mutex_ranges)

    axiom_layers = [-1] * len(ranges)
    for atom, layer in axiom_layer_dict.items():
        assert layer >= 0
        [(var, val)] = strips_to_sas[atom]
        axiom_layers[var] = layer
    variables = sas_tasks.SASVariables(ranges, axiom_layers)

    return sas_tasks.SASTask(variables, init, goal, operators, axioms, metric, [])


def set_function_values(operators, groups, mutex_groups):
    for operator in operators:
        for effect in operator.pre_post:
            if effect[1] == -2 or effect[1] == -3 or effect[1] == -4:
                groups[effect[0]][effect[2][2]].value = effect[2][0]
            # mutex_groups[effect[0]][effect[2][2]].value = effect[2][0]
    return


def obtain_metric_functions(groups, sas_task):
    sas_task.translated_metric = {}
    sas_task.translated_metric_vals = {}
    for metric_elem in sas_task.metric[1:]:
        gopup_index = 0
        for group in groups:
            if isinstance(group[0].predicate, pddl.f_expression.Increase) or \
                    isinstance(group[0].predicate, pddl.f_expression.Decrease) or \
                    isinstance(group[0].predicate, pddl.f_expression.Assign):
                if metric_elem.symbol == "*":
                    if metric_elem.args[1].name == group[0].predicate.fluent.symbol:
                        arg_index = 0
                        equal = True
                        for arg_elem in metric_elem.args[1].args:
                            if arg_elem.name != group[0].predicate.fluent.args[arg_index].name:
                                equal = False
                            arg_index = arg_index + 1
                        if equal:
                            sas_task.translated_metric[gopup_index] = metric_elem.args[1]
                            sas_task.translated_metric_vals[gopup_index] = float(metric_elem.args[0].name)
                elif metric_elem.symbol == "/":
                    if metric_elem.args[1].name == group[0].predicate.fluent.symbol:
                        arg_index = 0
                        equal = True
                        for arg_elem in metric_elem.args[1].args:
                            if arg_elem.name != group[0].predicate.fluent.args[arg_index].name:
                                equal = False
                            arg_index = arg_index + 1
                        if equal:
                            sas_task.translated_metric[gopup_index] = metric_elem.args[1]
                            sas_task.translated_metric_vals[gopup_index] = 1/float(metric_elem.args[0].name)
                elif metric_elem.symbol == group[0].predicate.fluent.symbol:
                    arg_index = 0
                    equal = True
                    for arg_elem in metric_elem.args:
                        if arg_elem.name != group[0].predicate.fluent.args[arg_index].name:
                            equal = False
                        arg_index = arg_index + 1
                    if equal:
                        sas_task.translated_metric[gopup_index] = metric_elem
                        sas_task.translated_metric_vals[gopup_index] = 1
            gopup_index = gopup_index + 1


def unsolvable_sas_task(msg):
    print("%s! Generating unsolvable task..." % msg)
    write_translation_key([])
    write_mutex_key([])
    variables = sas_tasks.SASVariables([2], [-1])
    init = sas_tasks.SASInit([0])
    goal = sas_tasks.SASGoal([(0, 1)])
    operators = []
    axioms = []
    metric = True
    return sas_tasks.SASTask(variables, init, goal, operators, axioms, metric, [])


def pddl_to_sas(task):
    with timers.timing("Instantiating", block=True):
        (relaxed_reachable, atoms, functions, actions, axioms,
         reachable_action_params) = instantiate.explore(task)

    if not relaxed_reachable:
        return unsolvable_sas_task("No relaxed solution")

    # HACK! Goals should be treated differently.
    if isinstance(task.goal, pddl.Conjunction):
        goal_list = task.goal.parts
    else:
        goal_list = [task.goal]
    for item in goal_list:
        assert isinstance(item, pddl.Literal)

    with timers.timing("Computing fact groups", block=True):
        groups, mutex_groups, translation_key, group_const_arg = fact_groups.compute_groups(
            task, atoms, functions, reachable_action_params,
            partial_encoding=USE_PARTIAL_ENCODING)

    with timers.timing("Building STRIPS to SAS dictionary"):
        ranges, strips_to_sas, aux_func_strips_to_sas = strips_to_sas_dictionary(
            groups, assert_partial=USE_PARTIAL_ENCODING)

    with timers.timing("Building dictionary for full mutex groups"):
        mutex_ranges, mutex_dict, aux_func_mutex_dict = strips_to_sas_dictionary(
            mutex_groups, assert_partial=False)

    if ADD_IMPLIED_PRECONDITIONS:
        with timers.timing("Building implied facts dictionary..."):
            implied_facts = build_implied_facts(strips_to_sas, groups, mutex_groups)
    else:
        implied_facts = {}

    with timers.timing("Translating task", block=True):
        sas_task = translate_task(
            strips_to_sas, ranges, mutex_dict, mutex_ranges,
            task.init, goal_list, actions, axioms, task.metric,
            implied_facts, aux_func_strips_to_sas, groups)

    print("%d implied effects removed" % removed_implied_effect_counter)
    print("%d effect conditions simplified" % simplified_effect_condition_counter)
    print("%d implied preconditions added" % added_implied_precondition_counter)

    obtain_metric_functions(groups, sas_task)
    set_function_values(sas_task.operators, groups, mutex_groups)

    with timers.timing("Building mutex information", block=True):
        mutex_key = build_mutex_key(strips_to_sas, mutex_groups)

    if DETECT_UNREACHABLE:
        with timers.timing("Detecting unreachable propositions", block=True):
            try:
                simplify.filter_unreachable_propositions(
                    sas_task, mutex_key, translation_key)
            except simplify.Impossible:
                return unsolvable_sas_task("Simplified to trivially false goal")

    with timers.timing("Writing translation key"):
        write_translation_key(translation_key)
    with timers.timing("Writing mutex key"):
        write_mutex_key(mutex_key)

    # agents_pred = graphs.get_agent_elements(task, strips_to_sas)
    # agents_pred_dics = graphs.get_agents_pred_dicts(agents_pred, strips_to_sas)
    # agent_minimal_vars = graphs.get_agents_minimal_variables(agents_pred)

    free_agent_index = graphs.find_free_agent_index(groups)
    dtgs = graphs.create_groups_dtgs(sas_task)
    translated_dtgs = graphs.translate_groups_dtgs(dtgs, translation_key)
    (casual_graph, casual_graph_type1, casual_graph_type2,
     propositional_casual_graph, propositional_casual_graph_type1,
     propositional_casual_graph_type2) = graphs.create_casual_graph(sas_task, groups, group_const_arg, free_agent_index,
                                                                    SIMPLIFIED_CASUAL_GRAPH)

    graphs.create_gexf_casual_graph_files(casual_graph, 0)
    graphs.create_gexf_casual_graph_files(casual_graph_type1, 1)
    graphs.create_gexf_casual_graph_files(casual_graph_type2, 2)
    graphs.create_gexf_casual_graph_files(propositional_casual_graph, 3)
    graphs.create_gexf_casual_graph_files(propositional_casual_graph_type1, 4)
    graphs.create_gexf_casual_graph_files(propositional_casual_graph_type2, 5)

    propositional_casual_graph_type1_simple1 = graphs.remove_two_way_cycles(deepcopy(propositional_casual_graph_type1))
    graphs.create_gexf_casual_graph_files(propositional_casual_graph_type1_simple1, 6)
    propositional_casual_graph_type1_simple2 = graphs.remove_three_way_cycles(
        deepcopy(propositional_casual_graph_type1_simple1))
    graphs.create_gexf_casual_graph_files(propositional_casual_graph_type1_simple2, 7)

    origin_nodes = graphs.obtain_origin_nodes(propositional_casual_graph_type1_simple2)

    basic_agents = graphs.fill_basic_agents(origin_nodes, propositional_casual_graph)
    basic_agents = graphs.assemble_basic_agents(basic_agents, group_const_arg)
    joint_agents = graphs.fill_joint_agents(basic_agents, propositional_casual_graph, 5)
    joint_final_agents = graphs.fill_remaining_agents(joint_agents, propositional_casual_graph, groups, group_const_arg)
    free_joint_agents = graphs.fill_free_agents(joint_final_agents, groups, free_agent_index)
    functional_agents = graphs.fill_func_agents(free_joint_agents, casual_graph, 2)
    agents_actions, extern_actions, shared_nodes = graphs.fill_agents_actions(basic_agents, joint_final_agents,
                                                                              functional_agents, casual_graph,
                                                                              sas_task, groups)
    agents_metric = graphs.fill_agents_metric(joint_agents, functional_agents, sas_task)
    agents_init = graphs.fill_agents_init(joint_agents, functional_agents, sas_task)
    agents_goals = graphs.fill_agents_goals(joint_agents, functional_agents, agents_actions, agents_metric, agents_init,
                                            casual_graph, sas_task, groups)

    # Create new tasks
    agent_tasks = []
    agent_index = 0
    for _ in basic_agents:

        if len(agents_goals[agent_index]) == 0:
            agent_index = agent_index + 1
            continue

        axiom_layers = [-1] * len(functional_agents[agent_index])
        vars = {}
        for var in functional_agents[agent_index]:
            vars[var] = len(groups[var])
        variables = sas_tasks.SASVariables(vars, axiom_layers)
        init = sas_tasks.SASInit(agents_init[agent_index])
        goal = sas_tasks.SASGoal(agents_goals[agent_index])

        new_task = sas_tasks.SASTask(variables, init,
                                     goal, agents_actions[agent_index], [],
                                     agents_metric[agent_index], shared_nodes)

        agent_tasks.append(new_task)
        agent_index = agent_index + 1

    mutex_keys = build_mutex_keys(strips_to_sas, mutex_groups, agent_tasks)
    write_mutex_keys(mutex_keys)

    fdtgs = graphs.create_functional_dtgs(sas_task, translation_key, groups)
    fdtgs_per_invariant = graphs.create_functional_dtgs_per_invariant(sas_task, translation_key, groups)
    fdtg_metric = graphs.create_functional_dtg_metric(sas_task, translation_key, groups)
    fdtgs_metric = graphs.create_functional_dtgs_metric(sas_task, translation_key, groups)

    graphs.create_csv_transition_graphs_files(translated_dtgs, groups)
    graphs.create_gexf_transition_graphs_files(translated_dtgs, groups)
    graphs.create_gexf_transition_functional_graphs_files(fdtgs)
    graphs.create_gexf_transition_functional_metric_graph_files(fdtg_metric)
    graphs.create_gexf_transition_functional_metric_graphs_files(fdtgs_metric)
    graphs.create_gexf_transition_functional_per_inv_graphs_files(fdtgs_per_invariant)

    set_func_init_value(sas_task, agent_tasks, task, groups)

    return sas_task, agent_tasks, groups


def set_func_init_value(sas_task, agent_tasks, task, groups):
    for init_val in task.init:
        index = 0
        for init_sas_val in sas_task.init.values:
            group = groups[index]
            if not isinstance(group[0].predicate, str) and not isinstance(init_val, pddl.Atom) and \
                    group[0].predicate.fluent.symbol == init_val.fluent.symbol:
                arg_index = 0
                equal = True
                for arg in init_val.fluent.args:
                    if group[0].predicate.fluent.args[arg_index].name != arg.name:
                        equal = False
                        break
                    arg_index = arg_index + 1

                if equal:
                    sas_task.init.values[index] = init_val.expression.value
            index = index + 1

        for agent_task in agent_tasks:
            for init_sas_val_key, init_sas_val in agent_task.init.values.items():
                group = groups[init_sas_val_key]
                if not isinstance(group[0].predicate, str) and not isinstance(init_val, pddl.Atom) and \
                        group[0].predicate.fluent.symbol == init_val.fluent.symbol:
                    arg_index = 0
                    equal = True
                    for arg in init_val.fluent.args:
                        if group[0].predicate.fluent.args[arg_index].name != arg.name:
                            equal = False
                            break
                        arg_index = arg_index + 1

                    if equal:
                        agent_task.init.values[init_sas_val_key] = init_val.expression.value





def build_mutex_key(strips_to_sas, groups):
    group_keys = []
    for group in groups:
        group_key = []
        for fact in group:
            if strips_to_sas.get(fact):
                for var, val in strips_to_sas[fact]:
                    group_key.append((var, val, str(fact)))
            else:
                print("not in strips_to_sas, left out:", fact)
        group_keys.append(group_key)
    return group_keys


def build_mutex_keys(strips_to_sas, groups, tasks):
    mutex_keys = []
    for task in tasks:
        group_keys = []
        for group in groups:
            group_key = []
            for fact in group:
                if strips_to_sas.get(fact):
                    for var, val in strips_to_sas[fact]:
                        if var in task.variables.ranges.keys():
                            group_key.append((var, val, str(fact)))
                else:
                    print("not in strips_to_sas, left out:", fact)
            if group_key:
                group_keys.append(group_key)
        mutex_keys.append(group_keys)
    return mutex_keys


def build_implied_facts(strips_to_sas, groups, mutex_groups):
    ## Compute a dictionary mapping facts (FDR pairs) to lists of FDR
    ## pairs implied by that fact. In other words, in all states
    ## containing p, all pairs in implied_facts[p] must also be true.
    ##
    ## There are two simple cases where a pair p implies a pair q != p
    ## in our FDR encodings:
    ## 1. p and q encode the same fact
    ## 2. p encodes a STRIPS proposition X, q encodes a STRIPS literal
    ##    "not Y", and X and Y are mutex.
    ##
    ## The first case cannot arise when we use partial encodings, and
    ## when we use full encodings, I don't think it would give us any
    ## additional information to exploit in the operator translation,
    ## so we only use the second case.
    ##
    ## Note that for a pair q to encode a fact "not Y", Y must form a
    ## fact group of size 1. We call such propositions Y "lonely".

    ## In the first step, we compute a dictionary mapping each lonely
    ## proposition to its variable number.
    lonely_propositions = {}
    for var_no, group in enumerate(groups):
        if len(group) == 1:
            lonely_prop = group[0]
            assert strips_to_sas[lonely_prop] == [(var_no, 0)]
            lonely_propositions[lonely_prop] = var_no

    ## Then we compute implied facts as follows: for each mutex group,
    ## check if prop is lonely (then and only then "not prop" has a
    ## representation as an FDR pair). In that case, all other facts
    ## in this mutex group imply "not prop".
    implied_facts = defaultdict(list)
    for mutex_group in mutex_groups:
        for prop in mutex_group:
            prop_var = lonely_propositions.get(prop)
            if prop_var is not None:
                prop_is_false = (prop_var, 1)
                for other_prop in mutex_group:
                    if other_prop is not prop:
                        for other_fact in strips_to_sas[other_prop]:
                            implied_facts[other_fact].append(prop_is_false)

    return implied_facts


def write_translation_key(translation_key):
    groups_file = open("/home/javier/Desktop/planners/outPreprocess/test.groups", "w")
    for var_no, var_key in enumerate(translation_key):
        print("var%d:" % var_no, file=groups_file)
        for value, value_name in enumerate(var_key):
            print("  %d: %s" % (value, value_name), file=groups_file)
    groups_file.close()


def write_mutex_key(mutex_key):
    invariants_file = open("/home/javier/Desktop/planners/outPreprocess/all.groups", "w")
    print("begin_groups", file=invariants_file)
    print(len(mutex_key), file=invariants_file)
    for group in mutex_key:
        # print map(str, group)
        no_facts = len(group)
        print("group", file=invariants_file)
        print(no_facts, file=invariants_file)
        for var, val, fact in group:
            # print fact
            assert str(fact).startswith("Atom ")
            if ("Increase" in str(fact) or
                    "Decrease" in str(fact) or
                    "GreaterThan" in str(fact) or
                    "LessThan" in str(fact)):
                predicate = str(fact)[5:].split("<")[0]
                pred_args_str = str(fact).split("<")[1][1:][:-1]
                if not pred_args_str == "":
                    # print "there are args" , pred_args_str
                    pred_args = pred_args_str.split(",")
                else:
                    pred_args = []
                print_line = "%d %d %s > %d " % (var, val, predicate, len(pred_args))
                for arg in pred_args:
                    print_line += str(arg).strip() + " "
            elif fact.find(":=") != -1:
                predicate = "Assign " + (str(fact)[5:].split("<")[0].split(":=")[0])[:-1] + ">" + \
                            (str(fact)[5:].split("<")[0].split(":=")[1])[1:]
                pred_args_str = str(fact).split("<")[1][1:][:-1]
                if not pred_args_str == "":
                    # print "there are args" , rest
                    pred_args = pred_args_str.split(",")
                else:
                    pred_args = []
                print_line = "%d %d %s > %d " % (var, val, predicate, len(pred_args))
                for arg in pred_args:
                    print_line += str(arg).strip() + " "
            else:
                predicate = str(fact)[5:].split("(")[0]
                # print predicate
                rest = str(fact).split("(")[1]
                rest = rest.strip(")").strip()
                if not rest == "":
                    # print "there are args" , rest
                    args = rest.split(",")
                else:
                    args = []
                print_line = "%d %d %s %d " % (var, val, predicate, len(args))
                for arg in args:
                    print_line += str(arg).strip() + " "
            # print fact
            # print print_line
            print(print_line, file=invariants_file)
    print("end_groups", file=invariants_file)
    invariants_file.close()


def write_mutex_keys(mutex_keys):
    index = 0
    for mutex_key in mutex_keys:
        invariants_file = open("/home/javier/Desktop/planners/outPreprocess/agent" + str(index) + ".groups", "w")
        print("begin_groups", file=invariants_file)
        print(len(mutex_key), file=invariants_file)
        for group in mutex_key:
            # print map(str, group)
            no_facts = len(group)
            print("group", file=invariants_file)
            print(no_facts, file=invariants_file)
            for var, val, fact in group:
                # print fact
                assert str(fact).startswith("Atom ")
                if ("Increase" in str(fact) or
                        "Decrease" in str(fact) or
                        "GreaterThan" in str(fact) or
                        "LessThan" in str(fact)):
                    predicate = str(fact)[5:].split("<")[0]
                    pred_args_str = str(fact).split("<")[1][1:][:-1]
                    if not pred_args_str == "":
                        # print "there are args" , pred_args_str
                        pred_args = pred_args_str.split(",")
                    else:
                        pred_args = []
                    print_line = "%d %d %s > %d " % (var, val, predicate, len(pred_args))
                    for arg in pred_args:
                        print_line += str(arg).strip() + " "
                elif fact.find(":=") != -1:
                    predicate = "Assign " + (str(fact)[5:].split("<")[0].split(":=")[0])[:-1] + ">" + \
                                (str(fact)[5:].split("<")[0].split(":=")[1])[1:]
                    pred_args_str = str(fact).split("<")[1][1:][:-1]
                    if not pred_args_str == "":
                        # print "there are args" , rest
                        pred_args = pred_args_str.split(",")
                    else:
                        pred_args = []
                    print_line = "%d %d %s > %d " % (var, val, predicate, len(pred_args))
                    for arg in pred_args:
                        print_line += str(arg).strip() + " "
                else:
                    predicate = str(fact)[5:].split("(")[0]
                    # print predicate
                    rest = str(fact).split("(")[1]
                    rest = rest.strip(")").strip()
                    if not rest == "":
                        # print "there are args" , rest
                        args = rest.split(",")
                    else:
                        args = []
                    print_line = "%d %d %s %d " % (var, val, predicate, len(args))
                    for arg in args:
                        print_line += str(arg).strip() + " "
                # print fact
                # print print_line
                print(print_line, file=invariants_file)
        print("end_groups", file=invariants_file)
        invariants_file.close()
        index = index + 1


if __name__ == "__main__":
    import pddl

    timer = timers.Timer()
    with timers.timing("Parsing"):
        durative_task = pddl.open_pddl_file()

    # EXPERIMENTAL!
    # import psyco
    # psyco.full()

    # Translate durative task to snap actions task
    snap_task = snap_actions.task_snap_translate(durative_task)

    sas_task, agent_tasks, groups = pddl_to_sas(snap_task)

    print("Files will be stored in: /home/javier/Desktop/planners/outPreprocess")
    with timers.timing("Writing output"):
        sas_task.output(open("/home/javier/Desktop/planners/outPreprocess/output.sas", "w"), groups)

        agent_index = 0
        for task in agent_tasks:
            name = "agent" + str(agent_index)
            task.outputma(open("/home/javier/Desktop/planners/outPreprocess/output_agent" + str(agent_index) + ".sas",
                               "w"), name, groups, agent_index)
            agent_index = agent_index + 1

    print("Done! %s" % timer)
