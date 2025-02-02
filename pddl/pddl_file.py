#! /usr/bin/env python
# -*- coding: latin-1 -*-
import copy
import itertools
import sys
import os.path
import re
import pddl

from . import parser

from . import tasks


def parse_pddl_file(filetype, filename):
    try:
        return parser.parse_nested_list(open(filename))
    except IOError as e:
        raise SystemExit("Error: Could not read file: %s\nReason: %s." %
                         (e.filename, e))
    except parser.ParseError as e:
        raise SystemExit("Error: Could not parse %s file: %s\n" % (filetype, filename))


def open_pddl_file(task_filename=None, domain_filename=None):
    if task_filename is None:
        if len(sys.argv) != 6:
            raise SystemExit("Error: Need exactly five command line arguments.\n"
                             "Usage: %s <domain.pddl> <task.pddl> <time_to_search> <agent_decomp(y/n)> "
                             "<goal_assigment_by_timed_goals(y/n)>" % sys.argv[0])

        task_filename = sys.argv[-4]
        print("\n" + task_filename + "\n")

        time_value = sys.argv[3]
        if sys.argv[4] == "y":
            agent_decomp = True
        else:
            agent_decomp = False

        if sys.argv[5] == "y":
            assignment_by_timed_goals = True
        else:
            assignment_by_timed_goals = False

    domain_filename = sys.argv[1]

    if not domain_filename:
        dirname, basename = os.path.split(task_filename)
        domain_filename = os.path.join(dirname, "domain.pddl")
        if not os.path.exists(domain_filename) and re.match(r"p[0-9][0-9]\b", basename):
            domain_filename = os.path.join(dirname, basename[:4] + "domain.pddl")
        if not os.path.exists(domain_filename) and re.match(r"p[0-9][0-9]\b", basename):
            domain_filename = os.path.join(dirname, basename[:3] + "-domain.pddl")
        if not os.path.exists(domain_filename) and re.match(r"p[0-9][0-9]\b", basename):
            domain_filename = os.path.join(dirname, "domain_" + basename)
        if not os.path.exists(domain_filename) and basename.endswith("-problem.pddl"):
            domain_filename = os.path.join(dirname, basename[:-13] + "-domain.pddl")
        if not os.path.exists(domain_filename):
            raise SystemExit("Error: Could not find domain file using "
                             "automatic naming rules.")

    domain_pddl = parse_pddl_file("domain", domain_filename)
    task_pddl = parse_pddl_file("task", task_filename)
    return tasks.Task.parse(domain_pddl, task_pddl), time_value, agent_decomp, assignment_by_timed_goals


def remove_negative_preconditions(durative_task):
    new_init = copy.deepcopy(durative_task.init)
    new_durative_actions = copy.deepcopy(durative_task.actions)
    new_predicates = copy.deepcopy(durative_task.predicates)

    # First identify the new predicates that are needed by checking the actions
    new_predicates_str = []
    for act in durative_task.actions:
        for cond in act.conditions.parts:
            if isinstance(cond, pddl.NegatedAtom) and \
                    cond.predicate not in new_predicates_str:
                new_predicates_str.append(cond.predicate)

    if new_predicates_str:
        # Now create the new necessary predicates
        for not_pred_str in new_predicates_str:
            # Find the associated predicate
            for predicate in durative_task.predicates:
                if predicate.name == not_pred_str:
                    new_predicates.append(pddl.Predicate("not_" + not_pred_str, predicate.arguments))
                    break

        # Once this is ready, change the preconditions in all durative-actions
        # so that they use the new predicates
        for act in new_durative_actions:
            new_conditions = []
            for cond in act.conditions.parts:
                if isinstance(cond, pddl.Atom):
                    new_conditions.append(copy.deepcopy(cond))
                elif isinstance(cond, pddl.NegatedAtom):
                    new_conditions.append(pddl.Atom("not_" + cond.predicate, cond.args))
                    new_conditions[-1].tmp = cond.tmp
            act.conditions = pddl.Conjunction(new_conditions)

        # Now do the same for effects. Positive and negative effects must evolve in tandem
        for act in new_durative_actions:
            new_effects = []
            for eff in act.effects:
                if isinstance(eff, pddl.Effect):
                    # Check if this effect needs to be replicated for the negative predicate
                    if eff.literal.predicate in new_predicates_str:
                        # Create and add new "other-way" effect
                        if isinstance(eff.literal, pddl.Atom):
                            new_effects.append(pddl.Effect([],
                                                           pddl.conditions.Truth(),
                                                           pddl.NegatedAtom("not_" + eff.literal.predicate,
                                                                            eff.literal.args)
                                                           ))
                            new_effects[-1].tmp = eff.tmp
                        elif isinstance(eff.literal, pddl.NegatedAtom):
                            new_effects.append(pddl.Effect([],
                                                           pddl.conditions.Truth(),
                                                           pddl.Atom("not_" + eff.literal.predicate,
                                                                     eff.literal.args)
                                                           ))
                            new_effects[-1].tmp = eff.tmp

                new_effects.append(copy.deepcopy(eff))
            act.effects = new_effects

        # Finally, we need to add the "not_" predicates to the initial state
        # Basically, this means that every possible instance of a predicate that is not present in the init definition
        # needs to be added as a "not_" predicate to the new initial state
        for not_pred_str in new_predicates_str:
            # Check which positive propositions exist for each duplicated predicate
            positive_props = []
            for prop in durative_task.init:
                if isinstance(prop, pddl.Atom) and prop.predicate != "=":
                    if prop.predicate == not_pred_str:
                        positive_props.append(prop.args)

            # Get the predicate to know argument types
            neg_predicate = pddl.Predicate
            for pred in new_predicates:
                if ("not_" + not_pred_str) == pred.name:
                    neg_predicate = pred
                    break

            # Now we know which positive facts exist and the argument types.
            # Instantiate evey non-existent possible proposition as negated
            possible_args = []
            for elem in neg_predicate.arguments:
                possible_args.append([])
                for obj in durative_task.objects:
                    if obj.type == elem.type:
                        possible_args[-1].append(obj)

            # Get all possible combinations of the extracted arguments
            possible_args_combinations = list(list(l) for l in itertools.product(*possible_args))

            # Remove from all possible combinations the ones that are present as positive in the original initial state
            for positive_prop in positive_props:
                for arg_comb in possible_args_combinations:
                    assert (len(positive_prop) == len(arg_comb))
                    # Check if the element should be removed
                    arg_index = 0
                    equal_args = True
                    for arg_name in positive_prop:
                        if arg_name != arg_comb[arg_index].name:
                            equal_args = False
                            break

                        if equal_args:
                            # Remove arg combination
                            possible_args_combinations.remove(arg_comb)
                        arg_index = arg_index + 1

            # Finally add all new negative propositions to the new initial state
            for new_neg_args in possible_args_combinations:
                new_init.append(pddl.Atom("not_" + not_pred_str, list(arg.name for arg in new_neg_args)))

    return pddl.Task(durative_task.domain_name, durative_task.task_name, durative_task.requirements,
                     durative_task.temp_task, durative_task.types, durative_task.objects,
                     new_predicates, durative_task.functions, new_init, durative_task.init_temp,
                     durative_task.goal, new_durative_actions, durative_task.axioms,
                     durative_task.metric)


if __name__ == "__main__":
    open_pddl_file().dump()
