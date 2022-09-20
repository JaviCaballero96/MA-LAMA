import sys
import io

from keyring.backends import null

import pddl.actions as act
import pddl.conditions as cond
import pddl.tasks as tasks
import pddl.predicates as pred
import pddl.effects as eff


def task_snap_translate(task):

    # Create executing actions predicates
    new_predicates = task.predicates
    create_start_end_predicates(new_predicates, task.actions)

    # Obtain the actions at start and end
    start_actions = obtain_start_snap_actions(task.actions)
    end_actions = obtain_end_snap_actions(task.actions)
    all_actions = start_actions + end_actions

    return tasks.Task(task.domain_name, task.task_name, task.requirements, task.types, task.objects,
                      new_predicates, task.functions, task.init, task.goal, all_actions, task.axioms,
                      task.metric)


def obtain_start_snap_actions(all_actions):
    start_actions = []

    # Iterate over actions: conditions and effects
    for action in all_actions:
        effects_list = []
        preconditions_list = []
        cost_list = []

        if isinstance(action.conditions, cond.Atom):
            if action.conditions.tmp == "start" or action.conditions.tmp == "all":
                preconditions_list.append(action.conditions)
        else:
            for condition in action.conditions.parts:
                if condition.tmp == "start" or condition.tmp == "all":
                    preconditions_list.append(condition)

        if isinstance(action.effects, eff.Effect):
            if action.effects.tmp == "start":
                effects_list.append(action.effects)
        else:
            for effect in action.effects:
                if effect.tmp == "start":
                    effects_list.append(effect)

        add_start_eff_cond(effects_list, action)

        if isinstance(action.conditions, cond.Conjunction):
            preconditions = cond.Conjunction(preconditions_list)
        elif isinstance(action.conditions, cond.Disjunction):
            preconditions = cond.Disjunction(preconditions_list)
        elif isinstance(action.conditions, cond.Atom):
            preconditions = cond.Conjunction(preconditions_list)

        if action.cost:
            for cost_effect in action.cost:
                if cost_effect.tmp == "start":
                    cost_list.append(cost_effect)

        new_action = act.Action(action.name + "_start", action.parameters, preconditions, effects_list,
                                cost_list)

        start_actions.append(new_action)
    return start_actions


def obtain_end_snap_actions(all_actions):
    end_actions = []

    # Iterate over actions: conditions and effects
    for action in all_actions:
        effects_list = []
        preconditions_list = []
        cost_list = []

        if isinstance(action.conditions, cond.Atom):
            if action.conditions.tmp == "end" or action.conditions.tmp == "end":
                preconditions_list.append(action.conditions)
        else:
            for condition in action.conditions.parts:
                if condition.tmp == "end" or condition.tmp == "all":
                    preconditions_list.append(condition)

        if isinstance(action.effects, eff.Effect):
            if action.effects.tmp == "end":
                effects_list.append(action.effects)
        else:
            for effect in action.effects:
                if effect.tmp == "end":
                    effects_list.append(effect)

        add_end_eff_cond(preconditions_list, effects_list, action)

        if isinstance(action.conditions, cond.Conjunction):
            preconditions = cond.Conjunction(preconditions_list)
        elif isinstance(action.conditions, cond.Disjunction):
            preconditions = cond.Disjunction(preconditions_list)
        elif isinstance(action.conditions, cond.Atom):
            preconditions = cond.Conjunction(preconditions_list)

        if action.cost:
            for cost_effect in action.cost:
                if cost_effect.tmp == "end":
                    cost_list.append(cost_effect)

        new_action = act.Action(action.name + "_end", action.parameters, preconditions, effects_list,
                                cost_list)
        end_actions.append(new_action)
    return end_actions


def create_start_end_predicates(predicates, all_actions):
    # Iterate over actions: conditions and effects
    # For every action create a predicate
    # that indicates the action has started
    for action in all_actions:
        name = action.name
        predicate = pred.Predicate(name + "_curr", action.parameters)
        predicates.append(predicate)

    return


def add_start_eff_cond(effects, action):

    # Create parameters list to update Atom list
    plist = []
    for param in action.parameters:
        plist.append(param.name)

    # Add init action effect
    simple_effect = eff.SimpleEffect(cond.Atom(action.name + "_curr", plist))
    effects.append(eff.Effect([], cond.Truth(), simple_effect.effect))

    return


def add_end_eff_cond(preconditions_list, effects, action):

    # Create parameters list to update Atom list
    plist = []
    for param in action.parameters:
        plist.append(param.name)

    # Add end action condition
    preconditions_list.append(cond.Atom(action.name + "_curr", plist))

    # Add end action negated effect
    simple_effect = eff.SimpleEffect(cond.NegatedAtom(action.name + "_curr", plist))
    effects.append(eff.Effect([], cond.Truth(), simple_effect.effect))

    return
