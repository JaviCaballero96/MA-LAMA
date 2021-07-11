import sys
import io

import pddl.actions as act
import pddl.effects as eff
import pddl.conditions as cond
import pddl.durative_actions
import pddl.tasks as tasks


def task_snap_translate(task):
    # Obtain the actions at start and end
    start_actions = obtain_start_snap_actions(task.actions)
    end_actions = obtain_end_snap_actions(task.actions)
    all_actions = start_actions + end_actions

    return tasks.Task(task.domain_name, task.task_name, task.requirements, task.types, task.objects,
                      task.predicates, task.functions, task.init, task.goal, all_actions, task.axioms,
                      task.metric)


def obtain_start_snap_actions(all_actions):
    start_actions = []

    # Iterate over actions: conditions and effects
    for action in all_actions:
        effects_list = []
        preconditions_list = []

        for condition in action.conditions.parts:
            if condition.tmp == "start" or condition.tmp == "all":
                preconditions_list.append(condition)

        if isinstance(action.conditions, cond.Conjunction):
            preconditions = cond.Conjunction(preconditions_list)
        elif isinstance(action.conditions, cond.Disjunction):
            preconditions = cond.Disjunction(preconditions_list)

        for effect in action.effects:
            if effect.tmp == "start":
                effects_list.append(effect)

        start_actions.append(act.Action(action.name + "_start", action.parameters, preconditions, effects_list,
                                        action.cost))
    return start_actions


def obtain_end_snap_actions(all_actions):
    end_actions = []

    # Iterate over actions: conditions and effects
    for action in all_actions:
        effects_list = []
        preconditions_list = []

        for condition in action.conditions.parts:
            if condition.tmp == "end" or condition.tmp == "all":
                preconditions_list.append(condition)

        if isinstance(action.conditions, cond.Conjunction):
            preconditions = cond.Conjunction(preconditions_list)
        elif isinstance(action.conditions, cond.Disjunction):
            preconditions = cond.Disjunction(preconditions_list)

        for effect in action.effects:
            if effect.tmp == "end":
                effects_list.append(effect)

        end_actions.append(act.Action(action.name + "_start", action.parameters, preconditions, effects_list,
                                      action.cost))
    return end_actions
