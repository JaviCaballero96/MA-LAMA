# -*- coding: latin-1 -*-
import itertools
import numpy

import invariant_finder
import pddl
import timers


def expand_group(group, task, reachable_facts, dict_reachable_facts):
    result = []
    for fact in group:
        try:
            pos = list(fact.args).index("?X")
        except ValueError:
            result.append(fact)
        else:
            # NOTE: This could be optimized by only trying objects of the correct
            #       type, or by using a unifier which directly generates the
            #       applicable objects. It is not worth optimizing this at this stage,
            #       though.

            imp_args = []
            for arg in fact.args:
                if arg == "?X":
                    imp_args.append("")
                else:
                    imp_args.append(arg)

            if len([a for a in fact.args if a == "?X"]) > 1:
                for pred in task.predicates:
                    if fact.predicate == pred.name:
                        predicate = pred
                        break

                arg_instanciated_obj = []
                index = 0
                for arg in fact.args:
                    arg_instanciated_obj.append([])
                    if arg == "?X":
                        for obj in task.objects:
                            if obj.type == predicate.arguments[index].type:
                                arg_instanciated_obj[index].append(obj.name)
                    else:
                        arg_instanciated_obj[index].append(arg)
                    index = index + 1

                all_possible_args = list(itertools.product(*arg_instanciated_obj))

                if fact.predicate in dict_reachable_facts:
                    if len(all_possible_args) < len(dict_reachable_facts[fact.predicate]):
                        for newargs in all_possible_args:
                            atom = pddl.Atom(fact.predicate, newargs)
                            if atom in reachable_facts:
                                result.append(atom)
                    else:
                        for d_fact in dict_reachable_facts[fact.predicate]:
                            all_ok = True
                            arg_index = 0
                            for arg in d_fact.args:
                                if arg != "" and arg != imp_args[arg_index]:
                                    all_ok = False
                                    break
                                arg_index = arg_index + 1
                            if all_ok:
                                result.append(d_fact)

            else:
                for obj in task.objects:
                    newargs = list(fact.args)
                    newargs[pos] = obj.name
                    atom = pddl.Atom(fact.predicate, newargs)
                    if atom in reachable_facts:
                        result.append(atom)
    return result


def obtaing_const_args(groups):
    const_args = []
    for group in groups:
        const_group_args = []
        for atom in group:
            for arg in atom.args:
                if "?" not in arg and arg not in const_group_args:
                    const_group_args.append(arg)
        const_args.append(const_group_args)
    return const_args


def obtaing_const_args_funcs(groups, arguments):
    for group in groups:
        const_group_args = []
        if isinstance(group[0].predicate, pddl.f_expression.Increase) or \
                isinstance(group[0].predicate, pddl.f_expression.Decrease) or \
                isinstance(group[0].predicate, pddl.f_expression.Assign) or \
                isinstance(group[0].predicate, pddl.f_expression.GreaterThan) or \
                isinstance(group[0].predicate, pddl.f_expression.LessThan):
            name = group[0].predicate.fluent.symbol
            for arg in group[0].predicate.fluent.args:
                name = name + "-" + arg.name
            const_group_args.append(name)
            arguments.append(const_group_args)
    return arguments


def obtaing_const_args_extra(groups, arguments, reachable_facts):
    arguments_extra = []
    arguments_extra_list = []
    to_remove_list = []
    for group in groups:
        if not isinstance(group[0].predicate, str):
            arguments_extra.append([group[0].predicate.fluent.symbol])
            for arg in group[0].predicate.fluent.args:
                arguments_extra[-1].append(arg.name)
            to_remove_list.append([])
            continue
        cands = {}
        to_remove = []
        for atom in group:
            if atom.predicate not in cands.keys():
                cands[atom.predicate] = []
                for arg in atom.args:
                    cands[atom.predicate].append(arg)
            else:
                if "_curr" in atom.predicate:
                    for arg in atom.args:
                        if arg not in cands[atom.predicate]:
                            cands[atom.predicate].append(arg)
                else:
                    arg_index = 0
                    for arg in atom.args:
                        if cands[atom.predicate][arg_index] != arg:
                            # if arg in cands[atom.predicate]:
                            #    cands[atom.predicate].remove(arg)
                            exists = False
                            for elem in to_remove:
                                if elem[0] == atom.predicate and elem[1] == arg:
                                    exists = True
                            if not exists:
                                to_remove.append([atom.predicate, cands[atom.predicate][arg_index]])
                                to_remove.append([atom.predicate, arg])
                        arg_index = arg_index + 1
        arguments_extra.append(cands)
        to_remove_list.append(to_remove)

    group_index = 0
    for arg_group in arguments_extra:
        arg_list = []
        if isinstance(arg_group, list):
            arguments_extra_list.append(arg_group)
            group_index = group_index + 1
            continue
        for pred, args in arg_group.items():
            for arg in args:
                if arg not in arg_list:
                    arg_list.append(arg)

        for arg in to_remove_list[group_index]:
            if arg[1] in arg_list:
                arg_list.remove(arg[1])

        arguments_extra_list.append(arg_list)
        group_index = group_index + 1

    return arguments_extra_list


def instantiate_groups(groups, task, reachable_facts, dict_reachable_facts):
    return [expand_group(group, task, reachable_facts, dict_reachable_facts) for group in groups]


def instantiate_function_groups(groups, task, functions):
    function_group_names = {}
    for func in functions:
        key = func.predicate.fluent.symbol + str(*func.predicate.fluent.args)
        if key not in function_group_names:
            function_group_names[key] = len(groups)
            groups.append([])
        if func not in groups[function_group_names[key]]:
            groups[function_group_names[key]].append(func)
    return groups


class GroupCoverQueue:
    def __init__(self, groups, arguments, partial_encoding):
        self.partial_encoding = partial_encoding
        if groups:
            self.max_size = max([len(group) for group in groups])
            self.groups_by_size = [[] for i in range(self.max_size + 1)]
            self.arguments = [[] for i in range(self.max_size + 1)]
            self.groups_by_fact = {}
            i = 0
            for group in groups:
                group = set(group)  # Copy group, as it will be modified.
                self.groups_by_size[len(group)].append(group)
                self.arguments[len(group)].append(arguments[i])
                for fact in group:
                    self.groups_by_fact.setdefault(fact, []).append(group)
                i = i + 1
            self._update_top()
        else:
            self.max_size = 0

    def __bool__(self):
        return self.max_size > 1

    def pop(self):
        result = list(self.top)  # Copy; this group will shrink further.
        if self.partial_encoding:
            for fact in result:
                for group in self.groups_by_fact[fact]:
                    group.remove(fact)
        self._update_top()
        return result

    def _update_top(self):
        while self.max_size > 1:
            max_list = self.groups_by_size[self.max_size]
            while max_list:
                candidate = max_list.pop()
                if len(candidate) == self.max_size:
                    self.top = candidate
                    return
                self.groups_by_size[len(candidate)].append(candidate)
            self.max_size -= 1


# I don't want to remove facts that have already been covered
# Thus, partial encoding is set to false for all cases
def choose_groups(groups, reachable_facts, functions, arguments, partial_encoding=False):
    queue = GroupCoverQueue(groups, arguments, partial_encoding=partial_encoding)
    uncovered_facts = reachable_facts.copy()

    # uncovered_funcs = functions.copy()
    result = []
    i = 0
    arguments_aux = []
    while queue:
        group = queue.pop()
        uncovered_facts.difference_update(group)
        result.append(group)

    for dummy in queue.arguments:
        if len(dummy):
            for arg in dummy:
                arguments_aux.append(arg)
    arguments_aux.reverse()

    for group in groups:
        if len(group) == 1 and (isinstance(group[0].predicate, pddl.f_expression.Increase) or
                                isinstance(group[0].predicate, pddl.f_expression.Decrease) or
                                isinstance(group[0].predicate, pddl.f_expression.Assign) or
                                isinstance(group[0].predicate, pddl.f_expression.GreaterThan) or
                                isinstance(group[0].predicate, pddl.f_expression.LessThan)) and group not in result:
            result.append(group)

    print(len(uncovered_facts), "uncovered facts")
    # for fact in uncovered_facts:
    #  print fact
    result += [[fact] for fact in uncovered_facts]
    # result += [[func] for func in uncovered_funcs]
    return result, arguments_aux


def remove_func_redundant(groups, mutex_groups):
    index = 0
    removed = 0
    length = len(mutex_groups)
    for _ in range(length):
        if index >= len(groups):
            mutex_groups.pop(index - removed)
            removed = removed + 1
        index = index + 1


def build_translation_key(groups):
    group_keys = []
    for group in groups:
        group_key = [str(fact) for fact in group]
        group_key.append("<none of those>")
        group_keys.append(group_key)
    return group_keys


def collect_all_mutex_groups(groups, atoms, functions):
    # NOTE: This should be functionally identical to choose_groups
    # when partial_encoding is set to False. Maybe a future
    # refactoring could take that into account.
    all_groups = []
    uncovered_facts = atoms.copy()
    for group in groups:
        uncovered_facts.difference_update(group)
        all_groups.append(group)
    all_groups += [[fact] for fact in uncovered_facts]

    uncovered_funcs = functions.copy()
    all_groups += [[func] for func in uncovered_funcs]
    return all_groups


def get_dict_reachable_facts(reachable_facts):
    dict = {}

    for fact in reachable_facts:
        if fact.predicate not in dict.keys():
            dict[fact.predicate] = []
        dict[fact.predicate].append(fact)

    return dict

def compute_groups(task, atoms, functions, reachable_action_params, partial_encoding=False):
    groups = invariant_finder.get_groups(task, reachable_action_params)
    with timers.timing("Instantiating groups"):
        arguments = obtaing_const_args(groups)
        dict_reachable_facts = get_dict_reachable_facts(atoms)
        groups = instantiate_groups(groups, task, atoms, dict_reachable_facts)
    with timers.timing("Instantiating function groups"):
        groups = instantiate_function_groups(groups, task, functions)
        arguments = obtaing_const_args_funcs(groups, arguments)
    # TODO: I think that collect_all_mutex_groups should do the same thing
    #       as choose_groups with partial_encoding=False, so these two should
    #       be unified.
    with timers.timing("Collecting mutex groups"):
        mutex_groups = collect_all_mutex_groups(groups, atoms, functions)
    with timers.timing("Choosing groups", block=True):
        groups, arguments = choose_groups(groups, atoms, functions, arguments, partial_encoding=partial_encoding)
        arguments_ex = obtaing_const_args_extra(groups, arguments, atoms)
    with timers.timing("Removing redundant functional propositions"):
        remove_func_redundant(groups, mutex_groups)
    with timers.timing("Building translation key"):
        translation_key = build_translation_key(groups)
    return groups, mutex_groups, translation_key, arguments_ex, arguments


def get_fluents_in_runtime(groups):
    fluents_in_runtime = []
    dict_fluents_in_runtime = {}
    index = 0
    for group in groups:
        for item in group:
            if isinstance(item.predicate, pddl.f_expression.Increase) or \
                    isinstance(item.predicate, pddl.f_expression.Decrease) or \
                    isinstance(item.predicate, pddl.f_expression.Assign):
                fluents_in_runtime.append(item.predicate.fluent)
                dict_fluents_in_runtime[str(item.predicate.fluent)] = index
                break
        index = index + 1

    return fluents_in_runtime, dict_fluents_in_runtime
