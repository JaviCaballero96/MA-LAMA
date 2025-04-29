import copy

import pddl
import os
import glob
import signal
import time
from simplify import DomainTransitionGraph
from datetime import date

WINDOWS = False


class DomainNode:
    def __init__(self, state, arcs):
        self.state = state
        self.arcs = arcs


class DomainCasualNode:
    def __init__(self, arcs, name, number, type1_arcs, type2_arcs, end_arcs, end_type1_arcs, end_type2_arcs):
        self.name = name
        self.number = number
        self.arcs = arcs
        self.end_arcs = end_arcs
        self.type1_arcs = type1_arcs
        self.end_type1_arcs = end_type1_arcs
        self.type2_arcs = type2_arcs
        self.end_type2_arcs = end_type2_arcs


class DomainArc:
    def __init__(self, origin_state, end_state, action):
        self.origin_state = origin_state
        self.end_state = end_state
        self.action = action


class DomainCasualArc:
    def __init__(self, origin_state, end_state, origin_state_name, end_state_name, action, arc_type, arc_id):
        self.origin_state = origin_state
        self.end_state = end_state
        self.origin_state_name = origin_state_name
        self.end_state_name = end_state_name
        self.action = action
        self.arc_type = arc_type
        self.arc_id = arc_id


class DomainTransGraph:
    def __init__(self, init, var_group, node_list):
        self.init = init
        self.var_group = var_group
        self.node_list = node_list


class DomainCasualGraph:
    def __init__(self, node_list):
        self.node_list = node_list


class EstimatedMetricNode:
    def __init__(self, app_actions, curr_state, estimated_metric, pending_additions, achieved_subgoals):
        self.app_actions = app_actions
        self.curr_state = curr_state
        self.estimated_metric = estimated_metric
        self.pending_additions = pending_additions
        self.achieved_subgoals = achieved_subgoals


def get_agent_elements(task, strips_to_sas):
    agents = [agent for agent in task.objects if agent.type == "agent"]
    agent_predicates = [agents]
    for agent in agents:
        agent_preds = []
        for pred in strips_to_sas:
            if isinstance(pred.predicate, str):
                if agent.name in pred.args:
                    agent_preds.append(pred)
        agent_predicates.append(agent_preds)
    return agent_predicates


def get_agents_pred_dicts(agents_pred, strips_to_sas):
    agents_pred_dict = [agents_pred[0]]
    for pred_list in agents_pred[1:]:
        dist_list_aux = []
        for atom in pred_list:
            dist_list_aux.append(strips_to_sas[atom])
        agents_pred_dict.append(dist_list_aux)
    return agents_pred_dict


def get_agents_minimal_variables(agents_pred):
    agent_minimal_vars = [agents_pred[0]]
    agent = 0
    for pred_list in agents_pred[1:]:
        agent_min_var_dict = {}
        agent_min_var_list = []
        for atom in pred_list:
            if "_curr" in atom.predicate:
                continue
            if not (atom.predicate in agent_min_var_list):
                agent_min_var_dict[atom.predicate] = [atom]
                agent_min_var_list.append(atom.predicate)
            else:
                agent_min_var_dict[atom.predicate].append(atom)
        agent = agent + 1
        agent_minimal_vars.append(agent_min_var_dict)
    return agent_minimal_vars


def find_free_agent_index(groups):
    index = 0
    for group in groups:
        for state in group:
            if state.predicate == "free_agent":
                return index
        index = index + 1
    return -10


def create_groups_dtgs(task):
    init_vals = task.init.values
    sizes = task.variables.ranges
    dtgs = [DomainTransitionGraph(init, size)
            for (init, size) in zip(init_vals, sizes)]

    def add_arc(var_no, pre_spec, post, op):
        if pre_spec == -1:
            pre_values = set(range(sizes[var_no])).difference([post])
        else:
            pre_values = [pre_spec]
        for pre in pre_values:
            if isinstance(post, list):
                dtgs[var_no].add_arc(pre, post[2])
                dtgs[var_no].add_named_arc(pre, post[2], op)
            else:
                dtgs[var_no].add_arc(pre, post)
                dtgs[var_no].add_named_arc(pre, post, op)

    for op in task.operators:
        for var_no, pre_spec, post, cond in op.pre_post:
            if pre_spec != -7 and pre_spec != -8:
                add_arc(var_no, pre_spec, post, op)
    for axiom in task.axioms:
        var_no, val = axiom.effect
        add_arc(var_no, -1, val, op)

    return dtgs


def create_groups_dtgs_per_agent(task):
    init_vals = task.init.values
    sizes = task.variables.ranges
    # dtgs = [DomainTransitionGraph(init, size)
    #        for (init, size) in zip(init_vals, sizes)]

    dtgs = {}
    for init_val_key in list(init_vals.keys()):
        dtgs[init_val_key] = DomainTransitionGraph(init_vals[init_val_key], sizes[init_val_key])

    def add_arc(var_no, pre_spec, post, op):
        if pre_spec == -1:
            pre_values = set(range(sizes[var_no])).difference([post])
        else:
            pre_values = [pre_spec]
        for pre in pre_values:
            if isinstance(post, list):
                dtgs[var_no].add_arc(pre, post[2])
                dtgs[var_no].add_named_arc(pre, post[2], op)
            else:
                dtgs[var_no].add_arc(pre, post)
                dtgs[var_no].add_named_arc(pre, post, op)

    for op in task.operators:
        for var_no, pre_spec, post, cond in op.pre_post:
            if var_no in list(init_vals.keys()) and pre_spec != -7 and pre_spec != -8:
                add_arc(var_no, pre_spec, post, op)
    for axiom in task.axioms:
        var_no, val = axiom.effect
        if var_no in list(init_vals.keys()):
            add_arc(var_no, -1, val, op)

    return dtgs


def translate_groups_dtgs(dtgs, translation_key):
    translated_dtgs = []
    index = 0
    for dtg in dtgs:
        graph = DomainTransGraph(translation_key[index][dtg.init], translation_key[index], [])
        var_index = 0
        for var in translation_key[index]:
            node = DomainNode(var, [])
            for arc in dtg.named_arcs[var_index]:
                node.arcs.append(DomainArc(translation_key[index][var_index], translation_key[index][arc.end_state],
                                           arc.action.name))
            var_index = var_index + 1
            graph.node_list.append(node)
        translated_dtgs.append(graph)
        index = index + 1

    return translated_dtgs


def translate_groups_dtgs_per_agent(dtgs, translation_key):
    translated_dtgs = {}
    index = 0
    for dtg_key, dtg in dtgs.items():
        graph = DomainTransGraph(translation_key[dtg_key][dtg.init], translation_key[dtg_key], [])
        var_index = 0
        for var in translation_key[dtg_key]:
            node = DomainNode(var, [])
            for arc in dtg.named_arcs[var_index]:
                node.arcs.append(DomainArc(translation_key[dtg_key][var_index], translation_key[dtg_key][arc.end_state],
                                           arc.action.name))
            var_index = var_index + 1
            graph.node_list.append(node)
        translated_dtgs[dtg_key] = graph
        index = index + 1

    return translated_dtgs


def create_functional_dtgs(sas_task, translation_key, groups):
    fdtgs = []
    index = 0
    for group in groups:

        # Check if the group is functional
        if not (isinstance(group[0].predicate, pddl.f_expression.Increase) or
                isinstance(group[0].predicate, pddl.f_expression.Assign) or
                isinstance(group[0].predicate, pddl.f_expression.Decrease) or
                isinstance(group[0].predicate, pddl.f_expression.GreaterThan) or
                isinstance(group[0].predicate, pddl.f_expression.LessThan)):
            index = index + 1
            continue

        node_dict = {}
        node_names = []
        for op in sas_task.operators:
            eff_index_1 = 0
            for n_var_no, n_pre_spec, n_post, n_cond in op.pre_post:
                if (n_pre_spec == -2 or n_pre_spec == -3 or n_pre_spec == -4) \
                        and n_var_no == index:
                    eff_index_2 = 0
                    for var_no, pre_spec, post, cond in op.pre_post:
                        if eff_index_1 != eff_index_2 and (pre_spec != -2 and pre_spec != -3 and pre_spec != -4
                                                           and pre_spec != -5 and pre_spec != -6
                                                           and pre_spec != -7 and pre_spec != -8):
                            if translation_key[var_no][pre_spec] != '<none of those>':
                                arc_pre_name = translation_key[var_no][pre_spec]
                                arc_pre_name = arc_pre_name.replace("<", "--")
                                arc_post_name = translation_key[var_no][post]
                                arc_post_name = arc_post_name.replace("<", "--")

                                if arc_pre_name not in node_names:
                                    node_dict[arc_pre_name] = []
                                    node_names.append(arc_pre_name)
                                if arc_post_name not in node_names:
                                    node_dict[arc_post_name] = []
                                    node_names.append(arc_post_name)

                                arc_act_name = translation_key[n_var_no][n_post[2]]
                                arc_act_name = arc_act_name.replace("<", "--")
                                arc_act_name = arc_act_name.replace(">", "--")
                                node_dict[translation_key[var_no][pre_spec]].append(
                                    DomainArc(arc_pre_name, arc_post_name,
                                              arc_act_name))
                        eff_index_2 = eff_index_2 + 1
                eff_index_1 = eff_index_1 + 1

        fdtgs.append(DomainTransGraph(0, index, node_dict))
        index = index + 1

    return fdtgs


def create_functional_dtgs_per_agent(sas_task, translation_key, groups):
    fdtgs = []
    index = 0
    for group in groups:

        if index not in list(sas_task.init.values.keys()):
            index = index + 1
            continue

        # Check if the group is functional
        if not (isinstance(group[0].predicate, pddl.f_expression.Increase) or
                isinstance(group[0].predicate, pddl.f_expression.Assign) or
                isinstance(group[0].predicate, pddl.f_expression.Decrease) or
                isinstance(group[0].predicate, pddl.f_expression.GreaterThan) or
                isinstance(group[0].predicate, pddl.f_expression.LessThan)):
            index = index + 1
            continue

        node_dict = {}
        node_names = []
        for op in sas_task.operators:
            eff_index_1 = 0
            for n_var_no, n_pre_spec, n_post, n_cond in op.pre_post:
                if (n_pre_spec == -2 or n_pre_spec == -3 or n_pre_spec == -4) \
                        and n_var_no == index:
                    eff_index_2 = 0
                    for var_no, pre_spec, post, cond in op.pre_post:
                        if eff_index_1 != eff_index_2 and (pre_spec != -2 and pre_spec != -3 and pre_spec != -4
                                                           and pre_spec != -5 and pre_spec != -6
                                                           and pre_spec != -7 and pre_spec != -8):
                            if translation_key[var_no][pre_spec] != '<none of those>':
                                arc_pre_name = translation_key[var_no][pre_spec]
                                arc_pre_name = arc_pre_name.replace("<", "--")
                                arc_post_name = translation_key[var_no][post]
                                arc_post_name = arc_post_name.replace("<", "--")

                                if arc_pre_name not in node_names:
                                    node_dict[arc_pre_name] = []
                                    node_names.append(arc_pre_name)
                                if arc_post_name not in node_names:
                                    node_dict[arc_post_name] = []
                                    node_names.append(arc_post_name)

                                arc_act_name = translation_key[n_var_no][n_post[2]]
                                arc_act_name = arc_act_name.replace("<", "--")
                                arc_act_name = arc_act_name.replace(">", "--")
                                node_dict[translation_key[var_no][pre_spec]].append(
                                    DomainArc(arc_pre_name, arc_post_name,
                                              arc_act_name))
                        eff_index_2 = eff_index_2 + 1
                eff_index_1 = eff_index_1 + 1

        fdtgs.append(DomainTransGraph(0, index, node_dict))
        index = index + 1

    return fdtgs


def create_functional_dtgs_per_invariant(sas_task, translation_key, groups):
    fdtgs_per_invariant = []
    index = 0
    fdtg_index = 0
    for invariant in groups:

        # Check if the group is propositional
        if (isinstance(invariant[0].predicate, pddl.f_expression.Increase) or
                isinstance(invariant[0].predicate, pddl.f_expression.Assign) or
                isinstance(invariant[0].predicate, pddl.f_expression.Decrease) or
                isinstance(invariant[0].predicate, pddl.f_expression.GreaterThan) or
                isinstance(invariant[0].predicate, pddl.f_expression.LessThan)):
            index = index + 1
            continue

        fdtgs_per_invariant.append([])
        index2 = 0

        for group in groups:

            # Check if the group is functional
            if not (isinstance(group[0].predicate, pddl.f_expression.Increase) or
                    isinstance(group[0].predicate, pddl.f_expression.Assign) or
                    isinstance(group[0].predicate, pddl.f_expression.Decrease) or
                    isinstance(group[0].predicate, pddl.f_expression.GreaterThan) or
                    isinstance(group[0].predicate, pddl.f_expression.LessThan)):
                index2 = index2 + 1
                continue

            node_dict = {}
            node_names = []
            for op in sas_task.operators:
                eff_index_1 = 0
                for n_var_no, n_pre_spec, n_post, n_cond in op.pre_post:
                    if (n_pre_spec == -2 or n_pre_spec == -3 or n_pre_spec == -4) and n_var_no == index2:
                        eff_index_2 = 0
                        for var_no, pre_spec, post, cond in op.pre_post:
                            if eff_index_1 != eff_index_2 and (pre_spec != -2 and pre_spec != -3
                                                               and pre_spec != -4 and pre_spec != -5
                                                               and pre_spec != -6 and pre_spec != -7
                                                               and pre_spec != 8) and var_no == index:
                                if translation_key[var_no][pre_spec] != '<none of those>':
                                    arc_pre_name = translation_key[var_no][pre_spec]
                                    arc_pre_name = arc_pre_name.replace("<", "--")
                                    arc_post_name = translation_key[var_no][post]
                                    arc_post_name = arc_post_name.replace("<", "--")

                                    if arc_pre_name not in node_names:
                                        node_dict[arc_pre_name] = []
                                        node_names.append(arc_pre_name)
                                    if arc_post_name not in node_names:
                                        node_dict[arc_post_name] = []
                                        node_names.append(arc_post_name)

                                    arc_act_name = translation_key[n_var_no][n_post[2]]
                                    arc_act_name = arc_act_name.replace("<", "--")
                                    arc_act_name = arc_act_name.replace(">", "--")
                                    node_dict[translation_key[var_no][pre_spec]].append(
                                        DomainArc(arc_pre_name, arc_post_name,
                                                  arc_act_name))
                            eff_index_2 = eff_index_2 + 1
                    eff_index_1 = eff_index_1 + 1
            fdtgs_per_invariant[fdtg_index].append(DomainTransGraph(0, index2, node_dict))

            index2 = index2 + 1

        fdtg_index = fdtg_index + 1
        index = index + 1

    return fdtgs_per_invariant


def create_functional_dtg_metric(sas_task, translation_key, groups):
    node_dict = {}
    node_names = []

    for op in sas_task.operators:
        eff_index_1 = 0
        for n_var_no, n_pre_spec, n_post, n_cond in op.pre_post:
            if (n_pre_spec == -2 or n_pre_spec == -3 or n_pre_spec == -4) \
                    and n_var_no in sas_task.translated_metric:
                eff_index_2 = 0
                for var_no, pre_spec, post, cond in op.pre_post:
                    if eff_index_1 != eff_index_2 and (pre_spec != -2 and pre_spec != -3 and pre_spec != -4
                                                       and pre_spec != -5 and pre_spec != -6 and pre_spec != -7
                                                       and pre_spec != -8):
                        if translation_key[var_no][pre_spec] != '<none of those>':
                            arc_pre_name = translation_key[var_no][pre_spec]
                            arc_pre_name = arc_pre_name.replace("<", "--")
                            arc_post_name = translation_key[var_no][post]
                            arc_post_name = arc_post_name.replace("<", "--")

                            if arc_pre_name not in node_names:
                                node_dict[arc_pre_name] = []
                                node_names.append(arc_pre_name)
                            if arc_post_name not in node_names:
                                node_dict[arc_post_name] = []
                                node_names.append(arc_post_name)

                            arc_act_name = translation_key[n_var_no][n_post[2]]
                            arc_act_name = arc_act_name.replace("<", "--")
                            arc_act_name = arc_act_name.replace(">", "--")
                            node_dict[translation_key[var_no][pre_spec]].append(
                                DomainArc(arc_pre_name, arc_post_name,
                                          arc_act_name))
                    eff_index_2 = eff_index_2 + 1
            eff_index_1 = eff_index_1 + 1

    return DomainTransGraph(0, 0, node_dict)


def create_functional_dtg_metric_per_agent(sas_task, translation_key, groups):
    node_dict = {}
    node_names = []

    for op in sas_task.operators:
        eff_index_1 = 0
        for n_var_no, n_pre_spec, n_post, n_cond in op.pre_post:
            if (n_pre_spec == -2 or n_pre_spec == -3 or n_pre_spec == -4) \
                    and n_var_no in sas_task.metric[1:]:
                eff_index_2 = 0
                for var_no, pre_spec, post, cond in op.pre_post:
                    if eff_index_1 != eff_index_2 and (pre_spec != -2 and pre_spec != -3 and pre_spec != -4
                                                       and pre_spec != -5 and pre_spec != -6 and pre_spec != -7
                                                       and pre_spec != -8):
                        if translation_key[var_no][pre_spec] != '<none of those>':
                            arc_pre_name = translation_key[var_no][pre_spec]
                            arc_pre_name = arc_pre_name.replace("<", "--")
                            arc_post_name = translation_key[var_no][post]
                            arc_post_name = arc_post_name.replace("<", "--")

                            if arc_pre_name not in node_names:
                                node_dict[arc_pre_name] = []
                                node_names.append(arc_pre_name)
                            if arc_post_name not in node_names:
                                node_dict[arc_post_name] = []
                                node_names.append(arc_post_name)

                            arc_act_name = translation_key[n_var_no][n_post[2]]
                            arc_act_name = arc_act_name.replace("<", "--")
                            arc_act_name = arc_act_name.replace(">", "--")
                            node_dict[translation_key[var_no][pre_spec]].append(
                                DomainArc(arc_pre_name, arc_post_name,
                                          arc_act_name))
                    eff_index_2 = eff_index_2 + 1
            eff_index_1 = eff_index_1 + 1

    return DomainTransGraph(0, 0, node_dict)


def create_functional_dtgs_metric(sas_task, translation_key, groups):
    metric_fdtgs = []
    index = 0
    for group in groups:

        # Check if the group is propositional
        if (isinstance(group[0].predicate, pddl.f_expression.Increase) or
                isinstance(group[0].predicate, pddl.f_expression.Assign) or
                isinstance(group[0].predicate, pddl.f_expression.Decrease) or
                isinstance(group[0].predicate, pddl.f_expression.GreaterThan) or
                isinstance(group[0].predicate, pddl.f_expression.LessThan)):
            index = index + 1
            continue

        node_dict = {}
        node_names = []
        for op in sas_task.operators:
            eff_index_1 = 0
            for n_var_no, n_pre_spec, n_post, n_cond in op.pre_post:
                if (n_pre_spec == -2 or n_pre_spec == -3 or n_pre_spec == -4) \
                        and n_var_no in sas_task.translated_metric:
                    eff_index_2 = 0
                    for var_no, pre_spec, post, cond in op.pre_post:
                        if eff_index_1 != eff_index_2 and (pre_spec != -2 and pre_spec != -3 and
                                                           pre_spec != -4 and pre_spec != -5 and
                                                           pre_spec != -6 and pre_spec != -7 and
                                                           pre_spec != -8) and var_no == index:
                            if translation_key[var_no][pre_spec] != '<none of those>':
                                arc_pre_name = translation_key[var_no][pre_spec]
                                arc_pre_name = arc_pre_name.replace("<", "--")
                                arc_post_name = translation_key[var_no][post]
                                arc_post_name = arc_post_name.replace("<", "--")

                                if arc_pre_name not in node_names:
                                    node_dict[arc_pre_name] = []
                                    node_names.append(arc_pre_name)
                                if arc_post_name not in node_names:
                                    node_dict[arc_post_name] = []
                                    node_names.append(arc_post_name)

                                arc_act_name = translation_key[n_var_no][n_post[2]]
                                arc_act_name = arc_act_name.replace("<", "--")
                                arc_act_name = arc_act_name.replace(">", "--")
                                node_dict[translation_key[var_no][pre_spec]].append(
                                    DomainArc(arc_pre_name, arc_post_name,
                                              arc_act_name))
                        eff_index_2 = eff_index_2 + 1
                eff_index_1 = eff_index_1 + 1

        metric_fdtgs.append(DomainTransGraph(0, index, node_dict))
        index = index + 1

    return metric_fdtgs


def create_gexf_transition_graphs_files(dtgs, groups, group_const_arg, n_agent):
    index = 0
    today = date.today()
    d1 = today.strftime("%d/%m/%Y")

    if WINDOWS:
        save_path = "C:\\Users\\JavCa\\PycharmProjects\\pddl2-SAS-translate2\\graphs"
    else:
        if n_agent == 0:
            save_path = "graphs"
        else:
            save_path = "graphs/per_agent"

    for graph in dtgs:

        # Check if the group is functional
        if isinstance(groups[index][0].predicate, pddl.f_expression.Increase) or \
                isinstance(groups[index][0].predicate, pddl.f_expression.Decrease) or \
                isinstance(groups[index][0].predicate, pddl.f_expression.Assign) or \
                isinstance(groups[index][0].predicate, pddl.f_expression.LessThan) or \
                isinstance(groups[index][0].predicate, pddl.f_expression.GreaterThan):
            index = index + 1
            continue

        if len(graph.var_group) > 2:
            graph_name = groups[index][0].predicate + "-" + '-'.join(group_const_arg[index])
            if n_agent != 0:
                file_name = "agent_" + str(n_agent) + "_dtg_" + str(index) + "_" + graph_name + ".gexf"
            else:
                file_name = "dtg_" + str(index) + "_" + graph_name + ".gexf"
            full_name = os.path.join(save_path, file_name)
            f = open(full_name, "w")
            f.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n")
            f.write("<gexf xmlns=\"http://www.gexf.net/1.3draft\" version=\"1.3\">\n")
            f.write("\t<meta lastmodifieddate=\"" + d1 + "\">\n")
            f.write("\t\t<creator>Javier Caballero</creator>\n")
            f.write("\t\t<description>graph_" + str(index) + "</description>\n")
            f.write("\t</meta>\n")
            f.write("\t<graph mode=\"static\" defaultedgetype=\"directed\">\n")
            f.write("\t\t<nodes>\n")
            for node in graph.node_list:
                if node.state != '<none of those>':
                    f.write("\t\t\t<node id=\"" + node.state + "\" label=\"" + node.state + "\" />\n")
            f.write("\t\t</nodes>\n")

            f.write("\t\t<edges>\n")
            for node in graph.node_list:
                if node.state != '<none of those>':
                    for arc in node.arcs:
                        if arc.origin_state != "<none of those>" and arc.end_state != "<none of those>":
                            f.write("\t\t\t<edge id=\"" + arc.action + "\" label=\"" + arc.action + "\" source=\"" +
                                    node.state + "\" target=\"" + arc.end_state + "\" />\n")
            f.write("\t\t</edges>\n")
            f.write("\t</graph>\n")
            f.write("</gexf>\n")

            f.close()
            index = index + 1


def create_gexf_transition_graphs_files_per_agent(dtgs, groups, group_const_arg, n_agent):
    index = 0
    today = date.today()
    d1 = today.strftime("%d/%m/%Y")

    if WINDOWS:
        save_path = "C:\\Users\\JavCa\\PycharmProjects\\pddl2-SAS-translate2\\graphs"
    else:
        if n_agent == 0:
            save_path = "graphs"
        else:
            save_path = "graphs/per_agent"

    for key, graph in dtgs.items():

        # Check if the group is functional
        if isinstance(groups[key][0].predicate, pddl.f_expression.Increase) or \
                isinstance(groups[key][0].predicate, pddl.f_expression.Decrease) or \
                isinstance(groups[key][0].predicate, pddl.f_expression.Assign) or \
                isinstance(groups[key][0].predicate, pddl.f_expression.LessThan) or \
                isinstance(groups[key][0].predicate, pddl.f_expression.GreaterThan):
            index = index + 1
            continue

        if len(graph.var_group) > 2:
            graph_name = groups[key][0].predicate + "-" + '-'.join(group_const_arg[key])
            if n_agent != 0:
                file_name = "agent_" + str(n_agent) + "_dtg_" + str(key) + "_" + graph_name + ".gexf"
            else:
                file_name = "dtg_" + str(key) + "_" + graph_name + ".gexf"
            full_name = os.path.join(save_path, file_name)
            f = open(full_name, "w")
            f.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n")
            f.write("<gexf xmlns=\"http://www.gexf.net/1.3draft\" version=\"1.3\">\n")
            f.write("\t<meta lastmodifieddate=\"" + d1 + "\">\n")
            f.write("\t\t<creator>Javier Caballero</creator>\n")
            f.write("\t\t<description>graph_" + str(key) + "</description>\n")
            f.write("\t</meta>\n")
            f.write("\t<graph mode=\"static\" defaultedgetype=\"directed\">\n")
            f.write("\t\t<nodes>\n")
            for node in graph.node_list:
                if node.state != '<none of those>':
                    f.write("\t\t\t<node id=\"" + node.state + "\" label=\"" + node.state + "\" />\n")
            f.write("\t\t</nodes>\n")

            f.write("\t\t<edges>\n")
            for node in graph.node_list:
                if node.state != '<none of those>':
                    for arc in node.arcs:
                        if arc.origin_state != "<none of those>" and arc.end_state != "<none of those>":
                            f.write("\t\t\t<edge id=\"" + arc.action + "\" label=\"" + arc.action + "\" source=\"" +
                                    node.state + "\" target=\"" + arc.end_state + "\" />\n")
            f.write("\t\t</edges>\n")
            f.write("\t</graph>\n")
            f.write("</gexf>\n")

            f.close()
            index = index + 1


def create_gexf_transition_functional_graphs_files(fdtgs, group_const_arg, n_agent):
    index = 0
    today = date.today()
    d1 = today.strftime("%d/%m/%Y")

    if WINDOWS:
        save_path = "C:\\Users\\JavCa\\PycharmProjects\\pddl2-SAS-translate2\\graphs"
    else:
        if n_agent == 0:
            save_path = "graphs"
        else:
            save_path = "graphs/per_agent"

    for graph in fdtgs:
        graph_name = '-'.join(group_const_arg[graph.var_group])
        if n_agent != 0:
            file_name = "agent_" + str(n_agent) + "_functional_dtg_" + str(graph.var_group) + "_" + graph_name + ".gexf"
        else:
            file_name = "functional_dtg_" + str(graph.var_group) + "_" + graph_name + ".gexf"

        full_name = os.path.join(save_path, file_name)
        f = open(full_name, "w")
        f.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n")
        f.write("<gexf xmlns=\"http://www.gexf.net/1.3draft\" version=\"1.3\">\n")
        f.write("\t<meta lastmodifieddate=\"" + d1 + "\">\n")
        f.write("\t\t<creator>Javier Caballero</creator>\n")
        f.write("\t\t<description>functional_graph_" + str(index) + "</description>\n")
        f.write("\t</meta>\n")
        f.write("\t<graph mode=\"static\" defaultedgetype=\"directed\">\n")
        f.write("\t\t<nodes>\n")
        for key, arcs in graph.node_list.items():
            if key != '<none of those>':
                f.write("\t\t\t<node id=\"" + key + "\" label=\"" + key + "\" />\n")
        f.write("\t\t</nodes>\n")

        f.write("\t\t<edges>\n")
        for key, arcs in graph.node_list.items():
            if key != '<none of those>':
                for arc in arcs:
                    if arc.origin_state != "<none of those>" and arc.end_state != "<none of those>":
                        f.write("\t\t\t<edge label=\"" + arc.action + "\" source=\"" +
                                arc.origin_state + "\" target=\"" + arc.end_state + "\" />\n")
        f.write("\t\t</edges>\n")
        f.write("\t</graph>\n")
        f.write("</gexf>\n")

        f.close()
        index = index + 1


def create_gexf_transition_functional_metric_graph_files(fdtg_metric, n_agent):
    today = date.today()
    d1 = today.strftime("%d/%m/%Y")

    if WINDOWS:
        save_path = "C:\\Users\\JavCa\\PycharmProjects\\pddl2-SAS-translate2\\graphs\\metric"
    else:
        if n_agent == 0:
            save_path = "graphs/metric"
        else:
            save_path = "graphs/per_agent/metric"

    if n_agent != 0:
        file_name = "agent_" + str(n_agent) + "_functional_metric_graph.gexf"
    else:
        file_name = "functional_metric_graph.gexf"
    full_name = os.path.join(save_path, file_name)
    f = open(full_name, "w")
    f.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n")
    f.write("<gexf xmlns=\"http://www.gexf.net/1.3draft\" version=\"1.3\">\n")
    f.write("\t<meta lastmodifieddate=\"" + d1 + "\">\n")
    f.write("\t\t<creator>Javier Caballero</creator>\n")
    f.write("\t\t<description>functional_metric_graph</description>\n")
    f.write("\t</meta>\n")
    f.write("\t<graph mode=\"static\" defaultedgetype=\"directed\">\n")
    f.write("\t\t<nodes>\n")
    for key, arcs in fdtg_metric.node_list.items():
        if key != '<none of those>':
            f.write("\t\t\t<node id=\"" + key + "\" label=\"" + key + "\" />\n")
    f.write("\t\t</nodes>\n")

    f.write("\t\t<edges>\n")
    for key, arcs in fdtg_metric.node_list.items():
        if key != '<none of those>':
            for arc in arcs:
                if arc.origin_state != "<none of those>" and arc.end_state != "<none of those>":
                    f.write("\t\t\t<edge label=\"" + arc.action + "\" source=\"" +
                            arc.origin_state + "\" target=\"" + arc.end_state + "\" />\n")
    f.write("\t\t</edges>\n")
    f.write("\t</graph>\n")
    f.write("</gexf>\n")

    f.close()


def create_gexf_transition_functional_metric_graphs_files(fdtgs, n_agent):
    index = 0
    today = date.today()
    d1 = today.strftime("%d/%m/%Y")

    if WINDOWS:
        save_path = "C:\\Users\\JavCa\\PycharmProjects\\pddl2-SAS-translate2\\graphs\\metric"
    else:
        if n_agent == 0:
            save_path = "graphs/metric"
        else:
            save_path = "graphs/per_agent/metric"

    for graph in fdtgs:
        file_name = "functional_metric_graph_" + str(graph.var_group) + ".gexf"
        full_name = os.path.join(save_path, file_name)
        f = open(full_name, "w")
        f.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n")
        f.write("<gexf xmlns=\"http://www.gexf.net/1.3draft\" version=\"1.3\">\n")
        f.write("\t<meta lastmodifieddate=\"" + d1 + "\">\n")
        f.write("\t\t<creator>Javier Caballero</creator>\n")
        f.write("\t\t<description>functional_metric_graph_" + str(graph.var_group) + "</description>\n")
        f.write("\t</meta>\n")
        f.write("\t<graph mode=\"static\" defaultedgetype=\"directed\">\n")
        f.write("\t\t<nodes>\n")
        for key, arcs in graph.node_list.items():
            if key != '<none of those>':
                f.write("\t\t\t<node id=\"" + key + "\" label=\"" + key + "\" />\n")
        f.write("\t\t</nodes>\n")

        f.write("\t\t<edges>\n")
        for key, arcs in graph.node_list.items():
            if key != '<none of those>':
                for arc in arcs:
                    if arc.origin_state != "<none of those>" and arc.end_state != "<none of those>":
                        f.write("\t\t\t<edge label=\"" + arc.action + "\" source=\"" +
                                arc.origin_state + "\" target=\"" + arc.end_state + "\" />\n")
        f.write("\t\t</edges>\n")
        f.write("\t</graph>\n")
        f.write("</gexf>\n")

        f.close()
        index = index + 1


def create_gexf_transition_functional_per_inv_graphs_files(fdtgs_per_invariant, n_agent):
    today = date.today()
    d1 = today.strftime("%d/%m/%Y")

    if WINDOWS:
        save_path = "C:\\Users\\JavCa\\PycharmProjects\\pddl2-SAS-translate2\\graphs\\functional_graphs_inv"
    else:
        if n_agent == 0:
            save_path = "graphs/functional_graphs_inv"
        else:
            save_path = "graphs/per_agent/functional_graphs_inv"

    n_invariant = 0
    for invariant in fdtgs_per_invariant:

        n_graph = 0
        for graph in invariant:

            if graph and graph.node_list:
                file_name = "functional_graph_" + str(n_invariant) + "_" + str(n_graph) + ".gexf"
                full_name = os.path.join(save_path, file_name)
                f = open(full_name, "w")
                f.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n")
                f.write("<gexf xmlns=\"http://www.gexf.net/1.3draft\" version=\"1.3\">\n")
                f.write("\t<meta lastmodifieddate=\"" + d1 + "\">\n")
                f.write("\t\t<creator>Javier Caballero</creator>\n")
                f.write(
                    "\t\t<description>functional_graph_" + str(n_invariant) + "_" + str(n_graph) + "</description>\n")
                f.write("\t</meta>\n")
                f.write("\t<graph mode=\"static\" defaultedgetype=\"directed\">\n")
                f.write("\t\t<nodes>\n")
                for key, arcs in graph.node_list.items():
                    if key != '<none of those>':
                        f.write("\t\t\t<node id=\"" + key + "\" label=\"" + key + "\" />\n")
                f.write("\t\t</nodes>\n")

                f.write("\t\t<edges>\n")
                for key, arcs in graph.node_list.items():
                    if key != '<none of those>':
                        for arc in arcs:
                            if arc.origin_state != "<none of those>" and arc.end_state != "<none of those>":
                                f.write("\t\t\t<edge label=\"" + arc.action + "\" source=\"" +
                                        arc.origin_state + "\" target=\"" + arc.end_state + "\" />\n")
                f.write("\t\t</edges>\n")
                f.write("\t</graph>\n")
                f.write("</gexf>\n")

                f.close()
                n_graph = n_graph + 1
        n_invariant = n_invariant + 1


def create_csv_transition_graphs_files(dtgs, groups):
    index = 0

    if WINDOWS:
        save_path = "C:\\Users\\JavCa\\PycharmProjects\\pddl2-SAS-translate2\\graphs"
    else:
        save_path = "graphs"

    for graph in dtgs:

        # Check if the group is functional
        if isinstance(groups[index][0].predicate, pddl.f_expression.Increase):
            index = index + 1
            continue

        if len(graph.var_group) > 2:
            file_name = "graph_" + str(index) + ".csv"
            full_name = os.path.join(save_path, file_name)
            f = open(full_name, "w")
            for node in graph.node_list:
                if node.state != '<none of those>':
                    f.write(node.state)
                    for arc in node.arcs:
                        f.write(";")
                        f.write(arc.end_state)
                    f.write("\n")
            f.close()
            index = index + 1


def create_casual_graph(sas_task, groups, group_const_arg, free_agent_index, temp_task):
    node_groups_list = []
    node_groups_list_type1 = []
    node_groups_list_type2 = []
    propositional_node_groups_list = []
    propositional_node_groups = {}
    propositional_node_groups_type1 = {}
    propositional_node_groups_type2 = {}
    group_number = 0

    for group in groups:
        name = ""
        atoms_included = []
        is_there_function_states = False

        for state in group:
            if isinstance(state.predicate, pddl.f_expression.Increase) or \
                    isinstance(state.predicate, pddl.f_expression.Decrease) or \
                    isinstance(state.predicate, pddl.f_expression.Assign) or \
                    isinstance(state.predicate, pddl.f_expression.GreaterThan) or \
                    isinstance(state.predicate, pddl.f_expression.LessThan):
                if isinstance(state.predicate, pddl.f_expression.Increase):
                    if "increase-" + state.predicate.fluent.symbol not in atoms_included:
                        atoms_included.append("increase-" + state.predicate.fluent.symbol)
                        name = name + "increase-" + state.predicate.fluent.symbol + "_"
                elif isinstance(state.predicate, pddl.f_expression.Decrease):
                    if "decrease-" + state.predicate.fluent.symbol not in atoms_included:
                        atoms_included.append("decrease-" + state.predicate.fluent.symbol)
                        name = name + "decrease-" + state.predicate.fluent.symbol + "_"
                elif isinstance(state.predicate, pddl.f_expression.Assign):
                    if "assign-" + state.predicate.fluent.symbol not in atoms_included:
                        atoms_included.append("assign-" + state.predicate.fluent.symbol)
                        name = name + "assign-" + state.predicate.fluent.symbol + "_"
                elif isinstance(state.predicate, pddl.f_expression.GreaterThan):
                    if "gt-" + state.predicate.fluent.symbol not in atoms_included:
                        atoms_included.append("gt-" + state.predicate.fluent.symbol)
                        name = name + "gt-" + state.predicate.fluent.symbol + "_"
                elif isinstance(state.predicate, pddl.f_expression.LessThan):
                    if "lt-" + state.predicate.fluent.symbol not in atoms_included:
                        atoms_included.append("lt-" + state.predicate.fluent.symbol)
                        name = name + "lt-" + state.predicate.fluent.symbol + "_"
                is_there_function_states = True
            else:
                if len(group) == 1:
                    name = state.predicate + "_" + "-".join(state.args)
                else:
                    if state.predicate not in atoms_included:
                        atoms_included.append(state.predicate)
                        name = name + state.predicate + "_"

        name = name[:-1]
        if group_number < len(group_const_arg):
            name = name + "_" + "-".join(group_const_arg[group_number])
        node_groups_list.append(DomainCasualNode([], name, group_number, [], [], [], [], []))
        node_groups_list_type1.append(DomainCasualNode([], name, group_number, [], [], [], [], []))
        node_groups_list_type2.append(DomainCasualNode([], name, group_number, [], [], [], [], []))
        if not is_there_function_states:
            propositional_node_groups_list.append(group_number)
            propositional_node_groups[group_number] = DomainCasualNode([], name, group_number, [], [], [], [], [])
            propositional_node_groups_type1[group_number] = DomainCasualNode([], name, group_number, [], [], [], [], [])
            propositional_node_groups_type2[group_number] = DomainCasualNode([], name, group_number, [], [], [], [], [])

        group_number = group_number + 1

    for op in sas_task.operators:
        end_action = False
        if "_end " in op.name:
            end_action = True
        operator_index1 = 0
        for var_no1, pre_spec1, post1, cond1 in op.pre_post:
            if pre_spec1 != -7 and pre_spec1 != -8:
                operator_index2 = 0
                # Check for arcs of type 2 (effect - effect) and type 1 (precondition)
                for var_no2, pre_spec2, post2, cond2 in op.pre_post:
                    # Type 2 (only if it is a different effect)
                    # We do not use type2 arcs
                    if False and operator_index2 != operator_index1 and pre_spec2 != -7 and pre_spec2 != -8:
                        arc_id = (op.name.split(' ')[0])[1:] + "-" + str(var_no1) + "_" + str(var_no2)
                        if arc_id not in node_groups_list[var_no1].type2_arcs and var_no1 != var_no2 \
                                and free_agent_index != var_no2 and free_agent_index != var_no1:
                            new_arc = DomainCasualArc(var_no1, var_no2, node_groups_list[var_no1].name,
                                                      node_groups_list[var_no2].name, (op.name.split(' ')[0])[1:],
                                                      2, arc_id)
                            node_groups_list[var_no1].arcs.append(new_arc)
                            node_groups_list[var_no2].end_arcs.append(new_arc)
                            node_groups_list[var_no1].type2_arcs.append(arc_id)
                            node_groups_list[var_no2].end_type2_arcs.append(arc_id)
                            node_groups_list_type2[var_no1].arcs.append(new_arc)
                            node_groups_list_type2[var_no2].end_arcs.append(new_arc)
                            node_groups_list_type2[var_no1].type2_arcs.append(arc_id)
                            node_groups_list_type2[var_no2].end_type2_arcs.append(arc_id)
                            if var_no2 in propositional_node_groups_list \
                                    and var_no1 in propositional_node_groups_list:
                                propositional_node_groups[var_no1].arcs.append(new_arc)
                                propositional_node_groups[var_no2].end_arcs.append(new_arc)
                                propositional_node_groups[var_no1].type2_arcs.append(arc_id)
                                propositional_node_groups[var_no2].end_type2_arcs.append(arc_id)
                                propositional_node_groups_type2[var_no1].arcs.append(new_arc)
                                propositional_node_groups_type2[var_no2].end_arcs.append(new_arc)
                                propositional_node_groups_type2[var_no1].type2_arcs.append(arc_id)
                                propositional_node_groups_type2[var_no2].end_type2_arcs.append(arc_id)

                    # Type 1 (only if a precondition exists)
                    if pre_spec1 != -1 and (pre_spec1 != -2 and pre_spec1 != -3 and pre_spec1 != -4 and
                                            pre_spec1 != -5 and pre_spec1 != -6 and
                                            pre_spec1 != -7 and pre_spec1 != -8):
                        arc_id = (op.name.split(' ')[0])[1:] + "-" + str(var_no1) + "_" + str(var_no2)
                        if arc_id not in node_groups_list[var_no1].type1_arcs and var_no1 != var_no2 \
                                and free_agent_index != var_no2 and free_agent_index != var_no1:
                            new_arc = DomainCasualArc(var_no1, var_no2, node_groups_list[var_no1].name,
                                                      node_groups_list[var_no2].name, (op.name.split(' ')[0])[1:],
                                                      1, arc_id)
                            node_groups_list[var_no1].arcs.append(new_arc)
                            node_groups_list[var_no2].end_arcs.append(new_arc)
                            node_groups_list[var_no1].type1_arcs.append(arc_id)
                            node_groups_list[var_no2].end_type1_arcs.append(arc_id)
                            node_groups_list_type1[var_no1].arcs.append(new_arc)
                            node_groups_list_type1[var_no2].end_arcs.append(new_arc)
                            node_groups_list_type1[var_no1].type1_arcs.append(arc_id)
                            node_groups_list_type1[var_no2].end_type1_arcs.append(arc_id)
                            if var_no2 in propositional_node_groups_list \
                                    and var_no1 in propositional_node_groups_list:
                                propositional_node_groups[var_no1].arcs.append(new_arc)
                                propositional_node_groups[var_no2].end_arcs.append(new_arc)
                                propositional_node_groups[var_no1].type1_arcs.append(arc_id)
                                propositional_node_groups[var_no2].end_type1_arcs.append(arc_id)
                                propositional_node_groups_type1[var_no1].arcs.append(new_arc)
                                propositional_node_groups_type1[var_no2].end_arcs.append(new_arc)
                                propositional_node_groups_type1[var_no1].type1_arcs.append(arc_id)
                                propositional_node_groups_type1[var_no2].end_type1_arcs.append(arc_id)

                    operator_index2 = operator_index2 + 1

                # Check for arcs of type 1 from prevail array (precondition - effect)
                if not end_action or not temp_task:
                    for var_no2, pre_spec2 in op.prevail:
                        arc_id = (op.name.split(' ')[0])[1:] + "-" + str(var_no2) + "_" + str(var_no1)
                        if arc_id not in node_groups_list[var_no2].type1_arcs and var_no1 != var_no2 \
                                and free_agent_index != var_no2 and free_agent_index != var_no1:
                            new_arc = DomainCasualArc(var_no2, var_no1, node_groups_list[var_no2].name,
                                                      node_groups_list[var_no1].name, (op.name.split(' ')[0])[1:],
                                                      1, arc_id)
                            node_groups_list[var_no2].arcs.append(new_arc)
                            node_groups_list[var_no1].end_arcs.append(new_arc)
                            node_groups_list[var_no2].type1_arcs.append(arc_id)
                            node_groups_list[var_no1].end_type1_arcs.append(arc_id)
                            node_groups_list_type1[var_no2].arcs.append(new_arc)
                            node_groups_list_type1[var_no1].end_arcs.append(new_arc)
                            node_groups_list_type1[var_no2].type1_arcs.append(arc_id)
                            node_groups_list_type1[var_no1].end_type1_arcs.append(arc_id)
                            if var_no2 in propositional_node_groups_list \
                                    and var_no1 in propositional_node_groups_list:
                                propositional_node_groups[var_no2].arcs.append(new_arc)
                                propositional_node_groups[var_no1].end_arcs.append(new_arc)
                                propositional_node_groups[var_no2].type1_arcs.append(arc_id)
                                propositional_node_groups[var_no1].end_type1_arcs.append(arc_id)
                                propositional_node_groups_type1[var_no2].arcs.append(new_arc)
                                propositional_node_groups_type1[var_no1].end_arcs.append(new_arc)
                                propositional_node_groups_type1[var_no2].type1_arcs.append(arc_id)
                                propositional_node_groups_type1[var_no1].end_type1_arcs.append(arc_id)

            operator_index1 = operator_index1 + 1

    return (DomainCasualGraph(node_groups_list),
            DomainCasualGraph(node_groups_list_type1),
            DomainCasualGraph(node_groups_list_type2),
            DomainCasualGraph(propositional_node_groups),
            DomainCasualGraph(propositional_node_groups_type1),
            DomainCasualGraph(propositional_node_groups_type2))


def simplify_graph(propositional_casual_graph_type1):
    node_groups_list = []
    for node in propositional_casual_graph_type1:
        node_groups_list.append(node)

    return DomainCasualGraph(node_groups_list)


def remove_two_way_cycles(casual_graph):
    arcs_to_remove = []
    for node_number in casual_graph.node_list:
        for first_arc in casual_graph.node_list[node_number].arcs[:]:
            for second_arc in casual_graph.node_list[first_arc.end_state].arcs[:]:
                if second_arc.end_state == node_number:
                    arcs_to_remove.append(first_arc)
                    arcs_to_remove.append(second_arc)
                    if first_arc in casual_graph.node_list[node_number].arcs:
                        casual_graph.node_list[node_number].arcs.remove(first_arc)
                    if second_arc in casual_graph.node_list[first_arc.end_state].arcs:
                        casual_graph.node_list[first_arc.end_state].arcs.remove(second_arc)

    for remove_arc in arcs_to_remove:
        for end_arc in casual_graph.node_list[remove_arc.end_state].end_arcs[:]:
            if end_arc.end_state == remove_arc.end_state and end_arc.origin_state == remove_arc.origin_state:
                casual_graph.node_list[remove_arc.end_state].end_arcs.remove(end_arc)

    return casual_graph


def remove_three_way_cycles(casual_graph):
    arcs_to_remove = []
    for node_number in casual_graph.node_list:
        for first_arc in casual_graph.node_list[node_number].arcs[:]:
            for second_arc in casual_graph.node_list[first_arc.end_state].arcs[:]:
                if second_arc.end_state != node_number:
                    for third_arc in casual_graph.node_list[second_arc.end_state].arcs[:]:
                        if third_arc.end_state == node_number:
                            arcs_to_remove.append(first_arc)
                            arcs_to_remove.append(second_arc)
                            arcs_to_remove.append(third_arc)
                            # casual_graph.node_list[third_arc.end_state].arcs.remove(first_arc)
                            # casual_graph.node_list[first_arc.end_state].arcs.remove(second_arc)
                            # casual_graph.node_list[second_arc.end_state].arcs.remove(third_arc)

    for remove_arc in arcs_to_remove:
        for end_arc in casual_graph.node_list[remove_arc.end_state].end_arcs[:]:
            if end_arc.end_state == remove_arc.end_state and end_arc.origin_state == remove_arc.origin_state:
                casual_graph.node_list[remove_arc.end_state].end_arcs.remove(end_arc)

    return casual_graph


def obtain_origin_nodes(casual_graph):
    origin_nodes = {}
    for node_number in casual_graph.node_list:
        if not casual_graph.node_list[node_number].end_arcs:
            for arc in casual_graph.node_list[node_number].arcs:
                if arc.arc_type == 1:
                    origin_nodes[node_number] = casual_graph.node_list[node_number]
                    break

    return origin_nodes


def fill_basic_agents(origin_nodes, propositional_casual_graph, groups):
    full_agents = []
    redundant_agents = []
    or_agent_nodes = [or_node_number for or_node_number in origin_nodes]
    for agent in origin_nodes:
        search_queue = []
        already_visited = []

        for a_node in agent:
            for node_app in propositional_casual_graph.node_list[a_node].arcs:
                if node_app.arc_type == 1 and node_app.end_state not in search_queue and \
                        node_app.end_state not in agent:
                    search_queue.append(node_app.end_state)
                    already_visited.append(node_app.end_state)

        full_agents.append(agent)
        while search_queue:
            node = search_queue.pop(0)

            # Check if all predecessors are in V
            bool_all = True
            curr_arc = False
            for node_arc in propositional_casual_graph.node_list[node].end_arcs:
                if node_app.arc_type == 1 and (node_arc.origin_state not in full_agents[-1]):
                    # Check if the arc found is part of a 1 level loop
                    if len(propositional_casual_graph.node_list[node_arc.origin_state].end_type1_arcs) == 1:
                        if "_curr_" in propositional_casual_graph.node_list[node].name:
                            continue
                    elif "_curr_" in propositional_casual_graph.node_list[node].name:
                        if not curr_arc:
                            curr_arc = True
                            continue

                    bool_all = False
                    break

            if bool_all:
                full_agents[-1].append(node)

                # Check if the new variable of the agent was considered a separated agent
                if node in or_agent_nodes:
                    redundant_agents.append(node)

                for arc_app in propositional_casual_graph.node_list[node].arcs:
                    if arc_app.arc_type == 1 and arc_app.end_state not in already_visited:
                        search_queue.append(arc_app.end_state)
                        already_visited.append(arc_app.end_state)

    while (True):

        # Remove redundant agents
        agents_removed = True
        out = []
        l = full_agents
        while len(l) > 0:
            first, *rest = l
            first = set(first)
            lf = -1
            while len(first) > lf:
                lf = len(first)
                rest2 = []
                for r in rest:
                    if len(first.intersection(set(r))) > 0:
                        first |= set(r)
                    else:
                        rest2.append(r)
                rest = rest2
            out.append(first)
            l = rest

        agents_removed = len(full_agents) != len(out)
        full_agents = out

        # Remove redundant states in agents
        index = 0
        for agent in full_agents[:]:
            aux = []
            [aux.append(x) for x in agent if x not in aux]
            full_agents[index] = aux
            index = index + 1

        if agents_removed:
            # Expand agents again
            f_agents_index = 0
            for agent in full_agents[:]:
                search_queue = []
                already_visited = []

                for a_node in agent:
                    for node_app in propositional_casual_graph.node_list[a_node].arcs:
                        if node_app.arc_type == 1 and node_app.end_state not in search_queue and \
                                node_app.end_state not in agent:
                            search_queue.append(node_app.end_state)
                            already_visited.append(node_app.end_state)

                while search_queue:
                    node = search_queue.pop(0)

                    # Check if all predecessors are in V
                    bool_all = True
                    curr_arc = False
                    for node_arc in propositional_casual_graph.node_list[node].end_arcs:
                        if node_app.arc_type == 1 and (node_arc.origin_state not in full_agents[f_agents_index]):
                            # Check if the arc found is part of a 1 level loop
                            if len(propositional_casual_graph.node_list[node_arc.origin_state].end_type1_arcs) == 1:
                                if "_curr_" in propositional_casual_graph.node_list[node].name:
                                    continue
                            elif "_curr_" in propositional_casual_graph.node_list[node].name:
                                if not curr_arc:
                                    curr_arc = True
                                    continue

                            bool_all = False
                            break

                    if bool_all:
                        full_agents[f_agents_index].append(node)

                        # Check if the new variable of the agent was considered a separated agent
                        if node in or_agent_nodes:
                            redundant_agents.append(node)

                        for arc_app in propositional_casual_graph.node_list[node].arcs:
                            if arc_app.arc_type == 1 and arc_app.end_state not in already_visited:
                                search_queue.append(arc_app.end_state)
                                already_visited.append(arc_app.end_state)

                f_agents_index = f_agents_index + 1
        else:
            break

    non_agent_nodes = []
    index = 0
    for node in groups:
        found = False
        for agent in full_agents:
            if not found and index in agent:
                found = True

        if not found and isinstance(node[0].predicate, str):
            non_agent_nodes.append(index)

        index = index + 1

    # for agent in full_agents_final:
    #    agent.sort()

    return full_agents, non_agent_nodes


def assemble_basic_agents(old_basic_agents, old_group_const_arg):
    final_basic_agents = []
    do_not_agent = []
    inherit = {}

    basic_agents = []
    group_const_arg = []
    index = 0
    for agent in old_basic_agents:
        # if old_group_const_arg[index]:
        basic_agents.append(agent)
        group_const_arg.append(old_group_const_arg[index])
        index = index + 1

    for agent in basic_agents:
        agent_nodes = []
        if type(agent) is list:

            if agent[0] in do_not_agent:
                continue

            for node_a in agent:
                agent_nodes.append(node_a)
            for agent_2 in basic_agents:
                if type(agent_2) is list:
                    if agent[0] != agent_2[0]:
                        for node_2 in agent_2:
                            for node_1 in agent:
                                if node_1 < len(old_group_const_arg) and node_2 < len(old_group_const_arg):
                                    if old_group_const_arg[node_1][0] in old_group_const_arg[node_2]:
                                        for node in agent_2:
                                            agent_nodes.append(node)
                                        do_not_agent.append(agent_2[0])
                                        if agent[0] in inherit:
                                            inherit[agent[0]].append(agent_2[0])
                                        else:
                                            inherit[agent[0]] = [agent_2[0]]
                else:
                    if agent[0] != agent_2:
                        for node_1 in agent:
                            if node_1 < len(old_group_const_arg) and old_group_const_arg[node_1][0] in \
                                    old_group_const_arg[agent_2]:
                                agent_nodes.append(agent_2)
                                do_not_agent.append(agent_2)
                                if agent[0] in inherit:
                                    inherit[agent[0]].append(agent_2)
                                else:
                                    inherit[agent[0]] = [agent_2]
        else:

            if agent in do_not_agent:
                continue

            agent_nodes.append(agent)
            for agent_2 in basic_agents:
                if type(agent_2) is list:
                    if agent != agent_2[0]:
                        for node_2 in agent_2:
                            if node_2 < len(old_group_const_arg) and old_group_const_arg[agent][0] in \
                                    old_group_const_arg[node_2]:
                                for node in agent_2:
                                    agent_nodes.append(node)
                                do_not_agent.append(agent_2[0])
                                if agent in inherit:
                                    inherit[agent].append(agent_2[0])
                                else:
                                    inherit[agent] = [agent_2[0]]
                else:
                    if agent != agent_2:
                        if old_group_const_arg[agent] and \
                                (old_group_const_arg[agent][0] in old_group_const_arg[agent_2]):
                            agent_nodes.append(agent_2)
                            do_not_agent.append(agent_2)
                            if agent in inherit:
                                inherit[agent].append(agent_2)
                            else:
                                inherit[agent] = [agent_2]

        res = []
        [res.append(x) for x in agent_nodes if x not in res]
        final_basic_agents.append(res)

    for inh, out in inherit.items():
        for out_elem in out:
            for arg in old_group_const_arg[out_elem]:
                if arg not in old_group_const_arg[inh]:
                    old_group_const_arg[inh].append(arg)

    return final_basic_agents


def fill_joint_agents(basic_agents, propositional_casual_graph, depth, groups):
    joint_agents = copy.deepcopy(basic_agents)
    not_jointed = []

    # All nodes in the propositional graph are analyzed:
    #   if a node is a child of a member of an agent, the node is added to that agent but
    #   before adding it, if that node already exists in other agent, the node is not added to neither
    #   and it will analyzed in next steps
    for _ in range(depth):
        for agent in joint_agents:
            agent_additions = []
            for node in propositional_casual_graph.node_list:
                if node not in agent:
                    for arc in propositional_casual_graph.node_list[node].end_arcs:
                        if arc.arc_type == 1 and agent.count(arc.origin_state) != 0:
                            add = True
                            if node not in not_jointed:
                                for agent2 in joint_agents:
                                    if agent != agent2 and node in agent2:
                                        agent2.remove(node)
                                        if node not in not_jointed:
                                            not_jointed.append(node)
                                        add = False
                            else:
                                add = False

                            if add:
                                agent_additions.append(node)
                                break
            for addin in agent_additions:
                agent.append(addin)

    # Same but for parents
    for _ in range(depth):
        for agent in joint_agents:
            agent_additions = []
            for node in propositional_casual_graph.node_list:
                if node not in agent:
                    for arc in propositional_casual_graph.node_list[node].arcs:
                        if arc.arc_type == 1 and agent.count(arc.end_state) != 0:
                            add = True
                            if node not in not_jointed:
                                for agent2 in joint_agents:
                                    if agent != agent2 and node in agent2:
                                        agent2.remove(node)
                                        if node not in not_jointed:
                                            not_jointed.append(node)
                                        add = False
                            else:
                                add = False

                            if add:
                                agent_additions.append(node)
                                break
            for addin in agent_additions:
                agent.append(addin)

    for agent in joint_agents:
        agent.sort()

    for node in propositional_casual_graph.node_list:
        found = False
        for agent in joint_agents:
            if agent.count(node) != 0:
                found = True
                break
        if not found and node not in not_jointed and propositional_casual_graph.node_list[node].name != "free_agent":
            not_jointed.append(node)

    non_agent_nodes = []
    index = 0
    for node in groups:
        found = False
        for agent in joint_agents:
            if not found and index in agent:
                found = True

        if not found and isinstance(node[0].predicate, str):
            non_agent_nodes.append(index)
        index = index + 1

    simple_joint_agents = copy.deepcopy(joint_agents)

    # For each non added node, a backward search is launched in the casual graph (using end arcs)
    # in order to check if they can be applied by just one agent
    times = 10
    while len(not_jointed) != 0 and times != 0:
        to_remove = []
        for node in not_jointed:

            remove_node = True
            if len(propositional_casual_graph.node_list[node].end_arcs) == 0:
                to_remove.append(node)
                continue

            added_node = False
            for agent in joint_agents:
                added_agent = False
                for node_a in agent:
                    if not added_agent:
                        for arc in propositional_casual_graph.node_list[node_a].end_arcs:
                            if not added_agent and arc.arc_type == 1 and arc.origin_state == node:
                                agent.append(node)
                                added_agent = True
                                added_node = True
                    if not added_agent:
                        for arc in propositional_casual_graph.node_list[node].end_arcs:
                            if not added_agent and arc.arc_type == 1 and arc.origin_state == node_a:
                                agent.append(node)
                                added_agent = True
                                added_node = True

            if added_node:
                to_remove.append(node)

        # for node_rem in to_remove:
        #     if node_rem in not_jointed:
        #         not_jointed.remove(node_rem)

        times = times - 1

    print("We could not find an agent for the nodes: " + str(not_jointed))
    # for node in not_jointed:
    #     for agent in joint_agents:
    #         agent.append(node)

    return joint_agents, simple_joint_agents, non_agent_nodes


def fill_remaining_agents(joint_agents, propositional_casual_graph, groups, group_const_arg):
    joint_final_agents = copy.deepcopy(joint_agents)

    remaining_nodes = []
    index = 0
    for node in groups:
        if isinstance(node[0].predicate, str):
            exists = False
            for agent in joint_agents:
                if index in agent:
                    exists = True

            if not exists:
                remaining_nodes.append(index)

        index = index + 1

    for node in remaining_nodes:
        agent_index = 0
        for agent in joint_agents:
            if node < len(group_const_arg):
                for arg in group_const_arg[node]:
                    if arg in group_const_arg[agent[0]] and node not in joint_final_agents[agent_index]:
                        joint_final_agents[agent_index].append(node)
            agent_index = agent_index + 1

    remaining_nodes = []
    index = 0
    for node in groups:
        if isinstance(node[0].predicate, str):
            exists = False
            for agent in joint_final_agents:
                if index in agent:
                    exists = True

            if not exists:
                remaining_nodes.append(index)
        index = index + 1

    for agent in joint_final_agents:
        agent.sort()

    # joint_final_agents_return = fill_joint_agents(joint_final_agents, propositional_casual_graph, 2)

    # for agent in joint_final_agents_return:
    #    agent.sort()

    return joint_final_agents, remaining_nodes


def fill_free_agents(joint_agents, groups, free_agent_index):
    free_agents = copy.deepcopy(joint_agents)

    for agent in free_agents:
        agent.append(free_agent_index)
        agent.sort()

    return free_agents


def fill_func_agents(joint_agents, casual_graph, depth):
    functional_agents = copy.deepcopy(joint_agents)
    not_jointed = []

    for _ in range(depth):
        for node in casual_graph.node_list:
            if "increase" in casual_graph.node_list[node.number].name or \
                    "decrease" in casual_graph.node_list[node.number].name or \
                    "assign" in casual_graph.node_list[node.number].name or \
                    "gt" in casual_graph.node_list[node.number].name or \
                    "lt" in casual_graph.node_list[node.number].name:
                for agent in functional_agents:
                    if node not in agent:
                        for arc in casual_graph.node_list[node.number].end_arcs:
                            if arc.arc_type == 1 and agent.count(arc.origin_state) != 0:
                                agent.append(node.number)
                                break

    for agent in functional_agents:
        agent.sort()

    # Remove redundant states in agents
    functional_agents_final = []
    for agent in functional_agents:
        agent_final = []
        [agent_final.append(x) for x in agent if x not in agent_final]
        functional_agents_final.append(agent_final)

    for node in casual_graph.node_list:
        found = False
        for agent in functional_agents_final:
            if agent.count(node.number) != 0:
                found = True
                break
        if not found:
            not_jointed.append(node.number)

    return functional_agents_final


def fill_agents_actions(simple_joint_agents, joint_agents, full_func_agents, sas_task, groups, temp_task):
    agent_actions = []
    not_added = []

    for _ in joint_agents:
        agent_actions.append([])

    # Obtain common nodes between agents
    agent_common_nodes = {}
    agent_index = 0
    for agent in joint_agents:
        for node in agent:
            agent_index_2 = 0
            for agent_2 in joint_agents:
                if agent_index_2 != agent_index:
                    for node_2 in agent_2:
                        if node == node_2:
                            if node not in agent_common_nodes:
                                agent_common_nodes[node] = [False] * len(joint_agents)
                            agent_common_nodes[node][agent_index_2] = True
                            agent_common_nodes[node][agent_index] = True
                agent_index_2 = agent_index_2 + 1
        agent_index = agent_index + 1

    for ope in sas_task.operators:
        index = 0
        for agent in simple_joint_agents:
            added = False
            for eff in ope.pre_post:
                if not added and agent.count(eff[0]) != 0 and eff[1] != -7 and eff[1] != -8:
                    added = True
                    agent_actions[index].append(ope)

            for pre in ope.prevail:
                if not added and agent.count(pre[0]) != 0:
                    added = True
                    agent_actions[index].append(ope)

            index = index + 1

    internal_agents_actions = copy.deepcopy(agent_actions)
    # print(len(internal_agents_actions[0]))

    for ope in sas_task.operators:
        found = False
        for agent in agent_actions:
            if not found and agent.count(ope) != 0:
                found = True
                break
        if not found:
            not_added.append(ope)

    # If there are actions not yet assigned, try to apply them by joint_agents
    not_added_second = []
    if not_added:
        for ope in not_added:
            index = 0
            for agent in joint_agents:
                added = False
                for eff in ope.pre_post:
                    if eff[0] == 0 and temp_task:
                        continue
                    if not added and agent.count(eff[0]) != 0 and eff[1] != -7 and eff[1] != -8:
                        added = True
                        agent_actions[index].append(ope)

                for pre in ope.prevail:
                    if not added and agent.count(pre[0]) != 0:
                        added = True
                        agent_actions[index].append(ope)

                index = index + 1

    for ope in sas_task.operators:
        found = False
        for agent in agent_actions:
            if not found and agent.count(ope) != 0:
                found = True
                break
        if not found:
            not_added_second.append(ope)

    # If there are not added actions, try to add them by functions
    if not_added_second:
        for ope in not_added_second:
            index = 0
            for agent in full_func_agents:
                added = False
                for eff in ope.pre_post:
                    if eff[0] == 0 and temp_task:
                        continue
                    if not added and agent.count(eff[0]) != 0 and eff[1] != -7 and eff[1] != -8:
                        added = True
                        agent_actions[index].append(ope)

                for pre in ope.prevail:
                    if not added and agent.count(pre[0]) != 0:
                        added = True
                        agent_actions[index].append(ope)

                index = index + 1
    not_added_third = []
    for ope in sas_task.operators:
        found = False
        for agent in agent_actions:
            if not found and agent.count(ope) != 0:
                found = True
                break
        if not found:
            not_added_third.append(ope)

    # Remove redundant actions in agents
    agent_actions_final = []
    for agent in agent_actions:
        agent_final = []
        [agent_final.append(x) for x in agent if x not in agent_final]
        agent_actions_final.append(agent_final)

    # remove the shared nodes if no agent acts upon them
    print("Fix shared nodes...")
    for node, agents_com in agent_common_nodes.items():
        a_index = 0
        for exists_in_agent in agents_com[:]:
            if exists_in_agent:
                node_changes = False
                for ope in agent_actions_final[a_index]:
                    if not node_changes:
                        for eff in ope.pre_post:
                            if eff[0] == node and eff[1] != -2 and eff[1] != -3 \
                                    and eff[1] != -4 and eff[1] != -7 and eff[1] != -8 and eff[2] != -1:
                                node_changes = True
                    else:
                        break

                if not node_changes:
                    agents_com[a_index] = False
            a_index = a_index + 1

    for node in list(agent_common_nodes):
        if True not in agent_common_nodes[node]:
            agent_common_nodes.pop(node)

    # Get common actions
    extern_actions = []
    for _ in joint_agents:
        extern_actions.append([])
    # actions that intersec between the agents
    print("Obtain intersection in agents actions...")
    for node, agents_com in agent_common_nodes.items():
        index = 0
        for exists_in_agent in agents_com:
            if exists_in_agent:
                for ope in agent_actions_final[index]:
                    added = False
                    # if ope not in agent_actions_final[index]:
                    for eff in ope.pre_post:
                        if not added and node == eff[0] and eff[1] != -1 and eff[1] != -2 and eff[1] != -3 \
                                and eff[1] != -4 and eff[1] != -7 and eff[1] != -8:
                            added = True
                            extern_actions[index].append(ope)
                    for pre in ope.prevail:
                        if not added and node == pre[0]:
                            added = True
                            extern_actions[index].append(ope)
            index = index + 1

    extern_actions_final = []
    for agent in extern_actions:
        agent_ex_final = []
        [agent_ex_final.append(x) for x in agent if x not in agent_ex_final]
        extern_actions_final.append(agent_ex_final)

    # obtain invalid actions and remove them for each agent
    out_var_actions = []
    agent_index = 0
    for agent_ac in agent_actions_final:
        agent_rem = []
        for ope in agent_ac:
            added = False
            for eff in ope.pre_post:
                if not not_added and eff[0] not in full_func_agents[agent_index] and eff[1] != -7 and eff[1] != -8:
                    not_added = True
                    agent_rem.append(ope)
            for pre in ope.prevail:
                if not not_added and pre[0] not in full_func_agents[agent_index]:
                    not_added = True
                    agent_rem.append(ope)
        out_var_actions.append(agent_rem)
        agent_index = agent_index + 1

    return agent_actions_final, extern_actions_final, agent_common_nodes, out_var_actions


def fill_agents_metric(joint_agents, functional_agents, sas_task):
    agent_metrics = []

    for _ in joint_agents:
        agent_metrics.append([])

    for metr in sas_task.translated_metric:
        index = 0
        for agent in functional_agents:
            if agent.count(metr) != 0:
                agent_metrics[index].append(metr)
            index = index + 1

    if sas_task.metric:
        for agent in agent_metrics:
            agent.insert(0, sas_task.metric[0])

    return agent_metrics


def fill_agents_init(joint_agents, functional_agents, sas_task):
    agent_init = []

    for _ in joint_agents:
        agent_init.append({})

    init_pos = 0
    for init_value in sas_task.init.values:
        index = 0
        for agent in functional_agents:
            if agent.count(init_pos) != 0:
                agent_init[index][init_pos] = init_value
            index = index + 1
        init_pos = init_pos + 1

    return agent_init


def fill_agents_goals_timed_facts(joint_agents, functional_agents, agents_actions, agents_metric, agents_init,
                                  casual_graph,
                                  sas_task, groups, time_value, temp_task):
    agent_goals = []
    agent_coop_goals = []
    goals_to_analyze = []
    time_clock_per_agent = []

    for _ in joint_agents:
        agent_goals.append([])
        agent_coop_goals.append([])
        time_clock_per_agent.append(0.0)

    goals_added = []
    print(sas_task.timed_goals_list)
    while len(goals_added) != len(sas_task.timed_goals_list.items()):
        min_time_value = -1.0
        index_min_time_value = -1
        index = 0
        # get goal with min timed fact
        for timed_goal, timed_facts in sas_task.timed_goals_list.items():
            if timed_goal in goals_added:
                pass
            else:
                for timed_fact in timed_facts:
                    if timed_fact[1] != -1:
                        if min_time_value == -1.0 or min_time_value > float(timed_fact[2]):
                            min_time_value = float(timed_fact[2])
                            index_min_time_value = index
                            min_timed_goal = timed_goal
            index = index + 1

        if index_min_time_value == -1:
            print("Error in the timed goal assignment")
            return False
        # get agent with min internal clock
        agent_index = 0
        min_agent_index = 0
        min_agent_clock = -1.0
        for agent_clock in time_clock_per_agent:
            if agent_clock < min_agent_clock or min_agent_clock == -1.0:
                min_agent_clock = agent_clock
                min_agent_index = agent_index
            agent_index = agent_index + 1

        time_clock_per_agent[min_agent_index] = time_clock_per_agent[min_agent_index] + min_time_value
        agent_goals[min_agent_index].append(min_timed_goal)
        goals_added.append(min_timed_goal)

        print(agent_goals)
        print(index_min_time_value)
        print(goals_added)
        print(min_time_value)
        print(time_clock_per_agent)

    return agent_goals, agent_coop_goals, goals_to_analyze, True


def fill_agents_goals(joint_agents, functional_agents, agents_actions, agents_metric, agents_init, casual_graph,
                      sas_task, groups, time_value, temp_task):
    agent_goals = []
    agent_coop_goals = []
    goals_to_analyze = []

    for _ in joint_agents:
        agent_goals.append([])
        agent_coop_goals.append([])

    # If there are goals_to_analyze, we have to assign them by analyzing the problem
    agents_possible_transitions, agents_possible_transitions_dict, agents_possible_transition_origins_dict = \
        get_agents_possible_transitions(agents_actions, functional_agents)
    # agents_necessary_conditions, agents_necessary_conditions_dict = get_agents_necessary_conditions(agents_actions,
    #                                                                                                 functional_agents)
    # First find if there are goals that belong only to one agent
    for goal in sas_task.goal.pairs:
        goals_to_analyze.append([goal[0], goal[1]])

    un_goals_to_analyze = []

    for goal in goals_to_analyze:
        if goal not in un_goals_to_analyze:
            un_goals_to_analyze.append(goal)

    correct_assignment = True
    if not un_goals_to_analyze:
        correct_assignment = False

    # agents_impossible_to_attain = []
    # index = 0
    # for agent_necessary_conditions in agents_necessary_conditions:
    #     agents_impossible_to_attain.append(
    #         [k for k in agent_necessary_conditions if k not in agents_possible_transitions[index]])
    #     index = index + 1

    # index = 0
    # for imp in agents_impossible_to_attain:
    #     print("Predicates impossible to attain by agent " + str(index) + ":")
    #     print(str(imp))
    #     for elem in imp:
    #        print(str(groups[elem[0]][elem[1]]))
    #    index = index + 1

    # If there are goals_to_analyze, we have to assign them by analyzing the problem
    estimations_agent_goals, cooperation_goals_estimations = fill_complex_agents_goals(
        un_goals_to_analyze, functional_agents,
        agents_actions, agents_metric, agents_init,
        sas_task, groups, time_value, temp_task,
        agents_possible_transitions_dict,
        agents_possible_transition_origins_dict)

    # goal_index = 0
    # goals_to_reanalyze = []
    # for goal_estimations in estimations_agent_goals:
    #     if len(goal_estimations) == goal_estimations.count([]):
    #         print("Goal " + str(un_goals_to_analyze[goal_index]) + " -- " + str(
    #             groups[un_goals_to_analyze[goal_index][0]][
    #                un_goals_to_analyze[goal_index][1]]) + " cannot be achieved by any single agent.")
    #       goals_to_reanalyze.append((un_goals_to_analyze[goal_index], goal_index))
    #   goal_index = goal_index + 1

    # If there are goals_to_analyze, we have to assign them by analyzing the problem
    # estimations_agent_goals = fill_complex_joint_agents_goals(goals_to_reanalyze, functional_agents,
    #                                                           agents_actions, agents_metric, agents_init,
    #                                                           sas_task, groups, time_value, temp_task,
    #                                                           estimations_agent_goals)

    # Now the calculated objectives will be assigned
    metric_total_agent = []

    for _ in joint_agents:
        metric_total_agent.append(0)

    goal_index = 0
    for goal_estimations in estimations_agent_goals:
        min_vals = []
        agent_index = 0
        goal_reachable = False
        for agent_estimations in goal_estimations:
            if agent_estimations:
                goal_reachable = True
            if not agent_estimations:
                min_value = 99999
            else:
                min_value = agent_estimations[0].estimated_metric
                for node in agent_estimations:
                    if node.estimated_metric < min_value:
                        min_value = node.estimated_metric
            min_vals.append(min_value)
            agent_index = agent_index + 1

        # print("min vals: " + str(min_vals))

        # Check if the min value for this
        # Deal with cooperation goals:
        already_assigned = False
        for coop_goal in cooperation_goals_estimations[:]:
            a_order = coop_goal[0][0]
            subgoals = coop_goal[0][1]
            if un_goals_to_analyze[goal_index] == subgoals[0]:
                # If the goal has both coordination and non-coordination estimations, pick the cheapest
                # if min(min_vals) > coop_goal[1].estimated_metric:
                if False:
                    subgoal_index = 0
                    max_len = 0
                    for goal in subgoals:
                        agent_coop_goals[a_order[subgoal_index]].append([len(a_order) - subgoal_index - 1, goal,
                                                                         subgoals[0]])
                        max_len = len(agent_coop_goals[a_order[subgoal_index]])
                        subgoal_index = subgoal_index + 1
                        already_assigned = True

                    for coop_goals in agent_coop_goals:
                        if len(coop_goals) < max_len:
                            coop_goals.append([-1, [], subgoals[0]])

                    cooperation_goals_estimations.remove(coop_goal)
                else:
                    cooperation_goals_estimations.remove(coop_goal)
                    break

        # Assign goal
        if goal_reachable and not already_assigned:
            estimations = []
            agent_analysis_index = 0
            for agent_analysis in min_vals:
                estimations.append(metric_total_agent[agent_analysis_index] + agent_analysis)
                #  estimations.append(agent_analysis)
                agent_analysis_index = agent_analysis_index + 1
            # print(str(metric_total_agent))
            # print(str(estimations))
            agent_index_chosen = estimations.index(min(estimations))
            # print("goal " + str(un_goals_to_analyze[goal_index]) + " to index " + str(agent_index_chosen))

            agent_goals[agent_index_chosen].append(un_goals_to_analyze[goal_index])
            # metric_total_agent[agent_index_chosen] = metric_total_agent[agent_index_chosen] + min(estimations)
            metric_total_agent[agent_index_chosen] = min(estimations)

        goal_index = goal_index + 1

    # Deal with remaining cooperation goals:
    for coop_goal in cooperation_goals_estimations[:]:
        a_order = coop_goal[0][0]
        subgoals = coop_goal[0][1]
        subgoal_index = 0
        max_len = 0
        for goal in subgoals:
            agent_coop_goals[a_order[subgoal_index]].append([len(a_order) - subgoal_index - 1, goal, subgoals[0]])
            max_len = len(agent_coop_goals[a_order[subgoal_index]])
            subgoal_index = subgoal_index + 1

        for coop_goals in agent_coop_goals:
            if len(coop_goals) < max_len:
                coop_goals.append([-1, [], subgoals[0]])

    if correct_assignment:
        a_index = 0
        for agent_go in agent_goals:
            print("Non-coop goals for agent " + str(a_index) + ": ")
            print("     " + str(agent_go)[1:-1])
            a_index = a_index + 1
            for go in agent_go:
                if go in goals_to_analyze:
                    goals_to_analyze.remove(go)

        if goals_to_analyze:
            a_index = 0
            for agent_go in agent_coop_goals:
                print("Coop goals for agent " + str(a_index) + ": ")
                print("     " + str(agent_go)[1:-1])
                a_index = a_index + 1
                for go in agent_go:
                    if go[0] != -1 and go[2] in goals_to_analyze:
                        goals_to_analyze.remove(go[2])

        if len(joint_agents) == 1:
            for gen_goal in goals_to_analyze:
                agent_goals[0].append(gen_goal)
            goals_to_analyze = []

        if goals_to_analyze:
            print("Goals without agent assigned: " + str(goals_to_analyze))

    return agent_goals, agent_coop_goals, goals_to_analyze, correct_assignment


def fill_complex_agents_goals(goals_to_analyze, functional_agents, agents_actions, agents_metric,
                              agents_init, sas_task, groups, time_value, temp_task, agents_possible_transitions_dict,
                              agents_possible_transition_origins_dict):
    analyzed_agent_goals = []
    cooperation_goals_estimations = []
    goal_index = 0

    # We have to do a backward search from the goals to the init state
    for goal in goals_to_analyze:
        print("The goal " + str(goal[0]) + ":" + str(goal[1]) + " -- " + str(
            groups[goal[0]][goal[1]]) + " ... launching non delete search")
        continue_analysis = True

        goal = [goal[0], goal[1]]
        # Go backwards searching for necessary init states
        agent_index = 0
        agent_sol_estimations = []

        for agent in functional_agents:

            # Checkm if the agent can achieve the goal
            if goal[0] in agents_possible_transitions_dict[agent_index]:
                if goal[1] not in agents_possible_transitions_dict[agent_index][goal[0]]:
                    print(
                        "The goal " + str(goal[0]) + ":" + str(goal[1]) +
                        " cannot be achieved by agent " + str(agent_index) + ", no search will be launched.")
                    agent_sol_estimations.append([])
                    agent_index = agent_index + 1
                    continue

            agent_sol_estimations.append([])
            agent_actions = agents_actions[agent_index]

            plan_length_metric = False
            agent_metric = agents_metric[agent_index]
            if not agent_metric:
                plan_length_metric = True
            agent_init = copy.deepcopy(agents_init[agent_index])

            search_queue = []
            init_node = EstimatedMetricNode([], agent_init, 0, [goal], [])
            search_queue.append((init_node, 0))
            visited_states = []
            coordination_points = {}
            g_index = 0
            for _ in groups:
                coordination_points[g_index] = []
                g_index = g_index + 1

            # Set a time limit for each goal and agent
            timeout_start = time.time()

            max_cost = 9999999
            coordination_points_found = False

            # min_heur_node = (init_node, -1)
            while search_queue and time.time() < timeout_start + (int(time_value) / 1000):
                (node, h_node) = search_queue.pop(0)
                # if min_heur_node[1] > h_node or min_heur_node[1] == -1:
                #     min_heur_node = (node, h_node)

                # Check if the agent has a pending to start action
                if temp_task:
                    last_action_end = False
                else:
                    last_action_end = True
                if node.app_actions:
                    last_action_name = node.app_actions[-1].name
                    if temp_task and "_end " in last_action_name:
                        last_action_end = True

                # Search actions that can set the state "node"
                for action in agent_actions:
                    added = False
                    if node.app_actions:
                        if temp_task and last_action_end and "_end " in action.name:
                            continue
                        if temp_task and not last_action_end and "_start " in action.name:
                            continue
                    for effect in action.pre_post:
                        for pending_subgoal in node.pending_additions:
                            if effect[1] != -7 and effect[1] != -8 and \
                                    effect[0] == pending_subgoal[0] and effect[2] == pending_subgoal[1] and not added:

                                # new_action_name = "_".join(
                                #    (((((action.name.split(" "))[0]).split("("))[1]).split("_"))[:-1])

                                # Create new current state for the new nodes
                                new_node_state = copy.deepcopy(node.curr_state)
                                new_node_state[effect[0]] = effect[2]

                                # If an action that can set the effect is found
                                # create a new state with all preconditions not met
                                # and add it to the queue

                                if plan_length_metric:
                                    new_node_cost = copy.deepcopy(node.estimated_metric + 1)
                                else:
                                    new_node_cost = copy.deepcopy(node.estimated_metric + action.cost)
                                new_node_actions = copy.deepcopy(node.app_actions)
                                new_node_actions.append(action)

                                last_subgoal_attained = []

                                new_node_subgoals = copy.deepcopy(node.pending_additions)
                                new_node_subgoals.remove(pending_subgoal)
                                last_subgoal_attained.append(pending_subgoal)
                                # Check if the action removes other pending goals too
                                for effect_2 in action.pre_post:
                                    if [effect_2[0], effect_2[2]] in new_node_subgoals:
                                        new_node_subgoals.remove([effect_2[0], effect_2[2]])
                                        last_subgoal_attained.append([effect_2[0], effect_2[2]])

                                new_node_actions[-1].last_subgoal_attained = last_subgoal_attained
                                new_node_achieved_subgoals = copy.deepcopy(node.achieved_subgoals)
                                # new_node_achieved_subgoals.append(pending_subgoal)

                                for pre in action.prevail:
                                    if agent_init[pre[0]] != pre[1] and \
                                            new_node_subgoals.count([pre[0], pre[1]]) == 0 and \
                                            new_node_achieved_subgoals.count([pre[0], pre[1]]) == 0:
                                        new_node_subgoals.append([pre[0], pre[1]])

                                        # Check if the new subgoal is a coordination point
                                        if agent_init[pre[0]] not in \
                                                agents_possible_transition_origins_dict[agent_index][pre[0]] and \
                                                pre[1] not in coordination_points[pre[0]]:
                                            # print("The atom " + str(groups[pre[0]][pre[1]]) + "is a coordination point")
                                            coordination_points_found = True
                                            coordination_points[pre[0]].append(pre[1])

                                for effect_2 in action.pre_post:
                                    if (effect_2[1] != -2 and effect_2[1] != -3 and effect_2[1] != -4 and
                                        effect_2[1] != -5 and effect_2[1] != -6 and
                                        effect_2[1] != -7 and effect_2[1] != -8) and \
                                            effect_2[1] != -1 and \
                                            agent_init[effect_2[0]] != effect_2[1]:
                                        if new_node_subgoals.count([effect_2[0], effect_2[1]]) == 0 and \
                                                new_node_achieved_subgoals.count([effect_2[0], effect_2[1]]) == 0:
                                            new_node_subgoals.append([effect_2[0], effect_2[1]])
                                            # Check if the new subgoal is a coordination point
                                            if agent_init[effect_2[0]] not in \
                                                    agents_possible_transition_origins_dict[agent_index][effect_2[0]] \
                                                    and effect_2[1] not in coordination_points[effect_2[0]]:
                                                # print("The atom " +
                                                #       str(groups[effect_2[0]][effect_2[1]]) + "is a coordination point")
                                                coordination_points_found = True
                                                coordination_points[effect_2[0]].append(effect_2[1])

                                new_node = EstimatedMetricNode(new_node_actions, new_node_state, new_node_cost,
                                                               new_node_subgoals, new_node_achieved_subgoals)

                                added = True

                                if len(new_node_subgoals) == 0:
                                    # start_act = len([k for k in new_node.app_actions if "_start" in k.name])
                                    # end_act = len([k for k in new_node.app_actions if "_end" in k.name])
                                    if new_node.estimated_metric < max_cost:  # and start_act == end_act:
                                        print(
                                            "The goal " + str(goal[0]) + ":" + str(goal[1]) +
                                            " has solution for agent (" + str(agent_index) + ") -- estimation -> " +
                                            str(new_node.estimated_metric) + " < " + str(max_cost))

                                        max_cost = new_node.estimated_metric

                                        agent_sol_estimations[agent_index].append(new_node)
                                else:
                                    if new_node.estimated_metric < max_cost:
                                        if (new_node.curr_state, new_node.pending_additions) not in visited_states:
                                            visited_states.append((new_node.curr_state, new_node.pending_additions))
                                            if last_action_end:
                                                search_queue.append((new_node, calculate_heuristic(new_node)))
                                            else:
                                                search_queue.append((new_node, h_node))
                                            search_queue.sort(key=take_second)
                                        # search_queue.insert(0, new_node)

            if len(search_queue) == 0:
                print("Completly explored search space!")
            if not agent_sol_estimations[agent_index]:
                print("No solution was found for agent " + str(agent_index))
                if coordination_points_found and continue_analysis:
                    print("But it seems like there are some coordination points")
                    # print(str(coordination_points))
                    a_order, solution = deal_with_coordination_points_for_goal(
                        coordination_points, agents_possible_transition_origins_dict, goal,
                        functional_agents, agents_actions, sas_task, groups, time_value, temp_task)

                    if a_order[0]:
                        print("A solution was found, this goal is considered to be analyzed:")
                        print("Agents used: " + str(a_order[0]))
                        print("Subgoals " + str(a_order[1]))

                        continue_analysis = False
                        # agent_sol_estimations[a_order[0]].append(solution)
                        cooperation_goals_estimations.append((a_order, solution))

            agent_index = agent_index + 1

        analyzed_agent_goals.append(agent_sol_estimations)

        goal_index = goal_index + 1

    return analyzed_agent_goals, cooperation_goals_estimations


def deal_with_coordination_points_for_goal(coordination_points, agents_possible_transition_origins_dict, goal,
                                           functional_agents, agents_actions, sas_task, groups, time_value, temp_task):
    result = [[], []]
    obtained_solutions = []
    print("The goal " + str(goal[0]) + ":" + str(goal[1]) + " -- " + str(
        groups[goal[0]][goal[1]]) + " ... launching non delete search with the full SAS task.")

    actions = sas_task.operators

    plan_length_metric = False
    metric = sas_task.translated_metric
    if not metric:
        plan_length_metric = True
    init = {}
    index = 0
    # print(str(sas_task.init.values))
    for init_val in sas_task.init.values:
        init[index] = init_val
        index = index + 1
    # print(str(init))

    search_queue = []
    init_node = EstimatedMetricNode([], init, 0, [goal], [])
    search_queue.append((init_node, 0))
    visited_states = []
    coordination_points = {}
    g_index = 0
    for _ in groups:
        coordination_points[g_index] = []
        g_index = g_index + 1

    # Set a time limit for each goal and agent
    timeout_start = time.time()

    max_cost = 9999999

    # min_heur_node = (init_node, -1)
    while search_queue and time.time() < timeout_start + ((int(time_value)/1000) * len(functional_agents)):
        (node, h_node) = search_queue.pop(0)
        # if min_heur_node[1] > h_node or min_heur_node[1] == -1:
        #     min_heur_node = (node, h_node)

        # Check if the agent has a pending to start action
        if temp_task:
            last_action_end = False
        else:
            last_action_end = True
        if node.app_actions:
            last_action_name = node.app_actions[-1].name
            if temp_task and "_end " in last_action_name:
                last_action_end = True

        # Search actions that can set the state "node"
        for action in actions:
            added = False
            if node.app_actions:
                if temp_task and last_action_end and "_end " in action.name:
                    continue
                if temp_task and not last_action_end and "_start " in action.name:
                    continue
            for effect in action.pre_post:
                for pending_subgoal in node.pending_additions:
                    if effect[1] != -7 and effect[1] != -8 and \
                            effect[0] == pending_subgoal[0] and effect[2] == pending_subgoal[1] and not added:

                        # new_action_name = "_".join(
                        #    (((((action.name.split(" "))[0]).split("("))[1]).split("_"))[:-1])

                        # Create new current state for the new nodes
                        new_node_state = copy.deepcopy(node.curr_state)
                        new_node_state[effect[0]] = effect[2]

                        # If an action that can set the effect is found
                        # create a new state with all preconditions not met
                        # and add it to the queue

                        if plan_length_metric:
                            new_node_cost = copy.deepcopy(node.estimated_metric + 1)
                        else:
                            new_node_cost = copy.deepcopy(node.estimated_metric + action.cost)
                        new_node_actions = copy.deepcopy(node.app_actions)
                        new_node_actions.append(action)

                        last_subgoal_attained = []

                        new_node_subgoals = copy.deepcopy(node.pending_additions)
                        new_node_subgoals.remove(pending_subgoal)
                        last_subgoal_attained.append(pending_subgoal)
                        # Check if the action removes other pending goals too
                        for effect_2 in action.pre_post:
                            if [effect_2[0], effect_2[2]] in new_node_subgoals:
                                new_node_subgoals.remove([effect_2[0], effect_2[2]])
                                last_subgoal_attained.append([effect_2[0], effect_2[2]])

                        new_node_actions[-1].last_subgoal_attained = last_subgoal_attained
                        new_node_achieved_subgoals = copy.deepcopy(node.achieved_subgoals)
                        # new_node_achieved_subgoals.append(pending_subgoal)

                        for pre in action.prevail:
                            if init[pre[0]] != pre[1] and \
                                    new_node_subgoals.count([pre[0], pre[1]]) == 0 and \
                                    new_node_achieved_subgoals.count([pre[0], pre[1]]) == 0:
                                new_node_subgoals.append([pre[0], pre[1]])

                        for effect_2 in action.pre_post:
                            if (effect_2[1] != -2 and effect_2[1] != -3 and effect_2[1] != -4 and
                                effect_2[1] != -5 and effect_2[1] != -6 and
                                effect_2[1] != -7 and effect_2[1] != -8) and \
                                    effect_2[1] != -1 and \
                                    init[effect_2[0]] != effect_2[1]:
                                if new_node_subgoals.count([effect_2[0], effect_2[1]]) == 0 and \
                                        new_node_achieved_subgoals.count([effect_2[0], effect_2[1]]) == 0:
                                    new_node_subgoals.append([effect_2[0], effect_2[1]])

                        new_node = EstimatedMetricNode(new_node_actions, new_node_state, new_node_cost,
                                                       new_node_subgoals, new_node_achieved_subgoals)

                        added = True

                        if len(new_node_subgoals) == 0:
                            if new_node.estimated_metric < max_cost:  # and start_act == end_act:
                                print(
                                    "The goal " + str(goal[0]) + ":" + str(goal[1]) +
                                    " has solution for relaxed SAS task -- estimation -> " +
                                    str(new_node.estimated_metric) + " < " + str(max_cost))

                                max_cost = new_node.estimated_metric

                                obtained_solutions.append(new_node)
                        else:
                            if new_node.estimated_metric < max_cost:
                                if (new_node.curr_state, new_node.pending_additions) not in visited_states:
                                    visited_states.append((new_node.curr_state, new_node.pending_additions))
                                    if last_action_end:
                                        search_queue.append((new_node,
                                                             calculate_heuristic_full_task(new_node,
                                                                                           coordination_points)))
                                    else:
                                        search_queue.append((new_node, h_node))
                                    search_queue.sort(key=take_second)
                                # search_queue.insert(0, new_node)

    order = []
    if obtained_solutions:
        # print(str(groups[goal[0]][init[goal[0]]]))
        for act in obtained_solutions[-1].app_actions:
            # print(act.name)
            agents_found = []
            for agent_act in agents_actions:
                found = False
                for op in agent_act:
                    if op.name == act.name:
                        found = True
                agents_found.append(found)
            # print(str(agents_found))
            order.append(agents_found.index(True))
        # print(str(groups[goal[0]][goal[1]]))
        # print("Agents order: " + str(order))

    subgoals = []
    subgoals.append(goal)
    last = -1
    index = 0
    for elem in order:
        if elem != last:
            last = elem
            result[0].append(elem)
            if index != 0:
                for l_goal in obtained_solutions[-1].app_actions[index].last_subgoal_attained:
                    subgoals.append(l_goal)
        index = index + 1

    result[1] = subgoals
    if obtained_solutions:
        obtained_solution = obtained_solutions[-1]
    else:
        obtained_solution = []

    # print("Agents order: " + str(result[0]))
    # print("Subgoals for echa agent: " + str(subgoals))
    # for subgoal in subgoals:
    # for subgo in subgoal:
    #     print(str(groups[subgoal[0]][subgoal[1]]))
    return result, obtained_solution


def get_agents_possible_transitions(agents_actions, functional_agents):
    agents_possible_transitions = []
    agents_possible_transitions_dict = []
    agents_possible_transition_origins_dict = []

    index = 0
    for agent_actions in agents_actions:
        agent_possible_transitions = []
        agent_possible_transitions_dict = {}
        agent_possible_transition_origins_dict = {}
        for node in functional_agents[index]:
            agent_possible_transitions_dict[node] = []
            agent_possible_transition_origins_dict[node] = []
        for op in agent_actions:
            for effect in op.pre_post:
                if effect[1] != -2 and effect[1] != -3 and effect[1] != -4 and \
                        effect[1] != -5 and effect[1] != -6 and \
                        effect[1] != -7 and effect[1] != -8 and \
                        [effect[0], effect[2]] not in agent_possible_transitions:
                    agent_possible_transitions.append([effect[0], effect[2]])
                    agent_possible_transitions_dict[effect[0]].append(effect[2])
                    agent_possible_transition_origins_dict[effect[0]].append(effect[1])

        agents_possible_transitions.append(agent_possible_transitions)
        agents_possible_transitions_dict.append(agent_possible_transitions_dict)
        agents_possible_transition_origins_dict.append(agent_possible_transition_origins_dict)
        index = index + 1

    return agents_possible_transitions, agents_possible_transitions_dict, agents_possible_transition_origins_dict


def get_agents_necessary_conditions(agents_actions, functional_agents):
    agents_necessary_conditions = []
    agents_necessary_conditions_dict = []

    index = 0
    for agent_actions in agents_actions:
        agent_necessary_conditions = []
        agent_necessary_conditions_dict = {}
        for node in functional_agents[index]:
            agent_necessary_conditions_dict[node] = []
        for op in agent_actions:
            for pre in op.prevail:
                if pre[1] != -1 and \
                        [pre[0], pre[1]] not in agent_necessary_conditions:
                    agent_necessary_conditions.append([pre[0], pre[1]])
                    agent_necessary_conditions_dict[pre[0]].append(pre[1])

        agents_necessary_conditions.append(agent_necessary_conditions)
        agents_necessary_conditions_dict.append(agent_necessary_conditions_dict)
        index = index + 1
    return agents_necessary_conditions, agents_necessary_conditions_dict


def calculate_heuristic(node):
    h_value = len(node.pending_additions) - (len(node.app_actions) / 100)
    return h_value


def calculate_heuristic_full_task(node, coordination_points):
    achieved_coor = 0
    for coor_p in coordination_points:
        if coor_p in coordination_points:
            achieved_coor = achieved_coor + 1

    h_value = len(node.pending_additions) - (len(node.app_actions) / 100) - (achieved_coor / 10)
    return h_value


def take_second(elem):
    return elem[1]


def create_gexf_casual_graph_files(casual_graph, type):
    index = 0
    today = date.today()
    d1 = today.strftime("%d/%m/%Y")

    if WINDOWS:
        save_path = "C:\\Users\\JavCa\\PycharmProjects\\pddl2-SAS-translate2\\graphs"
    else:
        save_path = "graphs"

    if type == 0:
        filelist = glob.glob(os.path.join(save_path, "*.csv"))
        for f in filelist:
            os.remove(f)

        filelist = glob.glob(os.path.join(save_path, "*.gexf"))
        for f in filelist:
            os.remove(f)

        filelist = glob.glob(os.path.join(save_path + "/metric", "*.gexf"))
        for f in filelist:
            os.remove(f)

        filelist = glob.glob(os.path.join(save_path + "/functional_graphs_inv", "*.gexf"))
        for f in filelist:
            os.remove(f)

    propo = False
    if type == 0:
        file_name = "casual_graph.gexf"
    elif type == 1:
        file_name = "casual_graph_type1.gexf"
    if type == 2:
        file_name = "casual_graph_type2.gexf"
    if type == 3:
        propo = True
        file_name = "propositional_casual_graph.gexf"
    if type == 4:
        propo = True
        file_name = "propositional_casual_graph_type1.gexf"
    if type == 5:
        propo = True
        file_name = "propositional_casual_graph_type2.gexf"
    if type == 6:
        propo = True
        file_name = "propositional_casual_cycles1_graph.gexf"
    if type == 7:
        propo = True
        file_name = "propositional_casual_cycles2_graph.gexf"

    full_name = os.path.join(save_path, file_name)
    f = open(full_name, "w")
    f.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n")
    f.write("<gexf xmlns=\"http://www.gexf.net/1.2draft\" version=\"1.2\">\n")
    f.write("\t<meta lastmodifieddate=\"" + d1 + "\">\n")
    f.write("\t\t<creator>Javier Caballero</creator>\n")
    f.write("\t\t<description>" + file_name + "</description>\n")
    f.write("\t</meta>\n")
    f.write("\t<graph mode=\"static\" defaultedgetype=\"directed\">\n")
    f.write("\t\t<nodes>\n")
    for node in casual_graph.node_list:
        if propo:
            node = casual_graph.node_list[node]
        if node.name != '<none of those>':
            f.write("\t\t\t<node id=\"" + str(node.number) + "\" label=\"" + node.name + "\" />\n")
    f.write("\t\t</nodes>\n")

    f.write("\t\t<edges>\n")
    for node in casual_graph.node_list:
        if propo:
            node = casual_graph.node_list[node]
        for arc in node.arcs:
            if arc.origin_state != "<none of those>" and arc.end_state != "<none of those>":
                f.write(
                    "\t\t\t<edge id=\"" + arc.arc_id + "--" + str(arc.arc_type) + "\" label=\"" + arc.arc_id + "--" +
                    str(arc.arc_type) + "\" source=\"" + str(arc.origin_state) + "\" target=\"" +
                    str(arc.end_state) + "\" />\n")
    f.write("\t\t</edges>\n")
    f.write("\t</graph>\n")
    f.write("</gexf>\n")
    f.close()


# This function will rely on symmetries and other characteristics to check
# how many agent types there are in a given problem
def calculate_agent_types(agents_fdtgs, agents_fdtg_metric, agents_causal_graph, groups):
    agent_types = []

    # [number of single graphs in total-time and metric,
    # number of root nodes and degrees in agent causal graph]
    agent_types_characteristics = []
    agent_index = 0
    for agent_fdtgs in agents_fdtgs:

        agent_characteristics = []

        root_nodes_time, n_root_nodes_time = count_root_nodes(agent_fdtgs[0])
        root_nodes_metric, n_root_nodes_metric = count_root_nodes(agents_fdtg_metric[agent_index])
        # print("Number of root nodes for agent " + str(agent_index) + " and total-time: " + str(len(root_nodes_time)))
        # print("Number of root nodes for agent " + str(agent_index) + " and metric: " + str(len(root_nodes_metric)))

        single_graphs_time = count_single_graphs(agent_fdtgs[0])
        single_graphs_metric = count_single_graphs(agents_fdtg_metric[agent_index])
        print("Number of single graphs for agent " + str(agent_index) + " and total-time: " + str(
            len(single_graphs_time)))
        print(
            "Number of single graphs for agent " + str(agent_index) + " and metric: " + str(len(single_graphs_metric)))

        agent_characteristics.append([len(single_graphs_time), len(single_graphs_metric)])

        agent_origin_nodes = obtain_origin_nodes(agents_causal_graph[agent_index])
        agent_to_remove = []
        for or_node in agent_origin_nodes:
            if len(groups[or_node]) < 2:
                agent_to_remove.append(or_node)
        for node in agent_to_remove:
            del agent_origin_nodes[node]

        print("Number of origin nodes for agent " + str(agent_index) + ": " + str(len(agent_origin_nodes)))

        agent_characteristics.append(len(agent_origin_nodes))

        agent_types_characteristics.append(agent_characteristics)

        agent_index = agent_index + 1

    agent_index = 0
    for agent_charac in agent_types_characteristics:
        type_match = False
        for type in agent_types:
            if agent_charac[0] == type[0][0] and agent_charac[1] == type[0][1]:
                type_match = True
                type[1].append(agent_index)
                break

        if not type_match:
            agent_types.append([agent_charac, [agent_index]])

        agent_index = agent_index + 1

    return agent_types


def count_root_nodes(graph):
    agent_types = []
    types = 0

    already_explored = []
    current_node_list = []

    def explore_node(node_name, arcs):
        if node_name not in already_explored:
            current_node_list.append(node_name)
            already_explored.append(node_name)
            for arc in arcs:
                explore_node(arc.end_state, graph.node_list[arc.end_state])

    for node_name, arcs in graph.node_list.items():
        if node_name not in already_explored:
            explore_node(node_name, arcs)
            agent_types.append(copy.deepcopy(current_node_list))
            current_node_list = []
            types = types + 1

    return agent_types, types


def count_single_graphs(graph):
    agent_types = []

    for node_name, arcs in graph.node_list.items():
        found = False
        node_list_type_index = 0
        for node_list_type in agent_types:
            if not found and node_name in node_list_type:
                agent_types[node_list_type_index].append(node_name)
                found = True
                break
            node_list_type_index = node_list_type_index + 1

        if not found:
            for arc in arcs:
                node_list_type_index = 0
                for node_list_type in agent_types:
                    if not found and arc.end_state in node_list_type:
                        agent_types[node_list_type_index].append(node_name)
                        found = True
                        break
                    node_list_type_index = node_list_type_index + 1

        if not found:
            agent_types.append([])
            agent_types[-1].append(node_name)

    # Refinement
    refined = True
    while refined:
        refined = False

        index_1 = 0
        for agent_type_1 in agent_types:
            index_2 = 0
            for agent_type_2 in agent_types:
                if not refined and index_1 != index_2:
                    for node_2 in agent_type_2:
                        if not refined and node_2 in agent_type_1:
                            refined = True
                            # Merge two groups
                            to_merge = copy.deepcopy(agent_type_2)
                            for node in to_merge:
                                if node not in agent_types[index_1]:
                                    agent_types[index_1].append(node)
                            del agent_types[index_2]
                            break

                        if not refined:
                            for arc in graph.node_list[node_2]:
                                if arc.end_state in agent_type_1:
                                    refined = True
                                    # Merge two groups
                                    to_merge = copy.deepcopy(agent_type_2)
                                    for node in to_merge:
                                        if node not in agent_types[index_1]:
                                            agent_types[index_1].append(node)
                                    del agent_types[index_2]
                                    break
                if refined:
                    break
                index_2 = index_2 + 1
            if refined:
                break
            index_1 = index_1 + 1
    return agent_types
