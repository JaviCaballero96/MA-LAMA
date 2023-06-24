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
    def __init__(self, app_actions, curr_state, estimated_metric, pending_additions):
        self.app_actions = app_actions
        self.curr_state = curr_state
        self.estimated_metric = estimated_metric
        self.pending_additions = pending_additions


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
    return -1


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
            add_arc(var_no, pre_spec, post, op)
    for axiom in task.axioms:
        var_no, val = axiom.effect
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
                if (n_pre_spec == -2 or n_pre_spec == -3 or n_pre_spec == -4 or n_pre_spec == -5 or n_pre_spec == -6) \
                        and n_var_no == index:
                    eff_index_2 = 0
                    for var_no, pre_spec, post, cond in op.pre_post:
                        if eff_index_1 != eff_index_2 and (n_pre_spec != -2 and n_pre_spec != -3 and n_pre_spec != -4
                                                           and n_pre_spec != -5 and n_pre_spec != -6):
                            if translation_key[var_no][pre_spec] != '<none of those>':
                                if translation_key[var_no][pre_spec] not in node_names:
                                    node_dict[translation_key[var_no][pre_spec]] = []
                                    node_names.append(translation_key[var_no][pre_spec])
                                if translation_key[var_no][post] not in node_names:
                                    node_dict[translation_key[var_no][post]] = []
                                    node_names.append(translation_key[var_no][post])
                                node_dict[translation_key[var_no][pre_spec]].append(
                                    DomainArc(translation_key[var_no][pre_spec], translation_key[var_no][post],
                                              translation_key[n_var_no][n_post[2]]))
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
        if not (isinstance(invariant[0].predicate, pddl.f_expression.Increase) or
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
                    if (n_pre_spec == -2 or n_pre_spec == -3 or n_pre_spec == -4 or n_pre_spec == -5 or
                        n_pre_spec == -6) and n_var_no == index2:
                        eff_index_2 = 0
                        for var_no, pre_spec, post, cond in op.pre_post:
                            if eff_index_1 != eff_index_2 and (n_pre_spec != -2 and n_pre_spec != -3
                                                               and n_pre_spec != -4 and n_pre_spec != -5 and
                                                               n_pre_spec != -6) and var_no == index:
                                if translation_key[var_no][pre_spec] != '<none of those>':
                                    if translation_key[var_no][pre_spec] not in node_names:
                                        node_dict[translation_key[var_no][pre_spec]] = []
                                        node_names.append(translation_key[var_no][pre_spec])
                                    if translation_key[var_no][post] not in node_names:
                                        node_dict[translation_key[var_no][post]] = []
                                        node_names.append(translation_key[var_no][post])
                                    node_dict[translation_key[var_no][pre_spec]].append(
                                        DomainArc(translation_key[var_no][pre_spec], translation_key[var_no][post],
                                                  translation_key[n_var_no][n_post[2]]))
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
            if (n_pre_spec == -2 or n_pre_spec == -3 or n_pre_spec == -4 or n_pre_spec == -5 or
                n_pre_spec == -6) \
                    and n_var_no in sas_task.translated_metric:
                eff_index_2 = 0
                for var_no, pre_spec, post, cond in op.pre_post:
                    if eff_index_1 != eff_index_2 and (n_pre_spec != -2 and n_pre_spec != -3 and n_pre_spec != -4 and
                                                       n_pre_spec != -5 and n_pre_spec != -6):
                        if translation_key[var_no][pre_spec] != '<none of those>':
                            if translation_key[var_no][pre_spec] not in node_names:
                                node_dict[translation_key[var_no][pre_spec]] = []
                                node_names.append(translation_key[var_no][pre_spec])
                            if translation_key[var_no][post] not in node_names:
                                node_dict[translation_key[var_no][post]] = []
                                node_names.append(translation_key[var_no][post])
                            node_dict[translation_key[var_no][pre_spec]].append(
                                DomainArc(translation_key[var_no][pre_spec], translation_key[var_no][post],
                                          translation_key[n_var_no][n_post[2]]))
                    eff_index_2 = eff_index_2 + 1
            eff_index_1 = eff_index_1 + 1

    return DomainTransGraph(0, 0, node_dict)


def create_functional_dtgs_metric(sas_task, translation_key, groups):
    metric_fdtgs = []
    index = 0
    for group in groups:

        # Check if the group is propositional
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
                if (n_pre_spec == -2 or n_pre_spec == -3 or n_pre_spec == -4 or
                        n_pre_spec == -5 or n_pre_spec == -6) and n_var_no in sas_task.translated_metric:
                    eff_index_2 = 0
                    for var_no, pre_spec, post, cond in op.pre_post:
                        if eff_index_1 != eff_index_2 and (n_pre_spec != -2 and n_pre_spec != -3 and
                                                           n_pre_spec != -4 and n_pre_spec != -5 and
                                                           n_pre_spec != -6) and var_no == index:
                            if translation_key[var_no][pre_spec] != '<none of those>':
                                if translation_key[var_no][pre_spec] not in node_names:
                                    node_dict[translation_key[var_no][pre_spec]] = []
                                    node_names.append(translation_key[var_no][pre_spec])
                                if translation_key[var_no][post] not in node_names:
                                    node_dict[translation_key[var_no][post]] = []
                                    node_names.append(translation_key[var_no][post])
                                node_dict[translation_key[var_no][pre_spec]].append(
                                    DomainArc(translation_key[var_no][pre_spec], translation_key[var_no][post],
                                              translation_key[n_var_no][n_post[2]]))
                        eff_index_2 = eff_index_2 + 1
                eff_index_1 = eff_index_1 + 1

        metric_fdtgs.append(DomainTransGraph(0, index, node_dict))
        index = index + 1

    return metric_fdtgs


def create_gexf_transition_functional_graphs_files(fdtgs):
    index = 0
    today = date.today()
    d1 = today.strftime("%d/%m/%Y")

    if WINDOWS:
        save_path = "C:\\Users\\JavCa\\PycharmProjects\\pddl2-SAS-translate2\\graphs"
    else:
        save_path = "graphs"

    for graph in fdtgs:
        file_name = "functional_graph_" + str(index) + ".gexf"
        full_name = os.path.join(save_path, file_name)
        f = open(full_name, "w")
        f.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n")
        f.write("<gexf xmlns=\"http://www.gexf.net/1.2draft\" version=\"1.2\">\n")
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


def create_gexf_transition_functional_metric_graph_files(fdtg_metric):
    today = date.today()
    d1 = today.strftime("%d/%m/%Y")

    if WINDOWS:
        save_path = "C:\\Users\\JavCa\\PycharmProjects\\pddl2-SAS-translate2\\graphs\\metric"
    else:
        save_path = "graphs/metric"

    file_name = "functional_metric_graph.gexf"
    full_name = os.path.join(save_path, file_name)
    f = open(full_name, "w")
    f.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n")
    f.write("<gexf xmlns=\"http://www.gexf.net/1.2draft\" version=\"1.2\">\n")
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


def create_gexf_transition_functional_metric_graphs_files(fdtgs):
    index = 0
    today = date.today()
    d1 = today.strftime("%d/%m/%Y")

    if WINDOWS:
        save_path = "C:\\Users\\JavCa\\PycharmProjects\\pddl2-SAS-translate2\\graphs\\metric"
    else:
        save_path = "graphs/metric"

    for graph in fdtgs:
        file_name = "functional_metric_graph_" + str(graph.var_group) + ".gexf"
        full_name = os.path.join(save_path, file_name)
        f = open(full_name, "w")
        f.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n")
        f.write("<gexf xmlns=\"http://www.gexf.net/1.2draft\" version=\"1.2\">\n")
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


def create_gexf_transition_functional_per_inv_graphs_files(fdtgs_per_invariant):
    today = date.today()
    d1 = today.strftime("%d/%m/%Y")

    if WINDOWS:
        save_path = "C:\\Users\\JavCa\\PycharmProjects\\pddl2-SAS-translate2\\graphs\\functional_graphs_inv"
    else:
        save_path = "graphs/functional_graphs_inv"

    n_invariant = 0
    for invariant in fdtgs_per_invariant:

        n_graph = 0
        for graph in invariant:

            if graph and graph.node_list:
                file_name = "functional_graph_" + str(n_invariant) + "_" + str(n_graph) + ".gexf"
                full_name = os.path.join(save_path, file_name)
                f = open(full_name, "w")
                f.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n")
                f.write("<gexf xmlns=\"http://www.gexf.net/1.2draft\" version=\"1.2\">\n")
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


def create_gexf_transition_graphs_files(dtgs, groups):
    index = 0
    today = date.today()
    d1 = today.strftime("%d/%m/%Y")

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
            file_name = "graph_" + str(index) + ".gexf"
            full_name = os.path.join(save_path, file_name)
            f = open(full_name, "w")
            f.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n")
            f.write("<gexf xmlns=\"http://www.gexf.net/1.2draft\" version=\"1.2\">\n")
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


def create_casual_graph(sas_task, groups, group_const_arg, free_agent_index, simplify):
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
            operator_index2 = 0
            # Check for arcs of type 2 (effect - effect) and type 1 (precondition)
            for var_no2, pre_spec2, post2, cond2 in op.pre_post:
                # Type 2 (only if it is a different effect)
                if operator_index2 != operator_index1:
                    if simplify:
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
                    else:
                        new_arc = DomainCasualArc(var_no1, var_no2, node_groups_list[var_no1].name,
                                                  node_groups_list[var_no2].name,
                                                  (op.name.split(' ')[0])[1:], 2, arc_id)
                        node_groups_list[var_no1].arcs.append(new_arc)
                        node_groups_list_type2[var_no1].arcs.append(new_arc)
                        if var_no2 in propositional_node_groups_list \
                                and var_no1 in propositional_node_groups_list:
                            propositional_node_groups[var_no1].arcs.append(new_arc)
                            propositional_node_groups_type2[var_no1].arcs.append(new_arc)

                # Type 1 (only if a precondition exists)
                if pre_spec1 != -1 and (pre_spec1 != -2 and pre_spec1 != -3 and pre_spec1 != -4):
                    if simplify:
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
                    else:
                        new_arc = DomainCasualArc(var_no1, var_no2, node_groups_list[var_no1].name,
                                                  node_groups_list[var_no2].name, (op.name.split(' ')[0])[1:],
                                                  1, arc_id)
                        node_groups_list[var_no1].arcs.append(new_arc)
                        node_groups_list_type1[var_no1].arcs.append(new_arc)
                        if var_no2 in propositional_node_groups_list \
                                and var_no1 in propositional_node_groups_list:
                            propositional_node_groups[var_no1].arcs.append(new_arc)
                            propositional_node_groups_type1[var_no1].arcs.append(new_arc)

                operator_index2 = operator_index2 + 1

            # Check for arcs of type 1 from prevail array (precondition - effect)
            if not end_action:
                for var_no2, pre_spec2 in op.prevail:
                    if simplify:
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
                    else:
                        new_arc = DomainCasualArc(var_no2, var_no1, node_groups_list[var_no2].name,
                                                  node_groups_list[var_no1].name, (op.name.split(' ')[0])[1:], 1,
                                                  arc_id)
                        node_groups_list[var_no2].arcs.append(new_arc)
                        node_groups_list_type1[var_no2].arcs.append(new_arc)
                        if var_no2 in propositional_node_groups_list \
                                and var_no1 in propositional_node_groups_list:
                            propositional_node_groups[var_no1].arcs.append(new_arc)
                            propositional_node_groups_type1[var_no2].arcs.append(new_arc)

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
                            #casual_graph.node_list[third_arc.end_state].arcs.remove(first_arc)
                            #casual_graph.node_list[first_arc.end_state].arcs.remove(second_arc)
                            #casual_graph.node_list[second_arc.end_state].arcs.remove(third_arc)

    for remove_arc in arcs_to_remove:
        for end_arc in casual_graph.node_list[remove_arc.end_state].end_arcs[:]:
            if end_arc.end_state == remove_arc.end_state and end_arc.origin_state == remove_arc.origin_state:
                casual_graph.node_list[remove_arc.end_state].end_arcs.remove(end_arc)

    return casual_graph


def obtain_origin_nodes(casual_graph):
    origin_nodes = {}
    for node_number in casual_graph.node_list:
        if not casual_graph.node_list[node_number].end_arcs and casual_graph.node_list[node_number].arcs:
            origin_nodes[node_number] = casual_graph.node_list[node_number]

    return origin_nodes


def fill_basic_agents(origin_nodes, propositional_casual_graph):
    full_agents = []
    redundant_agents = []
    or_agent_nodes = [or_node_number for or_node_number in origin_nodes]
    for agent in origin_nodes:
        search_queue = []
        already_visited = []

        for node_app in propositional_casual_graph.node_list[agent].arcs:
            if node_app.arc_type == 1:
                search_queue.append(node_app.end_state)

        for node_app in propositional_casual_graph.node_list[agent].arcs:
            if node_app.arc_type == 1:
                already_visited.append(node_app.end_state)

        full_agents.append([agent])
        while search_queue:
            node = search_queue.pop(0)

            # Check if all predecesors are in V
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

    # Remove redundant agents
    to_remove = []
    for agent in full_agents[:]:
        for agent2 in full_agents[:]:
            if agent[0] != agent2[0] and agent[0] not in to_remove:
                for agent_state in agent[:]:
                    if agent_state == agent2[0] and agent_state != agent[0]:
                        full_agents.remove(agent2)
                        to_remove.append(agent2[0])
                        break

    # Remove redundant states in agents
    full_agents_final = []
    for agent in full_agents:
        agent_final = []
        [agent_final.append(x) for x in agent if x not in agent_final]
        full_agents_final.append(agent_final)

    # for agent in full_agents_final:
    #    agent.sort()

    return full_agents_final


def assemble_basic_agents(basic_agents, group_const_arg):
    final_basic_agents = []
    do_not_agent = []
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
                                if node_1 < len(group_const_arg) and node_2 < len(group_const_arg):
                                    if group_const_arg[node_1][0] in group_const_arg[node_2]:
                                        for node in agent_2:
                                            agent_nodes.append(node)
                                        do_not_agent.append(agent_2[0])
                else:
                    if agent[0] != agent_2:
                        for node_1 in agent:
                            if node_1 < len(group_const_arg) and group_const_arg[node_1][0] in group_const_arg[agent_2]:
                                agent_nodes.append(agent_2)
                                do_not_agent.append(agent_2)
        else:

            if agent in do_not_agent:
                continue

            agent_nodes.append(agent)
            for agent_2 in basic_agents:
                if type(agent_2) is list:
                    if agent != agent_2[0]:
                        for node_2 in agent_2:
                            if node_2 < len(group_const_arg) and group_const_arg[agent][0] in group_const_arg[node_2]:
                                for node in agent_2:
                                    agent_nodes.append(node)
                                do_not_agent.append(agent_2[0])
                else:
                    if agent != agent_2:
                        if group_const_arg[agent][0] in group_const_arg[agent_2]:
                            agent_nodes.append(agent_2)
                            do_not_agent.append(agent_2)

        res = []
        [res.append(x) for x in agent_nodes if x not in res]
        final_basic_agents.append(res)

    return final_basic_agents


def fill_joint_agents(basic_agents, propositional_casual_graph, depth):
    joint_agents = copy.deepcopy(basic_agents)
    not_jointed = []

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

    while len(not_jointed) != 0:
        to_remove = []
        for node in not_jointed:

            remove_node = True
            if len(propositional_casual_graph.node_list[node].arcs) == 0:
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

        for node_rem in to_remove:
            if node_rem in not_jointed:
                not_jointed.remove(node_rem)

    return joint_agents


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
                    if arg in group_const_arg[agent[0]]:
                        joint_final_agents[agent_index].append(node)
            agent_index = agent_index + 1

    for agent in joint_final_agents:
        agent.sort()

    # joint_final_agents_return = fill_joint_agents(joint_final_agents, propositional_casual_graph, 2)

    # for agent in joint_final_agents_return:
    #    agent.sort()

    return joint_final_agents


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


def fill_agents_actions(full_agents, joint_agents, full_func_agents, casual_graph, sas_task, groups):
    agent_actions = []
    not_added = []

    for _ in full_agents:
        agent_actions.append([])

    # Get common actions
    extern_actions = []
    for _ in full_agents:
        extern_actions.append([])
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
        for agent in full_agents:
            added = False
            for eff in ope.pre_post:
                if not added and agent.count(eff[0]) != 0:
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
            not_added.append(ope)

    # If there are actions not yet assigned, try to apply them by joint_agents
    not_added_second = []
    if not_added:
        for ope in not_added:
            index = 0
            for agent in joint_agents:
                added = False
                for eff in ope.pre_post:
                    if eff[0] == 0:
                        continue
                    if not added and agent.count(eff[0]) != 0:
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
                    if eff[0] == 0:
                        continue
                    if not added and agent.count(eff[0]) != 0:
                        added = True
                        agent_actions[index].append(ope)

                for pre in ope.prevail:
                    if not added and agent.count(pre[0]) != 0:
                        added = True
                        agent_actions[index].append(pre)

                index = index + 1

    # Remove redundant actions in agents
    agent_actions_final = []
    for agent in agent_actions:
        agent_final = []
        [agent_final.append(x) for x in agent if x not in agent_final]
        agent_actions_final.append(agent_final)

    # cosas por determinar
    for node, agents_com in agent_common_nodes.items():
        index = 0
        for exists_in_agent in agents_com:
            if exists_in_agent:
                for ope in sas_task.operators:
                    added = False
                    if ope not in agent_actions_final[index]:
                        for eff in ope.pre_post:
                            if not added and node == eff[0] != 0:
                                added = True
                                extern_actions[index].append(ope)

                        for pre in ope.prevail:
                            if not added and node == pre[0] != 0:
                                added = True
                                extern_actions[index].append(ope)
            index = index + 1

    return agent_actions_final, extern_actions, agent_common_nodes


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


def fill_agents_goals(joint_agents, functional_agents, agents_actions, agents_metric, agents_init, casual_graph,
                      sas_task, groups):
    agent_goals = []
    goals_to_analyze = []

    for _ in joint_agents:
        agent_goals.append([])

    # First find if there are goals that belong only to one agent
    for goal in sas_task.goal.pairs:
        n_agent_found = -1
        direct_goal = True
        index = -1
        for agent in joint_agents:
            if agent.count(goal[0]) != 0:
                if n_agent_found != -1:
                    direct_goal = False
                    goals_to_analyze.append(goal)
                else:
                    n_agent_found = index + 1
            index = index + 1
        if direct_goal:
            agent_goals[n_agent_found].append(goal)

    un_goals_to_analyze = []

    for goal in goals_to_analyze:
        if goal not in un_goals_to_analyze:
            un_goals_to_analyze.append(goal)

    # If there are goals_to_analyze, we have to assign them by analyzing the problem
    estimations_agent_goals = fill_complex_agents_goals(un_goals_to_analyze, joint_agents, functional_agents,
                                                        agents_actions, agents_metric, agents_init, casual_graph,
                                                        sas_task, groups)

    # Now the calculated objectives will be assigned
    goal_index = 0
    metric_total_agent = []

    for _ in joint_agents:
        metric_total_agent.append(0)

    for goal_estimations in estimations_agent_goals:
        min_vals = []
        agent_index = 0
        for agent_estimations in goal_estimations:
            if not agent_estimations:
                min_value = 99999
            else:
                min_value = agent_estimations[0].estimated_metric
                for node in agent_estimations:
                    if node.estimated_metric < min_value:
                        min_value = node.estimated_metric
            min_vals.append(min_value)
            agent_index = agent_index + 1

        # Assign goal
        estimations = []
        agent_analysis_index = 0
        for agent_analysis in min_vals:
            estimations.append(metric_total_agent[agent_analysis_index] + agent_analysis)
            agent_analysis_index = agent_analysis_index + 1
        agent_index_chosen = estimations.index(min(estimations))

        agent_goals[agent_index_chosen].append(un_goals_to_analyze[goal_index])
        metric_total_agent[agent_index_chosen] = min(estimations)

        goal_index = goal_index + 1

    return agent_goals


def fill_complex_agents_goals(goals_to_analyze, joint_agents, functional_agents, agents_actions, agents_metric,
                              agents_init, casual_graph, sas_task, groups):
    analyzed_agent_goals = []
    goal_index = 0

    # We have to do a backward search from the goals to the init state
    for goal in goals_to_analyze:
        print("The goal " + str(goal[0]) + ":" + str(goal[1]) + " ... launching non delete search")

        # Go backwards searching for necessary init states
        agent_index = 0
        agent_sol_estimations = []

        for agent in functional_agents:

            # Checkm if the agent can achieve the goal
            if goal[0] not in agent:
                print(
                    "The goal " + str(goal[0]) + ":" + str(goal[1]) +
                    " cannot be achieved by agent " + str(agent_index) + ", no search will be launched.")
                agent_sol_estimations.append([])
                agent_index = agent_index + 1
                continue

            agent_sol_estimations.append([])
            agent_actions = agents_actions[agent_index]
            agent_metric = agents_metric[agent_index]
            agent_init = copy.deepcopy(agents_init[agent_index])
            joint_agent = joint_agents[agent_index]

            estimated_metric = 0
            search_queue = []
            solutions = []
            init_node = EstimatedMetricNode([], agent_init, 0, [goal])
            search_queue.append((init_node, 0))

            # Set a time limit for each goal and agent
            timeout_start = time.time()

            max_cost = 9999999

            while search_queue and time.time() < timeout_start + 1:
                (node, h_node) = search_queue.pop(0)

                # Check if the agent has a pending to start action
                last_action_end = False
                if node.app_actions:
                    last_action_name = node.app_actions[-1].name
                    if "_end " in last_action_name:
                        last_action_end = True

                # Search actions that can set the state "node"
                for action in agent_actions:
                    added = False
                    if node.app_actions:
                        if last_action_end and "_end " in action.name:
                            continue
                        if not last_action_end and "_start " in action.name:
                            continue
                    for effect in action.pre_post:
                        for pending_subgoal in node.pending_additions:
                            if effect[0] == pending_subgoal[0] and effect[2] == pending_subgoal[1] and not added:

                                new_action_name = "_".join(
                                    (((((action.name.split(" "))[0]).split("("))[1]).split("_"))[:-1])

                                # Create new current state for the new nodes
                                new_node_state = copy.deepcopy(node.curr_state)
                                new_node_state[effect[0]] = effect[2]

                                # If an action that can set the effect is found
                                # create a new state with all preconditions not met
                                # and add it to the queue

                                new_node_cost = copy.deepcopy(node.estimated_metric + action.cost)
                                new_node_actions = copy.deepcopy(node.app_actions)
                                new_node_actions.append(action)

                                new_node_subgoals = copy.deepcopy(node.pending_additions)
                                new_node_subgoals.remove(pending_subgoal)

                                for pre in action.prevail:
                                    if agent_init[pre[0]] != pre[1] and new_node_subgoals.count([pre[0], pre[1]]) == 0:
                                        new_node_subgoals.append([pre[0], pre[1]])

                                for effect_2 in action.pre_post:
                                    if (effect_2[1] != -2 and effect_2[1] != -3 and effect_2[1] != -4 and
                                        effect_2[1] != -5 and effect_2[1] != -6) and \
                                            effect_2[2] != -1 and \
                                            effect_2[1] != -1 and \
                                            agent_init[effect_2[0]] != effect_2[1]:
                                        if new_node_subgoals.count([effect_2[0], effect_2[1]]) == 0:
                                            new_node_subgoals.append([effect_2[0], effect_2[1]])

                                new_node = EstimatedMetricNode(new_node_actions, new_node_state, new_node_cost,
                                                               new_node_subgoals)

                                added = True

                                if not new_node_subgoals:

                                    if new_node.estimated_metric < max_cost:
                                        print(
                                            "The goal " + str(goal[0]) + ":" + str(goal[1]) +
                                            " has solution for agent (" + str(agent_index) + ") -- estimation -> " +
                                            str(new_node.estimated_metric) + " < " + str(max_cost))

                                        max_cost = new_node.estimated_metric

                                        agent_sol_estimations[agent_index].append(new_node)
                                else:
                                    if new_node.estimated_metric < max_cost:
                                        if last_action_end:
                                            search_queue.append((new_node, calculate_heuristic(new_node)))
                                        else:
                                            search_queue.append((new_node, h_node))
                                        search_queue.sort(key=take_second)
                                        # search_queue.insert(0, new_node)

            agent_index = agent_index + 1
        analyzed_agent_goals.append(agent_sol_estimations)

        goal_index = goal_index + 1

    return analyzed_agent_goals


def calculate_heuristic(node):
    h_value = len(node.pending_additions) - (len(node.app_actions) / 2)
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
