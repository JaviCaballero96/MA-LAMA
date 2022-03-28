import pddl
import os
import glob
from simplify import DomainTransitionGraph
from datetime import date

WINDOWS = False


class DomainNode:
    def __init__(self, state, arcs):
        self.state = state
        self.arcs = arcs


class DomainCasualNode:
    def __init__(self, arcs, name, number, type1_arcs, type2_arcs):
        self.name = name
        self.number = number
        self.arcs = arcs
        self.type1_arcs = type1_arcs
        self.type2_arcs = type2_arcs


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
                isinstance(group[0].predicate, pddl.f_expression.Decrease)):
            index = index + 1
            continue

        node_dict = {}
        node_names = []
        for op in sas_task.operators:
            eff_index_1 = 0
            for n_var_no, n_pre_spec, n_post, n_cond in op.pre_post:
                if n_pre_spec == -2 and n_var_no == index:
                    eff_index_2 = 0
                    for var_no, pre_spec, post, cond in op.pre_post:
                        if eff_index_1 != eff_index_2 and pre_spec != -2:
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
        if (isinstance(invariant[0].predicate, pddl.f_expression.Increase) or
                isinstance(invariant[0].predicate, pddl.f_expression.Assign) or
                isinstance(invariant[0].predicate, pddl.f_expression.Decrease)):
            index = index + 1
            continue

        fdtgs_per_invariant.append([])
        index2 = 0

        for group in groups:

            # Check if the group is functional
            if not (isinstance(group[0].predicate, pddl.f_expression.Increase) or
                    isinstance(group[0].predicate, pddl.f_expression.Assign) or
                    isinstance(group[0].predicate, pddl.f_expression.Decrease)):
                index2 = index2 + 1
                continue

            node_dict = {}
            node_names = []
            for op in sas_task.operators:
                eff_index_1 = 0
                for n_var_no, n_pre_spec, n_post, n_cond in op.pre_post:
                    if n_pre_spec == -2 and n_var_no == index2:
                        eff_index_2 = 0
                        for var_no, pre_spec, post, cond in op.pre_post:
                            if eff_index_1 != eff_index_2 and pre_spec != -2 and var_no == index:
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
            if n_pre_spec == -2 and n_var_no in sas_task.translated_metric:
                eff_index_2 = 0
                for var_no, pre_spec, post, cond in op.pre_post:
                    if eff_index_1 != eff_index_2 and pre_spec != -2:
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
        if (isinstance(group[0].predicate, pddl.f_expression.Increase) or
                isinstance(group[0].predicate, pddl.f_expression.Assign) or
                isinstance(group[0].predicate, pddl.f_expression.Decrease)):
            index = index + 1
            continue

        node_dict = {}
        node_names = []
        for op in sas_task.operators:
            eff_index_1 = 0
            for n_var_no, n_pre_spec, n_post, n_cond in op.pre_post:
                if n_pre_spec == -2 and n_var_no in sas_task.translated_metric:
                    eff_index_2 = 0
                    for var_no, pre_spec, post, cond in op.pre_post:
                        if eff_index_1 != eff_index_2 and pre_spec != -2 and var_no == index:
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
        save_path = "/home/caba/Escritorio/planners/pddl2-sas+trasnslate/graphs"

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
        save_path = "/home/caba/Escritorio/planners/pddl2-sas+trasnslate/graphs/metric"

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
        save_path = "/home/caba/Escritorio/planners/pddl2-sas+trasnslate/graphs/metric"

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
        save_path = "/home/caba/Escritorio/planners/pddl2-sas+trasnslate/graphs/functional_graphs_inv"

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
        save_path = "/home/caba/Escritorio/planners/pddl2-sas+trasnslate/graphs"

    filelist = glob.glob(os.path.join(save_path, "*.csv"))
    for f in filelist:
        os.remove(f)

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
        save_path = "/home/caba/Escritorio/planners/pddl2-sas+trasnslate/graphs"

    filelist = glob.glob(os.path.join(save_path, "*.gexf"))
    for f in filelist:
        os.remove(f)

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


def create_casual_graph(sas_task, groups, simplify):
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
                    isinstance(state.predicate, pddl.f_expression.Assign):
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
                is_there_function_states = True
            else:
                if state.predicate not in atoms_included:
                    atoms_included.append(state.predicate)
                    name = name + state.predicate + "_"

        name = name[:-1]
        node_groups_list.append(DomainCasualNode([], name, group_number, [], []))
        node_groups_list_type1.append(DomainCasualNode([], name, group_number, [], []))
        node_groups_list_type2.append(DomainCasualNode([], name, group_number, [], []))
        if not is_there_function_states:
            propositional_node_groups_list.append(group_number)
            propositional_node_groups[group_number] = DomainCasualNode([], name, group_number, [], [])
            propositional_node_groups_type1[group_number] = DomainCasualNode([], name, group_number, [], [])
            propositional_node_groups_type2[group_number] = DomainCasualNode([], name, group_number, [], [])

        group_number = group_number + 1

    for op in sas_task.operators:
        operator_index1 = 0
        for var_no1, pre_spec1, post1, cond1 in op.pre_post:
            operator_index2 = 0
            # Check for arcs of type 2 (effect - effect) and type 1 (precondition)
            for var_no2, pre_spec2, post2, cond2 in op.pre_post:
                # Type 2 (only if it is a different effect)
                if operator_index2 != operator_index1:
                    if simplify:
                        arc_id = (op.name.split(' ')[0])[1:] + "-" + str(var_no1) + "_" + str(var_no2)
                        if arc_id not in node_groups_list[var_no1].type2_arcs:
                            new_arc = DomainCasualArc(var_no1, var_no2, node_groups_list[var_no1].name,
                                                      node_groups_list[var_no2].name, (op.name.split(' ')[0])[1:],
                                                      2, arc_id)
                            node_groups_list[var_no1].arcs.append(new_arc)
                            node_groups_list[var_no1].type2_arcs.append(arc_id)
                            node_groups_list_type2[var_no1].arcs.append(new_arc)
                            node_groups_list_type2[var_no1].type2_arcs.append(arc_id)
                            if var_no2 in propositional_node_groups_list \
                                    and var_no1 in propositional_node_groups_list:
                                propositional_node_groups[var_no1].arcs.append(new_arc)
                                propositional_node_groups[var_no1].type2_arcs.append(arc_id)
                                propositional_node_groups_type2[var_no1].arcs.append(new_arc)
                                propositional_node_groups_type2[var_no1].type2_arcs.append(arc_id)

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
                if pre_spec1 != -1 and pre_spec1 != -2:
                    if simplify:
                        arc_id = (op.name.split(' ')[0])[1:] + "-" + str(var_no1) + "_" + str(var_no2)
                        if arc_id not in node_groups_list[var_no1].type1_arcs:
                            new_arc = DomainCasualArc(var_no1, var_no2, node_groups_list[var_no1].name,
                                                      node_groups_list[var_no2].name, (op.name.split(' ')[0])[1:],
                                                      1, arc_id)
                            node_groups_list[var_no1].arcs.append(new_arc)
                            node_groups_list[var_no1].type1_arcs.append(arc_id)
                            node_groups_list_type1[var_no1].arcs.append(new_arc)
                            node_groups_list_type1[var_no1].type1_arcs.append(arc_id)
                            if var_no2 in propositional_node_groups_list \
                                    and var_no1 in propositional_node_groups_list:
                                propositional_node_groups[var_no1].arcs.append(new_arc)
                                propositional_node_groups[var_no1].type1_arcs.append(arc_id)
                                propositional_node_groups_type1[var_no1].arcs.append(new_arc)
                                propositional_node_groups_type1[var_no1].type1_arcs.append(arc_id)
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
            for var_no2, pre_spec2 in op.prevail:
                if simplify:
                    arc_id = (op.name.split(' ')[0])[1:] + "-" + str(var_no2) + "_" + str(var_no1)
                    if arc_id not in node_groups_list[var_no2].type1_arcs:
                        new_arc = DomainCasualArc(var_no2, var_no1, node_groups_list[var_no2].name,
                                                  node_groups_list[var_no1].name, (op.name.split(' ')[0])[1:],
                                                  1, arc_id)
                        node_groups_list[var_no2].arcs.append(new_arc)
                        node_groups_list[var_no2].type1_arcs.append(arc_id)
                        node_groups_list_type1[var_no2].arcs.append(new_arc)
                        node_groups_list_type1[var_no2].type1_arcs.append(arc_id)
                        if var_no2 in propositional_node_groups_list \
                                and var_no1 in propositional_node_groups_list:
                            propositional_node_groups[var_no2].arcs.append(new_arc)
                            propositional_node_groups[var_no2].type1_arcs.append(arc_id)
                            propositional_node_groups_type1[var_no2].arcs.append(new_arc)
                            propositional_node_groups_type1[var_no2].type1_arcs.append(arc_id)
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


def remove_level2_cycles(casual_graph_type1, translation_key):
    print("a")


def create_gexf_casual_graph_files(casual_graph, type):
    index = 0
    today = date.today()
    d1 = today.strftime("%d/%m/%Y")

    if WINDOWS:
        save_path = "C:\\Users\\JavCa\\PycharmProjects\\pddl2-SAS-translate2\\graphs"
    else:
        save_path = "/home/caba/Escritorio/planners/pddl2-sas+trasnslate/graphs"

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
