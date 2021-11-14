import pddl
from simplify import DomainTransitionGraph


class DomainNode:
    def __init__(self, state, arcs):
        self.state = state
        self.arcs = arcs


class DomainArc:
    def __init__(self, origin_state, end_state, action):
        self.origin_state = origin_state
        self.end_state = end_state
        self.action = action


class DomainArc:
    def __init__(self, var_group, node_list):
        self.node_list = node_list
        self.var_group = var_group


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

    def add_arc(var_no, pre_spec, post):
        if pre_spec == -1:
            pre_values = set(range(sizes[var_no])).difference([post])
        else:
            pre_values = [pre_spec]
        for pre in pre_values:
            dtgs[var_no].add_arc(pre, post)

    for op in task.operators:
        for var_no, pre_spec, post, cond in op.pre_post:
            add_arc(var_no, pre_spec, post)
    for axiom in task.axioms:
        var_no, val = axiom.effect
        add_arc(var_no, -1, val)

    return dtgs


def creatae_frist_order_domain_graphs(agents_pred, agents_pred_dics, agent_minimal_vars, sas_task, strips_to_sas):
    first_order_graphs = []
    for minimal_var_group in agent_minimal_vars[1:]:
        for operator in sas_task.operators:
            for minimal_var in minimal_var_group.keys():
                atom_list = minimal_var_group[minimal_var]
                for literal_atom in atom_list:
                    dict_atom = strips_to_sas[literal_atom]
                    print("a")
