class SASTask:
    def __init__(self, variables, init, goal, operators, axioms, metric, shared_nodes):
        self.variables = variables
        self.init = init
        self.goal = goal
        self.operators = operators
        self.axioms = axioms
        self.metric = metric
        self.shared_nodes = shared_nodes
    def output(self, stream, groups):
        print("gen", file=stream)
        print("begin_metric", file=stream)
        if self.metric:
            print("(" + self.metric[0], file=stream)
            for me in self.translated_metric.keys():
                print(str(me) + " ", file=stream)
            print(")", file=stream)
        print("end_metric", file=stream)
        self.variables.output(stream, groups)
        self.init.output(stream)
        self.goal.output(stream)
        print(len(self.operators), file=stream)
        for op in self.operators:
            op.output(stream)
        print(len(self.axioms), file=stream)
        for axiom in self.axioms:
            axiom.output(stream)

    def outputma(self, stream, name, groups, agent_index):

        aux = {}
        if isinstance(self.variables.ranges, list):
            index = 0
            for var in self.variables.ranges:
                aux[index] = self.variables.ranges[index]
                index = index + 1
            self.variables.ranges = aux

        print(name, file=stream)
        print("begin_metric", file=stream)
        if self.metric:
            print("(" + self.metric[0], file=stream)
            for me in self.metric[1:]:
                print(str(me) + " ", file=stream)
            print(")", file=stream)
        print("end", file=stream)
        print("end_metric", file=stream)
        self.variables.output(stream, groups)
        self.init.output(stream)
        print("begin_shared", file=stream)
        shared_number = 0
        if self.shared_nodes:
            for me, is_agent in self.shared_nodes.items():
                if is_agent[agent_index]:
                    shared_number = shared_number + 1
            print(shared_number, file=stream)
            for me, is_agent in self.shared_nodes.items():
                if not is_agent[agent_index]:
                    continue
                index = 0
                for vari, range in self.variables.ranges.items():
                    if vari == me:
                        break
                    index = index + 1
                print(str(me) + " " + str(index), file=stream)
        else:
            print("0", file=stream)
        print("end_shared", file=stream)
        print("begin_goal", file=stream)
        print(len(self.goal.pairs), file=stream)
        for var, val in self.goal.pairs:
            index = 0
            for vari, range in self.variables.ranges.items():
                if vari == var:
                    break
                index = index + 1
            print(index, val, file=stream)
        print("end_goal", file=stream)

        # self.goal.output(stream)
        print(len(self.operators), file=stream)
        for op in self.operators:
            op.outputma(stream, self.variables.ranges)
        print(len(self.axioms), file=stream)
        for axiom in self.axioms:
            axiom.output(stream)
class SASVariables:
    def __init__(self, ranges, axiom_layers):
        self.ranges = ranges
        self.axiom_layers = axiom_layers
    def dump(self):
        for var, (rang, axiom_layer) in enumerate(zip(self.ranges, self.axiom_layers)):
            if axiom_layer != -1:
                axiom_str = " [axiom layer %d]" % axiom_layer
            else:
                axiom_str = ""
            print("v%d in {%s}%s" % (var, list(range(rang)), axiom_str))
    def output(self, stream, groups):
        print("begin_variables", file=stream)
        print(len(self.ranges), file=stream)
        if type(self.ranges) is not dict:
            for var, (rang, axiom_layer) in enumerate(zip(self.ranges, self.axiom_layers)):
                if (not isinstance(groups[var][0].predicate, str)) and \
                        'total-time' == groups[var][0].predicate.fluent.symbol:
                    time = 1
                else:
                    time = 0
                print("var%d %d %d %d" % (var, rang, axiom_layer, time), file=stream)
        else:
            for var, rang in self.ranges.items():
                if (not isinstance(groups[var][0].predicate, str)) and \
                        'total-time' == groups[var][0].predicate.fluent.symbol:
                    time = 1
                else:
                    time = 0
                print("var%d %d %d %d" % (var, rang + 1, -1, time), file=stream)
        print("end_variables", file=stream)

class SASInit:
    def __init__(self, values):
        self.values = values
    def dump(self):
        for var, val in enumerate(self.values):
            if val != -1:
                print("v%d: %d" % (var, val))
    def output(self, stream):
        print("begin_state", file=stream)
        if type(self.values) is not dict:
            for val in self.values:
                if isinstance(val, float):
                    print("-1", val, file=stream)
                else:
                    print(val, file=stream)
        else:
            for var, val in self.values.items():
                if isinstance(val, float):
                    print("-1", val, file=stream)
                else:
                    print(val, file=stream)
        print("end_state", file=stream)

class SASGoal:
    def __init__(self, pairs):
        self.pairs = sorted(pairs)
    def dump(self):
        for var, val in self.pairs:
            print("v%d: %d" % (var, val))
    def output(self, stream):
        print("begin_goal", file=stream)
        print(len(self.pairs), file=stream)
        for var, val in self.pairs:
            print(var, val, file=stream)
        print("end_goal", file=stream)

class SASOperator:
    def __init__(self, name, prevail, pre_post, cost):
        self.name = name
        self.prevail = sorted(prevail)
        self.pre_post = sorted(pre_post)
        self.cost = cost
    def dump(self):
        print(self.name)
        print("Prevail:")
        for var, val in self.prevail:
            print("  v%d: %d" % (var, val))
        print("Pre/Post:")
        for var, pre, post, cond in self.pre_post:
            if cond:
                cond_str = " [%s]" % ", ".join(["%d: %d" % tuple(c) for c in cond])
            else:
                cond_str = ""
            print("  v%d: %d -> %d%s" % (var, pre, post, cond_str))
    def output(self, stream):
        print("begin_operator", file=stream)
        print(self.name[1:-1], file=stream)
        print(len(self.prevail), file=stream)
        for var, val in self.prevail:
            print(var, val, file=stream)
        print(len(self.pre_post), file=stream)
        for var, pre, post, cond in self.pre_post:
            print(len(cond), end=' ', file=stream)
            for cvar, cval in cond:
                print(cvar, cval, end=' ', file=stream)
            if pre == -2 or pre == -3 or pre == -4 or pre == -5 or pre == -6:
                to_write = ""
                for elem in post:
                    to_write = to_write + str(elem) + " "
                to_write = to_write[:-1]
                print(var, pre, to_write, file=stream)
            else:
                print(var, pre, post, file=stream)
        print(self.cost, file=stream)
        if self.have_runtime_cost:
            print("runtime", file=stream)
            print(self.runtime_cost, file=stream)
        else:
            print("no-run", file=stream)
            print("-", file=stream)
        print("end_operator", file=stream)

    def outputma(self, stream, ranges):
        print("begin_operator", file=stream)
        print(self.name[1:-1], file=stream)
        print(len(self.prevail), file=stream)
        for var, val in self.prevail:
            index = 0
            for vari, range in ranges.items():
                if vari == var:
                    break
                index = index + 1
            print(index, val, file=stream)
        print(len(self.pre_post), file=stream)
        for var, pre, post, cond in self.pre_post:
            print(len(cond), end=' ', file=stream)
            for cvar, cval in cond:
                print(cvar, cval, end=' ', file=stream)
            if pre == -2 or pre == -3 or pre == -4 or pre == -5 or pre == -6:
                index = 0
                for vari, range in ranges.items():
                    if vari == var:
                        break
                    index = index + 1

                to_write = ""
                index_var = 0
                for elem in post:
                    if index_var != 1:
                        # Check if the element is a runtime cost
                        if isinstance(elem, str) and "_" in elem:
                            # Then we have to translate the variables
                            aux = elem
                            while "_" in elem:
                                aux = aux[(aux.find("_") + 1):]
                                run_var = aux[:aux.find("_")]
                                aux = aux[(aux.find("_") + 1):]
                                run_index = 0
                                for vari, range in ranges.items():
                                    if vari == int(run_var):
                                        break
                                    run_index = run_index + 1
                                elem = elem.replace("_" + run_var + "_", "!" + str(run_index) + "!")

                        to_write = to_write + str(elem) + " "
                    else:
                        to_write = to_write + str(index) + " "
                    index_var = index_var + 1
                to_write = to_write[:-1]

                print(index, pre, to_write, file=stream)
            else:
                index = 0
                for vari, range in ranges.items():
                    if vari == var:
                        break
                    index = index + 1
                print(index, pre, post, file=stream)
        print(self.cost, file=stream)
        if self.have_runtime_cost:
            print("runtime", file=stream)
            run_cost = self.runtime_cost
            if isinstance(run_cost, str) and "_" in run_cost:
                # Then we have to translate the variables
                aux = run_cost
                while "_" in run_cost:
                    aux = aux[(aux.find("_") + 1):]
                    run_var = aux[:aux.find("_")]
                    aux = aux[(aux.find("_") + 1):]
                    run_index = 0
                    for vari, range in ranges.items():
                        if vari == int(run_var):
                            break
                        run_index = run_index + 1
                    run_cost = run_cost.replace("_" + run_var + "_", "!" + str(run_index) + "!")
            print(self.run_cost, file=stream)
        else:
            print("no-run", file=stream)
            print("-", file=stream)
        print("end_operator", file=stream)

class SASAxiom:
    def __init__(self, condition, effect):
        self.condition = condition
        self.effect = effect
        assert self.effect[1] in (0, 1)

        for _, val in condition:
            assert val >= 0, condition
    def dump(self):
        print("Condition:")
        for var, val in self.condition:
            print("  v%d: %d" % (var, val))
        print("Effect:")
        var, val = self.effect
        print("  v%d: %d" % (var, val))
    def output(self, stream):
        print("begin_rule", file=stream)
        print(len(self.condition), file=stream)
        for var, val in self.condition:
            print(var, val, file=stream)
        var, val = self.effect
        print(var, 1 - val, val, file=stream)
        print("end_rule", file=stream)
