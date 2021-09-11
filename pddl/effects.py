import pddl.f_expression
from . import conditions
from . import pddl_types
from . import f_expression


def cartesian_product(*sequences):
    # TODO: Also exists in tools.py outside the pddl package (defined slightly
    #       differently). Not good. Need proper import paths.
    if not sequences:
        yield ()
    else:
        for tup in cartesian_product(*sequences[1:]):
            for item in sequences[0]:
                yield (item,) + tup


def parse_temp_info(alist):
    """Parse PDDL time identificators: over all, at start and at end """
    tag = alist[0]
    if tag in ("and", "or", "not", "imply"):
        args = alist[1:]
    elif tag == "over":
        return "all"
    elif tag == "at":
        return alist[1]
    else:
        args = alist

    parts = [parse_temp_info(part) for part in args]
    return parts


def parse_effects(alist, result, duration):
    """Parse a PDDL effect (any combination of simple, conjunctive, conditional, and universal)."""
    tmp_effect = parse_effect(alist)
    normalized = tmp_effect.normalize()
    tmp_info = parse_temp_info(alist)
    cost_eff, rest_effect = normalized.extract_cost(tmp_info)
    # Add total time effect
    time_effect = pddl.effects.CostEffect(pddl.f_expression.parse_assignment(["increase", "total-time",
                                                                              duration.expression]))
    time_effect.tmp = "end"

    cost_eff.append(time_effect)

    add_effect(rest_effect, result)

    # Add cost effects
    for cost_effect in cost_eff:
        cost_effect.condition = conditions.Truth()
        result.append(cost_effect)

    if cost_eff:
        return cost_eff
    else:
        return None


def add_effect(tmp_effect, result):
    """tmp_effect has the following structure:
       [ConjunctiveEffect] [UniversalEffect] [ConditionalEffect] SimpleEffect."""

    if isinstance(tmp_effect, ConjunctiveEffect):
        for effect in tmp_effect.effects:
            add_effect(effect, result)
        return
    else:
        parameters = []
        condition = conditions.Truth()
        if isinstance(tmp_effect, UniversalEffect):
            parameters = tmp_effect.parameters
            if isinstance(tmp_effect.effect, ConditionalEffect):
                condition = tmp_effect.effect.condition
                assert isinstance(tmp_effect.effect.effect, SimpleEffect)
                effect = tmp_effect.effect.effect.effect
            else:
                assert isinstance(tmp_effect.effect, SimpleEffect)
                effect = tmp_effect.effect.effect
        elif isinstance(tmp_effect, ConditionalEffect):
            condition = tmp_effect.condition
            assert isinstance(tmp_effect.effect, SimpleEffect)
            effect = tmp_effect.effect.effect
        else:
            assert isinstance(tmp_effect, SimpleEffect)
            effect = tmp_effect.effect
        assert isinstance(effect, conditions.Literal)
        # Check for contradictory effects
        condition = condition.simplified()
        new_effect = Effect(parameters, condition, effect)
        new_effect.tmp = tmp_effect.tmp
        contradiction = Effect(parameters, condition, effect.negate())
        if not contradiction in result:
            result.append(new_effect)
        else:
            # We use add-after-delete semantics, keep positive effect
            if isinstance(contradiction.literal, conditions.NegatedAtom):
                index = result.index(contradiction)
                if result[index].tmp == new_effect.tmp:
                    result.remove(contradiction)
                result.append(new_effect)


def parse_effect(alist):
    tag = alist[0]

    if tag in ("over", "at"):
        alist = alist[2]
        tag = alist[0]

    if tag == "and":
        return ConjunctiveEffect([parse_effect(eff) for eff in alist[1:]])
    elif tag == "forall":
        assert len(alist) == 3
        parameters = pddl_types.parse_typed_list(alist[1])
        effect = parse_effect(alist[2])
        return UniversalEffect(parameters, effect)
    elif tag == "when":
        assert len(alist) == 3
        condition = conditions.parse_condition(alist[1])
        effect = parse_effect(alist[2])
        return ConditionalEffect(condition, effect)
    elif tag == "increase":
        assert len(alist) == 3
        # assert alist[1] == ['total-cost']
        assignment = f_expression.parse_assignment(alist)
        return CostEffect(assignment)
    else:
        return SimpleEffect(conditions.parse_literal(alist))


class Effect(object):
    def __init__(self, parameters, condition, literal):
        self.parameters = parameters
        self.condition = condition
        self.literal = literal

    def __eq__(self, other):
        return (self.__class__ is other.__class__ and
                self.parameters == other.parameters and
                self.condition == other.condition and
                self.literal == other.literal)

    def dump(self):
        indent = "  "
        if self.parameters:
            print("%sforall %s" % (indent, ", ".join(map(str, self.parameters))))
            indent += "  "
        if self.condition != conditions.Truth():
            print("%sif" % indent)
            self.condition.dump(indent + "  ")
            print("%sthen" % indent)
            indent += "  "
        print("%s%s" % (indent, self.literal))

    def copy(self):
        return Effect(self.parameters, self.condition, self.literal)

    def uniquify_variables(self, type_map):
        renamings = {}
        self.parameters = [par.uniquify_name(type_map, renamings)
                           for par in self.parameters]
        self.condition = self.condition.uniquify_variables(type_map, renamings)
        self.literal = self.literal.rename_variables(renamings)

    def instantiate(self, var_mapping, init_facts, fluent_facts,
                    objects_by_type, result):
        if self.parameters:
            var_mapping = var_mapping.copy()  # Will modify this.
            object_lists = [objects_by_type.get(par.type, [])
                            for par in self.parameters]
            for object_tuple in cartesian_product(*object_lists):
                for (par, obj) in zip(self.parameters, object_tuple):
                    var_mapping[par.name] = obj
                self._instantiate(var_mapping, init_facts, fluent_facts, result)
        else:
            self._instantiate(var_mapping, init_facts, fluent_facts, result)

    def _instantiate(self, var_mapping, init_facts, fluent_facts, result):
        condition = []
        try:
            self.condition.instantiate(var_mapping, init_facts, fluent_facts, condition)
        except conditions.Impossible:
            return
        effects = []
        self.literal.instantiate(var_mapping, init_facts, fluent_facts, effects)
        assert len(effects) <= 1
        if effects:
            result.append((condition, effects[0]))

    def relaxed(self):
        if self.literal.negated:
            return None
        else:
            return Effect(self.parameters, self.condition.relaxed(), self.literal)

    def simplified(self):
        return Effect(self.parameters, self.condition.simplified(), self.literal)


class ConditionalEffect(object):
    def __init__(self, condition, effect):
        if isinstance(effect, ConditionalEffect):
            self.condition = conditions.Conjunction([condition, effect.condition])
            self.effect = effect.effect
        else:
            self.condition = condition
            self.effect = effect

    def dump(self, indent="  "):
        print("%sif" % (indent))
        self.condition.dump(indent + "  ")
        print("%sthen" % (indent))
        self.effect.dump(indent + "  ")

    def normalize(self):
        norm_effect = self.effect.normalize()
        if isinstance(norm_effect, ConjunctiveEffect):
            new_effects = []
            for effect in norm_effect.effects:
                assert isinstance(effect, SimpleEffect) or isinstance(effect, ConditionalEffect)
                new_effects.append(ConditionalEffect(self.condition, effect))
            return ConjunctiveEffect(new_effects)
        elif isinstance(norm_effect, UniversalEffect):
            child = norm_effect.effect
            cond_effect = ConditionalEffect(self.condition, child)
            return UniversalEffect(norm_effect.parameters, cond_effect)
        else:
            return ConditionalEffect(self.condition, norm_effect)

    def extract_cost(self):
        return None, self


class UniversalEffect(object):
    def __init__(self, parameters, effect):
        if isinstance(effect, UniversalEffect):
            self.parameters = parameters + effect.parameters
            self.effect = effect.effect
        else:
            self.parameters = parameters
            self.effect = effect

    def dump(self, indent="  "):
        print("%sforall %s" % (indent, ", ".join(map(str, self.parameters))))
        self.effect.dump(indent + "  ")

    def normalize(self):
        norm_effect = self.effect.normalize()
        if isinstance(norm_effect, ConjunctiveEffect):
            new_effects = []
            for effect in norm_effect.effects:
                assert isinstance(effect, SimpleEffect) or isinstance(effect, ConditionalEffect) \
                       or isinstance(effect, UniversalEffect)
                new_effects.append(UniversalEffect(self.parameters, effect))
            return ConjunctiveEffect(new_effects)
        else:
            return UniversalEffect(self.parameters, norm_effect)

    def extract_cost(self):
        return None, self


class ConjunctiveEffect(object):
    def __init__(self, effects):
        flattened_effects = []
        for effect in effects:
            if isinstance(effect, ConjunctiveEffect):
                flattened_effects += effect.effects
            else:
                flattened_effects.append(effect)
        self.effects = flattened_effects

    def dump(self, indent="  "):
        print("%sand" % (indent))
        for eff in self.effects:
            eff.dump(indent + "  ")

    def normalize(self):
        new_effects = []
        for effect in self.effects:
            new_effects.append(effect.normalize())
        return ConjunctiveEffect(new_effects)

    def extract_cost(self, tmp_info):
        new_effects = []
        cost_effects = []
        index = 0
        for effect in self.effects:
            effect.tmp = tmp_info[index]
            if isinstance(effect, CostEffect):
                cost_effects.append(effect)
            else:
                new_effects.append(effect)
            index = index + 1
        return cost_effects, ConjunctiveEffect(new_effects)


class SimpleEffect(object):
    def __init__(self, effect):
        self.effect = effect

    def dump(self, indent="  "):
        print("%s%s" % (indent, self.effect))

    def normalize(self):
        return self

    def extract_cost(self):
        return None, self


class CostEffect(object):
    def __init__(self, effect):
        self.effect = effect

    def dump(self, indent="  "):
        print("%s%s" % (indent, self.effect))

    def normalize(self):
        return self

    def extract_cost(self):
        return self, None  # this would only happen if
        # an action has no effect apart from the cost effect

    def inst_cost_effect(self, cost_eff, var_mapping, init_facts, arg_used):
        if cost_eff.symbol == "*":
            new_expression_1 = f_expression.PrimitiveNumericExpression(cost_eff.args[0].name,
                                                                       cost_eff.args[0].args)
            new_expression_2 = f_expression.PrimitiveNumericExpression(cost_eff.args[1].name,
                                                                       cost_eff.args[1].args)
            inc_ins_1 = self.inst_cost_effect(new_expression_1, var_mapping,
                                              init_facts, arg_used)
            inc_ins_2 = self.inst_cost_effect(new_expression_2, var_mapping,
                                              init_facts, arg_used)

            if isinstance(inc_ins_1, pddl.f_expression.FunctionAssignment):
                value_1 = inc_ins_1.expression.value
            else:
                value_1 = inc_ins_1.value

            if isinstance(inc_ins_2, pddl.f_expression.FunctionAssignment):
                value_2 = inc_ins_2.expression.value
            else:
                value_2 = inc_ins_2.value

            result_expression = f_expression.PrimitiveNumericExpression(cost_eff.symbol, [inc_ins_1, inc_ins_2])
            result_expression.value = value_1 * value_2
            return result_expression
        elif cost_eff.symbol == "/":
            new_expression_1 = f_expression.PrimitiveNumericExpression(cost_eff.args[0].name,
                                                                       cost_eff.args[0].args)
            new_expression_2 = f_expression.PrimitiveNumericExpression(cost_eff.args[1].name,
                                                                       cost_eff.args[1].args)
            inc_ins_1 = self.inst_cost_effect(new_expression_1, var_mapping,
                                              init_facts, arg_used)
            inc_ins_2 = self.inst_cost_effect(new_expression_2, var_mapping,
                                              init_facts, arg_used)
            if isinstance(inc_ins_1, pddl.f_expression.FunctionAssignment):
                value_1 = inc_ins_1.expression.value
            else:
                value_1 = inc_ins_1.value

            if isinstance(inc_ins_2, pddl.f_expression.FunctionAssignment):
                value_2 = inc_ins_2.expression.value
            else:
                value_2 = inc_ins_2.value

            result_expression = f_expression.PrimitiveNumericExpression(cost_eff.symbol, [inc_ins_1, inc_ins_2])
            result_expression.value = value_1 / value_2
            return result_expression
        elif cost_eff.symbol == "-":
            new_expression_1 = f_expression.PrimitiveNumericExpression(cost_eff.args[0].name,
                                                                       cost_eff.args[0].args)
            new_expression_2 = f_expression.PrimitiveNumericExpression(cost_eff.args[1].name,
                                                                       cost_eff.args[1].args)
            inc_ins_1 = self.inst_cost_effect(new_expression_1, var_mapping,
                                              init_facts, arg_used)
            inc_ins_2 = self.inst_cost_effect(new_expression_2, var_mapping,
                                              init_facts, arg_used)
            if isinstance(inc_ins_1, pddl.f_expression.FunctionAssignment):
                value_1 = inc_ins_1.expression.value
            else:
                value_1 = inc_ins_1.value

            if isinstance(inc_ins_2, pddl.f_expression.FunctionAssignment):
                value_2 = inc_ins_2.expression.value
            else:
                value_2 = inc_ins_2.value

            result_expression = f_expression.PrimitiveNumericExpression(cost_eff.symbol, [inc_ins_1, inc_ins_2])
            result_expression.value = value_1 - value_2
            return result_expression
        elif cost_eff.symbol == "+":
            new_expression_1 = f_expression.PrimitiveNumericExpression(cost_eff.args[0].name,
                                                                       cost_eff.args[0].args)
            new_expression_2 = f_expression.PrimitiveNumericExpression(cost_eff.args[1].name,
                                                                       cost_eff.args[1].args)
            inc_ins_1 = self.inst_cost_effect(new_expression_1, var_mapping,
                                              init_facts, arg_used)
            inc_ins_2 = self.inst_cost_effect(new_expression_2, var_mapping,
                                              init_facts, arg_used)
            if isinstance(inc_ins_1, pddl.f_expression.FunctionAssignment):
                value_1 = inc_ins_1.expression.value
            else:
                value_1 = inc_ins_1.value

            if isinstance(inc_ins_2, pddl.f_expression.FunctionAssignment):
                value_2 = inc_ins_2.expression.value
            else:
                value_2 = inc_ins_2.value

            result_expression = f_expression.PrimitiveNumericExpression(cost_eff.symbol, [inc_ins_1, inc_ins_2])
            result_expression.value = value_1 + value_2
            return result_expression
        else:
            for arg in cost_eff.args:
                arg_used.append(var_mapping.get(arg.name, arg.name))
            return cost_eff.instantiate(var_mapping, init_facts)
