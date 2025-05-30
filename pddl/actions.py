# -*- coding: latin-1 -*-

import copy

import pddl.f_expression
from . import conditions
from . import effects as Effects
from . import pddl_types
from . import f_expression


class Action(object):
    def __init__(self, name, parameters, precondition, num_condition, effects, cost):
        self.name = name
        self.parameters = parameters
        self.precondition = precondition
        self.num_condition = num_condition
        self.effects = effects
        self.cost = cost
        self.uniquify_variables()  # TODO: uniquify variables in cost?

    def __repr__(self):
        return "<Action %r at %#x>" % (self.name, id(self))

    def parse(alist):
        iterator = iter(alist)
        assert next(iterator) == ":action"
        name = next(iterator)
        parameters_tag_opt = next(iterator)
        if parameters_tag_opt == ":parameters":
            parameters = pddl_types.parse_typed_list(next(iterator),
                                                     only_variables=True)
            precondition_tag_opt = next(iterator)
        else:
            parameters = []
            precondition_tag_opt = parameters_tag_opt
        if precondition_tag_opt == ":precondition":
            precondition, num_condition = conditions.parse_condition(next(iterator))
            precondition = precondition.simplified()
            num_condition_final = []
            for num_cond in num_condition:
                num_condition_final.append(("no", num_cond[1]))
            effect_tag = next(iterator)
        else:
            precondition = conditions.Conjunction([])
            effect_tag = precondition_tag_opt
        assert effect_tag == ":effect"
        effect_list = next(iterator)
        eff = []
        try:
            cost = Effects.parse_effects(effect_list, eff, "no duration")
        except ValueError as e:
            raise SystemExit("Error in Action %s\nReason: %s." % (name, e))
        for rest in iterator:
            assert False, rest

        for effect in eff:
            effect.eff_type = "eff"
        for cost in eff:
            cost.eff_type = "eff"

        return Action(name, parameters, precondition, num_condition_final, eff, cost)

    parse = staticmethod(parse)

    def dump(self):
        print("%s(%s)" % (self.name, ", ".join(map(str, self.parameters))))
        print("Precondition:")
        self.precondition.dump()
        print("Effects:")
        for eff in self.effects:
            eff.dump()
        print("Cost:")
        if (self.cost):
            self.cost.dump()
        else:
            print("  None")

    def uniquify_variables(self):
        self.type_map = dict([(par.name, par.type) for par in self.parameters])
        self.precondition = self.precondition.uniquify_variables(self.type_map)
        for effect in self.effects:
            if not isinstance(effect, Effects.CostEffect) and "block" not in effect.eff_type:
                effect.uniquify_variables(self.type_map)

    def unary_actions(self):
        # TODO: An neue Effect-Repräsentation anpassen.
        result = []
        for i, effect in enumerate(self.effects):
            unary_action = copy.copy(self)
            unary_action.name += "@%d" % i
            if isinstance(effect, Effects.UniversalEffect):
                # Careful: Create a new parameter list, the old one might be shared.
                unary_action.parameters = unary_action.parameters + effect.parameters
                effect = effect.effect
            if isinstance(effect, Effects.ConditionalEffect):
                unary_action.precondition = conditions.Conjunction([unary_action.precondition,
                                                                    effect.condition]).simplified()
                effect = effect.effect
            unary_action.effects = [effect]
            result.append(unary_action)
        return result

    def relaxed(self):
        new_effects = []
        for eff in self.effects:
            relaxed_eff = eff.relaxed()
            if relaxed_eff:
                new_effects.append(relaxed_eff)
        return Action(self.name, self.parameters,
                      self.precondition.relaxed().simplified(),
                      new_effects)

    def untyped(self):
        # We do not actually remove the types from the parameter lists,
        # just additionally incorporate them into the conditions.
        # Maybe not very nice.
        result = copy.copy(self)
        parameter_atoms = [par.to_untyped_strips() for par in self.parameters]
        new_precondition = self.precondition.untyped()
        result.precondition = conditions.Conjunction(parameter_atoms + [new_precondition])
        result.effects = [eff.untyped() for eff in self.effects]
        return result

    def untyped_strips_preconditions(self):
        # Used in instantiator for converting unary actions into prolog rules.
        return [par.to_untyped_strips() for par in self.parameters] + \
               self.precondition.to_untyped_strips()

    def instantiate(self, var_mapping, init_facts, fluent_facts, objects_by_type, metric, modules):
        """Return a PropositionalAction which corresponds to the instantiation of
        this action with the arguments in var_mapping. Only fluent parts of the
        conditions (those in fluent_facts) are included. init_facts are evaluated
        whilte instantiating.
        Precondition and effect conditions must be normalized for this to work.
        Returns None if var_mapping does not correspond to a valid instantiation
        (because it has impossible preconditions or an empty effect list.)"""
        arg_list = [var_mapping[par.name] for par in self.parameters]
        name = "(%s %s)" % (self.name, " ".join(arg_list))

        precondition = []
        try:
            self.precondition.instantiate(var_mapping, init_facts,
                                          fluent_facts, precondition)
        except conditions.Impossible:
            return None
        effects = []
        for eff in self.effects:
            if isinstance(eff, Effects.CostEffect):
                if isinstance(eff.effect, pddl.f_expression.Increase):
                    eff_aux = f_expression.Increase("", "")
                elif isinstance(eff.effect, pddl.f_expression.Decrease):
                    eff_aux = f_expression.Decrease("", "")
                elif isinstance(eff.effect, pddl.f_expression.Assign):
                    eff_aux = f_expression.Assign("", "")
                elif isinstance(eff.effect, pddl.f_expression.GreaterThan):
                    eff_aux = f_expression.GreaterThan("", "")
                elif isinstance(eff.effect, pddl.f_expression.LessThan):
                    eff_aux = f_expression.LessThan("", "")

                eff_aux.fluent, is_mod_function = eff.effect.fluent.instantiate(var_mapping, init_facts, modules,
                                                                                objects_by_type)
                arg_used = [var_mapping.get(arg.name, arg.name) for arg in eff.effect.fluent.args]

                eff_aux.expression= eff.inst_cost_effect(eff.effect.expression, var_mapping,
                                                                           init_facts, arg_used, modules,
                                                                           objects_by_type)

                if isinstance(eff_aux.expression, tuple):
                    is_mod_function = eff_aux.expression[1]
                    eff_aux.expression = eff_aux.expression[0]

                args_ordered = [arg for arg in arg_list if arg in arg_used]
                eff_aux.negated = False
                eff_aux.parameters = args_ordered
                eff_aux.eff_type = eff.eff_type
                eff_aux.is_mod_function = is_mod_function
                effects.append(([], eff_aux))
            else:
                eff.instantiate(var_mapping, init_facts, fluent_facts,
                                objects_by_type, effects)
                if effects:
                    effects[-1][1].eff_type = eff.eff_type
        cost = float(0)
        if effects:
            if not self.cost:
                cost = float(0)
            else:
                for cond, cost_eff in effects:
                    if cost_eff.eff_type == "num eff" and cost_eff.is_mod_function:
                        continue
                    if isinstance(cost_eff, pddl.f_expression.Increase):
                        for m_elem in metric:
                            if not isinstance(m_elem, str):
                                if m_elem.symbol == "*":
                                    if m_elem.args[1].name == cost_eff.fluent.fluent.symbol and \
                                            [arg1.name for arg1 in m_elem.args[1].args] == [arg2.name for arg2 in
                                                                                            cost_eff.fluent.
                                                                                                    fluent.args]:
                                        if isinstance(cost_eff.expression,
                                                      pddl.f_expression.PrimitiveNumericExpression):
                                            cost = cost + (cost_eff.expression.value * float(m_elem.args[0].name))
                                        else:
                                            cost = cost + (cost_eff.expression.expression.value * float(m_elem.args[0].
                                                                                                        name))
                                            # cost = cost + int(cost_eff.effect.instantiate(var_mapping,
                                            # init_facts).expression.value)
                                            # cost = cost + self.calculateCost(cost_eff.effect, var_mapping, init_facts)
                                elif m_elem.symbol == "/":
                                    if m_elem.args[1].name == cost_eff.fluent.fluent.symbol and \
                                            [arg1.name for arg1 in m_elem.args[1].args] == [arg2.name for arg2 in
                                                                                            cost_eff.fluent.
                                                                                                    fluent.args]:
                                        if isinstance(cost_eff.expression,
                                                      pddl.f_expression.PrimitiveNumericExpression):
                                            cost = cost + (cost_eff.expression.value / float(m_elem.args[0].name))
                                        else:
                                            cost = cost + (cost_eff.expression.expression.value / float(m_elem.args[0].
                                                                                                        name))
                                else:
                                    if m_elem.symbol == cost_eff.fluent.fluent.symbol and \
                                            [arg1.name for arg1 in m_elem.args] == [arg2.name for arg2 in
                                                                                            cost_eff.fluent.
                                                                                                    fluent.args]:
                                        if isinstance(cost_eff.expression,
                                                      pddl.f_expression.PrimitiveNumericExpression):
                                            cost = cost + cost_eff.expression.value
                                        else:
                                            cost = cost + cost_eff.expression.expression.value
                    if isinstance(cost_eff, pddl.f_expression.Decrease):
                        for m_elem in metric:
                            if not isinstance(m_elem, str):
                                if m_elem.symbol == "*":
                                    if m_elem.args[1].name == cost_eff.fluent.fluent.symbol and \
                                            [arg1.name for arg1 in m_elem.args[1].args] == [arg2.name for arg2 in
                                                                                            cost_eff.fluent.
                                                                                                    fluent.args]:
                                        if isinstance(cost_eff.expression,
                                                      pddl.f_expression.PrimitiveNumericExpression):
                                            cost = cost - (cost_eff.expression.value * float(m_elem.args[0].name))
                                        else:
                                            cost = cost - (cost_eff.expression.expression.value * float(m_elem.args[0].
                                                                                                        name))
                                elif m_elem.symbol == "/":
                                    if m_elem.args[1].name == cost_eff.fluent.fluent.symbol and \
                                            [arg1.name for arg1 in m_elem.args[1].args] == [arg2.name for arg2 in
                                                                                            cost_eff.fluent.
                                                                                                    fluent.args]:
                                        if isinstance(cost_eff.expression,
                                                      pddl.f_expression.PrimitiveNumericExpression):
                                            cost = cost - (cost_eff.expression.value / float(m_elem.args[0].name))
                                        else:
                                            cost = cost - (cost_eff.expression.expression.value / float(m_elem.args[0].
                                                                                                        name))
                                else:
                                    if m_elem.symbol == cost_eff.fluent.fluent.symbol and \
                                            [arg1.name for arg1 in m_elem.args] == [arg2.name for arg2 in
                                                                                            cost_eff.fluent.
                                                                                                    fluent.args]:
                                        if isinstance(cost_eff.expression,
                                                      pddl.f_expression.PrimitiveNumericExpression):
                                            cost = cost - cost_eff.expression.value
                                        else:
                                            cost = cost - cost_eff.expression.expression.value

                # cost = int(self.cost.instantiate(var_mapping, init_facts).expression.value)
            return PropositionalAction(name, precondition, effects, cost)
        else:
            return None

    def calculateCost(self, cost_eff, var_mapping, init_facts):
        new_effect_1 = f_expression.Increase("", "")
        new_effect_2 = f_expression.Increase("", "")
        if cost_eff.expression.symbol == "*":
            new_effect_1.expression = f_expression.PrimitiveNumericExpression(cost_eff.expression.args[0].name,
                                                                              cost_eff.expression.args[0].args)
            new_effect_2.expression = f_expression.PrimitiveNumericExpression(cost_eff.expression.args[1].name,
                                                                              cost_eff.expression.args[1].args)
            new_effect_1.fluent = ""
            new_effect_2.fluent = ""
            return self.calculateCost(new_effect_1, var_mapping, init_facts) * self.calculateCost(
                new_effect_2, var_mapping, init_facts)
        elif cost_eff.expression.symbol == "/":
            new_effect_1.expression = f_expression.PrimitiveNumericExpression(cost_eff.expression.args[0].name,
                                                                              cost_eff.expression.args[0].args)
            new_effect_2.expression = f_expression.PrimitiveNumericExpression(cost_eff.expression.args[1].name,
                                                                              cost_eff.expression.args[1].args)
            new_effect_1.fluent = ""
            new_effect_2.fluent = ""
            return self.calculateCost(new_effect_1, var_mapping, init_facts) / self.calculateCost(
                new_effect_2, var_mapping, init_facts)
        elif cost_eff.expression.symbol == "-":
            new_effect_1.expression = f_expression.PrimitiveNumericExpression(cost_eff.expression.args[0].name,
                                                                              cost_eff.expression.args[0].args)
            new_effect_2.expression = f_expression.PrimitiveNumericExpression(cost_eff.expression.args[1].name,
                                                                              cost_eff.expression.args[1].args)
            new_effect_1.fluent = ""
            new_effect_2.fluent = ""
            return self.calculateCost(new_effect_1, var_mapping, init_facts) - self.calculateCost(
                new_effect_2, var_mapping, init_facts)
        elif cost_eff.expression.symbol == "+":
            new_effect_1.expression = f_expression.PrimitiveNumericExpression(cost_eff.expression.args[0].name,
                                                                              cost_eff.expression.args[0].args)
            new_effect_2.expression = f_expression.PrimitiveNumericExpression(cost_eff.expression.args[1].name,
                                                                              cost_eff.expression.args[1].args)
            new_effect_1.fluent = ""
            new_effect_2.fluent = ""
            return self.calculateCost(new_effect_1, var_mapping, init_facts) + self.calculateCost(
                new_effect_2, var_mapping, init_facts)
        else:
            return cost_eff.expression.instantiate(var_mapping, init_facts).expression.value


class PropositionalAction:
    def __init__(self, name, precondition, effects, cost):
        self.name = name
        self.precondition = precondition
        self.add_effects = []
        self.del_effects = []
        self.func_effects = []
        for condition, effect in effects:
            if not effect.negated:
                if isinstance(effect, f_expression.Increase):
                    self.func_effects.append((condition, effect))
                elif isinstance(effect, f_expression.Decrease):
                    self.func_effects.append((condition, effect))
                elif isinstance(effect, f_expression.Assign):
                    self.func_effects.append((condition, effect))
                elif isinstance(effect, f_expression.GreaterThan):
                    self.func_effects.append((condition, effect))
                elif isinstance(effect, f_expression.LessThan):
                    self.func_effects.append((condition, effect))
                else:
                    self.add_effects.append((condition, effect))
        # Warning: This is O(N^2), could be turned into O(N).
        # But that might actually harm performance, since there are
        # usually few effects.
        # TODO: Measure this in critical domains, then use sets if acceptable.
        for condition, effect in effects:
            if effect.negated and (condition, effect.negate()) not in self.add_effects:
                self.del_effects.append((condition, effect.negate()))
        self.cost = cost

    def dump(self):
        print(self.name)
        for fact in self.precondition:
            print("PRE: %s" % fact)
        for cond, fact in self.add_effects:
            print("ADD: %s -> %s" % (", ".join(map(str, cond)), fact))
        for cond, fact in self.del_effects:
            print("DEL: %s -> %s" % (", ".join(map(str, cond)), fact))
        print("cost:", self.cost)
