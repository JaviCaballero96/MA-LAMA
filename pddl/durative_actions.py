# -*- coding: latin-1 -*-

import copy

from . import conditions as cond
from . import effects as eff
from . import pddl_types
from . import f_expression


class DurativeAction(object):
    def __init__(self, name, duration_t, parameters, conditions, effects, cost):
        self.name = name
        self.duration_t = duration_t
        self.parameters = parameters
        self.conditions = conditions
        cond_tmp_info = conditions.temp_info
        self.effects = effects
        self.cost = cost
        self.uniquify_variables()  # TODO: uniquify variables in cost?
        self.conditions.include_temp_info(cond_tmp_info)

    def __repr__(self):
        return "<Durative-Action %r at %#x>" % (self.name, id(self))

    def parse(alist):
        iterator = iter(alist)
        assert next(iterator) == ":durative-action"
        name = next(iterator)
        parameters_tag_opt = next(iterator)
        if parameters_tag_opt == ":parameters":
            parameters = pddl_types.parse_typed_list(next(iterator),
                                                     only_variables=True)
            duration_tag_opt = next(iterator)
        else:
            parameters = []
            duration_tag_opt = parameters_tag_opt
        if duration_tag_opt == ":duration":
            print("Reading duration")
            duration_list = next(iterator)
            duration_t = parse_duration(duration_list)
            precondition_tag_opt = next(iterator)
        if precondition_tag_opt == ":condition":
            raw = next(iterator)
            precondition = cond.parse_durative_condition(raw)
            precondition = precondition.simplified()
            precondition.temp_info = precondition.parse_temp_info(raw)
            effect_tag = next(iterator)
        else:
            precondition = cond.Conjunction([])
            effect_tag = precondition_tag_opt
        assert effect_tag == ":effect"
        effect_list = next(iterator)
        effects = []
        try:
            cost = eff.parse_effects(effect_list, effects, duration_t)
        except ValueError as e:
            raise SystemExit("Error in Action %s\nReason: %s." % (name, e))
        for rest in iterator:
            assert False, rest
        return DurativeAction(name, duration_t, parameters, precondition, effects, cost)

    parse = staticmethod(parse)

    def uniquify_variables(self):
        self.type_map = dict([(par.name, par.type) for par in self.parameters])
        self.conditions = self.conditions.uniquify_variables(self.type_map)
        for effect in self.effects:
            if not isinstance(effect, eff.CostEffect):
                effect.uniquify_variables(self.type_map)


def parse_duration(alist):
    equal = alist[0]
    duration_name = alist[1]
    assert equal == "="
    assert duration_name == "?duration"
    return f_expression.parse_assignment(alist)
