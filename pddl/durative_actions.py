# -*- coding: latin-1 -*-

import copy

from . import conditions
from . import effects
from . import pddl_types


class DurativeAction(object):
    def __init__(self, name, duration, parameters, condition, effects, cost):
        self.name = name
        self.duration = duration
        self.parameters = parameters
        self.condition = condition
        self.effects = effects
        self.cost = cost
        self.uniquify_variables()  # TODO: uniquify variables in cost?

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
            precondition_tag_opt = next(iterator)
        if precondition_tag_opt == ":precondition":
            precondition = conditions.parse_condition(next(iterator))
            precondition = precondition.simplified()
            effect_tag = next(iterator)
        else:
            precondition = conditions.Conjunction([])
            effect_tag = precondition_tag_opt
        assert effect_tag == ":effect"
        effect_list = next(iterator)
        eff = []
        try:
            cost = effects.parse_effects(effect_list, eff)
        except ValueError as e:
            raise SystemExit("Error in Action %s\nReason: %s." % (name, e))
        for rest in iterator:
            assert False, rest
        return DurativeAction(name, parameters, precondition, eff, cost)

    parse = staticmethod(parse)
