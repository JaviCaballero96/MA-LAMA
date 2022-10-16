import string

import pddl.f_expression
from . import conditions


def parse_expression(exp):
    if isinstance(exp, list):
        functionsymbol = exp[0]
        return PrimitiveNumericExpression(functionsymbol,
                                          [conditions.parse_term(arg) for arg in exp[1:]])
    elif exp.replace(".", "").isdigit():
        return NumericConstant(float(exp))
    elif exp[0] == "-":
        raise ValueError("Negative numbers are not supported")
    else:
        return PrimitiveNumericExpression(exp, [])


def parse_assignment(alist):
    assert len(alist) == 3
    op = alist[0]
    head = parse_expression(alist[1])
    if isinstance(alist[2], pddl.f_expression.PrimitiveNumericExpression):
        exp = alist[2]
    elif isinstance(alist[2], pddl.f_expression.NumericConstant):
        exp = parse_expression(str(alist[2].value))
    else:
        exp = parse_expression(alist[2])
    if op == "=":
        return Assign(head, exp)
    elif op == "increase":
        return Increase(head, exp)
    elif op == "decrease":
        return Decrease(head, exp)
    elif op == "assign":
        return Assign(head, exp)
    else:
        assert False, "Assignment operator not supported."


class FunctionalExpression(object):
    def __init__(self, parts):
        self.parts = tuple(parts)

    def dump(self, indent="  "):
        print("%s%s" % (indent, self._dump()))
        for part in self.parts:
            part.dump(indent + "  ")

    def _dump(self):
        return self.__class__.__name__

    def instantiate(self, var_mapping, init_facts):
        raise ValueError("Cannot instantiate condition: not normalized")


class NumericConstant(FunctionalExpression):
    parts = ()

    def __init__(self, value):
        # if value != int(value):
        #    raise ValueError("Fractional numbers are not supported")
        self.value = value

    def __eq__(self, other):
        return (self.__class__ == other.__class__ and self.value == other.value)

    def __str__(self):
        return "%s %s" % (self.__class__.__name__, self.value)

    def _dump(self):
        return str(self)

    def instantiate(self, var_mapping, init_facts):
        return self


class PrimitiveNumericExpression(FunctionalExpression):
    parts = ()

    def __init__(self, symbol, args):
        self.symbol = symbol
        self.args = tuple(args)

    def __eq__(self, other):
        return (self.__class__ == other.__class__ and self.symbol == other.symbol
                and self.args == other.args)

    def __str__(self):
        return "%s %s(%s)" % ("PNE", self.symbol, ", ".join(map(str, self.args)))

    def dump(self, indent="  "):
        print("%s%s" % (indent, self._dump()))
        for arg in self.args:
            arg.dump(indent + "  ")

    def _dump(self):
        return str(self)

    def instantiate(self, var_mapping, init_facts):
        args = [conditions.ObjectTerm(var_mapping.get(arg.name, arg.name))
                for arg in self.args]
        pne = PrimitiveNumericExpression(self.symbol, args)
        assert not self.symbol == "total-cost"
        # We know this expression is constant. Substitute it by corresponding
        # initialization from task.
        # TODO: Currently, complex metric operations are no permited
        for fact in init_facts:
            if isinstance(fact, FunctionAssignment):
                if fact.fluent == pne:
                    return fact
        assert False, "Could not find instantiation for PNE!"


class FunctionAssignment(object):
    def __init__(self, fluent, expression):
        self.fluent = fluent
        self.expression = expression

    def __str__(self):
        return "%s %s>%s" % (self.__class__.__name__, self.fluent, self.expression)

    def dump(self, indent="  "):
        print("%s%s" % (indent, self._dump()))
        self.fluent.dump(indent + "  ")
        self.expression.dump(indent + "  ")

    def _dump(self):
        return self.__class__.__name__

    def instantiate(self, var_mapping, init_facts):
        if not (isinstance(self.expression, PrimitiveNumericExpression) or
                isinstance(self.expression, NumericConstant)):
            raise ValueError("Cannot instantiate assignment: not normalized")
        # We know that this assignment is a cost effect of an action (for initial state
        # assignments, "instantiate" is not called). Hence, we know that the fluent is
        # the 0-ary "total-cost" which does not need to be instantiated
        # assert self.fluent.symbol == "total-cost"
        # The comment above is no longer true
        if isinstance(self.fluent, str):
            fluent = ''
        else:
            fluent = self.fluent.instantiate(var_mapping, init_facts)
        expression = self.expression.instantiate(var_mapping, init_facts)
        inst_function = self.__class__(fluent, expression)
        return inst_function


class Assign(FunctionAssignment):
    def __str__(self):
        return "%s := %s" % (self.fluent, self.expression)


class Increase(FunctionAssignment):
    pass


class Decrease(FunctionAssignment):
    pass
