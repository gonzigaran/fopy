# -*- coding: utf-8 -*-
#!/usr/bin/env python

from fopy.misc.misc import indent


class Homomorphism(object):
    def __init__(self, d, source, target, subtype):
        self.values = d
        self.source = source
        self.target = target
        self.subtype = subtype

    def __call__(self, x):
        try:
            return self.values[x]
        except KeyError:
            return

    def vcall(self, xvector):
        return tuple(self(x) for x in xvector)

    def __repr__(self):
        result = "Homomorphism(\n"
        for a, b in self.values.items():
            result += "  %s->%s\n" % (a, b)
        result += "from:\n"
        result += indent(repr(self.source))
        result += "to:\n"
        result += indent(repr(self.target))
        result += ")"
        return result


class Isomorphism(object):
    def __init__(self, d, source, target, subtype):
        self.values = d
        self.source = source
        self.target = target
        self.subtype = subtype

    def __call__(self, x):
        try:
            return self.values[x]
        except KeyError:
            return
        return self.values[x]

    def inverse(self):
        return Isomorphism({v: k for k, v in self.values.items()}, self.target, self.source, self.subtype)

    def vcall(self, xvector):
        return tuple(self(x) for x in xvector)

    def __repr__(self):
        result = "Isomorphism(\n"
        for a, b in self.values.items():
            result += "  %s->%s\n" % (a, b)
        result += "from:\n"
        result += indent(repr(self.source))
        result += "to:\n"
        result += indent(repr(self.target))
        result += ")"
        return result


class Automorphism(object):
    def __init__(self, d, model, subtype):
        self.values = d
        self.model = model
        self.subtype = subtype

    def __call__(self, x):
        try:
            return self.values[x]
        except KeyError:
            return
        return self.values[x]

    def vcall(self, xvector):
        return tuple(self(x) for x in xvector)

    def __repr__(self):
        result = "Automorphism(\n"
        for a, b in self.values.items():
            result += "  %s->%s\n" % (a, b)
        result += "from:\n"
        result += indent(repr(self.model))
        result += ")"
        return result

