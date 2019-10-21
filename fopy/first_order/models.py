# -*- coding: utf-8 -*-
#!/usr/bin/env python

from itertools import product
from misc import indent


class Model(object):
    def __init__(self, universe, relations, operations):
        """
        Model
        Input: a universe list, relations dict, operations dict
        """
        self.universe = sorted(universe)
        self.relations = relations
        self.operations = operations

    def restrict(self, subuniverse):
        """
        restricion de un subuniverso a ciertas relaciones
        """
        relations = {}
        for r in self.relations:
            relations[r] = self.relations[r].restrict(subuniverse)
        operations = {}
        for o in self.operations:
            operations[o] = self.operations[o].restrict(subuniverse)
        return Model(subuniverse, relations, operations)

    def substructure(self, generators):
        news = set(generators)
        universe = set()

        while news:
            local_news = set()
            for operation in self.operations:
                arity = self.operations[operation].arity
                for t in product(universe | news, repeat=arity):
                    if any(e in news for e in t):  # tiene alguno nuevo
                        local_news.add(self.operations[operation](*t))

            local_news -= universe
            local_news -= news
            universe |= news
            news = local_news
        return self.restrict(universe)

    def __repr__(self):
        result = "Model(universe=%s,\nrelations=\n" % self.universe
        for sym in sorted(self.relations):
            result += indent(self.relations[sym]) + "\n"
        result += "operations=\n"
        for sym in sorted(self.operations):
            result += indent(self.operations[sym]) + "\n"
        result += ")"
        return result

    def __len__(self):
        return len(self.universe)

