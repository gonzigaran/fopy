# -*- coding: utf-8 -*-
# !/usr/bin/env python
# TODO decoradores para hacer operaciones y relaciones procedurales
class Relation(object):
    """
    Relation
    """
    
    def __init__(self, sym, arity, rel=set(), formula=None):
        self.sym = sym
        self.arity = arity
        self.r = rel
        self.formula = formula
    
    def add(self, t):
        if len(t) != self.arity:
            raise ValueError('%s is not of arity %s' % (t, self.arity))
        self.r.add(t)
    
    def __repr__(self):
        return "%s : %s" % (self.sym, self.r)
    
    def __call__(self, *args):
        return args in self.r
    
    def __len__(self):
        return len(self.r)
    
    def __iter__(self):
        return iter(self.r)
    
    def restrict(self, subuniverse):
        result = Relation(self.sym, self.arity)
        subuniverse = set(subuniverse)
        for t in self.r:
            if set(t) <= subuniverse:
                result.add(t)
        return result
    
    def __hash__(self):
        return hash(frozenset(self.r))


class Operation(object):
    """
    Operation
    """
    
    def __init__(self, sym, arity):
        self.sym = sym
        self.arity = arity
        self.op = dict()
    
    def add(self, t):
        if len(t) - 1 != self.arity:
            raise ValueError('%s is not of arity %s' % (t[:-1], self.arity))
        self.op[t[:-1]] = t[-1]
    
    def __repr__(self):
        return "%s : %s" % (self.sym, self.op)
    
    def __call__(self, *args):
        return self.op[args]
    
    def __len__(self):
        return len(self.op)
    
    def restrict(self, subuniverse):
        result = Operation(self.sym, self.arity)
        subuniverse = set(subuniverse)
        for t in self.op:
            if set(t) <= subuniverse:
                result.add(t + (self.op[t],))
        return result
    
    def graph_rel(self):
        rel = {t + (self.op[t],) for t in self.op}
        return Relation("g" + self.sym, self.arity + 1, rel)

def FO_Operation_decorator(d_universe, arity=None):
    """
    Decorador para definir facilmente operaciones de primer orden
    con funciones en Python
    """
    def wrap(f):
        return FO_Operation(f, d_universe=d_universe, arity=arity)
    return wrap


def FO_Relation_decorator(d_universe, arity=None):
    """
    Decorador para definir facilmente relaciones de primer orden
    con funciones en Python
    """
    def wrap(f):
        return FO_Relation(f, d_universe=d_universe, arity=arity)
    return wrap