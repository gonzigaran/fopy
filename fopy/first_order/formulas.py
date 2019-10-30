#!/usr/bin/env python
# -*- coding: utf8 -*-

# TERMS

from fopy.misc.myunicode import subscript
from itertools import product, combinations
from collections import defaultdict


class _Term(object):
    """
    Clase general de los terminos de primer orden
    """
    
    def __init__(self):
        pass
    
    def free_vars(self):
        raise NotImplemented
    
    def evaluate(self, model, vector):
        """
        Evalua el termino en el modelo para el vector de valores
        """
        raise NotImplemented
    
    def __hash__(self):
        raise NotImplemented
    
    def __le__(self, other):
        if self.grade() == other.grade():
            return repr(self) <= repr(other)
        else:
            return self.grade() <= other.grade()
    
    def grade(self):
        raise NotImplemented
    
    def __eq__(self, other):
        return hash(self) == hash(other)


class _Variable(_Term):
    """
    Variable de primer orden
    """
    
    def __init__(self, sym):
        if isinstance(sym, int):
            self.sym = "x" + subscript(sym)
        else:
            self.sym = sym
    
    def __repr__(self):
        return self.sym
    
    def __hash__(self):
        return hash(self.sym)
    
    def free_vars(self):
        return {self}
    
    def grade(self):
        return 0
    
    def evaluate(self, model, vector):
        try:
            return vector[self]
        except KeyError:
            raise ValueError("Free variable %s is not defined" % (self))


class OpSym(object):
    """
    Simbolo de operacion de primer orden
    """
    
    def __init__(self, op, arity):
        self.op = op
        self.arity = arity
    
    def __call__(self, *args):
        if len(args) != self.arity or any((not isinstance(a, _Term)) for a in args):
            raise ValueError("Arity not correct or any isn't a term")
        
        return _OpTerm(self, args)
    
    def __hash__(self):
        return hash((self.op, self.arity))
    
    def __repr__(self):
        return self.op


class _OpTerm(_Term):
    """
    Termino de primer orden de la aplicacion de una funcion
    """
    
    def __init__(self, sym, args):
        self.sym = sym
        self.args = args
    
    def __repr__(self):
        result = repr(self.sym)
        result += "("
        result += ", ".join(map(repr, self.args))
        result += ")"
        return result
    
    def __hash__(self):
        return hash((self.sym, self.args))
    
    def grade(self):
        return 1 + max(t.grade() for t in self.args)
    
    def free_vars(self):
        return set.union(*[f.free_vars() for f in self.args])
    
    def evaluate(self, model, vector):
        args = [t.evaluate(model, vector) for t in self.args]
        return model.operations[self.sym.op](*args)


# FORMULAS

class _Formula(object):
    """
    Clase general de las formulas de primer orden

    >>> x,y,z = variables("x","y","z") # declaracion de variables de primer orden

    >>> R = RelSym("R",2) # declaro una relacion R de aridad 2

    >>> f = OpSym("f",3) # declaro una operacion f de aridad 3

    >>> R(x,y) | R(y,x) & R(y,z)
    (R(x, y) ∨ (R(y, x) ∧ R(y, z)))

    >>> -R(f(x,y,z),y) | R(y,x) & R(y,z)
    (¬ R(f(x, y, z), y) ∨ (R(y, x) ∧ R(y, z)))

    >>> a = forall(x, -R(f(x,y,z),y))
    >>> a
    ∀ x ¬ R(f(x, y, z), y)
    >>> a.free_vars() == {y,z}
    True

    >>> a = R(x,x) & a
    >>> a
    (R(x, x) ∧ ∀ x ¬ R(f(x, y, z), y))
    >>> a.free_vars() == {x, y, z}
    True

    >>> exists(x, R(f(x,y,z),y))
    ∃ x R(f(x, y, z), y)

    >>> (-(true() & true() & false())) | false()
    ⊤

    """
    
    def __init__(self):
        pass
    
    def __and__(self, other):
        if isinstance(other, _AndFormula):
            return other & self
        elif isinstance(self, _TrueFormula):
            return other
        elif isinstance(other, _TrueFormula):
            return self
        elif isinstance(self, _FalseFormula) or isinstance(other, _FalseFormula):
            return false()
        elif self == -other:
            return false()
        
        return _AndFormula([self, other])
    
    def __or__(self, other):
        
        if isinstance(other, _OrFormula):
            return other | self
        elif isinstance(self, _FalseFormula):
            return other
        elif isinstance(other, _FalseFormula):
            return self
        elif isinstance(self, _TrueFormula) or isinstance(other, _TrueFormula):
            return true()
        elif self == -other:
            return true()
        
        return _OrFormula([self, other])
    
    def __neg__(self):
        if isinstance(self, _TrueFormula):
            return false()
        elif isinstance(self, _FalseFormula):
            return true()
        
        return _NegFormula(self)
    
    def free_vars(self):
        raise NotImplemented
    
    def satisfy(self, model, vector):
        raise NotImplemented
    
    def __eq__(self, other):
        return hash(self) == hash(other)
    
    def __hash__(self):
        raise NotImplemented
    
    def extension(self, model, arity=None):
        # TODO es un poco ineficiente al tener aridad mas grande que variables libres
        result = set()
        vs = list(self.free_vars())
        for t in product(model.universe,repeat=len(vs)):
            if self.satisfy(model,{vs[i]:t[i] for i in range(len(t))}):
                if arity and arity > len(vs):
                    for tt in product(model.universe, repeat=arity - len(vs)):
                        result.add(t+tt)
                else:
                    result.add(t)
        
        return result


class _NegFormula(_Formula):
    """
    Negacion de una formula
    """
    
    def __init__(self, f):
        self.f = f
    
    def __repr__(self):
        return "¬ %s" % self.f
    
    def __neg__(self):
        return self.f
    
    def __hash__(self):
        return hash(("-", self.f))
    
    def free_vars(self):
        return self.f.free_vars()
    
    def satisfy(self, model, vector):
        return not self.f.satisfy(model, vector)


class _BinaryOpFormula(_Formula):
    """
    Clase general de las formulas tipo f1 η ... η fn
    """
    
    def __init__(self, subformulas):
        self.subformulas = frozenset(subformulas)
    
    def free_vars(self):
        result = set()
        for f in self.subformulas:
            result = result.union(f.free_vars())
        return result


class _OrFormula(_BinaryOpFormula):
    """
    Disjuncion entre formulas
    """
    
    def __hash__(self):
        return hash(("or", self.subformulas))
    
    def __repr__(self):
        result = " ∨ ".join(str(f) for f in self.subformulas)
        result = "(" + result + ")"
        return result
    
    def __or__(self, other):
        if isinstance(self, _FalseFormula):
            return other
        elif isinstance(other, _FalseFormula):
            return self
        elif isinstance(other, _OrFormula):
            for a in self.subformulas:
                if -a in other.subformulas:
                    return true()
            return _OrFormula(self.subformulas | other.subformulas)
        elif -other in self.subformulas:
            return true()
        return _OrFormula(self.subformulas | {other})
    
    def satisfy(self, model, vector):
        # el or y el and de python son lazy
        return any(f.satisfy(model, vector) for f in self.subformulas)


class _AndFormula(_BinaryOpFormula):
    """
    Conjuncion entre formulas
    """
    
    def __hash__(self):
        return hash(("and", self.subformulas))
    
    def __repr__(self):
        result = " ∧ ".join(str(f) for f in self.subformulas)
        result = "(" + result + ")"
        return result
    
    def __and__(self, other):
        if isinstance(self, _TrueFormula):
            return other
        elif isinstance(other, _TrueFormula):
            return self
        elif isinstance(other, _AndFormula):
            for a in self.subformulas:
                if -a in other.subformulas:
                    return false()
            return _AndFormula(self.subformulas | other.subformulas)
        elif -other in self.subformulas:
            return false()
        return _AndFormula(self.subformulas | {other})
    
    def satisfy(self, model, vector):
        # el or y el and de python son lazy
        return all(f.satisfy(model, vector) for f in self.subformulas)


class RelSym(object):
    """
    Simbolo de relacion de primer orden
    """
    
    def __init__(self, rel, arity):
        self.rel = rel
        self.arity = arity
    
    def __call__(self, *args):
        if len(args) != self.arity or any((not isinstance(a, _Term)) for a in args):
            raise ValueError("Arity not correct or any isn't a term")
        
        return _RelFormula(self, args)
    
    def __repr__(self):
        return self.rel
    
    def __hash__(self):
        return hash((self.rel, self.arity))


class _RelFormula(_Formula):
    """
    Formula de primer orden de la aplicacion de una relacion
    """
    
    def __init__(self, sym, args):
        self.sym = sym
        self.args = args
    
    def __repr__(self):
        result = repr(self.sym)
        result += "("
        result += ", ".join(map(repr, self.args))
        result += ")"
        return result
    
    def free_vars(self):
        return set.union(*[f.free_vars() for f in self.args])
    
    def satisfy(self, model, vector):
        args = [t.evaluate(model, vector) for t in self.args]
        return model.relations[self.sym.rel](*args)
    
    def __hash__(self):
        return hash((self.sym, self.args))


class _EqFormula(_Formula):
    """
    Formula de primer orden que es una igualdad entre terminos
    """
    
    def __init__(self, t1, t2):
        if not (isinstance(t1, _Term) and isinstance(t2, _Term)):
            raise ValueError("Must be terms:%s %s" % (t1, t2))
        if t2 <= t1:
            t1, t2 = t2, t1
        self.t1 = t1
        self.t2 = t2
    
    def __repr__(self):
        return "%s == %s" % (self.t1, self.t2)
    
    def free_vars(self):
        return set.union(self.t1.free_vars(), self.t2.free_vars())
    
    def satisfy(self, model, vector):
        return self.t1.evaluate(model, vector) == self.t2.evaluate(model, vector)
    
    def __hash__(self):
        return hash((self.t1, self.t2))


class _QuantifierFormula(_Formula):
    """
    Clase general de una formula con cuantificador
    """
    
    def __init__(self, var, f):
        self.var = var
        self.f = f
    
    def free_vars(self):
        return self.f.free_vars() - {self.var}


class _ForAllFormula(_QuantifierFormula):
    """
    Formula Universal
    """
    
    def __repr__(self):
        return "∀ %s %s" % (self.var, self.f)
    
    def satisfy(self, model, vector):
        for i in model.universe:
            vector[self.var] = i
            if not self.f.satisfy(model, vector):
                return False
        return True
    
    def __hash__(self):
        return hash(("forall", self.var, self.f))


class _ExistsFormula(_QuantifierFormula):
    """
    Formula Existencial
    """
    
    def __repr__(self):
        return "∃ %s %s" % (self.var, self.f)
    
    def satisfy(self, model, vector):
        vector = vector.copy()
        for i in model.universe:
            vector[self.var] = i
            if self.f.satisfy(model, vector):
                return True
        return False
    
    def __hash__(self):
        return hash(("exists", self.var, self.f))


class _TrueFormula(_Formula):
    """
    Formula de primer orden constantemente verdadera
    """
    
    def __repr__(self):
        return "⊤"
    
    def free_vars(self):
        return set()
    
    def satisfy(self, model, vector):
        return True
    
    def extension(self, model, arity=None):
        if arity is None:
            raise ValueError("Extension of a non declared formula")
        return set(product(model.universe, repeat=arity))
    
    def __hash__(self):
        return hash(repr(self))


class _FalseFormula(_Formula):
    """
    Formula de primer orden constantemente falsa
    """
    
    def __repr__(self):
        return "⊥"
    
    def free_vars(self):
        return set()
    
    def satisfy(self, model, vector):
        return False
    
    def extension(self, model, arity=None):
        if arity is None:
            raise ValueError("Extension of a non declared formula")
        return set()
    
    def __hash__(self):
        return hash(repr(self))


# Shortcuts

def variables(*lvars):
    """
    Declara variables de primer orden
    """
    return [_Variable(x) for x in lvars]


def forall(var, formula):
    """
    Devuelve la formula universal
    """
    return _ForAllFormula(var, formula)


def eq(t1, t2):
    if t1 == t2:
        return true()
    return _EqFormula(t1, t2)


def exists(var, formula):
    """
    Devuelve la formula existencial
    """
    return _ExistsFormula(var, formula)


def true():
    """
    Devuelve la formula True
    """
    return _TrueFormula()


def false():
    """
    Devuelve la formula False
    """
    return _FalseFormula()


# Formulas generators

def grafico(term, vs, model):
    result = {}
    for tupla in product(model.universe, repeat=len(vs)):
        result[tupla] = term.evaluate(model, {v: a for v, a in zip(vs, tupla)})
    return tuple(sorted(result.items()))


def generate_terms(funtions, vs, model):
    """
    Devuelve todos los terminos (en realidad solo para infimo y supremo)
    usando las funciones y las variables con un anidaminento de rec
    """
    result = []
    graficos = set()
    
    for v in vs:
        g = grafico(v, vs, model)
        if not g in graficos:
            result.append(v)
            graficos.add(g)
    nuevos = [1]
    while nuevos:
        nuevos = []
        for f in funtions:
            for ts in product(result, repeat=f.arity):
                g = grafico(f(*ts), vs, model)
                if not g in graficos:
                    nuevos.append(f(*ts))
                    graficos.add(g)
            result += nuevos
    return result


def atomics(relations, terms, equality=True):
    """
    Genera todas las formulas atomicas con relations
    de arity variables libres

    >>> R = RelSym("R",2)
    >>> vs = variables(*range(2))
    >>> list(atomics([R],vs))
    [R(x₀, x₀), R(x₀, x₁), R(x₁, x₀), R(x₁, x₁), x₀ == x₁]
    >>> list(atomics([R],vs,equality=False))
    [R(x₀, x₀), R(x₀, x₁), R(x₁, x₀), R(x₁, x₁)]
    """
    terms
    for r in relations:
        for t in product(terms, repeat=r.arity):
            yield r(*t)
    
    if equality:
        for t in combinations(terms, 2):
            yield eq(*t)
