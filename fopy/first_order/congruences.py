#!/usr/bin/env python
# -*- coding: utf8 -*-

from fopy.first_order import Relation
from fopy.misc.misc import indent
from fopy.misc.myunicode import subscript
from fopy.interfaces.minion import MinionSol
from itertools import combinations, product, chain
from functools import lru_cache
from functools import reduce
from collections import defaultdict


class UnionFind(object):
    def __init__(self):
        '''
        Create an empty union find data structure.
        '''
        self.num_weights = {}
        self.parent_pointers = {}
        self.num_to_objects = {}
        self.objects_to_num = {}
        self.__repr__ = self.__str__
    def insert_objects(self, objects):
        '''
        Insert a sequence of objects into the structure.  All must be Python hashable.
        '''
        for object in objects:
            self.find(object);
    def find(self, object):
        '''
        Find the root of the set that an object is in.
        If the object was not known, will make it known, and it becomes its own set.
        Object must be Python hashable.
        '''
        if not object in self.objects_to_num:
            obj_num = len(self.objects_to_num)
            self.num_weights[obj_num] = 1
            self.objects_to_num[object] = obj_num
            self.num_to_objects[obj_num] = object
            self.parent_pointers[obj_num] = obj_num
            return object
        stk = [self.objects_to_num[object]]
        par = self.parent_pointers[stk[-1]]
        while par != stk[-1]:
            stk.append(par)
            par = self.parent_pointers[par]
        for i in stk:
            self.parent_pointers[i] = par
        return self.num_to_objects[par]
    def union(self, object1, object2):
        '''
        Combine the sets that contain the two objects given.
        Both objects must be Python hashable.
        If either or both objects are unknown, will make them known, and combine them.
        '''
        o1p = self.find(object1)
        o2p = self.find(object2)
        if o1p != o2p:
            on1 = self.objects_to_num[o1p]
            on2 = self.objects_to_num[o2p]
            w1 = self.num_weights[on1]
            w2 = self.num_weights[on2]
            if w1 < w2:
                o1p, o2p, on1, on2, w1, w2 = o2p, o1p, on2, on1, w2, w1
            self.num_weights[on1] = w1+w2
            del self.num_weights[on2]
            self.parent_pointers[on2] = on1
    def to_list(self):
        """
        Returns list of lists
        """
        result = defaultdict(list)
        for key,value in self.parent_pointers.items():
            result[value].append(self.num_to_objects[key])
        return list(result.values())
    def __str__(self):
        '''
        Included for testing purposes only.
        All information needed from the union find data structure can be attained
        using find.
        '''
        sets = {}
        for i in xrange(len(self.objects_to_num)):
            sets[i] = []
        for i in self.objects_to_num:
            sets[self.objects_to_num[self.find(i)]].append(i)
        out = []
        for i in sets.itervalues():
            if i:
                out.append(repr(i))
        return ', '.join(out)



class Eq_Rel(Relation):
    """
    Relacion binaria que cumple los axiomas de equivalencia

    >>> rel = Eq_Rel([(0, 0),(1, 1),(2, 2),(3, 3),(4, 4),(2, 3),(3, 2)], {0,1,2,3,4})
    >>> rel(2, 3)
    True
    >>> rel(4, 3)
    False
    >>> rel.table()
    [[0, 0], [1, 1], [2, 2], [2, 3], [3, 2], [3, 3], [4, 4]]
    """
    count = 0
    
    def __init__(self, sym, rel=set(), formula=None):
        if not sym:
            sym = "≡" + subscript(Eq_Rel.count)
        super(Eq_Rel, self).__init__(sym, 2, rel, formula)
        assert self.symm() and self.refl() and self.trans()
    # TODO PARTITION USANDO UNION FIND
    def refl(self):
        for x in self.model.universe:
            if not (x, x) in self.d:
                return False
        return True
    
    def symm(self):
        for r in self.d:
            if not (r[1], r[0]) in self.d:
                return False
        return True
    
    def trans(self):
        for r in self.d:
            for s in self.d:
                if r[1] == s[0]:
                    if not (r[0], s[1]) in self.d:
                        return False
        return True


class Congruence(Eq_Rel):
    """
    Congruencia

    >>> from definability import fotheories
    >>> rel = Congruence([(1, 1),(2, 2),(3, 3),(0, 0),(1, 3),(3, 1),(0, 2),(2, 0)], fotheories.Lat.find_models(4)[0])
    >>> rel(1, 3)
    True
    >>> rel(0, 3)
    False
    >>> rel.table()
    [[0, 0], [0, 2], [1, 1], [1, 3], [2, 0], [2, 2], [3, 1], [3, 3]]
    """
    
    def __init__(self, d, model):
        assert d and isinstance(d, list) and isinstance(d[0], tuple)
        assert model
        self.model = model
        self.d = d
        super(Congruence, self).__init__(d, model)
        # assert self.preserva_operaciones()
    
    def relacionados(self, t, s):
        for i in range(len(t)):
            if not (t[i], s[i]) in self.d:
                return False
        return True
    
    def __preserva_operacion(self, op):
        if self.model.operations[op].arity() == 0:
            pass
        else:
            for t in self.model.operations[op].domain():
                for s in self.model.operations[op].domain():
                    if self.relacionados(t, s):
                        if not (self.model.operations[op](*t), self.model.operations[op](*s)) in self.d:
                            return False
        return True
    
    def preserva_operaciones(self):
        result = True
        for op in self.model.operations:
            result = result and self.__preserva_operacion(op)
        return result
    
    @lru_cache(maxsize=None)
    def classes(self):
        result = set()
        for x in self.model.universe:
            result.add(frozenset(self.equiv_class(x)))
        return result
    
    def equiv_class(self, x):
        return {y for y in self.model.universe if (x, y) in self.d}
    
    def __and__(self, other):
        """
        Genera la congruencia a partir de la intersección de 2 congruencias
        """
        assert self.model == other.model
        result = list(set(self.d) & set(other.d))
        return Congruence(result, self.model)
    
    def __or__(self, other):
        """
        Genera la congruencia a partir de la unión de 2 congruencias
        """
        assert self.model == other.model
        result_ant = {}
        result = set(self.d) | set(other.d)
        while (result != result_ant):
            result_ant = result
            for x in self.model.universe:
                for y in self.model.universe:
                    if not (x, y) in result_ant:
                        for z in self.model.universe:
                            if (x, z) in result_ant and (z, y) in result_ant:
                                result = result | {(x, y), (y, x)}
        return Congruence(list(result), self.model)
    
    def __lt__(self, other):
        if self & other == self and self != other:
            return True
        return False
    
    def __le__(self, other):
        if self & other == self:
            return True
        return False
    
    def __eq__(self, other):
        if self.model != other.model:
            return False
        if set(self.d) != set(other.d):
            return False
        return True
    
    def __hash__(self):
        return hash(frozenset(self.dict.items()))
    
    def __repr__(self):
        result = "Congruence(\n"
        table = ["%s," % x for x in self.table()]
        table = indent("\n".join(table))
        return result + table + ")"


class CongruenceSystem(object):
    """
    Sistema de Congruecias
    Dado una lista de congruencias, una lista de elementos y un sigma generador
    del proyecto, genera el Sistema de Congruencias para ese proyectivo

    >>> from definability import fotheories
    >>> C1 = Congruence([(1, 1),(2, 2),(3, 3),(0, 0),(1, 3),(3, 1),(0, 2),(2, 0)], fotheories.Lat.find_models(4)[0])
    >>> C2 = Congruence([(1, 1),(2, 2),(3, 3),(0, 0),(0, 3),(3, 0),(1, 2),(2, 1)], fotheories.Lat.find_models(4)[0])
    >>> CS = CongruenceSystem([C1, C2], [2, 3])
    >>> CS.solutions()
    {0}
    """
    
    def __init__(self, cong, elem, sigma=None):
        assert cong and isinstance(cong, list)
        assert elem and isinstance(elem, list)
        assert len(cong) == len(elem)
        for tita in cong:
            assert tita.model == cong[0].model and isinstance(tita, Congruence)
        for x in elem:
            assert x in cong[0].model.universe
        self.model = cong[0].model
        self.cong = cong
        self.elem = elem
        if sigma:
            assert is_system(cong, elem, lambda x, y: sup_proj(sigma, x, y))
        else:
            assert is_system(cong, elem)
        self.sigma = sigma
    
    def solutions(self):
        sol = self.cong[0].equiv_class(self.elem[0])
        for i in list(range(len(self.cong))):
            if i != 0:
                sol = sol & self.cong[i].equiv_class(self.elem[i])
        return sol
    
    def has_solution(self):
        if len(self.solutions()) == 0:
            return False
        else:
            return True


def maxcon(model):
    univ = [(x, y) for x in model.universe for y in model.universe]
    return Congruence(univ, model)


def mincon(model):
    univ = [(x, x) for x in model.universe]
    return Congruence(univ, model)


def sup_proj(sigma, x, y):
    """
    Devuelve el supremo entre x e y dentro del reticulado de congruencias
    generado por el conjunto sigma
    """
    xy_up = {c for c in sigma if (set(x.d) <= set(c.d) and set(y.d) <= set(c.d))}
    e = maxcon(x.model)
    for r in xy_up:
        e = e & r
    return e


def empty_intersections(con_list):
    l = []
    for c in con_list:
        l.append(sorted(c.classes(), key=len))
    for t in product(*l):
        r = frozenset.intersection(*t)
        if not r:
            yield t


def find_system(sigma, con_list, tuple_of_sets):
    model = list(sigma)[0].model
    joins = dict()
    for i, j in combinations(range(len(con_list)), r=2):
        joins[(i, j)] = sup_proj(sigma, con_list[i], con_list[j])
    
    to_minion = "MINION 3\n\n"
    to_minion += "**VARIABLES**\n"
    to_minion += "DISCRETE x[%s]{0..%s}\n\n" % (len(con_list), len(model) - 1)
    to_minion += "**TUPLELIST**\n"
    for i, s in enumerate(tuple_of_sets):
        to_minion += "D%s %s 1\n" % (i, len(s))
        for a in s:
            to_minion += "%s\n" % a
        to_minion += "\n"
    for (i, j) in joins:
        to_minion += "J%sJ%s %s 2\n" % (i, j, len(joins[(i, j)].d))
        for a, b in joins[(i, j)].d:
            to_minion += "%s %s\n" % (a, b)
        to_minion += "\n"
    to_minion += "**CONSTRAINTS**\n"
    for i in range(len(tuple_of_sets)):
        to_minion += "table([x[%s]],D%s)\n" % (i, i)
    for (i, j) in joins:
        to_minion += "table([x[%s],x[%s]],J%sJ%s)\n" % (i, j, i, j)
    to_minion += "\n\n"
    to_minion += "**EOF**"
    return MinionSolLimpio(to_minion, allsols=False)


def find_system_output(sigma, con_list, e_i):
    model = list(sigma)[0].model
    joins = dict()
    for i, j in combinations(range(len(con_list)), r=2):
        joins[(i, j)] = con_list[i] | con_list[j]
    
    to_minion = "MINION 3\n\n"
    to_minion += "**VARIABLES**\n"
    to_minion += "DISCRETE x[%s]{0..%s}\n\n" % (len(con_list), len(model) - 1)
    to_minion += "**TUPLELIST**\n"
    
    to_minion2 = ""
    for (i, j) in joins:
        to_minion2 += "J%sJ%s %s 2\n" % (i, j, len(joins[(i, j)].d))
        for a, b in joins[(i, j)].d:
            to_minion2 += "%s %s\n" % (a, b)
        to_minion2 += "\n"
    to_minion2 += "**CONSTRAINTS**\n"
    
    to_minion4 = ""
    for (i, j) in joins:
        to_minion4 += "table([x[%s],x[%s]],J%sJ%s)\n" % (i, j, i, j)
    to_minion4 += "\n\n"
    to_minion4 += "**EOF**"
    
    for tuple_of_sets in e_i:
        to_minion1 = ""
        to_minion3 = ""
        for i, s in enumerate(tuple_of_sets):
            to_minion1 += "D%s 1 1\n" % i
            to_minion1 += "%s\n" % next(iter(s))
            to_minion1 += "\n"
            to_minion3 += "table([x[%s]],D%s)\n" % (i, i)
        
        yield MinionSolLimpio(to_minion + to_minion1 + to_minion2 + to_minion3 + to_minion4, allsols=False)


def not_all_min_systems_solvable(sigma):
    sigma_m = minorice(sigma)
    e_i = empty_intersections(sigma_m)
    for i, solution in enumerate(find_system_output(sigma, sigma_m, e_i)):
        if i % 100 == 0:
            print("\t%s" % i)
        if solution:
            print("\t%s" % i)
            return solution
    return False


def minimal_systems(sigma):
    model = list(sigma)[0].model
    sigma_m = minorice(sigma)
    joins = dict()
    for i, j in combinations(range(len(sigma_m)), r=2):
        joins[(i, j)] = sup_proj(sigma, sigma_m[i], sigma_m[j])
    
    to_minion = "MINION 3\n\n"
    to_minion += "**VARIABLES**\n"
    to_minion += "DISCRETE x[%s]{0..%s}\n\n" % (len(sigma_m), len(model) - 1)
    to_minion += "**TUPLELIST**\n"
    for (i, j) in joins:
        to_minion += "J%sJ%s %s 2\n" % (i, j, len(joins[(i, j)].d))
        for a, b in joins[(i, j)].d:
            to_minion += "%s %s\n" % (a, b)
        to_minion += "\n"
    to_minion += "**CONSTRAINTS**\n"
    for (i, j) in joins:
        to_minion += "table([x[%s],x[%s]],J%sJ%s)\n" % (i, j, i, j)
    to_minion += "\n\n"
    to_minion += "**EOF**"
    return MinionSolLimpio(to_minion)


def is_system(cong, elem, sup=lambda x, y: x | y):
    for i in list(range(len(cong))):
        for j in list(range(len(cong))):
            if i != j:
                if [elem[i], elem[j]] not in sup(cong[i], cong[j]):
                    return False
    return True


def minorice(sigma):
    """
    Dado un conjunto de congruecias devuelve el conjunto minimo
    {tita: tita in sigma tal que no existe delta in sigma con delta contenido en sigma}
    """
    rem = []
    sigma = list(set(sigma))
    for i in list(range(len(sigma))):
        if i not in rem:
            for j in range(i + 1, len(sigma)):
                if sigma[i] & sigma[j] == sigma[j]:
                    rem.append(i)
                    break
                elif sigma[i] & sigma[j] == sigma[i]:
                    rem.append(j)
    return [x for x in sigma if sigma.index(x) not in rem]


def subspectra(congruences):
    model = list(congruences)[0].model
    A_old = [[i] for i in range(len(congruences))]
    Adelta_old = []
    while A_old or Adelta_old:
        A = []
        Adelta = []
        for cs in A_old:
            for other in range(cs[-1] + 1, len(congruences)):
                if all(not congruences[other] < congruences[c] and not congruences[c] < congruences[other] for c in cs):
                    new = cs + [other]
                    
                    if reduce(lambda x, y: x & y, [congruences[i] for i in new], ) == mincon(model):
                        
                        Adelta.append(new)
                        yield [congruences[i] for i in new]
                    else:
                        A.append(new)
        for cs in Adelta_old:
            for other in range(cs[-1] + 1, len(congruences)):
                if all(not congruences[other] < congruences[c] and not congruences[c] < congruences[other] for c in cs):
                    new = cs + [other]
                    Adelta.append(new)
                    yield [congruences[i] for i in new]
        A_old = A
        Adelta_old = Adelta


def antichain(sigma, i, deltas):
    pass


def extend_const_sys(sigma, h, i):
    pass


def extend_non_sol_sys(sigma, h, i, vector):
    pass


def all_subspectra(A, sigma, all=True):
    n = len(sigma)
    H_old = [([], maxcon(A), [])]
    H_new = H_old
    solutions = []
    for i in range(n):
        for (deltas, intersection, vectors) in H_old:
            if antichain(sigma, i, deltas):
                intersection_new = intersection & sigma[i]
                deltas_new = deltas.append(i)
                vectors_new = extend_const_sys(sigma, deltas, i)
                for vector in vectors:
                    vectors_new = vectors_new + extend_non_sol_sys(sigma, deltas, i, vector)
                new_tuple = (deltas_new, intersection_new, vectors_new)
                if intersection == mincon(A) and vectors == []:
                    if all == False:
                        return new_tuple
                    else:
                        solutions.append(new_tuple)
                H_new.append(new_tuple)
    H_old = H_new
    return solutions


def all_global_desc(A, F, all=True):
    sigma = A.congruences_in(F)
    return all_subspectra(A, sigma, all)


if __name__ == "__main__":
    import doctest
    
    doctest.testmod()
"""
d = examples.cadena2sl
t = examples.cadena3sl
carpa = examples.carpasl
c = examples.cascosl
sigma = c.congruences_in([d,t,carpa])
functions.congruence.all_min_systems_solvable(sigma)
"""