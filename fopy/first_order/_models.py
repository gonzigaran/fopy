# -*- coding: utf-8 -*-
#!/usr/bin/env python

from itertools import product
from fopy.misc.misc import indent


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

class FO_Submodel(FO_Model):

    """
    Submodelos de algun tipo de primer orden.
    """

    def __init__(self, fo_type, universe, operations, relations, supermodel):
        super(FO_Submodel, self).__init__(
            fo_type, universe, operations, relations)
        self.supermodel = supermodel

    def __repr__(self):
        result = "FO_Submodel(\n"
        result += indent(repr(self.fo_type) + ",\n")
        result += indent(repr(self.universe) + ",\n")
        result += indent(repr(self.operations) + ",\n")
        result += indent(repr(self.relations) + ",\n")
        result += indent("supermodel= " + repr(self.supermodel) + "\n")
        return result + ")"

    def natural_embedding(self):
        """
        Genera el Embedding natural entre el submodelo y el modelo
        """
        d = {(x,): x for x in self.universe}
        return Embedding(d, self, self.supermodel, self.fo_type)

    def is_subdirect(self):
        """
        Dado un submodelo de un producto, decide si es un producto subdirecto o no
        """
        if isinstance(self.supermodel, FO_Product):
            for i in self.supermodel.indices():
                if not set((self.supermodel.projection(i).composition(self.natural_embedding())).image_model().universe) == set(self.supermodel.factors[i].universe):
                    return False
            return True
        return False


class FO_Product(FO_Model):

    def __init__(self, factors):
        """
        Toma una lista de factores
        """
        # TODO falta un armar las operaciones y relaciones
        for f in factors:
            if isinstance(f,FO_Product):
                factors.remove(f)
                factors+=f.factors
        self.factors = factors

        fo_type = factors[0].fo_type
        if any(f.fo_type != fo_type for f in factors):
            raise ValueError("Factors must be all from same fo_type")

        d_universe = list(product(*[f.universe for f in factors]))

        operations = {}
        for op in fo_type.operations:
            if fo_type.operations[op] == 0:
                operations[op] = FO_Constant(tuple([f.operations[op]() for f in factors]))
            else:
                operations[op] = FO_Operation_Product([f.operations[op] for f in factors],[f.universe for f in factors])

        relations = {}
        for rel in fo_type.relations:
            relations[rel] = FO_Relation_Product([f.relations[rel] for f in factors],[f.universe for f in factors])

        super(FO_Product, self).__init__(fo_type,
                                         d_universe,
                                         operations,
                                         relations)

    def projection(self, i):
        """
        Genera el morfismo que es la proyección en la coordenada i
        """
        assert i in self.indices()
        d = {(x,): x[i] for x in self.universe}
        return Homomorphism(d, self, self.factors[i], self.fo_type, surj=True)

    def indices(self):
        return list(range(len(self.factors)))


class FO_SubdirectProduct(FO_Submodel):

    """
    Producto Subdirecto

    >>> from definability.examples.examples import *
    >>> M2=FO_Model(tiporetacotado, [0,1], {'^': FO_Operation({(0,0):0,(0,1): 0,(1,0): 0,(1,1): 1}),'v': FO_Operation({(0,0):0,(0,1): 1,(1,0): 1,(1,1): 1}),'Max': FO_Constant(1),'Min': FO_Constant(0)}, {})
    >>> P=M2*M2*M2
    >>> FO_SubdirectProduct([(1,1,1), (0,0,0), (0,1,1)], P).is_global()
    False
    >>> FO_SubdirectProduct([(1,1,1), (0,0,0), (0,1,1), (1,0,0)], P).is_global()
    True
    """

    def __init__(self, universe, supermodel):
        assert isinstance(supermodel, FO_Product)
        super(FO_SubdirectProduct, self).__init__(
                supermodel.fo_type,
                universe,
                {op: supermodel.operations[op].restrict(universe) for op in supermodel.operations},
                {rel: supermodel.relations[rel].restrict(universe) for rel in supermodel.relations},
                supermodel)
        assert self.is_subdirect()

    def __repr__(self):
        result = "FO_SubdirectProduct(\n"
        result += indent(repr(self.fo_type) + ",\n")
        result += indent(repr(self.universe) + ",\n")
        result += indent(repr(self.operations) + ",\n")
        result += indent(repr(self.relations) + ",\n")
        result += indent("Product= " + repr(self.supermodel) + "\n")
        return result + ")"

    def tita(self, i):
        """
        Congruencia de la forma tita(i) = {(x,y) in A^2 : x(i) = y(i)}
        """
        assert i in self.supermodel.indices()
        return (self.supermodel.projection(i).composition(self.natural_embedding())).kernel()

    def sigma(self):
        """
        sigma = {tita(i)}
        """
        result = []
        for i in self.supermodel.indices():
            result.append(self.tita(i))
        return result

    def is_global(self):
        """
        Determina si el producto subdirecto es global o no
        """
        sigma = self.sigma()
        sigma_m = minorice(sigma)
        n = len(sigma_m)
        for xs in list(product(*[self.universe for i in list(range(n))])):
            if is_system(sigma_m, xs, lambda x, y: sup_proj(sigma, x, y)):
                CS = CongruenceSystem(sigma_m, list(xs), sigma)
                if not CS.has_solution():
                    return False
        return True


class FO_Quotient(FO_Model):

    """
    Modelo Cociente
    Dado un algebra y una congruencia, devuelve el álgebra cociente
    """

    def __init__(self, supermodel, congruence):
        assert supermodel.fo_type.relations == {}
        uni = list(supermodel.universe)
        elim = []
        n = len(uni)
        for i in range(n):
            if uni[i] not in elim:
                for j in range(i + 1, n):
                    if [uni[i], uni[j]] in congruence:
                        elim.append(uni[j])
        for i in elim:
            uni.remove(i)
        operations = {}
        for op in supermodel.operations:
            ope = supermodel.operations[op].restrict(uni)
            d = {}
            if supermodel.operations[op].arity() != 0:
                for i in list(ope.domain()):
                    if not ope(*i) in uni:
                        for j in uni:
                            if [ope(*i), j] in congruence:
                                d[i] = j
                                break
                    else:
                        d[i] = ope(*i)
                operations[op] = FO_Operation(d, uni, ope.arity())
            else:
                if not ope() in uni:
                    for j in uni:
                        if [ope(), j] in congruence:
                            operations[op] = FO_Constant(j)
                else:
                    operations[op] = ope
        super(FO_Quotient, self).__init__(
            supermodel.fo_type, uni, operations, {})
        self.congruence = congruence
        self.supermodel = supermodel

    def natural_map(self):
        """
        Devuelve el mapa natural entre el álgebra y el cociente
        """
        d = {}
        for i in self.supermodel.universe:
            for j in self.universe:
                if [i, j] in self.congruence:
                    d[(i,)] = j
                    break
        return Homomorphism(d, self.supermodel, self, self.fo_type, surj=True)

    def __repr__(self):
        result = "FO_Quotient(\n"
        result += indent(repr(self.fo_type) + ",\n")
        result += indent(repr(self.universe) + ",\n")
        result += indent(repr(self.operations) + ",\n")
        result += indent(repr(self.relations) + ",\n")
        result += indent("congruence= " + repr(self.congruence) + "\n")
        return result + ")"
