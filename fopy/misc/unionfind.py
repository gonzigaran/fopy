from collections import defaultdict


class UnionFind(object):
    """
    Union Find data structure to compute partitions.
    """
    
    def __init__(self):
        '''
        Create an empty union find data structure.
        '''
        self.num_weights = {}
        self.parent_pointers = {}
        self.num_to_objects = {}
        self.objects_to_num = {}
    
    def insert_objects(self, objects):
        '''
        Insert a sequence of objects into the structure.  All must be Python hashable.
        '''
        for object in objects:
            self.find(object)
    
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
            self.num_weights[on1] = w1 + w2
            del self.num_weights[on2]
            self.parent_pointers[on2] = on1
    
    def to_list(self):
        """
        Returns list of lists
        """
        result = defaultdict(list)
        for key, value in self.parent_pointers.items():
            result[value].append(self.num_to_objects[key])
        return list(result.values())
    
    def __repr__(self):
        '''
        Included for testing purposes only.
        All information needed from the union find data structure can be attained
        using find.
        '''
        sets = {}
        for i in range(len(self.objects_to_num)):
            sets[i] = []
        for i in self.objects_to_num:
            sets[self.objects_to_num[self.find(i)]].append(i)
        out = []
        for i in sets.values():
            if i:
                out.append(repr(i))
        return ', '.join(out)


class CardinalBlock(object):
    def __init__(self, value):
        self.value = value


class Partition(object):
    def __init__(self, iter_of_iter=()):
        self.v = dict()
        self.extend(iter_of_iter)
    
    def __call__(self, a, b):
        return self.root(a) == self.root(b)
    
    def to_list_of_pairs(self):
        result = set()
        for a in self.v:
            for b in self.v:
                if self(a, b):
                    result.add((a, b))
        return result
    
    def copy(self):
        result = Partition()
        result.v = self.v.copy()
        return result
    
    def extend(self, ls):
        """
        Extiende la particion con una lista de listas
        :param list:
        :return:
        """
        for l in ls:
            for e in l:
                self.add_element(e)
                self.join_blocks(e, l[0])
    
    def add_element(self, e):
        if e not in self.v:
            self.v[e] = CardinalBlock(-1)
    
    def root(self, e):
        """
        Representante de la clase de equivalencia de e
        """
        # TODO NO DEBERIA SER RECURSIVO
        j = self.v[e]
        if isinstance(j, CardinalBlock):
            result = e
        else:
            self.v[e] = self.root(j)
            result = self.v[e]
        return result
    
    def join_blocks(self, i, j):
        
        ri = self.root(i)
        rj = self.root(j)
        if ri != rj:
            si = self.v[ri].value
            sj = self.v[rj].value
            if si < sj:
                self.v[i] = rj
                self.v[j] = CardinalBlock(si + sj)
            else:
                self.v[j] = ri
                self.v[i] = CardinalBlock(si + sj)
    
    def to_list(self):
        result = defaultdict(list)
        for e in self.v:
            result[self.root(e)].append(e)
        return list(result.values())
    
    def __repr__(self):
        return repr(self.to_list())
    
    def meet(self, other):
        """

        :type other: Partition
        """
        result = Partition()
        ht = dict()
        for e in self.v:
            r1 = self.root(e)
            r2 = other.root(e)
            if (r1, r2) in ht:
                r = ht[r1, r2]
                result.v[r] = CardinalBlock(result.v[r].value + 1)
                result.v[e] = r
            else:
                ht[(r1, r2)] = e
                result.v[e] = CardinalBlock(-1)
        return result
    
    def join(self, other):
        """
        The join(U, V)
            for each i which is not a root of U
                join-blocks(i, U[i], V)
        :type other: Partition
        """
        result = other.copy()
        for e in self.v:
            if not isinstance(self.v[e], CardinalBlock): # not a root
                result.join_blocks(e, self.root(e))
        return result
