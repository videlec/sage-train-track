r"""
Free group of finite rank.
"""
#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
# 
#  Distributed under the terms of the GNU General Public License (GPL) 
#                  http://www.gnu.org/licenses/ 
#***************************************************************************** 
from sage.combinat.words.alphabet import build_alphabet
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.parent import Parent
from sage.groups.group import Group
from sage.categories.groups import Groups
from sage.categories.infinite_enumerated_sets import InfiniteEnumeratedSets
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.sets.finite_enumerated_set import FiniteEnumeratedSet

from inverse_alphabet import build_alphabet_with_inverses
from free_group_word import FreeGroupWord
class FreeGroup(UniqueRepresentation, Group):
    """
    Free group of finite rank.

    EXAMPLES::

        sage: A=AlphabetWithInverses(['a','b'])
        sage: FreeGroup(A)
        Free group over ['a', 'b']

        sage: FreeGroup(3)
        Free group over ['a', 'b', 'c']

        sage: A=AlphabetWithInverses(2,type='x0')
        sage: FreeGroup(A)
        Free group over ['x0', 'x1']

    AUTHORS: 
 
        - Thierry Coulbois (2013-05-16): beta.0 version 
    """
    Element = FreeGroupWord

    @staticmethod
    def __classcall__(cls, *data, **kwds):
        pos, neg = build_alphabet_with_inverses(*data, **kwds)
        return super(FreeGroup, cls).__classcall__(cls, pos, neg)

    def __init__(self, pos, neg=None):
        r"""
        INPUT:

        - ``pos`` - the alphabet of positive letters

        - ``neg`` - the alphabet of negative letters

        - ``bij`` - bijection between positive and negative letters
        """
        Group.__init__(self, category=(Groups(),InfiniteEnumeratedSets()))
        self._pos = pos
        self._neg = neg

        self._invert = {}
        self._invert.update(zip(pos,neg))
        self._invert.update(zip(neg,pos))
        self._alphabet = build_alphabet(pos.list() + neg.list())
        
    def gens(self):
        r"""
        Return the canonical generating set for this free group.
        """
        return tuple(self([letter],check=False) for letter in self.positive_letters())

    def __iter__(self):
        r"""
        TESTS::

            sage: it = iter(FreeGroup('ab'))
            sage: [it.next() for _ in xrange(25)]
            [THE_EMPTY_WORD,
             a,
             b,
             A,
             B,
             aa,
             ...
             aBa,
             aBA]
             sage: it.next()
             aBB
        """
        n = 0
        while True:
            for w in self.subset(n): yield w
            n += 1

    def inverse_letter(self, a):
        r"""
        Return the inverse of the letter ``a`` or raise a ValueError.

        EXAMPLES::

            sage: F = FreeGroup('abc','XYZ')
            sage: F.inverse_letter('b')
            'Y'
            sage: F.inverse_letter('Z')
            'c'
        """
        try:
            return self._invert[a]
        except StandardError:
            raise ValueError("the letter %s is not in the alphabet"%a)

    def one(self):
        r"""
        Return the identity element in self.

        EXAMPLES::

            sage: F = FreeGroup('abc')
            sage: F.one()
            THE_EMPTY_WORD
        """
        return self([])

    empty_word = one

    def alphabet(self):
        r"""
        Return the set of words of length 1.

        EXAMPLES::

            sage: F = FreeGroup('abc')
            sage: F.alphabet()
            {'a', 'b', 'c', 'A', 'B', 'C'}
        """
        return self._alphabet

    def positive_letters(self):
        r"""
        Return the set of positive letters

        EXAMPLES::

            sage: F = FreeGroup('abc')
            sage: F.positive_letters()
            {'a', 'b', 'c'}
        """
        return self._pos

    def negative_letters(self):
        r"""
        Return the set of negative letters

        EXAMPLES::

            sage: F = FreeGroup('abc')
            sage: F.negative_letters()
            {'A', 'B', 'C'}
        """
        return self._neg

    def subset(self, n):
        r"""
        Return the set of elements of given length.

        EXAMPLES::

            sage: F = FreeGroup('ab')
            sage: F.subset(2)
            Words of length 4 in Free group over {'a', 'b'}
        """
        try:
            n = n.__index__()
        except StandardError:
            raise TypeError("n should be integer")
        return FreeGroup_n(self, n)

    def _repr_(self):
        """
        String representation for free group

        TESTS::

            sage: FreeGroup('ab')      # indirect doctest
            Free group over {'a', 'b'}
        """
        return "Free group over %s"%self.positive_letters()

    def _element_constructor_(self, data=None, check=True):
        r"""
        Build an element of the free group,

        If ``check`` is True, then check that the validity of letters and that
        the word is reduced.

        TESTS::

            sage: F = FreeGroup('ab')
            sage: F('abAb')              # indirect doctest
            abAb
            sage: F('abAaBbBA')          # indirect doctest
            THE_EMPTY_WORD
            sage: F('aaac')              # indirect doctest
            Traceback (most recent call last):
            ...
            ValueError: the letter c is not in the alphabet
        """
        if data is None:
            data=[]
        return self.element_class(self, data, check)

    #TODO
    def identity_automorphism(self):
        """
        Identity automorphism of ``self``.
        """
        morph=dict((a,self([a])) for a in self.positive_letters())
        return FreeGroupAutomorphism(morph,group=self)

    #TODO
    def dehn_twist(self,a,b,on_left=False):
        """
        Dehn twist automorphism of ``self``.

        if ``on_left`` is ``False``: ``a -> ab``
        if ``on_left`` is ``True``: ``a -> ba``

        EXAMPLES

        sage: F=FreeGroup(3)
        sage: F.dehnt_twist('a','c')
        
        a->ac, b->b, c->c

        sage: F.dehn_twist('A','c')
        a->Ca,b->b,c->c

        """
        A = self.alphabet()

        if a not in A:
            raise ValueError, "Letter %s not in alphabet" %str(a)
        if b not in A:
            raise ValueError, "Letter %s not in alphabet" %str(b)
        if a == b:
            raise ValueError, "Letter a=%s should be different from b=%s" %(str(a),str(b))
        if A.are_inverse(a,b):
            raise ValueError, "Letter a=%s should be different from the inverse of b=%s" %(str(a),str(b))

        morphism = dict((letter,self([letter])) for letter in self.positive_letters())

        if A.is_positive_letter(a):
            if on_left:
                morphism[a] = self([b,a])
            else:
                morphism[a] = self([a,b])
        else:
            a = A.inverse_letter(a)
            b = A.inverse_letter(b)
            if on_left:
                morphism[a] = self([a,b])
            else:
                morphism[a] = self([b,a])

        return FreeGroupAutomorphism(morphism,group=self)

    #TODO
    def random_automorphism(self,length=1):
        """
        Random automorphism of ``self``.

        The output is a random word of given ``length`` on the set of Dehn twists.
        """

        if length==0: return self.identity_automorphism()

        A=self.alphabet()
        a=A.random_letter()
        b=A.random_letter([a,A.inverse_letter(a)])
        result=self.dehn_twist(a,b)
        for i in xrange(length-1):
            new_a=A.random_letter()
            if new_a==a:
                b=A.random_letter([a,A.inverse_letter(a),A.inverse_letter(b)])  
            else:
                a=new_a
                b=A.random_letter([a,A.inverse_letter(a)])  
            result=result*self.dehn_twist(a,b)
        return result

    #TODO
    def _surface_dehn_twist_e(self,i):
        
        a=self._alphabet[2*i]
        b=self._alphabet[2*i+1]
        return self.dehn_twist(a,b,True)

    #TODO
    def _surface_dehn_twist_c(self,i):
        A=self._alphabet
        result=dict((a,self([a])) for a in A.positive_letters())
        result[A[2*i+1]]=self([A[2*i+2],A.inverse_letter(A[2*i]),A[2*i+1]])
        result[A[2*i+3]]=self([A[2*i+3],A[2*i],A.inverse_letter(A[2*i+2])])

        return FreeGroupAutomorphism(result,group=self)

    #TODO
    def _surface_dehn_twist_m(self,i):
        A=self._alphabet
        result={}
        for j in xrange(2*i+1):
            result[A[j]]=self([A[j]])
        a=A[2*i]

        result[A[2*i+1]]=self([a,A[2*i+1]])
        aa=A.inverse_letter(a)
        for j in xrange(2*i+2,len(A)):
            result[A[j]]=self([a,A[j],aa])
        return FreeGroupAutomorphism(result,group=self)        

    #TODO
    def surface_dehn_twist(self,k):
        """
        Dehn twist of the surface (with one boundary component) with
        fundamental group ``self``.

        The surface is assumed to have genus g and 1 boundary
        component. The fundamental group has rank 2g, thus ``self`` is
        assumed to be of even rank. 

        ``k`` is an integer 0<=k<3g-1.

        MCG(S_{g,1}) is generated by the Dehn twist along
        the curves: 

        - g equators e_i, 
        
        - g meridian m_i 
        
        - g-1 circles c_i around two consecutive 'holes'.  

        for 0<=k<g returns the Dehn twist along e_i with i=k

        for g<=k<2g returns the Dehn twist along m_i with i=k-g

        for 2g<=k<3g-1 returns the Dehn twist along c_i with i=k-2g

        The fundamental group has 2g generators. We fix the base point
        on the boundary. The generators are:

        - g x_i that turns around the i-th hole

        - g y_i that goes inside the i-th hole

        T_{e_i}: x_j-> x_j, x_i->y_ix_i, y_j->y_j

        T_{m_i}: x_j->x_j, y_j->y_j, j<i
                 x_i->x_i, y_i->x_iy_i
                 x_j->x_ix_jx_i\inv, y_j->x_iy_jx_i\inv

        T_{c_i}: x_j->x_j, y_j->y_j, y_i->x_{i+1}x_i\inv y_i, y_{i+1}->y_{i+1}x_{i+1}x_i\inv

        WARNING:

        ``self`` is assumed to be of even rank.

        """
        assert len(self._alphabet)%2==0

        g=len(self._alphabet)/2
        if (0<=k and k<g): result=self._surface_dehn_twist_e(k)
        elif (g<=k and k<2*g): result=self._surface_dehn_twist_m(k-g)
        elif (2*g<=k and k<3*g-1): result=self._surface_dehn_twist_c(k-2*g)
       
        return result

    #TODO
    def random_mapping_class(self,n=1):
        """
        Random mapping class of length (as a product of
        generating dehn twists) at most ``n``. `

        WARNING:

        The rank of ``self` is assumed to be even.
        """

        assert len(self._alphabet)%2==0


        if n==0:
            return self.identity_automorphism()

        r=3*len(self._alphabet)/2-2
        i=randint(0,r)
        j=randint(0,1)
        if j==0:
            result=self.surface_dehn_twist(i)
        else:
            result=self.surface_dehn_twist(i).inverse()
        for ii in xrange(n-1):
            l=randint(0,1)
            if j==l:
                i=randint(0,r)
            else:
                k=randint(0,r-1)
                if k>=i: i=k+1
                j=l
            if j==0:
                result=result*self.surface_dehn_twist(i)
            else:
                result=result*self.surface_dehn_twist(i).inverse()
        return result

   
    #TODO
    def braid_automorphism(self,i,inverse=False):
        """
        Automorphism of ``self`` which corresponds to the generator
        sigma_i of the braid group.

        sigma_i: a_i -> a_i a_{i+1} a_i^{-1}
                 a_j -> a_j, for j!=i

        We assume 0<i<n, where n is the rank of ``self``. 

        If ``inverse`` is True returns the inverse of sigma_i.

        """
        A=self._alphabet
        result=dict((a,self([a])) for a in A.positive_letters())
        if not inverse:
            a=A[i-1]
            result[a]=self([a,A[i],A.inverse_letter(a)])
            result[A[i]]=self([a])
        else:
            a=A[i]
            result[a]=self([A.inverse_letter(a),A[i-1],a])
            result[A[i-1]]=self(a)
            
        return FreeGroupAutomorphism(result,group=self)

    #TODO
    def random_braid(self,n=1):
        """
        A random braid automorphism of ``self`` of length at most
        ``n``.
        """
        A=self._alphabet
        if n==0:
            return self.identity_automorphism()
        i=randint(1,len(A)-1)
        j=randint(0,1)
        result=self.braid_automorphism(i,j!=0)
        for ii in xrange(n-1):
            l=randint(0,1)
            if l==j: i=randint(1,len(A)-1)
            else:
                k=randint(1,len(A)-2)
                if j<=k: i=k+1
            result=result*self.braid_automorphism(i,j)
        return result


class FreeGroup_n(UniqueRepresentation, Parent):
    r"""
    The set of words of fixed length in a free group.

    EXAMPLES::

        sage: F = FreeGroup('ab')
        sage: F0 = F.subset(0)
        sage: F1 = F.subset(1)
        sage: F2 = F.subset(2)

        sage: F1.list()
        [a, b, A, B]
        sage: F2.list()
        [aa, ab, aB, ba, bb, bA, Ab, AA, AB, Ba, BA, BB]
        sage: F3.list()
        [aaa,
         aab,
         aaB,
         aba,
         abb,
         abA,
         aBa,
         ...
         BBB]

    Standard operations with finite enumerated sets can be performed::

        sage: F3.rank(F('aBa'))
        6
        sage: F3.unrank(6)
        aBa
        sage: F3.last()
        BBB
    """
    def __init__(self, free_group, n):
        r"""
        INPUT:

        - ``free_group`` - a free group

        - ``n`` - a non negative integer

        TESTS::

            sage: TestSuite(FreeGroup('ab').subset(0)).run()
            sage: TestSuite(FreeGroup('abc').subset(4)).run()
        """
        Parent.__init__(self, facade=free_group, category=FiniteEnumeratedSets())
        self._free_group = free_group
        self._n = n

    def an_element(self):
        r"""
        Return an element in that set.

        EXAMPLES::

            sage: F = FreeGroup('abcd')
            sage: F4 = F.subset(4)
            sage: F4.an_element()
            aaaa
        """
        alphabet = self._free_group.alphabet()
        if not alphabet:
            from sage.categories.sets_cat import EmptySetError
            raise EmptySetError
        return self._free_group([alphabet.an_element()] * self._n, check=False)

    def first(self):
        r"""
        Return the first element in that set.

        EXAMPLES::

            sage: F = FreeGroup('abcd')
            sage: F4 = F.subset(4)
            sage: F4.first()
            aaaa
        """
        alphabet = self._free_group.alphabet()
        if not alphabet:
            from sage.categories.sets_cat import EmptySetError
            raise EmptySetError
        return self._free_group([alphabet.first()] * self._n, check=False)

    def last(self):
        r"""
        Return the last element in that set.

        EXAMPLES::

            sage: F = FreeGroup('abcd')
            sage: F4 = F.subset(4)
            sage: F4.last()
            DDDD
        """
        alphabet = self._free_group.alphabet()
        if not alphabet:
            from sage.categories.sets_cat import EmptySetError
            raise EmptySetError
        return self._free_group([alphabet.last()] * self._n, check=False)

    def cardinality(self):
        r"""
        Return the cardinality of self.

        EXAMPLES::

            sage: F = FreeGroup('ab')
            sage: F.subset(1).cardinality()
            4
            sage: F.subset(2).cardinality()
            12
            sage: F.subset(3).cardinality()
            36
        """
        if self._n == 0:
            return 1

        d = self._free_group.alphabet().cardinality()
        if self._n == 1:
            return d
        return d * (d-1)**(self._n-1)

    def random_element(self):
        r"""
        Return a random element in self.

        EXAMPLES::

            sage: F = FreeGroup(3)
            sage: F.subset(3).random_element()  # random
            aBa
        """
        if self._n == 0:
            return self._free_group.one()

        alphabet = self._free_group.alphabet().list()
        D = len(alphabet)
        d = D/2
        from sage.misc.prandom import randint
        j = randint(0,D-1)
        data = [alphabet[j]]
        
        while len(data) != self._n:
            if j < d:
                i = j + d
            else:
                i = j - d
            j = randint(0,D-2)
            if j >= i:
                j += 1
            data.append(alphabet[j])
        
        return self(data, check=False)

    def _repr_(self):
        r"""
        String representation.

        TESTS::

            sage: FreeGroup('abc').subset(5)
            Words of length 5 in Free group over {a, b, c}
        """
        return "Words of length %s in %s"%(self._n,self._free_group)

    def _element_constructor_(self, data, check=True):
        r"""
        TESTS::

            sage: F = FreeGroup('abc')
            sage: G = F.subset(4)
            sage: G('abaa')
            abaa
            sage: G('Aa')
            Traceback (most recent call last):
            ...
            ValueError: can not build a word of length 4 from given data
        """
        w = self._free_group(data,check)
        if check:
            if len(w) != self._n:
                raise ValueError("can not build a word of length %s from given data"%self._n)
        return w

    def __iter__(self):
        r"""
        Lexicographic iterator.
        """
        F = self._free_group
        n = self._n

        if n == 0:
            yield F.one()
            return

        alphabet = F.alphabet().list()
        D = len(alphabet)
        d = len(alphabet) / 2
        last_pos = alphabet[d]

        data = []
        int_word = [] # the list of next letters
        i = -1
        while True:
            if i == d and len(data) != n:
                data.append(alphabet[1])
                int_word.append(2)
            while len(data) != n:
                data.append(alphabet[0])
                int_word.append(1)

            yield F(data[:], check=False)

            i = int_word.pop()
            while int_word and (i == D or (i == D-1 and int_word and int_word[-1] == d)):
                data.pop()
                i = int_word.pop()

            if int_word:
                if int_word[-1] + d - 1 == i or int_word[-1] - d - 1 == i:
                    i += 1
            elif i == D:
                return
            data[-1] = alphabet[i]
            int_word.append(i+1)
