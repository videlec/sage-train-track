#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
# 
#  Distributed under the terms of the GNU General Public License (GPL) 
#                  http://www.gnu.org/licenses/ 
#***************************************************************************** 
from sage.combinat.words.abstract_word import Word_class
from sage.structure.element import MonoidElement

# right now it is not possible to inherit from both Element and FiniteWord_list
# (they both defined an attribute Parent). But at least it is possible to
# inherit from FiniteWord.
# to be tested: powers, etc

# inheritance from FiniteWord_class or Word_class is a mess because of concatenation

class FreeGroupWord(MonoidElement):
    """
    Element of a free group of finite rank.

    EXAMPLES::

        sage: F = FreeGroup(3)
        sage: w = F('aba')
        aba

    AUTHORS: 
 
    - Thierry Coulbois (2013-05-16): initial version 
    """
    def __init__(self, parent, data, check=False):
        r"""
        INPUT:

        - ``parent`` - a free group

        - ``data`` - the data to be used

        - ``check`` - wether to check the consistency of the input is checked
          (default is ``True`` but it is much faster if ``check`` is set to
          ``False``)
        """
        MonoidElement.__init__(self, parent)
        if check:
            self._data = list(data)
            self._check_alphabet()
            self._reduce()
        else:
            assert isinstance(data, list)
            self._data = data
            
    def _check_alphabet(self):
        r"""
        Check the alphabet of ``self``.

        For internal use only.

        TESTS::

            sage: F = FreeGroup('ab')
            sage: F('abc')
            Traceback (most recent call last):
            ...
            TypeError: the letter c is not in the alphabet
        """
        A = self.parent().alphabet()
        for letter in self._data:
            if letter not in A:
                raise ValueError("the letter %s is not in the alphabet"%letter)
        
    def __iter__(self):
        r"""
        Iterator over the letters of ``self``.

        TESTS::

            sage: F = FreeGroup('ab')
            sage: it = iter(F('abA'))
            sage: it.next()
            'a'
            sage: it.next()
            'b'
            sage: it.next()
            'A'
            sage: it.next()
            Traceback (most recent call last):
            ...
            StopIteration:
        """
        return iter(self._data)

    def __reversed__(self):
        r"""
        Reversed iterator over the letters of ``self``.

        TESTS::

            sage: F = FreeGroup('ab')
            sage: it = reversed(F('abA'))
            sage: it.next()
            'A'
            sage: it.next()
            'b'
            sage: it.next()
            'a'
            sage: it.next()
            Traceback (most recent call last):
            ...
            StopIteration:
        """
        return reversed(self._data)

    def __eq__(self, other):
        r"""
        Equality test.
        """
        return isinstance(other, FreeGroupWord) and self.parent() is other.parent() and self._data == other._data

    def __ne__(self, other):
        return not self.__eq__(other)

    def __cmp__(self, other):
        if not isinstance(other, FreeGroupWord) or self.parent() is not other.parent():
            raise TypeError("can not compare words on different free groups")
        return cmp(self._data, other._data)

    def is_one(self):
        return not bool(self._data)

    def __len__(self):
        r"""
        The length of ``self`` as a Python integer.

        EXAMPLES::

            sage: F = FreeGroup('abcd')
            sage: w = F('aBccDaaC')
            sage: len(w)
            8
            sage: type(len(w))
            <type 'int'>
        """
        return len(self._data)

    def length(self):
        r"""
        The length of ``self`` as a Sage integer.

        EXAMPLES::

            sage: F = FreeGroup('abcd')
            sage: w = F('aBccDaaC')
            sage: w.length()
            8
            sage: type(w.length())
            <type 'sage.rings.integer.Integer'>
        """
        return Integer(len(self))

    def __getitem__(self, i):
        r"""
        Return a letter or a factor of self.

        TESTS::

            sage: F = FreeGroup('ab')
            sage: w = F('abAAbaaBBBabA')
            sage: w[3]
            'A'
            sage: w[1:5]
            bAAb
            sage: w[::-1]
            THE_EMPTY_WORD
        """
        n = len(self._data)
        if isinstance(i, slice):
            if i.step is not None and i.step != 1 and i.step != -1:
                raise ValueError("step can only be 1 or -1")
            start,stop,step = i.indices(n)
            # there is a python bug which prevents from doing l[start:stop:ste]
            #    sage: l = [1,2,3]
            #    sage: l[1:-1:-1]
            #    []
            return self.parent()(self._data[i])

        try:
            i = i.__index__()
        except StandardError:
            raise TypeError("word index must be integer or slice")

        return self._data[i]

    def _reduce(self):
        """
        Reduced the attribute _data of ``self``.
        
        EXAMPLES::
        
            sage: F = FreeGroup('abc')
            sage: w = "abcAab"
            sage: print w," = ",F(w)
            abcAab = abcb
        """
        data = self._data
        f = self.parent().inverse_letter
        
        i = 0
        j = 1
        length = len(data)
        while j < length:
            k = 0
            while i-k >= 0 and j+k < length and f(data[i-k]) == data[j+k]:
                k = k+1
            i = i-k+1
            j = j+k+1
            if j-1 < length:
                data[i] = data[j-1]
            else:
                i = i-1
        del data[i+1:]

    def _repr_(self):
        r"""
        String representation.

        TESTS::

            sage: F = FreeGroup('abc')
            sage: F('aBca')
            aBca
            sage: F('')      # not wonderful
            THE_EMPTY_WORD
        """
        if not self._data:
            return "THE_EMPTY_WORD"
        return ''.join(self._data)

    def _mul_(self, other):
        """
        Reduced product of ``self`` and ``other``.

        WARNING:

        ``self`` and ``other``are assumed to be reduced.

        EXAMPLES::

            sage: F = FreeGroup('abc')
            sage: u = F('abAc')
            sage: v = F('Caa')
            sage: u*v
            aba
        """
        A = self.parent().alphabet()
        i = 0
        f = self.parent().inverse_letter
        while i<len(self) and i<len(other) and f(self[-i-1]) == other[i]:
            i=i+1
        return self.parent()(self._data[:len(self)-i]+other._data[i:], check=False)

    def __invert__(self):
        """
        Inverse of self. 

        TESTS::

            sage: F = FreeGroup('abc')
            sage: u = F('abAc')
            sage: ~u
            CaBA
            sage: (~u * u).is_one()
            True
            sage: (u * ~u).is_one()
            True
        """
        F = self.parent()
        return F(map(F.inverse_letter, reversed(self._data)))

    def common_prefix_length(self, other):
        """
        Return the length of the longest common prefix of ``self`` and
        ``other``.

        EXAMPLES::
        
            sage: F = FreeGroup('abc')
            sage: u = F('aBaa')
            sage: v = F('aBcb')
            sage: u.common_prefix_length(v)
            2
        """
        k=0
        while k<len(u) and k<len(v) and u[k]==v[k]:
            k=k+1
        return k

    def is_prefix(self, other):
        """
        Test if ``self`` is a prefix of ``other``.

        EXAMPLES::
        
            sage: F = FreeGroup('abc')
            sage: u = F("aBaa")
            sage: v = F("aBcb")
            sage: w = F("aBa")
            sage: u.is_prefix(v) or u.is_prefix(w)
            False
            sage: v.is_prefix(u) or v.is_prefix(w)
            False
            sage: w.is_prefix(u)
            True
            sage: u.is_prefix(u) and v.is_prefix(v) and w.is_prefix(w)
            True
        """
        if len(other) < len(self):
            return False
        i = 0
        while i < len(self) and self[i] == other[i]:
            i += 1
        return i == len(self)

    def has_prefix(self, other):
        r"""
        Test if ``self`` has ``other`` as prefix.

        EXAMPLES::

            sage: F = FreeGroup('abc')
            sage: u = F("aBaa")
            sage: v = F("aBcb")
            sage: w = F("aBa")
            sage: v.has_prefix(u) or w.has_prefix(u)
            False
            sage: u.has_prefix(v) or w.has_prefix(v)
            False
            sage: u.has_prefix(w)
            True
            sage: u.has_prefix(u) and v.has_prefix(v) and w.has_prefix(w)
            True
        """
        if len(self) < len(other):
            return False
        i = 0
        while i < len(other) and self[i] == other[i]:
            i += 1
        return i == len(other)

    #TODO: check with Thierry that it does what it should
    def nielsen_lesser_than(self,other):
        """
        Determines wether ``self`` is strcitly before ``other`` in the Nielsen
        order used in the Nielsen reduction algorithm.

        OUTPUT:
        
        - ``len(v)-len(u)`` if it is >0, 

        - ``0`` if they have the same length, but ``u``<``v`` in the
          Nielsen order

        - ``-1`` if ``v=<u`` in the Nielsen order

        Recall that u<v iff 
           len(u)<len(v)  or 
             (  len(u) == len(v)  and 
                ( u = u'u'', v=v'v'' u'<_lex v' 
                 or 
                (u'=v' and u''<_lex v'')).
        """
        l = len(self)
        result = len(other)-l
        if result == 0:
            if l == 0: 
                return -1
            else:
                if l%2 == 1:
                    half = (l+1)/2
                else:
                    half = l/2
                u = self[0:half]
                v = other[0:half]
                if v < u:
                    return -1
                elif u == v:
                    uu = self[l-half:l] #TODO: do not we have to compare self.inverse(uuu) and self.inverse(vvv) instead ?
                    vv = self[l-half:l]
                    if self[l-half:l] <= self[l-half:l]:
                        return -1
        return result
