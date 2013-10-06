#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.combinat.words.alphabet import build_alphabet
from sage.rings.integer import Integer

def build_alphabet_with_inverses(data, neg=None, names=None, name=None, negname=None):
    r"""
    Build two disjoint alphabets (i.e. sets) and a bijection between them from
    the given data.

    This is mainly used to build free groups.

    EXAMPLES::

        sage: build_alphabet_with_inverses('abc')
        ({'a', 'b', 'c'}, {'A', 'B', 'C'})
        sage: build_alphabet(3, name='a')
        ({'a0', 'a1', 'a2'}, {'A0', 'A1', 'A2'})

    TODO:

    Fix conventions in order to fit with build_alphabet in
    sage.combinat.words.alphabet
    """
    if isinstance(data, (int,Integer)):
        if name is None:
            name = 'a'
        if negname is None:
            if name.islower():
                negname = name.upper()
            elif name.isupper():
                negname = name.lower()
        return build_alphabet([name+str(i) for i in xrange(data)]), build_alphabet([negname+str(i) for i in xrange(data)])

    pos = build_alphabet(data)

    if neg is None:
        from sage.combinat.words.alphabet import set_of_letters
        if all(letter in set_of_letters['lower'] for letter in pos):
            neg = build_alphabet(''.join(pos).upper())
        elif all(letter in set_of_letters['upper'] for letter in pos):
            pos = build_alphabet(''.join(neg).lower())
        else:
            raise ValueError("not able to determine default inverse letters")
    else:
        neg = build_alphabet(neg)
        assert pos.cardinality() == neg.cardinality()
        for letter in pos:
            if letter in neg:
                raise ValueError("letter %s is both positive and negative"%letter)
        for letter in neg:
            if letter in pos:
                raise ValueError("letter %s is both positive and negative"%letter)

    return pos, neg

