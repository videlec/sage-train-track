#*****************************************************************************
#       Copyright (C) 2013 Thierry Coulbois <thierry.coulbois@univ-amu.fr>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.combinat.words.alphabet import build_alphabet

def build_alphabet_with_inverses(data, neg=None, names=None, name=None):
    r"""
    Build two disjoint alphabets (i.e. sets) and a bijection between them from the given
    data.

    This is mainly used to build free groups.

    EXAMPLES::

        sage: build_alphabet_with_inverses('abc')
        ({'a', 'b', 'c'}, {'A', 'B', 'C'})

    TODO:

    Fix conventions in order to fit with build_alphabet in
    sage.combinat.words.alphabet
    """
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

def extension_alpha(pos, neg, n=1):
    r"""
    Return ``n`` letters to append to the free group with positive letters
    ``pos`` and negative letters ``neg``.

    The function test the letters 'a', 'b', ... with inverses 'A', 'B', ...
    """
    i = 0
    pos_to_add = []
    neg_to_add = []
    while i<26 and len(pos_to_add) < n:
        c = chr(97 + i)
        cc = chr(65+i)
        if not c not in pos and cc not in neg:
            pos_to_add.append(c)
            neg_to_add.append(cc)
        i += 1
    if i == 26 and len(pos_to_add) != n:
        raise ValueError("no further possible extension")
    return pos_to_add, neg_to_add

def extension_num(A, n=1, *args):
    r"""
    Return ``n`` letters to append to the alphabet ``A``.

    EXAMPLES::

        sage: A = AlphabetWithInverses('abc','ABC')
        sage: extension_num(A, n=3)
        sage: extension_num(A, n=3, 'b')
        sage: extension_num(A, n=3, 'c', 'Y')
    """
    i = 0
    pos = []
    neg = []
    
    if len(args) == 0:
        letter = 'a'
        LETTER = 'A'
    elif len(args) == 1:
        letter = args[0]
        LETTER = chr(ord(args[0])-32)
    elif len(args) == 2:
        letter = args[0]
        LETTER = args[1]
    else:
        raise ValueError("args should have length at most 2")

    while len(pos) < n:
        c = letter + str(i)
        if not A.is_positive_letter(c):
            pos.append(c)
            neg.append(LETTER + str(i))
        i += 1
    return pos,neg

