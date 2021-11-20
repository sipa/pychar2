#!/usr/bin/env python3
# Copyright (c) 2020-2021 Pieter Wuille
# Distributed under the MIT software license, see the accompanying
# file LICENSE or http://www.opensource.org/licenses/mit-license.php.

"""Native Python implementation of characteristic 2 field algebra.

For efficiency reasons, all field elements, vectors, and polynomials
are represented as ints, without individual wrapper objects. The
interpretation of elements is determined by field objects which are
passed around along with the elements, but the zero and one elements
are guaranteed to be represented by 0 and 1.

Field classes gf are expected to expose:
- gf.BITS: field order is (2**gf.BITS)
- gf.BASE: base field, or None
- gf.mulx(v): multiply v by generator
- gf.mul(a,b): multiply a and b
- gf.sqr(v): square v
- gf.inv(v): invert nonzero v

Addition of field elements is simply the xor (^) operation.
"""

def gf_pow(gf, v, n):
    """Raise field element v in field gf to power n (n >= 0)."""
    r = 1
    while n:
        if n & 1:
            r = gf.mul(r, v)
        n >>= 1
        v = gf.sqr(v)
    return r

def poly_degree(gf, p):
    """Get the degree of polynomial p over field gf."""
    if p == 0: return 0
    return (p.bit_length() - 1) // gf.BITS

def poly_coef(gf, p, n):
    """Get the nth degree coefficient of polynomial p over field gf."""
    return (p >> (n * gf.BITS)) & ((1 << gf.BITS) - 1)

def poly_make(gf, lst):
    """Make a polynomial from a list of coefficients (high to low)."""
    ret = 0
    for v in lst:
        ret <<= gf.BITS
        ret |= v
    return ret

def vec_mul(gf, p, v):
    """Multiply vector p over field gf with field element v."""
    if v == 0: return 0
    if v == 1: return p
    ret = 0
    for d in range(poly_degree(gf, p) + 1):
        ret |= gf.mul(v, poly_coef(gf, p, d)) << (gf.BITS * d)
    return ret

def poly_mul(gf, a, b):
    """Multiply two polynomials over field gf."""
    ret = 0
    if a == 0 or b == 0: return 0
    if a == 1: return b
    if b == 1: return a
    for d in range(poly_degree(gf, a) + 1):
        ret ^= vec_mul(gf, b, poly_coef(gf, a, d)) << (gf.BITS * d)
    return ret

def poly_addroot(gf, p, v):
    """Multiply polynomial p over field gf with (x - v)."""
    return (p << gf.BITS) ^ vec_mul(gf, p, v)

def poly_monic(gf, p):
    """Make polynomial p over field gf monic, also returning the multiplication factor."""
    i = gf.inv(poly_coef(gf, p, poly_degree(gf, p)))
    return vec_mul(gf, p, i), i

def poly_ismonic(gf, p):
    """Check whether polynomial p over field gf is monic."""
    return poly_coef(gf, p, poly_degree(gf, p)) == 1

def poly_divmod(gf, p, m):
    """Divide polynomial p by monic polynomial m, over field gf. Return quotient and remainder."""
    assert poly_ismonic(gf, m)
    pn, mn = poly_degree(gf, p), poly_degree(gf, m)
    if mn == 0:
        return p, 0
    quot = 0
    while pn >= mn:
        term = poly_coef(gf, p, pn)
        quot |= term << ((pn - mn) * gf.BITS)
        assert term != 0
        p ^= vec_mul(gf, m, term) << ((pn - mn) * gf.BITS)
        pn = poly_degree(gf, p)
    return quot, p

def poly_mod(gf, p, m):
    """Compute polynomial p modulo polynomial m, over field gf."""
    return poly_divmod(gf, p, m)[1]

def poly_extgcd(gf, a, b):
    """Return the gcd of polynomials a and b over field gf, as well as the Bezout coefficients."""
    aa, ab, ba, bb = 1, 0, 0, 1
    if a == 0 or poly_degree(gf, a) < poly_degree(gf, b):
        a, b = b, a
        aa, ab, ba, bb = ba, bb, aa, ab
    while b != 0:
        b, i = poly_monic(gf, b)
        ba, bb = vec_mul(gf, ba, i), vec_mul(gf, bb, i)
        q, r = poly_divmod(gf, a, b)
        a, b = b, r
        aa, ab, ba, bb = ba, bb, aa ^ poly_mul(gf, ba, q), ab ^ poly_mul(gf, bb, q)
    return a, aa, ab

def poly_gcd(gf, a, b):
    """Return the gcd of polynomials a and b over field gf."""
    return poly_extgcd(gf, a, b)[0]

def poly_invmod(gf, p, m):
    """Return the inverse of polynomial p over field gf, modulo polynomial m."""
    if p == 1: return 1
    gcd, inv, _ = poly_extgcd(gf, p, m)
    if gcd != 1:
        return None
    return inv

def poly_sqr(gf, p):
    """Square a polynomial p over field gf. This exploits the Frobenius endomorphism."""
    ret = 0
    for d in range(poly_degree(gf, p) + 1):
        ret |= gf.sqr(poly_coef(gf, p, d)) << (2 * gf.BITS * d)
    return ret


def poly_minpoly(gf, v):
    """Given an extension field gf and an element v in it, find its minimal polynomial over gf.BASE."""
    basebits = gf.BASE.BITS
    r = 1
    a = v
    while True:
        r = poly_addroot(gf, r, v)
        v = gf_pow(gf, v, 1 << basebits)
        if v == a:
            break
    s = 0
    for d in range(poly_degree(gf, r) + 1):
        s |= poly_coef(gf, r, d) << (basebits * d)
    return s

def poly_tracemod(gf, p, v):
    """Compute y + y^2 + y^4 + ... + y^(order(gf)/2) mod p over gf, where y=v*x."""
    out = v << gf.BITS
    for _ in range(gf.BITS - 1):
        out = poly_mod(gf, poly_sqr(gf, out) ^ (v << gf.BITS), p)
    return out

def poly_frobeniusmod(gf, p):
    """Compute x^(order(gf)) mod p, for polynomial p over gf."""
    out = 1 << gf.BITS
    for _ in range(gf.BITS):
        out = poly_mod(gf, poly_sqr(gf, out), p)
    return out

def poly_findroots(gf, p):
    """Find the roots of polynomial p over gf, or None if not fully factorizable into unique roots."""
    assert p != 0
    if poly_degree(gf, p) == 0:
        return []
    p, _ = poly_monic(gf, p)
    if poly_degree(gf, p) == 1:
        return [poly_coef(gf, p, 0)]
    if poly_frobeniusmod(gf, p) != (1 << gf.BITS):
        return None

    ret = []
    def rec_split(p, v):
        assert poly_degree(gf, p) > 0 and poly_ismonic(gf, p)
        if poly_degree(gf, p) == 1:
            ret.append(poly_coef(gf, p, 0))
            return
        while True:
            trace = poly_tracemod(gf, p, v)
            v = gf.mulx(v)
            gcd = poly_gcd(gf, trace, p)
            if poly_degree(gf, gcd) < poly_degree(gf, p) and poly_degree(gf, gcd) > 0:
                break
        factor1, _ = poly_monic(gf, gcd)
        factor2, _ = poly_divmod(gf, p, factor1)
        rec_split(factor1, v)
        rec_split(factor2, v)

    rec_split(p, random.randrange(1, 1 << gf.BITS))
    return sorted(ret)

class GF2:
    """Field operations object for GF(2)."""

    def __init__(self):
        self.BITS = 1
        self.BASE = None
        pass

    def mulx(self, v):
        return v

    def mul(self, a, b):
        return a & b

    def sqr(self, v):
        return v

    def inv(self, v):
        return v


class GF2Ext:
    """Field operations object for extension fields of characteristic 2 fields."""

    def __init__(self, base, primpoly):
        """Construct a field extension over field base and primitive monic polynomial primpoly over it."""
        if isinstance(primpoly, list):
            primpoly = poly_make(base, primpoly)
        assert(isinstance(primpoly, int))
        assert(poly_ismonic(base, primpoly))
        assert(poly_degree(base, primpoly) > 1)
        self._degree = poly_degree(base, primpoly)
        self._modulus = primpoly
        self.BITS = base.BITS * self._degree
        self.BASE = base

    def mulx(self, v):
        return poly_mod(self.BASE, v << self.BASE.BITS, self._modulus)

    def mul(self, a, b):
        return poly_mod(self.BASE, poly_mul(self.BASE, a, b), self._modulus)

    def sqr(self, v):
        return poly_mod(self.BASE, poly_sqr(self.BASE, v), self._modulus)

    def inv(self, v):
        return poly_invmod(self.BASE, v, self._modulus)

class GF2n:
    """Field operations object for GF(2^n).

    The behavior of GF2n(modulus) is identical to GF2Ext(GF2(), modulus), but faster.
    """

    def __init__(self, modulus):
        """Construct a field GF(2^n), given a degree n irreducible polynomial over GF(2)."""
        assert isinstance(modulus, int)
        assert modulus > 1
        self.BITS = modulus.bit_length() - 1
        self.BASE = GF2()
        self._modulus = modulus

    def mulx(self, v):
        v <<= 1
        if v >> self.BITS:
            v ^= self._modulus
        return v

    def mul(self, a, b):
        ret = 0
        while b:
            if b & 1:
                ret ^= a
            b >>= 1
            a = self.mulx(a)
        return ret

    def sqr(self, v):
        return self.mul(v, v)

    def inv(self, v):
        if v == 1: return 1
        assert v != 0
        t1, t2 = 0, 1
        r1, r2 = self._modulus, v
        r1l, r2l = self.BITS + 1, r2.bit_length()
        while r2:
            q = r1l - r2l
            r1 ^= r2 << q
            t1 ^= t2 << q
            r1l = r1.bit_length()
            if r1 < r2:
                t1, t2 = t2, t1
                r1, r2 = r2, r1
                r1l, r2l = r2l, r1l
        assert r1 == 1
        return t1


class GF2Table:
    """Class that optimizes havior of another field, using exp/log tables."""

    def __init__(self, unopt):
        """Construct a GF2Table object given the non-table version of the field."""
        logtbl = [0 for _ in range(1 << unopt.BITS)]
        exptbl = [0 for _ in range((1 << unopt.BITS) - 1)]
        v = 1
        for l in range((1 << unopt.BITS) - 1):
            assert (v == 1) == (l == 0)
            logtbl[v] = l
            exptbl[l] = v
            v = unopt.mulx(v)
        assert v == 1
        self.BITS = unopt.BITS
        self.BASE = unopt.BASE
        self._logtbl = tuple(logtbl)
        self._exptbl = tuple(exptbl)

    def mulx(self, v):
        """Multiply field element v by a (fixed) generator."""
        if v == 0: return 0
        l = self._logtbl[v] + 1
        if (l + 1) >> self.BITS:
            l = 0
        return self._exptbl[l]

    def mul(self, a, b):
        """Multiply field elements a and b."""
        if a == 0 or b == 0: return 0
        l = self._logtbl[a] + self._logtbl[b]
        if (l + 1) >> self.BITS:
            l = l + 1 - (1 << self.BITS)
        return self._exptbl[l]

    def sqr(self, v):
        """Square field element v."""
        if v == 0: return 0
        l = 2 * self._logtbl[v]
        if (l + 1) >> self.BITS:
            l = l + 1 - (1 << self.BITS)
        return self._exptbl[l]

    def inv(self, v):
        """Invert non-zero field element v."""
        assert v != 0
        if v == 1: return 1
        return self._exptbl[(1 << self.BITS) - 1 - self._logtbl[v]]

import random
import unittest

def test_fields():
    return [
        GF2(),
        GF2Table(GF2()),
        GF2n(7),
        GF2Ext(GF2(), 11),
        GF2n(19),
        GF2Table(GF2n(37)),
        GF2n(67),
        GF2Table(GF2Ext(GF2n(67), [1, 50, 63, 10])),
        GF2Ext(GF2n(19), 0x100014912),
    ]

class TestPolyInvMod(unittest.TestCase):
    """Test class for poly_invmod."""

    def field_test(self, gf, degree):
        b = random.getrandbits(degree * gf.BITS)
        while True:
            a = random.getrandbits(degree * gf.BITS)
            m = random.getrandbits(degree * gf.BITS) | (1 << (degree * gf.BITS))
            if poly_gcd(gf, a, m) == 1:
                break
        p = poly_mod(gf, poly_mul(gf, a, b), m)
        ai = poly_invmod(gf, a, m)
        aia = poly_mod(gf, poly_mul(gf, a, ai), m)
        assert aia == 1
        p = poly_mod(gf, poly_mul(gf, a, b), m)
        b2 = poly_mod(gf, poly_mul(gf, p, ai), m)
        assert b2 == b

    def test(self):
        """Run tests."""
        for field in test_fields():
            for degree in range(1, 100 // field.BITS):
                for j in range(5):
                    self.field_test(field, degree)

class TestPolyFindRoots(unittest.TestCase):
    """Test class for poly_findroots."""

    def field_test(self, gf):
        """Run tests for given field gf."""
        for test_size in [0, 1, 2, 3, 10]:
            roots = [random.randrange(1 << gf.BITS) for _ in range(test_size)]
            roots_set = set(roots)
            # Construct a polynomial with all elements of roots as roots (with multiplicity).
            poly = 1
            for root in roots:
                poly = poly_addroot(gf, poly, root)
            # Invoke the root finding algorithm.
            found_roots = poly_findroots(gf, poly)
            # The result must match the input, unless any roots were repeated.
            if len(roots) == len(roots_set):
                self.assertEqual(found_roots, sorted(roots))
            else:
                self.assertIsNone(found_roots)

    def test(self):
        """Run tests."""
        for field in test_fields():
            for j in range(10):
                self.field_test(field)

if __name__ == '__main__':
    unittest.main()
