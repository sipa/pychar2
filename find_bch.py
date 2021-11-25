#!/usr/bin/env python3
# Copyright (c) 2021 Pieter Wuille
# Distributed under the MIT software license, see the accompanying
# file LICENSE or http://www.opensource.org/licenses/mit-license.php.

import pychar2
import random
import math

def gen_bch(base_field, deg, dist, min_len, min_ext_deg=1, max_ext_deg=16, max_len=None, pad_degree=False, dedup_iso=True):
    if max_len is None:
        max_len = min_len << base_field.BITS

    # Build a map of acceptable lengths, giving the extension degree for each.
    lengths = {}
    for ext_deg in range(min_ext_deg, max_ext_deg):
        for div in pychar2.z_divisors((1 << (base_field.BITS * ext_deg)) - 1):
            if div >= min_len and div <= max_len:
                if div not in lengths:
                    lengths[div] = ext_deg

    # Cached extension fields with primitive modulus of any given degree.
    extfields = {}

    # Iterate over the valid codes, from short to long length.
    for length in sorted(lengths):
        ext_deg = lengths[length]
        print("# len=%i ext_deg=%i: start" % (length, ext_deg))

        # Build (and cache) extension field to use.
        if ext_deg in extfields:
            extfield = extfields[ext_deg]
        else:
            if ext_deg == 1:
                extfield = base_field
            else:
                while True:
                    primpoly = random.randrange(1 << (base_field.BITS * ext_deg), 2 << (base_field.BITS * ext_deg))
                    if pychar2.poly_isprimitive(base_field, primpoly):
                        break
                extfield = pychar2.GF2Ext(base_field, primpoly, True)
                if (ext_deg * base_field.BITS <= 20):
                    extfield = pychar2.GF2Table(extfield)
                extfields[ext_deg] = extfield

        # Primitive element of extension field (order 2^(BITS*ext_deg) - 1).
        prim = pychar2.gf_primitive(extfield)
        # Element with order length.
        len_base = pychar2.gf_pow(extfield, prim, ((1 << (base_field.BITS * ext_deg)) - 1) // length)
        assert(pychar2.gf_pow(extfield, len_base, length) == 1)

        # Cache of minpolys, in function of power of len_base.
        minpolys = [None for _ in range(length)]
        def minpoly(n):
            """Compute minpoly(len_base**n), using cache."""
            n = n % length
            if minpolys[n] is not None:
                return minpolys[n]
            v = pychar2.gf_pow(extfield, len_base, n)
            if ext_deg == 1:
                minpoly = v | (1 << base_field.BITS)
            else:
                minpoly = pychar2.gf_minpoly(extfield, v)
            # Store the computed minpoly, for *all* values p for which minpoly(len_base**p)
            # is the same as minpoly(len_base**n).
            p = n
            while True:
                minpolys[p] = minpoly
                p = (p << base_field.BITS) % length
                if p == n: break
            return minpoly

        gens = set()
        outputs = 0
        def output(alpha_pow, c):
            """Produce output for a given alpha_pow and c value."""
            gen = 1
            for factor in set(minpoly(alpha_pow * (c + i)) for i in range(dist - 1)):
                gen = pychar2.poly_mul(base_field, gen, factor)
            found_deg = pychar2.poly_degree(base_field, gen)
            assert found_deg == deg or (pad_degree and found_deg < deg)
            if gen in gens: return 0
            if dedup_iso:
                geni = gen
                for i in range(base_field.BITS):
                    genir, _ = pychar2.poly_monic(base_field, pychar2.poly_reverse(base_field, geni))
                    gens.add(geni)
                    gens.add(genir)
                    gen = min(min(gen, geni), genir)
                    geni = pychar2.poly_square_coef(base_field, geni)
            else:
                gens.add(gen)
            alpha_minpoly = minpoly(alpha_pow)
            for m in range(1 << ((deg - found_deg) * base_field.BITS), 2 << ((deg - found_deg) * base_field.BITS)):
                if pychar2.vec_get(base_field, m, 0) == 0: continue
                mgen = pychar2.poly_mul(base_field, m, gen)
                print("gen=%s deg=%i len=%i ext_poly=%s c=%i dist=%i bch_gen=%s bch_deg=%i" % (pychar2.poly_list(base_field, mgen), deg, length, pychar2.poly_list(base_field, alpha_minpoly), c, dist, pychar2.poly_list(base_field, gen), found_deg))
            return 1

        # Bitset of powers of alpha already processed (this includes powers of alpha
        # which have a minpoly equal to one that has already been processed).
        alpha_pows_done = 0
        # Iterate over all alphas (extfield elements with order length).
        num_distinct_alphas = 0
        # List of valid c values (constructed during alpha_pow==1, reused for later iterations).
        valid_cs = []
        for alpha_pow in range(1, length):
            # Skip powers of len_base with order different from length.
            if math.gcd(alpha_pow, length) != 1: continue
            # Skip alphas which have a minpoly equal to one already processed.
            if (alpha_pows_done >> alpha_pow) & 1: continue
            pp = alpha_pow
            while True:
                alpha_pows_done |= (1 << pp)
                pp = (pp << base_field.BITS) % length
                if pp == alpha_pow: break
            # Compute alpha (which will go through all extfield elements with order length).
            num_distinct_alphas += 1

            if alpha_pow == 1:
                # Iterate over all c values and see which ones give acceptable degree.
                for c in range(1, length):
                    found_deg = sum(pychar2.poly_degree(base_field, v) for v in set(minpoly(c + i) for i in range(0, dist - 1)))
                    if found_deg == deg or (pad_degree and found_deg < deg):
                        valid_cs.append(c)
                        outputs += output(alpha_pow, c)
            else:
                for c in valid_cs:
                    outputs += output(alpha_pow, c)
        print("# len=%i ext_deg=%i: alphas=%i cs=%i gens=%i" % (length, ext_deg, num_distinct_alphas, len(valid_cs), outputs))

F = pychar2.GF2Table(pychar2.GF2n(41))

gen_bch(F, deg=14, dist=9, min_len=69, dedup_iso=False, pad_degree=True)
