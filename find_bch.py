#!/usr/bin/env python3
# Copyright (c) 2021 Pieter Wuille
# Distributed under the MIT software license, see the accompanying
# file LICENSE or http://www.opensource.org/licenses/mit-license.php.

import pychar2
import random
import math
from enum import Enum

def combination(n, k):
    if n < 2*k: k = n - k
    r = 1
    for i in range(k):
        r *= n - i
        r //= (i + 1)
    return r

def viable(field_bits, length, deg, dist):
    # For odd distance, model the need to correct up to (dist-1)//2 errors.
    # For even distance, model the need to correct up to (dist-1)//2 errors after 1 erasure.
    comb = 0
    erasure = 1 - (dist & 1)
    for err in range(1 + ((dist - 1) >> 1)):
        comb += combination(length, err) * (((1 << field_bits) - 1) ** err)
        if erasure:
            comb += combination(length - 1, err) * (((1 << field_bits) - 1) ** (err + 1))
    bits_needed = (comb - 1).bit_length()
    return bits_needed <= field_bits * deg

def default_report_fn(data):
    field = data["field"]
    print("gen=[%s] degree=%i bch_length=%i bch_dist=%i bch_gen=[%s] bch_degree=%i bch_modulus=[%s] bch_c=%i" % (
              ",".join("%i" % v for v in pychar2.poly_list(field, data["generator"])),
              data["degree"],
              data["bch"]["length"],
              data["bch"]["distance"],
              ",".join("%i" % v for v in pychar2.poly_list(field, data["bch"]["generator"])),
              data["bch"]["degree"],
              ",".join("%i" % v for v in pychar2.poly_list(field, data["bch"]["modulus"])),
              data["bch"]["c"]))

def gen_bch(field, min_deg, dist, min_len, report_fn=default_report_fn, max_deg=None, min_ext_deg=1, max_ext_deg=None, max_len=None, pad_degree=False, dedup_iso=True, one_gen=False):
    """Generate BCH code generators and print them out.

    - field: the field the code is over
    - min_deg: the minimum number of checksum symbols
    - max_deg: the maximum number of checksum symbols (default: min_deg)
    - dist: the minimum distance the code must have
    - min_len: the minimum length the code must have
    - max_len: the maximum length the code must have (default max_len * size(field))
    - min_ext_deg: minimum extension field degree to consider (default: 1)
    - max_ext_deg: maximum extension field degree to consider (default: heuristic)
    - pad_degree: if a code is found with checksum symbols below min_deg reject it (False) or
                  extend the generator with all factors to make it reach it (True).
    - dedup_iso: among generators with identical error detection properties (assuming errors
                 uniformly affecting all values of field), only print out one
    - one_gen: stop after printing out one solution for each length
    """

    if max_deg is None: max_deg = min_deg
    if max_ext_deg is None: max_ext_deg = (4 * max_deg + dist - 2) // (dist - 1)
    if one_gen: dedup_iso = True

    # Build a map of acceptable lengths, giving the extension degree for each.
    lengths = {}
    for ext_deg in range(min_ext_deg, max_ext_deg):
        for div in pychar2.z_divisors((1 << (field.BITS * ext_deg)) - 1):
            if div >= min_len and (max_len is None or div <= max_len):
                if div not in lengths:
                    if not viable(field.BITS, div, max_deg, dist):
                        max_len = div - 1
                    else:
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
                extfield = field
            else:
                modulus = pychar2.poly_irreducible(field, ext_deg)
                extfield = pychar2.GF2Ext(field, modulus)
            extfields[ext_deg] = extfield

        # Construct an element of extfield of order length.
        while True:
            elem = random.getrandbits(field.BITS * ext_deg)
            len_base = pychar2.gf_pow(extfield, elem, ((1 << (field.BITS * ext_deg)) - 1) // length)
            if pychar2.gf_hasorder(extfield, len_base, length): break

        # Cache of minpolys, in function of power of len_base.
        minpolys = [None for _ in range(length)]
        def minpoly(n):
            """Compute minpoly(len_base**n), using cache."""
            n = n % length
            if minpolys[n] is not None:
                return minpolys[n]
            v = pychar2.gf_pow(extfield, len_base, n)
            if ext_deg == 1:
                minpoly = v | (1 << field.BITS)
            else:
                minpoly = pychar2.gf_minpoly(extfield, v)
            # Store the computed minpoly, for *all* values p for which minpoly(len_base**p)
            # is the same as minpoly(len_base**n).
            p = n
            while True:
                minpolys[p] = minpoly
                p = (p << field.BITS) % length
                if p == n: break
            return minpoly

        def output_mgen(alpha_pow, c, gen):
            """Produce output for (alpha_pow, c), adding factors to reach min_deg as needed."""
            alpha_minpoly = minpoly(alpha_pow)
            found_deg = pychar2.poly_degree(field, gen)
            assert found_deg <= max_deg and (found_deg >= min_deg or pad_degree)
            add_deg = max(0, min_deg - found_deg)
            for m in range(1 << (add_deg * field.BITS), 2 << (add_deg * field.BITS)):
                if pychar2.vec_get(field, m, 0) == 0: continue
                mgen = pychar2.poly_mul(field, m, gen)
                result_data = {
                    "generator": mgen,
                    "field": field,
                    "degree": found_deg + add_deg,
                    "bch": {
                        "length": length,
                        "generator": gen,
                        "degree": found_deg,
                        "distance": dist,
                        "modulus": alpha_minpoly,
                        "c": c
                    }
                }
                report_fn(result_data)
                if one_gen: break

        gens = set()
        num_distinct_gens = [0]
        def output_dedup(alpha_pow, c):
            """Produce output for (alpha_pow, c) combination, filtering out duplicates.

            If not dedup_iso, this also produces output for (+- alpha_pow * 2^i, c), which
            has distinct but equivalent generators."""
            c = (c % length)
            alpha_pow = (alpha_pow % length)
            # Compute the generator for the provided (alpha_pow, c).
            gen = 1
            for factor in set(minpoly(alpha_pow * (c + i)) for i in range(dist - 1)):
                gen = pychar2.poly_mul(field, gen, factor)
            if gen in gens: return
            # Compute the generator for (-alpha_pow, c).
            geni, _ = pychar2.poly_monic(field, pychar2.poly_reverse(field, gen))
            # Iterate over i to find the generators for (+- alpha_pow*2^i, c), adding all of them
            # to the gens set for deduplication.
            num_distinct_gens[0] += 1
            for i in range(field.BITS):
                if i == 0 or not dedup_iso: output_mgen(alpha_pow, c, gen)
                if not dedup_iso and geni != gen: output_mgen(length - alpha_pow, c, geni)
                gens.add(gen)
                gens.add(geni)
                gen = pychar2.poly_square_coef(field, gen)
                geni = pychar2.poly_square_coef(field, geni)
                alpha_pow = (alpha_pow << 1) % length

        # Determine which powers of alpha result in distinct minpolys and order length.
        # Multiplying alpha_pow with (1 << field.BITS) does not change the minpoly.
        # Multiplying alpha_pow with 2 corresponds to squaring all coefficients of the
        # minpoly, and of the generators that come out (which are distinct but equivalent).
        # The same is true for negating alpha_pow, which reverses the order of
        # coefficients of minpoly and the generators that come out.
        # We avoid processing alpha_pows with equivalent generators here, and print all
        # variants if desired in output_dedup.
        # The list of interesting alpha_pows.
        alpha_pows = []
        # Bitvector of alpha_pows and equivalent ones which have been added already.
        alpha_done = 0
        for alpha_pow in range(1, (length + 1) // 2):
            # Skip powers of alpha whose minpoly we have already added.
            if (alpha_done >> alpha_pow) & 1: continue
            # Skip powers of len_base with order different from length.
            if math.gcd(alpha_pow, length) != 1: continue
            # We have a good alpha_pow, remember it.
            alpha_pows.append(alpha_pow)
            # Add it, and all its equivalent powers, to the alpha_done bitset.
            pp = alpha_pow
            while True:
                if pp < (length + 1) // 2: alpha_done |= (1 << pp)
                pp = (pp << 1) % length
                if pp == alpha_pow: break

        # Iterate over all c values. Only [c,c+dist-2] intervals are searched which contain a value
        # in [0,c/2]. Mirroring the interval around c/2 corresponds to negating all the len_base
        # powers, which results in distinct but equivalent generators. output_dedup will output
        # both if desired, so we can avoid the double work here.
        found = False
        for c in range(2 - dist, (length + 1) // 2):
            first = True
            for alpha_pow in alpha_pows:
                if first:
                    # Determine if this c value results in acceptable generators.
                    first = False
                    found_deg = sum(pychar2.poly_degree(field, v) for v in set(minpoly(c + i) for i in range(0, dist - 1)))
                    if found_deg <= max_deg and (found_deg >= min_deg or pad_degree):
                        found = True
                        output_dedup(alpha_pow, c)
                    else:
                        break
                else:
                    # For other alpha_pows, we already know they'll work.
                    output_dedup(alpha_pow, c)
                    found = True
                if one_gen and found: break
            if one_gen and found: break

        print("# len=%i ext_deg=%i: %i alphas, %i classes, %i generators" % (length, ext_deg, len(alpha_pows), num_distinct_gens[0], len(gens)))

F = pychar2.GF2Table(pychar2.GF2n(41))
gen_bch(field=F, min_deg=13, dist=9, min_len=69, dedup_iso=False)
