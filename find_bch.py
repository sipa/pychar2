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

def gen_bch(field, min_deg, min_dist, min_len, report_fn=default_report_fn, max_deg=None, min_ext_deg=1, max_ext_deg=None, max_len=None, pad_degree=False, dedup_iso=True, one_gen=False):
    """Generate BCH code generators and print them out.

    - field: the field the code is over
    - min_deg: the minimum number of checksum symbols
    - max_deg: the maximum number of checksum symbols (default: min_deg)
    - min_dist: the minimum distance the code must have
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
    if max_ext_deg is None: max_ext_deg = (4 * max_deg + min_dist - 2) // (min_dist - 1) 

    # Build a map of acceptable lengths, giving the extension degree for each.
    lengths = {}
    for ext_deg in range(min_ext_deg, max_ext_deg):
        for div in pychar2.z_divisors((1 << (field.BITS * ext_deg)) - 1):
            if div >= min_len and (max_len is None or div <= max_len):
                if div not in lengths:
                    if not viable(field.BITS, div, max_deg, min_dist):
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

        gens = set()
        outputs = 0
        def output(alpha_pow, c, dist):
            """Produce output for a given alpha_pow and c value."""
            gen = 1
            for factor in set(minpoly(alpha_pow * (c + i)) for i in range(dist - 1)):
                gen = pychar2.poly_mul(field, gen, factor)
            found_deg = pychar2.poly_degree(field, gen)
            assert found_deg <= max_deg and (found_deg >= min_deg or pad_degree)
            if gen in gens: return 0
            if dedup_iso:
                geni = gen
                for i in range(field.BITS):
                    genir, _ = pychar2.poly_monic(field, pychar2.poly_reverse(field, geni))
                    gens.add(geni)
                    gens.add(genir)
                    gen = min(min(gen, geni), genir)
                    geni = pychar2.poly_square_coef(field, geni)
            else:
                gens.add(gen)
            alpha_minpoly = minpoly(alpha_pow)
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
            return 1

        # Bitset of powers of alpha already processed (this includes powers of alpha
        # which have a minpoly equal to one that has already been processed).
        alpha_pows_done = 0
        # Iterate over all alphas (extfield elements with order length).
        num_distinct_alphas = 0
        # List of valid c values (constructed during alpha_pow==1, reused for later iterations).
        valid_c_dists = []
        for alpha_pow in range(1, 2 if one_gen else length):
            # Skip powers of len_base with order different from length.
            if math.gcd(alpha_pow, length) != 1: continue
            # Skip alphas which have a minpoly equal to one already processed.
            if (alpha_pows_done >> alpha_pow) & 1: continue
            pp = alpha_pow
            while True:
                alpha_pows_done |= (1 << pp)
                pp = (pp << field.BITS) % length
                if pp == alpha_pow: break
            num_distinct_alphas += 1

            if alpha_pow == 1:
                # Iterate over all c values and see which ones give acceptable degree.
                for c in range(1, length):
                    # Start by searching for dist=min_dist, but as long as dists exist at or
                    # below max_deg, keep incrementing dist.
                    dist = min_dist
                    while True:
                        found_deg = sum(pychar2.poly_degree(field, v) for v in set(minpoly(c + i) for i in range(0, dist - 1)))
                        if found_deg > max_deg: break
                        if found_deg >= min_deg or pad_degree:
                            valid_c_dists.append((c, dist))
                            outputs += output(alpha_pow, c, dist)
                            if one_gen: break
                        dist += 1
                    if one_gen and outputs: break
            else:
                for c, dist in valid_c_dists:
                    outputs += output(alpha_pow, c, dist)

F = pychar2.GF2Table(pychar2.GF2n(41))

gen_bch(F, min_deg=13, min_dist=9, min_len=69, dedup_iso=False)
