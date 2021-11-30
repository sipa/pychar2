
import pychar2

def bch_checksum(field, generator, data):
    r = 0
    for d in data:
        r = pychar2.poly_mod(field, r << field.BITS, generator) ^ d
    return r

class BCHDecoder:
    def __init__(self, field, modulus, length, dist, c, generator):
        assert dist >= 2
        if isinstance(generator, list):
            generator = pychar2.poly_make(field, generator)
        degree = pychar2.poly_degree(field, generator)
        extfield = pychar2.GF2Ext(field, modulus)
        extgen = pychar2.poly_lift(extfield, generator)
        alpha = 1 << field.BITS
        assert pychar2.gf_hasorder(extfield, alpha, length)
        alphapow = [pychar2.gf_pow(extfield, alpha, i) for i in range(length)]
        for i in range(dist-1):
            assert pychar2.poly_eval(extfield, extgen, alphapow[(i+c) % length]) == 0

        def calc_syndrome(p):
            """Given a polynomial p over field, compute its syndrome polynomial (over extfield)."""
            pext = pychar2.poly_lift(extfield, p)
            ret = 0
            for i in range(dist-1):
                ret |= pychar2.poly_eval(extfield, pext, alphapow[(i+c) % length]) << (i * extfield.BITS)
            return ret

        trans = pychar2.trans_build(calc_syndrome, degree * field.BITS)
        print(trans)

        self._alphapow = alphapow
        self._length = length
        self._extfield = extfield
        self._dist = dist
        self._c = c
        self._trans = trans

    def length(self):
        return self._length

    def correct(self, checksum, erasures=None):
        if checksum == 0: return []
        if erasures is None:
            erasures = []

        # Compute the syndrome polynomial.
        syndrome = pychar2.trans_apply(self._trans, checksum)

        # Compute the gamma polynomial which encodes the erasure locations.
        gamma = 1
        for erasure in erasures:
            gamma ^= pychar2.vec_mul(self._extfield, gamma, self._alphapow[erasure]) << (self._extfield.BITS)

        # Compute err_loc (error locator polynomial) and omega (error evaluator polynomial).
        sl = pychar2.poly_mul(self._extfield, syndrome, gamma)
        max_degree = (len(erasures) + self._dist - 3) // 2
        xd = 1 << (self._extfield.BITS * (self._dist - 1))
        omega, err_loc, _ = pychar2.poly_extgcd(self._extfield, sl, xd, max_degree + 1)

        # Compute locator (locator polynomial for both errors and erasures).
        locator = pychar2.poly_mul(self._extfield, err_loc, gamma)

        # Locate errors (version using root finding).
        locations = list(erasures)
        roots = pychar2.poly_findroots(self._extfield, err_loc)
        if roots is None: return None
        for root in roots:
            if root not in self._alphapow: return None
            locations.append((-self._alphapow.index(root)) % self._length)

        # Locate errors (version using trial evaluation).
#        locations = list(erasures)
#        for i in range(self._length):
#            if pychar2.poly_eval(self._extfield, err_loc, self._alphapow[i]) == 0:
#                locations.append((-i) % self._length)
#        if len(locations) != pychar2.poly_degree(self._extfield, locator):
#            return None

        # Compute errors.
        ret = []
        locator_der = pychar2.poly_deriv(self._extfield, locator)
        for location in sorted(locations):
            amp = self._alphapow[(-location) % self._length]
            oe = pychar2.poly_eval(self._extfield, omega, amp)
            if oe == 0: continue
            le = pychar2.poly_eval(self._extfield, locator_der, amp)
            fe = self._alphapow[((1 - self._c) * location) % self._length]
            err = self._extfield.mul(self._extfield.mul(fe, oe), self._extfield.inv(le))
            ret.append((location, err))

        return ret

code_length = 21
distance = 9
c_const = 14
F = pychar2.GF2Table(pychar2.GF2n(67))
field_size = 1 << F.BITS
modulus = pychar2.poly_make(F, [57,1])
generator = pychar2.poly_make(F, [59,11,63,34,36,16,19,11,1])
degree = pychar2.poly_degree(F, generator)
B = BCHDecoder(F, modulus, code_length, distance, c_const, generator)

import random

while True:
    datalen = random.randrange(0, code_length - degree + 1)
    word = [random.randrange(0, field_size) for _ in range(datalen)]
    checksum = bch_checksum(F, generator, word + [0 for _ in range(degree)])
    codeword = word + list(reversed([pychar2.vec_get(F, checksum, i) for i in range(degree)]))
    length = datalen + degree
    assert bch_checksum(F, generator, codeword) == 0

    errword = list(codeword)
    erasures = set()
    num_error = random.randrange(1 + ((distance - 1) // 2))
    num_erase = random.randrange(0, distance - 2*num_error)
    assert len(codeword) == length
    assert len(errword) == length

    print("length %i, %i erasures, %i errors" % (length, num_erase, num_error))

    for _ in range(num_erase):
        pos = random.randrange(0, length)
        err = random.randrange(1, field_size)
        errword[pos] ^= err
        erasures.add(length - 1 - pos)

    for _ in range(num_error):
        pos = random.randrange(0, length)
        err = random.randrange(1, field_size)
        errword[pos] ^= err

    exp = []
    for i in range(length):
        if codeword[i] != errword[i]:
            exp.append((length-1-i, codeword[i] ^ errword[i]))

    newchecksum = bch_checksum(F, generator, errword)
    decode = B.correct(newchecksum, erasures)
    assert set(decode) == set(exp)
