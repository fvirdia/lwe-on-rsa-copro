# -*- coding: utf-8 -*-
"""
Kyber using big integer arithmetic - proof-of-concept

.. note :: Run tests as ``sage -t test.py``

"""
from sage.all import parent, ZZ, vector, PolynomialRing, GF
from sage.all import log, ceil, randint, set_random_seed, random_vector, matrix, floor


def BinomialDistribution(eta):
    r = 0
    for i in range(eta):
        r += randint(0, 1) - randint(0, 1)
    return r


def balance(e, q=None):
    """
    Return a representation of `e` with elements balanced between `-q/2` and `q/2`

    :param e: a vector, polynomial or scalar
    :param q: optional modulus, if not present this function tries to recover it from `e`

    :returns: a vector, polynomial or scalar over/in the integers
    """
    try:
        p = parent(e).change_ring(ZZ)
        return p([balance(e_, q=q) for e_ in e])
    except (TypeError, AttributeError):
        if q is None:
            try:
                q = parent(e).order()
            except AttributeError:
                q = parent(e).base_ring().order()
        e = ZZ(e)
        e = e % q
        return ZZ(e-q) if e>q//2 else ZZ(e)


# Kyber (sort of)

class Kyber:

    n = 256
    q = 7681
    eta = 4
    k = 3
    D = staticmethod(BinomialDistribution)
    f = [1]+[0]*(n-1)+[1]
    ce = n

    @classmethod
    def key_gen(cls, seed=None):
        """Generate a new public/secret key pair

        :param cls: Kyber class, inherit and change constants to change defaults
        :param seed: seed used for random sampling if provided

        .. note :: Resembles Algorithm 1 of the Kyber paper.

        """
        n, q, eta, k, D = cls.n, cls.q, cls.eta, cls.k, cls.D

        if seed is not None:
            set_random_seed(seed)

        R, x = PolynomialRing(ZZ, "x").objgen()
        Rq = PolynomialRing(GF(q), "x")
        f = R(cls.f)

        A = matrix(Rq, k, k, [Rq.random_element(degree=n-1) for _ in range(k*k)])
        s = vector(R, k, [R([(D(eta)) for _ in range(n)]) for _ in range(k)])
        e = vector(R, k, [R([(D(eta)) for _ in range(n)]) for _ in range(k)])
        t = (A*s + e)  % f  # NOTE ignoring compression

        return (A, t), s

    @classmethod
    def enc(cls, pk, m=None, seed=None):
        """IND-CPA encryption sans compression

        :param cls: Kyber class, inherit and change constants to change defaults
        :param pk: public key
        :param m: optional message, otherwise all zero string is encrypted
        :param seed: seed used for random sampling if provided

        .. note :: Resembles Algorithm 2 of the Kyber paper.

        """
        n, q, eta, k, D = cls.n, cls.q, cls.eta, cls.k, cls.D

        if seed is not None:
            set_random_seed(seed)

        A, t = pk

        R, x = PolynomialRing(ZZ, "x").objgen()
        f = R(cls.f)

        r  = vector(R, k, [R([(D(eta)) for _ in range(n)]) for _ in range(k)])
        e1 = vector(R, k, [R([(D(eta)) for _ in range(n)]) for _ in range(k)])
        e2 = R([(D(eta)) for _ in range(n)])

        if m is None:
            m = (0,)

        u = (r*A + e1) % f  # NOTE ignoring compression
        u.set_immutable()
        v = (r*t + e2 + q//2 * R(list(m))) % f  # NOTE ignoring compression
        return u, v

    @classmethod
    def dec(cls, sk, c, decode=True):
        """IND-CPA decryption

        :param cls: Kyber class, inherit and change constants to change defaults
        :param sk: secret key
        :param c: ciphertext
        :param decode: perform final decoding

        .. note :: Resembles Algorithm 3 of the Kyber paper.

        """
        n, q = cls.n, cls.q

        s = sk
        u, v = c

        R, x = PolynomialRing(ZZ, "x").objgen()
        f = R(cls.f)

        m = (v - s*u) % f
        m = list(m)
        while len(m) < n:
            m.append(0)

        m = balance(vector(m), q)

        if decode:
            return cls.decode(m, q, n)
        else:
            return m

    @staticmethod
    def decode(m, q, n):
        """Decode vector `m` to `\{0,1\}^n` depending on distance to `q/2`

        :param m: a vector of length `\leq n`
        :param q: modulus

        """
        return vector(GF(2), n, [abs(e)>q/ZZ(4) for e in m] + [0 for _ in range(n-len(m))])

    @classmethod
    def encap(cls, pk, seed=None):
        """IND-CCA encapsulation sans compression or extra hash

        :param cls: Kyber class, inherit and change constants to change defaults
        :param pk: public key
        :param seed: seed used for random sampling if provided

        .. note :: Resembles Algorithm 4 of the Kyber paper.

        """
        n = cls.n

        if seed is not None:
            set_random_seed(seed)

        m = random_vector(GF(2), n)
        m.set_immutable()
        set_random_seed(hash(m))  # NOTE: this is obviously not faithful

        K_ = random_vector(GF(2), n)
        K_.set_immutable()
        r = ZZ.random_element(0, 2**n-1)

        c = cls.enc(pk, m, r)

        K = hash((K_, c))  # NOTE: this obviously isn't a cryptographic hash
        return c, K

    @classmethod
    def decap(cls, sk, pk, c):
        """IND-CCA decapsulation

        :param cls: Kyber class, inherit and change constants to change defaults
        :param sk: secret key
        :param pk: public key
        :param c: ciphertext

        .. note :: Resembles Algorithm 5 of the Kyber paper.

        """
        n = cls.n

        m = cls.dec(sk, c)
        m.set_immutable()
        set_random_seed(hash(m))  # NOTE: this is obviously not faithful

        K_ = random_vector(GF(2), n)
        K_.set_immutable()
        r = ZZ.random_element(0, 2**n-1)

        c_ = cls.enc(pk, m, r)

        if c == c_:
            return hash((K_, c))  # NOTE: this obviously isn't a cryptographic hash
        else:
            return hash(c)  # NOTE ignoring z


class MiniKyber(Kyber):
    """
    Tiny parameters for testing.
    """
    n = 8
    q = 127
    eta = 1
    k = 1
    f = [1]+[0]*(n-1)+[1]
    ce = n


class Nose:
    """
    Snorting (packing) and sneezing (unpacking).
    """

    @staticmethod
    def snort(g, f, p):
        """
        Convert vector `g` in `\ZZ^n` with coefficients bounded by `p/2` in absolute value to
        integer `\bmodp f(p)`.

        :param g: a vector of length `n`
        :param f: a minpoly
        :param p: base

        :returns: an integer mod `f(p)`
        """
        return g.change_ring(ZZ)(p) % f(p)

    @staticmethod
    def sneeze(G, f, p):
        """Convert integer `G \bmodl f(p)` to vector of integers

        :param G: an integer `\bmodl f(p)`
        :param f: a minpoly
        :param p: base

        """
        assert(G >= 0 and G < f(p))
        n = f.degree()
        c = 0
        r = []
        for i in range(n):
            e = G % p
            G -= e
            e += c
            G = G//p
            c = int(e > p//2)
            e -= c*p
            r.append(e)

        for i in range(n):
            r[i] -= f[i]*(G+c)

        return r[:n]

    @staticmethod
    def proof_sneeze(G, f, p):
        """Convert integer `G \bmod f(p)` to vector of integers

        :param G: an integer `\bmod f(p)`
        :param f: a minpoly
        :param p: base

        """
        assert(G >= 0 and G < f(p))
        n = f.degree()
        r = []
        for i in range(n):
            e = G % p
            G -= e
            G = G//p
            if e > p//2:
                e -= p
                G += 1
            r.append(e)

        for i in range(n):
            r[i] -= f[i]*G

        return r[:n]

    @classmethod
    def prec(cls, scheme):
        """
        Return `\log_2(k ce eta (q-1)/2 + (q-1)/2 + 1) + 1`

        1. eta q/2 is the upper bound on the product in absolute value
        2. We add ce such products during modular reduction
        3. We add up k such numbers when doing inner products
        4. We add a number of size eta in absolute value
        5. The modular reduction of the integer multiplier might add +/- max_i(|f_i|) to balance the output
        6. One sign bit

        """
        eta, q, k, f, ce = scheme.eta, scheme.q, scheme.k, scheme.f, scheme.ce
        l = log(k*ce*floor(q/ZZ(2))*eta + eta + max([abs(fi) for fi in f]) + 1, 2) + 1
        return l

    @classmethod
    def muladd(cls, scheme, a, b, c, l=None):
        """
        Compute `a \cdot b + c mod f` using big-integer arithmetic

        :param cls: Skipper class
        :param scheme: Scheme class, inherit and change constants to change defaults
        :param a: vector of polynomials in `ZZ_q[x]/(x^n+1)`
        :param b: vector of polynomials in `ZZ_q[x]/(x^n+1)`
        :param c: polynomial in `ZZ_q[x]/(x^n+1)`
        :param l: bits of precision

        """
        R, x = PolynomialRing(ZZ, "x").objgen()
        k, f = scheme.k, R(scheme.f)

        if l is None:
            l = ceil(cls.prec(scheme))

        A = vector(R, k, [cls.snort(a[j], f, 2**l) for j in range(k)])
        B = vector(R, k, [cls.snort(b[j], f, 2**l) for j in range(k)])
        C = cls.snort(c, f, 2**l)
        F = f(2**l)
        D = (A*B + C) % F
        d = cls.sneeze(D % F, f, 2**l)
        return R(d)


# Skipper

class Skipper4(Nose):
    """
    Kyber using big integer arithmetic

    IND-CPA Decryption in 30 multiplication of (64 \cdot 25 =) 1600-bit integers.

    - Degree 4 polynomial multiplication
    - Standard signed Kronecker substitution to pack 64 coefficients into one integer.

    """

    @staticmethod
    def ff(v, offset, start=0):
        """Fast-forward through vector `v` in ``offset`` sized steps starting at ``start``

        :param v: vector
        :param offset: increment in each step
        :param start: start offset

        """
        p = parent(v)
        return p(list(v)[start::offset])

    @classmethod  # TODO: n vs 2n expansion factor # TODO: tempted of getting rid of this
    def prec(cls, kyber):
        """
        Return `\log_2(k n eta (q-1)/2 + (q-1)/2 + 1) + 1`

        1. eta q/2 is the upper bound on the product in absolute value
        2. We add n such products during modular reduction          # TODO: n vs 2n
        3. We add up k such numbers when doing inner products
        4. We add a number of size eta in absolute value
        5. The modular reduction of the integer multiplier might add +/- max_i(|f_i|) to balance the output
        6. One sign bit

        """
        n, eta, q, k, f = kyber.n, kyber.eta, kyber.q, kyber.k, kyber.f
        l = log(k*n*floor(q/ZZ(2))*eta + eta + max([abs(fi) for fi in f]) + 1, 2) + 1
        return l

    @classmethod
    def muladd(cls, kyber, a, b, c, l=None):
        """
        Compute `a \cdot b + c` using big-integer arithmetic

        :param cls: Skipper class
        :param kyber: Kyber class, inherit and change constants to change defaults
        :param a: vector of polynomials in `ZZ_q[x]/(x^n+1)`
        :param b: vector of polynomials in `ZZ_q[x]/(x^n+1)`
        :param c: polynomial in `ZZ_q[x]/(x^n+1)`
        :param l: bits of precision

        """
        m, k = 4, kyber.k
        w = kyber.n//m
        R, x = PolynomialRing(ZZ, "x").objgen()
        f = R([1]+[0]*(w-1)+[1])

        if l is None:
            # Could try passing degree w, but would require more careful
            # sneezing
            l = ceil(cls.prec(kyber))

        R = PolynomialRing(ZZ, "x")
        x = R.gen()

        A = vector(R, k, [sum(cls.snort(cls.ff(a[j], m, i), f, 2**l) * x**i
                              for i in range(m))
                          for j in range(k)])

        C = sum(cls.snort(cls.ff(c, m, i), f, 2**l) * x**i for i in range(m))

        B = vector(R, k, [sum(cls.snort(cls.ff(b[j], m, i), f, 2**l) * x**i
                              for i in range(m))
                          for j in range(k)])

        F = f(2**l)

        # MUL: k * 3^2 (Karatsuba for length 4)
        # % F here is applied to the 64-coeff-packs.
        # k comes from len(A) = len(B) = k, each constrains
        # a deg 4 poly needing (recursive) karatsuba => 9
        W = (A*B + C) % F

        # MUL: 3
        # specific trick for how we multiply degree n = 256 polys
        # the coefficients from above need readjustment
        # here doing 2**l *  is basically doing y * !!! and if this wraps around
        # it takes care of the - in front
        W = sum((W[0+i] + (2**l * W[m+i] % F))*x**i for i in range(m-1)) + W[m-1]*x**(m-1)

        D = [cls.sneeze(W[i] % F, f, 2**l) for i in range(m)]

        d = []
        for j in range(w):
            for i in range(m):
                d.append(D[i][j])

        return R(d)

    @classmethod
    def enc(cls, kyber, pk, m=None, seed=None, l=None):
        """IND-CPA encryption sans compression

        :param kyber: Kyber class, inherit and change constants to change defaults
        :param pk: public key
        :param m: optional message, otherwise all zero string is encrypted
        :param seed: seed used for random sampling if provided

        """
        n, q, eta, k, D = kyber.n, kyber.q, kyber.eta, kyber.k, kyber.D

        if seed is not None:
            set_random_seed(seed)

        A, t = pk

        R = PolynomialRing(ZZ, "x")

        r  = vector(R, k, [R([(D(eta)) for _ in range(n)]) for _ in range(k)])
        e1 = vector(R, k, [R([(D(eta)) for _ in range(n)]) for _ in range(k)])
        e2 = R([(D(eta)) for _ in range(n)])

        if m is None:
            m = (0,)

        u = vector(R, [cls.muladd(kyber, r, A.column(i), e1[i], l=l) for i in range(k)])
        u.set_immutable()
        v = cls.muladd(kyber, r, t, e2 + q//2 * R(list(m)), l=l)
        return u, v

    @classmethod
    def dec(cls, kyber, sk, c, l=None, decode=True):
        """Decryption.

        :param kyber: Kyber class, inherit and change constants to change defaults
        :param sk: secret key
        :param c: ciphertext
        :param l: bits of precision
        :param decode: perform final decoding

        """
        n, q = kyber.n, kyber.q

        u, v = c
        s = sk

        m = -cls.muladd(kyber, s, u, -v, l=l)
        m = balance(vector(m), q)
        if decode:
            return kyber.decode(m, q, n)
        else:
            return m


class Skipper2Negated(Skipper4):
    """
    Kyber using big integer arithmetic

    IND-CPA Kyber Decryption in 20 multiplications of (128 \cdot 13 =) 1664-bit integers.

    - Degree 2 polynomial multiplication
    - Negated, signed Kronecker substitution to pack 128 coefficients into one integer.
    """

    @classmethod
    def prec(cls, kyber):
        """
        Return half the precision required by ``Skipper4``.

        :param kyber: Kyber class, inherit and change constants to change defaults

        """
        return Skipper4.prec(kyber)/ZZ(2)

    @classmethod
    def muladd(cls, kyber, a, b, c, l=None):
        """
        Compute `a \cdot b + c` using big-integer arithmetic

        :param cls: Skipper class
        :param kyber: Kyber class, inherit and change constants to change defaults
        :param a: vector of polynomials in `ZZ_q[x]/(x^n+1)`
        :param b: vector of polynomials in `ZZ_q[x]/(x^n+1)`
        :param c: polynomial in `ZZ_q[x]/(x^n+1)`
        :param l: bits of precision

        """
        m, k = 2, kyber.k
        w = kyber.n//m
        R, x = PolynomialRing(ZZ, "x").objgen()
        f = R([1]+[0]*(w-1)+[1])
        g = R([1]+[0]*(w//2-1)+[1])

        if l is None:
            l = ceil(cls.prec(kyber))

        R = PolynomialRing(ZZ, "x")
        x = R.gen()

        Ap = vector(R, k, [sum(cls.snort(cls.ff(a[j], m, i), f, 2**l) * x**i for i in range(m))
                           for j in range(k)])
        An = vector(R, k, [sum(cls.snort(cls.ff(a[j], m, i), f, -2**l) * x**i for i in range(m))
                           for j in range(k)])

        Cp = sum(cls.snort(cls.ff(c, m, i), f,  2**l) * x**i for i in range(m))
        Cn = sum(cls.snort(cls.ff(c, m, i), f, -2**l) * x**i for i in range(m))

        Bp = vector(R, k, [sum(cls.snort(cls.ff(b[j], m, i), f, 2**l) * x**i for i in range(m))
                           for j in range(k)])
        Bn = vector(R, k, [sum(cls.snort(cls.ff(b[j], m, i), f, -2**l) * x**i for i in range(m))
                           for j in range(k)])

        F = 2**(w * l) + 1

        # MUL: 2 * k * 3
        Wp = (Ap*Bp + Cp) % F
        Wn = (An*Bn + Cn) % F

        We = R(map(lambda x: x % F, Wp+Wn))
        Wo = R(map(lambda x: x % F, Wp-Wn))

        Wo, We = (sum((Wo[0+i] + (2**l * We[m+i] % F))*x**i for i in range(m-1)) + Wo[m-1]*x**(m-1)) % F, \
                 (sum((We[0+i] + (2**l * Wo[m+i] % F))*x**i for i in range(m-1)) + We[m-1]*x**(m-1)) % F

        _inverse_of_2_mod_F = F - 2**(w*l-1)
        _inverse_of_2_to_the_l_plus_1_mod_F = F - 2**(w*l-1-l)
        We = (We * _inverse_of_2_mod_F) % F
        Wo = (Wo * _inverse_of_2_to_the_l_plus_1_mod_F) % F

        D =  [cls.sneeze(We[i] % F, g, 2**(2*l)) for i in range(m)]
        D += [cls.sneeze(Wo[i] % F, g, 2**(2*l)) for i in range(m)]

        d = []

        for j in range(w//2):
            for i in range(2*m):
                d.append(D[i][j])

        return R(d)
