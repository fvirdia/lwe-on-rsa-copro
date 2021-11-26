# -*- coding: utf-8 -*-

from sage.all import random_vector, GF, ceil, PolynomialRing
from sage.all import vector, randint, set_random_seed, ZZ, FreeModule

import sys
sys.path.append(".")  # HACK

from poc import MiniKyber, Kyber, Nose, Skipper2Negated, Skipper4, BinomialDistribution


class PseudoLima:
    n = 1018
    q = 12521473
    eta = 8  # ~ 12 * 3.16
    k = 1
    f = [1]*(n+1)
    ce = 2*n-1


class MiniPseudoLima:
    n = 4
    q = 113
    eta = 1
    k = 1
    f = [1]*(n+1)
    ce = 2*n-1


def test_kyber_cpa(cls=Kyber, t=16):
    """
    Test correctness of IND-CPA encryption/decryption.

    TESTS::

        sage: test_kyber_cpa(Kyber)
        sage: test_kyber_cpa(MiniKyber)

    .. note :: An ``AssertionError`` if decrypted plaintext does not match original.

    """
    for i in range(t):
        pk, sk = cls.key_gen(seed=i)
        m0 = random_vector(GF(2), cls.n)
        c = cls.enc(pk, m0, seed=i)
        m1 = cls.dec(sk, c)
        assert(m0 == m1)


def test_kyber_cca(cls=Kyber, t=16):
    """
    Test correctness of IND-CCA encapsulation/decapsulation.

    TESTS::

        sage: test_kyber_cca(Kyber)
        sage: test_kyber_cca(MiniKyber)

    .. note :: An ``AssertionError`` if final key does not match original.

    """
    for i in range(t):
        pk, sk = cls.key_gen(seed=i)
        c, K0 = cls.encap(pk, seed=i)
        K1 = cls.decap(sk, pk, c)
        assert(K0 == K1)


def test_kyber(cls=Kyber, t=16):
    """
    Test correctness of Kyber implementation.

    TESTS::

        sage: test_kyber(Kyber)
        <Kyber> CPA pass
        <Kyber> CCA pass

        sage: test_kyber(MiniKyber)
        <MiniKyber> CPA pass
        <MiniKyber> CCA pass

    """
    print("<%s> CPA"%(cls.__name__), end=" ")
    sys.stdout.flush()
    test_kyber_cpa(cls, t)
    print("pass")
    print("<%s> CCA"%(cls.__name__), end=" ")
    sys.stdout.flush()
    test_kyber_cca(cls, t)
    print("pass")


def test_nose(cls=Kyber, l=None, t=128, seed=0xdeadbeef, proof=False, worst_case=True):
    """
    Test correctness of the Sneeze/Snort gadget for normal form MLWE parameters.

    TESTS::

        sage: test_nose(MiniKyber)
        sage: test_nose(MiniPseudoLima, seed=1, worst_case=False)
        sage: test_nose(MiniKyber, l = Nose.prec(MiniKyber)-1)
        Traceback (most recent call last):
        ...
        AssertionError
        sage: test_nose(MiniPseudoLima, l = Nose.prec(MiniPseudoLima)-1, seed=1, worst_case=False)
        Traceback (most recent call last):
        ...
        AssertionError

    .. note :: An ``AssertionError`` if final key does not match original.

    """
    if seed is not None:
        set_random_seed(seed)

    R, x = PolynomialRing(ZZ, "x").objgen()
    D = BinomialDistribution
    # TODO ce
    n, q, eta, k, f = cls.n, cls.q, cls.eta, cls.k, R(cls.f)
    Rq = PolynomialRing(GF(q), "x")

    if not l:
        l = Nose.prec(cls)
    l = ceil(l)

    for _ in range(t):
        if worst_case:
            a = vector(Rq, k, [[q//2 + randint(0, 1)        for _ in range(n)] for i in range(k)])  # noqa
            s = vector(R,  k, [[((-1)**randint(0, 1)) * eta for _ in range(n)] for i in range(k)])
            e = R([((-1)**randint(0, 1)) * eta for _ in range(n)])
        else:
            a = vector(Rq, k, [Rq.random_element(degree=n-1) for i in range(k)])
            s = vector(R,  k, [[D(eta) for _ in range(n)] for i in range(k)])
            e = R([D(eta) for _ in range(n)])
        b = (a*s + e)  % f

        bb = Rq(Nose.muladd(cls, a, s, e, l=l))

        assert(b == bb)


def test_skipper_prec(skipper=Skipper4, kyber=Kyber, l=None):
    """Test precision prediction by construction worst case instance (?)

    :param skipper: Skipper instance
    :param kyber: Kyber instance for parameters such as `n` and `q`
    :param l: bits of precision to use

    TESTS::

        sage: test_skipper_prec(Skipper4, Kyber)
        sage: l = ceil(Skipper4.prec(Kyber)) - 1
        sage: test_skipper_prec(Skipper4, Kyber, l=l)
        Traceback (most recent call last):
        ...
        AssertionError

        sage: test_skipper_prec(Skipper2Negated, Kyber)
        sage: l = ceil(Skipper2Negated.prec(Kyber)) - 1
        sage: test_skipper_prec(Skipper2Negated, Kyber, l=l)
        Traceback (most recent call last):
        ...
        AssertionError

    """
    n, q, k, eta = kyber.n, kyber.q, kyber.k, kyber.eta
    R, x = PolynomialRing(ZZ, "x").objgen()
    f = R(kyber.f)

    # attempt to construct a worst-case instance
    a = vector(R, k, [R([q//2 for _ in range(n)]) for _ in range(k)])
    b = vector(R, k, [R([eta for _ in range(n)]) for _ in range(k)])
    c = R([eta for _ in range(n)])

    d0 = (a*b + c) % f
    d1 = skipper.muladd(kyber, a, b, c, l=l)
    assert(d0 == d1)


def test_skipper_cpa_dec(skipper=Skipper4, kyber=Kyber, t=128, l=None, exhaustive=False):
    if not exhaustive:
        for i in range(t):
            pk, sk = kyber.key_gen(seed=i)
            m0 = random_vector(GF(2), kyber.n)
            c = kyber.enc(pk, m0, seed=i)
            m1 = skipper.dec(kyber, sk, c, l=l)
            assert(m0 == m1)
    else:
        # exhaustive test
        for i in range(16):
            pk, sk = kyber.key_gen(seed=i)
            for m0 in FreeModule(GF(2), kyber.n):
                c = kyber.enc(pk, m0, seed=i)
                m1 = skipper.dec(kyber, sk, c, l=l)
                assert(m0 == m1)


def test_skipper_cpa_enc(skipper=Skipper4, kyber=Kyber, t=128, l=None, exhaustive=False):
    if not exhaustive:
        for i in range(t):
            pk, sk = kyber.key_gen(seed=i)
            m0 = random_vector(GF(2), kyber.n)
            c = skipper.enc(kyber, pk, m0, seed=i, l=l)
            m1 = kyber.dec(sk, c)
            assert(m0 == m1)
    else:
        # exhaustive test
        for i in range(16):
            pk, sk = kyber.key_gen(seed=i)
            for m0 in FreeModule(GF(2), kyber.n):
                c = skipper.enc(kyber, pk, m0, seed=i, l=l)
                m1 = kyber.dec(sk, c)
                assert(m0 == m1)


def test_minus_one(skipper=Skipper4, kyber=Kyber, t=16, l=None):
    """
    This test makes sense if one is using the appropriate full bitlength.
    In the case of skipped terms (say S4 using w as degree, or S2N), then one
    may need to implement a harder check
    """

    R, x = PolynomialRing(ZZ, "x").objgen()

    if skipper == Skipper2Negated:
        m = 2
        w = kyber.n//m
        f = R([1]+[0]*(w-1)+[1])
    else:
        f = R(kyber.f)

    if not l:
        l = ceil(skipper.prec(kyber))
    p = 2**l

    for i in range(t):
        a = R([-i]+[0]*(kyber.n-1))
        A = skipper.snort(a, f, p)
        aa = R(skipper.sneeze(A, f, p))
        assert (aa == a)

        A = -i % f(p)
        a = R(skipper.sneeze(A, f, p))
        AA = skipper.snort(a, f, p)
        assert (A == AA)


def test_skipper(skipper=Skipper4, kyber=Kyber, t=128, l=None):
    """
    :param skipper: Skipper instance
    :param kyber: Kyber instance for parameters such as `n` and `q`
    :param t: number of trials
    :param l: bits of precision to use

    TESTS::

        sage: test_skipper(Skipper4, MiniKyber)
        <Skipper4> Prec: 10, ell: None
        <Skipper4> -1 pass
        <Skipper4> Worst case pass
        <Skipper4> Dec pass
        <Skipper4> Enc pass

        sage: test_skipper(Skipper4, Kyber)
        <Skipper4> Prec: 25, ell: None
        <Skipper4> -1 pass
        <Skipper4> Worst case pass
        <Skipper4> Dec pass
        <Skipper4> Enc pass

        sage: test_skipper(Skipper2Negated, MiniKyber)
        <Skipper2Negated> Prec:  5, ell: None
        <Skipper2Negated> -1 pass
        <Skipper2Negated> Worst case pass
        <Skipper2Negated> Dec pass
        <Skipper2Negated> Enc pass

        sage: test_skipper(Skipper2Negated, Kyber)
        <Skipper2Negated> Prec: 13, ell: None
        <Skipper2Negated> -1 pass
        <Skipper2Negated> Worst case pass
        <Skipper2Negated> Dec pass
        <Skipper2Negated> Enc pass

    """
    print("<%s> Prec: %2d, ell: %s"%(skipper.__name__, ceil(skipper.prec(kyber)), l), end=" ")
    print("<%s> -1"%(skipper.__name__), end=" ")
    sys.stdout.flush()
    test_minus_one(skipper, kyber, l=l)
    print("pass")
    print("<%s> Worst case"%(skipper.__name__), end=" ")
    sys.stdout.flush()
    test_skipper_prec(skipper, kyber, l=l)
    print("pass")
    print("<%s> Dec"%(skipper.__name__), end=" ")
    sys.stdout.flush()
    test_skipper_cpa_dec(skipper, kyber, t, l=l)
    print("pass")
    print("<%s> Enc"%(skipper.__name__), end=" ")
    sys.stdout.flush()
    test_skipper_cpa_enc(skipper, kyber, t, l=l)
    print("pass")
