"""Test suite for Exclusion Arithmetic.  Run with `pytest` from the repo root."""

import math
import os
import random
import shutil
import subprocess
from itertools import product
from math import inf
from pathlib import Path

import pytest

from exclusion import eadd, emul, epow, g, normalize, v2, w
from exclusion.automata import (
    DFA3, DFA5, accepts, count_odd, dominant_root, equivalent, growth_rate,
    is_multiple_of_3, is_multiple_of_5, multiples_dfa, odd_members, rational_gf, runs,
    _tabulate, _step5, _accept5,
)
from exclusion.factor import (
    G, all_ones_lengths, divides, divisors, factorizations, g_tilde, gap_irreducible,
    has_stride_111, is_composite, is_irreducible, lengths, no111_exponent,
    odd_composites, quotients, top_gap_irreducible, verify_carry_bridge,
)

rng = random.Random(20261126)
SMALL = range(40)
ROOT = Path(__file__).resolve().parent.parent


def big(bits=300):
    return rng.getrandbits(rng.randint(0, bits))


def ones(k):
    """R_k = 1 + x + ... + x^(k-1)."""
    return (1 << k) - 1


# --- independent reference implementations (tests only) -----------------------

def eadd_carry_propagation(a, b):
    """Bitwise variant: a | b, then each unit of a & b rises to the next free bit."""
    r, d = a | b, a & b
    while d:
        t = d & -d
        m = r | t | (t - 1)
        r |= (m + 1) & ~m
        d ^= t
    return r


def emul_shift_add(a, b):
    """Distributivity: a [x] b = [+] over the bits k of a of (b << k)."""
    r, k = 0, 0
    while a >> k:
        if a >> k & 1:
            r = eadd_carry_propagation(r, b << k)
        k += 1
    return r


def rewrite_randomly(coefficients):
    """Apply 2 x^k -> x^k + x^(k+1) at random positions until none applies."""
    c = list(coefficients)
    while True:
        heavy = [k for k, v in enumerate(c) if v >= 2]
        if not heavy:
            return sum(v << k for k, v in enumerate(c))
        k = rng.choice(heavy)
        if k + 1 == len(c):
            c.append(0)
        c[k] -= 1
        c[k + 1] += 1


# --- Theorem 1: normal forms, the semiring, universal maps ---------------------

def test_small_values():
    assert [eadd(n, n) for n in range(12)] == [0, 3, 6, 15, 12, 15, 30, 63, 24, 27, 30, 63]
    assert [emul(n, n) for n in range(8)] == [0, 1, 4, 15, 16, 29, 60, 511]
    assert eadd(1, 1) == 3 and emul(3, 3) == emul(3, 5) == 15
    assert all(emul(2, n) == 2 * n for n in range(100))


def test_lindley_matches_carry_propagation():
    for a, b in product(range(256), repeat=2):
        assert eadd(a, b) == eadd_carry_propagation(a, b)
    for _ in range(3000):
        a, b = big(), big()
        assert eadd(a, b) == eadd_carry_propagation(a, b)


def test_bignum_product_matches_lindley_sums():
    for a, b in product(range(128), repeat=2):
        assert emul(a, b) == emul_shift_add(a, b)
    for _ in range(300):
        a, b = big(), big()
        assert emul(a, b) == emul_shift_add(a, b)
    for k in (64, 65, 200, 1000):  # densest carries, far beyond any machine word
        assert eadd(ones(k), ones(k)) == ones(2 * k)
        assert emul(ones(k), ones(7)) == ones(7 * k)
        assert emul(1 << k, 1 << k) == 1 << 2 * k


def test_normal_form_is_independent_of_rewriting_order():
    for _ in range(300):
        coeffs = [rng.randint(0, 4) for _ in range(rng.randint(1, 12))]
        expected = normalize(coeffs)
        assert all(rewrite_randomly(coeffs) == expected for _ in range(5))


def test_semiring_axioms_exhaustive():
    for a, b in product(SMALL, repeat=2):
        assert eadd(a, b) == eadd(b, a) and emul(a, b) == emul(b, a)
    for a in SMALL:
        assert eadd(a, 0) == a and emul(a, 1) == a and emul(a, 0) == 0
    for a, b, c in product(SMALL, repeat=3):
        assert eadd(eadd(a, b), c) == eadd(a, eadd(b, c))
        assert emul(emul(a, b), c) == emul(a, emul(b, c))
        assert emul(a, eadd(b, c)) == eadd(emul(a, b), emul(a, c))


def test_semiring_axioms_random_bignum():
    for _ in range(150):
        a, b, c = big(), big(), big()
        assert eadd(eadd(a, b), c) == eadd(a, eadd(b, c))
        assert emul(emul(a, b), c) == emul(a, emul(b, c))
        assert emul(a, eadd(b, c)) == eadd(emul(a, b), emul(a, c))


def test_epow():
    for a in range(20):
        p = 1
        for e in range(6):
            assert epow(a, e) == p
            p = emul(p, a)
    assert all(epow(3, k) == ones(2 ** k) for k in range(8))


def test_rejects_negative_arguments():
    for f in (eadd, emul):
        with pytest.raises(ValueError):
            f(-1, 3)
        with pytest.raises(ValueError):
            f(3, -1)


def test_superadditive_length():
    for a, b in product(range(1, 200), repeat=2):
        assert emul(a, b).bit_length() >= a.bit_length() + b.bit_length() - 1


# --- Theorem 1 (continued): w, v2, gap, finite quotients -----------------------

def test_weight_is_a_homomorphism_to_N():
    for a, b in product(range(200), repeat=2):
        assert w(eadd(a, b)) == w(a) + w(b)
        assert w(emul(a, b)) == w(a) * w(b)
    for _ in range(200):
        a, b = big(), big()
        assert w(eadd(a, b)) == w(a) + w(b) and w(emul(a, b)) == w(a) * w(b)


def test_v2_is_a_homomorphism_to_the_tropical_semiring():
    assert v2(0) == inf and v2(1) == 0 and v2(12) == 2
    for a, b in product(range(200), repeat=2):
        assert v2(eadd(a, b)) == min(v2(a), v2(b))
        assert v2(emul(a, b)) == v2(a) + v2(b)


def test_gap():
    assert [g(n) for n in (0, 1, 2, 3, 5, 12, 17, 40)] == [inf, inf, inf, 1, 2, 1, 4, 2]
    assert all(g(n) == v2(n - 1) for n in range(3, 500, 2))
    for a, b in product(range(1, 200), repeat=2):
        assert g(emul(a, b)) == min(g(a), g(b))


def test_truncation_mod_2_to_the_m_is_a_congruence():
    for m in range(1, 7):
        q = 1 << m
        for a, b in product(range(128), repeat=2):
            assert eadd(a, b) % q == eadd(a % q, b % q) % q
            assert emul(a, b) % q == emul(a % q, b % q) % q
    for _ in range(300):
        a, b, q = big(), big(), 1 << rng.randint(1, 200)
        assert eadd(a, b) % q == eadd(a % q, b % q) % q
        assert emul(a, b) % q == emul(a % q, b % q) % q


# --- Theorem 2: the unique prime, irreducibility lemmas, length sets -----------

def test_quotients_and_divisors_against_brute_force():
    limit = 128
    table = {}  # n -> {(d, c) : d [x] c = n}
    for d, c in product(range(1, limit), repeat=2):
        table.setdefault(emul(d, c), set()).add((d, c))
    for n in range(1, limit):
        pairs = table.get(n, set())
        for d in range(1, limit):
            expected = {c for dd, c in pairs if dd == d}
            assert quotients(n, d) == expected
            assert divides(d, n) == bool(expected)
        assert divisors(n) == sorted({d for d, _ in pairs})
    assert quotients(0, 5) == {0} and divides(0, 0) and not divides(0, 3)


def test_composites_three_ways():
    sieve = odd_composites(12)
    brute = {
        emul(a, b) for a in range(3, 1 << 11, 2) for b in range(a, 1 << 11, 2)
        if a.bit_length() + b.bit_length() <= 13
    }
    brute = {n for n in brute if n < 1 << 12}
    assert sieve == brute
    for n in range(1 << 12):
        expected = n >= 4 and (n % 2 == 0 or n in sieve)
        assert is_composite(n) == expected
        assert is_irreducible(n) == (n >= 2 and not expected)
    assert sorted(sieve)[:8] == [15, 27, 29, 45, 51, 63, 85, 89]


def test_odd_composite_counts():
    sieve = odd_composites(16)
    counts = [sum(1 for n in sieve if n.bit_length() == k) for k in range(1, 17)]
    assert counts == [0, 0, 0, 1, 2, 3, 8, 15, 29, 53, 108, 196, 337, 587, 1019, 1799]
    primes = {2, 3, 5, 7, 11, 13}
    assert not any(w(n) in primes for n in sieve)  # w(a [x] b) = w(a) w(b), so prime weight is irreducible


def test_factorizations():
    assert factorizations(1) == {()}
    assert factorizations(15) == {(3, 3), (3, 5)}
    assert factorizations(60) == {(2, 2, 3, 3), (2, 2, 3, 5)}
    for n in range(2, 600):
        fs = factorizations(n)
        assert fs
        for f in fs:
            assert all(is_irreducible(p) for p in f)
            prod = 1
            for p in f:
                prod = emul(prod, p)
            assert prod == n
        assert (fs == {(n,)}) == is_irreducible(n)


def test_two_is_prime_and_nothing_else_is():
    # 2 | a [x] b  iff  a [x] b is even  iff  a or b is even.
    for a, b in product(range(64), repeat=2):
        assert (emul(a, b) % 2 == 0) == (a % 2 == 0 or b % 2 == 0)
    # Every odd p > 1 divides a product R_w [x] R_m or q [x] R_m without
    # dividing either factor (w = w(p), q of weight w, m = 1 mod w large).
    for p in range(3, 200, 2):
        k = w(p)
        m = 2 * p.bit_length()
        m += (1 - m) % k
        a = ones(k) if p != ones(k) else ones(k - 1) | 1 << k
        assert emul(a, ones(m)) == ones(k * m) == emul(p, ones(m))  # so p | a [x] R_m
        assert w(a) == k and a != p and m % k == 1                  # weights: p divides neither
        assert not divides(p, a) and not divides(p, ones(m))


def test_repunits_multiply_like_integers():
    for a, b in product(range(1, 25), repeat=2):
        assert emul(ones(a), ones(b)) == ones(a * b)


# --- Theorem 2 (continued): Gap Lemma, Top-Gap Lemma, Carry-Bridge, elasticity ---

def test_gap_lemma_G_n_is_irreducible():
    composites = odd_composites(16)
    for n in range(2, 17):
        members = G(n)
        assert members == [m for m in range((1 << n - 1) + 1, 1 << n, 2) if gap_irreducible(m)]
        assert len(members) == 2 ** (n // 2 - 1)
        assert not composites.intersection(members)
    assert all(is_irreducible(m) for n in range(2, 13) for m in G(n))
    assert G(1) == [] and G(2) == [3] and G(6) == [33, 41, 49, 57]


def test_gap_lemma_is_sharp():
    for gap in range(2, 12):
        n = emul(1 | 1 << gap, 1 | 1 << gap)
        assert n == 1 | 1 << gap | 2 << gap | 1 << 2 * gap
        assert 2 * g(n) == n.bit_length() - 1 and not gap_irreducible(n)


def test_unbounded_elasticity():
    # R_(q 2^j) = P [x] R_q = 3^j [x] R_q with P = 1 + x^q R_(2^j - 1) irreducible.
    for j, q in ((1, 2), (2, 3), (3, 7), (4, 17), (5, 31)):
        P = 1 | ones(2 ** j - 1) << q
        assert gap_irreducible(P)
        assert emul(P, ones(q)) == ones(q * 2 ** j) == emul(epow(3, j), ones(q))
    assert is_irreducible(7) and is_irreducible(57)
    fs = factorizations(ones(12))  # j = 2, q = 3: lengths 2 and 3
    assert (7, 57) in fs and (3, 3, 7) in fs


def test_top_gap_lemma_sharpened():
    composites = odd_composites(16)
    flagged = [n for n in range(3, 1 << 16, 2) if top_gap_irreducible(n)]
    assert len(flagged) == 509 and not composites.intersection(flagged)
    assert all(is_irreducible(n) for n in flagged if n < 1 << 12)
    # 2h <= d cannot be relaxed to 2h <= d + 2: (1 + x^k)^2 = 1 + x^k + x^(k+1) + x^(2k).
    for k in range(2, 12):
        n = emul(1 | 1 << k, 1 | 1 << k)
        d = n.bit_length() - 1
        assert 2 * ((n ^ 1 << d).bit_length() - 1) == d + 2 and not top_gap_irreducible(n)
    assert not any(top_gap_irreducible(n) for n in (0, 1, 2, 6, 15, 27, 29))
    assert all(top_gap_irreducible(n) for n in (3, 5, 7, 9, 11, 17, 19, 39))


def test_g_tilde_and_carry_bridge():
    composites = odd_composites(16)
    assert [g_tilde(v) for v in range(2, 7)] == [3, 11, 39, 143, 543]
    for v in range(2, 200):
        assert w(g_tilde(v)) == v and top_gap_irreducible(g_tilde(v))
    assert not composites.intersection(g_tilde(v) for v in range(2, 10))
    assert all(verify_carry_bridge(u, v) for u, v in product(range(2, 51), repeat=2))
    assert not verify_carry_bridge(1, 5)  # u >= 2 is needed
    with pytest.raises(ValueError):
        g_tilde(1)


def test_length_sets_of_all_ones():
    def predicted(m):  # {1} for m prime, {2, ..., Omega(m)} otherwise
        omega, k, p = 0, m, 2
        while k > 1:
            while k % p == 0:
                omega, k = omega + 1, k // p
            p += 1
        return {1} if omega == 1 else set(range(2, omega + 1))

    for m in range(2, 17):
        assert all_ones_lengths(m) == predicted(m)
    assert all_ones_lengths(8) == {2, 3} and all_ones_lengths(16) == {2, 3, 4}
    for n in range(1, 400):  # lengths() agrees with the listed factorisations
        assert lengths(n) == {len(f) for f in factorizations(n)}
    # One-line infinite elasticity: R_(2^k) = 3^k = 3 [x] G~_(2^(k-1)).
    for k in range(2, 9):
        assert epow(3, k) == emul(3, g_tilde(1 << k - 1)) == ones(1 << k)


# --- Theorem 3: multiples of a fixed element form a regular language -------------

def odd_multiples_by_length(a, nmax):
    """sets[n] = odd n-bit multiples of a, from the products a [x] b themselves."""
    sets = [set() for _ in range(nmax + 1)]
    for b in range(1, 1 << nmax - a.bit_length() + 1, 2):
        p = emul(a, b)
        if p.bit_length() <= nmax:
            sets[p.bit_length()].add(p)
    return sets


def test_runs():
    assert runs(0b1011100111) == ([3, 3, 1], [2, 1])
    assert runs(1) == ([1], [])


def test_multiples_of_3_have_even_runs_and_fibonacci_counts():
    nmax = 18
    sets = odd_multiples_by_length(3, nmax)
    fib = [0, 1]
    while len(fib) < nmax:
        fib.append(fib[-1] + fib[-2])
    for n in range(3, nmax + 1):
        assert sets[n] == {m for m in range((1 << n - 1) + 1, 1 << n, 2) if is_multiple_of_3(m)}
        assert sorted(sets[n]) == odd_members(DFA3, n)
        assert len(sets[n]) == fib[n - 3]
    c = count_odd(DFA3, 60)
    assert c[3:5] == [0, 1] and all(c[n] == c[n - 1] + c[n - 2] for n in range(5, 61))


def test_multiples_of_5_set_equality():
    nmax = int(os.environ.get("EXCLUSION_NMAX", 20))
    sets = odd_multiples_by_length(5, nmax)
    for n in range(1, nmax + 1):
        assert sorted(sets[n]) == odd_members(DFA5, n)
    for n in range(1, min(nmax, 18) + 1):  # the run criterion, literally, on every odd n-bit integer
        assert sets[n] == {m for m in range((1 << n - 1) + 1, 1 << n, 2) if is_multiple_of_5(m)}
    D = [len(s) for s in sets]
    assert D[1:13] == [0, 0, 1, 1, 1, 2, 3, 6, 10, 17, 29, 49]
    assert all(D[n] == D[n - 1] + D[n - 2] + D[n - 5] for n in range(6, nmax + 1))


def test_recognisers_agree_with_their_dfas():
    for n in range(1 << 16):
        assert is_multiple_of_3(n) == accepts(DFA3, n)
        assert is_multiple_of_5(n) == accepts(DFA5, n)
    for n in range(1 << 11):
        assert is_multiple_of_3(n) == divides(3, n)
        assert is_multiple_of_5(n) == divides(5, n)


def test_certificate_proves_both_characterisations():
    assert equivalent(DFA3, multiples_dfa(1))
    assert equivalent(DFA5, multiples_dfa(2))
    assert len(multiples_dfa(2)[0]) == 7  # six live states and a sink


def test_certificate_rejects_wrong_characterisations():
    assert not equivalent(DFA3, DFA5)
    # Forbid only run length 2 (not 3) in condition (3):
    def wrong_step(q, bit):
        if q is not None and q[0] == "run" and not bit and q[1] == 0 and q[2] == 3:
            return ("gap", q[1] ^ q[3], 1)
        return _step5(q, bit)

    assert not equivalent(_tabulate(("lead",), wrong_step, _accept5), multiples_dfa(2))
    # Drop condition (2) altogether:
    def lax_step(q, bit):
        if q is not None and q[0] == "gap" and q[1] == 1 and not bit:
            return ("gap", 1, 2)
        return _step5(q, bit)

    assert not equivalent(_tabulate(("lead",), lax_step, _accept5), multiples_dfa(2))


def test_recurrence_and_generating_function_for_D5():
    nmax = 200
    D = count_odd(DFA5, nmax)
    assert D[1:6] == [0, 0, 1, 1, 1]
    assert all(D[n] == D[n - 1] + D[n - 2] + D[n - 5] for n in range(6, nmax + 1))
    # Power series of z^3 (1 - z^2) / (1 - z - z^2 - z^5).
    num = [0, 0, 0, 1, 0, -1] + [0] * nmax
    series = []
    for n in range(nmax + 1):
        series.append(num[n] + sum(series[n - k] for k in (1, 2, 5) if n >= k))
    assert series == D


def test_multiples_of_9_and_17_are_regular_too():
    for s, a in ((3, 9), (4, 17)):
        dfa = multiples_dfa(s)
        sets = odd_multiples_by_length(a, 16)
        for n in range(1, 17):
            assert sorted(sets[n]) == odd_members(dfa, n)
        assert count_odd(dfa, 16) == [len(x) for x in sets]


def test_exact_growth_rates_of_the_multiples_of_1_plus_2_to_the_r():
    expected = {1: "0.694241", 2: "0.769689", 3: "0.791046", 4: "0.799703", 5: "0.803880"}
    orders = {1: 2, 2: 5, 3: 18, 4: 50, 5: 172}
    for r, digits in expected.items():
        dfa = multiples_dfa(r)
        counts = count_odd(dfa, 4 * len(dfa[0]) + 40)
        num, den = rational_gf(counts)
        assert len(den) - 1 == orders[r]
        lam, gamma = growth_rate(dfa)
        assert str(gamma).startswith(digits)
        assert abs(float(lam) - counts[-1] / counts[-2]) < 1e-9
    assert rational_gf(count_odd(DFA5, 40)) == ([0, 0, 0, 1, 0, -1], [1, -1, -1, 0, 0, -1])
    assert rational_gf(count_odd(multiples_dfa(3), 100)) == (
        [0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1, 0, 2, 2, -1, 0, -1, 1, -1],
        [1, -1, -1, -1, 1, 0, 1, -2, -1, 0, 2, 2, 0, -1, -1, 0, -1, 0, -1],
    )
    assert str(dominant_root([1, -1, -1])).startswith("1.61803398874989484820")
    with pytest.raises(ValueError):
        rational_gf(count_odd(multiples_dfa(3), 30))  # too few terms for order 18


def test_multiples_are_supermultiplicative():
    # N1 (i bits) and N2 (j bits) multiples => N1 + 2^i N2 is one: gamma_a exists (Fekete).
    for r in (1, 2, 3, 4):
        D = count_odd(multiples_dfa(r), 60)
        assert all(D[i + j] >= D[i] * D[j] for i in range(1, 31) for j in range(1, 31))


# --- Theorem 4: density of the composites; the C engine ---------------------------

def exchange(b, r):
    """Move the middle bit of the highest stride-r triple of b one place up, and normalise."""
    i = (b & b >> r & b >> 2 * r).bit_length() - 1 + r
    return eadd(b ^ 1 << i, 2 << i)


def test_no_111_in_the_maximal_cofactor():
    nmax = 18
    total = 0
    for r in range(1, 9):
        a, best = 1 | 1 << r, {}
        for b in range(1, 1 << nmax - r, 2):
            p = emul(a, b)
            if p.bit_length() <= nmax:
                best[p] = max(best.get(p, 0), b)
                if has_stride_111(b, r) and b < 1 << 11:
                    c = exchange(b, r)  # the algebraic exchange: same product, larger cofactor
                    assert c > b and emul(a, c) == p
        assert not any(has_stride_111(b, r) for b in best.values())
        if r == 1:  # for 3 the maximal cofactor is fibbinary: N = 3 b*
            assert all(b & b >> 1 == 0 and 3 * b == p for p, b in best.items())
        total += len(best)
    assert total == 13154
    assert has_stride_111(0b10101, 2) and not has_stride_111(0b10101, 1)
    # the exchange is an identity of S: (1+x^r)(1+x^r+x^2r) = (1+x^r)(1+x^(r+1)+x^2r)
    for r in range(1, 40):
        a = 1 | 1 << r
        assert emul(a, 1 | 1 << r | 1 << 2 * r) == emul(a, eadd(1 | 1 << 2 * r, 2 << r))


def test_weighted_no_111_upper_bound():
    x, theta, E = no111_exponent()
    assert (f"{x:.6f}", f"{theta:.6f}", f"{E:.6f}") == ("0.808173", "0.705340", "0.874665")

    def H(t):
        return -t * math.log2(t) - (1 - t) * math.log2(1 - t)

    assert abs(H(theta) - E) < 1e-9                          # the two bounds cross at theta
    assert abs(H(1 / 4) - 0.811278) < 1e-6 < E - H(1 / 4)    # composites without a weight-2 factor
    # exact counts: strings of length L without 111, by weight, against the entropy bound
    L = 600
    by_tail = [[1], [0], [0]]
    for k in range(1, L + 1):
        z = [p + q + s for p, q, s in zip(*[t + [0] * (k + 1 - len(t)) for t in by_tail])]
        by_tail = [z, [0] + by_tail[0], [0] + by_tail[1]]
    no111 = [p + q + s for p, q, s in zip(*[t + [0] * (L + 2 - len(t)) for t in by_tail])]
    best = max(min(math.comb(L, W), no111[W // 2]) for W in range(2, L, 2))
    assert E - 0.01 < math.log2(best) / L < E
    # lower bound from the certified automaton for a = 65, upper bound E
    gamma65 = float(growth_rate(multiples_dfa(6))[1])
    assert f"{gamma65:.6f}" == "0.806113" and gamma65 < E


# --- the C engine -----------------------------------------------------------------

@pytest.fixture(scope="module")
def engine(tmp_path_factory):
    cc = shutil.which("cc") or shutil.which("gcc")
    if not cc:
        pytest.skip("no C compiler")
    exe = tmp_path_factory.mktemp("c") / "count_composites"
    src = ROOT / "src" / "c" / "count_composites.c"
    subprocess.run([cc, "-std=c11", "-O2", str(src), "-o", str(exe)], check=True)

    def run(*args):
        out = subprocess.run([str(exe), *map(str, args)], check=True, capture_output=True, text=True)
        return [int(line.split()[1]) for line in out.stdout.splitlines()]

    try:
        run(1)  # the build is fine; can the binary be launched at all?
    except OSError as error:  # e.g. WinError 4551: an application-control policy blocks fresh binaries
        pytest.skip(f"C engine built but the system refuses to run it: {error}")
    return run


def test_c_engine_matches_python(engine):
    sieve = odd_composites(16)
    assert engine(16) == [sum(1 for n in sieve if n.bit_length() == k) for k in range(1, 17)]
    assert engine(20, 5) == count_odd(DFA5, 20)[1:]
    assert engine(20, 3) == count_odd(DFA3, 20)[1:]
    assert engine(20, 9) == count_odd(multiples_dfa(3), 20)[1:]
    for a in (7, 11, 21):
        sets = odd_multiples_by_length(a, 14)
        assert engine(14, a) == [len(s) for s in sets[1:]]


def test_c_engine_lower_bound(engine):
    C, D = engine(24), engine(24, 5)
    assert all(d <= c for c, d in zip(C[3:], D[3:]))  # D_5(n) <= C(n) for n >= 4
    assert (C[2], D[2]) == (0, 1)                     # 5 itself is irreducible
