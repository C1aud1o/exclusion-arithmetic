#!/usr/bin/env python3
"""Reproduce every table and re-check Theorems 1-4 of the README.

    python scripts/verify_theorems.py [--nmax 24] [--cmax 31]

--nmax  bit length up to which multiples of 3 and 5 are compared, as sets, with
        the products a [x] b themselves (the brute-force audit of Theorem 3).
--cmax  bit length up to which the C engine counts composites (Theorem 4);
        memory 2^(cmax-4) bytes.  If the engine cannot be built or run, the
        counts committed in oeis/bfiles/b_count_odd_composites.txt are used
        and compared with the Python sieve as far as that reaches.

Exit status 0 iff every check passes.
"""

import argparse
import shutil
import subprocess
import sys
import tempfile
import time
from decimal import Decimal, localcontext
from itertools import product
from math import comb, log2
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))

from exclusion import eadd, emul, epow, g, v2, w  # noqa: E402
from exclusion.automata import (  # noqa: E402
    DFA3, DFA5, count_odd, dominant_root, equivalent, is_multiple_of_3, is_multiple_of_5,
    multiples_dfa, odd_members, rational_gf,
)
from exclusion.factor import (  # noqa: E402
    G, all_ones_lengths, factorizations, g_tilde, gap_irreducible, has_stride_111,
    no111_exponent, odd_composites, quotients, top_gap_irreducible, verify_carry_bridge,
)

failures = []


def check(label, ok):
    print(f"  [{'PASS' if ok else 'FAIL'}] {label}")
    if not ok:
        failures.append(label)


def section(title):
    print(f"\n{title}\n{'-' * len(title)}")
    return time.perf_counter()


def done(t0):
    print(f"  ({time.perf_counter() - t0:.1f} s)")


def ones(k):
    return (1 << k) - 1


_exe = None


def engine(*args):
    """Output of the C engine as a list [value for n = 1..N], or None if it cannot be built."""
    global _exe
    if _exe is None:
        cc = shutil.which("cc") or shutil.which("gcc") or shutil.which("clang")
        _exe = False
        if cc:
            exe = Path(tempfile.mkdtemp()) / "count_composites"
            src = ROOT / "src" / "c" / "count_composites.c"
            for flags in (["-fopenmp"], []):
                cmd = [cc, "-std=c11", "-O3", *flags, str(src), "-o", str(exe)]
                if subprocess.run(cmd, capture_output=True).returncode == 0:
                    _exe = exe
                    break
    if not _exe:
        return None
    try:
        out = subprocess.run([str(_exe), *map(str, args)], check=True, capture_output=True, text=True)
    except OSError as error:  # e.g. an application-control policy refusing a fresh binary
        print(f"  C engine built but cannot be run here: {error}")
        _exe = False
        return None
    return [int(line.split()[1]) for line in out.stdout.splitlines()]


def committed_counts():
    """C(1), C(2), ... as committed in the b-file (produced by the C engine)."""
    path = ROOT / "oeis" / "bfiles" / "b_count_odd_composites.txt"
    return [int(line.split()[1]) for line in path.read_text().splitlines()] if path.exists() else []


def theorem1():
    t0 = section("Theorem 1  (semiring structure: normal forms and the Lindley recursion)")
    R = range(32)
    check("commutativity, identities 0 and 1, absorbing 0   (a, b < 32)", all(
        eadd(a, b) == eadd(b, a) and emul(a, b) == emul(b, a) for a, b in product(R, R)
    ) and all(eadd(a, 0) == a and emul(a, 1) == a and emul(a, 0) == 0 for a in R))
    check("associativity of [+] and [x], distributivity      (a, b, c < 32)", all(
        eadd(eadd(a, b), c) == eadd(a, eadd(b, c))
        and emul(emul(a, b), c) == emul(a, emul(b, c))
        and emul(a, eadd(b, c)) == eadd(emul(a, b), emul(a, c))
        for a, b, c in product(R, R, R)
    ))
    check("1 [+] 1 = 3,  2 [x] n = 2n,  a [+] b >= a + b,  a [x] b >= a b   (a, b < 256)", (
        eadd(1, 1) == 3 and all(emul(2, n) == 2 * n for n in range(256))
        and all(eadd(a, b) >= a + b and emul(a, b) >= a * b for a, b in product(range(256), repeat=2))
    ))
    check("a [+] b = a + b iff a AND b = 0                    (a, b < 256)", all(
        (eadd(a, b) == a + b) == (a & b == 0) for a, b in product(range(256), repeat=2)
    ))
    check("len(a [x] b) >= len a + len b - 1                  (0 < a, b < 256)", all(
        emul(a, b).bit_length() >= a.bit_length() + b.bit_length() - 1
        for a, b in product(range(1, 256), repeat=2)
    ))
    check("R_a [x] R_b = R_ab for R_k = 2^k - 1               (a, b <= 24)", all(
        emul(ones(a), ones(b)) == ones(a * b) for a, b in product(range(1, 25), repeat=2)
    ))
    print("\n  a [+] b                          a [x] b")
    for a in range(8):
        print("  " + " ".join(f"{eadd(a, b):3d}" for b in range(8))
              + "    " + " ".join(f"{emul(a, b):3d}" for b in range(8)))
    done(t0)


def theorem2():
    t0 = section("Theorem 1, continued  (universal maps w and v2; residual finiteness)")
    R = range(256)
    check("w(a [+] b) = w(a) + w(b),  w(a [x] b) = w(a) w(b)        (a, b < 256)", all(
        w(eadd(a, b)) == w(a) + w(b) and w(emul(a, b)) == w(a) * w(b) for a, b in product(R, R)
    ))
    check("v2(a [+] b) = min(v2 a, v2 b),  v2(a [x] b) = v2 a + v2 b  (a, b < 256)", all(
        v2(eadd(a, b)) == min(v2(a), v2(b)) and v2(emul(a, b)) == v2(a) + v2(b)
        for a, b in product(R, R)
    ))
    check("reduction mod 2^m is a congruence for [+] and [x]         (m <= 6, a, b < 128)", all(
        eadd(a, b) % q == eadd(a % q, b % q) % q and emul(a, b) % q == emul(a % q, b % q) % q
        for q in (2, 4, 8, 16, 32, 64) for a, b in product(range(128), repeat=2)
    ))
    done(t0)


def theorem3():
    t0 = section("Theorem 2  (2 is the unique prime; S is not cancellative)")
    check("2 | a [x] b  iff  2 | a or 2 | b                          (a, b < 256)", all(
        (emul(a, b) % 2 == 0) == (a % 2 == 0 or b % 2 == 0) for a, b in product(range(256), repeat=2)
    ))
    check("3 [x] 3 = 3 [x] 5 = 15,   7 [x] 7 = 11 [x] 11 = 511", (
        emul(3, 3) == emul(3, 5) == 15 and emul(7, 7) == emul(11, 11) == 511
    ))
    ok = True
    for p in range(3, 1 << 10, 2):
        k = w(p)
        m = 2 * p.bit_length()
        m += (1 - m) % k
        a = ones(k) if p != ones(k) else ones(k - 1) | 1 << k
        # p | a [x] R_m = R_km, while p divides neither a (same weight, a != p)
        # nor R_m (w(p) does not divide m).
        ok &= emul(p, ones(m)) == ones(k * m) == emul(a, ones(m))
        ok &= w(a) == k and a != p and m % k == 1
        if p < 64:
            ok &= not quotients(a, p) and not quotients(ones(m), p)
    check("every odd p, 3 <= p < 1024, fails primality on an explicit product", ok)
    done(t0)


def theorem4(composites, nbits):
    t0 = section("Theorem 2, continued  (Gap and Top-Gap Lemmas, Carry-Bridge, length sets of 2^m - 1)")
    check("g(a [x] b) = min(g(a), g(b))                               (0 < a, b < 256)", all(
        g(emul(a, b)) == min(g(a), g(b)) for a, b in product(range(1, 256), repeat=2)
    ))
    check(f"G_n contains no composite and |G_n| = 2^(floor(n/2)-1)      (n <= {nbits})", all(
        len(G(n)) == 2 ** (n // 2 - 1) and not composites.intersection(G(n))
        and all(gap_irreducible(m) for m in G(n))
        for n in range(2, nbits + 1)
    ))
    check("sharpness: (1+x^k)^2 = 1+x^k+x^(k+1)+x^(2k) has 2g = len-1   (2 <= k <= 40)", all(
        emul(1 | 1 << k, 1 | 1 << k) == 1 | 3 << k | 1 << 2 * k for k in range(2, 41)
    ))
    ok = True
    for j, q in ((1, 2), (2, 3), (3, 7), (4, 17), (5, 31), (6, 67), (7, 127)):
        P = 1 | ones(2 ** j - 1) << q
        ok &= gap_irreducible(P) and w(ones(q)) == q  # R_q has prime weight q
        ok &= emul(P, ones(q)) == ones(q << j) == emul(epow(3, j), ones(q))
    check("R_(q 2^j) = P_j [x] R_q = 3^j [x] R_q: lengths 2 and j+1     (j <= 7)", ok)
    fs = factorizations(ones(12))
    check("factorisations of R_12 = 4095 include 7 [x] 57 and 3 [x] 3 [x] 7", (7, 57) in fs and (3, 3, 7) in fs)
    print(f"  R_12 has {len(fs)} factorisations, of lengths {sorted({len(f) for f in fs})}")

    flagged = [n for n in range(3, 1 << nbits, 2) if top_gap_irreducible(n)]
    check(f"Top-Gap Lemma: all {len(flagged)} odd n < 2^{nbits} with 2h <= d are irreducible",
          not composites.intersection(flagged))
    check("G~_v = (2^(v-1) - 1) + 2^(2v-3) has weight v and passes the Top-Gap test   (2 <= v <= 500)",
          all(w(g_tilde(v)) == v and top_gap_irreducible(g_tilde(v)) for v in range(2, 501)))
    check("Carry-Bridge: R_u [x] G~_v = R_uv                                      (2 <= u, v <= 50)",
          all(verify_carry_bridge(u, v) for u, v in product(range(2, 51), repeat=2)))

    def predicted(m):
        omega, k, p = 0, m, 2
        while k > 1:
            while k % p == 0:
                omega, k = omega + 1, k // p
            p += 1
        return {1} if omega == 1 else set(range(2, omega + 1))

    print("\n   m   exact length set of R_m = 2^m - 1   {1} or {2..Omega(m)}")
    ok = True
    for m in (4, 6, 8, 9, 10, 12, 14, 15, 16, 18):
        exact = all_ones_lengths(m)
        ok &= exact == predicted(m)
        print(f"  {m:2d}   {str(sorted(exact)):33s}   {sorted(predicted(m))}")
    check("L(2^m - 1) = {2, ..., Omega(m)} for composite m, {1} for prime m      (m <= 18)",
          ok and all(all_ones_lengths(m) == {1} for m in (2, 3, 5, 7, 11, 13, 17)))
    check("one-line elasticity: 2^(2^k) - 1 = 3^k = 3 [x] G~_(2^(k-1))             (2 <= k <= 10)",
          all(epow(3, k) == emul(3, g_tilde(1 << k - 1)) == ones(1 << k) for k in range(2, 11)))
    done(t0)


def theorem5(nmax):
    t0 = section(f"Theorem 3  (multiples of a fixed element are regular; audit of 3 and 5 for n <= {nmax})")
    sets = {3: [set() for _ in range(nmax + 1)], 5: [set() for _ in range(nmax + 1)]}
    for a, shift in ((3, 1), (5, 2)):
        for b in range(1, 1 << nmax - shift, 2):
            p = eadd(b, b << shift)  # (1 + x^shift) [x] b
            if p.bit_length() <= nmax:
                sets[a][p.bit_length()].add(p)
    bad3 = bad5 = None
    for n in range(1, nmax + 1):
        odd = range((1 << n - 1) | 1, 1 << n, 2)
        if bad3 is None and sets[3][n] != {m for m in odd if is_multiple_of_3(m)}:
            bad3 = n
        if bad5 is None and (sets[5][n] != {m for m in odd if is_multiple_of_5(m)}
                             or sorted(sets[5][n]) != odd_members(DFA5, n)):
            bad5 = n
    check(f"{{odd n-bit multiples of 3}} = {{all 1-runs even}}, as sets     (all n <= {nmax})", bad3 is None)
    check(f"{{odd n-bit multiples of 5}} = {{run criterion (1)-(3)}}, as sets (all n <= {nmax})", bad5 is None)
    if bad3 or bad5:
        print(f"  first failing n: 3 -> {bad3}, 5 -> {bad5}")
    D3 = [len(s) for s in sets[3]]
    D5 = [len(s) for s in sets[5]]
    fib = [0, 1]
    while len(fib) <= nmax:
        fib.append(fib[-1] + fib[-2])
    check("D_3(n) = Fibonacci(n-3) for 3 <= n <= nmax", all(D3[n] == fib[n - 3] for n in range(3, nmax + 1)))
    check("D_5(n) = D_5(n-1) + D_5(n-2) + D_5(n-5) for 6 <= n <= nmax",
          all(D5[n] == D5[n - 1] + D5[n - 2] + D5[n - 5] for n in range(6, nmax + 1)))

    print("\n  Certificate (all n): bounded-carry outputs = carry-abstracted outputs")
    check("multiples of 3: certified DFA is equivalent to the even-run DFA", equivalent(DFA3, multiples_dfa(1)))
    check("multiples of 5: certified DFA is equivalent to the DFA of (1)-(3)", equivalent(DFA5, multiples_dfa(2)))
    big = 400
    c3, c5 = count_odd(DFA3, big), count_odd(DFA5, big)
    check(f"DFA counts agree with the brute-force counts for n <= {nmax}", c3[: nmax + 1] == D3 and c5[: nmax + 1] == D5)
    series = []
    num = [0, 0, 0, 1, 0, -1] + [0] * big
    for n in range(big + 1):
        series.append(num[n] + sum(series[n - k] for k in (1, 2, 5) if n >= k))
    check(f"DFA counts = coefficients of z^3(1-z^2)/(1-z-z^2-z^5) for n <= {big}", series == c5)
    print(f"  (a {len(DFA5[0])}-state DFA and an order-5 recurrence: agreement on 2*{len(DFA5[0])}+5 terms is a proof)")

    print("\n  n      D_3(n)      D_5(n)")
    for n in range(1, nmax + 1):
        print(f"  {n:2d}  {D3[n]:10d}  {D5[n]:10d}")

    print("\n  Certified automata for the multiples of a = 2^s + 1, exact generating functions:")
    print("   s     a   states   order of recurrence   growth rate lambda_a   gamma_a = log2(lambda_a)")
    gammas = {}
    for s in range(1, 7):
        dfa = multiples_dfa(s)
        counts = count_odd(dfa, 4 * len(dfa[0]) + 40)
        den = rational_gf(counts)[1]  # verified exactly on every term supplied
        lam = dominant_root(den)
        with localcontext() as ctx:
            ctx.prec = 30
            gammas[s] = lam.ln() / Decimal(2).ln()
        print(f"   {s}  {2 ** s + 1:4d}   {len(dfa[0]):6d}   {len(den) - 1:19d}   {str(lam)[:17]}      {str(gammas[s])[:17]}")
    check("gamma_3, gamma_5, gamma_9, gamma_17, gamma_33 = 0.6942, 0.7697, 0.791046, 0.799704, 0.803881",
          [f"{float(gammas[s]):.6f}" for s in range(1, 6)]
          == ["0.694242", "0.769689", "0.791046", "0.799704", "0.803881"])
    check("gamma_a increases with s; gamma_65 = 0.806113",
          all(gammas[s] < gammas[s + 1] for s in range(1, 6)) and f"{float(gammas[6]):.6f}" == "0.806113")
    check("D_a(i + j) >= D_a(i) D_a(j), so gamma_a exists                (a = 3, 5, 9, 17; i, j <= 30)", all(
        D[i + j] >= D[i] * D[j] for s in (1, 2, 3, 4) for D in [count_odd(multiples_dfa(s), 60)]
        for i in range(1, 31) for j in range(1, 31)
    ))
    done(t0)
    return D5, gammas


def no111_by_weight(length):
    """Number of binary strings of the given length without 111, by weight."""
    tails = [[1], [0], [0]]  # by number of trailing 1s
    for k in range(1, length + 1):
        zero = [a + b + c for a, b, c in zip(*[t + [0] * (k + 1 - len(t)) for t in tails])]
        tails = [zero, [0] + tails[0], [0] + tails[1]]
    return [a + b + c for a, b, c in zip(*[t + [0] * (length + 2 - len(t)) for t in tails])]


def explicit_bound(n, cache):
    """U(n) >= C(n): the candidates allowed by the weight count and by the No-111 Lemma.

    A composite of weight W either has a factor 1 + x^r, and is then determined
    by a cofactor of weight W/2 with at most n - r bits and no 111 at stride r,
    or is b [x] c with both weights >= 3 and len b + len c <= n + 1.
    """
    slot = n + 2
    two = [0] * (n + 1)
    for r in range(1, n - 1):
        q, rem = divmod(n - r, r)  # the r residue classes have q or q + 1 positions
        packed = 1
        for length, count in ((q + 1, rem), (q, r - rem)):
            if length not in cache:
                cache[length] = no111_by_weight(length)
            packed *= sum(c << slot * i for i, c in enumerate(cache[length])) ** count
        for j in range(2, n // 2 + 1):
            two[2 * j] += packed >> slot * j & (1 << slot) - 1
    total = 0
    for W in range(4, n + 1):
        three = sum(comb(lb - 2, W // k - 2) * comb(n - lb, k - 1)
                    for k in range(3, int(W ** 0.5) + 1) if W % k == 0 for lb in range(W // k, n))
        total += min(comb(n - 2, W - 2), two[W] + three)
    return total


def growth(dfa):
    c = count_odd(dfa, 1500)
    r1, r2 = c[1000] / c[999], c[1500] / c[1499]
    assert abs(r1 - r2) < 1e-12
    return r2


def theorem6(composites, nbits, D5, cmax, gammas):
    t0 = section("Theorem 4  (density of the composites: 0.8061 <= gamma <= 0.8747)")
    Cpy = [0] + [sum(1 for n in composites if n.bit_length() == k) for k in range(1, nbits + 1)]
    check(f"odd composites never have prime weight                     (<= {nbits} bits)",
          all(any(w(n) % d == 0 for d in range(2, w(n))) for n in composites))
    # Counting lemma behind the upper bound: an odd n-bit composite of weight W
    # is b [x] c with w(b) w(c) = W and len b + len c <= n + 1.
    ok = True
    for n in range(4, nbits + 1):
        for W in range(4, n + 1):
            actual = sum(1 for m in composites if m.bit_length() == n and w(m) == W)
            pairs = sum(
                comb(lb - 2, u - 2) * comb(lc - 2, W // u - 2)
                for u in range(2, W) if W % u == 0 and u * u <= W
                for lb in range(2, n) for lc in range(2, n + 2 - lb)
            )
            ok &= actual <= min(comb(n - 2, W - 2), pairs)
    check(f"#(n-bit composites of weight W) <= min(binom, #factor pairs)  (n <= {nbits})", ok)

    C = engine(cmax)
    if C is None:
        C = [0] + committed_counts()
        print(f"  C engine not available: C(n), n <= {len(C) - 1}, taken from the committed b-file")
        check(f"committed C(n) = Python sieve for n <= {nbits}", C[: nbits + 1] == Cpy)
    else:
        C = [0] + C
        check(f"C engine = Python sieve for n <= {nbits}", C[: nbits + 1] == Cpy)
        E5 = [0] + engine(cmax, 5)
        check(f"C engine: D_5(n) = DFA count for n <= {cmax}", E5 == count_odd(DFA5, cmax))
        check(f"C engine: D_3(n) = DFA count for n <= {cmax}", [0] + engine(cmax, 3) == count_odd(DFA3, cmax))
        D5 = E5
    top = min(len(C), len(D5)) - 1
    check(f"D_5(n) <= C(n) for 4 <= n <= {top}   (D_5(3) = 1 > C(3) = 0: 5 is irreducible)",
          all(D5[n] <= C[n] for n in range(4, top + 1)) and (D5[3], C[3]) == (1, 0))

    print("\n   n         C(n)       D_5(n)   C(n)/C(n-1)  log2(C(n))/n  C(n)/2^(n-2)")
    for n in range(1, len(C)):
        d5 = D5[n] if n < len(D5) else ""
        if C[n] and C[n - 1]:
            print(f"  {n:2d} {C[n]:12d} {d5:>12} {C[n] / C[n - 1]:12.4f} {log2(C[n]) / n:13.4f} {C[n] / 2 ** (n - 2):13.6f}")
        else:
            print(f"  {n:2d} {C[n]:12d} {d5:>12}")

    lo, hi = 1.0, 2.0  # dominant root of x^5 = x^4 + x^3 + 1
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if mid ** 5 < mid ** 4 + mid ** 3 + 1 else (lo, mid)
    H = log2(3) - 2 / 3
    print(f"\n  lambda_5 = {lo:.10f},  log2(lambda_5) = {log2(lo):.10f}")
    print(f"  H(1/3)   = log2(3) - 2/3 = {H:.10f}")
    check("growth rate of the DFA5 counts equals lambda_5", abs(growth(DFA5) - lo) < 1e-12)

    print("\n  Lower bound.  Every multiple of a other than a is composite, so gamma >= gamma_a (Theorem 3).")
    best = float(gammas[6])
    check("log2(lambda_5) = 0.76969 <= gamma_65 = 0.8061 < H(1/3)",
          abs(log2(lo) - 0.76969) < 5e-6 and log2(lo) <= best < H and f"{best:.4f}" == "0.8061")
    top = len(C) - 1
    check(f"D_65(n) <= C(n) for 8 <= n <= {top}",
          all(d <= c for d, c in list(zip(count_odd(multiples_dfa(6), top), C))[8:]))

    print("\n  Upper bound.  No-111 Lemma: the largest cofactor of a multiple of 1 + x^r has no 111 at stride r.")
    nmax, total, clean, swaps, fibbinary = 18, 0, True, True, True
    for r in range(1, 9):
        a, largest = 1 | 1 << r, {}
        for b in range(1, 1 << nmax - r, 2):
            p = emul(a, b)
            if p.bit_length() <= nmax:
                largest[p] = max(largest.get(p, 0), b)
                if has_stride_111(b, r) and b < 1 << 12:
                    i = (b & b >> r & b >> 2 * r).bit_length() - 1 + r
                    c = eadd(b ^ 1 << i, 2 << i)  # the middle bit of the triple, one place up
                    swaps &= c > b and emul(a, c) == p
        total += len(largest)
        clean &= not any(has_stride_111(b, r) for b in largest.values())
        if r == 1:
            fibbinary = all(b & b >> 1 == 0 for b in largest.values())
    check(f"no 111 at stride r in the largest cofactor of all {total} odd multiples   (r <= 8, n <= {nmax})", clean)
    check("exchange (1+x^r)(x^(i-r)+x^i+x^(i+r)) = (1+x^r)(x^(i-r)+x^(i+1)+x^(i+r)): same product, larger cofactor", swaps)
    check("r = 1: the largest cofactor has no two adjacent 1s (N = 3 b*, A277335)", fibbinary)
    x, theta, E = no111_exponent()
    check(f"weighted No-111 optimum: x = {x:.6f}, theta = {theta:.6f}, E = {E:.6f}",
          (f"{x:.6f}", f"{theta:.6f}", f"{E:.6f}") == ("0.808173", "0.705340", "0.874665"))
    H4 = 2 - 0.75 * log2(3)
    check(f"composites without a factor of weight 2: exponent H(1/4) = {H4:.6f} < E", f"{H4:.6f}" == "0.811278" and H4 < E)
    for length in (1000, 4000):
        by_weight = no111_by_weight(length)
        most = max(min(comb(length, W), by_weight[W // 2]) for W in range(2, length, 2))
        print(f"    exact counts, length {length}: max_W min(binom(L, W), #no-111 of weight W/2) = 2^({log2(most) / length:.4f} L)")
    cache = {}
    U = {n: explicit_bound(n, cache) for n in list(range(4, top + 1)) + [60, 100, 200]}
    check(f"explicit finite bound U(n) >= C(n) for 4 <= n <= {top}   (U({top})/C({top}) = {U[top] / C[top]:.1f})",
          all(U[n] >= C[n] for n in range(4, top + 1)))
    check("U(n) < 2^(n-2) and U(n) < n 2^(0.8748 n) for every computed n",
          all(u < 2 ** (n - 2) and log2(u) < log2(n) + 0.8748 * n for n, u in U.items()))
    print("    log2(U(n))/n: " + ", ".join(f"n = {n}: {log2(U[n]) / n:.4f}" for n in (top, 60, 100, 200)))

    slope = log2(C[top] / C[top - 5]) / 5
    print(f"\n  Local slope of log2 C(n) over n = {top - 5}..{top}: {slope:.4f};   last step: {log2(C[top] / C[top - 1]):.4f}")
    check(f"pre-asymptotic gap: the local slope at n = {top} is below the proved lower bound gamma_65 = {best:.4f}",
          slope < best)
    print(f"  => {best:.4f} <= gamma <= {E:.4f}   (was {log2(lo):.4f} <= gamma <= {H:.4f} from D_5 and H(1/3) alone)")
    done(t0)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--nmax", type=int, default=24)
    ap.add_argument("--cmax", type=int, default=31)
    args = ap.parse_args()
    t0 = time.perf_counter()
    nbits = 16
    composites = odd_composites(nbits)
    theorem1()
    theorem2()
    theorem3()
    theorem4(composites, nbits)
    D5, gammas = theorem5(args.nmax)
    theorem6(composites, nbits, D5, args.cmax, gammas)
    print(f"\n{'ALL CHECKS PASSED' if not failures else 'FAILED: ' + '; '.join(failures)}"
          f"   (total {time.perf_counter() - t0:.1f} s)")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
