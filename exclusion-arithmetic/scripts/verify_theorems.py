#!/usr/bin/env python3
"""Reproduce every table and re-check Theorems 1-6 of the README.

    python scripts/verify_theorems.py [--nmax 24] [--cmax 31]

--nmax  bit length up to which multiples of 3 and 5 are compared, as sets, with
        the products a [x] b themselves (the brute-force audit of Theorem 5).
--cmax  bit length up to which the C engine counts composites (Theorem 6);
        memory 2^(cmax-4) bytes; skipped if no C compiler is found.

Exit status 0 iff every check passes.
"""

import argparse
import shutil
import subprocess
import sys
import tempfile
import time
from itertools import product
from math import comb, log2
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))

from exclusion import eadd, emul, epow, g, v2, w  # noqa: E402
from exclusion.automata import (  # noqa: E402
    DFA3, DFA5, count_odd, equivalent, is_multiple_of_3, is_multiple_of_5,
    multiples_dfa, odd_members,
)
from exclusion.factor import (  # noqa: E402
    G, factorizations, gap_irreducible, odd_composites, quotients,
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
    out = subprocess.run([str(_exe), *map(str, args)], check=True, capture_output=True, text=True)
    return [int(line.split()[1]) for line in out.stdout.splitlines()]


def theorem1():
    t0 = section("Theorem 1  (normal forms; S is a commutative semiring on N_0)")
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
    t0 = section("Theorem 2  (universal maps w and v2; residual finiteness)")
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
    t0 = section("Theorem 3  (2 is the unique prime; S is not cancellative)")
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
    t0 = section("Theorem 4  (Gap Lemma; unbounded elasticity)")
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
    done(t0)


def theorem5(nmax):
    t0 = section(f"Theorem 5  (multiples of 3 and 5; brute-force audit for n <= {nmax})")
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
    done(t0)
    return D5


def growth(dfa):
    c = count_odd(dfa, 1500)
    r1, r2 = c[1000] / c[999], c[1500] / c[1499]
    assert abs(r1 - r2) < 1e-12
    return r2


def theorem6(composites, nbits, D5, cmax):
    t0 = section("Theorem 6  (exponential decay of composites)")
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
        print("  no C compiler found: C(n) taken from the Python sieve only")
        C = Cpy
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

    print("\n  Certified regular sets of multiples of 2^s + 1  (D_a(n) <= C(n) for n > s + 1):")
    print("   s     a   carry-certified DFA states   growth rate   log2")
    best = 0
    for s in range(1, 7):
        dfa = multiples_dfa(s)
        rate = growth(dfa)
        best = max(best, log2(rate))
        print(f"   {s}  {2 ** s + 1:4d}   {len(dfa[0]):24d}   {rate:.10f}   {log2(rate):.6f}")
    check("log2(lambda_5) = 0.76969 <= best certified lower bound < H(1/3)", abs(log2(lo) - 0.76969) < 5e-6 and log2(lo) <= best < H)
    print(f"  => {best:.4f} <= gamma <= {H:.4f}")
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
    D5 = theorem5(args.nmax)
    theorem6(composites, nbits, D5, args.cmax)
    print(f"\n{'ALL CHECKS PASSED' if not failures else 'FAILED: ' + '; '.join(failures)}"
          f"   (total {time.perf_counter() - t0:.1f} s)")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
