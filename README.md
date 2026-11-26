# Exclusion Arithmetic

Arithmetic on the non-negative integers in which a binary column that receives
several units **keeps one and carries all the others**. Algebraically it is the
commutative semiring

$$S \;=\; \mathbb{N}_0[x]\,/\,\langle\, 2 \sim 1 + x \,\rangle ,$$

whose normal forms are the polynomials with coefficients in $\{0,1\}$; reading
them in base 2 ($x \mapsto 2$) puts a new sum $\boxplus$ and product $\boxtimes$
on $\mathbb{N}_0$.

This repository contains a dependency-free Python reference implementation, an
optional C sieve, a test suite, scripts that re-derive every number quoted
below, and a ready-to-submit [OEIS package](oeis/README.md).

## Definition

Rewrite $2x^k \to x^k + x^{k+1}$ until every coefficient is 0 or 1. Carried out
from the lowest column upward this is the **Lindley recursion**: if column $k$
receives $p_k$ units (for a sum, $p_k = a_k + b_k$; for a product, the $k$-th
coefficient of the polynomial product) and $c_0 = 0$, then

$$\text{digit}_k = [\,c_k + p_k \ge 1\,], \qquad c_{k+1} = \max(c_k + p_k - 1,\ 0).$$

Examples: $1 \boxplus 1 = 3$; $\;3 \boxtimes 3 = (1+x)^2 = 1 + 2x + x^2 = 1 + x + x^2 + x^3 = 15$;
$\;2 \boxtimes n = 2n$.

|  | $(\mathbb{N}_0, +, \cdot)$ | $S = (\mathbb{N}_0, \boxplus, \boxtimes)$ |
|---|---|---|
| carry rule | $2\cdot 2^k \to 2^{k+1}$ | $2x^k \to x^k + x^{k+1}$ |
| $1 + 1$ | $2$ | $3$ |
| comparison | | $a \boxplus b \ge a + b$, $a \boxtimes b \ge ab$; $a \boxplus b = a + b \iff a \mathbin{\&} b = 0$ |
| Hamming weight $w$ | no algebraic meaning | homomorphism onto $(\mathbb{N}_0, +, \cdot)$ |
| cancellation | holds | fails: $3 \boxtimes 3 = 3 \boxtimes 5 = 15$ |
| units | $1$ | $1$ |
| primes | infinitely many | only $2$ |
| irreducibles | the primes | $2$ and almost every odd number |
| factorisation | unique | not unique, lengths unbounded in ratio |
| odd composites with $n$ bits | all but $O(2^n/n)$ | $C(n) \le n\,2^{0.9183\,n}$: exponentially rare |
| multiples of 3 | $n \equiv 0 \pmod 3$ | every run of 1s has even length |
| reduction mod $2^m$ | the ring $\mathbb{Z}/2^m$ | a finite semiring with $2^m$ elements |

## Theorems

Notation: $w$ = Hamming weight, $v_2$ = 2-adic valuation, $\operatorname{len}$ = bit
length, $g(a)$ = distance between the two lowest 1-bits of $a$ (the *gap*;
$g(a) = v_2(a-1)$ for odd $a > 1$), $R_k = 2^k - 1$. An element $n \ge 2$ is
*irreducible* if $n = a \boxtimes b$ forces $a = 1$ or $b = 1$, *composite*
otherwise, and *prime* if $n \mid a \boxtimes b$ implies $n \mid a$ or $n \mid b$.
Each statement is re-checked by `scripts/verify_theorems.py`.

**Theorem 1 (normal form).** The rewriting system $2x^k \to x^k + x^{k+1}$ is
terminating and confluent, so every class of $S$ has exactly one representative
in $\{0,1\}[x]$, computed by the Lindley recursion. Consequently
$\operatorname{len}(a \boxtimes b) \ge \operatorname{len} a + \operatorname{len} b - 1$,
the only unit is 1, and $R_a \boxtimes R_b = R_{ab}$.

*Proof.* A rewrite never empties a column, so rewrites at different columns
commute and neither disables the other (diamond property). Mass is conserved
and an occupied column stays occupied, so a polynomial of degree $d$ and mass
$m$ never reaches beyond column $d + m$; each rewrite raises one unit, hence
the process stops. A polynomial whose coefficients are all $\ge 1$ on
$[0, d]$ normalises to $R_m$. $\square$

**Theorem 2 (universal maps, residual finiteness).**
(a) $w : S \to (\mathbb{N}_0, +, \cdot)$ is a surjective homomorphism, and every
homomorphism from $S$ to an additively cancellative semiring (for instance a
ring) factors uniquely through it.
(b) $v_2 : S \to (\mathbb{N}_0 \cup \{\infty\}, \min, +)$ is a surjective
homomorphism, and every homomorphism from $S$ to an additively idempotent
semiring factors uniquely through it.
(c) For every $m$, $a \mapsto a \bmod 2^m$ is a homomorphism of $S$ onto
$S/\langle x^m \sim 0\rangle$, a semiring with $2^m$ elements; these maps
separate points, so $S$ is residually finite.

*Proof.* (a) $\varphi(1) + \varphi(1) = \varphi(1) + \varphi(x)$ gives
$\varphi(x) = \varphi(1)$ after cancelling. (b) With $t = \varphi(x)$ and
$1 + 1 = 1$ we get $1 + t = 1$, then $1 + t^k = 1$ by induction and
$t^i + t^j = t^{\min(i,j)}$. (c) Carries only move upward. $\square$

**Theorem 3 (a single prime).** $2$ is prime, and it is the only prime of $S$.
An even number is composite iff it is $\ge 4$; $S$ is not cancellative.

*Proof.* $2 \boxtimes n = 2n$, so $2 \mid a \boxtimes b$ iff $a$ or $b$ is
even. Let $p > 1$ be odd, $k = w(p)$. For large $m$ every column of
$p \cdot R_m$ is fed fast enough that $p \boxtimes R_m = R_{km} = R_k \boxtimes R_m$.
Take $m \equiv 1 \pmod k$: by weights $p \nmid R_m$, and $p \mid R_k$ only if
$p = R_k$. If $p = R_k$, replace $R_k$ by any other odd $q$ of weight $k$:
again $q \boxtimes R_m = R_{km}$ and $p \nmid q$. $\square$

**Theorem 4 (Gap Lemma, infinite elasticity).**
$g(a \boxtimes b) = \min(g(a), g(b))$ for $a, b \ne 0$. Hence every odd $n > 1$
with $2\,g(n) > \operatorname{len}(n) - 1$ is irreducible; the set $G_n$ of
such $n$ with $n$ bits has $2^{\lfloor n/2 \rfloor - 1}$ elements, and the
inequality is sharp:
$(1 + x^k)^{\boxtimes 2} = 1 + x^k + x^{k+1} + x^{2k}$.
Moreover, for $j \ge 1$ and a prime $q \ge 2^j - 1$,

$$R_{q 2^j} \;=\; \bigl(1 + x^q R_{2^j - 1}\bigr) \boxtimes R_q \;=\; 3^{\boxtimes j} \boxtimes R_q$$

are factorisations into $2$ and into $j + 1$ irreducibles, so the elasticity
of $S$ is infinite.

*Proof.* If $n = a \boxtimes b$ with $a, b$ odd and $> 1$, then
$\operatorname{len}(n) - 1 \ge (\operatorname{len} a - 1) + (\operatorname{len} b - 1) \ge g(a) + g(b) \ge 2g(n)$.
In both products every coefficient of the polynomial product is $\ge 1$ on an
initial segment, so both normalise to the repunit of weight $q 2^j$. The first
factor on the left lies in $G_{q + 2^j - 1}$; $R_q$ and $3$ have prime weight. $\square$

**Theorem 5 (multiples of 3 and of 5).** Let $D_a(n)$ be the number of odd
$n$-bit multiples of $a$.
(a) $N$ is a multiple of $3 = 1 + x$ iff every maximal run of 1s of $N$ has
even length; $D_3(n) = F_{n-3}$ for $n \ge 3$.
(b) Read an odd $N$ from the least significant bit as runs of 1s of lengths
$M_1, \dots, M_r$ separated by runs of 0s of lengths $Z_1, \dots, Z_{r-1}$, and
let $u_0 = 0$, $u_i = (M_1 + \dots + M_i) \bmod 2$. Then $N$ is a multiple of
$5 = 1 + x^2$ iff (1) $u_r = 0$; (2) $Z_i = 1$ whenever $u_i = 1$; (3)
$M_i \notin \{2, 3\}$ whenever $u_{i-1} = 0$. Consequently

$$\sum_{n \ge 1} D_5(n) z^n = \frac{z^3 (1 - z^2)}{1 - z - z^2 - z^5}, \qquad D_5(n) = D_5(n-1) + D_5(n-2) + D_5(n-5) \quad (n \ge 6),$$

with $D_5(1..5) = 0, 0, 1, 1, 1$ and growth rate $\lambda_5 = 1.704902\ldots$,
$\log_2 \lambda_5 = 0.76968\ldots$.

*Proof (machine-checked, `exclusion.automata.multiples_dfa`).* Multiplication
by $1 + x^s$ is a transducer whose only unbounded quantity is the carry. Let
$I$ be the language of all multiples, $U_K \subseteq I$ the outputs of runs
with carry $\le K$, and $O_K \supseteq I$ the outputs when carries $\ge K$ are
remembered only modulo 2. The inclusion $O_K \subseteq U_K$ is a finite
automaton check; it holds with $K = 1$ for $s = 1, 2$, so $I = U_1$ is regular,
and its minimal DFA is equivalent to the DFA of the stated conditions.
Independently, the sets were compared with the products $5 \boxtimes b$
themselves for every $n \le 24$ and the counts for every $n \le 37$. $\square$

**Theorem 6 (composites are exponentially rare).** Let $C(n)$ be the number of
odd composites with $n$ bits and $H = \log_2 3 - \tfrac23 = 0.91829\ldots$ the binary
entropy of $\tfrac13$. Then

$$D_5(n) \;\le\; C(n) \quad (n \ge 4), \qquad C(n) \;\le\; (n + o(1))\, 2^{H n},$$

so every limit point $\gamma$ of $\log_2 C(n) / n$ satisfies
$0.76968 \le \gamma \le 0.91830$. The same certificate as in Theorem 5 works for
$a = 2^s + 1$, $s \le 6$, and sharpens the lower bound to $\gamma \ge 0.8061$
(table below); in particular $\gamma \in [0.7697, 0.9183)$.

*Proof.* Lower bound: a multiple of $a$ other than $a$ is composite. Upper
bound: let $N = b \boxtimes c$ have $n$ bits and weight $W = w(b)\,w(c)$,
$w(b) \le w(c)$. Either $W \ge 2n/3$ (at most $2^{Hn}$ such $N$); or
$w(b) = 2$, so $b = 1 + x^p$ and $w(c) < n/3$ (at most $n\,2^{Hn}$ pairs); or
$3 \le w(b) < \sqrt n$ and $w(c) < 2n/9$ (at most
$2^{H(2/9) n + o(n)}$ pairs, $H(2/9) < 0.7643$). $\square$

## Tables

Odd composites and odd multiples of 5 by bit length ($C$ from the C sieve,
$D_5$ from the automaton; equal to brute force wherever both exist):

| $n$ | $C(n)$ | $D_5(n)$ | $C(n)/C(n-1)$ | $C(n)/2^{n-2}$ |
|---:|---:|---:|---:|---:|
| 1 | 0 | 0 |  |  |
| 2 | 0 | 0 |  | 0.000000 |
| 3 | 0 | 1 |  | 0.000000 |
| 4 | 1 | 1 |  | 0.250000 |
| 5 | 2 | 1 | 2.0000 | 0.250000 |
| 6 | 3 | 2 | 1.5000 | 0.187500 |
| 7 | 8 | 3 | 2.6667 | 0.250000 |
| 8 | 15 | 6 | 1.8750 | 0.234375 |
| 9 | 29 | 10 | 1.9333 | 0.226562 |
| 10 | 53 | 17 | 1.8276 | 0.207031 |
| 11 | 108 | 29 | 2.0377 | 0.210938 |
| 12 | 196 | 49 | 1.8148 | 0.191406 |
| 13 | 337 | 84 | 1.7194 | 0.164551 |
| 14 | 587 | 143 | 1.7418 | 0.143311 |
| 15 | 1019 | 244 | 1.7359 | 0.124390 |
| 16 | 1799 | 416 | 1.7655 | 0.109802 |
| 17 | 3280 | 709 | 1.8232 | 0.100098 |
| 18 | 5937 | 1209 | 1.8101 | 0.090591 |
| 19 | 10541 | 2061 | 1.7755 | 0.080421 |
| 20 | 18750 | 3514 | 1.7788 | 0.071526 |
| 21 | 32688 | 5991 | 1.7434 | 0.062347 |
| 22 | 56243 | 10214 | 1.7206 | 0.053638 |
| 23 | 96990 | 17414 | 1.7245 | 0.046248 |
| 24 | 167786 | 29689 | 1.7299 | 0.040003 |
| 25 | 289771 | 50617 | 1.7270 | 0.034543 |
| 26 | 505475 | 86297 | 1.7444 | 0.030129 |
| 27 | 877597 | 147128 | 1.7362 | 0.026154 |
| 28 | 1519071 | 250839 | 1.7309 | 0.022636 |
| 29 | 2630267 | 427656 | 1.7315 | 0.019597 |
| 30 | 4537910 | 729112 | 1.7253 | 0.016905 |
| 31 | 7808175 | 1243065 | 1.7207 | 0.014544 |
| 32 | 13492483 | 2119305 | 1.7280 | 0.012566 |
| 33 | 23284013 | 3613209 | 1.7257 | 0.010842 |
| 34 | 40137598 | 6160170 | 1.7238 | 0.009345 |
| 35 | 69353698 | 10502491 | 1.7279 | 0.008074 |
| 36 | 119664274 | 17905726 | 1.7254 | 0.006965 |
| 37 | 205923302 | 30527522 | 1.7208 | 0.005993 |

The local ratio $C(n)/C(n-1) \approx 1.72$ is still below the proven
asymptotic rate $\ge 1.7484$: the range $n \le 37$ is pre-asymptotic.

Certified regular languages of multiples of $a = 2^s + 1$:

| $s$ | $a = 2^s + 1$ | states of the minimal DFA | growth rate $\lambda_a$ | $\log_2 \lambda_a$ |
|---:|---:|---:|---:|---:|
| 1 | 3 | 3 | 1.618034 | 0.6942 |
| 2 | 5 | 7 | 1.704903 | 0.7697 |
| 3 | 9 | 22 | 1.730329 | 0.7910 |
| 4 | 17 | 79 | 1.740744 | 0.7997 |
| 5 | 33 | 307 | 1.745791 | 0.8039 |
| 6 | 65 | 1292 | 1.748495 | 0.8061 |

## Quickstart

```console
$ pip install -e ".[dev]"          # or just: export PYTHONPATH=src
$ python
>>> from exclusion import eadd, emul, epow, w, v2, g
>>> eadd(1, 1), emul(3, 3), emul(3, 5), epow(3, 5) == 2**32 - 1
(3, 15, 15, True)
>>> from exclusion.factor import factorizations, is_irreducible, G
>>> sorted(factorizations(15)), is_irreducible(23), G(6)
([(3, 3), (3, 5)], True, [33, 41, 49, 57])
>>> from exclusion.automata import is_multiple_of_5, DFA5, count_odd
>>> [n for n in range(1, 64, 2) if is_multiple_of_5(n)], count_odd(DFA5, 12)[1:]
([5, 15, 29, 45, 63], [0, 0, 1, 1, 1, 2, 3, 6, 10, 17, 29, 49])
```

`eadd` is the literal $\Theta(n)$ Lindley recursion on Python integers; `emul`
obtains the coefficients of the polynomial product from one big-integer
multiplication (Kronecker substitution) and normalises once. Neither has a
word size to overflow.

## Reproducing everything

| command | does | time |
|---|---|---|
| `pytest` | 32 tests: semiring axioms, Lindley vs. bitwise carry propagation, big-integer product vs. shift-and-add, $w$, $v_2$, $g$, quotients mod $2^m$, factorisation, Gap Lemma, multiples of 3 and 5, the C engine | 15 s |
| `python scripts/verify_theorems.py` | checks Theorems 1-6 and prints all tables (audit of Theorem 5 for $n \le 24$, $C(n)$ for $n \le 31$) | 70 s |
| `python scripts/generate_oeis.py` | writes `oeis/drafts`, `oeis/bfiles`; runs the Python and PARI programs of every draft | 12 s |
| `python scripts/generate_oeis.py --cmax 37` | the same with $C(n)$ up to $n = 37$ (8 GiB of RAM) | 9 min |
| `make -C src/c && src/c/count_composites 31` | $C(n)$, $n \le 31$, directly (128 MiB); add an odd `a` for $D_a(n)$ | 7 s |

Timings are for a 4-core x86-64 machine with GCC 13 and OpenMP. `EXCLUSION_NMAX=24 pytest`
extends the set-equality test for multiples of 5 to 24 bits; `--nmax` and
`--cmax` set the ranges of `verify_theorems.py`. Python $\ge$ 3.10; no
dependencies outside the standard library (pytest for the tests, a C11
compiler for the sieve, `gp` to execute the PARI programs).

## OEIS

| sequence | A-number |
|---|---|
| $n \boxplus n$ | *pending* |
| $n \boxtimes n$ | *pending* |
| odd composites of $S$ | *pending* |
| odd irreducibles of $S$ | *pending* |
| $C(n)$ | *pending* |
| $D_5(n)$ | *pending* |

Drafts, b-files, submission order and checklist: [oeis/README.md](oeis/README.md).
Related existing entries: A277335 (multiples of 3 in $S$), A086799
($n \boxplus 1$, shifted), A162276 (agrees with $n \boxplus n$ for
$1 \le n \le 10$ only), A067139 (irreducibles of OR-numbral arithmetic, where
$1 + 1 = 1$).

## Layout

```
src/exclusion/core.py        eadd, emul, epow, w, v2, g
src/exclusion/factor.py      quotients, divisors, irreducibility, factorisations, sieve, Gap Lemma
src/exclusion/automata.py    recognisers for multiples of 3 and 5; certificate for 1 + x^s
src/c/count_composites.c     C11 sieve for C(n) and D_a(n), OpenMP optional
scripts/                     verify_theorems.py, generate_oeis.py
tests/test_exclusion.py      pytest suite
oeis/                        submission drafts and b-files
```

MIT licence.
