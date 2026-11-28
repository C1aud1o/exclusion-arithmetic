# Exclusion Arithmetic

Arithmetic on the non-negative integers in which a binary column that receives
several units **keeps one and carries all the others**. Algebraically it is the
commutative semiring

$$S = \mathbb{N}_0[x] / \langle 2 \sim 1 + x \rangle ,$$

whose normal forms are the polynomials with coefficients in $\lbrace 0,1 \rbrace$; reading
them in base 2 ($x \mapsto 2$) puts a new sum $\boxplus$ and product $\boxtimes$
on $\mathbb{N}_0$.

This repository contains a dependency-free Python reference implementation, an
optional C sieve, a test suite, and a script that re-checks the theorems and
re-derives the tables below.

## Definition

Rewrite $2x^k \to x^k + x^{k+1}$ until every coefficient is 0 or 1. Carried out
from the lowest column upward this is the **Lindley recursion**: if column $k$
receives $p_k$ units (for a sum, $p_k = a_k + b_k$; for a product, the $k$-th
coefficient of the polynomial product) and $c_0 = 0$, then

$$\text{digit}_k = [ c_k + p_k \ge 1 ], \qquad c_{k+1} = \max(c_k + p_k - 1,\ 0).$$

Examples: $1 \boxplus 1 = 3$; $3 \boxtimes 3 = (1+x)^2 = 1 + 2x + x^2 = 1 + x + x^2 + x^3 = 15$;
$2 \boxtimes n = 2n$.

|  | $(\mathbb{N}_0, +, \cdot)$ | $S = (\mathbb{N}_0, \boxplus, \boxtimes)$ |
|---|---|---|
| carry rule | $2\cdot 2^k \to 2^{k+1}$ | $2x^k \to x^k + x^{k+1}$ |
| $1 + 1$ | $2$ | $3$ |
| comparison | | $a \boxplus b \ge a + b$, $a \boxtimes b \ge ab$; $a \boxplus b = a + b \iff a \mathbin{\mathrm{AND}} b = 0$ |
| Hamming weight $w$ | no algebraic meaning | homomorphism onto $(\mathbb{N}_0, +, \cdot)$ |
| cancellation | holds | fails: $3 \boxtimes 3 = 3 \boxtimes 5 = 15$ |
| units | $1$ | $1$ |
| primes | infinitely many | only $2$ |
| irreducibles | the primes | $2$ and almost every odd number |
| factorisation | unique | not unique, lengths unbounded in ratio |
| odd composites with $n$ bits | all but $O(2^n/n)$ | $2^{0.8061 n} \lesssim C(n) \le 2^{0.8747 n + o(n)}$: exponentially rare |
| multiples of 3 | $n \equiv 0 \pmod 3$ | every run of 1s has even length |
| multiples of a fixed $a$ | a regular language | a regular language, for every $a$ |
| reduction mod $2^m$ | the ring $\mathbb{Z}/2^m$ | a finite semiring with $2^m$ elements |

## Theorems

Notation: $w$ = Hamming weight, $v_2$ = 2-adic valuation, $\mathrm{len}$ = bit
length, $g(a)$ = distance between the two lowest 1-bits of $a$ (the *gap*;
$g(a) = v_2(a-1)$ for odd $a > 1$), $R_k = 2^k - 1$, $\Omega(m)$ = number of
prime factors of $m$ with multiplicity. An element $n \ge 2$ is *irreducible*
if $n = a \boxtimes b$ forces $a = 1$ or $b = 1$, *composite* otherwise, and
*prime* if $n \mid a \boxtimes b$ implies $n \mid a$ or $n \mid b$.
$\mathcal{L}(n)$ is the set of lengths of the factorisations of $n$ into
irreducibles. Each statement is re-checked by `scripts/verify_theorems.py`.

**Theorem 1 (semiring structure).**
(a) The rewriting system $2x^k \to x^k + x^{k+1}$ is terminating and confluent,
so every class of $S$ has exactly one representative in $\lbrace 0,1 \rbrace[x]$, computed
in $\Theta(n)$ by the Lindley recursion. Consequently
$\mathrm{len}(a \boxtimes b) \ge \mathrm{len} a + \mathrm{len} b - 1$,
the only unit is 1, and $R_a \boxtimes R_b = R_{ab}$.
(b) $w : S \to (\mathbb{N}_0, +, \cdot)$ is a surjective homomorphism, and every
homomorphism from $S$ to an additively cancellative semiring (for instance a
ring) factors uniquely through it.
(c) $v_2 : S \to (\mathbb{N}_0 \cup \lbrace \infty \rbrace, \min, +)$ is a surjective
homomorphism, and every homomorphism from $S$ to an additively idempotent
semiring factors uniquely through it.
(d) For every $m$, $a \mapsto a \bmod 2^m$ is a homomorphism of $S$ onto
$S/\langle x^m \sim 0\rangle$, a semiring with $2^m$ elements; these maps
separate points, so $S$ is residually finite.

*Proof.* (a) A rewrite never empties a column, so rewrites at different columns
commute and neither disables the other (diamond property). Mass is conserved
and an occupied column stays occupied, so a polynomial of degree $d$ and mass
$m$ never reaches beyond column $d + m$; each rewrite raises one unit, hence
the process stops. A polynomial whose coefficients are all $\ge 1$ on
$[0, d]$ normalises to $R_m$. (b) $\varphi(1) + \varphi(1) = \varphi(1) + \varphi(x)$
gives $\varphi(x) = \varphi(1)$ after cancelling. (c) With $t = \varphi(x)$ and
$1 + 1 = 1$ we get $1 + t = 1$, then $1 + t^k = 1$ by induction and
$t^i + t^j = t^{\min(i,j)}$. (d) Carries only move upward. $\square$

**Theorem 2 (the prime, the irreducibles, factorisation lengths).**
(a) $2$ is prime, and it is the only prime of $S$. An even number is composite
iff it is $\ge 4$; $S$ is not cancellative ($3 \boxtimes 3 = 3 \boxtimes 5$).
(b) *Gap Lemma.* $g(a \boxtimes b) = \min(g(a), g(b))$ for $a, b \ne 0$. Hence
every odd $N > 1$ with $2 g(N) > \mathrm{len}(N) - 1$ is irreducible;
there are $2^{\lfloor n/2 \rfloor - 1}$ such $N$ with $n$ bits.
(c) *Top-Gap Lemma.* Let $N$ be odd with top bit $d$ and let $h < d$ be its
highest 1-bit below $d$. If $2h \le d$, then $N$ is irreducible.
(d) *Carry-Bridge identity.* $\widetilde G_v = (2^{v-1} - 1) + 2^{2v-3}$
($v \ge 2$: 3, 11, 39, 143, …) has weight $v$ and is irreducible, and

$$R_u \boxtimes \widetilde G_v = R_{uv} \qquad \text{for all } u, v \ge 2 .$$

(e) *Length sets.* For $m \ge 2$, $\mathcal{L}(2^m - 1) = \lbrace 1 \rbrace$ if $m$ is
prime and $\lbrace 2, 3, \dots, \Omega(m) \rbrace$ if $m$ is composite. In particular

$$2^{2^k} - 1 = \widetilde G_{2^{k-1}} \boxtimes 3 = 3^{\boxtimes k}$$

has factorisations of lengths $2$ and $k$: the elasticity of $S$ is infinite.

*Proof.* (a) $2 \boxtimes n = 2n$, so $2 \mid a \boxtimes b$ iff $a$ or $b$ is
even. Let $p > 1$ be odd, $k = w(p)$. For large $m$ every column of
$p \cdot R_m$ is fed fast enough that $p \boxtimes R_m = R_{km} = R_k \boxtimes R_m$.
Take $m \equiv 1 \pmod k$: by weights $p \nmid R_m$, and $p \mid R_k$ only if
$p = R_k$. If $p = R_k$, replace $R_k$ by any other odd $q$ of weight $k$.
(b) If $N = a \boxtimes b$ with $a, b$ odd and $> 1$, then
$\mathrm{len}(N) - 1 \ge (\mathrm{len} a - 1) + (\mathrm{len} b - 1) \ge g(a) + g(b) \ge 2g(N)$.
(c) Let $N = a \boxtimes b$ with $a, b$ odd, $> 1$, and $e = \deg a + \deg b \le d$.
If $e < d$, carries left the top column of the polynomial product, so columns
$e..d$ of $N$ are all 1 and $h = d - 1 > d/2$. If $e = d$, the second-highest
term of the product sits in column $\max(\deg a + h_b, \deg b + h_a) \ge d/2$
and that column stays occupied, so $h \ge d/2$; equality forces
$a = b = 1 + x^{d/2}$, whose square $1 + x^{d/2} + x^{d/2+1} + x^d$ has
$h = d/2 + 1$.
(d) $\widetilde G_v$ has $h = v - 2$ and $d = 2v - 3$. In
$R_u \widetilde G_v = R_u R_{v-1} + x^{2v-3} R_u$ the first block puts
$u(v-1)$ units on $u + v - 2$ columns; its $(u-1)(v-2)$ spare units cover the
$v - u - 1$ empty columns below $x^{2v-3}$ (if any), after which every column
is occupied: $uv$ units in a row.
(e) $R_m$ has weight $m$, so it is irreducible for $m$ prime, and no
factorisation is longer than $\Omega(m)$. For $m = p_1 \cdots p_k$ and
$2 \le j \le k$, $R_{p_1} \boxtimes \cdots \boxtimes R_{p_{j-1}} \boxtimes \widetilde G_v$
with $v = p_j \cdots p_k$ has length $j$ by (d). $\square$

The Gap Lemma gives a second family with unbounded elasticity: for $j \ge 1$
and a prime $q \ge 2^j - 1$,
$R_{q 2^j} = (1 + x^q R_{2^j - 1}) \boxtimes R_q = 3^{\boxtimes j} \boxtimes R_q$.

**Theorem 3 (multiples of a fixed element form a regular language).** Let
$D_a(n)$ be the number of odd $n$-bit multiples of $a$.
(a) For every $a \ge 1$ the binary numerals of $\lbrace a \boxtimes b : b \in S \rbrace$,
read from the least significant bit, form a regular language. Hence
divisibility by a fixed $a$ is decided in $O(n)$ time and $O(1)$ space,
$\sum_n D_a(n) z^n$ is rational, and for odd $a$ the limit
$\gamma_a = \lim_n \tfrac1n \log_2 D_a(n)$ exists. (For even $a$ every multiple
is even, so $D_a(n) = 0$; the multiples of $2^k a'$ are those of $a'$ shifted by
$k$ places.)
(b) $N$ is a multiple of $3 = 1 + x$ iff every maximal run of 1s of $N$ has
even length; $D_3(n) = F_{n-3}$ for $n \ge 3$.
(c) Read an odd $N$ from the least significant bit as runs of 1s of lengths
$M_1, \dots, M_r$ separated by runs of 0s of lengths $Z_1, \dots, Z_{r-1}$, and
let $u_0 = 0$, $u_i = (M_1 + \dots + M_i) \bmod 2$. Then $N$ is a multiple of
$5 = 1 + x^2$ iff (1) $u_r = 0$; (2) $Z_i = 1$ whenever $u_i = 1$; (3)
$M_i \notin \lbrace 2, 3 \rbrace$ whenever $u_{i-1} = 0$. Consequently

$$\sum_{n \ge 1} D_5(n) z^n = \frac{z^3 (1 - z^2)}{1 - z - z^2 - z^5}, \qquad D_5(n) = D_5(n-1) + D_5(n-2) + D_5(n-5) \quad (n \ge 6),$$

with $D_5(1..5) = 0, 0, 1, 1, 1$ and growth rate $\lambda_5 = 1.704902\ldots$.
(d) For $a = 2^s + 1$, $s \le 6$, the minimal automata, the exact generating
functions and the growth rates are computed (table below); $\gamma_a$
increases with $s$ throughout.

*Proof.* (a) Column $k$ of $N = a \boxtimes b$ is 0 exactly when it receives
no unit and no carry, so the carry vanishes at every 0 of $N$ and each run of
1s is a closed system. Between runs the only memory is the window of the last
$\deg a$ bits of $b$. The set of lengths of a run joining two given windows is
the set of lengths of accepting paths of a one-counter automaton (the counter
is the carry), i.e. a context-free language over one letter, hence ultimately
periodic by Parikh's theorem; a regular language of runs glued by a finite
control is regular. If $N_1$ has $i$ bits and $N_2$ has $j$ bits, then
$N_1 + 2^i N_2$ is a multiple with $i + j$ bits, so
$D_a(i + j) \ge D_a(i) D_a(j)$; for odd $a$, $D_a(n) > 0$ for all large $n$,
and Fekete's lemma applies.
(b)–(d), machine-checked by `exclusion.automata.multiples_dfa`: let $I$ be the
language of all multiples of $1 + x^s$, $U_K \subseteq I$ the outputs of runs
of the multiplication transducer with carry $\le K$, and $O_K \supseteq I$ the
outputs when carries $\ge K$ are remembered only modulo 2. The inclusion
$O_K \subseteq U_K$ is a finite automaton check; it holds with $K = 1$ for
$s = 1, 2$ and with some $K \le 6$ for $s \le 6$, so $I = U_K$, and for
$s = 1, 2$ its minimal DFA is equivalent to the DFA of the stated conditions.
The recurrences are found by Berlekamp–Massey and verified exactly.
Independently, the sets were compared with the products $5 \boxtimes b$
themselves for every $n \le 24$ and the counts for every $n \le 37$. $\square$

**Theorem 4 (density of the composites).** Let $C(n)$ be the number of odd
composites with $n$ bits. Every limit point $\gamma$ of $\log_2 C(n) / n$
satisfies

$$\mathbf{0.8061 \le \gamma \le 0.8747}.$$

(a) *Lower bound.* $D_a(n) - 1 \le C(n)$ for every odd $a \ge 3$, so
$\gamma \ge \gamma_a$; the certified automaton for $a = 65$ gives
$\gamma_{65} = 0.806113\ldots$
(b) *No-111 Lemma.* Let $N$ be a multiple of $1 + x^r$ and $b^{\ast}(N)$ its largest
cofactor. Then $b^{\ast}$ has no three 1s at positions $i - r, i, i + r$.
(c) *Upper bound.* At most $\tfrac{n^2}{2} 2^{E n}$ odd $n$-bit composites
have a factor of weight 2, with $E = 0.874665$, and at most
$2^{H(1/4) n + o(n)}$ have none ($H(1/4) = 0.811278$).

*Proof.* (a) A multiple of $a$ other than $a$ is composite.
(b) In $S$,
$(1 + x^r)(x^{i-r} + x^i + x^{i+r}) = (1 + x^r)(x^{i-r} + x^{i+1} + x^{i+r})$:
both sides are $x^{i-r}(1 + 2x^r + 2x^{2r} + x^{3r})$ after
$2x^k = x^k + x^{k+1}$. So moving the middle 1 of such a triple one place up
keeps the product, and it enlarges the cofactor because normalising never
lowers the integer value.
(c) Let $N = b \boxtimes c$ have $n$ bits and weight $W = w(b) w(c)$,
$w(b) \le w(c)$. If $w(b) = 2$, then $b = 1 + x^r$ and $N$ is determined by
$b^{\ast}(N)$, a word of at most $n - r$ bits and weight $W/2$ whose $r$ residue
classes avoid 111. Words without 111, each 1 weighted by $t$, number at most
$L(t)^{\ell+1}$ in length $\ell$, where $L^3 = L^2 + tL + t^2$ (a weighted
Tribonacci recurrence); so there are at most $t^{-W/2} L(t)^n$ such $N$ for
every $t > 0$, and at most $\binom{n}{W}$ by counting weights. With
$W = \theta n$ the two bounds cross at $\theta = 0.705340$, $t = 0.808173$,
where both equal $2^{En}$; sum over $r$ and $W$. If $w(b) = k \ge 3$, then
$k \le \sqrt n$ and there are at most $\binom{n}{W}$ such $N$ and at most
$\binom{n}{k}\binom{n}{W/k}$ pairs, and
$\min\bigl(\binom{n}{W}, \binom{n}{W/k}\bigr) \le 2^{H(1/(k+1)) n} \le 2^{H(1/4) n}$. $\square$

The weight count alone, without the No-111 Lemma, gives the elementary bound
$C(n) \le (n + o(1)) 2^{H(1/3) n}$, $H(1/3) = 0.918296$. The verification
script also evaluates the exact finite bound $U(n) \ge C(n)$ behind (c) for every
$n \le 37$ ($U(37)/C(37) = 19.6$).

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

**Pre-asymptotic gap.** The local slope $\log_2\bigl(C(n)/C(n-1)\bigr)$ is
about $0.786$ over $n = 32..37$ ($0.783$ at the last step, ratio $\approx 1.72$),
still *below* the proven lower bound $\gamma \ge \gamma_{65} = 0.8061$ (ratio
$\ge 1.7484$). The multiples of $2^s + 1$ with large $s$, which dominate
eventually, are still rare at this size, so the range $n \le 37$ is
pre-asymptotic and extrapolating $\gamma$ from the table would underestimate it.

Certified regular languages of multiples of $a = 2^s + 1$ (the states include
the sink; $\lambda_a$ is the exact dominant root of the minimal recurrence):

| $s$ | $a = 2^s + 1$ | states of the minimal DFA | order of the recurrence | growth rate $\lambda_a$ | $\gamma_a = \log_2 \lambda_a$ |
|---:|---:|---:|---:|---:|---:|
| 1 | 3 | 3 | 2 | 1.618034 | 0.694242 |
| 2 | 5 | 7 | 5 | 1.704903 | 0.769689 |
| 3 | 9 | 22 | 18 | 1.730329 | 0.791046 |
| 4 | 17 | 79 | 50 | 1.740744 | 0.799704 |
| 5 | 33 | 307 | 172 | 1.745791 | 0.803881 |
| 6 | 65 | 1292 | 589 | 1.748495 | 0.806113 |

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
>>> from exclusion.factor import all_ones_lengths, g_tilde, verify_carry_bridge, top_gap_irreducible
>>> sorted(all_ones_lengths(16)), g_tilde(4), verify_carry_bridge(3, 4), top_gap_irreducible(39)
([2, 3, 4], 39, True, True)
>>> from exclusion.automata import is_multiple_of_5, DFA5, count_odd
>>> [n for n in range(1, 64, 2) if is_multiple_of_5(n)], count_odd(DFA5, 12)[1:]
([5, 15, 29, 45, 63], [0, 0, 1, 1, 1, 2, 3, 6, 10, 17, 29, 49])
>>> from exclusion.automata import multiples_dfa, growth_rate
>>> str(growth_rate(multiples_dfa(3))[1])[:17]      # gamma_9, from an order-18 recurrence
'0.791046071188335'
```

`eadd` is the literal $\Theta(n)$ Lindley recursion on Python integers; `emul`
obtains the coefficients of the polynomial product from one big-integer
multiplication (Kronecker substitution) and normalises once. Neither has a
word size to overflow.

## Reproducing everything

| command | does | time |
|---|---|---|
| `pytest` | 39 tests: semiring axioms, Lindley vs. bitwise carry propagation, big-integer product vs. shift-and-add, $w$, $v_2$, $g$, quotients mod $2^m$, factorisation, Gap and Top-Gap Lemmas, Carry-Bridge, length sets of $2^m - 1$, multiples of 3, 5, 9, 17 and their exact growth rates, No-111 and the weighted upper bound, the C engine | 20 s |
| `python scripts/verify_theorems.py` | checks Theorems 1-4 and prints all tables (audit of Theorem 3 for $n \le 24$, $C(n)$ for $n \le 31$) | 90 s |
| `make -C src/c && src/c/count_composites 31` | $C(n)$, $n \le 31$, directly (128 MiB); add an odd `a` for $D_a(n)$ | 7 s |

Timings are for a 4-core x86-64 machine with GCC 13 and OpenMP. `EXCLUSION_NMAX=24 pytest`
extends the set-equality test for multiples of 5 to 24 bits; `--nmax` and
`--cmax` set the ranges of `verify_theorems.py` (the sieve needs
$2^{\mathrm{cmax} - 4}$ bytes: 8 GiB for the whole table, $n \le 37$). Where
the C engine cannot be built or run, the script falls back to the committed
counts in `data/count_odd_composites.txt` and says so. Python $\ge$ 3.10; no
dependencies outside the standard library (pytest for the tests, a C11
compiler for the sieve).

## Layout

```
src/exclusion/core.py        eadd, emul, epow, w, v2, g
src/exclusion/factor.py      quotients, divisors, irreducibility, factorisations and length sets, sieve,
                             Gap and Top-Gap Lemmas, Carry-Bridge, No-111 bound
src/exclusion/automata.py    recognisers for multiples of 3 and 5; certificate for 1 + x^s;
                             exact generating functions and growth rates
src/c/count_composites.c     C11 sieve for C(n) and D_a(n), OpenMP optional
scripts/verify_theorems.py   checks Theorems 1-4 and prints the tables
tests/test_exclusion.py      pytest suite
data/                        C(n) for n <= 37, as computed by the C sieve
```

MIT licence.
