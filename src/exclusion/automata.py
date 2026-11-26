"""Exact recognisers for the multiples of 3 = 1 + x and 5 = 1 + x^2 in S, and
a finite certificate that the multiples of 1 + x^s form a regular language.

Words are binary numerals read least significant bit first, padded with any
number of high zeros.  A DFA is a pair (table, accept): table[q] = (q0, q1)
are the successors of state q on bits 0 and 1, state 0 is initial.
"""

from decimal import Decimal, localcontext

from .core import v2

__all__ = [
    "runs", "is_multiple_of_3", "is_multiple_of_5", "DFA3", "DFA5",
    "multiples_dfa", "equivalent", "accepts", "count_odd", "odd_members",
    "rational_gf", "dominant_root", "growth_rate",
]


def runs(n):
    """Maximal runs of an odd n, LSB first: ([M_1..M_r], [Z_1..Z_{r-1}])."""
    ones, zeros = [], []
    while n:
        k = v2(n + 1)  # length of the run of 1s at the bottom
        ones.append(k)
        n >>= k
        if n:
            k = v2(n)
            zeros.append(k)
            n >>= k
    return ones, zeros


def is_multiple_of_3(n):
    """n in 3 [x] S  iff  every maximal run of 1s in n has even length."""
    return all(len(run) % 2 == 0 for run in format(n, "b").split("0"))


def is_multiple_of_5(n):
    """n in 5 [x] S, by the run criterion applied to the odd part of n.

    With u_i = (M_1 + ... + M_i) mod 2 and u_0 = 0:
      (1) u_r = 0;
      (2) u_i = 1 forces Z_i = 1;
      (3) no run of 1s of length 2 or 3 starts with u_{i-1} = 0.
    """
    if n == 0:
        return True
    ones, zeros = runs(n >> v2(n))
    u = 0
    for i, m in enumerate(ones):
        if u == 0 and m in (2, 3):
            return False
        u ^= m & 1
        if u == 1 and i < len(zeros) and zeros[i] != 1:
            return False
    return u == 0


# --- DFAs -------------------------------------------------------------------

def _tabulate(start, step, accepting):
    """The DFA reachable from `start` under step(state, bit)."""
    index, order, table = {start: 0}, [start], []
    for q in order:  # `order` grows while it is being scanned
        row = []
        for bit in (0, 1):
            r = step(q, bit)
            if r not in index:
                index[r] = len(order)
                order.append(r)
            row.append(index[r])
        table.append(tuple(row))
    return table, [accepting(q) for q in order]


def _minimize(dfa):
    """Moore partition refinement; the result is renumbered with start = 0."""
    table, accept = dfa
    block = [int(a) for a in accept]
    while True:
        names = {}
        refined = [
            names.setdefault((block[q], block[t0], block[t1]), len(names))
            for q, (t0, t1) in enumerate(table)
        ]
        done = len(names) == len(set(block))
        block = refined
        if done:
            break
    return _tabulate(
        block[0],
        lambda b, bit: block[table[block.index(b)][bit]],
        lambda b: accept[block.index(b)],
    )


def _step3(q, bit):
    # q = parity of the current run of 1s; None = dead
    if q is None:
        return None
    return q ^ 1 if bit else (None if q else 0)


def _step5(q, bit):
    # ("lead",)            low zeros, before the first 1
    # ("run", u, m, p)     inside a run of 1s that started in state u;
    #                      m = min(length, 4), p = length mod 2
    # ("gap", u, z)        inside a run of zeros, z = min(length, 2)
    if q is None:
        return None
    if q[0] == "lead":
        return ("run", 0, 1, 1) if bit else q
    if q[0] == "run":
        _, u, m, p = q
        if bit:
            return ("run", u, min(m + 1, 4), p ^ 1)
        return None if u == 0 and m in (2, 3) else ("gap", u ^ p, 1)
    _, u, z = q
    if bit:
        return ("run", u, 1, 1)
    return None if u else ("gap", 0, 2)  # after u = 1 the gap must be a single 0


def _accept5(q):
    if q is None or q[0] == "lead":
        return q is not None
    if q[0] == "gap":
        return q[1] == 0
    _, u, m, p = q
    return u == p and not (u == 0 and m in (2, 3))


DFA3 = _tabulate(0, _step3, lambda q: q == 0)
DFA5 = _tabulate(("lead",), _step5, _accept5)


# --- the multiplication transducer and its certificate ------------------------

def _moves(state, s, K, over):
    """Transitions (output bit, next state) of b -> (1 + x^s) [x] b.

    A state is (the last s input bits, carry).  Column k receives
    t = carry + b_k + b_{k-s} units, emits [t >= 1] and passes on max(t-1, 0).

    over=False: runs whose carry would exceed K are dropped   (under-approximation).
    over=True:  carries >= K are only remembered modulo 2, as the classes
                K and K + 1; a decrement of class K may land on K - 1 exactly
                or stay large                                  (over-approximation).
    """
    mem, c = state
    for bit in (0, 1):
        t = c + bit + mem[0]
        nxt = mem[1:] + (bit,)
        c2 = max(t - 1, 0)
        if over:
            if c2 >= K:
                c2 = K + (c2 - K) % 2
            if c == K and t == K:
                yield 1, (nxt, K + 1)
        elif c2 > K:
            continue
        yield (1 if t else 0), (nxt, c2)


def _quiet(state):
    return state[1] == 0 and not any(state[0])


def multiples_dfa(s, max_carry=6):
    """Minimal DFA of the multiples of 1 + x^s, with proof of correctness.

    Let I be the language of all multiples, U_K the outputs of runs with carry
    <= K and O_K the outputs of the abstracted transducer, so U_K <= I <= O_K.
    The function searches for K with O_K <= U_K; then I = U_K is regular and
    its determinisation is returned.  Raises ValueError if no K <= max_carry works.
    """
    start = ((0,) * s, 0)
    for K in range(1, max_carry + 1):
        succ = {}

        def step(S, bit):
            if (S, bit) not in succ:
                succ[S, bit] = frozenset(
                    q for p in S for out, q in _moves(p, s, K, False) if out == bit
                )
            return succ[S, bit]

        seen = {(start, frozenset([start]))}
        todo = list(seen)
        closed = True
        while todo and closed:
            p, S = todo.pop()
            if _quiet(p) and not any(map(_quiet, S)):
                closed = False  # a word of O_K outside U_K
            for out, q in _moves(p, s, K, True):
                pair = (q, step(S, out))
                if pair not in seen:
                    seen.add(pair)
                    todo.append(pair)
        if closed:
            dfa = _tabulate(frozenset([start]), step, lambda S: any(map(_quiet, S)))
            return _minimize(dfa)
    raise ValueError(f"no certificate with carry bound <= {max_carry}")


def equivalent(A, B):
    """True iff the DFAs A and B accept the same language."""
    seen = {(0, 0)}
    todo = [(0, 0)]
    while todo:
        p, q = todo.pop()
        if A[1][p] != B[1][q]:
            return False
        for bit in (0, 1):
            pair = (A[0][p][bit], B[0][q][bit])
            if pair not in seen:
                seen.add(pair)
                todo.append(pair)
    return True


def accepts(dfa, n):
    """Run the DFA on the binary digits of n, least significant first."""
    q = 0
    while n:
        q = dfa[0][q][n & 1]
        n >>= 1
    return dfa[1][q]


def count_odd(dfa, nmax):
    """[D(0), ..., D(nmax)], D(n) = number of odd n-bit integers accepted."""
    table, accept = dfa
    counts = [0]
    one = {table[0][1]: 1}   # states after a word starting and ending in 1
    zero = {}                # ... starting in 1 and ending in 0
    for _ in range(nmax):
        counts.append(sum(c for q, c in one.items() if accept[q]))
        nxt_one, nxt_zero = {}, {}
        for dist in (one, zero):
            for q, c in dist.items():
                nxt_zero[table[q][0]] = nxt_zero.get(table[q][0], 0) + c
                nxt_one[table[q][1]] = nxt_one.get(table[q][1], 0) + c
        one, zero = nxt_one, nxt_zero
    return counts


def odd_members(dfa, n):
    """Sorted list of the odd n-bit integers accepted by the DFA."""
    table, accept = dfa
    # live[q] = some accepting state is reachable from q
    live = set(q for q, a in enumerate(accept) if a)
    grew = True
    while grew:
        grew = False
        for q, row in enumerate(table):
            if q not in live and (row[0] in live or row[1] in live):
                live.add(q)
                grew = True
    out = []
    stack = [(table[0][1], 1, 1)] if n >= 1 else []
    while stack:
        q, value, length = stack.pop()
        if length == n:
            if accept[q] and value >> (n - 1):
                out.append(value)
            continue
        for bit in (0, 1):
            r = table[q][bit]
            if r in live:
                stack.append((r, value | bit << length, length + 1))
    return sorted(out)


# --- exact generating functions and growth rates ---------------------------------

def rational_gf(counts):
    """(P, Q): integer coefficient lists with sum counts[n] z^n = P(z) / Q(z), Q(0) = 1.

    The counts of a DFA with m states satisfy a linear recurrence of order
    <= m with integer coefficients.  Berlekamp-Massey modulo a large prime
    finds the shortest candidate; it is then verified exactly, over the
    integers, on every term supplied (ValueError otherwise).  Pass at least
    2 m + 2 terms.  The recurrence counts[n] = -sum_{i >= 1} Q[i] counts[n - i]
    holds for n > deg P.
    """
    p = (1 << 61) - 1
    c, b, L, m, last = [1], [1], 0, 1, 1
    for n, s in enumerate(counts):
        d = (s + sum(c[i] * counts[n - i] for i in range(1, L + 1))) % p
        if d == 0:
            m += 1
            continue
        t, coef = c[:], d * pow(last, -1, p) % p
        c += [0] * (len(b) + m - len(c))
        for i, x in enumerate(b):
            c[i + m] = (c[i + m] - coef * x) % p
        if 2 * L <= n:
            L, b, last, m = n + 1 - L, t, d, 1
        else:
            m += 1
    q = [x - p if x > p // 2 else x for x in (c + [0] * (L + 1))[: L + 1]]
    if 2 * L + 2 > len(counts) or any(
        sum(q[i] * counts[n - i] for i in range(L + 1)) for n in range(L, len(counts))
    ):
        raise ValueError("not enough terms, or no integer recurrence")
    num = [sum(q[i] * counts[n - i] for i in range(n + 1)) for n in range(L)]
    while q[-1] == 0:
        q.pop()
    while num and num[-1] == 0:
        num.pop()
    return num, q


def dominant_root(Q, digits=30):
    """The largest real root of x^k Q(1/x), k = deg Q, as a Decimal.

    For Q the denominator of a generating function with non-negative
    coefficients this is the growth rate of the coefficients.  Newton's
    method from x = 2, above every root here (the counts are at most 2^n).
    """
    with localcontext() as ctx:
        ctx.prec = digits + 15
        coeffs = [Decimal(c) for c in Q]
        k = len(coeffs) - 1
        x, tiny = Decimal(2), Decimal(10) ** -(digits + 8)
        for _ in range(1000):
            f = sum(c * x ** (k - i) for i, c in enumerate(coeffs))
            df = sum(c * (k - i) * x ** (k - i - 1) for i, c in enumerate(coeffs[:k]))
            step = f / df
            x -= step
            if abs(step) < tiny:
                break
        ctx.prec = digits
        return +x


def growth_rate(dfa, digits=30):
    """(lambda, log2 lambda) for the number of odd n-bit integers accepted by the DFA."""
    counts = count_odd(dfa, 4 * len(dfa[0]) + 40)
    lam = dominant_root(rational_gf(counts)[1], digits)
    with localcontext() as ctx:
        ctx.prec = digits
        return lam, lam.ln() / Decimal(2).ln()
