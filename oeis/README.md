# OEIS submission package

Six sequences from Exclusion Arithmetic, the semiring `N_0[x]/(2 = 1 + x)` on
binary expansions. Everything in `drafts/` and `bfiles/` is written by
`scripts/generate_oeis.py`; do not edit those files by hand, regenerate them.

| # | key | draft | b-file | offset | batch |
|---|-----|-------|--------|--------|-------|
| 1 | `doubling` — a(n) = n [+] n | `drafts/1_doubling.txt` | `bfiles/b_doubling.txt` | 0,2 | 1 |
| 2 | `squares` — a(n) = n [x] n | `drafts/2_squares.txt` | `bfiles/b_squares.txt` | 0,3 | 1 |
| 3 | `odd_composites` | `drafts/3_odd_composites.txt` | `bfiles/b_odd_composites.txt` | 1,1 | 1 |
| 4 | `odd_irreducibles` | `drafts/4_odd_irreducibles.txt` | `bfiles/b_odd_irreducibles.txt` | 1,1 | 2 |
| 5 | `count_odd_composites` — C(n) | `drafts/5_count_odd_composites.txt` | `bfiles/b_count_odd_composites.txt` | 1,5 | 2 |
| 6 | `multiples_of_5` — D_5(n) | `drafts/6_multiples_of_5.txt` | `bfiles/b_multiples_of_5.txt` | 1,6 | 2 |

## Submission order

**Batch 1** (sequences 1-3) cites only entries that already exist in the OEIS
and can be submitted as it stands.

**Batch 2** (sequences 4-6) cites batch 1. The drafts show the batch 1 numbers
still missing as `A??????(key)`, and nothing else: another batch 2 sequence is
mentioned only once its own number is passed with `--a`. Once batch 1 has its
numbers (the submission form allocates an A-number as soon as a draft is
created), regenerate:

    python scripts/generate_oeis.py --cmax 37 \
        --a doubling=A3xxxxx --a squares=A3xxxxx --a odd_composites=A3xxxxx

and, as the batch 2 numbers are allocated, add
`--a odd_irreducibles=A3xxxxx --a count_odd_composites=A3xxxxx --a multiples_of_5=A3xxxxx`
to make the batch 2 drafts cite each other. With all six numbers given, the
batch 1 drafts also gain a "Sequences from the same semiring" cross-reference
line; add it to the published batch 1 entries by an ordinary edit.

## Checklist for each sequence

1. `python scripts/generate_oeis.py` ends with `ALL DRAFTS AND B-FILES VERIFIED`
   and reports `Python OK, PARI OK` (PARI needs `gp` on the PATH).
2. No `A??????` is left in the draft being submitted.
3. The repository URL in LINKS is live (`--repo URL` changes it).
4. Paste NAME, DATA, OFFSET, COMMENTS, FORMULA, EXAMPLE, PROG, CROSSREFS and
   KEYWORD into the corresponding fields; one line of the draft is one line of
   the field. AUTHOR is filled in by the form.
5. Upload the b-file; its first terms equal DATA term for term (checked by the
   generator), and its first index equals the offset.

## Conventions and choices

* **Notation.** Plain ASCII: `[+]` and `[x]` for the two operations, `_2` for
  binary numerals. Every draft defines the semiring in its first comment, so
  each entry can be read on its own.
* **Offsets.** The second number is the position of the first term exceeding 1
  in absolute value. For C(n) the terms are 0, 0, 0, 1, 2, ..., so the offset is
  `1,5` (not `1,4`: a(4) = 1).
* **Offset of D_5.** `1,6`, with a(1) = a(2) = 0, rather than `3,4`. With offset
  1 the recurrence a(n) = a(n-1) + a(n-2) + a(n-5) holds for every n >= 6 from
  the five initial terms 0, 0, 1, 1, 1 (with offset 3 it would refer to the
  undefined a(1), a(2) until n = 8); the generating function
  x^3 (1 - x^2)/(1 - x - x^2 - x^5) is the ordinary generating function with no
  shift; and the index is the bit length, as for C(n), so the bound
  D_5(n) <= C(n) for n >= 4 compares equal indices. The zeros are genuine
  values: no multiple of 5 has fewer than three binary digits.
* **Line ends.** Drafts and b-files are written with LF line ends on every
  platform, and `.gitattributes` keeps them so in a Windows checkout, so a
  b-file can be uploaded from any machine as it is.
* **Length of C(n).** The generator never shortens the committed b-file of
  C(n): run with a `--cmax` below the number of committed terms, it checks the
  engine against them and keeps them all. Extending the table needs
  `--cmax N` with N larger than the committed length.
* **b-files.** 10001 terms (n = 0..10000) for sequences 1-2, 10000 terms for
  3-4, every computed term for C(n), and n = 1..1000 for D_5 (from the
  certified automaton; equal to the brute-force counts as far as those reach).
* **Bounds quoted for C(n).** The draft of C(n) states the proved window
  0.8061 <= lim inf, lim sup <= 0.8747 for log_2(a(n))/n, with a sketch of each
  side: the certified automaton for the multiples of 65 (lower) and the No-111
  lemma with the weighted tribonacci/entropy trade-off (upper). The generator
  recomputes both constants and refuses to write the draft if they change.
* **Novelty.** On 2026-11-26 a search of the OEIS for the leading terms of each
  of the six sequences returned no match.
* **Existing entries cited**, each compared with its definition by the
  generator (and with its b-file on oeis.org under `--online`): A162276 (agrees
  with n [+] n for 1 <= n <= 10 only), A086799 (n [+] 1 = A086799(n+1)),
  A277335 (the set of values of n [+] n), A003714, A052294, A067139 (irreducibles
  of OR-numbral, i.e. dismal base-2, arithmetic, for contrast).
