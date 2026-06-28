# LC_Solver: Lehmer–Clements Enumerator for Prime‑Complete Products

*Documentation for `LC_Solver.py`, version 6.6.*

Throughout this document **LCM** / **lcm** always means *least common multiple*.
The program's pruning engine is a **rank‑lcm engine**: it forms the least common
multiple of certain ranks of apparition. The older name "LCm" that appears in some
output filenames (e.g. `lcm_v6_summary_omega_NN.json`) is retained only for
continuity of existing data files and does not denote anything other than this
program.

---

## 1. High‑level purpose

`LC_Solver.py` implements the **Lehmer–Clements algorithm**, a specialised
Størmer–Lehmer–style Pell enumerator designed to study **prime‑complete products
of consecutive integers** of the form `m(m+1)` over a fixed initial prime set
`P_ω = {p_1, …, p_ω}`.

A positive integer is **prime‑complete** of order `ω` when its set of distinct
prime divisors is exactly the first `ω` primes `{2, 3, 5, …, p_ω}` — an unbroken
initial segment with no gaps. The known prime‑complete products `m(m+1)` are OEIS
[A141399](https://oeis.org/A141399); the largest, and conjecturally the last, is
`m = 633555` (order `ω = 8`).

LC_Solver does two things:

- **Search mode** finds and reports every prime‑complete `m(m+1)` of a given
  order, recovering the known A141399 values.
- **Certify mode** proves, level by level, that *no* prime‑complete `m(m+1)`
  exists at a given order beyond those already known — an unconditional statement
  given the Størmer–Lehmer index bound.

It is the computational engine of the unconditional finite base of the
termination argument for prime‑complete consecutive products.

---

## 2. Mathematical background and algorithm overview

### 2.1 Classical Størmer–Lehmer (for comparison)

By Størmer's theorem, every pair of consecutive `p_ω`‑smooth integers arises from
a solution of a Pell equation. Writing `x = 2m + 1`, the pair `m(m+1)` satisfies

```
x^2 − D y^2 = 1,     D | P_ω squarefree,
```

and the solutions are the powers `(x_1 + y_1 √D)^j` of the fundamental solution
`(x_1, y_1)`. We write `(x_j, y_j)` for the `j`‑th power and `m_j = (x_j − 1)/2`.
Lehmer's primitive‑divisor analysis bounds the relevant indices to

```
j ≤ L(ω) = max(30, p_ω + 1).
```

The classical enumeration tests every smooth pair at every admissible index. LC
adds the prime‑completeness requirement directly, which lets most discriminants
be discarded before any index is examined.

### 2.2 Lehmer–Clements fusion: the rank‑lcm engine

A prime‑complete pair of order `ω` must be divisible by **every** prime
`p_1, …, p_ω`. LC enforces this with two exact gates per squarefree discriminant
`D | P_ω`. (The discriminant used internally is `D = 2q` for a squarefree mask
product `q`; the description below is in terms of the effective `D`.)

**Gate 1 — y₁‑smoothness (Lucas divisibility).**
In the Pell–Lucas sequence `y_1 | y_j` for every `j`. Hence if `y_1` is not
`p_ω`‑smooth, no `y_j` is smooth, and `D` can produce no smooth pair at all. Such
discriminants are discarded immediately. This gate removes the large majority of
discriminants (for example, 128 443 of 131 071 at `ω = 17`).

**Gate 2 — rank‑lcm (the Lehmer–Clements condition).**
For an unramified odd prime `p ∤ D`, `p | y_j` **iff** `j` is a multiple of the
**rank of apparition**

```
ρ_p(D) = min { j ≥ 1 : p | y_j }.
```

For the pair at index `j` to be prime‑complete, *every* prime `p ≤ p_ω` not
already supplied by `D` or by `y_1` must divide `m_j(m_j+1)`. Therefore `j` must
be a common multiple of all the required ranks, i.e. a multiple of their least
common multiple

```
R(D) = lcm { ρ_p(D) : p missing }.
```

Two outcomes prune `D` outright, with no index examined:

- **rank_missing** — some required prime `p` has no rank within `j ≤ L` (its rank
  of apparition does not occur in the admissible window); that prime can never
  appear, so no prime‑complete pair exists for `D`.
- **LCM_EXCEEDS_L** — `R(D) > L(ω)`; no admissible index is a multiple of `R(D)`,
  so again no prime‑complete pair exists.

Only when `R(D) ≤ L(ω)` does `D` **survive**, and then only the multiples
`R(D), 2R(D), … ≤ L` need a full smoothness/completeness check. Missing primes are
processed largest‑first, since large primes tend to force large ranks and trip the
`R > L` cutoff early.

**Key logical property.** Pruning a discriminant by `R(D) > L` is exactly pruning
a branch of the search on which some required prime would necessarily have *zero*
exponent — a gap. This is the precise arithmetic form of "do not descend into any
branch that would leave a prime below the greatest prime factor missing."

---

## 3. What LC_Solver actually computes

### 3.1 Discriminants and Pell data

For a given `ω`, the prime set is `P_ω = (p_1, …, p_ω)`, with `pmax = p_ω` and the
index bound `L = max(30, p_ω + 1)`. A **mask** is an integer `1 ≤ mask < 2^ω`
whose 1‑bits select the primes whose product forms the squarefree `q`; the Pell
discriminant is `D = 2q`. Fundamental solutions `(x_1, y_1)` to `x^2 − D y^2 = 1`
are obtained from PARI/GP — in‑process through `cypari2` when available, otherwise
through a persistent `gp` subprocess with a validated handshake. Because `D` is
generated squarefree by construction, the Pell routine performs no internal
factorization.

### 3.2 Ranks of apparition and the rank‑lcm

For each missing prime `p`, the rank `ρ_p(D)` is found by iterating the
Pell–Lucas recurrence modulo `p` (in machine integers) up to `L`. The required
ranks are combined into `R(D) = lcm{ ρ_p(D) }`, accumulated largest‑prime‑first so
the `R > L` cutoff fires as early as possible. The result is one of the verdicts
of §2.2 (`rank_missing`, `LCM_EXCEEDS_L`, or *survive*).

### 3.3 Certify mode

In **certify mode** every squarefree `D | P_ω` is classified. Each `D` is sorted
into exactly one bucket: prefiltered, removed by Gate 1, removed by Gate 2
(`rank_missing` or `LCM_EXCEEDS_L`), or **survives** and has its admissible indices
`R(D), 2R(D), … ≤ L` checked for an actual prime‑complete pair. The accounting is
exact: every discriminant is accounted for. Certify mode refuses search caps and
runs a regression self‑test (below) before the certificate range. The verdict is
`COMPLETE_WITH_HITS` if any prime‑complete pair is found and `COMPLETE_NO_HITS`
otherwise; either is unconditional given the index bound `L`.

### 3.4 Search mode

**Search mode** does everything certify mode does and, for surviving
discriminants, runs the index check that records actual hits. For each admissible
index `j` (a multiple of `R(D)` up to `L`) it forms `(x_j, y_j)` by fast matrix
exponentiation of the Pell step matrix, takes `m = (x_j − 1)/2`, tests that both
`m` and `m+1` are `P_ω`‑smooth, and confirms that the combined support of their
factorizations is exactly `P_ω` (prime‑completeness). Any such `m` is recorded as
a **hit**. Search mode optionally accepts an `m`‑cap for partial runs; certify
mode does not.

---

## 4. The collapse of the survivor set

Beyond verification, the rank‑lcm engine exposes a striking empirical regularity.
Let `S(ω)` be the number of discriminants that survive both gates (and therefore
require an index check), and `C(ω)` the total indices then checked.

| ω | total D = 2^ω − 1 | Gate 1 removed | survivors S(ω) | indices C(ω) | hits |
|--:|------------------:|---------------:|---------------:|-------------:|-----:|
|  8 |    255 |   112 | 71 | 236 | 1 (m = 633555) |
|  9 |    511 |   287 | 66 | 194 | 0 |
| 10 |   1023 |   695 | 53 | 114 | 0 |
| 11 |   2047 |  1573 | 47 |  91 | 0 |
| 12 |   4095 |  3442 | 30 |  51 | 0 |
| 13 |   8191 |  7310 | 26 |  41 | 0 |
| 14 |  16383 | 15198 |  9 |  11 | 0 |
| 15 |  32767 | 31189 |  4 |  10 | 0 |
| 16 |  65535 | 63491 |  3 |   3 | 0 |
| 17 | 131071 | 128443 |  2 |   5 | 0 |

The survivor count `S(ω)` is **strictly decreasing** — 71, 66, 53, 47, 30, 26, 9,
4, 3, 2 — with no reappearance, even though the total number of discriminants
grows as `2^ω`. The survival **rate** `S(ω)/2^ω` falls from 0.28 at `ω = 8` to
about `1.5 × 10⁻⁵` at `ω = 17`. A least‑squares fit over `ω = 8…16` gives
`S(ω) ≈ exp(−0.42 ω + 8.1)`, a halving roughly every 1.6 levels; this fit,
formed without the `ω = 17` point, predicts `S(17) ≈ 2.4` against the measured 2 —
an out‑of‑sample confirmation.

In logarithms, per unit increase in `ω` the discriminant count contributes about
`+0.69` to `log S` while the survival rate contributes about `−1.11`, for a net
`−0.42`: **the rank‑lcm survival rate decays faster than the discriminant count
grows.** Only `ω = 8` produces a smooth pair at all (the terminal 633555); every
later level checked is empty.

This points to a combinatorial route to the termination theorem — a proof that
`S(ω) = 0` for all `ω` beyond an explicit threshold, a statement about the
distribution of ranks of apparition `ρ_p(D)` in Pell–Lucas sequences. The
monotone decay is verified through `ω = 17`; it is strong evidence, not yet a
proof. See `LehmerClements_note.pdf` for the formal treatment and the precise open
conjecture.

---

## 5. Program structure, outputs, and usage

### 5.1 Per‑ω driver and parallelism

For each `ω`, work is split into high‑prime **mask blocks** distributed across
worker processes; each worker generates and classifies its discriminants in
place. A per‑ω summary JSON records the full pruning funnel (discriminants by
gate, survivors, candidate indices, indices checked, hits), the verdict, and
timing. Per‑discriminant audit CSVs are emitted for small `ω`.

### 5.2 Checkpointing and resume

Long orders checkpoint periodically. The checkpoint stores **both** the set of
completed mask‑blocks **and** the aggregated funnel statistics accumulated so far.
On resume, the totals are seeded from the checkpoint so that a fully‑ or
partially‑resumed order reports correct accounting and writes an accurate summary
JSON. (Checkpoints are keyed by `ω` and the block split `H`, and by program
version, so checkpoints from an incompatible split or version are ignored rather
than misread.)

### 5.3 Outputs

| File (per ω) | Contents |
|--------------|----------|
| `lcm_v6_summary_omega_NN.json` | Funnel counts, survivors, indices, hits, verdict, timing |
| `lcm_v6_D_audit_omega_NN.csv`  | Per‑discriminant audit (small ω) |
| `lcm_v6_hits_omega_NN.csv`     | Prime‑complete pairs found |
| `lcm_v6_slow_D_omega_NN.csv`   | Slowest discriminants (diagnostics) |
| `lcm_v6_3_checkpoint_omega_NN_HNN.json` | Resume state (blocks + stats) |
| `lcm_v6_master_summary.json`   | Combined summary across the ω range |

(The `lcm_v6_` filename prefix is a historical artifact and, as noted at the top,
does not denote "least common multiple"; LCM is reserved for that meaning in this
documentation.)

### 5.4 Command‑line usage

Search mode, recover all known pairs for ω = 2…8:

```bash
python3 LC_Solver.py --mode search --start_omega 2 --end_omega 8 \
  --outdir lc_audit_v6 --gp_path /opt/homebrew/bin/gp --workers 10
```

Certify mode, prove no solutions for ω = 9…20 (multi‑day at the top end):

```bash
python3 LC_Solver.py --mode certify --start_omega 9 --end_omega 20 \
  --outdir lc_audit_v6 --gp_path /opt/homebrew/bin/gp --workers 10
```

Self‑test only, verify the engine against the known catalogue:

```bash
python3 LC_Solver.py --self_test_only --start_omega 1 --end_omega 8
```

Run `python3 LC_Solver.py --version` to print the version and which accelerators
(`cypari2`, `gmpy2`) are active.

---

## 6. Why the results are trustworthy

### 6.1 Soundness of the pruning

Both gates are exact necessary conditions. Gate 1 is Lucas divisibility
(`y_1 | y_j`), so a non‑smooth `y_1` provably forbids any smooth `y_j`. Gate 2 is
the rank condition: a missing prime divides `y_j` only at multiples of its rank,
so a prime‑complete index must be a multiple of `R(D) = lcm{ρ_p(D)}`; if that
exceeds `L`, no admissible index qualifies. A `COMPLETE_NO_HITS` verdict is
therefore unconditional given the validity of the index ceiling `L = max(30,
p_ω + 1)`.

### 6.2 Self‑test gate

Before any certificate range, certify mode runs a regression that re‑derives all
28 catalogued prime‑complete pairs for `ω ≤ 8` (A141399) and aborts on any
discrepancy. The reference runs recover `633555` at `ω = 8` and find nothing
above.

### 6.3 Exact accounting

Every discriminant is classified into exactly one bucket, and the summary asserts
`accounting_ok` only when the bucket counts reconcile with `2^ω − 1` and every
mask‑block is marked complete. The checkpoint‑stats mechanism (§5.2) makes this
accounting correct across interrupted and resumed runs.

### 6.4 External verifiability

Hits and the full funnel are written as plain JSON/CSV, and any reported pair can
be checked independently by factoring `m` and `m+1`. The Pell fundamental
solutions come from PARI/GP, an established computer‑algebra system.

---

## 7. Practical notes

- PARI/GP is required (`brew install pari` on macOS, `apt-get install pari-gp` on
  Debian/Ubuntu); `cypari2` and `gmpy2` are optional accelerators.
- Run time rises steeply with `ω`: `ω = 16` decides in roughly 18 minutes and
  `ω = 17` in about five hours on a single multi‑core host; higher orders are
  multi‑day and benefit from checkpoint/resume.
- For the termination program, certify mode is the relevant mode; search mode is
  for recovering and auditing the known pairs.

## End of Document
