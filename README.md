# LC_Solver

**Lehmer-Clements enumerator for prime-complete products of consecutive integers**

By Ken Clements · Lehmer-Clements algorithm first described: May 1, 2026
· v6.4-prune (rank-LCM engine): June 2026

---

## What This Is

LC_Solver exhaustively searches for — and certifies the absence of — *prime-complete* products
of the form $n(n+1)$ for a given range of prime-set orders $\omega$.

A positive integer $m$ is **prime-complete** if its set of distinct prime divisors is exactly
$\{2, 3, 5, \ldots, p_k\}$ for some $k$ — the first $k$ primes with no gaps.
Equivalently, $\omega(m) = \pi(\mathrm{gpf}(m))$: the count of distinct prime divisors
equals the prime-counting index of the greatest prime factor.

The known prime-complete products $n(n+1)$ form OEIS sequence
[A141399](https://oeis.org/A141399), comprising 28 values:

```
n = 1, 2, 3, 5, 8, 9, 14, 15, 20, 24, 35, 80, 125, 224, 384, 440, 539, 714,
    1715, 2079, 2400, 3024, 4374, 9800, 12375, 123200, 194480, 633555
```

The last term, $n = 633{,}555$, gives $633555 \times 633556 = 401{,}393{,}062{,}580$,
whose prime divisors are $\{2, 3, 5, 7, 11, 13, 17, 19\}$ — the first eight primes.
This program is part of an ongoing effort to prove that **no further terms exist**.

---

## The Lehmer-Clements Algorithm

The algorithm is a specialisation of the classical Størmer–Lehmer Pell enumeration that
fuses the smoothness and prime-completeness checks directly into the Pell iterate loop.
A prime-complete pair of order $\omega$ must be divisible by **every** prime
$p_1, \ldots, p_\omega$. The Lehmer-Clements idea is to prune, as early as possible, any
Pell family in which some required prime would necessarily have **zero exponent** — a gap.
After $\omega = 6$ such gaps become unavoidable for most families, and the prunable
fraction grows rapidly with $\omega$.

For a squarefree discriminant $D \mid P_\omega$, consecutive smooth candidates arise from
the Pell equation $x^2 - D y^2 = 1$ via $m_j = (x_j - 1)/2$, where $(x_j, y_j)$ is the
$j$-th power of the fundamental solution. Lehmer's primitive-divisor bound limits the
relevant indices to $j \le L(\omega) = \max(30,\, p_\omega + 1)$.

### The v6.4 rank-LCM engine

Version 6 replaces the explicit side-assignment ($\sigma$) enumeration of earlier versions
with a **rank-of-apparition** condition that prunes whole discriminants with a single
LCM comparison. Two exact gates are applied to each $D$:

| Symbol | Meaning |
|--------|---------|
| $(x_1, y_1)$ | Fundamental Pell solution for discriminant $D$ |
| $\rho_p(D)$ | **Rank of apparition**: $\min\{j \ge 1 : p \mid y_j\}$ |
| $R(D)$ | $\mathrm{lcm}\{\rho_p(D) : p \text{ missing from } D \text{ and } y_1\}$ |
| $L(\omega)$ | Index ceiling $\max(30,\, p_\omega + 1)$ |

**Gate 1 — $y_1$-smoothness (Lucas divisibility).**
Since $y_1 \mid y_j$ for every $j$, if $y_1$ is not $p_\omega$-smooth then no $y_j$ is, and
$D$ can produce no smooth pair. This removes the large majority of discriminants
(e.g. 63,491 of 65,535 at $\omega = 16$).

**Gate 2 — rank-LCM (the Lehmer-Clements condition).**
For an unramified odd prime $p \nmid D$, $p \mid y_j$ iff $j$ is a multiple of $\rho_p(D)$.
For the pair to carry **all** missing primes, $j$ must be a common multiple of every
required $\rho_p(D)$, hence a multiple of $R(D)$. Then:

- if any required prime has no rank within $j \le L$, the prime can never appear — $D$ is dead;
- if $R(D) > L(\omega)$, no admissible index is a multiple of $R(D)$ — no prime-complete pair exists;
- otherwise $D$ **survives**, and only the multiples $R(D), 2R(D), \ldots \le L$ need a full check.

**Key result:** If $R(D) > L(\omega)$, the discriminant $D$ contains no prime-complete
candidate. The rank-LCM computation delivers this verdict with a single arithmetic
comparison — no candidate values need to be examined. Pruning by $R > L$ is exactly
pruning a branch on which some required prime would have zero exponent.

A "certify" verdict is **unconditional given the index ceiling** $L(\omega)$: the rank-LCM
condition is necessary for any prime-complete index, and all indices $\le L$ are exhausted.

---

## The collapsing search space

The rank-LCM engine exposes a striking regularity. Let $S(\omega)$ be the number of
discriminants that **survive both gates** (and therefore require a Pell index check), and
$C(\omega)$ the total indices then checked. Measured values:

| $\omega$ | total $D = 2^\omega - 1$ | survivors $S(\omega)$ | indices $C(\omega)$ | hits |
|---------:|-------------------------:|----------------------:|--------------------:|-----:|
|  8 |    255 | 71 | 236 | 1 (n = 633555) |
|  9 |    511 | 66 | 194 | 0 |
| 10 |   1023 | 53 | 114 | 0 |
| 11 |   2047 | 47 |  91 | 0 |
| 12 |   4095 | 30 |  51 | 0 |
| 13 |   8191 | 26 |  41 | 0 |
| 14 |  16383 |  9 |  11 | 0 |
| 15 |  32767 |  4 |  10 | 0 |
| 16 |  65535 |  3 |   3 | 0 |

The survivor count $S(\omega)$ is **strictly decreasing** — 71, 66, 53, 47, 30, 26, 9, 4, 3 —
with no reappearance, even though the total number of discriminants grows as $2^\omega$.
The survival **rate** $S(\omega)/2^\omega$ falls from 0.28 at $\omega = 8$ to
$4.6 \times 10^{-5}$ at $\omega = 16$. A fit gives $S(\omega) \approx \exp(-0.42\,\omega + 8.1)$,
a halving roughly every 1.65 levels.

In logarithmic terms, per unit increase in $\omega$ the discriminant count contributes
$+\log 2 \approx +0.69$ while the survival rate contributes about $-1.11$, for a net
$-0.42$: **the rank-LCM survival rate decays faster than the discriminant count grows.**
Only $\omega = 8$ produces a smooth pair at all (the terminal 633555); every later level
checked is empty.

This points to a combinatorial route to the termination theorem: a bound showing
$S(\omega) = 0$ for all $\omega$ beyond an explicit threshold — a statement about the
distribution of ranks of apparition $\rho_p(D)$ in Pell–Lucas sequences. See
`LehmerClements_note.pdf` for details. The monotone decay is verified through $\omega = 16$;
this is strong evidence, not yet a proof.

---

## Files

| File | Description |
|------|-------------|
| `LCm_Solver_v6_4_prune.py` | Current multiprocessing reference implementation (v6.4, rank-LCM engine) |
| `lcm_v6_summary_omega_*.json` | Per-order run summaries (discriminant counts by gate, survivors, indices, hits) |
| `lcm_v6_master_summary.json` | Combined summary across an omega range |
| `LehmerClements_note.pdf` | Formal write-up: pruning gates, soundness, and the survivor-collapse finding |

Earlier single-process versions (`LC_Solver.py`, v3) remain in the history for reference;
`LCm_Solver_v6_4_prune.py` is recommended for all runs.

---

## Dependencies

| Requirement | Notes |
|-------------|-------|
| Python 3.9+ | f-strings, `pow(a, -1, m)` modular inverse, dataclasses |
| [PARI/GP](https://pari.math.u-bordeaux.fr/) | Pell fundamental-solution computation |
| `cypari2` *(optional)* | In-process PARI fast path; falls back to a persistent `gp` subprocess if absent |
| `gmpy2` *(optional)* | Faster big-integer factor-removal in the smoothness check |

### Installing PARI/GP

**macOS (Homebrew):**
```bash
brew install pari
which gp          # typically /opt/homebrew/bin/gp
```

**Ubuntu / Debian:**
```bash
sudo apt-get install pari-gp
which gp          # typically /usr/bin/gp
```

Optional accelerators:
```bash
pip install cypari2 gmpy2
```

**Other platforms:** see https://pari.math.u-bordeaux.fr/download.html

---

## Quick Start

### Search mode — recover all prime-complete products for ω = 2..8

```bash
python3 LCm_Solver_v6_4_prune.py \
  --mode search \
  --start_omega 2 \
  --end_omega 8 \
  --outdir lc_audit_v6 \
  --gp_path /opt/homebrew/bin/gp \
  --workers 10
```

Expected output includes all 28 known A141399 values, with `633555` recovered at ω = 8.

### Certify mode — prove no solutions for ω = 9..17 (multiprocessing)

```bash
python3 LCm_Solver_v6_4_prune.py \
  --mode certify \
  --start_omega 9 \
  --end_omega 17 \
  --outdir lc_audit_v6 \
  --gp_path /opt/homebrew/bin/gp \
  --workers 10
```

Certify mode refuses search caps and runs the full A141399 self-test gate (ω ≤ 8) before
the certificate range. Each ω writes a `COMPLETE_NO_HITS` verdict and a summary JSON.
The per-ω run time rises with ω; ω = 16 decides in roughly 18 minutes on a 10-core host,
with only three discriminants reaching an index check.

### Self-test only — verify the engine against the known catalogue

```bash
python3 LCm_Solver_v6_4_prune.py --self_test_only --start_omega 1 --end_omega 8
```

---

## Command-Line Reference

| Option | Default | Description |
|--------|---------|-------------|
| `--mode` | `search` | `search`: record hits; `certify`: classify all discriminants, refuse caps |
| `--start_omega` | `2` | First $\omega$ to process (inclusive) |
| `--end_omega` | `9` | Last $\omega$ to process (inclusive) |
| `--outdir` | `lc_audit_v6` | Output directory for summaries and audit CSVs |
| `--gp_path` | `gp` | Path to the PARI/GP binary |
| `--workers` | all cores | Number of worker processes |
| `--max_m_expo` | `0` | If > 0, cap search to $m \le 10^{\text{expo}}$ (search mode only; certify refuses) |
| `--L_override` | `0` | Override the index ceiling $L$ (certify refuses values below the proven $L$) |
| `--max_low_bits` | `0` | Load-balance granularity; 0 schedules one discriminant mask per task |
| `--scheduler` | `hard_first` | Block order: `hard_first` submits heavy blocks first to reduce tail stalls |
| `--d_csv_cutoff` | `20` | Emit per-discriminant audit CSV when $\omega \le$ this value |
| `--slow_d_limit` | `50` | Retain this many slowest discriminants in a separate audit |
| `--no_self_test` | off | Skip the known-pair regression gate (not recommended) |
| `--self_test_only` | off | Run only the known-pair regression gate |
| `--version` | — | Print version and accelerator availability, then exit |

---

## Verdict semantics

| Verdict | Meaning |
|---------|---------|
| `COMPLETE_WITH_HITS` | All discriminants classified; one or more prime-complete pairs found |
| `COMPLETE_NO_HITS` | All discriminants classified; no prime-complete pair exists at this ω (given $L$) |

Each summary JSON records the full pruning funnel: discriminants removed by the $y_1$ gate,
by the rank-LCM gate (`n_rank_lcm_exceeds`), the survivors (`n_rank_survives`), the indices
checked, and any hits. The accounting is exact — every discriminant is classified.

---

## Status of the proof

This program supplies the **unconditional finite base** of the termination argument: it
certifies, level by level, that no prime-complete product $n(n+1)$ exists beyond 633555 for
each ω it processes. The accompanying analysis (floor/ceiling crossing against
[A002072](https://oeis.org/A002072), and the rank-LCM survivor collapse documented here)
addresses the tail. A full unconditional proof for all ω remains open; the rank-LCM survival
bound (this README's central finding) and an effective sublinear bound on the A002072 ceiling
are two routes toward it.

---

## License

See the repository for license details.

## Citation

If you use this software or its results, please cite the repository and the accompanying note,
*The Lehmer-Clements enumerator: rank-LCM pruning for prime-complete consecutive pairs*
(K. Clements, 2026).
