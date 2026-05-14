# LC_Solver

**Lehmer-Clements enumerator for prime-complete products of consecutive integers**

By Ken Clements · Lehmer-Clements algorithm first described: May 1, 2026

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

For a fixed squarefree **mask** $q$ supported on $P_\omega = \{p_1, \ldots, p_\omega\}$,
consecutive smooth candidates arise from the Pell equation $x^2 - 2qy^2 = 1$
via $m_j = (x_j - 1)/2$. The key mathematical objects are:

| Symbol | Meaning |
|--------|---------|
| $T_p(q)$ | Period of the Pell sequence $x_j \bmod p$ |
| $E_p^\varepsilon(q)$ | Indices $j \bmod T_p(q)$ where $p \mid m_j + \varepsilon$ |
| $\sigma$ | Side assignment: each prime $p$ in $q$ gets $\sigma(p) \in \{0,1\}$ |
| $\Lambda(q,\sigma)$ | $\mathrm{lcm}_{p \mid q}\, T_p(q)$ — combined CRT period |
| $\lambda(q,\sigma)$ | Minimum $j \geq 1$ satisfying all entry conditions simultaneously (CRT) |
| $L_\omega$ | Størmer–Lehmer bound: $\max(3,\, p_\omega)$ |

**Key result:** If $\lambda(q,\sigma) > L_\omega$, the Pell family $(q, \sigma)$ contains
no prime-complete candidate. The CRT computation delivers this verdict with a single
arithmetic comparison — no candidate values need to be examined.

### Three algorithmic improvements over earlier versions

1. **3^ω work instead of 4^ω.**
   Earlier versions iterated $\sigma$ over all $\omega$ primes ($2^\omega$ sigmas per
   mask, $4^\omega$ total). Correct: $\sigma$ ranges only over the $k$ primes present
   in mask $q$, giving $\sum_k \binom{\omega}{k} 2^k = 3^\omega$ total pairs — a
   10× saving at $\omega = 8$.

2. **No matrix exponentiation.**
   Earlier versions called `mat_pow` to reach index $\lambda$, which blows up for
   large $\lambda$. Since $L_\omega \leq 59$ for all $\omega \leq 17$, iterating
   $j = 1 \ldots L$ via the cheap two-term Pell recurrence
   $(x,y) \to (x_1 x + D y_1 y,\; x_1 y + y_1 x)$
   is sufficient and requires no big-integer exponentiation.

3. **Canonical sigma halving.**
   A side assignment $\sigma$ and its complement $\bar\sigma$ always identify the
   same prime-complete $m$. By fixing $\sigma(p_{\min}) = 0$ as the canonical
   representative, the effective search space is halved with no loss of coverage.

---

## Files

| File | Description |
|------|-------------|
| `LC_Solver.py` | Single-process reference implementation (v3) |
| `LCm_Solver.py` | Multiprocessing version — masks parallelised across CPU cores (v1) |

Both versions produce identical output and use the same certificate format.
`LCm_Solver.py` is recommended for runs at $\omega \geq 12$.

---

## Dependencies

| Requirement | Notes |
|-------------|-------|
| Python 3.9+ | f-strings, `pow(a, -1, m)` modular inverse, dataclasses |
| [PARI/GP](https://pari.math.u-bordeaux.fr/) | Used for Pell fundamental-solution computation |

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

**Other platforms:** see https://pari.math.u-bordeaux.fr/download.html

No Python packages beyond the standard library are required.

---

## Quick Start

### Search mode — find all prime-complete products for ω = 2..8

```bash
python3 LC_Solver.py \
  --mode search \
  --start_omega 2 \
  --end_omega 8 \
  --outdir lc_audit \
  --gp_path /opt/homebrew/bin/gp
```

Expected output includes all 28 known A141399 values, one per HIT line.

### Certify mode — prove no solutions for ω = 9..17 (multiprocessing)

```bash
python3 LCm_Solver.py \
  --mode certify \
  --start_omega 9 \
  --end_omega 17 \
  --outdir lc_audit \
  --gp_path /opt/homebrew/bin/gp \
  --workers 10
```

On a 10-core Mac mini M-series this completes in under five hours and writes
`COMPLETE_NO_HITS` verdicts for every ω in the range. Users may notice a
considerable pause at the last mask count of each ω section as the last
worker thread processes the remaining masks alone.

---

## Command-Line Reference

All options apply to both `LC_Solver.py` and `LCm_Solver.py`.
`--workers` is available only in `LCm_Solver.py`.

| Option | Default | Description |
|--------|---------|-------------|
| `--mode` | `search` | `search`: find hits and record candidates; `certify`: classify all pairs without iterating candidates |
| `--start_omega` | `9` | First $\omega$ to process (inclusive) |
| `--end_omega` | `17` | Last $\omega$ to process (inclusive) |
| `--outdir` | `lc_audit` | Output directory for certificates and summaries |
| `--gp_path` | `gp` | Path to the `gp` binary |
| `--gp_timeout` | `300.0` | Seconds to wait for a single PARI/GP call |
| `--max_m` | `0` (unlimited) | Stop searching above this value of $m$ |
| `--max_period_factor` | `4` | Search window for entry-period computation: $4(p-1)$ |
| `--workers` | `1` | *(LCm only)* Number of parallel worker processes |
| `--debug` | off | Enable verbose debug output |
| `--version` | — | Print version JSON and exit |

---

## Output Structure

```
lc_audit/
├── lc_master_summary.json          ← top-level verdict across all ω
└── omega_09/
    ├── lc_certificates_omega_09.csv   ← one row per canonical (q,σ) pair
    └── lc_summary_omega_09.json       ← per-ω counts and SHA-256 of CSV
```

### Master summary (`lc_master_summary.json`)

```json
{
  "program": "LCm_Solver",
  "version": 1,
  "mode": "certify",
  "start_omega": 9,
  "end_omega": 17,
  "any_prime_complete_hit": false,
  "per_omega": [
    {
      "omega": 9,
      "L": 23,
      "total_pairs": 4374,
      "excluded_empty": 2187,
      "excluded_lambda": 2187,
      "hits_total": 0,
      "open_total": 0,
      "verdict": "COMPLETE_NO_HITS",
      "elapsed_sec": 12.4
    }
  ]
}
```

### Certificate CSV columns

| Column | Description |
|--------|-------------|
| `omega` | Prime-set order |
| `q` | Squarefree mask value (product of primes in mask) |
| `mask` | Bitmask index into $P_\omega$ |
| `sigma_str` | Side assignment, e.g. `p2:0,p3:1,p5:0` |
| `Lambda` | CRT period $\Lambda(q,\sigma)$ |
| `lambda_val` | First simultaneous-entry index $\lambda(q,\sigma)$, or `inf` |
| `L` | Størmer–Lehmer bound |
| `verdict` | `EXCLUDED_EMPTY`, `EXCLUDED_LAMBDA`, `HIT`, or `OPEN` |
| `hits` | Semicolon-separated list of prime-complete $m$ values found |
| `loop_iters` | Number of Pell iterates examined |
| `entry_periods` | Per-prime entry periods $T_p$ |
| `entry_residues` | Per-prime entry residue sets |

### Verdict meanings

| Verdict | Meaning |
|---------|---------|
| `EXCLUDED_EMPTY` | CRT system is inconsistent — no index $j$ satisfies all conditions |
| `EXCLUDED_LAMBDA` | First valid index $\lambda > L$ — outside the Størmer–Lehmer range |
| `HIT` | One or more prime-complete $m$ values found in $[1, L]$ |
| `OPEN` | A valid index $\lambda \leq L$ exists but the candidate is not prime-complete |

A complete certificate for a range $[\omega_1, \omega_2]$ requires every row to carry
verdict `EXCLUDED_EMPTY` or `EXCLUDED_LAMBDA` (no `HIT` or `OPEN` rows).

---

## Mathematical Background

### Why solutions must eventually stop

The primorial $P_r = 2 \cdot 3 \cdot 5 \cdots p_r$ bounds the prime-divisor count:
any $m < P_{r+1}$ satisfies $\omega(m) \leq r$. For $n(n+1)$ to be prime-complete
in the interval $P_r \leq n(n+1) < P_{r+1}$, its greatest prime factor index must
also satisfy $\pi(\mathrm{gpf}(n(n+1))) \leq r$.

The primorial barrier grows as $r \sim 2\log(n) / \log(\log(n))$, while smooth-number
theory (Dickman–de Bruijn) predicts the minimum greatest-prime-factor index grows as
$\sim (\log(n))^2 / (2\log(\log(n)))$. Their ratio grows as $\log(n)/4 \to \infty$,
implying that prime-complete products must become impossible beyond a finite point.

### Størmer's theorem

For any fixed finite prime set $P$, Størmer (1897) proved that there are only
finitely many pairs of consecutive $P$-smooth integers, and that all of them can
be found via Pell equations. This provides the finite-reduction framework: for each
fixed $\omega$, the Lehmer-Clements search is provably complete.

### The CRT tail-closure argument

The catch-up block $H_\omega = \{p_9, \ldots, p_\omega\}$ must be absorbed
simultaneously by the coprime pair $(n, n+1)$ for any order $\omega$ solution.
The CRT/LCM Catch-Up Proposition states: if $\lambda_{H_\omega}(q,\sigma) > L_\omega$
for every mask $q$ and side assignment $\sigma$, then no prime-complete products
of order $\omega$ exist. As $\omega$ grows, the LCM of entry periods grows far faster
than $L_\omega = p_\omega$, providing the analytic tail closure beyond the
computationally verified base.

Full details of the proof structure are given in `CRT_LCM_Catch_Up_Lemma.tex`
(see the companion repository).

---

## Reproducing the Certificate

```bash
# Full certification run, ω = 9..17, on a 10-core machine
python3 LCm_Solver.py \
  --mode certify \
  --start_omega 9 \
  --end_omega 17 \
  --outdir lc_cert_2026 \
  --gp_path $(which gp) \
  --workers $(nproc)

# Verify the master verdict
python3 -c "
import json
m = json.load(open('lc_cert_2026/lc_master_summary.json'))
print('any_hit:', m['any_prime_complete_hit'])
for p in m['per_omega']:
    print(f\"  omega={p['omega']}  verdict={p['verdict']}  elapsed={p['elapsed_sec']:.1f}s\")
"
```

Expected output:
```
any_hit: False
  omega=9   verdict=COMPLETE_NO_HITS  elapsed=...
  omega=10  verdict=COMPLETE_NO_HITS  elapsed=...
  ...
  omega=17  verdict=COMPLETE_NO_HITS  elapsed=...
```

The SHA-256 hash of each certificate CSV is recorded in the per-omega summary JSON,
providing a tamper-evident audit trail.

---

## Related Programs

- **[Nr_Solver](https://github.com/kenatiod/Nr_Solver)** — earlier Størmer–Lehmer enumerator for run-length $r$ products; data files for $\omega = 2$ to $17$ are archived there.
- **[Delta_min](https://github.com/kenatiod/Delta_min)** — C program that scans doubling intervals for the minimum $\pi(\mathrm{gpf}(n(n+1))) - \omega(n(n+1))$ gap, providing heuristic corroboration for finiteness across $n$ up to $2^{46}$.

---

## Citation

If you use this code or the certificate data in your research, please cite:

> Ken Clements, *LC_Solver: Lehmer-Clements enumerator for prime-complete products
> of consecutive integers*, GitHub, May 2026.
> https://github.com/kenatiod/LC_Solver

---

## Authors

Ken Clements May 2026.

Lehmer-Clements algorithm first described: May 1, 2026.

---

## License

This project is released under the [MIT License](LICENSE).
