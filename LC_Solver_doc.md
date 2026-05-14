# LC_Solver: Lehmer–Clements Enumerator for Prime‑Complete Products

## 1. High‑level purpose

`LC_Solver.py` implements the **Lehmer–Clements algorithm**, a specialised Størmer–Lehmer–style Pell enumerator designed to study **prime‑complete products of consecutive integers** of the form \(m(m+1)\) over a fixed initial prime set \(P_\omega = \{p_1,\dots,p_\omega\}\).[file:1]  

For each \(\omega\) in a user‑specified range, the program systematically explores all squarefree masks \(q\) over \(P_\omega\) and all side assignments \(\sigma : P_\omega \to \{0,1\}\).[file:1]  

- A **prime‑complete hit** is an integer \(m > 0\) such that:
  - both \(m\) and \(m+1\) are \(P_\omega\)-smooth, and  
  - the product \(m(m+1)\) involves **exactly** the primes in \(P_\omega\) (no missing primes, no extra primes).[file:1]

For each pair \((q,\sigma)\), LC_Solver either:

- **Certifies impossibility** of a prime‑complete hit up to the Størmer–Lehmer bound \(L_\omega = \max(3, p_\omega)\), or  
- **Finds and records hits**, or  
- In rare cases, declares the pair still **OPEN** (search mode) if \(\lambda \le L_\omega\) and the fused Pell loop produced no hit.[file:1]

The program writes per‑\(\omega\) CSV and JSON certificate files plus a master summary that can be audited independently.

---

## 2. Mathematical background and algorithm overview

### 2.1 Classical Størmer–Lehmer (for comparison)

In the “classical” Nr_Solver‑style Størmer–Lehmer approach, one proceeds as follows for each squarefree mask \(q\) over \(P_\omega\):[file:1]

1. Solve the Pell equation \(x^2 - 2q y^2 = 1\) and enumerate the Pell family
   \[
   m_j(q) = \frac{x_j - 1}{2}, \quad j = 1,\dots,L_\omega.
   \]
2. Filter these \(m_j\) by \(P_\omega\)‑smoothness of \(m_j(m_j+1)\).
3. Filter the survivors by prime‑completeness \(\mathrm{rad}(m_j(m_j+1)) = p_\omega^\#\).[file:1]

This works but does a lot of **redundant Pell iteration** where per‑prime divisibility conditions are obviously impossible.

### 2.2 Lehmer–Clements fusion

LC_Solver fuses the per‑prime conditions into the Pell iterate loop using periodicity modulo primes and the Chinese Remainder Theorem (CRT).[file:1]

For each prime \(p_i \in P_\omega\) and side \(\varepsilon \in \{0,1\}\):

- The Pell sequence \((x_j)\) modulo \(p_i\) is periodic with some period \(T_i(q)\).[file:1]  
- The “entry set”
  \[
  E_i^{(\varepsilon)}(q) = \{ j \bmod T_i(q) : p_i \mid m_j(q) + \varepsilon \}
  \]
  is a union of residue classes modulo \(T_i(q)\).[file:1]

A **side assignment**
\[
\sigma : P_\omega \to \{0,1\}
\]
specifies for each prime whether it divides \(m\) or \(m+1\).[file:1]  

The CRT combines all per‑prime congruence conditions into:

- a **combined period** \(\Lambda(q,\sigma) = \mathrm{lcm}_{p_i \in P_\omega} T_i(q)\), and  
- a **first compatible index** \(\lambda(q,\sigma)\), the smallest \(j \ge 1\) satisfying all per‑prime congruences simultaneously.[file:1]

The fused Pell loop then only has to examine Pell indices of the form
\[
j = \lambda, \lambda + \Lambda, \lambda + 2\Lambda, \dots
\]
up to the Størmer–Lehmer bound \(L_\omega\).[file:1]

**Key logical property:** if \(\lambda(q,\sigma) > L_\omega\), the loop body never runs. This is not merely a computational shortcut; it is a **certificate** that no prime‑complete hit can occur for that \((q,\sigma)\) up to the Størmer–Lehmer bound.[file:1]

---

## 3. What LC_Solver actually computes

### 3.1 Masks, side assignments, and Pell data

For a given \(\omega\):

- The prime set is \(P_\omega = (p_1,\dots,p_\omega)\) obtained by `first_n_primes(omega)`, with `pmax = p_omega` and `L = max(3, pmax)`.[file:1]
- A **mask** is an integer \(1 \le \text{mask} < 2^\omega\).  
  The function `q_from_mask(mask, primes)` multiplies the primes corresponding to 1‑bits of `mask` to obtain the squarefree \(q\).[file:1]
- The Pell discriminant is \(D = 2q\).[file:1]
- The program calls PARI/GP’s `pellxy(D, max_x)` to obtain the **fundamental Pell solution** \((x_1,y_1)\) to \(x^2 - D y^2 = 1\), via a robust subprocess handshake that validates a test case and supports optional `max_x` ceilings.[file:1]

For each prime \(p \in P_\omega\) and each side \(\varepsilon \in \{0,1\}\), the routine
`compute_entry_period_and_residues(prime_p, side, x1, y1, D, max_period)`
computes:

- the period \(T\) of the Pell sequence modulo \(p\), and  
- the list of residues \(j \in [1, T]\) where the side condition holds:  
  - side \(= 0\): \(p \mid m_j\) ↔ \(x_j \equiv 1 \pmod p\)  
  - side \(= 1\): \(p \mid m_j + 1\) ↔ \(x_j \equiv -1 \pmod p\).[file:1]

These data are stored in `period_data[p] = (T0, r0, T1, r1)` for all primes in \(P_\omega\).[file:1]

### 3.2 Computing \(\lambda\) and \(\Lambda\) for a given \((q,\sigma)\)

Given `period_data` and a side assignment \(\sigma\), `compute_lambda_lambda(...)`:

1. Chooses for each prime \(p\) either the “side 0” or “side 1” period and residue set based on `sigma[p]`.[file:1]  
2. Populates dictionaries:
   - `entry_periods[p] = T_p(q,σ(p))`
   - `entry_residues[p] = [residues modulo T_p(q,σ(p))]`.[file:1]
3. Declares the system **inconsistent** if any prime’s residue list is empty (i.e. the required side condition never occurs modulo \(p\)).[file:1]
4. Computes
   \[
   \Lambda = \mathrm{lcm}\bigl( T_p(q, \sigma(p)) \bigr)
   \]
   using `lcm_list` over all populated `entry_periods`.[file:1]
5. If not inconsistent, uses a product of CRT combinations over all primes and residue choices to find the minimal positive \(j\) satisfying all congruences simultaneously; this is \(\lambda(q,\sigma)\).[file:1]  
   - CRT is implemented by `crt_combine` and `crt_system`, with explicit detection of inconsistent pairs and proper handling of moduli via gcd and modular inverses.[file:1]

The function returns `(lambda_val, Lambda, entry_periods, entry_residues, inconsistent)`.[file:1]

### 3.3 Certify mode

In **certify mode** (`--mode certify`):

- For each mask \(q\) and each side assignment `sigma` over **all primes in \(P_\omega\)**, LC_Solver:
  1. Precomputes `period_data` for all primes once.[file:1]
  2. Calls `compute_lambda_lambda` to obtain \(\lambda(q,\sigma)\) and \(\Lambda(q,\sigma)\).[file:1]
  3. Issues one of three verdicts:[file:1]
     - `EXCLUDED_EMPTY`: at least one prime had no valid residues on its assigned side (CRT system empty).  
     - `EXCLUDED_LAMBDA`: \(\lambda > L\) so no compatible Pell index is reachable before the Størmer–Lehmer bound.  
     - `OPEN`: \(\lambda \le L\); computation stops here in certify mode, deferring full search to `--mode search`.

Each such result is recorded in an `LCCertificate` dataclass instance with the following fields:[file:1]

- `omega, q, mask, sigma`  
- `entry_periods, entry_residues`  
- `Lambda, lambda_val, L`  
- `verdict ∈ {EXCLUDED_EMPTY, EXCLUDED_LAMBDA, OPEN}`  
- `hits = []`, `loop_iterations = 0`, `elapsed_sec`.[file:1]

### 3.4 Search mode (fused iterate loop)

In **search mode** (`--mode search`) the program does everything certify mode does, *plus* a fused Pell iterate loop for `OPEN` pairs:[file:1]

1. For each mask \(q\) and side assignment `sigma`, `compute_lambda_lambda` returns \(\lambda, \Lambda\) and consistency status.[file:1]
2. If inconsistent or \(\lambda > L\), the same `EXCLUDED_EMPTY` / `EXCLUDED_LAMBDA` verdicts are issued. No loop runs.[file:1]
3. If \(\lambda \le L\), LC_Solver:
   - Computes the matrix
     \[
     M = \begin{pmatrix}x_1 & D y_1 \\ y_1 & x_1\end{pmatrix}
     \]
     and uses fast exponentiation (`mat_pow`) to get:
       - `Ml = M^lambda` yielding \((x_\lambda, y_\lambda)\),
       - `Ms = M^Lambda` as the “step” matrix to move from \(j\) to \(j+\Lambda\).[file:1]
   - Starts from \((x_j,y_j) = (x_\lambda, y_\lambda)\) and repeatedly:
     1. Checks if `xj` is odd and \(m = (x_j - 1)/2 > 0\).[file:1]
     2. If a `max_m` bound is requested (`--max_m`), exits early if \(m > \text{max_m}\).[file:1]
     3. Tests whether both \(m\) and \(m+1\) are \(P_\omega\)‑smooth using `is_P_smooth`.[file:1]
     4. Factors \(m\) and \(m+1\) over \(P_\omega\) and ensures no leftover factor remains (i.e. both completely factor over \(P_\omega\)) using `factor_over_P`.[file:1]
     5. Merges exponents and checks that the **support** (set of primes) of the combined factorization equals the whole `primes` tuple, certifying prime‑completeness via `support_tuple(merged) == primes`.[file:1]
     6. Records any such `m` as a **HIT**.[file:1]
   - Steps \((x_j,y_j)\) forward via `Ms` and increments `j` by \(\Lambda\) until \(j > L\).[file:1]

The final verdict is:

- `HIT` if at least one prime‑complete \(m\) was found;  
- `OPEN` otherwise (consistent CRT system, \(\lambda \le L\), but no hit witnessed up to the bound).[file:1]

These richer certificates record:

- All fields from certify mode, plus:
  - `hits` (list of hit values `m`),  
  - `loop_iterations` (number of Pell loop iterations for this pair).[file:1]

---

## 4. Program structure, outputs, and usage

### 4.1 Top‑level driver per ω

The core driver `run_omega(...)`:

- Sets `all_primes = first_n_primes(omega)`, `pmax = all_primes[-1]`, `L = max(3, pmax)`.[file:1]
- Iterates over all masks `mask` in `[1, 2^omega)` and corresponding `q = q_from_mask(mask, all_primes)`, skipping the degenerate `q = 2` case.[file:1]
- For each mask, obtains the fundamental Pell solution via `_pell_xy_gp(D)` once and dispatches to `lc_certify_one_mask` (certify mode) or `lc_search_one_mask` (search mode).[file:1]
- Collects all `LCCertificate` objects, counts verdict categories (`excluded_empty`, `excluded_lambda`, `hits_total`, `open_total`), and aggregates distinct `hit_values`.[file:1]

It then writes:

1. **Certificate CSV** `lc_certificates_omega_{omega:02d}.csv` in a per‑ω directory:
   - One row per \((q,\sigma)\) pair.
   - Columns include: `omega, q, mask, sigma_str, Lambda, lambda_val, L, verdict, hits, loop_iters, elapsed_sec, entry_periods, entry_residues`.[file:1]

2. **Summary JSON** `lc_summary_omega_{omega:02d}.json`:
   - Includes program metadata, counts of each verdict type, unique `hit_values`, elapsed time, and a `verdict` summarising the ω‑level state:
     - `COMPLETE_NO_HITS`
     - `COMPLETE_WITH_HITS`
     - `PARTIAL` if any pair remains `OPEN`.[file:1]
   - Includes a SHA‑256 hash of the certificate CSV for tamper detection.[file:1]

### 4.2 Master summary and CLI usage

The `main()` function:

- Parses command‑line arguments (mode, ω‑range, outdir, gp_path, gp_timeout, max_m, max_period_factor, debug, assertions).[file:1]
- Runs `run_omega(...)` for each `omega` in `[start_omega, end_omega]`.[file:1]
- Generates a **master summary** JSON (`lc_master_summary.json`) with:
  - Per‑ω summaries (`total_pairs`, verdict counts, `hit_values`, elapsed time).  
  - A global `any_prime_complete_hit` flag.[file:1]
- Prints a terminal summary with a strong **certificate statement** if no hits are found:
  > All (q,σ) pairs excluded via EXCLUDED_EMPTY or EXCLUDED_LAMBDA.  
  > Lehmer‑Clements certificate: no prime‑complete products m(m+1) of order ω = … exist.[file:1]

Basic usage patterns (as documented in the file header):

- **Certify + search (recommended):**
  ```bash
  python3 LC_Solver.py --mode search --start_omega 9 --end_omega 17 \
      --outdir lc_audit --gp_path /opt/homebrew/bin/gp
  ```
- **Certify only (fast λ/Λ sweep, leaving OPEN pairs unresolved):**
  ```bash
  python3 LC_Solver.py --mode certify --start_omega 9 --end_omega 17 \
      --outdir lc_audit --gp_path /opt/homebrew/bin/gp
  ```
- **High‑ω certificate generation:**
  ```bash
  python3 LC_Solver.py --mode certify --start_omega 18 --end_omega 30 \
      --outdir lc_audit --gp_path /opt/homebrew/bin/gp
  ```[file:1]

---

## 5. Why the results are trustworthy

### 5.1 Mathematical soundness of the filtering logic

Several design choices make the certificates **logically derived** rather than empirically guessed:

1. **Exact CRT treatment of per‑prime conditions.**  
   The combination of `compute_entry_period_and_residues`, `crt_combine`, `crt_system`, and `first_positive_in_class` ensures that:
   - Every per‑prime congruence condition is represented at the residue‑class level.  
   - Inconsistent systems are explicitly detected and marked `EXCLUDED_EMPTY`.  
   - The smallest global Pell index satisfying all congruences is correctly computed as \(\lambda\).[file:1]

2. **Global period and first index.**  
   The algorithm uses the lcm of per‑prime periods (over **all** primes in \(P_\omega\)) to compute \(\Lambda\). The property “if \(\lambda > L\) then no hit up to \(L\)” follows directly from the combinatorial structure of the residue classes and does not depend on numerical accidents.[file:1]

3. **Complete enumeration of \((q,\sigma)\) pairs.**  
   For each \(\omega\), the program iterates over:
   - every nonzero mask \(q\) over \(P_\omega\) (excluding a single trivial `q = 2` case), and  
   - every side assignment \(\sigma\) implemented as a bitmask over the primes.[file:1]  
   This ensures no potential prime‑complete configuration is missed for the chosen \(\omega\)-range.

4. **Exact arithmetic for smoothness and prime‑completeness.**  
   Testing prime‑completeness uses:
   - integer‑exact smoothness checks restricted to \(P_\omega\),  
   - explicit factorization of \(m\) and \(m+1\) over \(P_\omega\), and  
   - a support equality check to enforce that every prime in \(P_\omega\) appears and no extra primes appear.[file:1]  
   No floating‑point or heuristic approximation is used in this core reasoning.

### 5.2 Robustness of Pell computations

The Pell backbone is delegated to PARI/GP, but LC_Solver wraps it in a **defensive protocol**:[file:1]

- `_PELLXY_DEF` defines a pure‑GP implementation of `pellxy_cf` and `pellxy`, including handling of non‑fundamental discriminants and an internal correctness check \(a^2 - D y^2 = 1\).[file:1]
- `_gp_start` launches gp with `-q`, sends the Pell code, and runs a **self‑test** on the discriminant \(D=46\), checking:
  - that the solution satisfies the Pell equation, and  
  - that a bailout call with a low `max_x` returns `[0, 0]` as expected.[file:1]
- `_gp_eval` wraps all gp interaction with:
  - a BEGIN/END marker protocol to delimit outputs,  
  - a per‑call timeout,  
  - automatic process restart if gp dies or misbehaves, and  
  - a small retry budget.[file:1]
- `_pell_xy_gp` parses the final line as a two‑integer vector and raises a structured error if the format is unexpected.[file:1]

In addition, Python’s `sys.set_int_max_str_digits(0)` is used when available to disable defensive digit limits, ensuring very large Pell solutions can be printed and parsed safely.[file:1]

### 5.3 Fixes for subtle correctness issues (v2 notes)

The header explicitly documents two nontrivial fixes that are incorporated into this version:[file:1]

1. **Bug 1 (KeyError in inconsistent CRT cases):**  
   Earlier versions sometimes broke out of the “catch‑up” loop early in inconsistent situations, leaving `entry_periods` only partially populated; subsequent lcm calculations mistakenly expected entries for all primes in the catch‑up set.  
   The current code:
   - always fills `entry_periods` for all primes before computing `Lambda`, and  
   - uses `lcm_list(list(entry_periods.values()))` so only actual entries are included.[file:1]

2. **Bug 2 (OPEN ω=9 at 193280):**  
   Considering only the “new primes” in a catch‑up block produced periods \(T_i\) too small to push \(\lambda\) beyond \(L_\omega\) for many pairs.  
   The corrected algorithm uses **all primes in \(P_\omega\)** for the CRT period:
   \[
   \Lambda = \mathrm{lcm}(T_2,\dots,T_\omega),
   \]
   making \(\Lambda\) large enough that \(\lambda > L_\omega\) for all but a handful of \((q,\sigma)\) pairs, which are then fully handled by the fused search loop.[file:1]

These fixes reduce the risk of spurious `OPEN` classifications and strengthen the certificate’s coverage.

### 5.4 External verifiability

The output is designed for independent checking:

- Every \((q,\sigma)\) has a row in the per‑ω CSV, including the exact `entry_periods` and `entry_residues` for all primes.[file:1]
- The JSON summaries contain enough metadata (program version, Python version, platform, timestamps, SHA‑256 hashes of CSVs) to support reproducibility and audit trails.[file:1]
- A third party can:
  - recompute Pell sequences modulo primes to verify `entry_periods` and `entry_residues`,  
  - recompute CRT solutions to check \(\lambda\) and \(\Lambda\), and  
  - re‑run the Pell iterate loop to confirm that no hits exist below \(L_\omega\) when the program claims `EXCLUDED_LAMBDA` or `EXCLUDED_EMPTY` for all pairs.

In other words, LC_Solver is not just a search engine but a generator of **transparent, machine‑checkable certificates** for the non‑existence (or existence) of prime‑complete consecutive‑integer products for a given ω‑range.

---

## 6. Practical notes for users

- For research use, `--mode search` on a moderate ω‑range (e.g. 9–17) is the recommended default, as it both certifies exclusions and resolves all nontrivial `OPEN` pairs via the fused loop.[file:1]
- For very large ω, `--mode certify` gives a fast λ/Λ sweep that already excludes the vast majority of pairs; one can then selectively revisit any remaining `OPEN` configurations if necessary.[file:1]
- The output directory (`--outdir`) is structured by ω (`omega_XX` subdirectories) and contains everything needed for independent verification or further analysis.[file:1]

## End of Document
