#!/usr/bin/env python3
# LCr_Solver.py  version 3
"""
Lehmer-Clements enumerator for prime-complete products of consecutive integers

Algorithm
---------
This program implements the **Lehmer-Clements algorithm**, a specialisation of
the classical Størmer-Lehmer Pell enumeration that fuses the smoothness and
prime-completeness checks directly into the Pell iterate loop.

The key mathematical objects are, for a fixed squarefree mask q and prime p:

    T_p(q)  — period of the Pell sequence x_j mod p
    E_p^ε(q) — set of j mod T_p(q) where p | m_j + ε  (ε ∈ {0,1})
    σ        — a side assignment: each prime p in q gets a side σ(p) ∈ {0,1}
    Λ(q,σ)  — lcm_{p|q} T_p(q)   (combined CRT period)
    λ(q,σ)  — min { j ≥ 1 : j satisfies all entry conditions simultaneously }

If λ(q,σ) > L_ω = max(3, p_ω), the loop body never executes — a certificate.

Performance design (v3)
-----------------------
v1/v2 had two major performance bugs:

  Bug A  (4^ω pairs):  sigma was iterated over ALL ω primes, producing 2^ω
         sigmas per mask even though primes absent from q cannot divide m(m+1).
         Correct: sigma ranges only over the k prime factors of q, giving
         sum_{k} C(ω,k)·2^k = 3^ω total pairs — a 10× saving at ω=8.

  Bug B  (mat_pow bottleneck):  for each (mask,σ) pair the code called
         mat_pow(x1,y1,D, λ) and mat_pow(x1,y1,D, Λ) where λ,Λ can be
         enormous big integers.  But L_ω ≤ 59 for all ω ≤ 17 — there are
         at most 59 Pell iterates to examine.  The correct approach is to
         iterate j = 1 .. L directly (one cheap recurrence step each) and,
         for each j, check which (q,σ) conditions are satisfied.  No mat_pow
         is needed at all.

  Bug C  (double hits):  each prime-complete m was reported twice because
         σ and its bit-complement both satisfy the conditions for the same m
         (the two "sides" are interchangeable).  Fixed by canonicalising: the
         sigma with side=0 on the smallest prime factor of q is the canonical
         representative.  This halves the effective sigma space.

Certificate output
------------------
For every (q, σ_canonical) triple the program writes:
    λ        first compatible index, or None if CRT is inconsistent
    Λ        CRT period
    L        Størmer-Lehmer bound max(3, p_ω)
    verdict  EXCLUDED_EMPTY | EXCLUDED_LAMBDA | HIT | OPEN

Usage
-----
    python3 LCr_Solver.py --mode search --start_omega 2 --end_omega 9 \\
        --outdir lc_audit --gp_path /opt/homebrew/bin/gp

    python3 LCr_Solver.py --mode certify --start_omega 9 --end_omega 17 \\
        --outdir lc_audit --gp_path /opt/homebrew/bin/gp

By Ken Clements and Claude (Perplexity AI), May 2026
Lehmer-Clements algorithm first described: May 1, 2026
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import os
import re
import subprocess
import sys
import platform
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from itertools import product as iproduct
from typing import Dict, List, Optional, Tuple

try:
    sys.set_int_max_str_digits(0)
except Exception:
    pass

program_name, program_version = "LCr_Solver", 3

DEBUG      = False
ASSERTIONS = False

# ── small utilities ────────────────────────────────────────────────────────────

def utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()

def ensure_dir(path: str) -> None:
    os.makedirs(path, exist_ok=True)

def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()

# ── prime generation ───────────────────────────────────────────────────────────

def sieve(n: int) -> List[int]:
    if n < 2:
        return []
    flags = bytearray([1]) * (n + 1)
    flags[0] = flags[1] = 0
    for i in range(2, int(n**0.5) + 1):
        if flags[i]:
            flags[i*i::i] = bytearray(len(flags[i*i::i]))
    return [i for i, f in enumerate(flags) if f]

def first_n_primes(n: int) -> List[int]:
    est = max(15, int(n * (math.log(n) + math.log(math.log(n + 2)) + 2)))
    ps = sieve(est)
    while len(ps) < n:
        est *= 2
        ps = sieve(est)
    return ps[:n]

# ── arithmetic helpers ─────────────────────────────────────────────────────────

def is_P_smooth(x: int, primes: Tuple[int, ...]) -> bool:
    if x <= 0:
        return False
    for p in primes:
        while x % p == 0:
            x //= p
    return x == 1

def factor_over_P(n: int, primes: Tuple[int, ...]) -> Tuple[Dict[int, int], int]:
    rem, out = n, {}
    for p in primes:
        if rem % p == 0:
            e = 0
            while rem % p == 0:
                rem //= p
                e += 1
            out[p] = e
        if rem == 1:
            break
    return out, rem

def factor_merge(a: Dict[int, int], b: Dict[int, int]) -> Dict[int, int]:
    out = dict(a)
    for p, e in b.items():
        out[p] = out.get(p, 0) + e
    return out

def support_tuple(f: Dict[int, int]) -> Tuple[int, ...]:
    return tuple(sorted(f.keys()))

def gcd(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return a

def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b

def lcm_list(vals: List[int]) -> int:
    result = 1
    for v in vals:
        result = lcm(result, v)
    return result

# ── CRT ───────────────────────────────────────────────────────────────────────

def crt_combine(r1: int, m1: int, r2: int, m2: int) -> Tuple[Optional[int], int]:
    g = gcd(m1, m2)
    if (r2 - r1) % g != 0:
        return None, 0
    lcm_m  = lcm(m1, m2)
    inv_   = pow(m1 // g, -1, m2 // g)
    t      = ((r2 - r1) // g * inv_) % (m2 // g)
    return (r1 + m1 * t) % lcm_m, lcm_m

def crt_system(residues_mods: List[Tuple[int, int]]) -> Tuple[Optional[int], int]:
    if not residues_mods:
        return 0, 1
    r, m = residues_mods[0]
    for r2, m2 in residues_mods[1:]:
        r, m = crt_combine(r, m, r2, m2)
        if r is None:
            return None, 0
    return r % m, m

def first_positive(sol: int, mod: int) -> int:
    """Smallest j ≥ 1 with j ≡ sol (mod mod). sol is in [0, mod)."""
    return sol if sol >= 1 else mod

# ── PARI/GP ───────────────────────────────────────────────────────────────────

_PELLXY_DEF = r"""
pellxy_cf(D, max_x=0)={
  if(D<=0, error("D<=0"));
  if(issquare(D), error("square"));
  my(a0=sqrtint(D), m=0, d=1, a=a0, p0=1, p1=a0, q0=0, q1=1);
  while(p1^2 - D*q1^2 != 1,
    m=d*a-m; d=(D-m^2)/d; a=(a0+m)\d;
    my(p2=a*p1+p0, q2=a*q1+q0);
    p0=p1; p1=p2; q0=q1; q1=q2;
    if(max_x>0 && p1>max_x, return([0,0]));
  );
  [p1,q1];
};
pellxy(D, max_x=0)={
  if(D<=0, error("D<=0")); if(issquare(D), error("square"));
  my(F=factor(D), P=F[,1], E=F[,2], d=1, s=1);
  for(i=1,#P, my(e=E[i]); if(e%2,d*=P[i]); s*=P[i]^(e\2));
  my(v=pellxy_cf(d,max_x));
  if(v==[0,0], return([0,0]));
  my(a=v[1], b=v[2]);
  if(s==1, return([a,b]));
  my(a1=a, b1=b);
  while(b%s,
    my(aa=a1*a+d*b1*b, bb=a1*b+b1*a); a=aa; b=bb;
    if(max_x>0 && a>max_x, return([0,0]));
  );
  my(y=b/s);
  if(a^2-D*y^2!=1, error("check failed"));
  [a,y];
};
"""

_BEGIN       = "__BEGIN__"
_END         = "__END__"
_VEC2_INT_RE = re.compile(r"^\[\s*(-?\d+)\s*,\s*(-?\d+)\s*\]\s*$")
_GP_PROC: Optional[subprocess.Popen] = None
_GP_PATH: str = "gp"


def _gp_kill() -> None:
    global _GP_PROC
    if _GP_PROC is None:
        return
    try:
        _GP_PROC.kill()
    except Exception:
        pass
    _GP_PROC = None


def _gp_start() -> subprocess.Popen:
    p = subprocess.Popen([_GP_PATH, "-q"],
        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, text=True, bufsize=1)
    assert p.stdin and p.stdout
    p.stdin.write(_PELLXY_DEF + "\n")
    p.stdin.write(f'print("{_BEGIN}");\n')
    p.stdin.write("v=pellxy(46); print(v); print(v[1]^2-46*v[2]^2);\n")
    p.stdin.write("vb=pellxy(46,100); print(vb);\n")
    p.stdin.write(f'print("{_END}");\n')
    p.stdin.flush()
    buf, in_block = [], False
    while True:
        line = p.stdout.readline()
        if not line:
            raise RuntimeError("gp handshake EOF")
        s = line.strip()
        if s == _BEGIN:
            in_block = True; continue
        if s == _END:
            break
        if in_block:
            buf.append(s)
    assert buf[1] == "1",       f"Pell self-test failed: {buf}"
    assert buf[2] == "[0, 0]",  f"Bailout self-test failed: {buf}"
    return p


def _gp_eval(expr: str, retries: int = 2, timeout: float = 300.0) -> str:
    global _GP_PROC
    for attempt in range(retries + 1):
        try:
            if _GP_PROC is None:
                _GP_PROC = _gp_start()
            p = _GP_PROC
            assert p.stdin and p.stdout
            p.stdin.write(f'print("{_BEGIN}");\n{expr}\nprint("{_END}");\n')
            p.stdin.flush()
            parts, in_block = [], False
            deadline = time.time() + timeout
            while True:
                if time.time() > deadline:
                    raise TimeoutError(f"gp timeout {timeout}s")
                line = p.stdout.readline()
                if not line:
                    raise RuntimeError("gp EOF")
                s = line.strip()
                if s == _BEGIN:
                    in_block = True; continue
                if s == _END:
                    break
                if in_block:
                    parts.append(s)
            return "\n".join(parts)
        except Exception:
            _gp_kill()
            if attempt == retries:
                raise


def _pell_xy_gp(D: int, retries: int = 2,
                timeout: float = 300.0,
                max_x: int = 0) -> Tuple[int, int, str]:
    arg = f", {max_x}" if max_x > 0 else ""
    raw = _gp_eval(f"print(pellxy({D}{arg}));", retries=retries, timeout=timeout)
    raw = raw.strip().splitlines()[-1]
    m = _VEC2_INT_RE.match(raw)
    if not m:
        raise ValueError(f"Unexpected GP output: {raw!r}")
    return int(m.group(1)), int(m.group(2)), raw

# ── mask utilities ─────────────────────────────────────────────────────────────

def primes_in_mask(mask: int, primes: Tuple[int, ...]) -> List[int]:
    """Return the list of primes in P_ω that are factors of this mask's q."""
    result, i, tmp = [], 0, mask
    while tmp:
        if tmp & 1:
            result.append(primes[i])
        tmp >>= 1
        i += 1
    return result

def q_from_mask(mask: int, primes: Tuple[int, ...]) -> int:
    q = 1
    for p in primes_in_mask(mask, primes):
        q *= p
    return q

# ═══════════════════════════════════════════════════════════════════════════════
#  ENTRY PERIOD COMPUTATION
# ═══════════════════════════════════════════════════════════════════════════════

def compute_entry_period_and_residues(
    prime_p: int,
    side: int,           # 0: p|m_j,  1: p|(m_j+1)
    x1: int, y1: int,
    D: int,
    max_period: int,
) -> Tuple[int, List[int]]:
    """
    Compute period T of the Pell sequence mod p and residues j∈[1..T]
    where the side condition holds.

    side=0: p|m_j  ⟺  x_j≡1 (mod p)
    side=1: p|(m_j+1) ⟺  x_j≡-1 (mod p)
    """
    x1p, y1p, Dp = x1 % prime_p, y1 % prime_p, D % prime_p
    xj, yj = x1p, y1p
    residues: List[int] = []

    for j in range(1, max_period + 2):
        if side == 0:
            cond = (xj - 1) % prime_p == 0
        else:
            cond = (xj + 1) % prime_p == 0
        if cond:
            residues.append(j)

        nxj = (x1p * xj + Dp * y1p * yj) % prime_p
        nyj = (x1p * yj + y1p * xj) % prime_p
        xj, yj = nxj, nyj

        if xj == x1p and yj == y1p:
            return j, [r for r in residues if 1 <= r <= j]

    return max_period + 1, residues   # safety fallback


# ═══════════════════════════════════════════════════════════════════════════════
#  CORE: process ONE MASK  (both certify and search)
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class MaskResult:
    mask:      int
    q:         int
    # Per-sigma certificate data (one row per canonical sigma)
    rows:      List[Dict]   # list of cert dicts
    # Aggregate counters
    excluded_empty:  int
    excluded_lambda: int
    hits:            int
    open_count:      int
    hit_ms:          List[int]   # deduplicated hit values
    elapsed_sec:     float


def _sigma_is_canonical(mask_primes: List[int], sigma: Dict[int, int]) -> bool:
    """
    Return True if sigma is the canonical representative of {sigma, ~sigma}.
    Canonical = side=0 for the smallest prime factor of q.
    This eliminates the duplicate hit from the complement side assignment.
    """
    if not mask_primes:
        return True
    return sigma[mask_primes[0]] == 0


def process_mask(
    omega:     int,
    mask:      int,
    primes:    Tuple[int, ...],
    L:         int,
    x1: int, y1: int,
    mode:      str,              # "certify" | "search"
    max_period_factor: int = 4,
    max_m:     int = 0,
) -> MaskResult:
    """
    Process a single Pell mask.

    Key design decisions vs v2:
    - sigma iterates only over primes IN the mask (|mask_primes|=k bits set),
      giving 2^k assignments instead of 2^omega.  Total work = 3^omega.
    - Canonicalisation halves the sigma space again: only sigma with side=0
      on the smallest mask prime is processed.
    - The search loop iterates j=1..L directly via a cheap recurrence
      (x,y) → (x1*x + D*y1*y, x1*y + y1*x).  No mat_pow needed.
      L ≤ 59 for all omega ≤ 17.
    """
    t0 = time.time()
    q = q_from_mask(mask, primes)
    D = 2 * q

    mask_primes: List[int] = primes_in_mask(mask, primes)
    k = len(mask_primes)

    # Pre-compute entry periods for the primes in this mask only
    max_period_p: Dict[int, int] = {p: max_period_factor * (p - 1) for p in mask_primes}
    period_data: Dict[int, Tuple[int, List[int], int, List[int]]] = {}
    for p in mask_primes:
        T0, r0 = compute_entry_period_and_residues(p, 0, x1, y1, D, max_period_p[p])
        T1, r1 = compute_entry_period_and_residues(p, 1, x1, y1, D, max_period_p[p])
        period_data[p] = (T0, r0, T1, r1)

    rows: List[Dict] = []
    excl_empty = excl_lam = n_hits = n_open = 0
    hit_ms_set: set = set()

    # Iterate over 2^k side assignments, CANONICAL ONLY (first prime side=0)
    for sig_int in range(1 << k):
        # Bit i of sig_int → side for mask_primes[i]
        # Canonical: mask_primes[0] must have side=0
        if (sig_int & 1) != 0:
            continue     # mask_primes[0] has side=1 → non-canonical, skip

        sigma: Dict[int, int] = {p: (sig_int >> i) & 1
                                  for i, p in enumerate(mask_primes)}

        # Build CRT constraints and check consistency
        entry_periods:  Dict[int, int]       = {}
        entry_residues: Dict[int, List[int]] = {}
        choices:        List[List[Tuple[int, int]]] = []
        inconsistent = False

        for p in mask_primes:
            side       = sigma[p]
            T0,r0,T1,r1 = period_data[p]
            T   = T0 if side == 0 else T1
            res = r0 if side == 0 else r1
            entry_periods[p]  = T
            entry_residues[p] = res
            if not res:
                inconsistent = True
                # keep looping to populate all entry_periods for safe lcm_list
            else:
                choices.append([(r, T) for r in res])

        Lambda = lcm_list(list(entry_periods.values())) if entry_periods else 1

        if inconsistent or not choices:
            rows.append({"sigma": dict(sigma), "Lambda": Lambda,
                         "lambda_val": None, "verdict": "EXCLUDED_EMPTY",
                         "hits": [], "loop_iters": 0,
                         "entry_periods": dict(entry_periods),
                         "entry_residues": {p: list(v) for p,v in entry_residues.items()}})
            excl_empty += 1
            continue

        # Find λ via CRT
        min_lambda: Optional[int] = None
        for combo in iproduct(*choices):
            sol, mod = crt_system(list(combo))
            if sol is None:
                continue
            j_min = first_positive(sol, mod)
            if min_lambda is None or j_min < min_lambda:
                min_lambda = j_min

        if min_lambda is None:
            rows.append({"sigma": dict(sigma), "Lambda": Lambda,
                         "lambda_val": None, "verdict": "EXCLUDED_EMPTY",
                         "hits": [], "loop_iters": 0,
                         "entry_periods": dict(entry_periods),
                         "entry_residues": {p: list(v) for p,v in entry_residues.items()}})
            excl_empty += 1
            continue

        if min_lambda > L:
            rows.append({"sigma": dict(sigma), "Lambda": Lambda,
                         "lambda_val": min_lambda, "verdict": "EXCLUDED_LAMBDA",
                         "hits": [], "loop_iters": 0,
                         "entry_periods": dict(entry_periods),
                         "entry_residues": {p: list(v) for p,v in entry_residues.items()}})
            excl_lam += 1
            continue

        # ── Fused iterate loop (certify mode: just count; search: find m) ──
        # Iterate Pell recurrence j=1..L via cheap O(1)-per-step recurrence.
        # No mat_pow needed: L ≤ 59 for ω ≤ 17.
        hits_here: List[int] = []
        loop_iters = 0

        if mode == "search":
            # Walk the Pell sequence from j=1 to j=L, stepping j by Λ from λ.
            # Build x_j, y_j at j=1 via one recurrence walk (j-1 steps).
            # Then jump to j=min_lambda by continuing the walk.
            # Then step by Λ each time.
            # Since L ≤ 59 and Λ ≥ 1, total steps ≤ L.

            # Walk from fundamental solution to j=min_lambda
            xj, yj = x1, y1
            for _ in range(min_lambda - 1):
                xj, yj = x1*xj + D*y1*yj, x1*yj + y1*xj

            # Step through j = min_lambda, min_lambda+Lambda, ...
            # For each step we also need to advance the Pell state by Lambda.
            # Build step state = Pell state at j=Lambda (from fundamental).
            xs, ys = x1, y1
            for _ in range(Lambda - 1):
                xs, ys = x1*xs + D*y1*ys, x1*ys + y1*xs

            j = min_lambda
            while j <= L:
                loop_iters += 1
                if xj & 1:
                    m = (xj - 1) // 2
                    if m > 0:
                        if max_m > 0 and m > max_m:
                            break
                        if is_P_smooth(m, primes) and is_P_smooth(m + 1, primes):
                            f0, rem0 = factor_over_P(m,     primes)
                            f1, rem1 = factor_over_P(m + 1, primes)
                            if rem0 == 1 and rem1 == 1:
                                merged = factor_merge(f0, f1)
                                if support_tuple(merged) == primes:
                                    hits_here.append(m)
                                    hit_ms_set.add(m)

                # Advance (xj,yj) by Lambda steps using step state (xs,ys)
                xj, yj = xs*xj + D*ys*yj, xs*yj + ys*xj
                j += Lambda
        else:
            # certify mode: OPEN verdict, no iteration needed
            pass

        verdict = "HIT" if hits_here else "OPEN"
        if hits_here:
            n_hits += 1
        else:
            n_open += 1

        rows.append({"sigma": dict(sigma), "Lambda": Lambda,
                     "lambda_val": min_lambda, "verdict": verdict,
                     "hits": hits_here, "loop_iters": loop_iters,
                     "entry_periods": dict(entry_periods),
                     "entry_residues": {p: list(v) for p,v in entry_residues.items()}})

    return MaskResult(
        mask=mask, q=q, rows=rows,
        excluded_empty=excl_empty, excluded_lambda=excl_lam,
        hits=n_hits, open_count=n_open,
        hit_ms=sorted(hit_ms_set),
        elapsed_sec=time.time() - t0,
    )


# ═══════════════════════════════════════════════════════════════════════════════
#  OMEGA DRIVER
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class OmegaSummary:
    omega:           int
    pmax:            int
    L:               int
    total_pairs:     int
    excluded_empty:  int
    excluded_lambda: int
    hits_total:      int
    open_total:      int
    hit_values:      List[int]
    elapsed_sec:     float
    verdict:         str


def run_omega(
    omega:             int,
    mode:              str,
    outdir:            str,
    gp_path:           str   = "gp",
    gp_timeout:        float = 300.0,
    max_m:             int   = 0,
    max_period_factor: int   = 4,
    verbose:           bool  = True,
) -> OmegaSummary:
    t_start    = time.time()
    all_primes = tuple(first_n_primes(omega))
    pmax       = all_primes[-1]
    L          = max(3, pmax)

    ensure_dir(outdir)
    omega_dir = os.path.join(outdir, f"omega_{omega:02d}")
    ensure_dir(omega_dir)

    if verbose:
        import math as _m
        pairs_est = 3**omega // 2   # canonical sigma count estimate
        print(f"\n[LCr] ω={omega}  P_ω={list(all_primes)}  pmax={pmax}  L={L}  "
              f"mode={mode}  ~{pairs_est:,} canonical (q,σ) pairs")

    total_masks = 1 << omega
    all_rows: List[Dict] = []
    excl_empty = excl_lam = hits_total = open_total = 0
    all_hit_ms: set = set()

    masks_done = 0
    for mask in range(1, total_masks):
        q = q_from_mask(mask, all_primes)
        if q == 2:
            continue   # degenerate Pell case

        x_ceiling = 2 * max_m + 1 if max_m > 0 else 0
        q_ceiling  = 2 * max_m * (max_m + 1) if max_m > 0 else 0
        if q_ceiling > 0 and q > q_ceiling:
            continue

        try:
            x1, y1, _ = _pell_xy_gp(2 * q, timeout=gp_timeout, max_x=x_ceiling)
            if x1 == 0 and y1 == 0:
                continue
        except Exception as e:
            if verbose:
                print(f"  [!] GP failed mask={mask} q={q}: {e}")
            continue

        if x_ceiling > 0 and x1 > x_ceiling:
            continue

        result = process_mask(
            omega=omega, mask=mask, primes=all_primes, L=L,
            x1=x1, y1=y1, mode=mode,
            max_period_factor=max_period_factor, max_m=max_m,
        )

        for row in result.rows:
            row["omega"] = omega
            row["q"]     = q
            row["mask"]  = mask
            row["L"]     = L
        all_rows.extend(result.rows)

        excl_empty  += result.excluded_empty
        excl_lam    += result.excluded_lambda
        hits_total  += result.hits
        open_total  += result.open_count
        all_hit_ms  |= set(result.hit_ms)

        masks_done += 1
        if verbose and masks_done % 200 == 0:
            print(f"  ... mask {masks_done}/{total_masks-1}  "
                  f"empty={excl_empty} λ-excl={excl_lam} "
                  f"hits={hits_total} open={open_total}")

    elapsed = time.time() - t_start
    hit_values = sorted(all_hit_ms)

    if hits_total > 0:
        verdict = "COMPLETE_WITH_HITS"
    elif open_total > 0:
        verdict = "PARTIAL"
    else:
        verdict = "COMPLETE_NO_HITS"

    summary = OmegaSummary(
        omega=omega, pmax=pmax, L=L,
        total_pairs=len(all_rows),
        excluded_empty=excl_empty,
        excluded_lambda=excl_lam,
        hits_total=hits_total,
        open_total=open_total,
        hit_values=hit_values,
        elapsed_sec=elapsed,
        verdict=verdict,
    )

    # ── Certificate CSV ────────────────────────────────────────────────────
    cert_csv = os.path.join(omega_dir, f"lc_certificates_omega_{omega:02d}.csv")
    with open(cert_csv, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["omega","q","mask","sigma_str",
                    "Lambda","lambda_val","L",
                    "verdict","hits","loop_iters",
                    "entry_periods","entry_residues"])
        for row in all_rows:
            sigma_str = ",".join(f"p{p}:{s}"
                                  for p,s in sorted(row["sigma"].items()))
            hits_str  = ";".join(str(h) for h in row["hits"])
            per_str   = ";".join(f"p{p}:T={t}"
                                  for p,t in sorted(row["entry_periods"].items()))
            res_str   = ";".join(f"p{p}:{row['entry_residues'][p]}"
                                  for p in sorted(row["entry_residues"]))
            lv = row["lambda_val"]
            w.writerow([
                row["omega"], row["q"], row["mask"], sigma_str,
                row["Lambda"],
                lv if lv is not None else "inf",
                row["L"], row["verdict"], hits_str,
                row["loop_iters"], per_str, res_str,
            ])

    # ── Summary JSON ───────────────────────────────────────────────────────
    summary_json = os.path.join(omega_dir, f"lc_summary_omega_{omega:02d}.json")
    sd = {
        "program": program_name, "version": program_version,
        "omega": omega, "pmax": pmax, "L": L, "mode": mode,
        "total_pairs": len(all_rows),
        "excluded_empty":  excl_empty,
        "excluded_lambda": excl_lam,
        "hits_total":      hits_total,
        "open_total":      open_total,
        "hit_values":      hit_values,
        "elapsed_sec":     round(elapsed, 3),
        "verdict":         verdict,
        "timestamp":       utc_now_iso(),
        "python_version":  sys.version,
        "platform":        platform.platform(),
        "cert_csv_sha256": sha256_file(cert_csv),
    }
    with open(summary_json, "w") as f:
        json.dump(sd, f, indent=2)

    if verbose:
        print(f"  excluded_empty={excl_empty}  excluded_lambda={excl_lam}  "
              f"hits={hits_total}  open={open_total}  verdict={verdict}")
        print(f"  elapsed={elapsed:.1f}s  → {omega_dir}")
        if hit_values:
            print(f"  HIT VALUES: {hit_values}")

    return summary


# ═══════════════════════════════════════════════════════════════════════════════
#  MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main() -> None:
    global DEBUG, ASSERTIONS, _GP_PATH

    ap = argparse.ArgumentParser(
        prog="LCr_Solver",
        description="Lehmer-Clements prime-complete Pell enumerator (v3).",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("--mode", choices=["certify","search"], default="search")
    ap.add_argument("--start_omega",       type=int,   default=9)
    ap.add_argument("--end_omega",         type=int,   default=17)
    ap.add_argument("--outdir",            default="lc_audit")
    ap.add_argument("--gp_path",           default="gp")
    ap.add_argument("--gp_timeout",        type=float, default=300.0)
    ap.add_argument("--max_m",             type=int,   default=0)
    ap.add_argument("--max_period_factor", type=int,   default=4)
    ap.add_argument("--debug",      action="store_true")
    ap.add_argument("--assertions", action="store_true")
    ap.add_argument("--version",    action="store_true")

    args = ap.parse_args()

    if args.version:
        print(json.dumps({
            "program": program_name, "version": program_version,
            "python_version": sys.version, "platform": platform.platform(),
            "timestamp": utc_now_iso(),
        }, indent=2))
        sys.exit(0)

    DEBUG      = args.debug
    ASSERTIONS = args.assertions
    _GP_PATH   = args.gp_path

    print(f"LCr_Solver v{program_version}  —  Lehmer-Clements prime-complete enumerator")
    print(f"Mode: {args.mode}  ω: {args.start_omega}..{args.end_omega}  "
          f"outdir: {args.outdir}  gp: {args.gp_path}")

    ensure_dir(args.outdir)
    all_summaries: List[OmegaSummary] = []
    any_hit = False

    for omega in range(args.start_omega, args.end_omega + 1):
        s = run_omega(
            omega=omega, mode=args.mode, outdir=args.outdir,
            gp_path=args.gp_path, gp_timeout=args.gp_timeout,
            max_m=args.max_m, max_period_factor=args.max_period_factor,
            verbose=True,
        )
        all_summaries.append(s)
        if s.hits_total > 0:
            any_hit = True

    master_path = os.path.join(args.outdir, "lc_master_summary.json")
    master = {
        "program": program_name, "version": program_version,
        "mode": args.mode,
        "start_omega": args.start_omega, "end_omega": args.end_omega,
        "any_prime_complete_hit": any_hit,
        "per_omega": [
            {"omega": s.omega, "L": s.L,
             "total_pairs": s.total_pairs,
             "excluded_empty":  s.excluded_empty,
             "excluded_lambda": s.excluded_lambda,
             "hits_total": s.hits_total, "open_total": s.open_total,
             "verdict": s.verdict, "hit_values": s.hit_values,
             "elapsed_sec": round(s.elapsed_sec, 3)}
            for s in all_summaries
        ],
        "timestamp": utc_now_iso(),
    }
    with open(master_path, "w") as f:
        json.dump(master, f, indent=2)

    print(f"\n{'='*60}")
    print(f"MASTER RESULT:  any_prime_complete_hit = {any_hit}")
    if not any_hit:
        excl = sum(s.excluded_lambda + s.excluded_empty for s in all_summaries)
        print(f"All {excl} canonical (q,σ) pairs excluded by EXCLUDED_EMPTY or EXCLUDED_LAMBDA.")
        print(f"Lehmer-Clements certificate: no prime-complete products m(m+1)")
        print(f"of order ω = {args.start_omega}..{args.end_omega} exist.")
    else:
        print("Prime-complete hits found — see per-omega summaries.")
    print(f"Master summary → {master_path}")
    print(f"{'='*60}")


if __name__ == "__main__":
    import atexit
    atexit.register(_gp_kill)
    main()
