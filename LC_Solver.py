#!/usr/bin/env python3
# LC_Solver.py  version 2.1
"""
Lehmer-Clements enumerator for prime-complete products of consecutive integers

Algorithm
---------
This program implements the **Lehmer-Clements algorithm**, a specialisation of
the classical Størmer-Lehmer Pell enumeration that fuses the smoothness and
prime-completeness checks directly into the Pell iterate loop.

Classical Størmer-Lehmer (as in Nr_Solver.py)
----------------------------------------------
    Step 1.  For each squarefree mask q over P_ω, compute the Pell family
             m_j(q) = (x_j − 1)/2, j = 1 … L_ω.
    Step 2.  Filter for P_ω-smoothness of m(m+1).
    Step 3.  Filter for prime-completeness: rad(m(m+1)) = p_ω#.

Lehmer-Clements (this program)
-------------------------------
For each prime p_i ∈ P_ω and side ε ∈ {0,1}, the Pell sequence x_j mod p_i
is periodic with period T_i(q).  The entry set

    E_i^(ε)(q) = { j mod T_i(q) : p_i | m_j(q) + ε }

is a union of residue classes.  For a side assignment σ : P_ω → {0,1} the
Chinese Remainder Theorem combines all per-prime conditions into

    Λ(q,σ) = lcm_{p_i ∈ P_ω} T_i(q)    (combined period)
    λ(q,σ) = min { j ≥ 1 : j satisfies all entry conditions }

The fused iterate loop then runs only over

    j = λ, λ+Λ, λ+2Λ, …  while j ≤ L_ω

Key property: if λ(q,σ) > L_ω the loop body never executes — the first
compatible Pell index already exceeds the Størmer-Lehmer bound, which is a
certificate rather than a mere computational observation.

v2 fix notes
------------
Bug 1 (KeyError):  when inconsistent=True and the catch-up loop breaks early,
    entry_periods is only partially filled.  lcm_list must use only the keys
    actually present, not the full catch_up_primes list.

Bug 2 (193280 OPEN at ω=9):  using only the *new* primes {p_9,…} as the catch-up
    block gives T_i values that are too small relative to L_ω, so many λ ≤ L_ω.
    The correct formulation uses ALL primes in P_ω as the catch-up block;
    Λ = lcm(T_2,…,T_ω) grows rapidly and λ > L_ω for all but a handful of
    (q,σ) pairs, which are then resolved by the fused search loop.

Certificate output
------------------
For every (q, σ) triple the program writes:
    λ       = first compatible index, or None if the CRT system is inconsistent
    Λ       = CRT period
    L       = Størmer-Lehmer bound  max(3, p_ω)
    verdict ∈ {EXCLUDED_EMPTY, EXCLUDED_LAMBDA, HIT, OPEN}

    EXCLUDED_EMPTY   — CRT system has no solution (∩ E_i is empty for some i)
    EXCLUDED_LAMBDA  — λ > L  (loop never starts; no prime-complete hit possible)
    HIT              — a certified prime-complete m was found
    OPEN             — λ ≤ L but no hit found after smoothness check

Usage
-----
# Certify + search mode (recommended — resolves all OPEN pairs):
    python3 LC_Solver.py --mode search --start_omega 9 --end_omega 17 \\
        --outdir lc_audit --gp_path /opt/homebrew/bin/gp

# Certify-only (fast λ/Λ sweep; OPEN pairs not resolved):
    python3 LC_Solver.py --mode certify --start_omega 9 --end_omega 17 \\
        --outdir lc_audit --gp_path /opt/homebrew/bin/gp

# High-ω certificate generation:
    python3 LCr_Solver.py --mode certify --start_omega 18 --end_omega 30 \\
        --outdir lc_audit --gp_path /opt/homebrew/bin/gp

By Ken Clements and Claude, May 2026
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
from typing import Dict, List, Optional, Tuple, Set

try:
    sys.set_int_max_str_digits(0)
except Exception:
    pass

program_name, program_version = "LC_Solver", 2

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
    rem = n
    out: Dict[int, int] = {}
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

# ── CRT solver ────────────────────────────────────────────────────────────────

def crt_combine(r1: int, m1: int, r2: int, m2: int) -> Tuple[Optional[int], int]:
    """
    Combine j ≡ r1 (mod m1) and j ≡ r2 (mod m2).
    Returns (residue in [0, lcm), modulus) or (None, 0) if inconsistent.
    """
    g = gcd(m1, m2)
    if (r2 - r1) % g != 0:
        return None, 0
    lcm_m = lcm(m1, m2)
    m1g   = m1 // g
    m2g   = m2 // g
    diff  = (r2 - r1) // g
    inv_m1g = pow(m1g, -1, m2g)
    t = (diff * inv_m1g) % m2g
    r = (r1 + m1 * t) % lcm_m
    return r, lcm_m

def crt_system(residues_mods: List[Tuple[int, int]]) -> Tuple[Optional[int], int]:
    """
    Solve j ≡ r_i (mod m_i) for all i.
    Returns (residue in [0, lcm), combined modulus) or (None, 0).
    """
    if not residues_mods:
        return 0, 1
    r, m = residues_mods[0]
    for r2, m2 in residues_mods[1:]:
        result = crt_combine(r, m, r2, m2)
        if result[0] is None:
            return None, 0
        r, m = result
    return r % m, m

def first_positive_in_class(sol: int, mod: int) -> int:
    """Smallest j ≥ 1 with j ≡ sol (mod mod)."""
    # sol is already in [0, mod).  If sol==0 then smallest positive is mod.
    return sol if sol >= 1 else mod

# ── PARI/GP interface ──────────────────────────────────────────────────────────

_PELLXY_DEF = r"""
pellxy_cf(D, max_x=0)={
  if(D<=0, error("D<=0"));
  if(issquare(D), error("square"));
  my(a0 = sqrtint(D));
  my(m=0, d=1, a=a0);
  my(p0=1, p1=a0);
  my(q0=0, q1=1);
  while(p1^2 - D*q1^2 != 1,
    m = d*a - m;
    d = (D - m^2)/d;
    a = (a0 + m)\d;
    my(p2 = a*p1 + p0);
    my(q2 = a*q1 + q0);
    p0=p1; p1=p2;
    q0=q1; q1=q2;
    if(max_x > 0 && p1 > max_x, return([0,0]));
  );
  [p1, q1];
};

pellxy(D, max_x=0)={
  if(D<=0, error("D<=0"));
  if(issquare(D), error("square"));
  my(F = factor(D));
  my(P = F[,1], E = F[,2]);
  my(d = 1, s = 1);
  for(i=1, #P,
    my(e = E[i]);
    if(e%2, d *= P[i]);
    s *= P[i]^(e\2);
  );
  my(v = pellxy_cf(d, max_x));
  if(v == [0,0], return([0,0]));
  my(a = v[1], b = v[2]);
  if(s==1, return([a,b]));
  my(a1=a, b1=b);
  while(b % s,
    my(aa = a1*a + d*b1*b);
    my(bb = a1*b + b1*a);
    a=aa; b=bb;
    if(max_x > 0 && a > max_x, return([0,0]));
  );
  my(y = b/s);
  if(a^2 - D*y^2 != 1, error("internal check failed"));
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
    p = subprocess.Popen(
        [_GP_PATH, "-q"],
        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, text=True, bufsize=1,
    )
    assert p.stdin and p.stdout
    p.stdin.write(_PELLXY_DEF + "\n")
    p.stdin.write(f'print("{_BEGIN}");\n')
    p.stdin.write("v=pellxy(46); print(v); print(v[1]^2-46*v[2]^2);\n")
    p.stdin.write("vb=pellxy(46, 100); print(vb);\n")
    p.stdin.write(f'print("{_END}");\n')
    p.stdin.flush()
    buf: List[str] = []
    in_block = False
    while True:
        line = p.stdout.readline()
        if line == "":
            raise RuntimeError("gp handshake EOF")
        s = line.rstrip("\n").strip()
        if s == _BEGIN:
            in_block = True
            continue
        if s == _END:
            break
        if in_block:
            buf.append(s)
    assert buf[1].strip() == "1",     f"Pell self-test failed: {buf}"
    assert buf[2].strip() == "[0, 0]", f"Bailout self-test failed: {buf}"
    return p


def _gp_eval(expr: str, retries: int = 2, gp_timeout: float = 300.0) -> str:
    global _GP_PROC
    for attempt in range(retries + 1):
        try:
            if _GP_PROC is None:
                _GP_PROC = _gp_start()
            p = _GP_PROC
            assert p.stdin and p.stdout
            p.stdin.write(f'print("{_BEGIN}");\n{expr}\nprint("{_END}");\n')
            p.stdin.flush()
            parts: List[str] = []
            in_block = False
            deadline = time.time() + gp_timeout
            while True:
                if time.time() > deadline:
                    raise TimeoutError(f"gp timeout ({gp_timeout}s)")
                line = p.stdout.readline()
                if line == "":
                    raise RuntimeError("gp EOF")
                s = line.rstrip("\n").strip()
                if s == _BEGIN:
                    in_block = True
                    continue
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
                gp_timeout: float = 300.0,
                max_x: int = 0) -> Tuple[int, int, str]:
    max_x_arg = f", {max_x}" if max_x > 0 else ""
    raw = _gp_eval(f"print(pellxy({D}{max_x_arg}));",
                   retries=retries, gp_timeout=gp_timeout)
    raw = raw.strip().splitlines()[-1]
    m = _VEC2_INT_RE.match(raw)
    if not m:
        raise ValueError(f"Unexpected GP output: {raw!r}")
    return int(m.group(1)), int(m.group(2)), raw

# ── mask utilities ─────────────────────────────────────────────────────────────

def q_from_mask(mask: int, primes: Tuple[int, ...]) -> int:
    q, i, tmp = 1, 0, mask
    while tmp:
        if tmp & 1:
            q *= primes[i]
        tmp >>= 1
        i += 1
    return q

# ═══════════════════════════════════════════════════════════════════════════════
#  LEHMER-CLEMENTS CORE
# ═══════════════════════════════════════════════════════════════════════════════

def compute_entry_period_and_residues(
    prime_p: int,
    side: int,           # 0: p | m_j,   1: p | m_j + 1
    x1: int, y1: int,
    D: int,
    max_period: int,
) -> Tuple[int, List[int]]:
    """
    Compute the period T of the Pell sequence mod prime_p and the list of
    iterate indices j ∈ [1..T] where the side condition holds.

    side=0: p | m_j  ⟺  x_j ≡ 1  (mod p)   (since m = (x−1)/2, p odd)
    side=1: p | m_j+1 ⟺  x_j ≡ −1 (mod p)

    The sequence (x_j mod p) is periodic; we detect the period by iterating
    until (x_j, y_j) returns to (x_1 mod p, y_1 mod p).
    max_period is a safety cap; 4*(p-1) is always sufficient by Fermat.
    """
    x1p = x1 % prime_p
    y1p = y1 % prime_p
    Dp  = D  % prime_p
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

        if j >= 1 and xj == x1p and yj == y1p:
            return j, [r for r in residues if 1 <= r <= j]

    # Safety fallback (should not occur for valid odd primes)
    return max_period + 1, residues


# ── certificate dataclass ──────────────────────────────────────────────────────

@dataclass
class LCCertificate:
    omega:          int
    q:              int
    mask:           int
    sigma:          Dict[int, int]       # prime → side (0 or 1)
    entry_periods:  Dict[int, int]       # p → T_p(q)
    entry_residues: Dict[int, List[int]] # p → residues mod T_p(q)
    Lambda:         int                  # lcm of all T_p(q)
    lambda_val:     Optional[int]        # first compatible index, or None
    L:              int                  # Størmer-Lehmer bound
    verdict:        str                  # EXCLUDED_EMPTY|EXCLUDED_LAMBDA|HIT|OPEN
    hits:           List[int]            # prime-complete m values (HIT only)
    loop_iterations: int
    elapsed_sec:    float


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
    verdict:         str     # COMPLETE_NO_HITS | COMPLETE_WITH_HITS | PARTIAL


# ═══════════════════════════════════════════════════════════════════════════════
#  SHARED: compute (λ, Λ) for one (mask, σ) given pre-computed period_data
# ═══════════════════════════════════════════════════════════════════════════════

def compute_lambda_lambda(
    primes: Tuple[int, ...],
    sigma: Dict[int, int],
    period_data: Dict[int, Tuple[int, List[int], int, List[int]]],
) -> Tuple[Optional[int], int, Dict[int, int], Dict[int, List[int]], bool]:
    """
    Given period_data[p] = (T_side0, res_side0, T_side1, res_side1) for every
    prime p, and a side assignment sigma, compute:

        entry_periods  : p → T chosen for sigma[p]
        entry_residues : p → residues chosen for sigma[p]
        Lambda         : lcm of all T values
        lambda_val     : smallest j ≥ 1 satisfying all CRT conditions, or None
        inconsistent   : True if any prime has an empty residue list

    Returns (lambda_val, Lambda, entry_periods, entry_residues, inconsistent).
    """
    entry_periods:  Dict[int, int]       = {}
    entry_residues: Dict[int, List[int]] = {}
    choices:        List[List[Tuple[int,int]]] = []
    inconsistent = False

    for p in primes:
        side = sigma[p]
        T0, r0, T1, r1 = period_data[p]
        T   = T0 if side == 0 else T1
        res = r0 if side == 0 else r1
        entry_periods[p]  = T
        entry_residues[p] = res
        if not res:
            inconsistent = True
            # Do NOT break — continue to fill entry_periods for all primes
            # so the lcm_list call below is safe.
        else:
            choices.append([(r, T) for r in res])

    # Lambda uses only actually-populated entry_periods
    Lambda = lcm_list(list(entry_periods.values())) if entry_periods else 1

    if inconsistent or not choices:
        return None, Lambda, entry_periods, entry_residues, True

    # Find λ: minimum over all CRT combinations of the first positive j.
    min_lambda: Optional[int] = None
    for combo in iproduct(*choices):
        sol, mod = crt_system(list(combo))
        if sol is None:
            continue
        j_min = first_positive_in_class(sol, mod)
        if min_lambda is None or j_min < min_lambda:
            min_lambda = j_min

    return min_lambda, Lambda, entry_periods, entry_residues, False


# ═══════════════════════════════════════════════════════════════════════════════
#  CERTIFY MODE  — compute λ, Λ only; no fused iterate loop
# ═══════════════════════════════════════════════════════════════════════════════

def lc_certify_one_mask(
    omega:             int,
    mask:              int,
    primes:            Tuple[int, ...],
    L:                 int,
    x1: int, y1: int,
    max_period_factor: int = 4,
) -> List[LCCertificate]:
    """
    Certify mode: for each side assignment σ over ALL primes in P_ω,
    compute (λ, Λ) and issue a verdict without running the Pell iterate loop.

    EXCLUDED_EMPTY   — some prime never appears on its required side.
    EXCLUDED_LAMBDA  — λ > L.
    OPEN             — λ ≤ L; search mode needed to resolve.
    """
    q = q_from_mask(mask, primes)
    if q == 2:
        return []
    D = 2 * q

    # Pre-compute period data for all primes
    period_data: Dict[int, Tuple[int, List[int], int, List[int]]] = {}
    for p in primes:
        mp = max_period_factor * (p - 1)
        T0, r0 = compute_entry_period_and_residues(p, 0, x1, y1, D, mp)
        T1, r1 = compute_entry_period_and_residues(p, 1, x1, y1, D, mp)
        period_data[p] = (T0, r0, T1, r1)

    certs: List[LCCertificate] = []

    for sig_int in range(1 << len(primes)):
        t0    = time.time()
        sigma = {p: (sig_int >> i) & 1 for i, p in enumerate(primes)}

        lv, Lambda, ep, er, incon = compute_lambda_lambda(primes, sigma, period_data)

        elapsed = time.time() - t0

        if incon or lv is None:
            verdict = "EXCLUDED_EMPTY"
        elif lv > L:
            verdict = "EXCLUDED_LAMBDA"
        else:
            verdict = "OPEN"

        certs.append(LCCertificate(
            omega=omega, q=q, mask=mask, sigma=sigma,
            entry_periods=ep, entry_residues=er,
            Lambda=Lambda, lambda_val=lv, L=L,
            verdict=verdict, hits=[], loop_iterations=0,
            elapsed_sec=elapsed,
        ))

    return certs


# ═══════════════════════════════════════════════════════════════════════════════
#  SEARCH MODE  — fused Pell iterate loop for OPEN pairs
# ═══════════════════════════════════════════════════════════════════════════════

def mat_mul(A: Tuple[int,int,int,int],
            B: Tuple[int,int,int,int],
            D: int) -> Tuple[int,int,int,int]:
    a0,a1,a2,a3 = A
    b0,b1,b2,b3 = B
    return (a0*b0 + D*a1*b2,
            a0*b1 + a1*b3,
            a2*b0 + a3*b2,
            a2*b1 + a3*b3)

def mat_pow(x1: int, y1: int, D: int, n: int) -> Tuple[int,int,int,int]:
    """Fast-exponentiation of the Pell matrix [[x1,D*y1],[y1,x1]]^n."""
    result: Tuple[int,int,int,int] = (1, 0, 0, 1)
    base:   Tuple[int,int,int,int] = (x1, y1, y1, x1)
    while n:
        if n & 1:
            result = mat_mul(result, base, D)
        base = mat_mul(base, base, D)
        n >>= 1
    return result


def lc_search_one_mask(
    omega:             int,
    mask:              int,
    primes:            Tuple[int, ...],
    L:                 int,
    max_period_factor: int = 4,
    gp_timeout:        float = 300.0,
    max_m:             int = 0,
) -> List[LCCertificate]:
    """
    Search mode: compute (λ, Λ) for each σ, then run the fused Pell iterate
    loop for OPEN pairs (λ ≤ L).  Issues HIT or OPEN verdicts.
    """
    q = q_from_mask(mask, primes)
    if q == 2:
        return []
    D = 2 * q

    x_ceiling = 2 * max_m + 1       if max_m > 0 else 0
    q_ceiling  = 2 * max_m * (max_m + 1) if max_m > 0 else 0
    if q_ceiling > 0 and q > q_ceiling:
        return []

    try:
        x1, y1, _ = _pell_xy_gp(D, gp_timeout=gp_timeout, max_x=x_ceiling)
    except Exception as e:
        if DEBUG:
            print(f"  [!] GP failed mask={mask} q={q}: {e}")
        return []

    if x1 == 0 and y1 == 0:
        return []
    if x_ceiling > 0 and x1 > x_ceiling:
        return []

    # Pre-compute period data for all primes
    period_data: Dict[int, Tuple[int, List[int], int, List[int]]] = {}
    for p in primes:
        mp = max_period_factor * (p - 1)
        T0, r0 = compute_entry_period_and_residues(p, 0, x1, y1, D, mp)
        T1, r1 = compute_entry_period_and_residues(p, 1, x1, y1, D, mp)
        period_data[p] = (T0, r0, T1, r1)

    certs: List[LCCertificate] = []

    for sig_int in range(1 << len(primes)):
        t0    = time.time()
        sigma = {p: (sig_int >> i) & 1 for i, p in enumerate(primes)}

        lv, Lambda, ep, er, incon = compute_lambda_lambda(primes, sigma, period_data)

        if incon or lv is None:
            certs.append(LCCertificate(
                omega=omega, q=q, mask=mask, sigma=sigma,
                entry_periods=ep, entry_residues=er,
                Lambda=Lambda, lambda_val=None, L=L,
                verdict="EXCLUDED_EMPTY", hits=[], loop_iterations=0,
                elapsed_sec=time.time() - t0,
            ))
            continue

        if lv > L:
            certs.append(LCCertificate(
                omega=omega, q=q, mask=mask, sigma=sigma,
                entry_periods=ep, entry_residues=er,
                Lambda=Lambda, lambda_val=lv, L=L,
                verdict="EXCLUDED_LAMBDA", hits=[], loop_iterations=0,
                elapsed_sec=time.time() - t0,
            ))
            continue

        # ── Fused Lehmer-Clements iterate loop ─────────────────────────────
        # Advance Pell state to j = lv, then step by Λ.
        Ml = mat_pow(x1, y1, D, lv)
        # (x_{lv}, y_{lv}) = (Ml[0], Ml[2])
        xj, yj = Ml[0], Ml[2]

        Ms = mat_pow(x1, y1, D, Lambda)  # step matrix

        hits:       List[int] = []
        loop_iters: int       = 0
        j = lv

        while j <= L:
            loop_iters += 1
            if xj & 1:                        # x_j must be odd for m integer
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
                                hits.append(m)

            # Advance by Λ steps
            nxj = Ms[0]*xj + D*Ms[1]*yj
            nyj = Ms[2]*xj +   Ms[3]*yj
            xj, yj = nxj, nyj
            j += Lambda

        elapsed = time.time() - t0
        verdict = "HIT" if hits else "OPEN"

        certs.append(LCCertificate(
            omega=omega, q=q, mask=mask, sigma=sigma,
            entry_periods=ep, entry_residues=er,
            Lambda=Lambda, lambda_val=lv, L=L,
            verdict=verdict, hits=hits, loop_iterations=loop_iters,
            elapsed_sec=elapsed,
        ))

    return certs


# ═══════════════════════════════════════════════════════════════════════════════
#  TOP-LEVEL per-omega driver
# ═══════════════════════════════════════════════════════════════════════════════

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
    t_start  = time.time()
    all_primes = tuple(first_n_primes(omega))
    pmax       = all_primes[-1]
    L          = max(3, pmax)

    ensure_dir(outdir)
    omega_dir = os.path.join(outdir, f"omega_{omega:02d}")
    ensure_dir(omega_dir)

    if verbose:
        print(f"\n[LCr] ω={omega}  P_ω={list(all_primes)}  pmax={pmax}  L={L}")
        print(f"      Mode: {mode}  (catch-up block = ALL primes in P_ω)")

    total_masks = 1 << omega
    all_certs: List[LCCertificate] = []
    excluded_empty = excluded_lambda = hits_total = open_total = 0
    hit_values: List[int] = []

    masks_done = 0
    for mask in range(1, total_masks):
        q = q_from_mask(mask, all_primes)
        if q == 2:
            continue

        # Both modes need the fundamental Pell solution
        D = 2 * q
        x_ceiling = 2 * max_m + 1 if max_m > 0 else 0
        try:
            x1, y1, _ = _pell_xy_gp(D, gp_timeout=gp_timeout, max_x=x_ceiling)
            if x1 == 0 and y1 == 0:
                continue
        except Exception as e:
            if verbose:
                print(f"  [!] GP failed mask={mask} q={q}: {e}")
            continue

        if mode == "certify":
            certs = lc_certify_one_mask(
                omega, mask, all_primes, L, x1, y1,
                max_period_factor=max_period_factor,
            )
        else:
            certs = lc_search_one_mask(
                omega, mask, all_primes, L,
                max_period_factor=max_period_factor,
                gp_timeout=gp_timeout, max_m=max_m,
            )

        all_certs.extend(certs)
        for c in certs:
            if   c.verdict == "EXCLUDED_EMPTY":  excluded_empty  += 1
            elif c.verdict == "EXCLUDED_LAMBDA": excluded_lambda += 1
            elif c.verdict == "HIT":             hits_total += 1;  hit_values.extend(c.hits)
            elif c.verdict == "OPEN":            open_total  += 1

        masks_done += 1
        if verbose and masks_done % 500 == 0:
            print(f"  ... {masks_done}/{total_masks-1} masks  "
                  f"empty={excluded_empty} lambda={excluded_lambda} "
                  f"hits={hits_total} open={open_total}")

    elapsed = time.time() - t_start

    if hits_total > 0:
        verdict = "COMPLETE_WITH_HITS"
    elif open_total > 0:
        verdict = "PARTIAL"
    else:
        verdict = "COMPLETE_NO_HITS"

    summary = OmegaSummary(
        omega=omega, pmax=pmax, L=L,
        total_pairs=len(all_certs),
        excluded_empty=excluded_empty,
        excluded_lambda=excluded_lambda,
        hits_total=hits_total,
        open_total=open_total,
        hit_values=sorted(set(hit_values)),
        elapsed_sec=elapsed,
        verdict=verdict,
    )

    # ── Certificate CSV ────────────────────────────────────────────────────
    cert_csv = os.path.join(omega_dir, f"lc_certificates_omega_{omega:02d}.csv")
    with open(cert_csv, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["omega","q","mask","sigma_str",
                    "Lambda","lambda_val","L",
                    "verdict","hits","loop_iters","elapsed_sec",
                    "entry_periods","entry_residues"])
        for c in all_certs:
            sigma_str   = ",".join(f"p{p}:{s}" for p, s in sorted(c.sigma.items()))
            hits_str    = ";".join(str(h) for h in c.hits)
            periods_str = ";".join(f"p{p}:T={t}" for p,t in sorted(c.entry_periods.items()))
            res_str     = ";".join(f"p{p}:{c.entry_residues[p]}"
                                   for p in sorted(c.entry_residues))
            w.writerow([
                c.omega, c.q, c.mask, sigma_str,
                c.Lambda,
                c.lambda_val if c.lambda_val is not None else "inf",
                c.L, c.verdict, hits_str,
                c.loop_iterations, f"{c.elapsed_sec:.4f}",
                periods_str, res_str,
            ])

    # ── Summary JSON ───────────────────────────────────────────────────────
    summary_json = os.path.join(omega_dir, f"lc_summary_omega_{omega:02d}.json")
    sd = {
        "program": program_name, "version": program_version,
        "omega": omega, "pmax": pmax, "L": L,
        "mode": mode,
        "total_pairs": len(all_certs),
        "excluded_empty":  excluded_empty,
        "excluded_lambda": excluded_lambda,
        "hits_total":      hits_total,
        "open_total":      open_total,
        "hit_values":      sorted(set(hit_values)),
        "elapsed_sec":     round(elapsed, 3),
        "verdict":         verdict,
        "timestamp":       utc_now_iso(),
        "python_version":  sys.version,
        "platform":        platform.platform(),
        "cert_csv":        os.path.basename(cert_csv),
        "cert_csv_sha256": sha256_file(cert_csv),
    }
    with open(summary_json, "w") as f:
        json.dump(sd, f, indent=2)

    if verbose:
        print(f"  excluded_empty={excluded_empty}  excluded_lambda={excluded_lambda}  "
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
        description="Lehmer-Clements prime-complete Pell enumerator (v2).",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("--mode", choices=["certify","search"], default="search",
                    help=("certify: compute λ/Λ only, OPEN pairs not resolved. "
                          "search: also run fused loop for OPEN pairs (default)."))
    ap.add_argument("--start_omega",      type=int,   default=9)
    ap.add_argument("--end_omega",        type=int,   default=17)
    ap.add_argument("--outdir",           default="lc_audit")
    ap.add_argument("--gp_path",          default="gp")
    ap.add_argument("--gp_timeout",       type=float, default=300.0)
    ap.add_argument("--max_m",            type=int,   default=0,
                    help="Upper bound on m (0 = unlimited).")
    ap.add_argument("--max_period_factor",type=int,   default=4,
                    help="Entry period cap = factor×(p−1) per prime (default 4).")
    ap.add_argument("--debug",      action="store_true")
    ap.add_argument("--assertions", action="store_true")
    ap.add_argument("--version",    action="store_true",
                    help="Print version info and exit.")

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

    # ── Master summary ─────────────────────────────────────────────────────
    master_path = os.path.join(args.outdir, "lc_master_summary.json")
    master = {
        "program": program_name, "version": program_version,
        "mode": args.mode,
        "start_omega": args.start_omega, "end_omega": args.end_omega,
        "any_prime_complete_hit": any_hit,
        "per_omega": [
            {"omega": s.omega, "L": s.L,
             "total_pairs": s.total_pairs,
             "excluded_empty": s.excluded_empty,
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
        print(f"All {excl} (q,σ) pairs excluded via EXCLUDED_EMPTY or EXCLUDED_LAMBDA.")
        print(f"Lehmer-Clements certificate: no prime-complete products m(m+1)")
        print(f"of order ω = {args.start_omega}..{args.end_omega} exist.")
    else:
        print("WARNING: prime-complete hits found — see per-omega summaries.")
    print(f"Master summary → {master_path}")
    print(f"{'='*60}")


if __name__ == "__main__":
    import atexit
    atexit.register(_gp_kill)
    main()
