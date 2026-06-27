#!/usr/bin/env python3
# LCm_Solver.py version 6.4-prune

"""
LCm_Solver — Lehmer-Clements prime-complete enumerator, version 6.4-prune
================================================================================
VERSION 6.4-prune (June 2026) — Y1-SUPPORT RANK PRUNING
================================================================================

Purpose
-------
For a target omega, enumerate squarefree discriminants D | P_omega, solve

    x^2 - D y^2 = 1,

and certify/search for prime-complete consecutive pairs

    m = (x_j - 1)/2,   m+1 = (x_j + 1)/2,

with rad(m(m+1)) = P_omega.

Version 6 extends the v5 high-omega engine.  Version 6.2 keeps the v6 mathematics 
but changes the default work unit to Pell microblocks: at most one low-prime DFS 
bit per high-mask task.  At omega=16 this changes the default from 1,024 blocks 
of 64 discriminants to 32,768 blocks of one or two discriminants, so one 
pathological Pell discriminant cannot strand a worker with a large private queue.

Version 6.0 note:  Version 4 enumerated every canonical
(D, sigma_U) seat system.  That is a useful proof object, but at omega=18 it
creates about 2.58e8 sigma rows.  Merely writing those rows to /dev/null still
requires Python dictionary/list construction, IPC, formatting, and aggregation.

The v6 default engine computes a provable rank-of-apparition LCM for each D and 
checks only admissible Pell indices j <= L.  Under
the same Lehmer/primitive-divisor ceiling used by v4,

    L(omega) = max(30, p_omega + 1),

this is a direct certificate: every possible target pair appears among these
indices.  The work is bounded by roughly (2^omega-1) * L recurrence positions,
before the y1 smoothness gate.  For omega=18 this is ~16.25 million index
positions instead of ~258 million sigma-row decisions.

Main systems changes
--------------------
1. cypari2 fast path.  Each worker initializes one PARI session and calls the
   in-memory pellxy() function directly.  If cypari2 is unavailable or fails,
   v6 falls back to a persistent subprocess-gp session.

2. Squarefree-only Pell function.  Because D is generated as a squarefree
   divisor of P_omega, the GP/PARI function does not factor D internally.

3. y1 smoothness gate.  If the fundamental y1 is not P_omega-smooth, then y1
   divides every y_j in the Pell-Lucas sequence, so that discriminant cannot
   produce a P_omega-smooth consecutive pair and is skipped.

4. In-worker block generation.  Tasks are high-prime blocks, not individual D's.
   Each worker runs a DFS over the low primes internally and returns one compact
   aggregate per block.  In v6.3, --max_low_bits 0 is also supported: H=omega,
   so each task is a single nonempty discriminant mask.  This is adapted from
   A002072_Solver v10.

5. Compact audit output.  v6 writes optional one-row-per-D CSV records, not
   one-row-per-(D,sigma_U) certificate rows.  This keeps high-omega audit files
   feasible.

Soundness note
--------------
A v6 "certify" verdict is conditional on the index ceiling L being valid for
the target theorem.  This is the same ceiling asserted in v4's Cor. 3.13 note,
but v6 uses it through a rank-LCM necessary condition: every unramified odd
census prime p must divide y_j, so j must be a multiple of the rank
rho_p(D).  If the accumulated LCM exceeds L, the vein is provably dead;
otherwise only multiples of that LCM are checked.

By Ken Clements, version 6.3 implementation generated with ChatGPT, June 2026.
"""

from __future__ import annotations

import argparse
import atexit
import csv
import hashlib
import json
import math
import multiprocessing as mp
import os
import platform
import re
import resource
import subprocess
import sys
import time
from collections import defaultdict
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Any, Dict, Iterable, List, Optional, Set, Tuple

try:
    sys.set_int_max_str_digits(0)
except Exception:
    pass

PROGRAM_NAME = "LCm_Solver"
PROGRAM_VERSION = "6.4-prune"

# ---------------------------------------------------------------------------
# Known prime-complete consecutive pairs, keyed by omega level.
# Regression gate: a certificate run should recover all catalogued pairs.
# ---------------------------------------------------------------------------
KNOWN_PRIME_COMPLETE: Dict[int, List[int]] = {
    1:  [1],
    2:  [2, 3, 8],
    3:  [5, 9, 15, 24, 80],
    4:  [14, 20, 35, 125, 224, 2400, 4374],
    5:  [384, 440, 539, 3024, 9800],
    6:  [1715, 2079, 123200],
    7:  [714, 12375, 194480],
    8:  [633555],
}

# ---------------------------------------------------------------------------
# Optional accelerators
# ---------------------------------------------------------------------------
try:
    import gmpy2  # type: ignore
    from gmpy2 import mpz as _mpz  # type: ignore

    def mpz(x):
        return _mpz(x)

    HAS_GMPY2 = True
except Exception:
    def mpz(x):  # type: ignore[misc]
        return int(x)

    HAS_GMPY2 = False

try:
    import cypari2 as _cypari2  # type: ignore
    HAS_CYPARI2 = True
except Exception:
    _cypari2 = None  # type: ignore
    HAS_CYPARI2 = False

try:
    _popcount = int.bit_count  # unbound method
    _popcount(0)
except Exception:
    def _popcount(x: int) -> int:  # type: ignore[misc]
        return bin(x).count("1")

# ---------------------------------------------------------------------------
# Utilities
# ---------------------------------------------------------------------------

def utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def ensure_dir(path: str) -> None:
    os.makedirs(path, exist_ok=True)


def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def sieve(n: int) -> List[int]:
    if n < 2:
        return []
    flags = bytearray([1]) * (n + 1)
    flags[0] = flags[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if flags[i]:
            flags[i * i::i] = bytearray(len(flags[i * i::i]))
    return [i for i, f in enumerate(flags) if f]


def first_n_primes(n: int) -> List[int]:
    if n <= 0:
        return []
    est = max(15, int(n * (math.log(n) + math.log(math.log(n + 2)) + 2)))
    ps = sieve(est)
    while len(ps) < n:
        est *= 2
        ps = sieve(est)
    return ps[:n]


def proven_L(pmax: int) -> int:
    """Unconditional index ceiling used by LCm v4: max(30, p_omega + 1)."""
    return max(30, pmax + 1)


def gcd_int(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return abs(a)


def lcm_int(a: int, b: int) -> int:
    if a == 0 or b == 0:
        return 0
    return a // gcd_int(a, b) * b


def peak_rss_mb() -> float:
    try:
        ru = resource.getrusage(resource.RUSAGE_SELF)
        if platform.system() == "Darwin":
            return ru.ru_maxrss / (1024 * 1024)
        return ru.ru_maxrss / 1024
    except Exception:
        return 0.0


def D_from_mask(mask: int, primes: Tuple[int, ...]) -> int:
    D, tmp, i = 1, mask, 0
    while tmp:
        if tmp & 1:
            D *= primes[i]
        tmp >>= 1
        i += 1
    return D


def mask_to_primes(mask: int, primes: Tuple[int, ...]) -> List[int]:
    out: List[int] = []
    tmp, i = mask, 0
    while tmp:
        if tmp & 1:
            out.append(primes[i])
        tmp >>= 1
        i += 1
    return out


def choose_high_bits(omega: int, block_log2: int, workers: int,
                     min_blocks_per_worker: int = 64,
                     max_low_bits: int = 7) -> int:
    """Choose high-mask split H.

    ``low_bits = omega - H`` is the number of low-prime DFS bits per task.
    v6.2 defaulted to ``max_low_bits=1`` (one or two discriminants per task).
    v6.3 also permits ``max_low_bits=0``; then H=omega and each nonempty
    high_mask is exactly one discriminant task.

    These are load-balancing constraints only.  They do not change the set of
    discriminants or any LC-rank proof condition.
    """
    if omega <= 1:
        return 0
    if max_low_bits <= 0:
        return omega
    min_blocks = max(2, workers * max(1, min_blocks_per_worker))
    H_from_block_size = omega - max(1, block_log2)
    H_from_min_blocks = math.ceil(math.log2(min_blocks))
    H_from_low_cap = omega - max(1, max_low_bits)
    H = max(H_from_block_size, H_from_min_blocks, H_from_low_cap)
    return max(0, min(H, omega - 1))


def high_mask_sort_key(high_mask: int, primes_high: Tuple[int, ...]) -> Tuple[int, float, int]:
    """Heuristic difficulty key for block scheduling.

    Blocks containing many large high primes tend to contain larger D values and
    are often Pell-expensive.  Submitting them first reduces tail latency.  The
    key is only a scheduling heuristic; correctness is independent of it.
    """
    pc = _popcount(high_mask)
    log_prod = 0.0
    for i, p in enumerate(primes_high):
        if (high_mask >> i) & 1:
            log_prod += math.log(p)
    return (pc, log_prod, high_mask)


# ---------------------------------------------------------------------------
# PARI / GP Pell interface
# ---------------------------------------------------------------------------

# D is already squarefree in this solver, so no factor(D) normalization is done.
_PELL_GP_SRC = r"""
pellxy(D, max_x=0)={
  if(D<=0, error("D<=0"));
  if(issquare(D), error("D is square"));
  my(a0=sqrtint(D), m=0, d=1, a=a0, p0=1, p1=a0, q0=0, q1=1);
  while(p1^2 - D*q1^2 != 1,
    m = d*a - m;
    d = (D - m^2)/d;
    a = (a0 + m)\d;
    my(p2=a*p1+p0, q2=a*q1+q0);
    p0=p1; p1=p2; q0=q1; q1=q2;
    if(max_x>0 && p1>max_x, return([0,0]));
  );
  if(max_x>0 && p1>max_x, return([0,0]));
  [p1, q1];
};
"""

_VEC2_RE = re.compile(r"^\[\s*(-?\d+)\s*,\s*(-?\d+)\s*\]\s*$")
_SENTINEL = "__LCM_SOLVER_V6_SEP__"

_PARI_SESSION = None
_GP_PROC: Optional[subprocess.Popen] = None
_GP_PATH_GLOBAL = "gp"


def _gp_kill() -> None:
    global _GP_PROC
    if _GP_PROC is not None:
        try:
            _GP_PROC.kill()
        except Exception:
            pass
    _GP_PROC = None


def _init_pari(gp_path: str, quiet: bool = True) -> None:
    """Initialize a cypari2 session in this process if available."""
    global _PARI_SESSION, _GP_PATH_GLOBAL
    _GP_PATH_GLOBAL = gp_path
    _PARI_SESSION = None
    if not HAS_CYPARI2:
        return
    try:
        pari = _cypari2.Pari()  # type: ignore[union-attr]
        try:
            pari.allocatemem(256 * 1024 * 1024, silent=True)
        except TypeError:
            import contextlib
            import io
            with contextlib.redirect_stdout(io.StringIO()):
                pari.allocatemem(256 * 1024 * 1024)
        pari(_PELL_GP_SRC)
        v = pari("pellxy(46)")
        if int(v[0]) ** 2 - 46 * int(v[1]) ** 2 != 1:
            raise RuntimeError("cypari2 Pell self-test failed")
        _PARI_SESSION = pari
    except Exception as e:
        _PARI_SESSION = None
        if not quiet:
            print(f"  [pari] cypari2 init failed: {e!r}; using subprocess gp", flush=True)


def _gp_start() -> subprocess.Popen:
    p = subprocess.Popen(
        [_GP_PATH_GLOBAL, "-q"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )
    assert p.stdin and p.stdout
    p.stdin.write(_PELL_GP_SRC + "\n")
    p.stdin.write(f'print("{_SENTINEL}_start");\n')
    p.stdin.write("print(pellxy(46));\n")
    p.stdin.write("v=pellxy(46); print(v[1]^2 - 46*v[2]^2);\n")
    p.stdin.write("print(pellxy(46, 100));\n")
    p.stdin.write(f'print("{_SENTINEL}_end");\n')
    p.stdin.flush()

    lines: List[str] = []
    in_block = False
    while True:
        line = p.stdout.readline()
        if not line:
            raise RuntimeError("gp handshake EOF")
        s = line.strip()
        if s == f"{_SENTINEL}_start":
            in_block = True
            continue
        if s == f"{_SENTINEL}_end":
            break
        if in_block:
            lines.append(s)
    if len(lines) < 3 or lines[1] != "1" or lines[2].replace(" ", "") != "[0,0]":
        raise RuntimeError(f"gp handshake failed: {lines}")
    return p


def _gp_eval(expr: str) -> str:
    """Persistent subprocess-gp fallback.  No per-call thread/timeout overhead."""
    global _GP_PROC
    if _GP_PROC is None:
        _GP_PROC = _gp_start()
    assert _GP_PROC.stdin and _GP_PROC.stdout
    _GP_PROC.stdin.write(f'print("{_SENTINEL}_start");\n')
    _GP_PROC.stdin.write(f"print({expr});\n")
    _GP_PROC.stdin.write(f'print("{_SENTINEL}_end");\n')
    _GP_PROC.stdin.flush()

    lines: List[str] = []
    in_block = False
    while True:
        line = _GP_PROC.stdout.readline()
        if not line:
            raise RuntimeError("gp EOF")
        s = line.strip()
        if s == f"{_SENTINEL}_start":
            in_block = True
            continue
        if s == f"{_SENTINEL}_end":
            break
        if in_block:
            lines.append(s)
    return "\n".join(lines).strip()


def _pell_fundamental(D: int, max_x: int = 0, retries: int = 2) -> Tuple[int, int]:
    """Return fundamental (x1,y1), or (0,0) if max_x>0 and x1>max_x."""
    if _PARI_SESSION is not None:
        try:
            v = _PARI_SESSION(f"pellxy({D}, {max_x})") if max_x > 0 else _PARI_SESSION(f"pellxy({D})")
            return int(v[0]), int(v[1])
        except Exception:
            # Fall through to gp.  A single bad cypari2 call should not kill a run.
            pass

    last_exc: Optional[Exception] = None
    for _ in range(retries + 1):
        try:
            expr = f"pellxy({D}, {max_x})" if max_x > 0 else f"pellxy({D})"
            out = _gp_eval(expr)
            if "***" in out or "error" in out.lower():
                raise RuntimeError(f"gp error: {out[:200]}")
            last = out.strip().splitlines()[-1]
            m = _VEC2_RE.match(last)
            if not m:
                raise RuntimeError(f"Unexpected gp output: {out!r}")
            return int(m.group(1)), int(m.group(2))
        except Exception as e:
            last_exc = e
            _gp_kill()
    raise RuntimeError(f"Pell solver failed for D={D}: {last_exc!r}")


# ---------------------------------------------------------------------------
# Per-process recurrence worker state
# ---------------------------------------------------------------------------

_S: Dict[str, Any] = {}


def _worker_init(primes: Tuple[int, ...], gp_path: str, max_m: int, L_index: int,
                 H: int, emit_d_rows: bool, quiet_pari: bool,
                 slow_d_limit: int = 50, slow_d_min_sec: float = 0.0) -> None:
    try:
        sys.set_int_max_str_digits(0)
    except Exception:
        pass
    _init_pari(gp_path, quiet=quiet_pari)

    omega = len(primes)
    low_count = omega - H
    primes_low = primes[:low_count]
    primes_high = primes[low_count:]
    primes_mpz = [mpz(p) for p in primes]

    if HAS_GMPY2:
        remove_fn = gmpy2.remove  # type: ignore[name-defined]
    else:
        def remove_fn(n, p):  # type: ignore[misc]
            k = 0
            while n % p == 0:
                n //= p
                k += 1
            return n, k

    ONE = mpz(1)
    full_mask = (1 << omega) - 1

    def factor_smooth_mask(n) -> Tuple[bool, int]:
        """Return (is P_omega-smooth, support mask) for n >= 1."""
        if n < ONE:
            return False, 0
        support = 0
        for i, p in enumerate(primes_mpz):
            if n % p == 0:
                support |= 1 << i
                n, _ = remove_fn(n, p)
                if n <= ONE:
                    return True, support
        return n == ONE, support

    _S.clear()
    _S.update({
        "primes": primes,
        "omega": omega,
        "H": H,
        "low_count": low_count,
        "primes_low": primes_low,
        "primes_high": primes_high,
        "max_m": max_m,
        "max_x": 2 * max_m + 1 if max_m > 0 else 0,
        # Sharpened cap prefilter.  If m <= max_m and
        # 4*m*(m+1) = D*y^2, then D is also the squarefree kernel of
        # m*(m+1), hence D <= m*(m+1) <= max_m*(max_m+1).
        "D_prefilter_T": max_m * (max_m + 1) if max_m > 0 else 0,
        "L_index": L_index,
        "ONE": ONE,
        "full_mask": full_mask,
        "factor_smooth_mask": factor_smooth_mask,
        "emit_d_rows": emit_d_rows,
        "slow_d_limit": slow_d_limit,
        "slow_d_min_sec": slow_d_min_sec,
    })


@dataclass
class DRow:
    D: int
    mask: int
    status: str
    x1_digits: int = 0
    y1_digits: int = 0
    y1_smooth: Optional[bool] = None
    rank_R: int = 0
    rank_missing_prime: int = 0
    rank_multiples: int = 0
    j_checked: int = 0
    smooth_pairs: int = 0
    hits: List[int] = field(default_factory=list)
    error: str = ""
    pell_sec: float = 0.0
    total_sec: float = 0.0


@dataclass
class BlockResult:
    high_mask: int
    n_d_run: int = 0
    n_prefiltered: int = 0
    n_cut_by_x: int = 0
    n_gate_y1: int = 0
    n_rank_missing: int = 0
    n_rank_lcm_exceeds: int = 0
    n_rank_survives: int = 0
    n_rank_candidate_indices: int = 0
    n_index_checked: int = 0
    n_odd_x: int = 0
    n_y_smooth_at_rank: int = 0
    n_smooth_pairs: int = 0
    n_hit_discriminants: int = 0
    hit_values: List[int] = field(default_factory=list)
    hit_records: List[Dict[str, Any]] = field(default_factory=list)
    n_errors: int = 0
    error_samples: List[str] = field(default_factory=list)
    d_rows: List[DRow] = field(default_factory=list)
    slow_d_rows: List[DRow] = field(default_factory=list)
    elapsed_sec: float = 0.0
    pell_sec: float = 0.0
    rank_sec: float = 0.0
    recurrence_sec: float = 0.0


# ---------------------------------------------------------------------------
# Recurrence engine
# ---------------------------------------------------------------------------

def _digits(n: int) -> int:
    try:
        return len(str(n))
    except ValueError:
        return int(n.bit_length() * 0.30103) + 1


def _record_d_row(br: BlockResult, row: DRow) -> None:
    if _S.get("emit_d_rows", False):
        br.d_rows.append(row)


def _finalize_d_row(br: BlockResult, row: DRow, t_d0: float) -> None:
    """Attach timing, emit the normal D-row if requested, and retain slow-D samples.

    Slow-D retention is independent of the full D audit CSV.  Each worker keeps
    only its local top N rows; the parent merges and truncates again.
    """
    row.total_sec = time.time() - t_d0
    _record_d_row(br, row)
    limit = int(_S.get("slow_d_limit", 0) or 0)
    if limit <= 0:
        return
    min_sec = float(_S.get("slow_d_min_sec", 0.0) or 0.0)
    if row.total_sec < min_sec:
        return
    br.slow_d_rows.append(row)
    br.slow_d_rows.sort(key=lambda r: (r.total_sec, r.pell_sec), reverse=True)
    del br.slow_d_rows[limit:]


def _rank_mod_p(D: int, x1: int, y1: int, p: int, L_index: int) -> int:
    """
    Return rho_p(D) = min{j>=1: y_j == 0 mod p}, searched only up to L_index.
    Return 0 if no such j occurs within the certified index window.

    For p odd and p ∤ D, y_j == 0 mod p iff x_j == ±1 mod p, hence p divides
    m_j(m_j+1).  The set of such j is exactly the multiples of rho_p.
    """
    x1p = x1 % p
    y1p = y1 % p
    Dp = D % p
    xj = x1p
    yj = y1p
    for j in range(1, L_index + 1):
        if yj == 0:
            return j
        nx = (x1p * xj + Dp * y1p * yj) % p
        ny = (x1p * yj + y1p * xj) % p
        xj, yj = nx, ny
    return 0


def _rank_lcm_for_D(D: int, mask_D: int, mask_y1: int, x1: int, y1: int,
                    L_index: int) -> Tuple[int, int]:
    """
    Compute the LC rank-LCM obstruction for one vein.

    Only unramified odd census primes p (p != 2 and p ∤ D) whose support is
    not already supplied by y1 impose a nontrivial rank condition.  If p | y1,
    then p | y_j for every Pell-Lucas y_j, so rho_p(D)=1 and the prime can be
    skipped.  The remaining missing primes are processed from largest to
    smallest as a safe pruning heuristic: larger primes tend to force larger
    ranks, so the accumulated LCM often exceeds L_index earlier.

    If any required p has no rank within j <= L, return (0, p).  Otherwise
    return (R, 0), where every prime-complete index must be a multiple of R.
    The computation stops as soon as the accumulated LCM exceeds L_index.
    """
    primes: Tuple[int, ...] = _S["primes"]
    full_mask = int(_S["full_mask"])
    need_mask = full_mask & ~(mask_D | mask_y1)

    R = 1
    needed_indices = [
        i for i, p in enumerate(primes)
        if p != 2 and ((need_mask >> i) & 1)
    ]
    needed_indices.sort(key=lambda i: primes[i], reverse=True)

    for i in needed_indices:
        p = primes[i]
        rho = _rank_mod_p(D, x1, y1, p, L_index)
        if rho == 0:
            return 0, p
        R = lcm_int(R, rho)
        if R > L_index:
            return R, 0
    return R, 0


def _pell_power_mpz(x1, y1, Dm, n: int):
    """Return (x_n,y_n) = (x1+y1*sqrt(D))^n using binary exponentiation."""
    xr = mpz(1)
    yr = mpz(0)
    xb = x1
    yb = y1
    while n:
        if n & 1:
            xr, yr = xr * xb + Dm * yr * yb, xr * yb + yr * xb
        xb, yb = xb * xb + Dm * yb * yb, 2 * xb * yb
        n >>= 1
    return xr, yr


def _process_D_recurrence(D: int, mask_D: int, br: BlockResult) -> None:
    L_index = int(_S["L_index"])
    max_x = int(_S["max_x"])
    ONE = _S["ONE"]
    full_mask = int(_S["full_mask"])
    factor_smooth_mask = _S["factor_smooth_mask"]

    br.n_d_run += 1
    t_d0 = time.time()
    row = DRow(D=D, mask=mask_D, status="START")

    t_pell = time.time()
    try:
        x1, y1 = _pell_fundamental(D, max_x=max_x)
    except Exception as e:
        br.n_errors += 1
        msg = f"D={D}: {e!r}"
        if len(br.error_samples) < 20:
            br.error_samples.append(msg)
        row.status = "ERROR_PELL"
        row.error = repr(e)
        _finalize_d_row(br, row, t_d0)
        return
    finally:
        pell_dt = time.time() - t_pell
        br.pell_sec += pell_dt
        row.pell_sec = pell_dt

    if x1 == 0 and y1 == 0:
        br.n_cut_by_x += 1
        row.status = "CUT_BY_X_CAP"
        _finalize_d_row(br, row, t_d0)
        return

    row.x1_digits = _digits(x1)
    row.y1_digits = _digits(y1)

    Dm = mpz(D)
    x1m = mpz(x1)
    y1m = mpz(y1)
    if x1m * x1m - Dm * y1m * y1m != ONE:
        br.n_errors += 1
        msg = f"D={D}: Pell identity check failed"
        if len(br.error_samples) < 20:
            br.error_samples.append(msg)
        row.status = "ERROR_IDENTITY"
        row.error = msg
        _finalize_d_row(br, row, t_d0)
        return

    sm_y1, mask_y1 = factor_smooth_mask(y1m)
    row.y1_smooth = bool(sm_y1)
    if not sm_y1:
        # Lucas divisibility: y1 | y_j for every j.
        br.n_gate_y1 += 1
        row.status = "GATE_Y1_NOT_SMOOTH"
        _finalize_d_row(br, row, t_d0)
        return

    # LC rank-LCM pruning.  For each unramified odd census prime p, p can occur
    # in m_j(m_j+1) only when p | y_j, i.e. when j is a multiple of rho_p(D).
    t_rank = time.time()
    try:
        R, missing_p = _rank_lcm_for_D(D, mask_D, int(mask_y1), x1, y1, L_index)
    except Exception as e:
        br.n_errors += 1
        msg = f"D={D}: rank computation error {e!r}"
        if len(br.error_samples) < 20:
            br.error_samples.append(msg)
        row.status = "ERROR_RANK"
        row.error = repr(e)
        _finalize_d_row(br, row, t_d0)
        br.rank_sec += time.time() - t_rank
        return
    br.rank_sec += time.time() - t_rank

    row.rank_R = int(R)
    row.rank_missing_prime = int(missing_p)
    if missing_p:
        br.n_rank_missing += 1
        row.status = "RANK_MISSING"
        _finalize_d_row(br, row, t_d0)
        return
    if R <= 0:
        br.n_errors += 1
        msg = f"D={D}: invalid rank LCM R={R}"
        if len(br.error_samples) < 20:
            br.error_samples.append(msg)
        row.status = "ERROR_RANK"
        row.error = msg
        _finalize_d_row(br, row, t_d0)
        return
    if R > L_index:
        br.n_rank_lcm_exceeds += 1
        row.status = "LCM_EXCEEDS_L"
        _finalize_d_row(br, row, t_d0)
        return

    max_k = L_index // R
    row.rank_multiples = max_k
    br.n_rank_survives += 1
    br.n_rank_candidate_indices += max_k

    # Jump directly to j=R and then advance by R each step.  This avoids big-int
    # expansion at indices that cannot possibly contain all missing primes.
    local_smooth_pairs = 0
    local_hits: List[int] = []

    t_rec = time.time()
    try:
        x_step, y_step = _pell_power_mpz(x1m, y1m, Dm, R)
        x = x_step
        y = y_step
        for k in range(1, max_k + 1):
            j = k * R
            if max_x and x > max_x:
                break

            br.n_index_checked += 1
            row.j_checked += 1

            sm_y, mask_y = factor_smooth_mask(y)
            if sm_y:
                br.n_y_smooth_at_rank += 1
                if x & 1:
                    br.n_odd_x += 1
                    local_smooth_pairs += 1
                    br.n_smooth_pairs += 1
                    support = mask_D | mask_y
                    if support == full_mask:
                        m_val = (x - 1) >> 1
                        if m_val > 0:
                            m_int = int(m_val)
                            local_hits.append(m_int)
                            br.hit_values.append(m_int)
                            br.hit_records.append({
                                "m": m_int,
                                "D": D,
                                "mask": mask_D,
                                "j": j,
                                "rank_R": R,
                                "x_digits": _digits(int(x)),
                                "y_digits": _digits(int(y)),
                            })

            if k != max_k:
                x, y = x_step * x + Dm * y_step * y, x_step * y + y_step * x
    except Exception as e:
        br.n_errors += 1
        msg = f"D={D}: recurrence error {e!r}"
        if len(br.error_samples) < 20:
            br.error_samples.append(msg)
        row.status = "ERROR_RECURRENCE"
        row.error = repr(e)
        _finalize_d_row(br, row, t_d0)
        br.recurrence_sec += time.time() - t_rec
        return

    br.recurrence_sec += time.time() - t_rec
    row.smooth_pairs = local_smooth_pairs
    row.hits = local_hits
    if local_hits:
        br.n_hit_discriminants += 1
        row.status = "HIT"
    else:
        row.status = "CHECKED_NO_HIT"
    _finalize_d_row(br, row, t_d0)

def _solver_block(high_mask: int) -> BlockResult:
    t0 = time.time()
    br = BlockResult(high_mask=high_mask)
    try:
        primes_low: Tuple[int, ...] = _S["primes_low"]
        primes_high: Tuple[int, ...] = _S["primes_high"]
        low_count = int(_S["low_count"])
        T = int(_S["D_prefilter_T"])

        base = 1
        high_global_mask = 0
        for i, p in enumerate(primes_high):
            if (high_mask >> i) & 1:
                base *= p
                high_global_mask |= 1 << (low_count + i)

        def run_D(D: int, mask_D: int) -> None:
            _process_D_recurrence(D, mask_D, br)

        if high_mask > 0 and T and base > T:
            # All low subsets keep D >= base > T.  Empty-low included.
            br.n_prefiltered += 1 << low_count
        else:
            if high_mask > 0:
                run_D(base, high_global_mask)

            def rec(i: int, prod: int, mask_prod: int) -> None:
                for j in range(i, low_count):
                    np_ = prod * primes_low[j]
                    nm_ = mask_prod | (1 << j)
                    if T and np_ > T:
                        # All supersets produced by adding primes_low[j:] exceed T.
                        br.n_prefiltered += (1 << (low_count - j)) - 1
                        break
                    run_D(np_, nm_)
                    rec(j + 1, np_, nm_)

            rec(0, base, high_global_mask)

    except Exception as e:
        br.n_errors += 1
        if len(br.error_samples) < 20:
            br.error_samples.append(f"block={high_mask}: {e!r}")
    finally:
        br.elapsed_sec = time.time() - t0
    return br


# ---------------------------------------------------------------------------
# Checkpoints
# ---------------------------------------------------------------------------

def _checkpoint_path(omega_dir: str, omega: int, H: int) -> str:
    # H is part of the checkpoint identity.  A completed high_mask has a
    # different meaning when H changes, so v6.1 deliberately does not reuse
    # v6.0 checkpoints or checkpoints from a different split.
    return os.path.join(omega_dir, f"lcm_v6_3_checkpoint_omega_{omega:02d}_H{H:02d}.json")


def _load_checkpoint(omega_dir: str, omega: int, H: int) -> Set[int]:
    cp = _checkpoint_path(omega_dir, omega, H)
    if not os.path.exists(cp):
        return set()
    try:
        with open(cp) as fh:
            data = json.load(fh)
        if int(data.get("H", -1)) != H or data.get("version") != PROGRAM_VERSION:
            return set()
        return set(int(x) for x in data.get("completed_high_masks", []))
    except Exception:
        return set()


def _save_checkpoint(omega_dir: str, omega: int, H: int, completed: Set[int]) -> None:
    cp = _checkpoint_path(omega_dir, omega, H)
    tmp = cp + ".tmp"
    with open(tmp, "w") as fh:
        json.dump({
            "program": PROGRAM_NAME,
            "version": PROGRAM_VERSION,
            "omega": omega,
            "H": H,
            "completed_high_masks": sorted(completed),
            "timestamp": utc_now_iso(),
        }, fh, indent=2)
    os.replace(tmp, cp)


# ---------------------------------------------------------------------------
# Summary structures / writers
# ---------------------------------------------------------------------------

@dataclass
class OmegaSummary:
    omega: int
    pmax: int
    L: int
    H: int
    block_log2: int
    n_blocks: int
    n_blocks_done: int
    n_discriminants_expected: int
    n_discriminants_run: int
    n_prefiltered: int
    n_cut_by_x: int
    n_gate_y1: int
    n_rank_missing: int
    n_rank_lcm_exceeds: int
    n_rank_survives: int
    n_rank_candidate_indices: int
    n_index_checked: int
    n_odd_x: int
    n_y_smooth_at_rank: int
    n_smooth_pairs: int
    hits_total: int
    hit_values: List[int]
    elapsed_sec: float
    verdict: str
    peak_rss_mb: float = 0.0
    blocks_per_sec: float = 0.0
    discriminants_per_sec: float = 0.0
    indices_per_sec: float = 0.0
    total_pell_sec: float = 0.0
    total_rank_sec: float = 0.0
    total_recurrence_sec: float = 0.0
    total_worker_elapsed_sec: float = 0.0
    n_errors: int = 0
    error_samples: List[str] = field(default_factory=list)
    self_test_ok: Optional[bool] = None
    self_test_detail: Optional[str] = None
    accounting_ok: bool = False
    hit_records: List[Dict[str, Any]] = field(default_factory=list)
    d_csv_sha256: Optional[str] = None
    hit_csv_sha256: Optional[str] = None
    slow_d_csv_sha256: Optional[str] = None
    slow_d_records: List[Dict[str, Any]] = field(default_factory=list)


def _write_d_csv_header(writer: csv.writer) -> None:
    writer.writerow([
        "omega", "D", "mask", "status", "x1_digits", "y1_digits",
        "y1_smooth", "rank_R", "rank_missing_prime", "rank_multiples",
        "j_checked", "smooth_pairs", "hits", "pell_sec", "total_sec", "error",
    ])


def _write_d_row(writer: csv.writer, omega: int, row: DRow) -> None:
    writer.writerow([
        omega, row.D, row.mask, row.status, row.x1_digits, row.y1_digits,
        "" if row.y1_smooth is None else int(bool(row.y1_smooth)),
        row.rank_R, row.rank_missing_prime, row.rank_multiples,
        row.j_checked, row.smooth_pairs,
        ";".join(str(x) for x in row.hits),
        f"{row.pell_sec:.6f}", f"{row.total_sec:.6f}", row.error,
    ])


def _slow_d_record(row: DRow) -> Dict[str, Any]:
    return {
        "D": row.D,
        "mask": row.mask,
        "status": row.status,
        "total_sec": round(row.total_sec, 6),
        "pell_sec": round(row.pell_sec, 6),
        "x1_digits": row.x1_digits,
        "y1_digits": row.y1_digits,
        "y1_smooth": row.y1_smooth,
        "rank_R": row.rank_R,
        "rank_missing_prime": row.rank_missing_prime,
        "rank_multiples": row.rank_multiples,
        "j_checked": row.j_checked,
        "smooth_pairs": row.smooth_pairs,
        "hits": list(row.hits),
        "error": row.error,
    }


def _write_slow_d_csv(path: str, omega: int, rows: List[DRow]) -> str:
    with open(path, "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow([
            "omega", "rank", "D", "mask", "status", "total_sec", "pell_sec",
            "x1_digits", "y1_digits", "y1_smooth", "rank_R",
            "rank_missing_prime", "rank_multiples", "j_checked",
            "smooth_pairs", "hits", "error",
        ])
        for i, row in enumerate(sorted(rows, key=lambda r: (r.total_sec, r.pell_sec), reverse=True), 1):
            w.writerow([
                omega, i, row.D, row.mask, row.status,
                f"{row.total_sec:.6f}", f"{row.pell_sec:.6f}",
                row.x1_digits, row.y1_digits,
                "" if row.y1_smooth is None else int(bool(row.y1_smooth)),
                row.rank_R, row.rank_missing_prime, row.rank_multiples,
                row.j_checked, row.smooth_pairs,
                ";".join(str(x) for x in row.hits), row.error,
            ])
    return sha256_file(path)


def _write_hit_csv(path: str, omega: int, hit_records: List[Dict[str, Any]]) -> str:
    with open(path, "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["omega", "m", "m_plus_1", "D", "mask", "j", "rank_R", "x_digits", "y_digits"])
        for rec in sorted(hit_records, key=lambda r: (r["m"], r["D"], r["j"])):
            w.writerow([
                omega, rec["m"], rec["m"] + 1, rec["D"], rec["mask"],
                rec["j"], rec.get("rank_R", ""), rec["x_digits"], rec["y_digits"],
            ])
    return sha256_file(path)


def _write_summary_json(omega_dir: str, s: OmegaSummary, args: argparse.Namespace) -> str:
    path = os.path.join(omega_dir, f"lcm_v6_summary_omega_{s.omega:02d}.json")
    data = {
        "program": PROGRAM_NAME,
        "version": PROGRAM_VERSION,
        "engine": "rank_lcm_recurrence",
        "omega": s.omega,
        "pmax": s.pmax,
        "L": s.L,
        "H": s.H,
        "block_log2": s.block_log2,
        "scheduler": args.scheduler,
        "min_blocks_per_worker": args.min_blocks_per_worker,
        "max_low_bits": args.max_low_bits,
        "n_blocks": s.n_blocks,
        "n_blocks_done": s.n_blocks_done,
        "n_discriminants_expected": s.n_discriminants_expected,
        "n_discriminants_run": s.n_discriminants_run,
        "n_prefiltered": s.n_prefiltered,
        "n_cut_by_x": s.n_cut_by_x,
        "n_gate_y1": s.n_gate_y1,
        "n_rank_missing": s.n_rank_missing,
        "n_rank_lcm_exceeds": s.n_rank_lcm_exceeds,
        "n_rank_survives": s.n_rank_survives,
        "n_rank_candidate_indices": s.n_rank_candidate_indices,
        "n_index_checked": s.n_index_checked,
        "n_odd_x": s.n_odd_x,
        "n_y_smooth_at_rank": s.n_y_smooth_at_rank,
        "n_smooth_pairs": s.n_smooth_pairs,
        "hits_total": s.hits_total,
        "hit_values": s.hit_values,
        "hit_records": s.hit_records,
        "slow_d_records": s.slow_d_records,
        "slow_d_limit": args.slow_d_limit,
        "slow_d_min_sec": args.slow_d_min_sec,
        "accounting_ok": s.accounting_ok,
        "verdict": s.verdict,
        "elapsed_sec": round(s.elapsed_sec, 3),
        "rates": {
            "blocks_per_sec": round(s.blocks_per_sec, 4),
            "discriminants_per_sec": round(s.discriminants_per_sec, 4),
            "indices_per_sec": round(s.indices_per_sec, 4),
        },
        "timing": {
            "total_pell_sec": round(s.total_pell_sec, 3),
            "total_rank_sec": round(getattr(s, "total_rank_sec", 0.0), 3),
            "total_recurrence_sec": round(s.total_recurrence_sec, 3),
            "total_worker_elapsed_sec": round(s.total_worker_elapsed_sec, 3),
        },
        "n_errors": s.n_errors,
        "error_samples": s.error_samples[:20],
        "self_test_ok": s.self_test_ok,
        "self_test_detail": s.self_test_detail,
        "d_csv_sha256": s.d_csv_sha256,
        "hit_csv_sha256": s.hit_csv_sha256,
        "slow_d_csv_sha256": s.slow_d_csv_sha256,
        "max_m": 0 if args.max_m_expo == 0 else 10 ** args.max_m_expo,
        "max_m_expo": args.max_m_expo,
        "cypari2_available": HAS_CYPARI2,
        "gmpy2_available": HAS_GMPY2,
        "gp_path": args.gp_path,
        "workers": args.workers,
        "scheduler": args.scheduler,
        "min_blocks_per_worker": args.min_blocks_per_worker,
        "max_low_bits": args.max_low_bits,
        "peak_rss_mb": round(s.peak_rss_mb, 2),
        "timestamp": utc_now_iso(),
        "python_version": sys.version.replace("\n", " "),
        "platform": platform.platform(),
    }
    with open(path, "w") as fh:
        json.dump(data, fh, indent=2)
    return path


# ---------------------------------------------------------------------------
# Self-test / regression gate
# ---------------------------------------------------------------------------

def _scan_known_pairs_single_process(omega: int, gp_path: str, L: int,
                                    max_m: int = 0) -> Tuple[Set[int], List[str]]:
    """Small-omega single-process recurrence scan used by regression gate."""
    primes = tuple(first_n_primes(omega))
    _worker_init(primes, gp_path, max_m, L, H=0, emit_d_rows=False, quiet_pari=True,
                 slow_d_limit=0, slow_d_min_sec=0.0)
    br_total = BlockResult(high_mask=0)
    errors: List[str] = []
    for mask in range(1, 1 << omega):
        D = D_from_mask(mask, primes)
        br = BlockResult(high_mask=0)
        _process_D_recurrence(D, mask, br)
        br_total.hit_values.extend(br.hit_values)
        if br.error_samples:
            errors.extend(br.error_samples)
    _gp_kill()
    return set(br_total.hit_values), errors


def self_test_known_pairs(omega: int, gp_path: str, L: int,
                          verbose: bool = True) -> Tuple[bool, str]:
    expected = set(KNOWN_PRIME_COMPLETE.get(omega, []))
    if not expected:
        return True, f"no known pairs catalogued at omega={omega}; gate vacuous"
    found, errors = _scan_known_pairs_single_process(omega, gp_path, L)
    missing = expected - found
    extra = found - expected
    ok = (not missing) and (not errors)
    detail = (f"expected={sorted(expected)} found={sorted(found)} "
              f"missing={sorted(missing)} extra={sorted(extra)} "
              f"errors={errors[:3]}")
    if verbose:
        print(f" [self_test omega={omega}] {'PASS' if ok else 'FAIL'}: {detail}")
    return ok, detail


# ---------------------------------------------------------------------------
# run_omega
# ---------------------------------------------------------------------------

def run_omega(args: argparse.Namespace, omega: int, run_self_test: bool) -> OmegaSummary:
    t_start = time.time()
    primes = tuple(first_n_primes(omega))
    pmax = primes[-1]
    L_index = args.L_override if args.L_override > 0 else proven_L(pmax)
    if args.mode == "certify" and args.L_override > 0 and args.L_override < proven_L(pmax):
        raise RuntimeError(
            f"certify mode refuses L_override={args.L_override}; proven L is {proven_L(pmax)}"
        )

    H = choose_high_bits(
        omega, args.block_log2, args.workers,
        min_blocks_per_worker=args.min_blocks_per_worker,
        max_low_bits=args.max_low_bits,
    )
    n_mask_space = 1 << H
    n_expected = (1 << omega) - 1
    # If H == omega, each nonempty high_mask is one global D-mask task.
    # The empty mask is not a valid discriminant and is not scheduled.
    all_task_ids = list(range(1, n_mask_space)) if H == omega else list(range(n_mask_space))
    n_blocks = len(all_task_ids)
    max_m = 0 if args.max_m_expo == 0 else 10 ** args.max_m_expo

    omega_dir = os.path.join(args.outdir, f"omega_{omega:02d}")
    ensure_dir(omega_dir)

    self_test_ok: Optional[bool] = None
    self_test_detail: Optional[str] = None
    if run_self_test:
        self_test_ok, self_test_detail = self_test_known_pairs(
            omega, args.gp_path, L_index, verbose=True
        )
        if args.mode == "certify" and not self_test_ok:
            raise RuntimeError(f"SELF-TEST FAILED at omega={omega}: {self_test_detail}")

    completed: Set[int] = _load_checkpoint(omega_dir, omega, H) if not args.no_checkpoint else set()
    valid_task_id_set = set(all_task_ids)
    completed &= valid_task_id_set
    block_ids = [hm for hm in all_task_ids if hm not in completed]
    low_count_for_schedule = omega - H
    primes_high_for_schedule = primes[low_count_for_schedule:]
    if args.scheduler == "hard_first":
        block_ids.sort(key=lambda hm: high_mask_sort_key(hm, primes_high_for_schedule), reverse=True)
    elif args.scheduler == "light_first":
        block_ids.sort(key=lambda hm: high_mask_sort_key(hm, primes_high_for_schedule))

    emit_d_rows = (args.d_csv_cutoff == 0 or omega <= args.d_csv_cutoff)
    d_csv_path = os.path.join(omega_dir, f"lcm_v6_D_audit_omega_{omega:02d}.csv") if emit_d_rows else os.devnull
    hit_csv_path = os.path.join(omega_dir, f"lcm_v6_hits_omega_{omega:02d}.csv")
    slow_d_csv_path = os.path.join(omega_dir, f"lcm_v6_slow_D_omega_{omega:02d}.csv") if args.slow_d_limit > 0 else None

    d_fh = open(d_csv_path, "w", newline="")
    d_writer = csv.writer(d_fh)
    if emit_d_rows:
        _write_d_csv_header(d_writer)

    print(
        f"\n[LCm v{PROGRAM_VERSION}] omega={omega} primes={list(primes)} pmax={pmax} L={L_index} "
        f"mode={args.mode} workers={args.workers} H={H} low_bits={omega - H} "
        f"blocks={len(block_ids)}/{n_blocks} block_log2={args.block_log2} "
        f"scheduler={args.scheduler} d_csv={'on' if emit_d_rows else 'off'}"
    )
    if completed:
        print(f" [checkpoint] Resuming with {len(completed)} completed high-mask blocks.")

    totals = BlockResult(high_mask=-1)
    hit_set: Set[int] = set()
    completed_now: Set[int] = set(completed)
    last_progress = time.time()
    checkpoint_interval = max(1, len(block_ids) // 20) if block_ids else 1

    def merge(br: BlockResult) -> None:
        totals.n_d_run += br.n_d_run
        totals.n_prefiltered += br.n_prefiltered
        totals.n_cut_by_x += br.n_cut_by_x
        totals.n_gate_y1 += br.n_gate_y1
        totals.n_rank_missing += br.n_rank_missing
        totals.n_rank_lcm_exceeds += br.n_rank_lcm_exceeds
        totals.n_rank_survives += br.n_rank_survives
        totals.n_rank_candidate_indices += br.n_rank_candidate_indices
        totals.n_index_checked += br.n_index_checked
        totals.n_odd_x += br.n_odd_x
        totals.n_y_smooth_at_rank += br.n_y_smooth_at_rank
        totals.n_smooth_pairs += br.n_smooth_pairs
        totals.n_hit_discriminants += br.n_hit_discriminants
        totals.n_errors += br.n_errors
        totals.pell_sec += br.pell_sec
        totals.rank_sec += br.rank_sec
        totals.recurrence_sec += br.recurrence_sec
        totals.elapsed_sec += br.elapsed_sec
        if br.error_samples:
            totals.error_samples.extend(br.error_samples[:max(0, 20 - len(totals.error_samples))])
        if br.hit_values:
            totals.hit_values.extend(br.hit_values)
            hit_set.update(br.hit_values)
        if br.hit_records:
            totals.hit_records.extend(br.hit_records)
        if br.slow_d_rows and args.slow_d_limit > 0:
            totals.slow_d_rows.extend(br.slow_d_rows)
            totals.slow_d_rows.sort(key=lambda r: (r.total_sec, r.pell_sec), reverse=True)
            del totals.slow_d_rows[args.slow_d_limit:]
        if emit_d_rows:
            for row in br.d_rows:
                _write_d_row(d_writer, omega, row)

    if args.workers <= 1:
        _worker_init(primes, args.gp_path, max_m, L_index, H, emit_d_rows, quiet_pari=False,
                     slow_d_limit=args.slow_d_limit, slow_d_min_sec=args.slow_d_min_sec)
        for done_count, hm in enumerate(block_ids, 1):
            br = _solver_block(hm)
            merge(br)
            completed_now.add(hm)
            if (not args.no_checkpoint) and (done_count % checkpoint_interval == 0):
                d_fh.flush()
                _save_checkpoint(omega_dir, omega, H, completed_now)
            now = time.time()
            if args.progress_interval > 0 and now - last_progress >= args.progress_interval:
                print(
                    f"  blocks={done_count:,}/{len(block_ids):,} D_run={totals.n_d_run:,} "
                    f"gate_y1={totals.n_gate_y1:,} rank_dead={totals.n_rank_missing + totals.n_rank_lcm_exceeds:,} j_checked={totals.n_index_checked:,} "
                    f"hits={len(hit_set)} elapsed={(now - t_start) / 60:.1f}min",
                    flush=True,
                )
                last_progress = now
        _gp_kill()
    else:
        ctx = mp.get_context("fork") if sys.platform == "darwin" else mp.get_context()
        with ctx.Pool(
            processes=args.workers,
            initializer=_worker_init,
            initargs=(primes, args.gp_path, max_m, L_index, H, emit_d_rows, False,
                      args.slow_d_limit, args.slow_d_min_sec),
        ) as pool:
            for done_count, br in enumerate(pool.imap_unordered(_solver_block, block_ids, chunksize=1), 1):
                merge(br)
                completed_now.add(br.high_mask)
                if (not args.no_checkpoint) and (done_count % checkpoint_interval == 0):
                    d_fh.flush()
                    _save_checkpoint(omega_dir, omega, H, completed_now)
                now = time.time()
                if args.progress_interval > 0 and now - last_progress >= args.progress_interval:
                    print(
                        f"  blocks={done_count:,}/{len(block_ids):,} D_run={totals.n_d_run:,} "
                        f"gate_y1={totals.n_gate_y1:,} rank_dead={totals.n_rank_missing + totals.n_rank_lcm_exceeds:,} j_checked={totals.n_index_checked:,} "
                        f"hits={len(hit_set)} elapsed={(now - t_start) / 60:.1f}min",
                        flush=True,
                    )
                    last_progress = now

    d_fh.close()
    if not args.no_checkpoint:
        _save_checkpoint(omega_dir, omega, H, completed_now)

    elapsed = time.time() - t_start
    d_csv_sha = sha256_file(d_csv_path) if emit_d_rows else None
    hit_csv_sha = _write_hit_csv(hit_csv_path, omega, totals.hit_records)
    slow_d_csv_sha = None
    if slow_d_csv_path is not None:
        slow_d_csv_sha = _write_slow_d_csv(slow_d_csv_path, omega, totals.slow_d_rows)

    accounting_ok = (totals.n_d_run + totals.n_prefiltered == n_expected) and (len(completed_now) == n_blocks)
    hit_values = sorted(hit_set)
    hits_total = len(hit_values)

    if totals.n_errors:
        verdict = "INCOMPLETE_ERRORS"
    elif not accounting_ok:
        verdict = "INCOMPLETE_ACCOUNTING"
    elif hits_total:
        verdict = "COMPLETE_WITH_HITS"
    else:
        verdict = "COMPLETE_NO_HITS"

    summary = OmegaSummary(
        omega=omega,
        pmax=pmax,
        L=L_index,
        H=H,
        block_log2=args.block_log2,
        n_blocks=n_blocks,
        n_blocks_done=len(completed_now),
        n_discriminants_expected=n_expected,
        n_discriminants_run=totals.n_d_run,
        n_prefiltered=totals.n_prefiltered,
        n_cut_by_x=totals.n_cut_by_x,
        n_gate_y1=totals.n_gate_y1,
        n_rank_missing=totals.n_rank_missing,
        n_rank_lcm_exceeds=totals.n_rank_lcm_exceeds,
        n_rank_survives=totals.n_rank_survives,
        n_rank_candidate_indices=totals.n_rank_candidate_indices,
        n_index_checked=totals.n_index_checked,
        n_odd_x=totals.n_odd_x,
        n_y_smooth_at_rank=totals.n_y_smooth_at_rank,
        n_smooth_pairs=totals.n_smooth_pairs,
        hits_total=hits_total,
        hit_values=hit_values,
        elapsed_sec=elapsed,
        verdict=verdict,
        peak_rss_mb=peak_rss_mb(),
        blocks_per_sec=len(block_ids) / elapsed if elapsed > 0 else 0.0,
        discriminants_per_sec=totals.n_d_run / elapsed if elapsed > 0 else 0.0,
        indices_per_sec=totals.n_index_checked / elapsed if elapsed > 0 else 0.0,
        total_pell_sec=totals.pell_sec,
        total_rank_sec=totals.rank_sec,
        total_recurrence_sec=totals.recurrence_sec,
        total_worker_elapsed_sec=totals.elapsed_sec,
        n_errors=totals.n_errors,
        error_samples=totals.error_samples[:20],
        self_test_ok=self_test_ok,
        self_test_detail=self_test_detail,
        accounting_ok=accounting_ok,
        hit_records=sorted(totals.hit_records, key=lambda r: (r["m"], r["D"], r["j"])),
        d_csv_sha256=d_csv_sha,
        hit_csv_sha256=hit_csv_sha,
        slow_d_csv_sha256=slow_d_csv_sha,
        slow_d_records=[_slow_d_record(r) for r in sorted(totals.slow_d_rows, key=lambda r: (r.total_sec, r.pell_sec), reverse=True)],
    )

    summary_path = _write_summary_json(omega_dir, summary, args)

    print(
        f" verdict={verdict} accounting_ok={accounting_ok} "
        f"D_run={totals.n_d_run:,}/{n_expected:,} prefiltered={totals.n_prefiltered:,} "
        f"gate_y1={totals.n_gate_y1:,} rank_dead={totals.n_rank_missing + totals.n_rank_lcm_exceeds:,} j_checked={totals.n_index_checked:,} "
        f"smooth_pairs={totals.n_smooth_pairs:,} hits={hits_total}"
    )
    print(
        f" elapsed={elapsed:.1f}s D/s={summary.discriminants_per_sec:.2f} "
        f"j/s={summary.indices_per_sec:.2f} peak_rss={summary.peak_rss_mb:.1f}MB "
        f"pell_worker_sec={summary.total_pell_sec:.1f} rank_worker_sec={summary.total_rank_sec:.1f} "
        f"rec_worker_sec={summary.total_recurrence_sec:.1f}"
    )
    if hit_values:
        print(f" HIT VALUES: {hit_values}")
    if totals.error_samples:
        print(f" ERROR SAMPLES: {totals.error_samples[:3]}")
    print(f" summary --> {summary_path}")
    if emit_d_rows:
        print(f" D audit --> {d_csv_path}")
    if slow_d_csv_path is not None:
        print(f" slow-D audit --> {slow_d_csv_path}")
    print(f" hits --> {hit_csv_path}")

    return summary


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    ap = argparse.ArgumentParser(
        prog="LCm_Solver",
        description="Lehmer-Clements prime-complete enumerator v6 rank-LCM recurrence engine.",
    )
    ap.add_argument("--mode", choices=["certify", "search"], default="search")
    ap.add_argument("--start_omega", type=int, default=2)
    ap.add_argument("--end_omega", type=int, default=9)
    ap.add_argument("--outdir", default="lc_audit_v6")
    ap.add_argument("--gp_path", default="gp")
    ap.add_argument("--workers", type=int, default=max(1, os.cpu_count() or 1))
    ap.add_argument("--max_m_expo", type=int, default=0,
                    help="If >0, cap search to m <= 10^expo. Certify mode refuses caps.")
    ap.add_argument("--L_override", type=int, default=0,
                    help="Override index ceiling L. Certify mode refuses values below proven L.")
    ap.add_argument("--block_log2", type=int, default=8,
                    help="Target log2 low-prime subsets per worker block before load-balance caps. v6.1 default is smaller than v6.0 to reduce tail latency.")
    ap.add_argument("--min_blocks_per_worker", type=int, default=64,
                    help="Load-balance floor: choose H so there are at least this many blocks per worker when possible.")
    ap.add_argument("--max_low_bits", type=int, default=0,
                    help="Load-balance cap. 0 means H=omega and schedules exactly one nonempty discriminant mask per task. 1 gives v6.2-style one-or-two-D microblocks.")
    ap.add_argument("--scheduler", choices=["hard_first", "natural", "light_first"], default="hard_first",
                    help="Order high-mask blocks. hard_first submits large/high-popcount blocks first to prevent tail stalls.")
    ap.add_argument("--d_csv_cutoff", type=int, default=20,
                    help="If 0 or omega<=cutoff, write one-row-per-D audit CSV; otherwise suppress it.")
    ap.add_argument("--progress_interval", type=float, default=30.0,
                    help="Seconds between progress lines; 0 disables progress lines.")
    ap.add_argument("--slow_d_limit", type=int, default=50,
                    help="Keep this many slowest discriminants in a separate slow-D audit CSV and summary JSON. Use 0 to disable.")
    ap.add_argument("--slow_d_min_sec", type=float, default=0.0,
                    help="Minimum per-D elapsed seconds required for inclusion in the slow-D audit.")
    ap.add_argument("--no_self_test", action="store_true",
                    help="Skip known-pair regression gate. Not recommended for certificates.")
    ap.add_argument("--self_test_only", action="store_true",
                    help="Run only the known-pair regression gate over the omega range.")
    ap.add_argument("--no_checkpoint", action="store_true")
    ap.add_argument("--version", action="store_true")
    args = ap.parse_args()

    if args.version:
        print(json.dumps({
            "program": PROGRAM_NAME,
            "version": PROGRAM_VERSION,
            "cypari2_available": HAS_CYPARI2,
            "gmpy2_available": HAS_GMPY2,
            "timestamp": utc_now_iso(),
        }, indent=2))
        return

    if args.start_omega < 1 or args.end_omega < args.start_omega:
        print("ERROR: invalid omega range")
        sys.exit(1)
    if args.mode == "certify" and args.max_m_expo > 0:
        print("ERROR: certify mode refuses --max_m_expo > 0.")
        sys.exit(1)
    if args.block_log2 < 1:
        print("ERROR: --block_log2 must be >= 1")
        sys.exit(1)
    if args.min_blocks_per_worker < 1:
        print("ERROR: --min_blocks_per_worker must be >= 1")
        sys.exit(1)
    if args.max_low_bits < 0:
        print("ERROR: --max_low_bits must be >= 0")
        sys.exit(1)
    if args.slow_d_limit < 0:
        print("ERROR: --slow_d_limit must be >= 0")
        sys.exit(1)
    if args.slow_d_min_sec < 0:
        print("ERROR: --slow_d_min_sec must be >= 0")
        sys.exit(1)

    ensure_dir(args.outdir)

    print(f"{PROGRAM_NAME} v{PROGRAM_VERSION} rank-LCM recurrence engine")
    print(
        f"Mode: {args.mode} omega: {args.start_omega}..{args.end_omega} "
        f"outdir: {args.outdir} gp: {args.gp_path} workers: {args.workers} "
        f"scheduler: {args.scheduler} min_blocks_per_worker: {args.min_blocks_per_worker} max_low_bits: {args.max_low_bits} "
        f"slow_d_limit: {args.slow_d_limit} slow_d_min_sec: {args.slow_d_min_sec} "
        f"self_test: {not args.no_self_test} checkpoint: {not args.no_checkpoint} "
        f"cypari2: {HAS_CYPARI2} gmpy2: {HAS_GMPY2}"
    )

    if args.self_test_only:
        all_ok = True
        for omega in range(args.start_omega, args.end_omega + 1):
            pmax = first_n_primes(omega)[-1]
            L = args.L_override if args.L_override > 0 else proven_L(pmax)
            ok, _detail = self_test_known_pairs(omega, args.gp_path, L, verbose=True)
            all_ok = all_ok and ok
        print("\n" + "=" * 60)
        print(f"SELF-TEST RESULT: {'ALL PASS' if all_ok else 'FAILURES PRESENT'}")
        print("=" * 60)
        sys.exit(0 if all_ok else 1)

    # Full-catalogue gate for certificates.  Above omega=8 the per-omega known
    # catalogue is vacuous, so run all known levels before any certificate range.
    full_gate_ok = True
    if args.mode == "certify" and not args.no_self_test:
        print("\n[gate] Full known-pair catalogue self-test (omega <= 8):")
        for o in sorted(KNOWN_PRIME_COMPLETE):
            pmax_o = first_n_primes(o)[-1]
            L_o = args.L_override if args.L_override > 0 else proven_L(pmax_o)
            ok, _detail = self_test_known_pairs(o, args.gp_path, L_o, verbose=True)
            full_gate_ok = full_gate_ok and ok
        if not full_gate_ok:
            print("ERROR: full-catalogue gate FAILED; refusing certificate run.")
            sys.exit(1)
        print("[gate] PASS -- all 28 known prime-complete pairs recovered.\n")

    summaries: List[OmegaSummary] = []
    any_hit = False
    any_errors = False
    for omega in range(args.start_omega, args.end_omega + 1):
        s = run_omega(
            args,
            omega,
            run_self_test=(not args.no_self_test) and args.mode != "certify",
        )
        summaries.append(s)
        any_hit = any_hit or bool(s.hits_total)
        any_errors = any_errors or bool(s.n_errors or not s.accounting_ok)

    master_path = os.path.join(args.outdir, "lcm_v6_master_summary.json")
    master = {
        "program": PROGRAM_NAME,
        "version": PROGRAM_VERSION,
        "engine": "rank_lcm_recurrence",
        "mode": args.mode,
        "start_omega": args.start_omega,
        "end_omega": args.end_omega,
        "workers": args.workers,
        "block_log2": args.block_log2,
        "scheduler": args.scheduler,
        "min_blocks_per_worker": args.min_blocks_per_worker,
        "max_low_bits": args.max_low_bits,
        "any_prime_complete_hit": any_hit,
        "any_errors_or_incomplete": any_errors,
        "full_catalogue_gate_ok": full_gate_ok,
        "per_omega": [
            {
                "omega": s.omega,
                "pmax": s.pmax,
                "L": s.L,
                "H": s.H,
                "n_blocks": s.n_blocks,
                "n_discriminants_run": s.n_discriminants_run,
                "n_prefiltered": s.n_prefiltered,
                "n_gate_y1": s.n_gate_y1,
                "n_rank_missing": s.n_rank_missing,
                "n_rank_lcm_exceeds": s.n_rank_lcm_exceeds,
                "n_rank_survives": s.n_rank_survives,
                "n_rank_candidate_indices": s.n_rank_candidate_indices,
                "n_index_checked": s.n_index_checked,
                "n_y_smooth_at_rank": s.n_y_smooth_at_rank,
                "n_smooth_pairs": s.n_smooth_pairs,
                "hits_total": s.hits_total,
                "hit_values": s.hit_values,
                "verdict": s.verdict,
                "accounting_ok": s.accounting_ok,
                "n_errors": s.n_errors,
                "elapsed_sec": round(s.elapsed_sec, 3),
            }
            for s in summaries
        ],
        "timestamp": utc_now_iso(),
    }
    with open(master_path, "w") as fh:
        json.dump(master, fh, indent=2)

    print("\n" + "=" * 60)
    print(f"MASTER RESULT: any_prime_complete_hit = {any_hit}")
    if any_errors:
        print("WARNING: errors or incomplete accounting occurred; see per-omega summaries.")
    if not any_hit and not any_errors:
        print(
            "No prime-complete hits found in the requested omega range by the "
            "rank-LCM recurrence engine, conditional on the stated index ceiling L."
        )
    elif any_hit:
        print("Prime-complete hits found -- see per-omega summaries / hit CSVs.")
    print(f"Master summary --> {master_path}")
    print("=" * 60)


if __name__ == "__main__":
    atexit.register(_gp_kill)
    main()
