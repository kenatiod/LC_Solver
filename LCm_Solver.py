#!/usr/bin/env python3
# LCm_Solver.py version 4.0

"""
LCm_Solver — Lehmer-Clements prime-complete enumerator, multiprocessing edition.

================================================================================
VERSION 4.0  (June 2026) — VEIN-SPACE CORRECTION
================================================================================
v3.1 enumerated only veins of the form D = 2*q (q a product of odd census
primes), i.e. it forced the Pell discriminant to be EVEN.  That is unsound:
the correct discriminant of a consecutive pair is the squarefree kernel
D = sf(m(m+1)) (Step-0 Normalization Lemma), which is ODD whenever 2 divides
the even member to an even power.  Eleven of the 28 known prime-complete pairs
have an ODD kernel — including the last pair m = 633555 (D = 255255), which is
the fundamental solution of its (odd) vein.  v3.1 could not represent any of
them, so a "no prime-complete pair" verdict from v3.1 was structurally blind to
exactly the hits the proof concerns.

v4.0 enumerates the FULL correct vein space and matches the Step-0 lemmas:

  C1. VEIN SPACE.  D ranges over every squarefree divisor of P_omega with
      D > 1, of EITHER parity.  A mask is a nonempty subset of ALL omega
      census primes {p_1=2, ..., p_omega}; D = product of the masked primes.
      (No D = 2q restriction; no q=2 special-casing.)

  C2. SIGMA DOMAIN = sigma_U.  The side assignment is enumerated ONLY over the
      unramified odd census primes
          U(D, omega) = { p <= p_omega : p does not divide D, p != 2 }.
      Ramified primes (p | D) and p = 2 impose NO index congruence: they divide
      m(m+1) automatically (p | D => p | m; 2 | m(m+1) always for consecutive
      integers).  Their side is read off after the fact, never chosen.  This is
      exactly sigma_U of the Step-0 canonicalization note.

  C3. ODD WHEEL ORDER => SIDE B UNAVAILABLE.  For an unramified odd p, side A
      is hit iff w_p | j and side B iff w_p even and j == w_p/2 (mod w_p).  If
      w_p is odd, side B is unrealizable; any sigma_U asking side B at such a p
      yields a DECLARED-EMPTY system (EXCLUDED_EMPTY).  This falls out of the
      seat-set intersection automatically (the B side-set is empty).

  C4. PROVEN INDEX CEILING.  L(omega) defaults to the unconditional
      max(30, p_omega + 1) (primitive-divisor / Lehmer ceiling, Cor 3.13 of the
      Step-0 note).  Overridable with --L_override for experiments, but a
      certificate run must use a value at least the proven ceiling.  A solvable
      seat system whose minimal in-range index exceeds L is EXCLUDED_LAMBDA;
      under the proven ceiling this is a sound exclusion (no prime-complete pair
      from that (D, sigma_U) can exist below the ceiling, hence none at all).

  C5. KNOWN-PAIR REGRESSION GATE.  Before any certify run is trusted, the
      enumerator is self-tested: every known prime-complete pair at the target
      omega level MUST be representable and recovered by the corrected pipeline.
      Run with --self_test (or it runs automatically at the start of certify
      mode) and aborts if any known pair is missed.  This is precisely the check
      that would have caught the v3.1 bug.

Mathematical core (unchanged identities)
----------------------------------------
With x^2 - D*y^2 = 1, D squarefree > 1, x odd: m = (x-1)/2, m+1 = (x+1)/2,
m(m+1) = D*z^2 with y = 2z.  m, m+1 are P_omega-smooth and the pair is
prime-complete at level omega iff rad(m(m+1)) = P_omega, i.e. every census
prime divides m(m+1).  Seat conditions (Seat Lemma): for unramified odd p,
p | m  <=>  x_j == +1 (mod p)  (side A);  p | m+1  <=>  x_j == -1 (mod p)
(side B).

Parallelism, PARI/GP interface, checkpointing, status protocol, and the
JSON/CSV output schema are inherited from v3.1.

By Ken Clements, with Claude (Anthropic), June 2026.
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
import concurrent.futures
from collections import defaultdict
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Dict, List, Optional, Set, Tuple, Any

try:
    sys.set_int_max_str_digits(0)
except Exception:
    pass

program_name, program_version = "LCm_Solver", 4.0

# ---------------------------------------------------------------------------
# Known prime-complete pairs (m values), keyed by level omega.
# Used by the regression gate (C5) and as ground truth in self-test.
# These are the consecutive-integer prime-complete records; each is the unique
# representative of its level except where the level repeats (none do here).
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

def gcd(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return a

def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b

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

def support_tuple(f: Dict[int, int]) -> Tuple[int, ...]:
    return tuple(sorted(f.keys()))

def D_from_mask(mask: int, primes: Tuple[int, ...]) -> int:
    """Vein discriminant: product of ALL masked census primes (C1)."""
    D, tmp, i = 1, mask, 0
    while tmp:
        if tmp & 1:
            D *= primes[i]
        tmp >>= 1
        i += 1
    return D

def primes_in_mask(mask: int, primes: Tuple[int, ...]) -> List[int]:
    result, tmp, i = [], mask, 0
    while tmp:
        if tmp & 1:
            result.append(primes[i])
        tmp >>= 1
        i += 1
    return result

def unramified_odd_primes(D: int, primes: Tuple[int, ...]) -> List[int]:
    """U(D, omega) = { p <= p_omega : p does not divide D, p != 2 } (C2)."""
    return [p for p in primes if p != 2 and D % p != 0]

def proven_L(pmax: int) -> int:
    """Unconditional index ceiling max(30, p_omega + 1) (C4, Cor 3.13)."""
    return max(30, pmax + 1)

def peak_rss_mb() -> float:
    try:
        ru = resource.getrusage(resource.RUSAGE_SELF)
        if platform.system() == "Darwin":
            return ru.ru_maxrss / (1024 * 1024)
        else:
            return ru.ru_maxrss / 1024
    except Exception:
        return 0.0

# ---------------------------------------------------------------------------
# Fast-doubling Pell exponentiation
# ---------------------------------------------------------------------------

def pell_power(x1: int, y1: int, D: int, n: int) -> Tuple[int, int]:
    if n == 0:
        return 1, 0
    xr, yr = 1, 0
    xb, yb = x1, y1
    while n:
        if n & 1:
            xr, yr = xr * xb + D * yr * yb, xr * yb + yr * xb
        xb, yb = xb * xb + D * yb * yb, 2 * xb * yb
        n >>= 1
    return xr, yr

# ---------------------------------------------------------------------------
# PARI/GP interface
# ---------------------------------------------------------------------------

_PELLXY_GP = r"""
pellxy_cf(D,mx=0)={
my(a0=sqrtint(D),m=0,d=1,a=a0,p0=1,p1=a0,q0=0,q1=1);
while(p1^2-D*q1^2!=1,
m=d*a-m;d=(D-m^2)/d;a=(a0+m)\d;
my(p2=a*p1+p0,q2=a*q1+q0);p0=p1;p1=p2;q0=q1;q1=q2;
if(mx>0&&p1>mx,return([0,0])));[p1,q1]};
pellxy(D,mx=0)={
if(D<=0,error("D<=0"));
if(issquare(D),error("square"));
my(F=factor(D),P=F[,1],E=F[,2],d=1,s=1);
for(i=1,#P,my(e=E[i]);if(e%2,d*=P[i]);s*=P[i]^(e\2));
my(v=pellxy_cf(d,mx));if(v==[0,0],return([0,0]));
my(a=v[1],b=v[2]);
if(s==1,return([a,b]));
my(a1=a,b1=b);
while(b%s,my(aa=a1*a+d*b1*b,bb=a1*b+b1*a);a=aa;b=bb;
if(mx>0&&a>mx,return([0,0])));
my(y=b/s);
if(a^2-D*y^2!=1,error("check failed"));
[a,y]};
"""

_BEGIN = "__BEGIN__"
_END = "__END__"
_VEC2_RE = re.compile(r"^\[\s*(-?\d+)\s*,\s*(-?\d+)\s*\]\s*$")

_gp_proc: Optional[subprocess.Popen] = None
_gp_path: str = "gp"

def _gp_kill() -> None:
    global _gp_proc
    if _gp_proc is not None:
        try:
            _gp_proc.kill()
        except Exception:
            pass
    _gp_proc = None

def _gp_start() -> subprocess.Popen:
    p = subprocess.Popen(
        [_gp_path, "-q"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )
    assert p.stdin and p.stdout
    p.stdin.write(_PELLXY_GP + "\n")
    p.stdin.write(f'print("{_BEGIN}");\n')
    p.stdin.write("v=pellxy(46);print(v);print(v[1]^2-46*v[2]^2);\n")
    p.stdin.write("vb=pellxy(46,100);print(vb);\n")
    p.stdin.write(f'print("{_END}");\n')
    p.stdin.flush()

    buf, in_block = [], False
    while True:
        line = p.stdout.readline()
        if not line:
            raise RuntimeError("gp handshake EOF")
        s = line.strip()
        if s == _BEGIN:
            in_block = True
            continue
        if s == _END:
            break
        if in_block:
            buf.append(s)

    assert len(buf) >= 3, f"Unexpected GP handshake output: {buf}"
    assert buf[1] == "1", f"Pell self-test failed: {buf}"
    assert buf[2] == "[0, 0]", f"Bailout self-test failed: {buf}"
    return p

def _gp_eval(expr: str, retries: int = 2, timeout: float = 300.0) -> str:
    global _gp_proc
    for attempt in range(retries + 1):
        try:
            if _gp_proc is None:
                _gp_proc = _gp_start()
            p = _gp_proc
            assert p.stdin and p.stdout

            p.stdin.write(f'print("{_BEGIN}");\n{expr}\nprint("{_END}");\n')
            p.stdin.flush()

            def read_until_end() -> List[str]:
                collected: List[str] = []
                inside = False
                while True:
                    line = p.stdout.readline()
                    if not line:
                        raise RuntimeError("gp EOF")
                    s = line.strip()
                    if s == _BEGIN:
                        inside = True
                        continue
                    if s == _END:
                        return collected
                    if inside:
                        collected.append(s)

            with concurrent.futures.ThreadPoolExecutor(max_workers=1) as ex:
                future = ex.submit(read_until_end)
                try:
                    parts = future.result(timeout=timeout)
                except concurrent.futures.TimeoutError:
                    _gp_kill()
                    raise TimeoutError(f"gp timeout {timeout}s")

            return "\n".join(parts)

        except TimeoutError:
            _gp_kill()
            if attempt == retries:
                raise
        except Exception:
            _gp_kill()
            if attempt == retries:
                raise

    raise RuntimeError("unreachable in _gp_eval")

def _pell_xy_gp(D: int, max_x: int = 0, timeout: float = 300.0) -> Tuple[int, int]:
    arg = f", {max_x}" if max_x > 0 else ""
    raw = _gp_eval(f"print(pellxy({D}{arg}));", timeout=timeout).strip().splitlines()[-1]
    m = _VEC2_RE.match(raw)
    if not m:
        raise ValueError(f"Unexpected GP output: {raw!r}")
    return int(m.group(1)), int(m.group(2))

# ---------------------------------------------------------------------------
# Core data structures
# ---------------------------------------------------------------------------

@dataclass
class MaskResult:
    mask: int
    D: int
    excluded_empty: int
    excluded_lambda: int
    hits: int
    open_count: int
    hit_ms: List[int]
    cert_rows: List[Dict[str, Any]]
    elapsed_sec: float
    gp_elapsed_sec: float = 0.0
    excl_empty_by_prime: Dict[int, int] = field(default_factory=dict)
    lambda_combined_vals: List[int] = field(default_factory=list)
    worker_pid: int = 0

def _compute_period(state_seq: List[Tuple[int, int]]) -> int:
    """True period of the Pell sequence mod p on the (x, y) state."""
    target = state_seq[0]
    for t in range(1, len(state_seq)):
        if state_seq[t] == target:
            return t
    return len(state_seq)

def process_mask(
    omega: int,
    mask: int,
    primes: Tuple[int, ...],
    L: int,
    x1: int,
    y1: int,
    mode: str,
    gp_elapsed: float = 0.0,
) -> MaskResult:
    """
    Enumerate the seat systems for one vein D = D_from_mask(mask).

    sigma ranges over sigma_U: the unramified odd census primes (C2).
    Ramified primes (p | D) and p = 2 are NOT in sigma_U; they divide m(m+1)
    automatically and impose no index congruence.  An odd wheel order makes the
    B side-set empty, so a sigma_U requesting side B there is EXCLUDED_EMPTY (C3).
    """
    t0 = time.time()
    D = D_from_mask(mask, primes)
    U = unramified_odd_primes(D, primes)   # sigma_U domain (C2)
    k = len(U)

    # Pell sequence mod p for each unramified odd prime; detect period (wheel order).
    pell_seq_mod: Dict[int, List[int]] = {}
    period_by_prime: Dict[int, int] = {}
    for p in U:
        x1p, y1p, Dp = x1 % p, y1 % p, D % p
        xj, yj = x1p, y1p
        seq: List[int] = []
        states: List[Tuple[int, int]] = []
        for _ in range(L):
            seq.append(xj)
            states.append((xj, yj))
            nxj = (x1p * xj + Dp * y1p * yj) % p
            nyj = (x1p * yj + y1p * xj) % p
            xj, yj = nxj, nyj
        pell_seq_mod[p] = seq
        period_by_prime[p] = _compute_period(states)

    # Seat sets, over j = 1..L.  s0 = side A (x == +1), s1 = side B (x == -1).
    # If s1 is empty for some p, that p has odd wheel order: side B unavailable (C3).
    side_sets: Dict[int, Tuple[Set[int], Set[int]]] = {}
    for p in U:
        seq = pell_seq_mod[p]
        s0: Set[int] = {j + 1 for j, xj in enumerate(seq) if xj % p == 1}
        s1: Set[int] = {j + 1 for j, xj in enumerate(seq) if xj % p == p - 1}
        side_sets[p] = (s0, s1)

    excl_empty = excl_lam = n_hits = n_open = 0
    excl_empty_by_prime: Dict[int, int] = defaultdict(int)
    hit_ms_set: Set[int] = set()
    rows: List[Dict[str, Any]] = []
    lambda_combined_vals: List[int] = []

    # Enumerate ALL 2^k side assignments over sigma_U.  No sigma/sigma_bar halving
    # (Step-0 Prop: index-side complementation is unsound).
    for sig_int in range(1 << k):
        sigma: Dict[int, int] = {p: (sig_int >> i) & 1 for i, p in enumerate(U)}

        valid_js: Optional[Set[int]] = None
        empty = False
        triggering_prime: Optional[int] = None
        lambda_combined = 1
        for p in U:
            js = side_sets[p][sigma[p]]
            lambda_combined = lcm(lambda_combined, period_by_prime[p])
            if not js:
                empty = True
                triggering_prime = p
                break
            valid_js = js if valid_js is None else valid_js & js
            if not valid_js:
                empty = True
                triggering_prime = p
                break

        # No unramified odd primes (every odd census prime ramified): the seat
        # system is vacuously satisfiable; all indices are candidates.
        if valid_js is None and not empty:
            valid_js = set(range(1, L + 1))

        if empty or not valid_js:
            if triggering_prime is not None:
                excl_empty_by_prime[triggering_prime] += 1
            rows.append({
                "sigma": dict(sigma),
                "lambda_val": None,
                "lambda_combined": None,
                "verdict": "EXCLUDED_EMPTY",
                "hits": [],
                "j_candidates": [],
            })
            excl_empty += 1
            continue

        js_in_L = sorted(j for j in valid_js if 1 <= j <= L)

        if not js_in_L:
            # Seat system solvable but no index within the proven ceiling.
            # Sound exclusion under L = proven ceiling (C4).
            rows.append({
                "sigma": dict(sigma),
                "lambda_val": min(valid_js),
                "lambda_combined": lambda_combined,
                "verdict": "EXCLUDED_LAMBDA",
                "hits": [],
                "j_candidates": [],
            })
            lambda_combined_vals.append(lambda_combined)
            excl_lam += 1
            continue

        lambda_combined_vals.append(lambda_combined)

        # Resolve every surviving index in big integers (both modes).
        hits_here: List[int] = []
        for j in js_in_L:
            xj, _ = pell_power(x1, y1, D, j)
            if xj % 2 == 0:
                continue
            m = (xj - 1) // 2
            if m <= 0:
                continue
            if is_P_smooth(m, primes) and is_P_smooth(m + 1, primes):
                f0, r0 = factor_over_P(m, primes)
                f1, r1 = factor_over_P(m + 1, primes)
                if r0 == 1 and r1 == 1:
                    merged = {pp: f0.get(pp, 0) + f1.get(pp, 0)
                              for pp in set(f0) | set(f1)}
                    # prime-complete iff radical == P_omega
                    if support_tuple(merged) == primes:
                        hits_here.append(m)
                        hit_ms_set.add(m)

        verdict = "HIT" if hits_here else "CHECKED_NO_HIT"
        n_hits += int(bool(hits_here))
        n_open += int(not hits_here)
        rows.append({
            "sigma": dict(sigma),
            "lambda_val": min(js_in_L),
            "lambda_combined": lambda_combined,
            "verdict": verdict,
            "hits": hits_here,
            "j_candidates": js_in_L,
        })

    return MaskResult(
        mask=mask,
        D=D,
        excluded_empty=excl_empty,
        excluded_lambda=excl_lam,
        hits=n_hits,
        open_count=n_open,
        hit_ms=sorted(hit_ms_set),
        cert_rows=rows,
        elapsed_sec=time.time() - t0,
        gp_elapsed_sec=gp_elapsed,
        excl_empty_by_prime=dict(excl_empty_by_prime),
        lambda_combined_vals=lambda_combined_vals,
        worker_pid=os.getpid(),
    )

# ---------------------------------------------------------------------------
# Worker
# ---------------------------------------------------------------------------

def _worker_init(gp_path_arg: str) -> None:
    global _gp_path, _gp_proc
    _gp_path = gp_path_arg
    _gp_proc = None
    atexit.register(_gp_kill)

def _worker_task(args: Tuple) -> Tuple[str, Any]:
    """
    Returns (status, payload):
      ('ok', MaskResult) | ('pruned', mask) | ('error', (mask, reason))
    """
    omega, mask, primes, L, mode, max_m, gp_timeout = args
    D = D_from_mask(mask, primes)
    gp_t0 = time.time()
    try:
        x_ceil = 2 * max_m + 1 if max_m > 0 else 0
        x1, y1 = _pell_xy_gp(D, max_x=x_ceil, timeout=gp_timeout)
        if (x1 == 0 and y1 == 0) or (x_ceil > 0 and x1 > x_ceil):
            return ("pruned", mask)
        # sanity: fundamental solution must satisfy the Pell identity
        if x1 * x1 - D * y1 * y1 != 1:
            return ("error", (mask, f"Pell identity failed D={D}"))
    except Exception as e:
        return ("error", (mask, repr(e)))
    gp_elapsed = time.time() - gp_t0
    return ("ok", process_mask(omega, mask, primes, L, x1, y1, mode,
                               gp_elapsed=gp_elapsed))

# ---------------------------------------------------------------------------
# Checkpoint helpers
# ---------------------------------------------------------------------------

def _checkpoint_path(omega_dir: str, omega: int) -> str:
    return os.path.join(omega_dir, f"lc_checkpoint_omega_{omega:02d}.json")

def _load_checkpoint(omega_dir: str, omega: int) -> Set[int]:
    cp = _checkpoint_path(omega_dir, omega)
    if not os.path.exists(cp):
        return set()
    try:
        with open(cp) as fh:
            data = json.load(fh)
        return set(data.get("completed_masks", []))
    except Exception:
        return set()

def _save_checkpoint(omega_dir: str, omega: int, completed: Set[int]) -> None:
    cp = _checkpoint_path(omega_dir, omega)
    tmp = cp + ".tmp"
    with open(tmp, "w") as fh:
        json.dump({"completed_masks": sorted(completed),
                   "timestamp": utc_now_iso()}, fh)
    os.replace(tmp, cp)

# ---------------------------------------------------------------------------
# Driver structures
# ---------------------------------------------------------------------------

@dataclass
class OmegaSummary:
    omega: int
    pmax: int
    L: int
    total_pairs: int
    excluded_empty: int
    excluded_lambda: int
    hits_total: int
    open_total: int
    hit_values: List[int]
    elapsed_sec: float
    verdict: str
    masks_per_sec: float = 0.0
    peak_rss_mb: float = 0.0
    lambda_min: Optional[int] = None
    lambda_max: Optional[int] = None
    lambda_mean: Optional[float] = None
    lambda_L_ratio_min: Optional[float] = None
    lambda_L_ratio_max: Optional[float] = None
    excl_empty_by_prime: Dict[int, int] = field(default_factory=dict)
    total_gp_elapsed_sec: float = 0.0
    total_mask_elapsed_sec: float = 0.0
    error_masks: List[int] = field(default_factory=list)
    pruned_masks: List[int] = field(default_factory=list)
    self_test_ok: Optional[bool] = None
    self_test_detail: Optional[str] = None

def _write_summary_json(omega: int, omega_dir: str, s: OmegaSummary,
                        mode: str, cert_csv_sha: str) -> None:
    summary_json = os.path.join(omega_dir, f"lc_summary_omega_{omega:02d}.json")
    sd = {
        "program": program_name,
        "version": program_version,
        "omega": omega,
        "pmax": s.pmax,
        "L": s.L,
        "mode": mode,
        "total_pairs": s.total_pairs,
        "excluded_empty": s.excluded_empty,
        "excluded_lambda": s.excluded_lambda,
        "hits_total": s.hits_total,
        "open_total": s.open_total,
        "hit_values": s.hit_values,
        "elapsed_sec": round(s.elapsed_sec, 3),
        "masks_per_sec": round(s.masks_per_sec, 4),
        "peak_rss_mb": round(s.peak_rss_mb, 2),
        "lambda_stats": {
            "lambda_min": s.lambda_min,
            "lambda_max": s.lambda_max,
            "lambda_mean": round(s.lambda_mean, 2) if s.lambda_mean is not None else None,
            "lambda_L_ratio_min": round(s.lambda_L_ratio_min, 4) if s.lambda_L_ratio_min is not None else None,
            "lambda_L_ratio_max": round(s.lambda_L_ratio_max, 4) if s.lambda_L_ratio_max is not None else None,
        },
        "excl_empty_by_prime": {str(k): v for k, v in sorted(s.excl_empty_by_prime.items())},
        "timing": {
            "total_elapsed_sec": round(s.elapsed_sec, 3),
            "total_gp_elapsed_sec": round(s.total_gp_elapsed_sec, 3),
            "total_mask_elapsed_sec": round(s.total_mask_elapsed_sec, 3),
        },
        "verdict": s.verdict,
        "error_masks": s.error_masks,
        "pruned_masks": s.pruned_masks,
        "self_test_ok": s.self_test_ok,
        "self_test_detail": s.self_test_detail,
        "timestamp": utc_now_iso(),
        "python_version": sys.version,
        "platform": platform.platform(),
        "cert_csv_sha256": cert_csv_sha,
    }
    with open(summary_json, "w") as fh:
        json.dump(sd, fh, indent=2)

def _cert_row_to_csv(row: Dict[str, Any], omega: int, L: int) -> List[Any]:
    sigma_str = ",".join(f"p{p}:{sv}" for p, sv in sorted(row["sigma"].items()))
    hits_str = ";".join(str(h) for h in row["hits"])
    jc_str = ";".join(str(j) for j in row.get("j_candidates", []))
    lv = row["lambda_val"]
    lc = row.get("lambda_combined")
    lambda_over_L = ""
    if lc is not None and L > 0:
        lambda_over_L = f"{lc / L:.4f}"
    return [
        omega, row["D"], row["mask"], sigma_str,
        lv if lv is not None else "inf",
        lc if lc is not None else "",
        L, lambda_over_L,
        row["verdict"], hits_str, jc_str,
    ]

# ---------------------------------------------------------------------------
# Known-pair regression gate (C5)
# ---------------------------------------------------------------------------

def self_test_known_pairs(omega: int, gp_path: str, gp_timeout: float,
                          L: int, verbose: bool = True) -> Tuple[bool, str]:
    """
    Re-derive, single-process and uncapped, every known prime-complete pair at
    THIS omega level and assert the corrected pipeline recovers it.  Aborts the
    certificate if any known pair is missed — exactly the check that would have
    caught the v3.1 D=2q bug.
    """
    global _gp_path, _gp_proc
    _gp_path = gp_path
    _gp_proc = None

    expected = set(KNOWN_PRIME_COMPLETE.get(omega, []))
    if not expected:
        return True, f"no known pairs catalogued at omega={omega}; gate vacuous"

    primes = tuple(first_n_primes(omega))
    found: Set[int] = set()
    for mask in range(1, 1 << omega):
        D = D_from_mask(mask, primes)
        try:
            x1, y1 = _pell_xy_gp(D, max_x=0, timeout=gp_timeout)
        except Exception as e:
            return False, f"gp failure on D={D}: {e!r}"
        if x1 == 0 and y1 == 0:
            continue
        res = process_mask(omega, mask, primes, L, x1, y1, "certify")
        found.update(res.hit_ms)

    missing = expected - found
    extra = found - expected
    ok = not missing
    detail = (f"expected={sorted(expected)} found={sorted(found)} "
              f"missing={sorted(missing)} extra={sorted(extra)}")
    if verbose:
        status = "PASS" if ok else "FAIL"
        print(f" [self_test omega={omega}] {status}: {detail}")
    _gp_kill()
    return ok, detail

# ---------------------------------------------------------------------------
# run_omega
# ---------------------------------------------------------------------------

def run_omega(
    omega: int,
    mode: str,
    outdir: str,
    gp_path: str = "gp",
    gp_timeout: float = 300.0,
    workers: int = 1,
    max_m: int = 0,
    L_override: int = 0,
    run_self_test: bool = True,
    verbose: bool = True,
    checkpoint: bool = True,
) -> OmegaSummary:
    t_start = time.time()
    all_primes = tuple(first_n_primes(omega))
    pmax = all_primes[-1]
    L = L_override if L_override > 0 else proven_L(pmax)

    ensure_dir(outdir)
    omega_dir = os.path.join(outdir, f"omega_{omega:02d}")
    ensure_dir(omega_dir)

    # ---- C5: regression gate.  Mandatory in certify mode (unless overridden).
    self_test_ok: Optional[bool] = None
    self_test_detail: Optional[str] = None
    if run_self_test:
        self_test_ok, self_test_detail = self_test_known_pairs(
            omega, gp_path, gp_timeout, L, verbose=verbose)
        if mode == "certify" and not self_test_ok:
            raise RuntimeError(
                f"SELF-TEST FAILED at omega={omega}: the enumerator does not "
                f"recover all known prime-complete pairs, so no certificate can "
                f"be trusted. Detail: {self_test_detail}")

    completed_masks: Set[int] = _load_checkpoint(omega_dir, omega) if checkpoint else set()
    if completed_masks and verbose:
        print(f" [checkpoint] Resuming omega={omega}: "
              f"{len(completed_masks)} masks already done.")

    # ---- C1: vein space = all nonempty submasks over ALL omega census primes.
    # D = product of masked primes (squarefree by construction, > 1).  Order by
    # popcount descending so the heaviest veins (most constrained) run first.
    all_masks = sorted(
        (mask for mask in range(1, 1 << omega)
         if max_m == 0 or D_from_mask(mask, all_primes) <= 2 * max_m * (max_m + 1)),
        key=lambda m: bin(m).count("1"),
        reverse=True,
    )

    tasks: List[Tuple] = []
    for mask in all_masks:
        if mask in completed_masks:
            continue
        D = D_from_mask(mask, all_primes)
        if max_m > 0 and D > 2 * max_m * (max_m + 1):
            continue
        tasks.append((omega, mask, all_primes, L, mode, max_m, gp_timeout))

    if verbose:
        print(
            f"\n[LCm] omega={omega} P_omega={list(all_primes)} "
            f"pmax={pmax} L={L} mode={mode} "
            f"workers={workers} masks={len(tasks)} "
            f"(+{len(completed_masks)} resumed)"
        )

    # ---- Streaming certificate CSV: rows are written per-mask as results
    # arrive, so memory stays O(workers) rather than O(total rows).  This is
    # what makes high omega (e.g. ~2.6e8 rows at omega=18) feasible.
    cert_csv = os.path.join(omega_dir, f"lc_certificates_omega_{omega:02d}.csv")
    cert_fh = open(cert_csv, "w", newline="")
    cert_writer = csv.writer(cert_fh)
    cert_writer.writerow([
        "omega", "D", "mask", "sigma_str",
        "lambda_val", "lambda_combined", "L", "lambda_over_L",
        "verdict", "hits", "j_candidates"
    ])

    total_rows = 0
    all_hit_ms: Set[int] = set()
    excl_empty = excl_lam = hits_total = open_total = 0
    excl_empty_by_prime: Dict[int, int] = defaultdict(int)
    lam_min: Optional[int] = None
    lam_max: Optional[int] = None
    lam_sum = 0
    lam_count = 0
    total_gp_elapsed = 0.0
    total_mask_elapsed = 0.0
    error_masks: List[int] = []
    pruned_masks: List[int] = []

    checkpoint_interval = max(50, len(tasks) // 20) if tasks else 50

    def _merge(r: MaskResult) -> None:
        nonlocal excl_empty, excl_lam, hits_total, open_total
        nonlocal total_gp_elapsed, total_mask_elapsed, total_rows
        nonlocal lam_min, lam_max, lam_sum, lam_count
        # stream rows
        for row in r.cert_rows:
            row["mask"] = r.mask
            row["D"] = r.D
            cert_writer.writerow(_cert_row_to_csv(row, omega, L))
        total_rows += len(r.cert_rows)
        all_hit_ms.update(r.hit_ms)
        excl_empty += r.excluded_empty
        excl_lam += r.excluded_lambda
        hits_total += r.hits
        open_total += r.open_count
        total_gp_elapsed += r.gp_elapsed_sec
        total_mask_elapsed += r.elapsed_sec
        for v in r.lambda_combined_vals:
            if v > 0:
                lam_min = v if lam_min is None else min(lam_min, v)
                lam_max = v if lam_max is None else max(lam_max, v)
                lam_sum += v
                lam_count += 1
        for p, cnt in r.excl_empty_by_prime.items():
            excl_empty_by_prime[p] += cnt

    if workers <= 1:
        global _gp_path, _gp_proc
        _gp_path = gp_path
        _gp_proc = None
        for i, task in enumerate(tasks):
            status, payload = _worker_task(task)
            if status == "pruned":
                pruned_masks.append(int(payload))
                continue
            if status == "error":
                mask, reason = payload
                error_masks.append(int(mask))
                if verbose:
                    print(f"[omega={omega}] ERROR in mask {mask}: {reason}")
                continue
            if status != "ok":
                continue
            _merge(payload)
            completed_masks.add(task[1])
            if checkpoint and (i + 1) % checkpoint_interval == 0:
                cert_fh.flush()
                _save_checkpoint(omega_dir, omega, completed_masks)
    else:
        ctx = mp.get_context("spawn")
        done = 0
        with ctx.Pool(workers, initializer=_worker_init,
                      initargs=(gp_path,)) as pool:
            for status, payload in pool.imap_unordered(_worker_task, tasks,
                                                       chunksize=1):
                done += 1
                if status == "pruned":
                    pruned_masks.append(int(payload))
                    continue
                if status == "error":
                    mask, reason = payload
                    error_masks.append(int(mask))
                    if verbose:
                        print(f"[omega={omega}] ERROR in mask {mask}: {reason}")
                    continue
                if status != "ok":
                    continue
                _merge(payload)
                completed_masks.add(payload.mask)
                if checkpoint and done % checkpoint_interval == 0:
                    cert_fh.flush()
                    _save_checkpoint(omega_dir, omega, completed_masks)

    cert_fh.close()

    elapsed = time.time() - t_start
    hit_values = sorted(all_hit_ms)
    rss = peak_rss_mb()
    masks_processed = len(tasks)

    lam_mean = (lam_sum / lam_count) if lam_count else None
    lam_L_min = (lam_min / L) if lam_min is not None else None
    lam_L_max = (lam_max / L) if lam_max is not None else None

    if error_masks:
        verdict = "INCOMPLETE_ERRORS"
    elif hits_total > 0:
        verdict = "COMPLETE_WITH_HITS"
    else:
        verdict = "COMPLETE_NO_HITS"

    summary = OmegaSummary(
        omega=omega, pmax=pmax, L=L,
        total_pairs=total_rows,
        excluded_empty=excl_empty, excluded_lambda=excl_lam,
        hits_total=hits_total, open_total=open_total,
        hit_values=hit_values, elapsed_sec=elapsed, verdict=verdict,
        masks_per_sec=masks_processed / elapsed if elapsed > 0 else 0.0,
        peak_rss_mb=rss,
        lambda_min=lam_min, lambda_max=lam_max, lambda_mean=lam_mean,
        lambda_L_ratio_min=lam_L_min, lambda_L_ratio_max=lam_L_max,
        excl_empty_by_prime=dict(excl_empty_by_prime),
        total_gp_elapsed_sec=total_gp_elapsed,
        total_mask_elapsed_sec=total_mask_elapsed,
        error_masks=sorted(set(error_masks)),
        pruned_masks=sorted(set(pruned_masks)),
        self_test_ok=self_test_ok,
        self_test_detail=self_test_detail,
    )

    cert_sha = sha256_file(cert_csv)
    _write_summary_json(omega, omega_dir, summary, mode, cert_sha)
    if checkpoint:
        _save_checkpoint(omega_dir, omega, completed_masks)

    if verbose:
        print(f" excluded_empty={excl_empty} excluded_lambda={excl_lam} "
              f"hits={hits_total} open={open_total} verdict={verdict}")
        if elapsed > 0:
            print(f" elapsed={elapsed:.1f}s masks/s={summary.masks_per_sec:.2f} "
                  f"peak_rss={rss:.1f}MB gp_frac={total_gp_elapsed/elapsed:.2%}")
        if lam_min is not None:
            print(f" Lambda(D,sigma_U): min={lam_min} max={lam_max} "
                  f"mean={lam_mean:.1f} Lambda/L: min={lam_L_min:.3f} max={lam_L_max:.3f}")
        if excl_empty_by_prime:
            top = sorted(excl_empty_by_prime.items(), key=lambda x: -x[1])[:5]
            print(f" EXCLUDED_EMPTY top triggers: {top}")
        print(f" --> {omega_dir}")
        if hit_values:
            print(f" HIT VALUES: {hit_values}")

    return summary

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    global _gp_path

    ap = argparse.ArgumentParser(
        prog="LCm_Solver",
        description="Lehmer-Clements prime-complete enumerator v4 (corrected vein space).",
    )
    ap.add_argument("--mode", choices=["certify", "search"], default="search")
    ap.add_argument("--start_omega", type=int, default=2)
    ap.add_argument("--end_omega", type=int, default=9)
    ap.add_argument("--outdir", default="lc_audit")
    ap.add_argument("--gp_path", default="gp")
    ap.add_argument("--gp_timeout", type=float, default=600.0)
    ap.add_argument("--workers", type=int, default=max(1, (os.cpu_count() or 1)))
    ap.add_argument("--max_m", type=int, default=0)
    ap.add_argument("--L_override", type=int, default=0,
                    help="Override index ceiling L (default: max(30, p_omega+1)). "
                         "A certificate run must use at least the proven ceiling.")
    ap.add_argument("--no_self_test", action="store_true",
                    help="Skip the known-pair regression gate (NOT for certificates).")
    ap.add_argument("--self_test_only", action="store_true",
                    help="Run only the regression gate for the omega range and exit.")
    ap.add_argument("--no_checkpoint", action="store_true")
    ap.add_argument("--version", action="store_true")
    args = ap.parse_args()

    if args.version:
        print(json.dumps({
            "program": program_name,
            "version": program_version,
            "timestamp": utc_now_iso(),
        }, indent=2))
        sys.exit(0)

    if args.mode == "certify" and args.max_m > 0:
        print("ERROR: certify mode refuses --max_m > 0 (soundness S6).")
        sys.exit(1)

    _gp_path = args.gp_path

    print(f"LCm_Solver v{program_version} -- "
          f"Lehmer-Clements prime-complete enumerator (corrected vein space)")
    print(f"Mode: {args.mode} omega: {args.start_omega}..{args.end_omega} "
          f"outdir: {args.outdir} gp: {args.gp_path} workers: {args.workers} "
          f"self_test: {not args.no_self_test} checkpoint: {not args.no_checkpoint}")

    ensure_dir(args.outdir)

    # ---- Full-catalogue gate.  In certify mode, before trusting ANY high-omega
    # certificate, verify the corrected enumerator recovers EVERY known prime-
    # complete pair across all catalogued levels (omega <= 8).  The per-omega
    # gate inside run_omega is vacuous above omega=8 (no known pairs there), so
    # this startup pass is what gives a high-omega certify run its teeth.  It is
    # exactly the check that catches a v3.1-style vein-space regression.
    if args.mode == "certify" and not args.no_self_test:
        print("\n[gate] Full known-pair catalogue self-test (omega <= 8):")
        gate_ok = True
        for o in sorted(KNOWN_PRIME_COMPLETE):
            pmax_o = first_n_primes(o)[-1]
            L_o = args.L_override if args.L_override > 0 else proven_L(pmax_o)
            ok, _ = self_test_known_pairs(o, args.gp_path, args.gp_timeout,
                                          L_o, verbose=True)
            gate_ok = gate_ok and ok
        if not gate_ok:
            print("ERROR: full-catalogue gate FAILED; refusing to emit a "
                  "certificate. The enumerator does not recover all known "
                  "prime-complete pairs.")
            sys.exit(1)
        print("[gate] PASS -- all 28 known prime-complete pairs recovered.\n")

    # ---- self_test_only fast path
    if args.self_test_only:
        all_ok = True
        for omega in range(args.start_omega, args.end_omega + 1):
            pmax = first_n_primes(omega)[-1]
            L = args.L_override if args.L_override > 0 else proven_L(pmax)
            ok, detail = self_test_known_pairs(omega, args.gp_path,
                                               args.gp_timeout, L, verbose=True)
            all_ok = all_ok and ok
        print("\n" + "=" * 60)
        print(f"SELF-TEST RESULT: {'ALL PASS' if all_ok else 'FAILURES PRESENT'}")
        print("=" * 60)
        sys.exit(0 if all_ok else 1)

    all_summaries: List[OmegaSummary] = []
    any_hit = False
    any_errors = False

    for omega in range(args.start_omega, args.end_omega + 1):
        s = run_omega(
            omega=omega, mode=args.mode, outdir=args.outdir,
            gp_path=args.gp_path, gp_timeout=args.gp_timeout,
            workers=args.workers, max_m=args.max_m,
            L_override=args.L_override,
            # Certify mode already ran the full-catalogue gate at startup;
            # the per-omega gate is only useful for ad-hoc search runs.
            run_self_test=(not args.no_self_test) and (args.mode != "certify"),
            verbose=True, checkpoint=not args.no_checkpoint,
        )
        all_summaries.append(s)
        if s.hits_total > 0:
            any_hit = True
        if s.error_masks:
            any_errors = True

    master_path = os.path.join(args.outdir, "lc_master_summary.json")
    master = {
        "program": program_name,
        "version": program_version,
        "mode": args.mode,
        "start_omega": args.start_omega,
        "end_omega": args.end_omega,
        "workers": args.workers,
        "any_prime_complete_hit": any_hit,
        "any_errors": any_errors,
        "all_self_tests_ok": all(sv.self_test_ok is not False for sv in all_summaries),
        "per_omega": [
            {
                "omega": sv.omega, "L": sv.L, "pmax": sv.pmax,
                "total_pairs": sv.total_pairs,
                "excluded_empty": sv.excluded_empty,
                "excluded_lambda": sv.excluded_lambda,
                "hits_total": sv.hits_total,
                "open_total": sv.open_total,
                "verdict": sv.verdict,
                "hit_values": sv.hit_values,
                "elapsed_sec": round(sv.elapsed_sec, 3),
                "self_test_ok": sv.self_test_ok,
                "error_masks": sv.error_masks,
                "pruned_masks": sv.pruned_masks,
            }
            for sv in all_summaries
        ],
        "timestamp": utc_now_iso(),
    }
    with open(master_path, "w") as fh:
        json.dump(master, fh, indent=2)

    print("\n" + "=" * 60)
    print(f"MASTER RESULT: any_prime_complete_hit = {any_hit}")
    if any_errors:
        print("WARNING: Some omegas have INCOMPLETE_ERRORS; see per-omega summaries.")
    if not all(sv.self_test_ok is not False for sv in all_summaries):
        print("WARNING: A regression gate FAILED; certificates are NOT valid.")
    if not any_hit:
        excl = sum(sv.excluded_lambda + sv.excluded_empty for sv in all_summaries)
        print(f"All {excl:,} canonical (D, sigma_U) seat systems excluded or checked.")
        print(f"Lehmer-Clements certificate (conditional on error-free, "
              f"self-test-passed omegas): no prime-complete m(m+1) of order "
              f"omega={args.start_omega}..{args.end_omega} exist "
              f"(beyond the known catalogue).")
    else:
        print("Prime-complete hits found -- see per-omega summaries / hit_values.")
    print(f"Master summary --> {master_path}")
    print("=" * 60)

if __name__ == "__main__":
    atexit.register(_gp_kill)
    main()
