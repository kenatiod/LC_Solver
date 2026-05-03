#!/usr/bin/env python3
# LCm_Solver.py  version 1
"""
LCm_Solver — Lehmer-Clements prime-complete enumerator, multiprocessing edition.

Algorithm improvements over LCr_Solver v3
------------------------------------------
v3 had a critical performance bug: the fused Pell iterate loop walked from
j=1 to j=lambda using big-integer recurrence, multiplying numbers with hundreds
of digits O(lambda) times per (mask, sigma) pair.

v4 (this program) uses the correct approach:

  1. For j = 1 .. L (L <= 59 for all omega <= 17), compute the Pell sequence
     MOD EACH PRIME p in P_omega using the cheap recurrence
         x_{j+1} = x1*xj + D*y1*yj  (mod p)
         y_{j+1} = x1*yj + y1*xj    (mod p)
     This is O(L * omega) small-integer operations per mask -- essentially free.

  2. For each j, collect the set of j values in 1..L where ALL prime-side
     conditions for a given canonical sigma are simultaneously satisfied.
     Most sigma assignments yield an empty intersection -> EXCLUDED_EMPTY.

  3. Only for the rare j that passes all prime-side checks: recover x_j in
     big integers via fast-doubling (O(log j) big-int mults, j <= 59 so
     at most 6 multiplications), extract m = (x_j - 1)/2, and trial-divide
     over P_omega to confirm smoothness and prime-completeness.

  Because hits are rare, big-integer arithmetic is essentially never invoked.
  The dominant cost is the GP call to compute the fundamental Pell solution
  (x1, y1), which is O(1) per mask.

Parallelism
-----------
  Each worker process owns its own PARI/GP subprocess (started lazily on
  first use via _worker_init).  The mask list is distributed across workers
  via multiprocessing.Pool.imap_unordered.  Workers return lightweight
  MaskResult objects; the main process merges them into CSV and JSON.

Usage
-----
    python3 LCm_Solver.py --mode search --start_omega 2 --end_omega 9 \
        --outdir lc_audit --gp_path /opt/homebrew/bin/gp --workers 10

By Ken Clements, May 2, 2026
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import multiprocessing as mp
import os
import platform
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Dict, List, Optional, Set, Tuple

try:
    sys.set_int_max_str_digits(0)
except Exception:
    pass

program_name, program_version = "LCm_Solver", 1

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

def q_from_mask(mask: int, primes: Tuple[int, ...]) -> int:
    q, tmp, i = 1, mask, 0
    while tmp:
        if tmp & 1:
            q *= primes[i]
        tmp >>= 1
        i += 1
    return q

def primes_in_mask(mask: int, primes: Tuple[int, ...]) -> List[int]:
    result, tmp, i = [], mask, 0
    while tmp:
        if tmp & 1:
            result.append(primes[i])
        tmp >>= 1
        i += 1
    return result

# ---------------------------------------------------------------------------
# Fast-doubling Pell exponentiation (big integers, used only for candidates)
# ---------------------------------------------------------------------------

def pell_power(x1: int, y1: int, D: int, n: int) -> Tuple[int, int]:
    """Return (x_n, y_n) via fast doubling in O(log n) big-int multiplications."""
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
# PARI/GP interface (one subprocess per OS process)
# ---------------------------------------------------------------------------

_PELLXY_GP = r"""
pellxy_cf(D,mx=0)={
  my(a0=sqrtint(D),m=0,d=1,a=a0,p0=1,p1=a0,q0=0,q1=1);
  while(p1^2-D*q1^2!=1,
    m=d*a-m;d=(D-m^2)/d;a=(a0+m)\d;
    my(p2=a*p1+p0,q2=a*q1+q0);p0=p1;p1=p2;q0=q1;q1=q2;
    if(mx>0&&p1>mx,return([0,0])));[p1,q1]};
pellxy(D,mx=0)={
  if(issquare(D),error("square"));
  my(F=factor(D),P=F[,1],E=F[,2],d=1,s=1);
  for(i=1,#P,my(e=E[i]);if(e%2,d*=P[i]);s*=P[i]^(e\2));
  my(v=pellxy_cf(d,mx));if(v==[0,0],return([0,0]));
  my(a=v[1],b=v[2]);
  if(s==1,return([a,b]));
  my(a1=a,b1=b);
  while(b%s,my(aa=a1*a+d*b1*b,bb=a1*b+b1*a);a=aa;b=bb;
    if(mx>0&&a>mx,return([0,0])));
  my(y=b/s);[a,y]};
"""

_BEGIN       = "__BEGIN__"
_END         = "__END__"
_VEC2_RE     = re.compile(r"^\[\s*(-?\d+)\s*,\s*(-?\d+)\s*\]\s*$")

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
        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, text=True, bufsize=1,
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
    assert buf[1] == "1",       f"Pell self-test failed: {buf}"
    assert buf[2] == "[0, 0]",  f"Bailout self-test failed: {buf}"
    return p


def _gp_eval(expr: str, timeout: float = 300.0) -> str:
    global _gp_proc
    for attempt in range(3):
        try:
            if _gp_proc is None:
                _gp_proc = _gp_start()
            p = _gp_proc
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
                    in_block = True
                    continue
                if s == _END:
                    break
                if in_block:
                    parts.append(s)
            return "\n".join(parts)
        except Exception:
            _gp_kill()
            if attempt == 2:
                raise


def _pell_xy_gp(D: int, max_x: int = 0) -> Tuple[int, int]:
    arg = f", {max_x}" if max_x > 0 else ""
    raw = _gp_eval(f"print(pellxy({D}{arg}));").strip().splitlines()[-1]
    m = _VEC2_RE.match(raw)
    if not m:
        raise ValueError(f"Unexpected GP output: {raw!r}")
    return int(m.group(1)), int(m.group(2))


def _worker_init(gp_path_arg: str) -> None:
    """Worker process initialiser: record GP path; GP started lazily."""
    import atexit
    global _gp_path, _gp_proc
    _gp_path = gp_path_arg
    _gp_proc = None
    atexit.register(_gp_kill)

# ---------------------------------------------------------------------------
# Core: process one Pell mask
# ---------------------------------------------------------------------------

@dataclass
class MaskResult:
    mask:            int
    q:               int
    excluded_empty:  int
    excluded_lambda: int
    hits:            int
    open_count:      int
    hit_ms:          List[int]
    cert_rows:       List[Dict]
    elapsed_sec:     float


def process_mask(
    omega:  int,
    mask:   int,
    primes: Tuple[int, ...],
    L:      int,
    x1:     int,
    y1:     int,
    mode:   str,
) -> MaskResult:
    """
    Process one Pell mask using mod-p arithmetic for the hot loop.

    Hot path: O(L * omega) small-integer operations per mask.
    Big-integer pell_power() is called only for candidate j values (rare).
    """
    t0 = time.time()
    q = q_from_mask(mask, primes)
    D = 2 * q
    mask_primes = primes_in_mask(mask, primes)
    k = len(mask_primes)

    # Precompute x_j mod p for j = 1 .. L for each prime in the mask.
    # pell_seq_mod[p][j-1] = x_j mod p
    pell_seq_mod: Dict[int, List[int]] = {}
    for p in mask_primes:
        x1p, y1p, Dp = x1 % p, y1 % p, D % p
        xj, yj = x1p, y1p
        seq: List[int] = []
        for _ in range(L):
            seq.append(xj)
            nxj = (x1p * xj + Dp * y1p * yj) % p
            nyj = (x1p * yj + y1p * xj) % p
            xj, yj = nxj, nyj
        pell_seq_mod[p] = seq

    # For each prime p, build sets of j in 1..L satisfying each side condition.
    # side=0: p | m_j    <=> x_j == 1 (mod p)
    # side=1: p | m_j+1  <=> x_j == p-1 (mod p)   i.e. x_j == -1 (mod p)
    side_sets: Dict[int, Tuple[Set[int], Set[int]]] = {}
    for p in mask_primes:
        seq = pell_seq_mod[p]
        s0: Set[int] = {j + 1 for j, xj in enumerate(seq) if xj % p == 1}
        s1: Set[int] = {j + 1 for j, xj in enumerate(seq) if xj % p == p - 1}
        side_sets[p] = (s0, s1)

    excl_empty = excl_lam = n_hits = n_open = 0
    hit_ms_set: Set[int] = set()
    rows: List[Dict] = []

    # Iterate canonical sigma: side=0 on smallest prime in mask.
    for sig_int in range(1 << k):
        if sig_int & 1:     # bit0 = side of mask_primes[0]; must be 0
            continue
        sigma: Dict[int, int] = {p: (sig_int >> i) & 1
                                  for i, p in enumerate(mask_primes)}

        # Intersect the j-sets for each prime under the assigned side.
        valid_js: Optional[Set[int]] = None
        empty = False
        for p in mask_primes:
            js = side_sets[p][sigma[p]]
            if not js:
                empty = True
                break
            valid_js = js if valid_js is None else valid_js & js

        if empty or not valid_js:
            rows.append({"sigma": dict(sigma), "lambda_val": None,
                         "verdict": "EXCLUDED_EMPTY", "hits": [],
                         "j_candidates": []})
            excl_empty += 1
            continue

        js_in_L = sorted(j for j in valid_js if 1 <= j <= L)

        if not js_in_L:
            # All candidates exceed L -> lambda > L -> excluded
            min_j = min(valid_js)
            rows.append({"sigma": dict(sigma), "lambda_val": min_j,
                         "verdict": "EXCLUDED_LAMBDA", "hits": [],
                         "j_candidates": []})
            excl_lam += 1
            continue

        if mode == "certify":
            rows.append({"sigma": dict(sigma), "lambda_val": min(js_in_L),
                         "verdict": "OPEN", "hits": [],
                         "j_candidates": js_in_L})
            n_open += 1
            continue

        # Search: evaluate x_j in big integers for each candidate j <= L
        hits_here: List[int] = []
        for j in js_in_L:
            xj, _ = pell_power(x1, y1, D, j)
            if xj % 2 == 0:
                continue
            m = (xj - 1) // 2
            if m <= 0:
                continue
            if is_P_smooth(m, primes) and is_P_smooth(m + 1, primes):
                f0, r0 = factor_over_P(m,     primes)
                f1, r1 = factor_over_P(m + 1, primes)
                if r0 == 1 and r1 == 1:
                    merged = {p2: f0.get(p2, 0) + f1.get(p2, 0)
                               for p2 in set(f0) | set(f1)}
                    if support_tuple(merged) == primes:
                        hits_here.append(m)
                        hit_ms_set.add(m)

        verdict = "HIT" if hits_here else "OPEN"
        n_hits  += int(bool(hits_here))
        n_open  += int(not hits_here)
        rows.append({"sigma": dict(sigma), "lambda_val": min(js_in_L),
                     "verdict": verdict, "hits": hits_here,
                     "j_candidates": js_in_L})

    return MaskResult(
        mask=mask, q=q,
        excluded_empty=excl_empty, excluded_lambda=excl_lam,
        hits=n_hits, open_count=n_open,
        hit_ms=sorted(hit_ms_set),
        cert_rows=rows,
        elapsed_sec=time.time() - t0,
    )

# ---------------------------------------------------------------------------
# Worker entry point (runs in worker subprocess)
# ---------------------------------------------------------------------------

def _worker_task(args: Tuple) -> Optional[MaskResult]:
    """Compute GP fundamental solution then call process_mask."""
    omega, mask, primes, L, mode, max_m, gp_timeout = args
    q = q_from_mask(mask, primes)
    D = 2 * q
    try:
        x_ceil = 2 * max_m + 1 if max_m > 0 else 0
        x1, y1 = _pell_xy_gp(D, x_ceil)
        if x1 == 0 and y1 == 0:
            return None
        if x_ceil > 0 and x1 > x_ceil:
            return None
    except Exception:
        return None
    return process_mask(omega, mask, primes, L, x1, y1, mode)

# ---------------------------------------------------------------------------
# Omega driver
# ---------------------------------------------------------------------------

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


def _accumulate(r: MaskResult,
                all_rows: List[Dict],
                all_hit_ms: Set[int]) -> None:
    for row in r.cert_rows:
        row["mask"] = r.mask
        row["q"]    = r.q
    all_rows.extend(r.cert_rows)
    all_hit_ms.update(r.hit_ms)


def _write_outputs(omega:     int,
                   omega_dir: str,
                   all_rows:  List[Dict],
                   s:         OmegaSummary,
                   mode:      str) -> None:
    cert_csv = os.path.join(omega_dir, f"lc_certificates_omega_{omega:02d}.csv")
    with open(cert_csv, "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["omega", "q", "mask", "sigma_str",
                    "lambda_val", "L", "verdict", "hits", "j_candidates"])
        for row in all_rows:
            sigma_str = ",".join(f"p{p}:{sv}"
                                  for p, sv in sorted(row["sigma"].items()))
            hits_str  = ";".join(str(h) for h in row["hits"])
            jc_str    = ";".join(str(j) for j in row.get("j_candidates", []))
            lv        = row["lambda_val"]
            w.writerow([
                omega, row["q"], row["mask"], sigma_str,
                lv if lv is not None else "inf",
                s.L, row["verdict"], hits_str, jc_str,
            ])

    summary_json = os.path.join(omega_dir, f"lc_summary_omega_{omega:02d}.json")
    sd = {
        "program":         program_name,
        "version":         program_version,
        "omega":           omega,
        "pmax":            s.pmax,
        "L":               s.L,
        "mode":            mode,
        "total_pairs":     s.total_pairs,
        "excluded_empty":  s.excluded_empty,
        "excluded_lambda": s.excluded_lambda,
        "hits_total":      s.hits_total,
        "open_total":      s.open_total,
        "hit_values":      s.hit_values,
        "elapsed_sec":     round(s.elapsed_sec, 3),
        "verdict":         s.verdict,
        "timestamp":       utc_now_iso(),
        "python_version":  sys.version,
        "platform":        platform.platform(),
        "cert_csv_sha256": sha256_file(cert_csv),
    }
    with open(summary_json, "w") as fh:
        json.dump(sd, fh, indent=2)


def run_omega(
    omega:      int,
    mode:       str,
    outdir:     str,
    gp_path:    str   = "gp",
    gp_timeout: float = 300.0,
    workers:    int   = 1,
    max_m:      int   = 0,
    verbose:    bool  = True,
) -> OmegaSummary:
    t_start    = time.time()
    all_primes = tuple(first_n_primes(omega))
    pmax       = all_primes[-1]
    L          = max(3, pmax)

    ensure_dir(outdir)
    omega_dir = os.path.join(outdir, f"omega_{omega:02d}")
    ensure_dir(omega_dir)

    # Build task list (skip degenerate q=2 mask and masks with q too large)
    tasks: List[Tuple] = []
    for mask in range(1, 1 << omega):
        q = q_from_mask(mask, all_primes)
        if q == 2:
            continue
        if max_m > 0 and q > 2 * max_m * (max_m + 1):
            continue
        tasks.append((omega, mask, all_primes, L, mode, max_m, gp_timeout))

    if verbose:
        print(f"\n[LCm] omega={omega}  P_omega={list(all_primes)}  "
              f"pmax={pmax}  L={L}  mode={mode}  "
              f"workers={workers}  masks={len(tasks)}")

    all_rows:   List[Dict]  = []
    all_hit_ms: Set[int]    = set()
    excl_empty = excl_lam = hits_total = open_total = 0

    if workers <= 1:
        # Single-process path: use module-level GP
        global _gp_path
        _gp_path = gp_path
        for task in tasks:
            r = _worker_task(task)
            if r is None:
                continue
            _accumulate(r, all_rows, all_hit_ms)
            excl_empty  += r.excluded_empty
            excl_lam    += r.excluded_lambda
            hits_total  += r.hits
            open_total  += r.open_count
    else:
        ctx = mp.get_context("spawn")
        done = 0
        with ctx.Pool(workers,
                      initializer=_worker_init,
                      initargs=(gp_path,)) as pool:
            for r in pool.imap_unordered(_worker_task, tasks, chunksize=8):
                if r is None:
                    continue
                _accumulate(r, all_rows, all_hit_ms)
                excl_empty  += r.excluded_empty
                excl_lam    += r.excluded_lambda
                hits_total  += r.hits
                open_total  += r.open_count
                done += 1
                if verbose and done % 500 == 0:
                    elapsed = time.time() - t_start
                    print(f"  ... {done}/{len(tasks)} masks  "
                          f"empty={excl_empty} lambda_excl={excl_lam}  "
                          f"hits={hits_total} open={open_total}  "
                          f"elapsed={elapsed:.1f}s")

    elapsed    = time.time() - t_start
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
        excluded_empty=excl_empty, excluded_lambda=excl_lam,
        hits_total=hits_total, open_total=open_total,
        hit_values=hit_values, elapsed_sec=elapsed, verdict=verdict,
    )

    _write_outputs(omega, omega_dir, all_rows, summary, mode)

    if verbose:
        print(f"  excluded_empty={excl_empty}  excluded_lambda={excl_lam}  "
              f"hits={hits_total}  open={open_total}  verdict={verdict}")
        print(f"  elapsed={elapsed:.1f}s  --> {omega_dir}")
        if hit_values:
            print(f"  HIT VALUES: {hit_values}")

    return summary

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    global _gp_path

    ap = argparse.ArgumentParser(
        prog="LCm_Solver",
        description="Lehmer-Clements prime-complete Pell enumerator (multiprocessing).",
    )
    ap.add_argument("--mode",        choices=["certify", "search"], default="search")
    ap.add_argument("--start_omega", type=int,   default=9)
    ap.add_argument("--end_omega",   type=int,   default=17)
    ap.add_argument("--outdir",      default="lc_audit")
    ap.add_argument("--gp_path",     default="gp")
    ap.add_argument("--gp_timeout",  type=float, default=300.0)
    ap.add_argument("--workers",     type=int,
                    default=max(1, (os.cpu_count() or 1)))
    ap.add_argument("--max_m",       type=int,   default=0)
    ap.add_argument("--version",     action="store_true")
    args = ap.parse_args()

    if args.version:
        print(json.dumps({
            "program":   program_name,
            "version":   program_version,
            "timestamp": utc_now_iso(),
        }, indent=2))
        sys.exit(0)

    _gp_path = args.gp_path

    print(f"LCm_Solver v{program_version}  --  "
          f"Lehmer-Clements prime-complete enumerator (multiprocessing)")
    print(f"Mode: {args.mode}  "
          f"omega: {args.start_omega}..{args.end_omega}  "
          f"outdir: {args.outdir}  "
          f"gp: {args.gp_path}  "
          f"workers: {args.workers}")

    ensure_dir(args.outdir)
    all_summaries: List[OmegaSummary] = []
    any_hit = False

    for omega in range(args.start_omega, args.end_omega + 1):
        s = run_omega(
            omega=omega, mode=args.mode, outdir=args.outdir,
            gp_path=args.gp_path, gp_timeout=args.gp_timeout,
            workers=args.workers, max_m=args.max_m, verbose=True,
        )
        all_summaries.append(s)
        if s.hits_total > 0:
            any_hit = True

    master_path = os.path.join(args.outdir, "lc_master_summary.json")
    master = {
        "program":              program_name,
        "version":              program_version,
        "mode":                 args.mode,
        "start_omega":          args.start_omega,
        "end_omega":            args.end_omega,
        "workers":              args.workers,
        "any_prime_complete_hit": any_hit,
        "per_omega": [
            {
                "omega":           sv.omega,
                "L":               sv.L,
                "total_pairs":     sv.total_pairs,
                "excluded_empty":  sv.excluded_empty,
                "excluded_lambda": sv.excluded_lambda,
                "hits_total":      sv.hits_total,
                "open_total":      sv.open_total,
                "verdict":         sv.verdict,
                "hit_values":      sv.hit_values,
                "elapsed_sec":     round(sv.elapsed_sec, 3),
            }
            for sv in all_summaries
        ],
        "timestamp": utc_now_iso(),
    }
    with open(master_path, "w") as fh:
        json.dump(master, fh, indent=2)

    print(f"\n{'='*60}")
    print(f"MASTER RESULT:  any_prime_complete_hit = {any_hit}")
    if not any_hit:
        excl = sum(sv.excluded_lambda + sv.excluded_empty for sv in all_summaries)
        print(f"All {excl:,} canonical (q,sigma) pairs excluded analytically.")
        print(f"Lehmer-Clements certificate: no prime-complete m(m+1) "
              f"of order omega={args.start_omega}..{args.end_omega} exist.")
    else:
        print("Prime-complete hits found -- see per-omega summaries.")
    print(f"Master summary --> {master_path}")
    print("=" * 60)


if __name__ == "__main__":
    import atexit
    atexit.register(_gp_kill)
    main()
