#!/usr/bin/env python3
"""Independent exact-rational and numerical checks for the fixed-sample theorem.

Analytic proof: goal_b/paper/main.tex. This code is evidence, not a proof.
Usage: python goal_b/code/verify_goal_b.py --maxN 60 --numericN 18
Dependencies: NumPy, SciPy. No internet or Docker.
"""
import argparse
import json
import math
from fractions import Fraction as Q
from pathlib import Path

import numpy as np
from scipy.optimize import minimize_scalar


def scale(N, m):
    return Q(m * (N - m), N - 1)


def central_variance(N, m):
    c = N // 2
    return scale(N, m) * Q(c * (N - c), N * N)


def uniform_gap(N, m):
    M = scale(N, m)
    if N % 2 == 0:
        return M / (3 * N * N + 4)
    return M * Q(2 * N * N - 3, 4 * N * N * (N * N + 3))


def rational_cap(N, k, m):
    # First reduce both margins by distribution-preserving complements.
    kk, mm = min(k, N - k), min(m, N - m)
    if kk >= mm:
        d = Q(N - 2 * kk, N)
        return scale(N, m) / (4 * (1 + d * d / 3))
    return Q(kk * (N - kk), 4 * (N - 1))


def exact_certificate(maxN):
    total, branches = 0, {"m<=k": 0, "k<m": 0}
    smallest, example = None, None
    for N in range(2, maxN + 1):
        for m in range(1, N):
            W, D = central_variance(N, m), uniform_gap(N, m)
            assert D > 0
            for k in range(1, N):
                kk, mm = min(k, N - k), min(m, N - m)
                if kk == N // 2:
                    continue
                cap = rational_cap(N, k, m)
                slack = W - D - cap
                assert slack >= 0, (N, k, m, str(slack))
                assert cap < W
                branch = "m<=k" if mm <= kk else "k<m"
                branches[branch] += 1
                total += 1
                if smallest is None or slack < smallest:
                    smallest, example = slack, (N, k, m)
    return {"maxN": maxN, "offcenter_triples": total, "branches": branches,
            "minimum_slack": str(smallest), "minimum_slack_parameters": example}


def proxy_numeric(N, k, m):
    lo, hi = max(0, k + m - N), min(k, m)
    js = np.arange(lo, hi + 1, dtype=float)
    probs = np.array(
        [math.comb(k, j) * math.comb(N - k, m - j) / math.comb(N, m)
         for j in range(lo, hi + 1)], dtype=float)
    assert abs(float(np.sum(probs)) - 1) < 1e-10
    delta = js - k * m / N
    v = float(scale(N, m) * Q(k * (N - k), N * N))
    third = float(np.dot(probs, delta ** 3))
    fourth = float(np.dot(probs, delta ** 4)) - 3 * v ** 2

    def quotient(t):
        # Taylor evaluation prevents cancellation near 0.
        if abs(t) < 0.002:
            return v + third * t / 3 + fourth * t * t / 12
        shifted = t * delta
        peak = float(np.max(shifted))
        return 2 * (peak + math.log(float(np.dot(probs, np.exp(shifted - peak))))) / (t * t)

    tgrid = np.r_[np.linspace(-16, -0.003, 28), [0.0],
                  np.linspace(0.003, 16, 28)]
    candidates = sorted(((quotient(float(t)), float(t)) for t in tgrid),
                        reverse=True)
    best_value, best_tilt = candidates[0]
    for _, center in candidates[:2]:
        sol = minimize_scalar(lambda t: -quotient(t),
                              method="bounded",
                              bounds=(max(-26, center - 0.6), min(26, center + 0.6)),
                              options={"xatol": 1e-11})
        if -sol.fun > best_value:
            best_value, best_tilt = -float(sol.fun), float(sol.x)
    return max(v, best_value), best_tilt


def numerical_certificate(maxN):
    tests, cases, samples = 0, 0, []
    for N in range(2, maxN + 1):
        for m in range(1, N):
            c = N // 2
            W, D = float(central_variance(N, m)), float(uniform_gap(N, m))
            central, tilt = proxy_numeric(N, c, m)
            assert central >= W - 5e-6
            if N % 2 == 0:
                assert abs(central - W) < 2e-5
            for k in range(1, N):
                val, _ = proxy_numeric(N, k, m)
                if k in (c, N-c):
                    assert abs(val - central) < 3e-5, (N, k, m)
                else:
                    assert val <= W - D + 3e-5, (N, k, m, val, W, D)
                    assert val <= central + 3e-5
                    tests += 1
            cases += 1
            if N in [5, 7, 9, 11] and m in [1, 2, 3]:
                samples.append({"N": N, "m": m, "central_optimum": central,
                                "variance": W, "tilt": tilt})
    return {"maxN": maxN, "offcenter_optimized_triples": tests,
            "fixed_margin_cases": cases, "examples": samples}


def check_small_closed_forms():
    checks = []
    for N in range(3, 20, 2):
        for m in [1, 2]:
            value, _ = proxy_numeric(N, N//2, m)
            # At N=3, m=2 is the complement of singleton sampling.
            exact = (1 / (2*N*math.log((N+1)/(N-1)))
                     if m in (1,N-1)
                     else 2 / (N*math.log((N+1)/(N-3))))
            assert abs(value-exact) < 2e-5, (N, m, value, exact)
            checks.append({"N":N,"m":m,"computed":value,
                           "formula":exact,"error":abs(value-exact)})
    return checks


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--maxN", type=int, default=60)
    ap.add_argument("--numericN", type=int, default=18)
    ap.add_argument("--output", default="goal_b/checks/verification.json")
    args = ap.parse_args()
    assert args.maxN >= 2 and args.numericN >= 2
    report = {"result": "PASS", "scope": "computational checking, not formal proof",
              "exact": exact_certificate(args.maxN),
              "numerical": numerical_certificate(args.numericN),
              "closed_forms": check_small_closed_forms()}
    path = Path(args.output)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print("PASS", report["exact"]["offcenter_triples"],
          "exact-rational gaps;", report["numerical"]["offcenter_optimized_triples"],
          "numerical proxies;", len(report["closed_forms"]), "closed-form cases")


if __name__ == "__main__":
    main()
