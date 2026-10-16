#!/usr/bin/env python3
"""A1/A2/A5 tail matrix with support-safe KL comparisons.

The exact tail column is rational.  The scaled-Bernoulli and reference bounds
use high-precision mpmath only after the event/support logic has been decided
with exact rational arithmetic.  This script writes a deterministic CSV
artifact and marks all unavailable or inapplicable rows explicitly.
"""

import csv
from fractions import Fraction
from math import comb
from pathlib import Path

import mpmath as mp

from check_exact_hypergeom_tail_kl import hypergeom_tail, mass_numerators, support


mp.mp.dps = 80
ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "checks" / "results" / "problem_a_tail_matrix.csv"


CASES = (
    (7, 3, 3, "odd_sparse"),
    (8, 3, 3, "even_nonbalanced"),
    (8, 4, 4, "even_balanced_a_zero"),
    (15, 3, 3, "odd_sparse"),
    (15, 7, 3, "odd_central_low_sample"),
    (15, 7, 7, "odd_high_sample"),
    (16, 3, 3, "even_sparse"),
    (16, 8, 3, "even_central_low_sample"),
    (16, 8, 8, "even_balanced_a_zero"),
    (31, 3, 3, "odd_sparse"),
    (31, 15, 3, "odd_central_low_sample"),
    (31, 15, 15, "odd_high_sample"),
    (101, 3, 3, "odd_sparse"),
    (101, 50, 17, "odd_central"),
    (101, 50, 49, "odd_high_sample"),
    (10, 1, 1, "m_one_boundary"),
    (10, 2, 2, "m_two_boundary"),
)

X_GRID = (Fraction(1, 4), Fraction(1, 2), Fraction(1), Fraction(2), Fraction(4))


def mp_fraction(value):
    return mp.mpf(value.numerator) / value.denominator


def ceil_fraction(value):
    return -((-value.numerator) // value.denominator)


def floor_fraction(value):
    return value.numerator // value.denominator


def lower_tail(N, K, m, r):
    lo, hi, denominator, numerators = mass_numerators(N, K, m)
    if r < lo:
        return Fraction(0)
    if r >= hi:
        return Fraction(sum(numerators), denominator)
    return Fraction(sum(numerators[: r - lo + 1]), denominator)


def binary_kl(theta, p):
    result = mp.mpf("0")
    if theta > 0:
        result += theta * mp.log(theta / p)
    if theta < 1:
        result += (1 - theta) * mp.log((1 - theta) / (1 - p))
    return result


def parameters(N, K, m):
    p = mp.mpf(K) / N
    M = mp.mpf(m * (N - m)) / (N - 1)
    a = mp.mpf(N - 2 * m) / (N - 2)
    return p, M, a


def scaled_bound(N, K, m, x, upper, exact):
    if exact == 0:
        return "support_zero", mp.mpf("0")
    p, M, a = parameters(N, K, m)
    if abs(a) < mp.mpf("1e-70"):
        if abs(p - mp.mpf("0.5")) < mp.mpf("1e-70"):
            return "quadratic_limit", mp.exp(-2 * x * x / M)
        return "a_zero_invalid", None

    theta = p + (a * x / M if upper else -a * x / M)
    if theta < 0 or theta > 1:
        if exact == 0:
            return "support_zero", mp.mpf("0")
        return "theta_invalid_nonzero", None
    return "scaled_kl", mp.exp(-(M / (a * a)) * binary_kl(theta, p))


def binomial_kl_bound(N, K, m, x, upper, exact):
    if exact == 0:
        return "support_zero", mp.mpf("0")
    p = mp.mpf(K) / N
    theta = p + (x / m if upper else -x / m)
    if theta < 0 or theta > 1:
        if exact == 0:
            return "support_zero", mp.mpf("0")
        return "theta_invalid_nonzero", None
    return "binomial_kl", mp.exp(-m * binary_kl(theta, p))


def curvature_quadratic_bound(N, K, m, x):
    variance_cap = mp.mpf(min(K * (N - K), m * (N - m))) / (4 * (N - 1))
    return mp.exp(-(x * x) / (2 * variance_cap))


def global_constant(N):
    if N % 2 == 0:
        return mp.mpf(N) / (N - 1)
    return 1 / ((N - 1) * mp.atanh(mp.mpf(1) / N))


def global_quadratic_bound(N, m, x):
    coefficient = global_constant(N) * mp.mpf(m * (N - m)) / (4 * N)
    return coefficient, mp.exp(-(x * x) / (2 * coefficient))


def hoeffding_bound(m, x):
    return mp.exp(-2 * x * x / m)


def serfling_bound(N, m, x):
    return mp.exp(-2 * N * x * x / (m * (N - m + 1)))


def log_mgf(N, K, m, t):
    lo, hi, denominator, numerators = mass_numerators(N, K, m)
    mu = mp.mpf(m * K) / N
    terms = [mp.mpf(num) / denominator * mp.exp(t * (i - mu))
             for i, num in zip(range(lo, hi + 1), numerators)]
    return mp.log(mp.fsum(terms))


def variance_at_zero(N, K, m):
    p = mp.mpf(K) / N
    return mp.mpf(m * (N - m)) / (N - 1) * p * (1 - p)


def quadratic_proxy_value(N, K, m, t):
    if abs(t) < mp.mpf("1e-8"):
        return variance_at_zero(N, K, m)
    return 2 * log_mgf(N, K, m, t) / (t * t)


def golden_maximum(function, left, right):
    phi = (mp.sqrt(5) - 1) / 2
    x1 = right - phi * (right - left)
    x2 = left + phi * (right - left)
    f1 = function(x1)
    f2 = function(x2)
    for _ in range(100):
        if f1 < f2:
            left = x1
            x1 = x2
            f1 = f2
            x2 = left + phi * (right - left)
            f2 = function(x2)
        else:
            right = x2
            x2 = x1
            f2 = f1
            x1 = right - phi * (right - left)
            f1 = function(x1)
    point = (left + right) / 2
    return function(point)


def optimal_quadratic_proxy(N, K, m):
    """High-precision diagnostic, not a formal global-optimizer proof."""
    span = mp.mpf(20)
    grid = [(-span + 2 * span * i / 400) for i in range(401)]
    values = [quadratic_proxy_value(N, K, m, t) for t in grid]
    best = variance_at_zero(N, K, m)
    for i in range(1, len(grid) - 1):
        if values[i] >= values[i - 1] and values[i] >= values[i + 1]:
            best = max(best, golden_maximum(
                lambda t: quadratic_proxy_value(N, K, m, t),
                grid[i - 1], grid[i + 1]))
    return best


def fmt(value):
    if value is None:
        return ""
    if isinstance(value, Fraction):
        return f"{value.numerator}/{value.denominator}"
    return mp.nstr(value, 30)


def row_for(N, K, m, label, side, x, sigma2):
    mu = Fraction(m * K, N)
    threshold = ceil_fraction(mu + x) if side == "upper" else floor_fraction(mu - x)
    exact = (hypergeom_tail(N, K, m, threshold)
             if side == "upper" else lower_tail(N, K, m, threshold))
    exact_mp = mp_fraction(exact)
    domain = N >= 7 and m >= 3 and m <= K <= N // 2 and N > 2 * m
    scaled_status, scaled = (scaled_bound(N, K, m, mp_fraction(x), side == "upper", exact)
                             if domain or N == 2 * m else ("outside_envelope_domain", None))
    bin_status, binomial = binomial_kl_bound(
        N, K, m, mp_fraction(x), side == "upper", exact)
    dual_status, dual_binomial = binomial_kl_bound(
        N, m, K, mp_fraction(x), side == "upper", exact)
    curvature = curvature_quadratic_bound(N, K, m, mp_fraction(x))
    global_coefficient, global_tail = global_quadratic_bound(
        N, m, mp_fraction(x))
    return {
        "N": N,
        "K": K,
        "m": m,
        "case": label,
        "side": side,
        "x": fmt(x),
        "threshold": threshold,
        "exact_tail": fmt(exact),
        "scaled_status": scaled_status,
        "scaled_bound": fmt(scaled),
        "binomial_kl_status": bin_status,
        "binomial_kl_bound": fmt(binomial),
        "dual_binomial_kl_status": dual_status,
        "dual_binomial_kl_bound": fmt(dual_binomial),
        "conditional_curvature_tail": fmt(curvature),
        "global_C_N": fmt(global_constant(N)),
        "V_global": fmt(global_coefficient),
        "global_quadratic_tail": fmt(global_tail),
        "fixed_parameter_proxy_diagnostic": fmt(sigma2),
        "fixed_proxy_tail_diagnostic": fmt(
            mp.exp(-mp_fraction(x) ** 2 / (2 * sigma2))),
        "hoeffding_bound": fmt(hoeffding_bound(m, mp_fraction(x))),
        "serfling_bound": fmt(serfling_bound(N, m, mp_fraction(x))),
        "notes": ("nonzero event; global bound is conditional on sharp C_N^*"
                  if exact else "exact event empty; no KL evaluated"),
    }


def main():
    rows = []
    for N, K, m, label in CASES:
        sigma2 = optimal_quadratic_proxy(N, K, m)
        for side in ("upper", "lower"):
            for x in X_GRID:
                row = row_for(N, K, m, label, side, x, sigma2)
                if row["scaled_status"] in ("scaled_kl", "quadratic_limit"):
                    scaled = mp.mpf(row["scaled_bound"])
                    exact = mp_fraction(Fraction(row["exact_tail"]))
                    assert scaled + mp.mpf("1e-60") >= exact, row
                if row["binomial_kl_status"] == "binomial_kl":
                    exact = mp_fraction(Fraction(row["exact_tail"]))
                    assert mp.mpf(row["binomial_kl_bound"]) + mp.mpf("1e-60") >= exact, row
                if row["dual_binomial_kl_status"] == "binomial_kl":
                    exact = mp_fraction(Fraction(row["exact_tail"]))
                    assert mp.mpf(row["dual_binomial_kl_bound"]) + mp.mpf("1e-60") >= exact, row
                if row["scaled_status"] == "theta_invalid_nonzero":
                    raise AssertionError(row)
                rows.append(row)

    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    fields = list(rows[0])
    with OUTPUT.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)

    valid = sum(row["scaled_status"] == "scaled_kl" for row in rows)
    limits = sum(row["scaled_status"] == "quadratic_limit" for row in rows)
    support_zero = sum(row["notes"].startswith("exact event empty") for row in rows)
    print("PASS: wrote", len(rows), "A1/A2/A5 matrix rows to", OUTPUT.relative_to(ROOT))
    print("PASS: scaled KL rows:", valid,
          "quadratic-limit rows:", limits,
          "support-empty rows:", support_zero)
    print("PASS: no nonzero event used an invalid theta")
    print("PASS: primal and symmetry-transposed dual KL rows dominate exact tails")
    print("NOTE: fixed-parameter proxy is a high-precision diagnostic only")
    print("NOTE: V_global uses the manuscript C_N^* formula conditionally")


if __name__ == "__main__":
    main()
