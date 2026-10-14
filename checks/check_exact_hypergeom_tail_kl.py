#!/usr/bin/env python3
"""Exact hypergeometric tails and the binomial KL/Chernoff comparison.

Every probability and every KL benchmark in this check is a Fraction.  The
finite sweep is evidence only; the endpoint strict-improvement argument is
recorded separately in TASK_STATUS_A.md.
"""

from fractions import Fraction
from math import comb


MAX_N = 50


def support(N, K, m):
    return max(0, m + K - N), min(K, m)


def mass_numerators(N, K, m):
    lo, hi = support(N, K, m)
    denominator = comb(N, m)
    numerators = [comb(K, i) * comb(N - K, m - i)
                  for i in range(lo, hi + 1)]
    return lo, hi, denominator, numerators


def hypergeom_tail(N, K, m, r):
    """Return P(H >= r) exactly for H ~ Hyp(N,K,m)."""
    lo, hi, denominator, numerators = mass_numerators(N, K, m)
    if r <= lo:
        numerator = sum(numerators)
    elif r > hi:
        numerator = 0
    else:
        numerator = sum(numerators[r - lo:])
    return Fraction(numerator, denominator)


def hypergeom_lower_tail(N, K, m, r):
    """Return P(H <= r) exactly for H ~ Hyp(N,K,m)."""
    lo, hi, denominator, numerators = mass_numerators(N, K, m)
    if r < lo:
        numerator = 0
    elif r >= hi:
        numerator = sum(numerators)
    else:
        numerator = sum(numerators[: r - lo + 1])
    return Fraction(numerator, denominator)


def kl_chernoff_bound(N, K, m, r):
    """Return exp(-m*D(r/m || K/N)) exactly as a rational number.

    For integral r and m, the logarithms cancel after exponentiation:
      (p*m/r)^r * ((1-p)*m/(m-r))^(m-r).
    The endpoint conventions are the continuous limits of the same formula.
    """
    p = Fraction(K, N)
    if r == 0:
        return (1 - p) ** m
    if r == m:
        return p ** m
    return (p * m / r) ** r * (((1 - p) * m) / (m - r)) ** (m - r)


def endpoint_strict_certificate(max_n):
    """Check the factorwise proof for both all-success and all-failure tails."""
    upper_rows = 0
    lower_rows = 0
    for N in range(3, max_n + 1):
        for K in range(1, N):
            for m in range(2, K + 1):
                exact = hypergeom_tail(N, K, m, m)
                product = Fraction(1)
                for j in range(m):
                    product *= Fraction(K - j, N - j)
                    if j >= 1:
                        assert (K - j) * N < K * (N - j)
                assert exact == product
                assert exact < Fraction(K, N) ** m
                upper_rows += 1

            for m in range(2, N - K + 1):
                exact_zero = Fraction(comb(N - K, m), comb(N, m))
                product_zero = Fraction(1)
                for j in range(m):
                    product_zero *= Fraction(N - K - j, N - j)
                    if j >= 1:
                        assert (N - K - j) * N < (N - K) * (N - j)
                assert exact_zero == product_zero
                assert exact_zero < (Fraction(N - K, N)) ** m
                lower_rows += 1
    return upper_rows, lower_rows


def finite_kl_sweep(max_n):
    """Exhaust all nontrivial upper and lower thresholds through max_n."""
    comparisons = 0
    strict = 0
    equal = []
    violations = []
    lower_comparisons = 0
    lower_strict = 0
    lower_equal = []
    lower_violations = []
    symmetry_checks = 0

    for N in range(2, max_n + 1):
        for K in range(1, N):
            for m in range(1, N + 1):
                lo, hi = support(N, K, m)
                threshold = max(lo, (m * K) // N + 1)
                for r in range(threshold, hi + 1):
                    exact = hypergeom_tail(N, K, m, r)
                    assert exact == hypergeom_tail(N, m, K, r)
                    symmetry_checks += 1
                    bound = kl_chernoff_bound(N, K, m, r)
                    dual_bound = kl_chernoff_bound(N, m, K, r)
                    comparisons += 1
                    if exact > bound or exact > dual_bound:
                        violations.append((N, K, m, r, exact, bound, dual_bound))
                    if exact < bound:
                        strict += 1
                    elif exact == bound:
                        equal.append((N, K, m, r))

                lower_last = min(hi, (m * K + N - 1) // N - 1)
                for lower_r in range(lo, lower_last + 1):
                    lower_exact = hypergeom_lower_tail(N, K, m, lower_r)
                    assert lower_exact == hypergeom_lower_tail(N, m, K, lower_r)
                    symmetry_checks += 1
                    lower_bound = kl_chernoff_bound(N, K, m, lower_r)
                    lower_dual = kl_chernoff_bound(N, m, K, lower_r)
                    lower_comparisons += 1
                    if lower_exact > lower_bound or lower_exact > lower_dual:
                        lower_violations.append(
                            (N, K, m, lower_r, lower_exact,
                             lower_bound, lower_dual))
                    if lower_exact < lower_bound:
                        lower_strict += 1
                    elif lower_exact == lower_bound:
                        lower_equal.append((N, K, m, lower_r))

    assert not violations, violations[:1]
    assert not lower_violations, lower_violations[:1]
    expected_equal = sum(N - 1 for N in range(2, max_n + 1))
    assert len(equal) == expected_equal
    assert all(m == 1 and r == 1 for _, _, m, r in equal)
    assert strict + len(equal) == comparisons
    assert len(lower_equal) == expected_equal
    assert all(m == 1 and r == 0 for _, _, m, r in lower_equal)
    assert lower_strict + len(lower_equal) == lower_comparisons
    return (comparisons, strict, len(equal), lower_comparisons,
            lower_strict, len(lower_equal), symmetry_checks)


def main():
    upper, lower = endpoint_strict_certificate(MAX_N)
    (comparisons, strict, equal, lower_comparisons, lower_strict,
     lower_equal, symmetry_checks) = finite_kl_sweep(MAX_N)

    sample = (17, 8, 4, 3)
    N, K, m, r = sample
    exact = hypergeom_tail(N, K, m, r)
    bound = kl_chernoff_bound(N, K, m, r)
    assert exact < bound

    print("PASS: exact endpoint strictness checks:",
          upper, "all-success rows and", lower, "all-failure rows")
    print("PASS: exact upper-tail/KL sweep:", comparisons,
          "comparisons; strict:", strict, "equality:", equal,
          "dual violations: 0")
    print("PASS: exact lower-tail/KL sweep:", lower_comparisons,
          "comparisons; strict:", lower_strict,
          "equality:", lower_equal, "dual violations: 0")
    print("PASS: exact symmetry-transposition checks:", symmetry_checks)
    print("CERTIFICATE sample N,K,m,r =", sample)
    print("  exact tail =", exact)
    print("  KL/Chernoff =", bound)
    print("  exact gap =", bound - exact)


if __name__ == "__main__":
    main()
