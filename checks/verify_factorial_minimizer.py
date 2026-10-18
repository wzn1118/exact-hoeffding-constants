#!/usr/bin/env python3
"""Finite independent regression for the factorial-moment minimizing index.

The manuscript gives an algebraic ratio proof valid for all parameters.
This finite check is supplementary evidence, not its proof.
"""
from fractions import Fraction
from math import comb


def verify(max_population: int = 26) -> int:
    checked = 0
    for N in range(2, max_population + 1):
        for k in range(1, N):
            for m in range(1, N):
                for d in range(1, min(k, m) + 1):
                    if N * d <= k * m:
                        continue
                    numerator = N * d - k * m
                    denominator = N + d - k - m
                    assert numerator > 0 and denominator > 0
                    j_star = (numerator + denominator - 1) // denominator
                    assert 1 <= j_star <= d
                    candidates = [
                        Fraction(comb(k, j) * comb(m, j),
                                 comb(N, j) * comb(d, j))
                        for j in range(d + 1)
                    ]
                    minimum = min(candidates)
                    minimizers = [j for j, c in enumerate(candidates) if c == minimum]
                    expected = [j_star]
                    if numerator % denominator == 0 and j_star < d:
                        expected.append(j_star + 1)
                    assert minimizers == expected, (N, k, m, d, minimizers, expected)
                    checked += 1
    return checked


if __name__ == "__main__":
    print(f"PASS: {verify()} exact rational factorial-moment index cases")
