#!/usr/bin/env python3
"""Exact rational checks of the Gaussian channel, not a Yang--Mills model.

Moments use independent scalar Gaussian expectations, rather than the
polynomial Laplacian used in Lean. The sector check evaluates every matrix
index in the stripping contraction, including the incoming identity terms.
"""
from fractions import Fraction as F
from math import comb
import json


def gaussian_moment(degree, variance):
    if degree % 2:
        return F(0)
    result = F(1)
    for factor in range(1, degree, 2):
        result *= factor * variance
    return result


def shifted_moment(x, degree, variance):
    return sum(F(comb(degree, k)) * x ** (degree-k) * gaussian_moment(k, variance)
               for k in range(degree+1))


def heat(n, s):
    return [[F(1), n*s, n*(n+2)*s*s],
            [F(0), F(1), 2*(n+2)*s],
            [F(0), F(0), F(1)]]


def product(left, right):
    return [[sum(left[i][k]*right[k][j] for k in range(3))
             for j in range(3)] for i in range(3)]


def stripping(n, d, dimension, low, unit, vacuum):
    transport, inverse = heat(n, -d), heat(n, d)

    def coefficient(i, j, k):
        if i == j == 1:
            return {0: vacuum, 1: low, 2: unit}[k]
        if (i, j, k) in ((0, 1, 1), (1, 0, 1), (0, 0, 0)):
            return unit
        return F(0)

    return sum(transport[1][k]*inverse[i][1]*inverse[j][1]*coefficient(i, j, k)
               for i in range(dimension) for j in range(dimension)
               for k in range(dimension))


def main():
    cases = []
    for n in (1, 3, 8, 15):
        variance = F(2, 3)
        coordinates = [F(i+1, n+1) for i in range(n)]
        q = sum(x*x for x in coordinates)
        second = [shifted_moment(x, 2, variance) for x in coordinates]
        e_q = sum(second)
        e_p = sum(shifted_moment(x, 4, variance) for x in coordinates)
        e_p += 2*sum(second[i]*second[j] for i in range(n) for j in range(i+1, n))
        assert e_q == q+n*variance
        assert e_p == q*q+2*(n+2)*variance*q+n*(n+2)*variance**2
        d, low, unit, vacuum = F(3, 7), F(5, 11), F(2, 5), F(19, 23)
        full = stripping(n, d, 3, low, unit, vacuum)
        small = stripping(n, d, 2, low, unit, vacuum)
        assert full == low-4*d*unit
        assert small == low+2*n*d*unit
        assert full-small == -2*(n+2)*d*unit != 0
        assert product(heat(n, d), heat(n, -d)) == heat(n, F(0))
        assert stripping(n, F(0), 3, low, unit, vacuum) == low
        assert stripping(n, F(0), 2, low, unit, vacuum) == low
        cases.append({"colors": n, "laplacian_Q_squared_coefficient": 2*(n+2),
                      "double_contraction_coefficient": n*(n+2),
                      "full_minus_small_without_scale_power": str(full-small)})
    print(json.dumps({"status": "INDEPENDENT_RENORMALIZED_GAUSSIAN_CHECKS_PASSED",
                      "arithmetic": "exact rational",
                      "complete_generated_YM_prescription": False, "cases": cases}, indent=2))


if __name__ == "__main__":
    main()
