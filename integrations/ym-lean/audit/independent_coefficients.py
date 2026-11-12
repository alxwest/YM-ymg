#!/usr/bin/env python3
"""Independent Gaussian calculations; no claim of full generated YM matching.

The exact moments come from exp(v*t^2/2), not the Lean Wick recursion.
The numerical check integrates the radial reduction of the formally checked
free F_01 kernel. Angular reduction and quadrature are not Lean-certified.
Only Python's standard library is required.
"""
from __future__ import annotations

from fractions import Fraction
import json
import math


def moment_factor(degree: int) -> Fraction:
    """n! times the t^n coefficient in exp(t^2/2), for unit variance."""
    if degree % 2:
        return Fraction(0)
    pairs = degree // 2
    return Fraction(math.factorial(degree), 2**pairs * math.factorial(pairs))


def simpson(function, upper: float, intervals: int) -> float:
    if intervals <= 0 or intervals % 2:
        raise ValueError("Simpson quadrature requires positive even intervals")
    step = upper / intervals
    total = function(0.0) + function(upper)
    total += 4 * math.fsum(function(i * step) for i in range(1, intervals, 2))
    total += 2 * math.fsum(function(i * step) for i in range(2, intervals, 2))
    return total * step / 3


def run_checks() -> dict:
    moments = {n: moment_factor(n) for n in (0, 2, 4, 6)}
    if list(moments.values()) != [1, 1, 3, 15]:
        raise AssertionError("Gaussian moment factors disagree with native Wick identities")

    # Solve E[X^4 + a*v*X^2 + b*v^2] = 0 and its X^2 pairing = 0.
    # Divide out the corresponding powers of a nonzero variance v.
    a = (moments[4] * moments[2] - moments[6]) / (moments[4] - moments[2]**2)
    b = -moments[4] - a * moments[2]
    if (a, b) != (-6, 3):
        raise AssertionError("Independent subtraction coefficients disagree with Lean identities")

    radial = []
    for infrared, ultraviolet in ((1.0, 2.0), (0.5, 3.0), (2.0, 5.0), (1.0, 1.0)):
        # On S^3, average (p_0^2+p_1^2)/|p|^2 = 1/2 and area = 2*pi^2.
        # With (2*pi)^-4 Fourier measure, the radial factor is 1/(16*pi^2).
        def integrand(radius):
            return radius**3 * (
                math.exp(-(radius / ultraviolet)**2)
                - math.exp(-(radius / infrared)**2)
            ) / (16 * math.pi**2)

        expected = (ultraviolet**4 - infrared**4) / (32 * math.pi**2)
        numerical = simpson(integrand, 8 * ultraviolet, 32768)
        coarse = simpson(integrand, 8 * ultraviolet, 16384)
        tolerance = 1e-10 * max(1.0, abs(expected))
        error = abs(numerical - expected)
        if error > tolerance or abs(coarse - numerical) > tolerance:
            raise AssertionError("Radial quadrature disagrees with the Gaussian integral")
        radial.append({
            "infrared": infrared, "ultraviolet": ultraviolet,
            "analytic_variance": expected, "numerical_variance": numerical,
            "absolute_error": error, "resolution_difference": abs(coarse - numerical),
            "tolerance": tolerance,
        })

    return {
        "status": "INDEPENDENT_GAUSSIAN_CHECKS_PASSED",
        "moment_factors": {str(n): str(value) for n, value in moments.items()},
        "normal_four_coefficients": {"v_x_squared": str(a), "v_squared": str(b)},
        "radial_checks": radial,
        "radial_check_is_numerical": True,
        "generated_physical_mixing_coefficient_computed": False,
        "existence_only_kernel_certificate": False,
    }


if __name__ == "__main__":
    print(json.dumps(run_checks(), indent=2))
