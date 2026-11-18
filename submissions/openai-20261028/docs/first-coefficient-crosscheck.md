# First perturbative coefficient cross-check with ym-lean

**Scope:** an algebraic normalisation comparison against
[`alxwest/ym-lean` PR #11](https://github.com/alxwest/ym-lean/pull/11),
not an identification theorem for the constructed quantum field theory.
No mass gap is assumed or claimed.

## Exact formulas and definitions

In this October source tree:

- `submission/YM/Gauge/Colors.lean` defines `G.casimir` and
  `G.slopeConstant = 11 G.casimir/(24 pi²)`.
- `submission/YM/Pert/Asymptotics/RawAxis.lean` defines
  `b0 G = 11 G.casimir/(48 pi²)`.
- `submission/YM/TraceExtension/Chart/Nectar.lean` proves
  `d2 G = -b0 G/2`.
- `submission/YM/TraceExtension/Verse/Day.lean` defines
  `award G = 12 (d2 G)^2/(b0 G)^2 * lieDim(G)/pi⁴`.

The target's `YangMills/Renormalization.lean` explicitly defines
the conventional two-loop beta polynomial with first coefficient
`-(11/3) C_A/(4 pi)^2`.

The independent [Lean 4.31.0 proof on the target PR](https://github.com/alxwest/ym-lean/blob/bridge/ym-ymg-existence-kinematics/YangMills/YMYMGLeadingCoefficient.lean)
checks algebraically that:

1. The above Wilson action slope equals `2*b0`.
2. The target's explicit `g³` beta coefficient equals `-b0`, **provided the
   target and source adjoint-Casimir scalar values are identified**.
3. The source trace amplitude reduces to `3 lieDim(G)/pi⁴` for nonzero
   `b0`.

The target [audit](https://github.com/alxwest/ym-lean/blob/bridge/ym-ymg-existence-kinematics/YangMills/YMYMGLeadingCoefficientAudit.lean)
compiled with only standard Lean axioms.

## This does not establish physical agreement

The algebraic agreement is **not** an equality between the source
reconstructed physical correlator and the target generated-sector
correlations. Precisely, the following are still not proved:

- Equality of the group Casimir normalisations for a common group and
  invariant bilinear form, including the identification of the two
  presentations of its Lie algebra.
- Equality of the target's *generated* beta-series jet with the explicit
  conventional `betaTwoLoop` polynomial at the first nontrivial order.
- Equality of the source selected centered stress trace with the
  target's quantum curvature-square/trace-anomaly observable, including
  its normalization and actual two-point function.
- Fixed all-orders OPE/correlation predictions.

Thus there is **no numerical contradiction at the conventional one-loop
level**, but there is still a substantive physical identification gap.

Issues: [YM UV/loop matching #2](https://github.com/alxwest/ym-lean/issues/2),
[stress/normalization #6](https://github.com/alxwest/ym-lean/issues/6).

This note is supplementary to the original October submission and
does not change the historical verification scope.
