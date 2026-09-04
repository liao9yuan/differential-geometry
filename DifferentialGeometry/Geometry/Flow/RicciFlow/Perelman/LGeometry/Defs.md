# `Defs.lean`

## Status

Focused verification, including `lLength_join`, passes without local warnings.
The first check of the new theorem failed only because the neighborhood lemmas
`Iio_mem_nhds` and `Ioi_mem_nhds` were incorrectly qualified by `Set`; removing
those qualifiers resolved the issue.

## Checked content

- `lVelocity` is the manifold derivative of a raw curve applied to unit
  backward-time velocity.
- `lSpeedSq` uses the total family metric at forward time `T - tau`.
- `lDensity` has the Morgan--Tian normalization
  `sqrt tau * (R + |X|^2)`; no nonnegativity theorem is claimed for it.
- `lLength` is the oriented interval integral of `lDensity`.
- Zero intervals, adjacent-interval additivity, speed-square nonnegativity,
  germ-level curve congruence, moving-metric/scalar continuity, and interval
  integrability are checked.

## 2026-08-29 same-clock concatenation

- `lLength_join` uses the native paste
  `Set.piecewise (Set.Iic c) gamma0 gamma1` and states exact additivity from the
  two piece-density interval-integrability hypotheses.
- The order hypotheses `a <= c <= b` are necessary to identify the two sides
  of the threshold with the two oriented subintervals.
- No node equality, continuity, or derivative matching is needed for this
  numerical identity.  Away from the single seam the pasted curve has the
  same germ as the corresponding piece, while the seam itself is
  volume-null.
- This is only the same-clock action concatenation adapter.  It does not define
  a restricted segment cost, competitor domain, or dynamic-programming
  principle.

The continuity proof reuses the native tangent-bundle velocity lift and the
native moving-metric quadratic evaluation.  It fully applies the metric before
comparing values, so it does not unfold dependent tangent bundles or Hom
representations.  The scalar hypothesis is kept separate from metric
smoothness, and the carrier condition is imposed only on the theorems that use
solution-time regularity.

## 2026-08-29 local density measurability

- `lDensity_aemeas` is source-written with the weakest local curve regularity
  needed by transported pointed curves: `ContMDiffOn` only on `Ioo a b` and
  backward-time carrier membership only on that open interval.  It has no
  endpoint-order hypothesis.
- The proof obtains continuity of the within-tangent map, identifies it with
  the ordinary tangent map on the open interval, and reuses the native moving
  metric quadratic evaluation.  Atomlessness identifies the restricted
  `Ioo a b` and `Ioc a b` measures, so endpoint regularity is unnecessary.
- This is the local measurability producer consumed by fixed-curve pointed
  action convergence.  Focused verification is warning-free green, and the
  named module refresh is current for its downstream consumer.
- The first focused check reached only the pointwise velocity identification:
  `tangentMapWithin_eq_tangentMap` inferred the total-space projection as the
  curve.  The source now avoids that fragile implicit inference and uses the
  native open-set identity `mfderivWithin_of_isOpen`.  The second check showed
  that the ensuing `simp only` already closes the equality, so its redundant
  trailing `rfl` was removed.

Curve congruence intentionally assumes equality of germs at each integration
point.  Pointwise or almost-everywhere equality of curves alone does not imply
equality of their manifold derivatives.

## Progress and next target

`lLength_join` and `lDensity_aemeas` are focused-green (**100% completion for
their stated endpoints**) with complete dedicated proofs.  This closes the
numerical concatenation and local measurability bricks, not the restricted-cost
DPP or no-mass-loss producers.  Compact P2a `redVolume_anti` remains **100%**;
the broader P2b/P2c packages are accounted separately in `L_GEOMETRY_PLAN.md`.
