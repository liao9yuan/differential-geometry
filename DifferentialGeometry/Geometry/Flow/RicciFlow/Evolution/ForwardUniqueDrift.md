# ForwardUniqueDrift

## 2026-07-26 — invariant Ricci-drift layer

The component drift is the signed four-slot combination of the single tensor
`Ric(Rm(X,Y)Z,W)`.  The signs come from pair symmetry and the first- and
last-pair skew symmetries of lowered Riemann curvature; no component
enumeration is needed.

The new invariant difference estimate splits the two-flow drift into
`(Ric₁ - Ric₂) * Rm₁` and `Ric₂ * (Rm¹₁ - Rm¹₂)`.  Its second factor is exactly
the Kotschwar carrier after lowering, so the bound closes in terms of the
Ricci-difference norm, `rmDiffSq`, and background `Rm₁`/`Ric₂` norms.
The generic `lowerTri_split` identity performs this split at the fiber layer;
its proof needs explicit multilinearity in the lowered tensor's first slot,
not scalar normalization alone.

Focused verification later passed after the required upstream export became
available.

## 2026-07-26 — pointwise API repair

The repair pass keeps every public statement unchanged.  It adapts the two
`lowerTriSq_le` uses to the theorem's pointwise tensor/map arguments, makes the
last-pair curvature skew proof compare `metricCov` and `LeviCivita` explicitly,
and puts the first-slot Ricci expansion in the exact `tensor02_expand` input
shape.  The component reconstruction uses `ricciDrift_comp` in its direct
orientation.

Focused verification passed after the `ForwardUniqueRem` dependency export was
refreshed; the file is warning-clean.  The targeted export refresh also passed.
