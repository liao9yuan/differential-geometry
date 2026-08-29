# PolarEvaluation

## Mathematical route

`setLIntegral_polar` specializes the existing function-level polar integration
formula to a measurable restricted set by applying it to the set indicator.
The radial measure remains `volumeIoiPow`, so its density already contains the
Euclidean radial power.

`integral_ioiPow` exposes that density for signed or vector-valued integrals:
an integral on the positive-real subtype becomes the Lebesgue set integral of
the original ambient function multiplied by the radial power.  It reuses the
Mathlib `withDensity` integral formula followed by subtype-comap evaluation.
The equality itself needs no integrability or measurability hypothesis because
Mathlib's Bochner integral formula handles the nonintegrable case on both
sides; downstream non-vacuous applications must still supply their existing
integrability facts.

`integrable_ioiPow_iff` supplies the matching exact integrability criterion:
integrability of the subtype function against `volumeIoiPow d` is equivalent
to integrability on `Ioi 0` of the ambient function weighted by `r ^ d`.
It uses the same `withDensity` and subtype-comap reduction as
`integral_ioiPow`; no extra measurability or endpoint hypothesis is added.

`integral_ioiPow_set` is the measurable-support projection needed by the radial
consumer.  For `S ⊆ Ioi 0`, it turns the subtype integral of
`S.indicator F` directly into the weighted Lebesgue set integral over `S`.
The proof applies `integral_ioiPow`, restricts the resulting positive-ray
integral to `S` because the indicator vanishes on the complement, and removes
the indicator on `S`.  Its only hypotheses are measurability of `S` and the
positive-radius inclusion; it adds no integrability or hierarchy assumptions.

`integral_polar_prod` transports a Bochner-integrable function across the
polar measure-preserving equivalence and applies signed Fubini.  The public
`integral_polar` and `setIntegral_polar` projections provide the whole-space
and measurable-set signed formulas used by radial integration by parts.  They
do not require positivity or a complete codomain.

`integrable_polar_prod` exposes the product-integrability fact formerly local
to the proof of `integral_polar`: every `μ`-integrable `f` pulls back to an
integrable `(u, r) ↦ f (r • u)` under the sphere-times-positive-radius product
measure.  `integral_polar` now consumes this public adapter directly.  The
adapter needs only the normed additive group structure on its codomain; the
unused real normed-space assumption is deliberately omitted.

This is a general measure-theory adapter.  It is used by the direct polar proof
of the weak distance-Laplacian comparison, but it contains no comparison
geometry itself.

This two-adapter task and the signed `PolarEvaluation` API are complete (100%).
They are infrastructure only: the four formal P1c endpoints, including the
distance-Laplacian comparison theorem, remain separate 0% theorem endpoints.
The authoritative comparison plan's last estimate before this local adapter
change was about 32--36% for whole-P1c dedicated machinery and 90--93% for the
Laplacian-specific machinery; this general measure file does not revise those
project-level estimates.

## Verification

Focused verification of the complete signed polar API, including
`integrable_ioiPow_iff`, `integrable_polar_prod`, and
`integral_ioiPow_set`, passes without warnings.  No named refresh was run for
the two new declarations.
