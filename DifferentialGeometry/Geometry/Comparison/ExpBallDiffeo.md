# ExpBallDiffeo.lean — item-3a assembly + generic injective-local-diffeo glue

Part of the Step A `lbl383` item-3 un-parking (see `ConvexBalls.md` for the brick
plan). Verification passed, sorry-free (2026-06-11).

## What's here

- **`exists_diffeo_of_injOn`** (generic, reusable — listed as a TODO in Mathlib's
  `Geometry.Manifold.LocalDiffeomorph`): an injective local diffeomorphism on an
  open set `s` is realised by a `PartialDiffeomorph` with source `s`, target
  `f '' s`. Construction: inverse = `Function.invFunOn f s`; target open + inverse
  smooth by locality — near each image point both agree with the smooth local
  inverse of the `IsLocalDiffeomorphAt` witness `φ` (injectivity forces
  `invFunOn = φ.symm` on `φ '' (s ∩ φ.source)`), glued with
  `contMDiffOn_of_locally_contMDiffOn`.
- **`exists_expBall_diffeo`** (MSM135 `lbl383` item 3a, assembly form): for
  `ofReal r < injRadius g p`, given `hloc : IsLocalDiffeomorphOn 𝓘(ℝ,E) I 1
  (expMap g p) (ball 0 r)`, the exponential restricts to a `C^1`
  `PartialDiffeomorph` with source `Metric.ball (0:E) r`. Injectivity is
  discharged (`injOn_expMap_ball_of_ofReal_lt_injRadius`); `hloc` is the one
  remaining input.

## The remaining input (B3 frontier)

`hloc` = nonsingularity of `d exp` on the ball (no conjugate points below the
scale). Native route (B0-shared, see `ConvexBalls.md` B3): exp-variation-is-Jacobi
(gated on the W=∂ₜ covariant commutation — the recorded smallest missing lemma) →
parallel-frame Grönwall `J(t) ≈ tw` → `d(exp)_v` invertible for `|v| < c/√C₀` →
`IsLocalDiffeomorphAt` at each `v` via the chart-pushed Banach IFT (mimic
`LocalDiffeomorphism.lean`'s at-zero construction with invertible-derivative
input instead of identity). At `v = 0` it already holds
(`expMap_isLocalDiffeomorphAt_zero`).

## Lean gotchas

- `IsLocalDiffeomorphOn I J n f s` quantifies over the SUBTYPE: apply as
  `hf ⟨x, hx⟩`, not `hf x hx`; dot notation `hloc.theorem` does NOT resolve
  (the def unfolds to a Pi type), call the lemma by name.
- `OpenPartialHomeomorph.isOpen_image_of_subset_source` is the image-openness
  workhorse; reach it via `φ.toOpenPartialHomeomorph`.
- `Function.invFunOn` needs `[Nonempty M]` (source side).
