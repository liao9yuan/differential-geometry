# DeTurckVFCovDeriv.lean — notes

Status: **COMPLETE, sorry-free, axiom-clean** (`[propext, Classical.choice, Quot.sound]`),
verified by a real `lake build` of the module (not only `lake env lean`).

## What it delivers

The identity that makes `∇^{g}` commute with the `g`-cometric trace defining the DeTurck
vector field, plus the frame linear algebra it rests on.

* `orthoFrame_expand` — `u = ∑ᵢ g(u, Bᵢ) • Bᵢ` for a `g_x`-orthonormal frame.  Proved from
  the *scalar* Parseval `g_inner_eq_orthonormal_parseval_sum` by showing `g(u−S, u−S) = 0`
  and using `g.pos`.  (Home debt: canonical home is next to
  `g_inner_eq_orthonormal_parseval_sum` in
  `Geometry/Curvature/Bochner/OrthonormalFrameTrace.lean`; kept here to avoid invalidating
  that deep module while other lanes build.)
* `frameDiag_indep` — the diagonal trace `∑ᵢ A(Bᵢ, Bᵢ)` of a *vector-valued* bilinear map is
  independent of the `g_x`-orthonormal frame.
* `deTurckVF_frame_trace` — hence `deTurckVF g g_bg x = ∑ᵢ connDiff g g_bg x (Bᵢ, Bᵢ)` for any
  `g_x`-orthonormal family, not only the `x`-centred `smoothOrthoFrame g x`.
* `frameCorr_vanish` — `∑ᵢ A(∇^{g}_v Bᵢ, Bᵢ) = 0` (private helper `skewDiag_zero`): skew
  frame one-form (`smoothOrthoFrame_cov_skew`) contracted with symmetric `A`
  (`connDiff_symm`).
* `cov_sum` (private) — a covariant derivative distributes over a finite sum of smooth
  sections.  Empty case is Mathlib's `CovariantDerivative.zero`.
* `deTurckVF_covDeriv_eq` — the headline:
  `∇^{g}_v W = ∑ᵢ [ (∇^{g_bg}_v A)(Bᵢ,Bᵢ) + A(A(Bᵢ,Bᵢ),v) − A(Bᵢ,A(Bᵢ,v)) − A(A(Bᵢ,v),Bᵢ) ]`
  with `A = connDiff g g_bg`, `W = deTurckVF g g_bg`, `Bᵢ = smoothOrthoFrame g x i`, and the
  first summand `covDerivConnDiff g_bg g (ext v) Bᵢ Bᵢ x`.

## Key facts found (do not re-derive)

* **The recon's "the orthonormal frame cannot be differentiated pointwise" is FALSE.**
  `smoothOrthoFrame g x i` is a *smooth section*, and `smoothOrthoFrame_orthonormal`
  (`Curvature/CurvatureOperator/RicciIdentitySmoothFrame.lean`) says it is `g_y`-orthonormal
  for **every** `y ∈ smoothOrthoFrameNbhd x`, not merely at the centre.  That is exactly what
  lets `IsCovariantDerivativeOn.congr_of_eventuallyEq` replace `W` by the frozen frame sum on
  a neighbourhood and then differentiate it.
* `connDiff_symm`'s own docstring already announced this route ("paired with
  `cometric_skew_core`, discharges the moving-frame correction in the covariant
  differentiation of the intrinsic trace") — the pairing was planned, never built.
* `connDiff_outerCovDeriv_eq` (`DeTurckVFConnDiffVariation.lean:382`) takes its direction
  argument `X` only through `X x`, so `X := smoothExtensionTangent x v` is free.
* `diffSec (LC g_bg) (LC g) Y Z b = connDiff g g_bg b (Z b) (Y b)` — definitional; this is
  what makes the frozen-sum section literally the object `connDiff_outerCovDeriv_eq`
  differentiates.

## Lean lessons

* `rw [map_sum]` on `(A Σ₁) Σ₂` hits the **outer** application (second slot) first; expand the
  second slot first, then the first slot, then `Finset.sum_comm` to reorder — do not fight it.
* To expand *both* slots of `A u₁ u₂` with `orthoFrame_expand`, first generalise to free
  variables `u₁ u₂` (a `key : ∀ u₁ u₂, …` have).  Rewriting `B i` in place loops through the
  coefficients.
* `ContMDiffAt.mdifferentiableAt` leaves an unsolvable `¬?m = 0` when the smoothness order is
  a metavariable — always pin `n` with an explicit `have hz : ContMDiffAt … ∞ … := …` first.
  (`contMDiff_zeroSection ℝ V` alone does not pin it.)
* `self_eq_add_left` resolves to the wrong lemma here; `add_left_cancel` on a hand-built
  `a + a = a + 0` is robust.  (Moot now: `CovariantDerivative.zero` does the job.)
* `Finset.sum_add_distrib` rewrites *both* sides when the same instantiation occurs there;
  prove the correction sum `= 0` as a standalone `have` in the exact grouped shape rather
  than trying to split it in the goal.

## Verification

Real `lake build +DifferentialGeometry.Geometry.Flow.DeTurckVFCovDeriv` passes, no warnings.
