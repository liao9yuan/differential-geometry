import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Garding
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.IntegratedOrder2WeitzenbockCurvature

/-!
# The all-valence intrinsic curvature `L²` bounds for the rough-Laplacian commutator defect

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates
the two **intrinsic curvature `L²` estimates** that are the genuine curvature-derivative content
feeding the all-order intrinsic Gårding bootstrap (`AllOrderGardingBootstrap.lean`):

* the **integrated order-`2` Weitzenböck cross-term bound** — at every covariant rank `s` the
  one-sided `L²` pairing of the rough-Laplacian / covariant-gradient commutator defect
  `Curv := Δ_∇(∇S) − ∇(Δ_∇ S)` against `∇S` is controlled (in absolute value) by a curvature
  constant times `‖∇S‖²_{L²} + ‖S‖_{L²}·‖∇S‖_{L²}`;
* the **all-order/all-valence commutator-defect bound** — the rough-Laplacian / iterated-gradient
  commutator defect `Δ_∇(∇^p U) − ∇^p(Δ_∇ U)` is `L²`-controlled by the lower gradients
  `∑_{i ≤ p+1} ‖∇^i U‖_{L²}`.

## What is proved vs. posited

The single-step base case of the commutator-defect bound — gradient order `p = 0` — is the exact
statement `Δ_∇ U − Δ_∇ U = 0`, hence vanishes; this is proved here unconditionally
(`covGradRoughLap_commutatorDefect_iter_zero`).

The remaining curvature content is genuine intrinsic differential geometry that, on a closed
manifold, follows from the boundedness of the Riemann curvature tensor and finitely many of its
covariant derivatives (continuous on the compact manifold, hence sup-bounded), combined with the
fibrewise Ricci identity. Two facts are **posited** here as named atomic curvature inputs with
precise signatures, their bodies `sorry`:

* `exists_abs_curvCrossTerm_l2_bound` — the integrated order-`2` Weitzenböck cross-term bound, in
  absolute-value form. Its truth is the standard *integrated* Bochner statement: by the Ricci
  identity on the gradient field (`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`) the fibre
  value of `Curv` is a curvature contraction, and after the integration-by-parts packaged in the
  integrated order-`2` Weitzenböck identity (`weitzenbock_integrated_covGrad_l2_normSq`) the
  cross-term is controlled by the uniform curvature sup `‖R‖_∞` over the compact manifold. The
  integrated form is required: the corresponding pointwise fibre-norm bound on `Curv` carries a
  genuine moving-frame `∇²S`-order discrepancy (`tensor3rdCurvBracket`, the false slot-`0`
  frame-trace matching on a normal manifold) that only the `L²` integration removes.

* `exists_commutatorDefect_l2_bound_succ` — the all-order/all-valence commutator-defect bound at
  gradient orders `p + 1`. Its truth is the iterated Ricci identity: each commutation of `Δ_∇` past
  one covariant gradient produces a contraction of the curvature (and finitely many of its
  covariant derivatives) against lower gradients, the top-order term cancelling, so the iterated
  defect `[Δ_∇, ∇^{p+1}]` is an operator of order `≤ p+1` in `U` with curvature-derivative
  coefficients, all bounded by compactness.

Both posited statements are the genuine curvature-derivative sub-program flagged in the module
docstrings of `Geometry/Curvature/CovGradRoughLap/L2Bound.lean` and
`Geometry/Curvature/Bochner/PointwiseTensorBochner.lean`; isolating them here keeps the all-order
Gårding bootstrap free of any other `sorry`.

**Valence/order-dependent constants (the constants are `ℕ → ℝ`, not single scalars).** Both
posited statements expose a *valence/order-dependent* constant — `Ccross : ℕ → ℝ` indexed by
the tensor rank `s`, and `Cc : ℕ → ℝ` indexed by the gradient order — matching the
valence/order-dependent shapes of `CurvatureCrossTermBound` / `CommutatorDefectBound` /
`Order2GardingFamily` in `AllOrderGardingBootstrap.lean`. A *single* constant uniform over
*all* valences (`∀ s : ℕ`) / *all* gradient orders would be *unsatisfiable* on a non-flat
closed manifold: the curvature endomorphism of the `(0, s)`-tensor bundle is an `s`-slot
derivation, so its operator norm (for the unnormalised fibre norm `riemannianFiberNormSq`)
grows like `s · ‖R‖_∞`, forcing such a constant `≳ (s+1)·‖R‖_∞ → ∞`. (Contrast the
curvature-*free* order-`1` control `Order1ControlFamily` / `order1ControlFamily_holds`, whose
constant is `1`, genuinely valence-uniform and provable.) At each *fixed* valence/order the
curvature and its finitely-many relevant covariant derivatives are continuous on the compact
manifold, hence sup-bounded, so the *per-valence* / *per-order* constant is finite and each
statement is TRUE. The all-order Gårding bootstrap consumes them through a *finite max over
the finite valence/order window* `s, p ≤ 2k + 2` it actually visits at each fixed order `k`.
These two `sorry`s are the genuine remaining analytic curvature leaves (correctly
per-valence/per-order-quantified); the per-statement docstrings below give the details.

## Sign / order conventions

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace) for the rough Laplacian
`rawTensorConnLapSmooth`. The covariant gradient `covGrad g 0 s` raises the tensor rank from
`(0, s)` to `(0, s + 1)`; `iteratedCovGrad g 0 2 j` is its `j`-fold iterate from `(0, 2)` to
`(0, 2 + j)`. All `L²` norms are the global metric `L²` (semi)norm `tensorL2Norm`, which on a
`SmoothCcTensor` is exactly its seminorm `‖·‖`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
/-- **The gradient-order-`0` commutator defect vanishes.** At gradient order `p = 0` the
rough-Laplacian / iterated-gradient commutator defect is
`Δ_∇(∇^0 U) − ∇^0(Δ_∇ U) = Δ_∇ U − Δ_∇ U = 0`, since `∇^0 = id` (`iteratedCovGrad_zero`). This is
the unconditional base case of the all-order commutator-defect bound. -/
theorem covGradRoughLap_commutatorDefect_iter_zero
    (g : SmoothRiemannianMetric I M) (U : SmoothCcTensor g 0 2) :
    rawTensorConnLapSmooth (I := I) g 0 (2 + 0)
          (iteratedCovGrad g 0 2 0 U) -
        iteratedCovGrad g 0 2 0 (rawTensorConnLapSmooth (I := I) g 0 2 U) = 0 := by
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
  simp

set_option linter.unusedSectionVars false in
/-- **The integrated order-`2` Weitzenböck cross-term bound (posited curvature input,
per-valence).** For a closed smooth Riemannian manifold `(M, g)` there is a
*valence-dependent* nonnegative constant `Ccross : ℕ → ℝ` such that, at every covariant
rank `s` and for every smooth compactly-supported `(0, s)`-tensor `S`, the **absolute
value** of the `L²` pairing of the rough-Laplacian / covariant-gradient commutator defect
`Curv := Δ_∇(∇S) − ∇(Δ_∇ S)` against `∇S` is bounded by
`Ccross s · (‖∇S‖²_{L²} + ‖S‖_{L²}·‖∇S‖_{L²})`.

This is the integrated Bochner curvature term of the order-`2` Weitzenböck identity:
fibrewise `Curv` is a Riemann-curvature contraction of `∇S` (the Ricci identity on the
gradient field, `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`), so once the
moving-frame discrepancy is removed by the integration-by-parts packaged in the integrated
identity (`weitzenbock_integrated_covGrad_l2_normSq`) the cross-pairing is controlled, *at
each fixed valence* `s`, by the curvature sup `‖R‖_∞` over the compact manifold (the
uniform fibre-norm gradient-curvature bound `riemannOp_covGrad_fiberNormSq_le_gen` /
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`). The estimate is stated in
the integrated `L²` form precisely because the corresponding pointwise fibre-norm bound on
`Curv` carries a genuine `∇²S`-order moving-frame discrepancy (`tensor3rdCurvBracket`, the
false slot-`0` frame-trace matching on a normal manifold) that only the `L²` integration
removes.

**Why the constant is valence-dependent (`ℕ → ℝ`), not a single scalar.** The curvature
endomorphism `riemannOp (tensorCov g 0 s)` of the `(0, s)`-tensor bundle acts as a
derivation across the `s` tensor slots, so for the standard fibre norm
`riemannianFiberNormSq` (the unnormalised sum of squared orthonormal components) its
operator norm grows like `s · ‖R^{(0,1)}‖`. A *single* `Ccross` uniform over *all* ranks
`s : ℕ` is therefore unsatisfiable on any non-flat closed manifold (`Ccross ≳ (s+1)·‖R‖_∞
→ ∞`); but at each *fixed* valence `s` the curvature and its derivatives are continuous on
the compact manifold, hence sup-bounded, so the *per-valence* constant `Ccross s` is
finite and the statement is TRUE. (Contrast the curvature-*free* order-`1` control
`Order1ControlFamily` / `order1ControlFamily_holds`, whose constant is `1`, genuinely
valence-uniform and provable.) The all-order Gårding bootstrap consumes this through a
*finite max over the valence window* `s ≤ 2k + 2` it actually visits at each fixed order
`k`. This `sorry` is the genuine remaining analytic curvature leaf (now correctly
per-valence-quantified). -/
theorem exists_abs_curvCrossTerm_l2_bound (g : SmoothRiemannianMetric I M) :
    ∃ Ccross : ℕ → ℝ, (∀ s, 0 ≤ Ccross s) ∧ ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
      |tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S) -
              covGrad (I := I) (M := M) g 0 s
                (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun| ≤
        Ccross s *
          (tensorL2Norm (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S).toFun ^ 2 +
            tensorL2Norm (I := I) (M := M) g 0 s S.toFun *
              tensorL2Norm (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S).toFun) := by
  sorry

set_option linter.unusedSectionVars false in
/-- **The all-order/all-valence commutator-defect bound at gradient orders `p + 1` (posited
curvature input, per-order).** For a closed smooth Riemannian manifold `(M, g)` there is a
*order-dependent* nonnegative constant `Cc : ℕ → ℝ` such that, for every smooth
compactly-supported `(0, 2)`-tensor base `U` and every gradient order `p`, the
rough-Laplacian / iterated-gradient commutator defect at order `p + 1` satisfies
`‖Δ_∇(∇^{p+1} U) − ∇^{p+1}(Δ_∇ U)‖_{L²} ≤ Cc (p + 1) · ∑_{i ≤ p+2} ‖∇^i U‖_{L²}`.

This is the genuine curvature-derivative content of the all-order bootstrap: each
commutation of `Δ_∇` past one covariant gradient produces, via the Ricci identity, a
contraction of the curvature (and finitely many covariant derivatives of it) against lower
gradients — the top-order term cancelling — so the iterated commutator `[Δ_∇, ∇^{p+1}]` is
a lower-order (order `≤ p+1`) operator in `U` whose coefficients are built from
`∇^{≤ p}Rm`, all bounded by compactness. It is **posited** here as the genuinely-deep
curvature sub-estimate; its body is `sorry`. The gradient-order-`0` case is the
unconditional `covGradRoughLap_commutatorDefect_iter_zero`.

**Why the constant is order-dependent (`ℕ → ℝ`), not a single scalar.** The iterated
commutator `[Δ_∇, ∇^{p+1}]U` is a contraction of `∇^{≤ p}Rm` across the `(0, 2 + p)`-tensor
slots of `∇^{≤ p}U`, whose coefficient grows with the order `p` (the tensor-bundle
curvature endomorphism is an `O(p)`-slot derivation, and the number of curvature-derivative
terms grows with `p`). A *single* `Cc` uniform over *all* gradient orders `p` is therefore
unsatisfiable on any non-flat closed manifold (`Cc ≳ p·‖∇^{≤p}Rm‖_∞ → ∞`); but at each
*fixed* order `p + 1` the curvature and its finitely-many relevant covariant derivatives are
continuous on the compact manifold, hence sup-bounded, so the *per-order* constant
`Cc (p + 1)` is finite and the statement is TRUE. The all-order Gårding bootstrap consumes
this through a *finite max over the order window* `p ≤ 2k + 1` it actually visits at each
fixed order `k`. This `sorry` is the genuine remaining analytic curvature leaf (now
correctly per-order-quantified). -/
theorem exists_commutatorDefect_l2_bound_succ (g : SmoothRiemannianMetric I M) :
    ∃ Cc : ℕ → ℝ, (∀ p, 0 ≤ Cc p) ∧ ∀ (U : SmoothCcTensor g 0 2) (p : ℕ),
      ‖rawTensorConnLapSmooth (I := I) g 0 (2 + (p + 1))
            (iteratedCovGrad g 0 2 (p + 1) U) -
          iteratedCovGrad g 0 2 (p + 1) (rawTensorConnLapSmooth (I := I) g 0 2 U)‖ ≤
        Cc (p + 1) * ∑ i ∈ Finset.range (p + 1 + 2),
          ‖iteratedCovGrad g 0 2 i U‖ := by
  sorry

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
