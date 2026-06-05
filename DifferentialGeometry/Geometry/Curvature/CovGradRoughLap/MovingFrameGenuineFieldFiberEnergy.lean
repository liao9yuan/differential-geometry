import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochnerFieldSplit
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformProportionalCurvatureSup
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup

/-!
# Frame-summed fibre-norm energy of the genuine moving-frame curvature fibre fields

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the
genuinely-irreducible *per-fibre-field* energy primitives underneath the order-separated fibre
bounds and the moving-frame divergence datum of the rank-generic order-`2` rough-Laplacian /
covariant-gradient commutator defect `Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)` (`pointwiseTensorCurv g s S`).

The order bounds on the concrete genuine curvature sections `GcurvSection g s S`,
`GcurvDerivSection g s S` and on the moving-frame remainder `Curv S − GcurvSection − GcurvDerivSection`
(`MovingFrameGenuineSectionOrderDivergence`) all reduce, through the slot-`0` fibre-match suite
(`GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR`, etc.) together with the frame-invariant
fibre-norm reconstruction `riemannianFiberNormSq_eq_tensorInnerPointwise` /
`tensorInnerPointwise_0s_eq_diag_sum_orthoFrame` (valid in *any* `g_x`-orthonormal frame), to a single
shared statement: the frame-summed squared energy of the corresponding *fibre field*
(`genuineThirdCurvFieldFibPureR`, `genuineThirdCurvFieldFibCovDeriv`, `bracketThirdCurvFieldFib`,
the inner-product-weighted frame reconstructions of the curvature contractions) is bounded by a
single valence-dependent proportional constant times the appropriate fibre-norm order. These three
energy bounds, and the moving-frame divergence datum, are the irreducible genuine content; this file
states them as the precise primitives the order-divergence producer consumes.

## The three energy primitives

For a `g_x`-orthonormal frame `e` with `n = Module.finrank ℝ (TangentSpace I x)`:

* `genuineThirdCurvFieldFibPureR_fiberNormEnergy_le` — the pure-Riemann fibre field
  `genuineThirdCurvFieldFibPureR g s S x e` carries `∑ₐ ⟨e a, ·⟩_g • R(B_i, W a)(∇_{B_i} S)`; its
  frame-summed squared energy `∑_{φ : Fin (s+1) → Fin n} (genuineThirdCurvFieldFibPureR … (e (φ 0))
  (e ∘ φ.tail))²` is bounded `rfns(∇S)`-order. **Why TRUE.** Orthonormality collapses the inner
  weight `⟨e a, e (φ 0)⟩_g = δ_{a, φ 0}`, leaving the single curvature contraction
  `∑_i R(B_i, e (φ 0))(∇_{B_i} S)` (the Ricci identity on the gradient field,
  `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`, in bundled-operator form
  `riemannOp (tensorCov g 0 (s + 1)) x B_i (e (φ 0)) (∇S(x))`); each contraction is fibre-bounded by
  the uniform proportional curvature bound
  `riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound` (with the orthonormal Gram
  scalars `g(B_i, B_i) = 1`, `g(e (φ 0), e (φ 0)) = 1`), and the `n`-fold frame sum is controlled by
  the fibre-norm sub-additivity. The proportional constant is independent of `x`.

* `genuineThirdCurvFieldFibCovDeriv_fiberNormEnergy_le` — the differentiated-curvature fibre field
  `genuineThirdCurvFieldFibCovDeriv g s S x e` carries `∑ₐ ⟨e a, ·⟩_g • ∇_{B_i}(R(B_i, W a) S)`; its
  frame-summed squared energy is bounded `rfns(S)`-order by the uniform differentiated-curvature sup
  `exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound` (`‖∇R‖_∞`), again after the
  orthonormal collapse of the inner weight.

* `bracketThirdCurvFieldFib_fiberNormEnergy_le` — the bracket fibre field
  `bracketThirdCurvFieldFib g s S x e` carries the frame-bracket discrepancy
  `[B_i, W a]` contractions (`covGradRoughLapTraceDiscrepancy_gen`, `tensor3rdCurvBracket`,
  `covGradRoughLapMovingFrameResidual_gen`); its frame-summed squared energy is bounded `rfns(∇²S)`-
  order after the third-order Weitzenböck cancellation of the top-order `∇³S` terms by the iterated
  Ricci identity. **Non-vacuity.** The bracket energy genuinely carries the `∇²S` order and is
  *false* if replaced by an `rfns(∇S)`- or `rfns(S)`-only envelope on a non-flat manifold; the
  cancellation is *false term-by-term* through `smoothExtensionTangent` — only the tensorial
  frame-sum is `∇²S`-order.

These three energy primitives are the deepest moving-frame curvature-endomorphism order content at
general rank; they are posited here and recursed into by the orchestrator. The three order-separated
fibre bounds on the concrete genuine curvature sections
(`MovingFrameGenuineSectionOrderDivergence`) glue from these energy primitives through the slot-`0`
fibre-match suite and the frame-invariant fibre-norm reconstruction. (The moving-frame divergence
datum is the genuinely-irreducible construction of an explicit `∇S`-order field with an almost-
everywhere divergence identity; it remains a separate leaf in the order-divergence producer.)
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Frame-summed squared energy of the pure-Riemann genuine curvature fibre field
(`rfns(∇S)`-order).** For a closed smooth Riemannian manifold `(M, g)` there is a valence-dependent
nonnegative constant `C₁ : ℕ → ℝ` such that, at every covariant rank `s`, smooth compactly-supported
`(0, s)`-tensor `S`, point `x`, and `g_x`-orthonormal frame `e` (with
`n = Module.finrank ℝ (TangentSpace I x)`), the frame-summed squared energy of the pure-Riemann fibre
field is bounded `rfns(∇S)`-order:
```
∑_{φ : Fin (s+1) → Fin n} (genuineThirdCurvFieldFibPureR g s S x e (e (φ 0)) (e ∘ Fin.tail φ))²
  ≤ (C₁ s)² · rfns(∇S)(x),    ∇S := covGrad g 0 s S.
```

**Why this is TRUE.** `genuineThirdCurvFieldFibPureR g s S x e w m
  = ∑ₐ ⟨e a, w⟩_g • toModel (∑ᵢ R(Bᵢ, W a)(∇_{Bᵢ} S)(x)) m`, `W a := smoothExtensionTangent x (e a)`.
With `w = e (φ 0)` the orthonormal Gram `⟨e a, e (φ 0)⟩_g = δ_{a, φ 0}` collapses the `a`-sum to the
single index `a = φ 0`, leaving the model value of the pure-Riemann curvature contraction
`∑ᵢ riemannOp (tensorCov g 0 (s + 1)) x Bᵢ (e (φ 0)) (∇S(x))` (the Ricci identity on the gradient
field, `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`, in bundled-operator form
`tensor3rdCurv_pure_R_eq_riemannOp`). Re-summing the squared model components over `φ` reassembles
the intrinsic fibre norm of this contraction (the frame-invariant reconstruction
`riemannianFiberNormSq_eq_tensorInnerPointwise` / `tensorInnerPointwise_0s_eq_diag_sum_orthoFrame`),
fibre-bounded `rfns(∇S)`-order by the uniform proportional curvature bound
`riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound` (with `g(Bᵢ, Bᵢ) = 1`,
`g(e (φ 0), e (φ 0)) = 1`), summed over the orthonormal frame and reassembled. The constant `C₁ s` is
independent of `x`.

**Non-vacuity.** A zero envelope `C₁ s = 0` would force the pure-Riemann energy to vanish for all
`S, x, e`, but it carries the curvature contraction `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, genuinely non-zero when
`R ≠ 0` and `∇S ≠ 0` on a non-flat manifold; so the bound genuinely envelopes the per-point curvature
operator norm. -/
theorem genuineThirdCurvFieldFibPureR_fiberNormEnergy_le
    (g : SmoothRiemannianMetric I M) :
    ∃ C₁ : ℕ → ℝ, (∀ s, 0 ≤ C₁ s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
        {n : ℕ} (e : Fin n → TangentSpace I x),
        n = Module.finrank ℝ (TangentSpace I x) →
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) →
        ∑ φ : Fin (s + 1) → Fin n,
            genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e (e (φ 0))
              (fun k => e (Fin.tail φ k)) ^ 2 ≤
          C₁ s ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  sorry

/-- **Frame-summed squared energy of the differentiated-curvature genuine fibre field
(`rfns(S)`-order).** For a closed smooth Riemannian manifold `(M, g)` there is a valence-dependent
nonnegative constant `C₂ : ℕ → ℝ` such that, at every covariant rank `s`, smooth compactly-supported
`(0, s)`-tensor `S`, point `x`, and `g_x`-orthonormal frame `e` (with
`n = Module.finrank ℝ (TangentSpace I x)`), the frame-summed squared energy of the
differentiated-curvature fibre field is bounded `rfns(S)`-order:
```
∑_{φ : Fin (s+1) → Fin n} (genuineThirdCurvFieldFibCovDeriv g s S x e (e (φ 0)) (e ∘ Fin.tail φ))²
  ≤ (C₂ s)² · rfns(S)(x).
```

**Why this is TRUE.** `genuineThirdCurvFieldFibCovDeriv g s S x e w m
  = ∑ₐ ⟨e a, w⟩_g • toModel (∑ᵢ ∇_{Bᵢ}(R(Bᵢ, W a) S)(x)) m`. With `w = e (φ 0)` the orthonormal Gram
collapses the `a`-sum to `a = φ 0`, leaving the model value of the differentiated-curvature
contraction `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, e (φ 0)) S)(x)`, the covariant gradient of the curvature contraction of
`S`. Re-summing the squared model components over `φ` reassembles its intrinsic fibre norm
(frame-invariant reconstruction `riemannianFiberNormSq_eq_tensorInnerPointwise`), fibre-bounded
`rfns(S)`-order by the uniform differentiated-curvature sup
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound` (`‖∇R‖_∞`), summed over the orthonormal
frame. The constant `C₂ s` is independent of `x`.

**Non-vacuity.** A zero envelope `C₂ s = 0` would force the differentiated-curvature energy to vanish
for all `S, x, e`, but it carries the contraction `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)`, genuinely non-zero when
`∇R ≠ 0` and `S` non-parallel; so the bound genuinely envelopes the differentiated-curvature sup. -/
theorem genuineThirdCurvFieldFibCovDeriv_fiberNormEnergy_le
    (g : SmoothRiemannianMetric I M) :
    ∃ C₂ : ℕ → ℝ, (∀ s, 0 ≤ C₂ s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
        {n : ℕ} (e : Fin n → TangentSpace I x),
        n = Module.finrank ℝ (TangentSpace I x) →
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) →
        ∑ φ : Fin (s + 1) → Fin n,
            genuineThirdCurvFieldFibCovDeriv (I := I) (M := M) g s S x e (e (φ 0))
              (fun k => e (Fin.tail φ k)) ^ 2 ≤
          C₂ s ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by
  sorry

/-- **Frame-summed squared energy of the bracket genuine curvature fibre field (`rfns(∇²S)`-order).**
For a closed smooth Riemannian manifold `(M, g)` there is a valence-dependent nonnegative constant
`C₃ : ℕ → ℝ` such that, at every covariant rank `s`, smooth compactly-supported `(0, s)`-tensor `S`,
point `x`, and `g_x`-orthonormal frame `e` (with `n = Module.finrank ℝ (TangentSpace I x)`), the
frame-summed squared energy of the bracket fibre field is bounded `rfns(∇²S)`-order:
```
∑_{φ : Fin (s+1) → Fin n} (bracketThirdCurvFieldFib g s S x e (e (φ 0)) (e ∘ Fin.tail φ))²
  ≤ (C₃ s)² · rfns(∇²S)(x),    ∇²S := covGrad g 0 (s+1) (covGrad g 0 s S).
```

**Why this is TRUE.** `bracketThirdCurvFieldFib g s S x e w m
  = ∑ₐ ⟨e a, w⟩_g • toModel (covGradRoughLapTraceDiscrepancy_gen g s S x (e a)
       + tensor3rdCurvBracket g 0 s (W a) S x (unit)
       − covGradRoughLapMovingFrameResidual_gen g s S x (e a)) m`. With `w = e (φ 0)` the orthonormal
Gram collapses the `a`-sum to `a = φ 0`. The surviving frame-bracket discrepancy carries the
bracket-jet `[Bᵢ, W (φ 0)]`, a contraction of the smooth frame data against `∇²S`; its top-order
`∇³S` terms cancel by the iterated Ricci identity, leaving a genuinely `rfns(∇²S)`-order tensorial
field (`riemannianFiberNormSq_tensor3rdCurvGenuine_le` controls the genuine part; the bracket fibre
order controls the discrepancy). Re-summing the squared model components over `φ` reassembles the
intrinsic fibre norm of this `∇²S`-order field. This cancellation is *false term-by-term* through
`smoothExtensionTangent`; only the tensorial frame-sum is `∇²S`-order — the irreducible moving-frame
content.

**Non-vacuity.** The bracket energy genuinely carries the `∇²S` order: an `rfns(∇S)`- or `rfns(S)`-
only envelope is *false* on a non-flat manifold (downstream the moving-frame remainder bound and the
bracket-free pairing `‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` are nonzero), so the genuine `∇²S`-order content
cannot be dropped. -/
theorem bracketThirdCurvFieldFib_fiberNormEnergy_le
    (g : SmoothRiemannianMetric I M) :
    ∃ C₃ : ℕ → ℝ, (∀ s, 0 ≤ C₃ s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
        {n : ℕ} (e : Fin n → TangentSpace I x),
        n = Module.finrank ℝ (TangentSpace I x) →
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) →
        ∑ φ : Fin (s + 1) → Fin n,
            bracketThirdCurvFieldFib (I := I) (M := M) g s S x e (e (φ 0))
              (fun k => e (Fin.tail φ k)) ^ 2 ≤
          C₃ s ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S)).toSection x) := by
  sorry

/-- **The moving-frame remainder fibre-matches the bracket curvature fibre field (any orthonormal
frame).** For a closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, smooth
compactly-supported `(0, s)`-tensor `S`, point `x`, and *arbitrary* `g_x`-orthonormal frame `e` (with
`n = Module.finrank ℝ (TangentSpace I x)`), the unit-section value of the moving-frame remainder
`Curv S − GcurvSection − GcurvDerivSection` (`Curv S := pointwiseTensorCurv g s S`) reconstructs, at
every slot-`0` direction `w` and tail tuple `m`, as the bracket curvature fibre field:
```
toModel ((Curv S − GcurvSection − GcurvDerivSection).toSection x (unit)) (Fin.cons w m)
  = bracketThirdCurvFieldFib g s S x e w m.
```

**Why this is TRUE.** The field split `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`
reads `toModel ((Curv S).toSection x (unit)) (Fin.cons w m)` as
`genuineThirdCurvFieldFib g s S x e w m + bracketThirdCurvFieldFib g s S x e w m` in a witness
`g_x`-orthonormal frame, and `GcurvSection_add_GcurvDerivSection_toSection_eq_genuineThirdCurvField`
identifies `toModel ((GcurvSection + GcurvDerivSection).toSection x (unit)) (Fin.cons w m)` with
`genuineThirdCurvFieldFib g s S x e w m`. Because the genuine moving-frame curvature trace is
*independent of the orthonormal frame* used to assemble it
(`genuineCurvTraceFixedFramePureR_frame_independent` and its differentiated-curvature analogue —
the inner frame sum `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)` does not depend on the choice of `g_x`-orthonormal
`Bᵢ`), both identities hold in *one common* arbitrary orthonormal frame `e`; subtracting the genuine
sections from `Curv S` therefore leaves exactly the bracket field
`bracketThirdCurvFieldFib g s S x e w m`. (The subtraction is at the level of the model coercion of
the unit-section, which is additive: `toModel (A − B) = toModel A − toModel B`.)

**Non-vacuity.** Replacing the genuine sections by zero would assert
`toModel ((Curv S).toSection x (unit)) (Fin.cons w m) = bracketThirdCurvFieldFib g s S x e w m`,
dropping the genuine field `genuineThirdCurvFieldFib`, which is *false* on a non-flat manifold (the
pure-Riemann and differentiated-curvature contractions are genuinely nonzero). So the identity holds
exactly for the genuine curvature sections. -/
theorem movingFrameRemainder_toSection_eq_bracketField
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (w : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S -
              GcurvSection (I := I) (M := M) g s S -
              GcurvDerivSection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
      bracketThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  sorry

end Connection
end Integral
end DifferentialGeometry

end
