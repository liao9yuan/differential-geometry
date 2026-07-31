import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion

/-!
# Transport of the spectral Sobolev scale along an equality of exponents

The spectral scale `tensorHs g r s σ` is indexed by a *real* exponent, so
arithmetically equal exponents give equal but not definitionally equal spaces:
`(2 : ℝ) + 2` and `(4 : ℝ)` name the same real number, yet `Real` addition
does not reduce, so `tensorHs g r s ((2 : ℝ) + 2)` and `tensorHs g r s (4 : ℝ)`
are not interchangeable by `rfl`.

This matters as soon as a family produced at a literal order (`H4 →L H2`, say)
has to feed a consumer whose orders are written arithmetically in a scale
parameter (`H^{a+2} →L H^a`).  Unification cannot solve `?a + 2 =?= 4`, so an
explicit transport is required.  `tensorHsCongr` is that transport; it
generalizes the one-off `orderOneH2Iso` used for `(1 : ℝ) + 1 = 2`.

Because the transport is `LinearIsometryEquiv.refl` after `cases` on the
exponent equality, every compatibility statement below is definitional.

## Main definitions

* `tensorHsCongr h` — the isometric equivalence `Hᵃ ≃ₗᵢ Hᵇ` for `a = b`.
* `tensorHsCongrL h` — the same transport as a continuous linear map.

## Main results

* `tensorHsCongr_incl`, `tensorHsCongrL_incl` — the transport commutes with
  the scale inclusions, in pointwise and in composed form.
* `norm_tensorHsCongr` — the transport is norm preserving.
* `tensorHsCongrL_refl`, `opNorm_comp_congr_le` — reduction at `rfl` and the
  operator-norm bound needed to move a uniform coefficient bound across a
  transport.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

/-- Transport of the spectral Sobolev scale along an equality of exponents. -/
def tensorHsCongr (g : SmoothRiemannianMetric I M) (r s : ℕ) {a b : ℝ}
    (h : a = b) :
    tensorHs (I := I) (M := M) g r s a ≃ₗᵢ[ℝ]
      tensorHs (I := I) (M := M) g r s b := by
  cases h
  exact LinearIsometryEquiv.refl ℝ _

/-- The transport as a continuous linear map. -/
def tensorHsCongrL (g : SmoothRiemannianMetric I M) (r s : ℕ) {a b : ℝ}
    (h : a = b) :
    tensorHs (I := I) (M := M) g r s a →L[ℝ]
      tensorHs (I := I) (M := M) g r s b :=
  (tensorHsCongr (I := I) (M := M) g r s h).toLinearIsometry.toContinuousLinearMap

@[simp] theorem tensorHsCongr_refl (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (a : ℝ) :
    tensorHsCongr (I := I) (M := M) g r s (rfl : a = a) =
      LinearIsometryEquiv.refl ℝ _ :=
  rfl

@[simp] theorem tensorHsCongrL_refl (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (a : ℝ) :
    tensorHsCongrL (I := I) (M := M) g r s (rfl : a = a) =
      ContinuousLinearMap.id ℝ (tensorHs (I := I) (M := M) g r s a) :=
  rfl

theorem tensorHsCongrL_apply {a b : ℝ} (h : a = b)
    (u : tensorHs (I := I) (M := M) g r s a) :
    tensorHsCongrL (I := I) (M := M) g r s h u =
      tensorHsCongr (I := I) (M := M) g r s h u :=
  rfl

/-- The transport is norm preserving. -/
@[simp] theorem norm_tensorHsCongr {a b : ℝ} (h : a = b)
    (u : tensorHs (I := I) (M := M) g r s a) :
    ‖tensorHsCongr (I := I) (M := M) g r s h u‖ = ‖u‖ :=
  (tensorHsCongr (I := I) (M := M) g r s h).norm_map u

/-- The transport commutes with the scale inclusions. -/
theorem tensorHsCongr_incl {a b c d : ℝ}
    (hac : a = c) (hbd : b = d) (hab : a ≤ b) (hcd : c ≤ d)
    (u : tensorHs (I := I) (M := M) g r s b) :
    tensorHsCongr (I := I) (M := M) g r s hac
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hab u) =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hcd
        (tensorHsCongr (I := I) (M := M) g r s hbd u) := by
  cases hac
  cases hbd
  rfl

/-- Composed form of `tensorHsCongr_incl`: this is the shape in which a
commuting inclusion square stated at literal exponents is moved to one stated
at arithmetic exponents. -/
theorem tensorHsCongrL_incl {a b c d : ℝ}
    (hac : a = c) (hbd : b = d) (hab : a ≤ b) (hcd : c ≤ d) :
    (tensorHsCongrL (I := I) (M := M) g r s hac).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hab) =
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hcd).comp
        (tensorHsCongrL (I := I) (M := M) g r s hbd) := by
  cases hac
  cases hbd
  rfl

/-- Postcomposing with a transport does not change the operator norm, so a
uniform coefficient bound survives normalizing the *codomain* exponent. -/
theorem norm_congr_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b : ℝ} (h : a = b)
    (L : X →L[ℝ] tensorHs (I := I) (M := M) g r s a) :
    ‖(tensorHsCongrL (I := I) (M := M) g r s h).comp L‖ = ‖L‖ := by
  cases h
  rw [tensorHsCongrL_refl, ContinuousLinearMap.id_comp]

/-- Precomposing with a transport does not increase the operator norm, so a
uniform coefficient bound survives the exponent normalization. -/
theorem opNorm_comp_congr_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {a b : ℝ} (h : a = b)
    (L : tensorHs (I := I) (M := M) g r s b →L[ℝ] X) :
    ‖L.comp (tensorHsCongrL (I := I) (M := M) g r s h)‖ ≤ ‖L‖ := by
  cases h
  rw [tensorHsCongrL_refl, ContinuousLinearMap.comp_id]

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
