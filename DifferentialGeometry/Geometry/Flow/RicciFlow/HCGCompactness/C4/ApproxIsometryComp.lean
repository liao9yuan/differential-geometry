-- NOTE: deliberately imports `AllTimesBounds` (the home of `MetricUniformEquivalentOn`)
-- and not `ApproximateIsometry`, which is currently stale-broken against the in-flight
-- tensor-layer refactor (`Tensor0SBundle.normRS` relocation).
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Composition of approximate isometries (MSM135 F5/F6, metric layer)

The unconditional (`C⁰`) layer of MSM135 "Composition of approximate isometries, I/II"
(`lbl371`/`lbl372`) in the same-domain supplied-pullback formulation: uniform metric
equivalences compose with multiplicative constants (`metricEquiv_trans`), the constant
converts to the book's additive `ε`-form (`metricEquiv_comp_eps`,
`(1+ε₀)(1+ε₁) ≤ 1 + 3(ε₀+ε₁)` for `ε ≤ 1`), and the `lbl372` accumulation of `ε`'s
over a chain of compositions is the scalar fold `compEpsAccum`.

The derivative (`C^p`) part of F5/F6 is the Lemma 4.5 consumer (the book applies
Corollary `lbl370` to `T := Φ₁^*g₂ − g₁`); it is gated on the one-step interface of
`lemma45Double` and is wired when the contraction-Leibniz engine lands.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- The quadratic form of a smooth Riemannian metric is nonnegative. -/
theorem metricInner_nonneg
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

/-- Uniform metric equivalence is monotone in the constant. -/
theorem metricEquiv_mono
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {g h : SmoothRiemannianMetric I M} {C C' : Real}
    (hCC' : C ≤ C')
    (hgh : MetricUniformEquivalentOn (I := I) K g h C) :
    MetricUniformEquivalentOn (I := I) K g h C' := by
  obtain ⟨hC1, hbound⟩ := hgh
  refine ⟨hC1.trans hCC', fun x hx v => ?_⟩
  obtain ⟨hlow, hup⟩ := hbound x hx v
  have hg0 : 0 ≤ g.inner x v v := metricInner_nonneg (I := I) g x v
  have hC0 : (0 : Real) < C := lt_of_lt_of_le one_pos hC1
  have hC'0 : (0 : Real) < C' := lt_of_lt_of_le one_pos (hC1.trans hCC')
  constructor
  · have hinv : C'⁻¹ ≤ C⁻¹ := inv_anti₀ hC0 hCC'
    calc C'⁻¹ * g.inner x v v ≤ C⁻¹ * g.inner x v v :=
          mul_le_mul_of_nonneg_right hinv hg0
      _ ≤ h.inner x v v := hlow
  · calc h.inner x v v ≤ C * g.inner x v v := hup
      _ ≤ C' * g.inner x v v := mul_le_mul_of_nonneg_right hCC' hg0

/-- MSM135 `lbl371` (`C⁰` part): uniform metric equivalences compose with the
product of the constants. -/
theorem metricEquiv_trans
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {g h k : SmoothRiemannianMetric I M} {C₁ C₂ : Real}
    (hgh : MetricUniformEquivalentOn (I := I) K g h C₁)
    (hhk : MetricUniformEquivalentOn (I := I) K h k C₂) :
    MetricUniformEquivalentOn (I := I) K g k (C₁ * C₂) := by
  obtain ⟨hC₁, hbound₁⟩ := hgh
  obtain ⟨hC₂, hbound₂⟩ := hhk
  have hC₁0 : (0 : Real) ≤ C₁ := le_trans zero_le_one hC₁
  have hC₂0 : (0 : Real) ≤ C₂ := le_trans zero_le_one hC₂
  refine ⟨by nlinarith, fun x hx v => ?_⟩
  obtain ⟨hlow₁, hup₁⟩ := hbound₁ x hx v
  obtain ⟨hlow₂, hup₂⟩ := hbound₂ x hx v
  constructor
  · have h1 : (C₁ * C₂)⁻¹ * g.inner x v v =
        C₂⁻¹ * (C₁⁻¹ * g.inner x v v) := by
      rw [mul_inv]
      ring
    rw [h1]
    calc C₂⁻¹ * (C₁⁻¹ * g.inner x v v) ≤ C₂⁻¹ * h.inner x v v :=
          mul_le_mul_of_nonneg_left hlow₁ (inv_nonneg.mpr hC₂0)
      _ ≤ k.inner x v v := hlow₂
  · calc k.inner x v v ≤ C₂ * h.inner x v v := hup₂
      _ ≤ C₂ * (C₁ * g.inner x v v) :=
          mul_le_mul_of_nonneg_left hup₁ hC₂0
      _ = C₁ * C₂ * g.inner x v v := by ring

/-- MSM135 `lbl371` in the book's additive `ε`-form: composing `(1+ε₀)`- and
`(1+ε₁)`-equivalences yields a `(1+3(ε₀+ε₁))`-equivalence when `ε᎐ ≤ 1`. -/
theorem metricEquiv_comp_eps
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {g h k : SmoothRiemannianMetric I M} {eps₀ eps₁ : Real}
    (heps₀ : 0 ≤ eps₀) (heps₀1 : eps₀ ≤ 1)
    (heps₁ : 0 ≤ eps₁)
    (hgh : MetricUniformEquivalentOn (I := I) K g h (1 + eps₀))
    (hhk : MetricUniformEquivalentOn (I := I) K h k (1 + eps₁)) :
    MetricUniformEquivalentOn (I := I) K g k (1 + 3 * (eps₀ + eps₁)) := by
  have hC : (1 + eps₀) * (1 + eps₁) ≤ 1 + 3 * (eps₀ + eps₁) := by
    nlinarith [mul_le_of_le_one_left heps₁ heps₀1]
  exact metricEquiv_mono hC (metricEquiv_trans hgh hhk)

/-- MSM135 `lbl372` accumulation (scalar core of "Composition of approximate
isometries, II"): if each composition step costs at most `C` times the new `ε`,
the `n`-fold composite is controlled by `C` times the sum of the `ε`'s. -/
theorem compEpsAccum {C : Real} {e δ : Nat → Real}
    (h0 : e 0 ≤ C * δ 0)
    (hstep : ∀ k : Nat, e (k + 1) ≤ e k + C * δ (k + 1)) :
    ∀ n : Nat, e n ≤ C * Finset.sum (Finset.range (n + 1)) (fun i => δ i) := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
      have h3 : C * Finset.sum (Finset.range (n + 1)) (fun i => δ i) + C * δ (n + 1) =
          C * Finset.sum (Finset.range (n + 1 + 1)) (fun i => δ i) := by
        conv_rhs => rw [Finset.sum_range_succ, mul_add]
      linarith [hstep n, ih]

end HCGCompactness
end DifferentialGeometry
