import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ProperCone
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ScalarStrong
import DifferentialGeometry.Geometry.Operator.MetricFamilyRegularity

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff

universe u uE uH uF

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]

theorem properCone_innerDual_pairing_eq_zero_of_terminal_eq_zero
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (C : ProperCone Real F)
    (u : Real → M → F)
    (y : F) (hy : y ∈ ProperCone.innerDual (C : Set F))
    (V : Real → M → Real)
    (hsol : IsHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G V (innerScalarization u y))
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    (hmem : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, u t x ∈ C)
    (hgrad_cont : ∀ rho : M → Real,
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M ↦
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) tau))
    (hlaplacian_cont : ∀ rho : M → Real,
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M ↦
        laplacianAt (I := I) G p.1 rho p.2)
        (spacetimeSlab (M := M) tau))
    (L : Real)
    (hV : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, L ≤ V t x)
    {x₀ : M} (hzero : innerScalarization u y tau x₀ = 0) :
    ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      innerScalarization u y t x = 0 := by
  let w : Real → M → Real := innerScalarization u y
  have hwcont : ContinuousOn (fun p : Real × M ↦ w p.1 p.2)
      (spacetimeSlab (M := M) tau) := by
    apply hsol.jointCont.mono
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans htau.2.le⟩, hp.2⟩
  have hwnonneg : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, 0 ≤ w t x := by
    intro t ht x
    simpa [w, innerScalarization, real_inner_comm] using hy (hmem t ht x)
  have hwtime : ∀ t : Real, t ∈ Set.Icc 0 tau → 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s ↦ w s x) (Set.Icc 0 tau) t := by
    intro t ht htpos x
    have htreg : t ∈ (RealTimeInterval.closed 0 T hT).regular := by
      change t ∈ Set.Ioo 0 T
      exact ⟨htpos, lt_of_le_of_lt ht.2 htau.2⟩
    exact (hsol.timeDiff t htreg x).differentiableWithinAt
  have hwmdiff : ∀ t : Real, t ∈ Set.Icc 0 tau → 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (w t) x := by
    intro t ht _ x
    have htcarrier : t ∈ (RealTimeInterval.closed 0 T hT).carrier := by
      change t ∈ Set.Icc 0 T
      exact ⟨ht.1, ht.2.trans htau.2.le⟩
    exact (hsol.sliceSmooth t htcarrier).mdifferentiable (by simp) x
  have hwgrad : ∀ t : Real, t ∈ Set.Icc 0 tau → 0 < t → ∀ x : M,
      MDiffAt (T% fun z : M ↦ gradientFun (I := I) (G.metric t) (w t) z) x := by
    intro t ht _ x
    have htcarrier : t ∈ (RealTimeInterval.closed 0 T hT).carrier := by
      change t ∈ Set.Icc 0 T
      exact ⟨ht.1, ht.2.trans htau.2.le⟩
    exact gradientFun_mdiffAt (I := I) (G.metric t) (hsol.sliceSmooth t htcarrier) x
  have hwsuper : ∀ t : Real, t ∈ Set.Icc 0 tau → 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s ↦ w s x) (Set.Icc 0 tau) t -
        laplacianAt (I := I) G t (w t) x - V t x * w t x := by
    intro t ht htpos x
    have htreg : t ∈ (RealTimeInterval.closed 0 T hT).regular := by
      change t ∈ Set.Ioo 0 T
      exact ⟨htpos, lt_of_le_of_lt ht.2 htau.2⟩
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 tau) t :=
      (uniqueDiffOn_Icc htau.1).uniqueDiffWithinAt ht
    have hderiv : derivWithin (fun s ↦ w s x) (Set.Icc 0 tau) t =
        deriv (fun s ↦ w s x) t :=
      (hsol.timeDiff t htreg x).derivWithin huniq
    rw [hderiv]
    linarith [hsol.equation_ge t htreg x]
  exact scalar_strong_maximum_principle_time_dependent_metric_with_potential
    (I := I) G htau.1 hgrad_cont hlaplacian_cont V L w hwcont
      hwnonneg hwtime hwmdiff hwgrad hwsuper hV hzero

theorem properCone_innerDual_pairing_eq_zero_of_terminal_eq_zero_of_metricFamilySmoothOn
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (C : ProperCone Real F)
    (u : Real → M → F)
    (y : F) (hy : y ∈ ProperCone.innerDual (C : Set F))
    (V : Real → M → Real)
    (hsol : IsHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G V (innerScalarization u y))
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    (hmem : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, u t x ∈ C)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D (G.restrict D))
    (hslab : Set.Icc 0 tau ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 tau,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (L : Real)
    (hV : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, L ≤ V t x)
    {x₀ : M} (hzero : innerScalarization u y tau x₀ = 0) :
    ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      innerScalarization u y t x = 0 := by
  apply properCone_innerDual_pairing_eq_zero_of_terminal_eq_zero
    (I := I) G hT C u y hy V hsol htau hmem (L := L) (x₀ := x₀)
  · intro rho hrho
    exact G.gradient_norm_sq_continuousOn hG hslab hrho
  · intro rho hrho
    exact G.laplacianAt_continuousOn
      hG hslab (uniqueDiffOn_Icc htau.1) hconn hrho
  · exact hV
  · exact hzero

end

end DifferentialGeometry.Analysis.Parabolic
