import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Hopf
import DifferentialGeometry.Analysis.Parabolic.ScalarTimeDependent

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem heat_pot_hopf_boundary_point_on_compact_annulus
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    {S : Real} (hS : 0 ≤ S) (V u : Real → M → Real)
    (hsol : IsHeatPotOn (RealTimeInterval.closed 0 S hS) G V u)
    {tau : Real} (htau : tau ∈ Set.Ioo 0 S)
    (L : Real)
    (rho : M → Real)
    (hrho : ContMDiff I (modelWithCornersSelf Real Real) ∞ rho)
    {r R eta m B kappa alpha : Real}
    (hr : 0 ≤ r) (hrR : r < R) (heta : 0 < eta)
    (hK : IsCompact {x | r ≤ rho x ∧ rho x ≤ R})
    (hkappa : 0 < kappa) (hinit : R ≤ r + kappa * tau ^ 2)
    (halpha : 0 < alpha) (hdom : 2 * kappa * tau + B ≤ alpha * m)
    (hgrad_lower : ∀ t ∈ Set.Icc 0 tau, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        m ≤ (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) rho x)
          (gradientFun (I := I) (G.metric t) rho x))
    (hheat_upper : ∀ t ∈ Set.Icc 0 tau, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        heatOperatorWithDrift (I := I) G t
          (fun y => (0 : TangentSpace I y)) rho x ≤ B)
    (hV_lower : ∀ t ∈ Set.Icc 0 tau,
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R}, L ≤ V t x)
    (hu_nonneg : ∀ t ∈ Set.Icc 0 tau,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R}, 0 ≤ u t x)
    (hu_inner : ∀ t ∈ Set.Icc 0 tau,
      ∀ x ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R},
        rho x = r → eta ≤ u t x)
    {p : M}
    (hp : p ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R})
    (hp_outer : rho p = R)
    (hgrad_boundary : 0 < (G.metric tau).inner p
      (gradientFun (I := I) (G.metric tau) rho p)
      (gradientFun (I := I) (G.metric tau) rho p))
    (hu_zero : u tau p = 0) :
    (G.metric tau).inner p
      (gradientFun (I := I) (G.metric tau) (u tau) p)
      (levelSetOutwardNormal (I := I) (G.metric tau) rho p) < 0 := by
  let X : Real → (x : M) → TangentSpace I x := fun _ x => 0
  have hu_cont : ContinuousOn (fun q : Real × M => u q.1 q.2)
      (Set.Icc 0 tau ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}) := by
    apply hsol.jointCont.mono
    intro q hq
    exact ⟨⟨hq.1.1, hq.1.2.trans htau.2.le⟩, Set.mem_univ q.2⟩
  have hu_time : ∀ t ∈ Set.Icc 0 tau, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 tau) t := by
    intro t ht htpos x
    have htreg : t ∈ (RealTimeInterval.closed 0 S hS).regular := by
      change t ∈ Set.Ioo 0 S
      exact ⟨htpos, lt_of_le_of_lt ht.2 htau.2⟩
    exact (hsol.equation t htreg x).differentiableAt.differentiableWithinAt
  have hu_mdiff : ∀ t ∈ Set.Icc 0 tau, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (u t) x := by
    intro t ht _htpos x
    have htcarrier : t ∈ (RealTimeInterval.closed 0 S hS).carrier := by
      change t ∈ Set.Icc 0 S
      exact ⟨ht.1, ht.2.trans htau.2.le⟩
    exact (hsol.sliceSmooth t htcarrier).mdifferentiable (by simp) x
  have hu_grad : ∀ t ∈ Set.Icc 0 tau, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x := by
    intro t ht _htpos x
    have htcarrier : t ∈ (RealTimeInterval.closed 0 S hS).carrier := by
      change t ∈ Set.Icc 0 S
      exact ⟨ht.1, ht.2.trans htau.2.le⟩
    exact gradientFun_mdiffAt (I := I) (G.metric t)
      (hsol.sliceSmooth t htcarrier) x
  have hu_super : ∀ t ∈ Set.Icc 0 tau, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        0 ≤ parabolicOperatorWithDrift (I := I) G tau X u t x - V t x * u t x := by
    intro t ht htpos x _hx
    have htreg : t ∈ (RealTimeInterval.closed 0 S hS).regular := by
      change t ∈ Set.Ioo 0 S
      exact ⟨htpos, lt_of_le_of_lt ht.2 htau.2⟩
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 tau) t :=
      (uniqueDiffOn_Icc htau.1).uniqueDiffWithinAt ht
    have hderiv : derivWithin (fun s => u s x) (Set.Icc 0 tau) t =
        laplacianAt (I := I) G t (u t) x + V t x * u t x :=
      (hsol.equation t htreg x).hasDerivWithinAt.derivWithin huniq
    unfold parabolicOperatorWithDrift heatOperatorWithDrift driftTerm
    rw [hderiv]
    simp [X]
  exact scalar_hopf_boundary_point_with_potential_on_compact_annulus
    (I := I) G htau.1 X V L rho hrho hr hrR heta hK hkappa hinit
    halpha hdom hgrad_lower (by simpa only [X] using hheat_upper) u
    hu_cont hu_nonneg hu_inner hu_time hu_mdiff hu_grad hu_super hV_lower
    hp hp_outer hgrad_boundary hu_zero

theorem heat_hopf_boundary_point_on_compact_annulus
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    {S : Real} (hS : 0 ≤ S) (u : Real → M → Real)
    (hsol : IsHeatOn (RealTimeInterval.closed 0 S hS) G u)
    {tau : Real} (htau : tau ∈ Set.Ioo 0 S)
    (rho : M → Real)
    (hrho : ContMDiff I (modelWithCornersSelf Real Real) ∞ rho)
    {r R eta m B kappa alpha : Real}
    (hr : 0 ≤ r) (hrR : r < R) (heta : 0 < eta)
    (hK : IsCompact {x | r ≤ rho x ∧ rho x ≤ R})
    (hkappa : 0 < kappa) (hinit : R ≤ r + kappa * tau ^ 2)
    (halpha : 0 < alpha) (hdom : 2 * kappa * tau + B ≤ alpha * m)
    (hgrad_lower : ∀ t ∈ Set.Icc 0 tau, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        m ≤ (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) rho x)
          (gradientFun (I := I) (G.metric t) rho x))
    (hheat_upper : ∀ t ∈ Set.Icc 0 tau, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        heatOperatorWithDrift (I := I) G t
          (fun y => (0 : TangentSpace I y)) rho x ≤ B)
    (hu_nonneg : ∀ t ∈ Set.Icc 0 tau,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R}, 0 ≤ u t x)
    (hu_inner : ∀ t ∈ Set.Icc 0 tau,
      ∀ x ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R},
        rho x = r → eta ≤ u t x)
    {p : M}
    (hp : p ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R})
    (hp_outer : rho p = R)
    (hgrad_boundary : 0 < (G.metric tau).inner p
      (gradientFun (I := I) (G.metric tau) rho p)
      (gradientFun (I := I) (G.metric tau) rho p))
    (hu_zero : u tau p = 0) :
    (G.metric tau).inner p
      (gradientFun (I := I) (G.metric tau) (u tau) p)
      (levelSetOutwardNormal (I := I) (G.metric tau) rho p) < 0 := by
  exact heat_pot_hopf_boundary_point_on_compact_annulus
    (I := I) G hS (fun _ _ => 0) u hsol htau 0 rho hrho hr hrR heta hK
    hkappa hinit halpha hdom hgrad_lower hheat_upper
    (fun _ _ _ _ => le_rfl) hu_nonneg hu_inner hp hp_outer
    hgrad_boundary hu_zero

end

end DifferentialGeometry.Analysis.Parabolic
