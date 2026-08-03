import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Strong
import DifferentialGeometry.Geometry.Boundary.DefiningFunctionCurve

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem scalar_hopf_boundary_point_of_defining_function_on_compact_annulus
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (rho : M → Real)
    (hrho : ContMDiff I (modelWithCornersSelf Real Real) ∞ rho)
    {r R eta m B kappa alpha : Real}
    (hr : 0 ≤ r) (hrR : r < R) (heta : 0 < eta)
    (hK : IsCompact {x | r ≤ rho x ∧ rho x ≤ R})
    (hkappa : 0 < kappa) (hinit : R ≤ r + kappa * T ^ 2)
    (halpha : 0 < alpha) (hdom : 2 * kappa * T + B ≤ alpha * m)
    (hgrad_lower : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        m ≤ (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) rho x)
          (gradientFun (I := I) (G.metric t) rho x))
    (hheat_upper : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        heatOperatorWithDrift (I := I) G t (X t) rho x ≤ B)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R}, 0 ≤ u t x)
    (hu_inner : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R},
        rho x = r → eta ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x)
    {p : M}
    (hp : p ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R})
    (hp_outer : rho p = R)
    (hgrad_boundary : 0 < (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) rho p)
      (gradientFun (I := I) (G.metric T) rho p))
    (hu_zero : u T p = 0) :
    (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) (u T) p)
      (levelSetOutwardNormal (I := I) (G.metric T) rho p) < 0 := by
  let K : Set M := {x | r ≤ rho x ∧ rho x ≤ R}
  change IsCompact K at hK
  change p ∈ frontier K at hp
  have hpK : p ∈ K := by
    have hpcl : p ∈ closure K := frontier_subset_closure hp
    rw [hK.isClosed.closure_eq] at hpcl
    exact hpcl
  have hKne : K.Nonempty := ⟨p, hpK⟩
  have hgrad_ne : gradientFun (I := I) (G.metric T) rho p ≠ 0 := by
    intro hzero
    rw [hzero] at hgrad_boundary
    simp at hgrad_boundary
  obtain ⟨a, ha, gamma, hgamma0, hgamma, hgamma_mdiff,
      hgamma_velocity⟩ :=
    exists_levelSet_inward_curve_of_gradient_ne_zero (I := I)
      (G.metric T) rho (hrho.mdifferentiable (by simp) p)
      hrR hp_outer hgrad_ne
  exact scalar_hopf_boundary_point_of_defining_function (I := I)
    G hT X hK hKne rho hrho hr heta (by
      intro x hx
      exact hx) (frontier_levelSet_annulus_subset hrho.continuous)
      hkappa hinit halpha hdom hgrad_lower
      hheat_upper u hu_cont hu_nonneg hu_inner hu_time hu_mdiff hu_grad
      hu_super hp hp_outer hgrad_boundary gamma ha hgamma0 hgamma
      hgamma_mdiff hgamma_velocity hu_zero

end DifferentialGeometry.Integral.Connection
