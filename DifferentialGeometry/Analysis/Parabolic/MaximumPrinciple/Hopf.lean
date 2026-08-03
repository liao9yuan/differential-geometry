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

theorem scalar_hopf_boundary_point_of_subsolution_on_compact_annulus
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
    (hu_nonpos : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R}, u t x ≤ 0)
    (hu_inner : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R},
        rho x = r → u t x ≤ -eta)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_sub : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        parabolicOperatorWithDrift (I := I) G T X u t x ≤ 0)
    {p : M}
    (hp : p ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R})
    (hp_outer : rho p = R)
    (hgrad_boundary : 0 < (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) rho p)
      (gradientFun (I := I) (G.metric T) rho p))
    (hu_zero : u T p = 0) :
    0 < (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) (u T) p)
      (levelSetOutwardNormal (I := I) (G.metric T) rho p) := by
  let w : Real → M → Real := fun t x => -u t x
  have hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}) := by
    simpa [w] using hu_cont.neg
  have hw_nonneg : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R}, 0 ≤ w t x := by
    intro t ht x hx
    exact neg_nonneg.mpr (hu_nonpos t ht x hx)
  have hw_inner : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R},
        rho x = r → eta ≤ w t x := by
    intro t ht x hx hrho_x
    dsimp [w]
    linarith [hu_inner t ht x hx hrho_x]
  have hw_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => w s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    simpa [w] using (hu_time t ht htpos x).neg
  have hw_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (w t) x := by
    intro t ht htpos x
    simpa [w] using (hu_mdiff t ht htpos x).neg
  have hw_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x := by
    intro t ht htpos x
    have heq :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (w t) y) =
          (T% fun y : M => -gradientFun (I := I) (G.metric t) (u t) y) := by
      funext y
      apply congrArg (fun q =>
        (⟨y, q⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      exact gradientFun_neg (I := I) (G.metric t)
        (hu_mdiff t ht htpos y)
    rw [heq]
    exact mdifferentiableAt_neg_section (hu_grad t ht htpos x)
  have hw_super : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        0 ≤ parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht htpos x hx
    have hneg := parabolic_neg (I := I) G T X u t x
      (hu_time t ht htpos x) (hu_mdiff t ht htpos) (hu_grad t ht htpos x)
    change parabolicOperatorWithDrift (I := I) G T X w t x = _ at hneg
    rw [hneg]
    exact neg_nonneg.mpr (hu_sub t ht htpos x hx)
  have hw_zero : w T p = 0 := by
    simp [w, hu_zero]
  have hhopf :=
    scalar_hopf_boundary_point_of_defining_function_on_compact_annulus
      (I := I) G hT X rho hrho hr hrR heta hK hkappa hinit halpha hdom
      hgrad_lower hheat_upper w hw_cont hw_nonneg hw_inner hw_time
      hw_mdiff hw_grad hw_super hp hp_outer hgrad_boundary hw_zero
  have hgradient :
      gradientFun (I := I) (G.metric T) (w T) p =
        -gradientFun (I := I) (G.metric T) (u T) p := by
    exact gradientFun_neg (I := I) (G.metric T)
      (hu_mdiff T ⟨hT.le, le_rfl⟩ hT p)
  rw [hgradient, map_neg] at hhopf
  change -((G.metric T).inner p
    (gradientFun (I := I) (G.metric T) (u T) p)
    (levelSetOutwardNormal (I := I) (G.metric T) rho p)) < 0 at hhopf
  linarith

theorem scalar_hopf_boundary_comparison_on_compact_annulus
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
    (u v : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}))
    (hv_cont : ContinuousOn (fun p : Real × M => v p.1 p.2)
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}))
    (huv : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R}, u t x ≤ v t x)
    (huv_inner : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R},
        rho x = r → u t x + eta ≤ v t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hv_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => v s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (u t) x)
    (hv_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (v t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hv_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (v t) y) x)
    (hoperator : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        parabolicOperatorWithDrift (I := I) G T X u t x ≤
          parabolicOperatorWithDrift (I := I) G T X v t x)
    {p : M}
    (hp : p ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R})
    (hp_outer : rho p = R)
    (hgrad_boundary : 0 < (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) rho p)
      (gradientFun (I := I) (G.metric T) rho p))
    (huv_eq : u T p = v T p) :
    (G.metric T).inner p
        (gradientFun (I := I) (G.metric T) (v T) p)
        (levelSetOutwardNormal (I := I) (G.metric T) rho p) <
      (G.metric T).inner p
        (gradientFun (I := I) (G.metric T) (u T) p)
        (levelSetOutwardNormal (I := I) (G.metric T) rho p) := by
  let d : Real → M → Real := fun t x => u t x - v t x
  have hd_cont : ContinuousOn (fun p : Real × M => d p.1 p.2)
      (Set.Icc 0 T ×ˢ {x | r ≤ rho x ∧ rho x ≤ R}) := by
    simpa [d] using hu_cont.sub hv_cont
  have hd_nonpos : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ {x | r ≤ rho x ∧ rho x ≤ R}, d t x ≤ 0 := by
    intro t ht x hx
    exact sub_nonpos.mpr (huv t ht x hx)
  have hd_inner : ∀ t ∈ Set.Icc 0 T,
      ∀ x ∈ frontier {x | r ≤ rho x ∧ rho x ≤ R},
        rho x = r → d t x ≤ -eta := by
    intro t ht x hx hrho_x
    dsimp [d]
    linarith [huv_inner t ht x hx hrho_x]
  have hd_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => d s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    simpa [d] using (hu_time t ht htpos x).sub (hv_time t ht htpos x)
  have hd_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (d t) x := by
    intro t ht htpos x
    simpa [d] using (hu_mdiff t ht htpos x).sub (hv_mdiff t ht htpos x)
  have hd_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (d t) y) x := by
    intro t ht htpos x
    have heq :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (d t) y) =
          (T% fun y : M =>
            gradientFun (I := I) (G.metric t) (u t) y -
              gradientFun (I := I) (G.metric t) (v t) y) := by
      funext y
      apply congrArg (fun q =>
        (⟨y, q⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      exact gradientFun_sub (I := I) (G.metric t)
        (hu_mdiff t ht htpos y) (hv_mdiff t ht htpos y)
    rw [heq]
    exact mdifferentiableAt_sub_section
      (hu_grad t ht htpos x) (hv_grad t ht htpos x)
  have hd_sub : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ∀ x ∈ interior {x | r ≤ rho x ∧ rho x ≤ R},
        parabolicOperatorWithDrift (I := I) G T X d t x ≤ 0 := by
    intro t ht htpos x hx
    have hsub := parabolic_sub (I := I) G T X u v t x
      (hu_time t ht htpos x) (hv_time t ht htpos x)
      (hu_mdiff t ht htpos) (hv_mdiff t ht htpos)
      (hu_grad t ht htpos x) (hv_grad t ht htpos x)
    change parabolicOperatorWithDrift (I := I) G T X d t x = _ at hsub
    rw [hsub]
    exact sub_nonpos.mpr (hoperator t ht htpos x hx)
  have hd_zero : d T p = 0 := by
    simp [d, huv_eq]
  have hhopf := scalar_hopf_boundary_point_of_subsolution_on_compact_annulus
    (I := I) G hT X rho hrho hr hrR heta hK hkappa hinit halpha hdom
    hgrad_lower hheat_upper d hd_cont hd_nonpos hd_inner hd_time hd_mdiff
    hd_grad hd_sub hp hp_outer hgrad_boundary hd_zero
  have hgradient :
      gradientFun (I := I) (G.metric T) (d T) p =
        gradientFun (I := I) (G.metric T) (u T) p -
          gradientFun (I := I) (G.metric T) (v T) p := by
    exact gradientFun_sub (I := I) (G.metric T)
      (hu_mdiff T ⟨hT.le, le_rfl⟩ hT p)
      (hv_mdiff T ⟨hT.le, le_rfl⟩ hT p)
  rw [hgradient, map_sub] at hhopf
  change 0 <
    (G.metric T).inner p
        (gradientFun (I := I) (G.metric T) (u T) p)
        (levelSetOutwardNormal (I := I) (G.metric T) rho p) -
      (G.metric T).inner p
        (gradientFun (I := I) (G.metric T) (v T) p)
        (levelSetOutwardNormal (I := I) (G.metric T) rho p) at hhopf
  linarith

end DifferentialGeometry.Integral.Connection
