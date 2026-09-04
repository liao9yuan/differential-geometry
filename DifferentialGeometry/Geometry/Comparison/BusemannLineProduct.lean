import DifferentialGeometry.Geometry.Comparison.BusemannLineFlow
import DifferentialGeometry.Topology.Morse.RegularLevel
import DifferentialGeometry.Topology.Morse.RegularSublevel

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold Topology

namespace DifferentialGeometry

open Geometry.Operator
open Geometry.Riemannian
open Geometry.Riemannian.BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The zero level of the forward Busemann function, crossed with time, is in
bijection with the ambient manifold by the complete Busemann-gradient flow. -/
noncomputable def busemannProdEquiv
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    {x : M // busemann (I := I) γ x = 0} × ℝ ≃ M where
  toFun := fun p ↦
    busemannFlow (I := I) g hEnorm hγ hd hRic (-p.2) p.1.1
  invFun := fun y ↦
    (⟨busemannFlow (I := I) g hEnorm hγ hd hRic
        (-(busemann (I := I) γ y)) y, by
      rw [busemannFlow_value (I := I) g hEnorm hγ hd hRic]
      ring⟩,
      -(busemann (I := I) γ y))
  left_inv := by
    rintro ⟨z, t⟩
    have hb :
        busemann (I := I) γ
            (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1) = -t := by
      rw [busemannFlow_value (I := I) g hEnorm hγ hd hRic, z.2, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change busemannFlow (I := I) g hEnorm hγ hd hRic
          (-(busemann (I := I) γ
            (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1)))
          (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1) = z.1
      rw [hb, neg_neg]
      calc
        busemannFlow (I := I) g hEnorm hγ hd hRic t
              (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1) =
            busemannFlow (I := I) g hEnorm hγ hd hRic ((-t) + t) z.1 :=
          (busemannFlow_add (I := I) g hEnorm hγ hd hRic z.1 (-t) t).symm
        _ = z.1 := by rw [neg_add_cancel, busemannFlow_zero]
    · change -(busemann (I := I) γ
          (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1)) = t
      rw [hb, neg_neg]
  right_inv := by
    intro y
    change busemannFlow (I := I) g hEnorm hγ hd hRic
        (-(-(busemann (I := I) γ y)))
        (busemannFlow (I := I) g hEnorm hγ hd hRic
          (-(busemann (I := I) γ y)) y) = y
    rw [neg_neg]
    calc
      busemannFlow (I := I) g hEnorm hγ hd hRic
            (busemann (I := I) γ y)
            (busemannFlow (I := I) g hEnorm hγ hd hRic
              (-(busemann (I := I) γ y)) y) =
          busemannFlow (I := I) g hEnorm hγ hd hRic
            (-(busemann (I := I) γ y) + busemann (I := I) γ y) y :=
        (busemannFlow_add (I := I) g hEnorm hγ hd hRic y
          (-(busemann (I := I) γ y)) (busemann (I := I) γ y)).symm
      _ = y := by rw [neg_add_cancel, busemannFlow_zero]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The raw zero level of the forward Busemann function, crossed with time, is
homeomorphic to the ambient manifold by the complete Busemann-gradient flow. -/
noncomputable def busemannProdHomeo
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    {x : M // busemann (I := I) γ x = 0} × ℝ ≃ₜ M where
  toEquiv := busemannProdEquiv (I := I) g hEnorm hγ hd hRic
  continuous_toFun := by
    exact (busemannFlow_smooth (I := I) g hEnorm hγ hd hRic).continuous.comp
      ((continuous_neg.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst))
  continuous_invFun := by
    have hb : Continuous (busemann (I := I) γ) :=
      (busemann_smooth (I := I) g hEnorm hγ hd hRic).continuous
    have ht : Continuous (fun y : M ↦ -(busemann (I := I) γ y)) :=
      continuous_neg.comp hb
    have hflow : Continuous (fun y : M ↦
        busemannFlow (I := I) g hEnorm hγ hd hRic
          (-(busemann (I := I) γ y)) y) :=
      (busemannFlow_smooth (I := I) g hEnorm hγ hd hRic).continuous.comp
        (ht.prodMk continuous_id)
    exact (Continuous.subtype_mk hflow (fun y ↦ by
      rw [busemannFlow_value (I := I) g hEnorm hγ hd hRic]
      ring)).prodMk ht

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The differential of the forward Busemann function is nonzero everywhere. -/
theorem busemann_deriv_ne
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (x : M) :
    mfderiv I 𝓘(ℝ, ℝ) (busemann (I := I) γ) x ≠ 0 := by
  classical
  letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  intro hcrit
  have hb := busemann_smooth (I := I) g hEnorm hγ hd hRic
  have hunit :
      g.inner x
          (gradientFun (I := I) g (busemann (I := I) γ) x)
          (gradientFun (I := I) g (busemann (I := I) γ) x) = 1 :=
    busemann_grad_sq (I := I) g hEnorm hγ.pos_ray x
      (hb.contMDiffAt.mdifferentiableAt (by simp))
  have hzero :
      g.inner x
          (gradientFun (I := I) g (busemann (I := I) γ) x)
          (gradientFun (I := I) g (busemann (I := I) γ) x) = 0 := by
    rw [inner_gradientFun (I := I) g, hcrit]
    rfl
  exact one_ne_zero (hunit.symm.trans hzero)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The regular zero level of the forward Busemann function, crossed with time, is smoothly
equivalent to the ambient manifold by the complete Busemann-gradient flow. -/
noncomputable def busemannProdDiffeo
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0)
    {m : ℕ} (e : E ≃L[ℝ] Topology.Morse.MorseModel (m + 1)) :
    let b : M → ℝ := busemann (I := I) γ
    let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
      I.transContinuousLinearEquiv e
    letI : J.Boundaryless := by
      constructor
      change Set.range (I.transContinuousLinearEquiv e) = Set.univ
      rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
        Set.image_univ]
      exact Set.range_eq_univ.mpr e.surjective
    letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
      dsimp [J]
      infer_instance
    let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
      exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
        (I := I) (e := e)).2 (busemann_smooth (I := I) g hEnorm hγ hd hRic)
    let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
      intro x _ hx
      exact busemann_deriv_ne (I := I) g hEnorm hγ hd hRic x
        ((Topology.Morse.isCrit_trans_iff I e b x).1 hx)
    letI : ChartedSpace (Topology.Morse.MorseModel m)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
    letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
    (Topology.Morse.LevelSetSpace b 0 × ℝ) ≃ₘ^((⊤ : ℕ∞) : WithTop ℕ∞)⟮
      (𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ), I⟯ M :=
  let b : M → ℝ := busemann (I := I) γ
  let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
    I.transContinuousLinearEquiv e
  letI : J.Boundaryless := by
    constructor
    change Set.range (I.transContinuousLinearEquiv e) = Set.univ
    rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
      Set.image_univ]
    exact Set.range_eq_univ.mpr e.surjective
  letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
    dsimp [J]
    infer_instance
  let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
      (I := I) (e := e)).2 (busemann_smooth (I := I) g hEnorm hγ hd hRic)
  let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
    intro x _ hx
    exact busemann_deriv_ne (I := I) g hEnorm hγ hd hRic x
      ((Topology.Morse.isCrit_trans_iff I e b x).1 hx)
  letI : ChartedSpace (Topology.Morse.MorseModel m)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
  letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
  { toEquiv := busemannProdEquiv (I := I) g hEnorm hγ hd hRic
    contMDiff_toFun := by
      have hlevelJ : ContMDiff (𝓘(ℝ, Topology.Morse.MorseModel m)) J
          ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : Topology.Morse.LevelSetSpace b 0 => x.1) :=
        Topology.Morse.contMDiff_levelSetInclusion J b 0 hbJ hregJ
      have hlevelI : ContMDiff (𝓘(ℝ, Topology.Morse.MorseModel m)) I
          ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : Topology.Morse.LevelSetSpace b 0 => x.1) :=
        (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right
          (I := I) (e := e)).1 hlevelJ
      have htime : ContMDiff
          ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
          ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : Topology.Morse.LevelSetSpace b 0 × ℝ => -p.2) :=
        contMDiff_snd.neg
      have hbase : ContMDiff
          ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
          ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : Topology.Morse.LevelSetSpace b 0 × ℝ => p.1.1) :=
        hlevelI.comp contMDiff_fst
      exact (busemannFlow_smooth (I := I) g hEnorm hγ hd hRic).comp
        (htime.prodMk hbase)
    contMDiff_invFun := by
      have hbI : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b :=
        busemann_smooth (I := I) g hEnorm hγ hd hRic
      have htime : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M => -b y) := hbI.neg
      let F : M → M := fun y =>
        busemannFlow (I := I) g hEnorm hγ hd hRic (-b y) y
      have hFI : ContMDiff I I ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
        exact (busemannFlow_smooth (I := I) g hEnorm hγ hd hRic).comp
          (htime.prodMk contMDiff_id)
      have hFJ : ContMDiff I J ((⊤ : ℕ∞) : WithTop ℕ∞) F :=
        (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right
          (I := I) (e := e)).2 hFI
      have hFzero : ∀ y : M, b (F y) = 0 := by
        intro y
        dsimp [F, b]
        rw [busemannFlow_value (I := I) g hEnorm hγ hd hRic]
        ring
      have hfirst : ContMDiff I (𝓘(ℝ, Topology.Morse.MorseModel m))
          ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M =>
            (⟨F y, hFzero y⟩ : Topology.Morse.LevelSetSpace b 0)) :=
        Topology.Morse.contMDiff_levelSet_factor J b 0 hbJ hregJ F hFJ hFzero
      exact hfirst.prodMk htime }

end DifferentialGeometry
