import DifferentialGeometry.Analysis.Parabolic.Harnack.LiYau

noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Parabolic.Harnack

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem hasDerivAt_inner_self_of_hasDerivAt
    (g : SmoothRiemannianMetric I M) (x : M)
    {G : ℝ → TangentSpace I x} {G' : TangentSpace I x} {t : ℝ}
    (hG : HasDerivAt G G' t) :
    HasDerivAt (fun s => g.inner x (G s) (G s)) (2 * g.inner x G' (G t)) t := by
  have hB := ContinuousLinearMap.hasFDerivAt_of_bilinear
    (B := g.inner x) (f := G) (g := G) (x := t)
    hG.hasFDerivAt hG.hasFDerivAt
  let Gf : ℝ →L[ℝ] TangentSpace I x := ContinuousLinearMap.toSpanSingleton ℝ G'
  have hGf1 : Gf (1 : ℝ) = G' := by
    simp [Gf, ContinuousLinearMap.toSpanSingleton]
  have hder : HasDerivAt (fun s => g.inner x (G s) (G s))
      (((g.inner x).precompR ℝ (G t) Gf +
          (g.inner x).precompL ℝ Gf (G t)) (1 : ℝ)) t := by
    rw [hasDerivAt_iff_hasFDerivAt]
    have hB' : HasFDerivAt (fun s => g.inner x (G s) (G s))
        ((g.inner x).precompR ℝ (G t) Gf +
          (g.inner x).precompL ℝ Gf (G t)) t := by
      simpa [Gf] using hB
    have hL : ContinuousLinearMap.toSpanSingleton ℝ
          (((g.inner x).precompR ℝ (G t) Gf +
            (g.inner x).precompL ℝ Gf (G t)) (1 : ℝ)) =
        ((g.inner x).precompR ℝ (G t) Gf +
          (g.inner x).precompL ℝ Gf (G t)) :=
      ContinuousLinearMap.toSpanSingleton_apply_map_one (R₁ := ℝ)
        (c := ((g.inner x).precompR ℝ (G t) Gf +
          (g.inner x).precompL ℝ Gf (G t)))
    rwa [← hL] at hB'
  have hval : (((g.inner x).precompR ℝ (G t) Gf +
          (g.inner x).precompL ℝ Gf (G t)) (1 : ℝ)) =
      2 * g.inner x G' (G t) := by
    rw [ContinuousLinearMap.add_apply]
    have hr : ((g.inner x).precompR ℝ (G t) Gf) (1 : ℝ) =
        g.inner x (G t) (Gf (1 : ℝ)) := by
      rfl
    have hl : ((g.inner x).precompL ℝ Gf (G t)) (1 : ℝ) =
        g.inner x (Gf (1 : ℝ)) (G t) := by
      rfl
    rw [hr, hl, hGf1]
    rw [g.symm x (G t) G']
    ring
  rwa [hval] at hder

omit [T2Space M] [SigmaCompactSpace M] in
theorem normGradSq_timeDeriv_of_log_heat
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {t : ℝ} (x : M) :
    HasDerivAt (fun s : ℝ =>
        g.inner x (gradientFun (I := I) g (fun y => Real.log (u s y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u s y)) x))
      (2 * g.inner x
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g
            (fun y => deriv (fun σ : ℝ => Real.log (u σ y)) t) x)) t := by
  classical
  let f : ℝ → M → ℝ := fun s y => Real.log (u s y)
  let hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) := by
    simpa [f] using
      DifferentialGeometry.Analysis.Parabolic.Moser.contMDiff_log_of_pos hu hpos
  have hgrad := gradientFun_time_deriv g f hf (t := t) (x := x)
  have hmain := hasDerivAt_inner_self_of_hasDerivAt g x
    (G := fun s => gradientFun (I := I) g (f s) x)
    (G' := gradientFun (I := I) g (fun y => deriv (fun σ : ℝ => f σ y) t) x) hgrad
  simpa [f, g.symm] using hmain

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem gradientFun_add
    (g : SmoothRiemannianMetric I M) {f h : M → ℝ} (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x) :
    gradientFun (I := I) g (f + h) x = gradientFun (I := I) g f x + gradientFun (I := I) g h x := by
  simpa using (DifferentialGeometry.Integral.DivergenceTheorem.gradFun_add g hf hh)


theorem normGradSq_log_heat_evolution_identity
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (hpde : ∀ t x, deriv (fun s => u s x) t =
      Δ_g g (smoothScalarSlice (I := I) g u hu t).smooth x)
    {t : ℝ} (x : M)
    (hN : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => g.inner p.2
        (gradientFun (I := I) g (fun y => Real.log (u p.1 y)) p.2)
        (gradientFun (I := I) g (fun y => Real.log (u p.1 y)) p.2))) :
    deriv (fun s : ℝ =>
        g.inner x (gradientFun (I := I) g (fun y => Real.log (u s y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u s y)) x)) t -
      Δ_g g (smoothScalarSlice (I := I) g
        (fun s y => g.inner y (gradientFun (I := I) g (fun z => Real.log (u s z)) y)
          (gradientFun (I := I) g (fun z => Real.log (u s z)) y)) hN t).smooth x =
      2 * g.inner x (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => g.inner y
            (gradientFun (I := I) g (fun z => Real.log (u t z)) y)
            (gradientFun (I := I) g (fun z => Real.log (u t z)) y)) x) -
        2 * chartHessFrobeniusSq (I := I) g (fun y => Real.log (u t y)) x -
        2 * ricciTensor (I := I) g x (gradFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradFun (I := I) g (fun y => Real.log (u t y)) x) := by
  classical
  let f : ℝ → M → ℝ := fun s y => Real.log (u s y)
  let hlog : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) := by
    simpa [f] using
      DifferentialGeometry.Analysis.Parabolic.Moser.contMDiff_log_of_pos hu hpos
  have hslice : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => f t y) := by
    have harg : ContMDiff I ((𝓘(ℝ, ℝ)).prod I) ∞ (fun y : M => (t, y)) :=
      (contMDiff_const (c := t) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => t)).prodMk
        (contMDiff_id : ContMDiff I I ∞ (fun y : M => y))
    simpa [f] using hlog.comp harg
  let N : ℝ → M → ℝ := fun s y => g.inner y
        (gradientFun (I := I) g (fun z => Real.log (u s z)) y)
        (gradientFun (I := I) g (fun z => Real.log (u s z)) y)
  have hNt := DifferentialGeometry.Analysis.Parabolic.Harnack.normGradSq_timeDeriv_of_log_heat
    g u hu hpos (t := t) x
  have hder_N : deriv (fun s : ℝ => N s x) t =
      2 * g.inner x (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
        (gradientFun (I := I) g (fun y => deriv (fun σ : ℝ => Real.log (u σ y)) t) x) := by
    simpa [N] using hNt.deriv
  have hlog_ev : ∀ s y,
      deriv (fun σ : ℝ => Real.log (u σ y)) s =
        Δ_g g (smoothScalarSlice (I := I) g (fun σ z => Real.log (u σ z)) hlog s).smooth y +
          N s y := by
    intro s y
    have h := DifferentialGeometry.Analysis.Parabolic.Harnack.heatSolution_log_evolution
      g u hu hpos (hpde s y)
    simpa [N, f] using h
  have hNslice_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (N t) x :=
    (hN.comp (contMDiff_const.prodMk (contMDiff_id : ContMDiff I I ∞ (fun y : M => y)))).mdifferentiableAt
      (x := x) (by norm_num)
  have hdel_cd : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => Δ_g g (smoothScalarSlice (I := I) g (fun σ z => Real.log (u σ z)) hlog t).smooth y) := by
    simpa using (Δ_g_contMDiff (I := I) g
      (hlog.comp (contMDiff_const.prodMk (contMDiff_id : ContMDiff I I ∞ (fun y : M => y)))))
  have hDel_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => Δ_g g (smoothScalarSlice (I := I) g (fun σ z => Real.log (u σ z)) hlog t).smooth y) x :=
    hdel_cd.mdifferentiableAt (x := x) (by norm_num)
  have hgrad_ft : gradientFun (I := I) g
        (fun y => deriv (fun σ : ℝ => Real.log (u σ y)) t) x =
      gradientFun (I := I) g
          (fun y : M => Δ_g g (smoothScalarSlice (I := I) g (fun σ z => Real.log (u σ z)) hlog t).smooth y) x +
        gradientFun (I := I) g (N t) x := by
    have hfun : (fun y : M => deriv (fun σ : ℝ => Real.log (u σ y)) t) =
        (fun y : M => Δ_g g (smoothScalarSlice (I := I) g (fun σ z => Real.log (u σ z)) hlog t).smooth y +
          N t y) := by
      funext y
      exact hlog_ev t y
    rw [hfun]
    exact gradientFun_add g x hDel_mdiff hNslice_mdiff
  have hbochner := DifferentialGeometry.Integral.Connection.bochner_pointwise_grad_normSq_of_boundaryless
    (I := I) g hslice x
  have hbochner' : Δ_g g (smoothScalarSlice (I := I) g N hN t).smooth x =
      2 * frobeniusSq_grad_vector (I := I) g (fun b => gradFun (I := I) g (fun y => f t y) b) x +
        2 * ricciTensor (I := I) g x (gradFun (I := I) g (fun y => f t y) x) (gradFun (I := I) g (fun y => f t y) x) +
        2 * g.inner x (gradFun (I := I) g (fun y => f t y) x) (gradFun (I := I) g (Δ_g (I := I) g hslice) x) := by
    have hcongr : Δ_g g (smoothScalarSlice (I := I) g N hN t).smooth x =
        Δ_g g (normGradSqFun_contMDiff (I := I) g hslice) x := by
      refine Δ_g_congr_of_eventuallyEq (I := I) g (smoothScalarSlice (I := I) g N hN t).smooth
        (normGradSqFun_contMDiff (I := I) g hslice) ?_
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      intro y hy
      simp [N, f, normGradSqFun]
      rfl
    exact hcongr.trans hbochner
  have hmain : deriv (fun s : ℝ => N s x) t -
        Δ_g g (smoothScalarSlice (I := I) g N hN t).smooth x =
      2 * g.inner x (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (N t) x) -
        2 * frobeniusSq_grad_vector (I := I) g (fun b => gradFun (I := I) g (fun y => f t y) b) x -
        2 * ricciTensor (I := I) g x (gradFun (I := I) g (fun y => f t y) x)
          (gradFun (I := I) g (fun y => f t y) x) := by
    rw [hder_N]
    rw [hgrad_ft]
    rw [hbochner']
    rw [map_add]
    have hΔf_eq : g.inner x (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => Δ_g g (smoothScalarSlice (I := I) g (fun σ z => Real.log (u σ z)) hlog t).smooth y) x) =
        g.inner x (gradFun (I := I) g (fun y => f t y) x) (gradFun (I := I) g (Δ_g (I := I) g hslice) x) := by
      rfl
    rw [hΔf_eq]
    ring
  have hfrob : frobeniusSq_grad_vector (I := I) g (fun b => gradFun (I := I) g (fun y => f t y) b) x =
      chartHessFrobeniusSq (I := I) g (fun y => Real.log (u t y)) x := by
    simpa [f] using (frobeniusSq_grad_vector_eq_chartHessFrobeniusSq (I := I) g hslice x)
  rw [hfrob] at hmain
  simpa [f, N] using hmain

end DifferentialGeometry.Analysis.Parabolic.Harnack

end
