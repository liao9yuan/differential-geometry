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

end DifferentialGeometry.Analysis.Parabolic.Harnack

end
