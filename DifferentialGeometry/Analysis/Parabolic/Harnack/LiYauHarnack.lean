import DifferentialGeometry.Analysis.Parabolic.Harnack.LiYau
import DifferentialGeometry.Analysis.Parabolic.Harnack.PathIntegration

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Harnack

open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M]

theorem heat_solution_one_point_harnack_of_nonnegative_ricci
    [CompactSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle (⊤ : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hRic : ∀ x v, 0 ≤ ricciTensor (I := I) g x v v)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (hpde : ∀ t x, deriv (fun s => u s x) t =
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : M) :
    u a x ≤ (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) * u b x := by
  classical
  let n : ℝ := (Module.finrank ℝ E : ℝ)
  have hly_all : ∀ t : ℝ, 0 < t →
      liYauQuantity g (fun τ y => Real.log (u τ y)) t x ≤ n / (2 * t) :=
    fun t ht => by
      simpa [n] using liYau_estimate_of_nonnegative_ricci (I := I) (M := M) g hRic u hu hpos hpde ht x
  have hliYau_bound : ∀ t ∈ Set.Icc a b,
      -(n / 2 / t) ≤ deriv (fun s => u s x) t / u t x := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    have hly := hly_all t htpos
    have hlogderiv : deriv (fun s => Real.log (u s x)) t = deriv (fun s => u s x) t / u t x := by
      have hu_slice : ContDiff ℝ ∞ (fun s => u s x) := by
        have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞ (fun s : ℝ => (s, x)) :=
          contMDiff_id.prodMk contMDiff_const
        exact contMDiff_iff_contDiff.mp (hu.comp hc)
      have hder : HasDerivAt (fun s => u s x) (deriv (fun s => u s x) t) t :=
        (ContDiff.differentiable hu_slice (by norm_num) t).hasDerivAt
      exact (hder.log (hpos t x).ne').deriv
    have hq_nonneg_grad : 0 ≤ g.inner x
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x) := by
      let v : TangentSpace I x := gradientFun (I := I) g (fun y => Real.log (u t y)) x
      have hvnonneg : 0 ≤ g.inner x v v := by
        by_cases hv : v = 0
        · rw [hv]
          simp
        · exact le_of_lt (g.pos x v hv)
      simpa [v] using hvnonneg
    have hq : liYauQuantity g (fun τ y => Real.log (u τ y)) t x =
        g.inner x (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x) -
          deriv (fun s => Real.log (u s x)) t := rfl
    have hstep : -(n / (2 * t)) ≤ deriv (fun s => Real.log (u s x)) t := by
      rw [hq] at hly
      have hgrad_le : 0 ≤ g.inner x
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x) := hq_nonneg_grad
      linarith
    rw [hlogderiv] at hstep
    have hrewrite : n / (2 * t) = n / 2 / t := by
      field_simp [htpos.ne']
    rw [hrewrite] at hstep
    simpa using hstep
  have hu_path_pos : ∀ t ∈ Set.Icc a b, 0 < u t x := fun t ht => hpos t x
  have hderivative_cont : ContinuousOn (fun t : ℝ => deriv (fun s => u s x) t) (Set.Icc a b) := by
    have hu_slice : ContDiff ℝ ∞ (fun s => u s x) := by
      have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞ (fun s : ℝ => (s, x)) :=
        contMDiff_id.prodMk contMDiff_const
      exact contMDiff_iff_contDiff.mp (hu.comp hc)
    have hder_cont : Continuous (fun t : ℝ => deriv (fun s => u s x) t) :=
      ContDiff.iterate_deriv 1 hu_slice |>.continuous
    exact hder_cont.continuousOn
  have hu_path_deriv : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun s : ℝ => u s x) (deriv (fun s => u s x) t) t := by
    intro t ht
    have hu_slice : ContDiff ℝ ∞ (fun s => u s x) := by
      have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞ (fun s : ℝ => (s, x)) :=
        contMDiff_id.prodMk contMDiff_const
      exact contMDiff_iff_contDiff.mp (hu.comp hc)
    exact (ContDiff.differentiable hu_slice (by norm_num) t).hasDerivAt
  have hbridge := harnack_endpoint_of_li_yau_bound
    (V := ℝ) (u := fun t : ℝ => u t x)
    (derivative := fun t : ℝ => deriv (fun s => u s x) t)
    (timePart := fun t : ℝ => deriv (fun s => u s x) t / u t x)
    (gradient := fun _ : ℝ => (0 : ℝ))
    (velocity := fun _ : ℝ => (0 : ℝ))
    (a := a) (b := b) (c := n / 2) (alpha := (1 : ℝ))
    (by norm_num) ha hab hu_path_pos hderivative_cont continuousOn_const
    hu_path_deriv (by intro t ht; simp) (by
      intro t ht
      simpa using hliYau_bound t ht)
  simpa [n] using hbridge

end DifferentialGeometry.Analysis.Parabolic.Harnack

end
