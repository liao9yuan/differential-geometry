import DifferentialGeometry.Analysis.Parabolic.Moser.LogEnergy
import DifferentialGeometry.Analysis.Calculus.TimeJetCommute
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Operator.Operators
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.TangentAction
import DifferentialGeometry.Analysis.Integration.Measure.Invariance

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Harnack

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M]

theorem heatSolution_log_evolution
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {t : ℝ} {x : M}
    (hpde : deriv (fun s => u s x) t =
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x) :
    deriv (fun s => Real.log (u s x)) t =
      Δ_g (I := I) g
        (smoothScalarSlice (I := I) g (fun s y => Real.log (u s y))
          (Moser.contMDiff_log_of_pos hu hpos) t).smooth x +
      g.inner x
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x) := by
  classical
  let ut := smoothScalarSlice (I := I) g u hu t
  let hlog := Moser.contMDiff_log_of_pos hu hpos
  let logut := smoothScalarSlice (I := I) g (fun s y => Real.log (u s y)) hlog t
  have htime : ContDiff ℝ ∞ (fun s => u s x) :=
    contMDiff_iff_contDiff.mp (hu.comp (contMDiff_id.prodMk contMDiff_const))
  have htime_deriv :
      deriv (fun s => Real.log (u s x)) t =
        (u t x)⁻¹ * deriv (fun s => u s x) t := by
    exact ((Real.hasDerivAt_log (hpos t x).ne').comp t
      ((htime.differentiable (by norm_num)).differentiableAt.hasDerivAt)).deriv
  have hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g ut.toFun y) x :=
    (grad_g (I := I) g ut.smooth).mdifferentiable x
  have hlap_raw := laplacian_log (I := I)
    (LeviCivita (I := I) g) g
    (fun y => ut.smooth.mdifferentiable (by simp) y)
    (fun y => hpos t y) hgrad
  have hlap :
      Δ_g (I := I) g logut.smooth x =
        (u t x)⁻¹ * Δ_g (I := I) g ut.smooth x -
          (u t x ^ 2)⁻¹ *
            g.inner x (gradientFun (I := I) g ut.toFun x)
              (gradientFun (I := I) g ut.toFun x) := by
    rw [← laplacian_levi_eq (I := I) g logut.smooth x,
      ← laplacian_levi_eq (I := I) g ut.smooth x]
    simpa only [ut, logut, smoothScalarSlice_toFun] using hlap_raw
  have hloggrad := Moser.inner_gradientFun_log_self (I := I) g
    (ut.smooth.mdifferentiable (by simp) x) (hpos t x)
  have hloggrad' :
      g.inner x
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x) =
        (u t x ^ 2)⁻¹ *
          g.inner x (gradientFun (I := I) g ut.toFun x)
            (gradientFun (I := I) g ut.toFun x) := by
    simpa only [ut, smoothScalarSlice_toFun] using hloggrad
  calc
    deriv (fun s => Real.log (u s x)) t
        = (u t x)⁻¹ * deriv (fun s => u s x) t := htime_deriv
    _ = (u t x)⁻¹ * Δ_g (I := I) g ut.smooth x := by rw [hpde]
    _ = Δ_g (I := I) g logut.smooth x +
        g.inner x
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x) := by
      rw [hlap, hloggrad']
      ring

theorem liYauQuantity_eq_neg_laplacian_log
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {t : ℝ} {x : M}
    (hpde : deriv (fun s => u s x) t =
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x) :
    g.inner x
          (gradientFun (I := I) g (fun y : M => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y : M => Real.log (u t y)) x) -
        deriv (fun s : ℝ => Real.log (u s x)) t =
      -Δ_g (I := I) g
        (smoothScalarSlice (I := I) g (fun s : ℝ => fun y : M => Real.log (u s y))
          (Moser.contMDiff_log_of_pos hu hpos) t).smooth x := by
  have h := heatSolution_log_evolution (I := I) (M := M) g u hu hpos hpde
  rw [h]
  ring

omit [T2Space M] in
theorem gradientFun_time_deriv
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {t : ℝ} {x : M} :
    HasDerivAt (fun s : ℝ => gradientFun (I := I) g (u s) x)
      (gradientFun (I := I) g (fun y : M => deriv (fun s : ℝ => u s y) t) x) t := by
  classical
  set α : M := x with hα
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I) α]
    exact mem_chart_source H α
  have hxsrc : x ∈ (chartAt H α).source := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I) α] at hxbase
    exact hxbase
  have hxextsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I) α]
    exact hxsrc
  have hxtarget : (extChartAt I α) x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxextsrc
  have hxint : (extChartAt I α) x ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hxtarget
  have hΦ : ContDiffAt ℝ ∞
      (fun r : ℝ × E => scalarOnE (I := I) α (u r.1) r.2) (t, (extChartAt I α) x) := by
    have hua : ContMDiffAt ((𝓘(ℝ, ℝ).prod I)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => u p.1 p.2) (t, x) := hu (t, x)
    have hiff := contMDiffAt_iff (I := (𝓘(ℝ, ℝ).prod I)) (I' := 𝓘(ℝ, ℝ))
      (n := ∞) (f := fun p : ℝ × M => u p.1 p.2) (x := (t, x))
    rcases hiff.mp hua with ⟨_, hcd⟩
    have hcd' : ContDiffWithinAt ℝ ∞
        (fun r : ℝ × E => u r.1 ((extChartAt I α).symm r.2))
        Set.univ (t, (extChartAt I α) x) := by
      have hprod : extChartAt ((𝓘(ℝ, ℝ).prod I)) (t, x) =
          (extChartAt 𝓘(ℝ, ℝ) t).prod (extChartAt I x) :=
        extChartAt_prod (x := (t, x))
      have hself : extChartAt 𝓘(ℝ, ℝ) (u t x) = PartialEquiv.refl ℝ := by
        simp [extChartAt]
      have hcomp_eq : (extChartAt 𝓘(ℝ, ℝ) (u t x) ∘ (fun p : ℝ × M => u p.1 p.2) ∘
          (extChartAt ((𝓘(ℝ, ℝ).prod I)) (t, x)).symm) =
          (fun r : ℝ × E => u r.1 ((extChartAt I α).symm r.2)) := by
        funext r
        simp only [hself, hprod, Function.comp_def, α,
          PartialEquiv.prod_coe_symm, extChartAt_coe_symm,
          modelWithCornersSelf_coe_symm]
        change u r.1 ((extChartAt I α).symm r.2) = u r.1 ((extChartAt I α).symm r.2)
        rfl
      have hrange : range ((𝓘(ℝ, ℝ).prod I)) = Set.univ := by
        have hI : range I = Set.univ := ModelWithCorners.range_eq_univ I
        apply Set.Subset.antisymm
        · intro y hy
          trivial
        · intro y hy
          have hy2 : y.2 ∈ range I := by
            rw [hI]
            trivial
          rcases hy2 with ⟨x₂, hx₂⟩
          exact ⟨(y.1, x₂), by simp [hx₂]⟩
      rw [hcomp_eq] at hcd
      have hbase : (extChartAt ((𝓘(ℝ, ℝ).prod I)) (t, x)) (t, x) =
          (t, (extChartAt I α) x) := by
        simp [α]
      rw [hrange, hbase] at hcd
      exact hcd
    exact (contDiffWithinAt_univ.mp hcd')
  have hpd : ∀ j : Fin (Module.finrank ℝ E),
      HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) j (scalarOnE (I := I) α (u s))
          ((extChartAt I α) x))
        (partialDeriv (E := E) j (scalarOnE (I := I) α
          (fun y : M => deriv (fun s : ℝ => u s y) t)) ((extChartAt I α) x)) t := by
    intro j
    have hc := fderiv_deriv_hasDerivAt_comm
      (fun r : ℝ × E => scalarOnE (I := I) α (u r.1) r.2) t
      ((extChartAt I α) x) (chartModelBasis E j) hΦ
    have hc1 : HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) j (scalarOnE (I := I) α (u s))
          ((extChartAt I α) x))
        (fderiv ℝ (fun y : E => deriv (fun s : ℝ => scalarOnE (I := I) α (u s) y) t)
          ((extChartAt I α) x) (chartModelBasis E j)) t := by
      simpa [partialDeriv] using hc
    have hfun : (fun y : E => deriv (fun s : ℝ => scalarOnE (I := I) α (u s) y) t) =
        scalarOnE (I := I) α (fun z : M => deriv (fun s : ℝ => u s z) t) := by
      funext y
      rfl
    have hval : fderiv ℝ (fun y : E => deriv (fun s : ℝ => scalarOnE (I := I) α (u s) y) t)
          ((extChartAt I α) x) (chartModelBasis E j) =
        partialDeriv (E := E) j (scalarOnE (I := I) α
          (fun y : M => deriv (fun s : ℝ => u s y) t)) ((extChartAt I α) x) := by
      rw [hfun]
      rfl
    simpa [hval, partialDeriv] using hc1
  have hcoeff : ∀ i : Fin (Module.finrank ℝ E),
      HasDerivAt
        (fun s : ℝ => gradChartCoeff (I := I) g α (u s) i x)
        (gradChartCoeff (I := I) g α
          (fun y : M => deriv (fun s : ℝ => u s y) t) i x) t := by
    intro i
    have hsum : ∀ j : Fin (Module.finrank ℝ E),
        HasDerivAt
          (fun s : ℝ => chartInvGramMatrix (I := I) g α x i j *
            partialDeriv (E := E) j (scalarOnE (I := I) α (u s))
              ((extChartAt I α) x))
          (chartInvGramMatrix (I := I) g α x i j *
            partialDeriv (E := E) j (scalarOnE (I := I) α
              (fun y : M => deriv (fun s : ℝ => u s y) t)) ((extChartAt I α) x)) t := by
        intro j
        exact (hpd j).const_mul (chartInvGramMatrix (I := I) g α x i j)
    have hsumall : HasDerivAt
        (fun s : ℝ => ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α x i j *
            partialDeriv (E := E) j (scalarOnE (I := I) α (u s)) ((extChartAt I α) x))
        (∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α x i j *
            partialDeriv (E := E) j (scalarOnE (I := I) α
              (fun y : M => deriv (fun s : ℝ => u s y) t)) ((extChartAt I α) x)) t := by
      exact HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hsum j)
    simpa [gradChartCoeff_def] using hsumall
  have hsum2 : HasDerivAt
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α (u s) i x • chartBasisVecFiber (I := I) α i x)
      (∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α (fun y : M => deriv (fun s : ℝ => u s y) t) i x •
          chartBasisVecFiber (I := I) α i x) t := by
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (hcoeff i).smul_const (chartBasisVecFiber (I := I) α i x))
  have hcore : HasDerivAt (fun s : ℝ => gradChartLocal (I := I) g α (u s) x)
      (gradChartLocal (I := I) g α
        (fun y : M => deriv (fun s : ℝ => u s y) t) x) t := by
    simpa [gradChartLocal] using hsum2
  have hslice_mdiff : ∀ s : ℝ, MDifferentiableAt I 𝓘(ℝ, ℝ) (u s) x := by
    intro s
    exact (hu.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (x := x) (by simp)
  have hloc_l : ∀ s : ℝ, gradientFun (I := I) g (u s) x =
      gradChartLocal (I := I) g α (u s) x := by
    intro s
    exact (gradChartLocal_eq_gradFun (I := I) g α
      (hf := hslice_mdiff s) hxbase hxint).symm
  have htarget_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => deriv (fun s : ℝ => u s y) t) x := by
    have hcd_slice : ContDiffAt ℝ ∞
        (fun y : E => deriv (fun s : ℝ => scalarOnE (I := I) α (u s) y) t)
        ((extChartAt I α) x) := by
      have hswap : ContDiffAt ℝ ∞ (fun p : E × ℝ => (p.2, p.1))
          ((extChartAt I α) x, t) :=
        contDiffAt_snd.prodMk contDiffAt_fst
      have hf : ContDiffAt ℝ ∞ (Function.uncurry
          (fun (y : E) => fun (s : ℝ) => scalarOnE (I := I) α (u s) y))
          ((extChartAt I α) x, t) := by
        exact hΦ.comp ((extChartAt I α) x, t) hswap
      have hg : ContDiffAt ℝ ∞ (fun _ : E => (t : ℝ)) ((extChartAt I α) x) := contDiffAt_const
      have hfd := ContDiffAt.fderiv
        (f := fun (y : E) => fun (s : ℝ) => scalarOnE (I := I) α (u s) y)
        (g := fun _ : E => (t : ℝ)) hf hg (by simp)
      have hcd0 : ContDiffAt ℝ ∞
          (fun y : E => (fderiv ℝ (fun s : ℝ => scalarOnE (I := I) α (u s) y) t) (1 : ℝ))
          ((extChartAt I α) x) := by
        simpa using
          ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).contDiff.contDiffAt.comp
            ((extChartAt I α) x) hfd)
      change ContDiffAt ℝ ∞
          (fun y : E => deriv (fun s : ℝ => scalarOnE (I := I) α (u s) y) t)
          ((extChartAt I α) x)
      exact hcd0
    have hpull : ContDiffAt ℝ ∞
        (scalarOnE (I := I) α (fun y : M => deriv (fun s : ℝ => u s y) t))
        ((extChartAt I α) x) := by
      simpa [scalarOnE_def] using hcd_slice
    have hua_mdiff : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y : M => deriv (fun s : ℝ => u s y) t) x := by
      rw [contMDiffAt_iff]
      constructor
      · have hcont_pull : ContinuousAt
            (scalarOnE (I := I) α (fun y : M => deriv (fun s : ℝ => u s y) t))
            ((extChartAt I α) x) := hpull.continuousAt
        have hw_eq : (fun y : M => deriv (fun s : ℝ => u s y) t) =ᶠ[𝓝 x]
            (scalarOnE (I := I) α (fun y : M => deriv (fun s : ℝ => u s y) t)) ∘
              (extChartAt I α) := by
          rw [Filter.eventuallyEq_iff_exists_mem]
          refine ⟨(extChartAt I α).source,
            (isOpen_extChartAt_source (I := I) α).mem_nhds hxextsrc, ?_⟩
          intro y hy
          have hlinv : (extChartAt I α).symm ((extChartAt I α) y) = y :=
            (extChartAt I α).left_inv hy
          change deriv (fun s : ℝ => u s y) t =
            deriv (fun s : ℝ => u s ((extChartAt I α).symm ((extChartAt I α) y))) t
          rw [hlinv]
        exact (hcont_pull.comp (continuousAt_extChartAt α)).congr_of_eventuallyEq hw_eq
      · have hcd_w : ContDiffWithinAt ℝ ∞
            (scalarOnE (I := I) α (fun y : M => deriv (fun s : ℝ => u s y) t))
            Set.univ ((extChartAt I α) x) := hpull.contDiffWithinAt
        have hcomp_eq : (extChartAt 𝓘(ℝ, ℝ) (deriv (fun s : ℝ => u s x) t) ∘
            (fun y : M => deriv (fun s : ℝ => u s y) t) ∘
              (extChartAt I α).symm) =
            scalarOnE (I := I) α (fun y : M => deriv (fun s : ℝ => u s y) t) := by
          funext z
          simp only [Function.comp_def, extChartAt_coe_symm, α]
          change scalarOnE (I := I) α (fun y : M => deriv (fun s : ℝ => u s y) t) z =
            scalarOnE (I := I) α (fun y : M => deriv (fun s : ℝ => u s y) t) z
          rfl
        rw [hcomp_eq]
        simpa [ModelWithCorners.range_eq_univ I, α] using hcd_w
    exact hua_mdiff.mdifferentiableAt (by simp)
  have hloc_r : gradientFun (I := I) g
      (fun y : M => deriv (fun s : ℝ => u s y) t) x =
      gradChartLocal (I := I) g α (fun y : M => deriv (fun s : ℝ => u s y) t) x :=
    (gradChartLocal_eq_gradFun (I := I) g α
      (hf := htarget_mdiff) hxbase hxint).symm
  have hgoal : HasDerivAt (fun s : ℝ => gradChartLocal (I := I) g α (u s) x)
      (gradientFun (I := I) g (fun y : M => deriv (fun s : ℝ => u s y) t) x) t := by
    rw [hloc_r]
    exact hcore
  have hgoal' : HasDerivAt (fun s : ℝ => gradientFun (I := I) g (u s) x)
      (gradientFun (I := I) g (fun y : M => deriv (fun s : ℝ => u s y) t) x) t := by
    rw [show (fun s : ℝ => gradientFun (I := I) g (u s) x) =
        fun s : ℝ => gradChartLocal (I := I) g α (u s) x from by
          funext s
          exact hloc_l s]
    exact hgoal
  exact hgoal'

end DifferentialGeometry.Analysis.Parabolic.Harnack

end
