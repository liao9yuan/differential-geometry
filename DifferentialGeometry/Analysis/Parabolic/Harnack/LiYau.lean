import DifferentialGeometry.Analysis.Parabolic.Moser.LogEnergy
import DifferentialGeometry.Analysis.Calculus.TimeJetCommute
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Operator.Operators
import DifferentialGeometry.Geometry.Operator.VossWeyl
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
import DifferentialGeometry.Geometry.Operator.NormGradSq
import DifferentialGeometry.Geometry.Operator.HessianTraceInequality
import DifferentialGeometry.Geometry.Curvature.Bochner.BochnerConcrete
import DifferentialGeometry.Analysis.Calculus.Extrema
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Weak
import DifferentialGeometry.Geometry.Curvature.Realized.Operators
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily
import DifferentialGeometry.Geometry.Connection.LeviCivita.KoszulFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.TangentAction
import DifferentialGeometry.Analysis.Integration.Measure.Invariance

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Harnack

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M]

def liYauQuantity (g : SmoothRiemannianMetric I M) (f : ℝ → M → ℝ) (t : ℝ) (x : M) : ℝ :=
  g.inner x (gradientFun (I := I) g (f t) x) (gradientFun (I := I) g (f t) x) -
    deriv (fun s : ℝ => f s x) t

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

theorem liYauQuantity_eq_neg_laplacian
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {t : ℝ} {x : M}
    (hpde : deriv (fun s => u s x) t =
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x) :
    liYauQuantity g (fun τ y => Real.log (u τ y)) t x =
      -Δ_g (I := I) g
        (smoothScalarSlice (I := I) g (fun s : ℝ => fun y : M => Real.log (u s y))
          (Moser.contMDiff_log_of_pos hu hpos) t).smooth x := by
  simpa [liYauQuantity] using
    liYauQuantity_eq_neg_laplacian_log (I := I) (M := M) g u hu hpos hpde

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

variable [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem scalarOnE_jointContDiffAt
    (f : ℝ → M → ℝ)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2))
    (α : M) {t : ℝ} {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2) (t, y) := by
  have hU : ContMDiffOn ((𝓘(ℝ, ℝ).prod I)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) Set.univ := hf.contMDiffOn
  have hids : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun r : ℝ × E => r.1) (Set.univ ×ˢ (extChartAt I α).target) :=
    contMDiffOn_fst
  have hsym : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) I ∞
      (fun r : ℝ × E => (extChartAt I α).symm r.2)
      (Set.univ ×ˢ (extChartAt I α).target) := by
    refine (contMDiffOn_extChartAt_symm (I := I) α).comp ?_ ?_
    · exact contMDiffOn_snd
    · intro r hr
      exact hr.2
  have hsymm : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ((𝓘(ℝ, ℝ).prod I)) ∞
      (fun r : ℝ × E => (r.1, (extChartAt I α).symm r.2))
      (Set.univ ×ˢ (extChartAt I α).target) :=
    hids.prodMk hsym
  have hcomp : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun r : ℝ × E => f r.1 ((extChartAt I α).symm r.2))
      (Set.univ ×ˢ (extChartAt I α).target) :=
    hU.comp hsymm (fun r hr => Set.mem_univ _)
  have hcd : ContDiffOn ℝ ∞
      (fun r : ℝ × E => f r.1 ((extChartAt I α).symm r.2))
      (Set.univ ×ˢ (extChartAt I α).target) := by
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hcomp
  have hpt : (t, y) ∈ Set.univ ×ˢ (extChartAt I α).target := ⟨Set.mem_univ _, hy⟩
  have hopen : IsOpen ((Set.univ : Set ℝ) ×ˢ (extChartAt I α).target) :=
    isOpen_univ.prod (isOpen_extChartAt_target (I := I) α)
  have hat := hcd.contDiffAt
    (hopen.mem_nhds hpt)
  simpa [scalarOnE_def] using hat

theorem laplacian_time_deriv
    (g : SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2))
    (t : ℝ)
    (hft : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) t))
    (x : M) :
    deriv (fun s : ℝ => Δ_g g (smoothScalarSlice g f hf s).smooth x) t =
      Δ_g g
        (smoothScalarSlice g (fun _ : ℝ => fun y : M => deriv (fun σ : ℝ => f σ y) t) hft t).smooth x := by
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
  have hΦ : ∀ y : E, y ∈ (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2) (t, y) :=
    fun y hy => scalarOnE_jointContDiffAt (I := I) (M := M) f hf α hy
  have hpd : ∀ (j : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ (extChartAt I α).target →
      HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) j (scalarOnE (I := I) α (f s)) y)
        (partialDeriv (E := E) j (scalarOnE (I := I) α
          (fun z : M => deriv (fun s : ℝ => f s z) t)) y) t := by
    intro j y hy
    have hc := fderiv_deriv_hasDerivAt_comm
      (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2) t y
      (chartModelBasis E j) (hΦ y hy)
    have hc1 : HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) j (scalarOnE (I := I) α (f s)) y)
        (fderiv ℝ (fun z : E => deriv (fun s : ℝ => scalarOnE (I := I) α (f s) z) t)
          y (chartModelBasis E j)) t := by
      simpa [partialDeriv] using hc
    have hfun : (fun z : E => deriv (fun s : ℝ => scalarOnE (I := I) α (f s) z) t) =
        scalarOnE (I := I) α (fun w : M => deriv (fun s : ℝ => f s w) t) := by
      funext z
      rfl
    have hval : fderiv ℝ (fun z : E => deriv (fun s : ℝ => scalarOnE (I := I) α (f s) z) t)
          y (chartModelBasis E j) =
        partialDeriv (E := E) j (scalarOnE (I := I) α
          (fun w : M => deriv (fun s : ℝ => f s w) t)) y := by
      rw [hfun]
      rfl
    simpa [hval, partialDeriv] using hc1
  have hcoeff : ∀ (i : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ (extChartAt I α).target →
      HasDerivAt
        (fun s : ℝ => gradChartCoeffOnE (I := I) g α (f s) i y)
        (gradChartCoeffOnE (I := I) g α
          (fun w : M => deriv (fun s : ℝ => f s w) t) i y) t := by
    intro i y hy
    have hsum : ∀ j : Fin (Module.finrank ℝ E),
        HasDerivAt
          (fun s : ℝ => chartInvGramOnE (I := I) g α i j y *
            partialDeriv (E := E) j (scalarOnE (I := I) α (f s)) y)
          (chartInvGramOnE (I := I) g α i j y *
            partialDeriv (E := E) j (scalarOnE (I := I) α
              (fun w : M => deriv (fun s : ℝ => f s w) t)) y) t := by
        intro j
        exact (hpd j y hy).const_mul (chartInvGramOnE (I := I) g α i j y)
    have hsumall : HasDerivAt
        (fun s : ℝ => ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i j y *
            partialDeriv (E := E) j (scalarOnE (I := I) α (f s)) y)
        (∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i j y *
            partialDeriv (E := E) j (scalarOnE (I := I) α
              (fun w : M => deriv (fun s : ℝ => f s w) t)) y) t := by
      exact HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hsum j)
    simpa [gradChartCoeffOnE_def] using hsumall
  have hint : ∀ (i : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ (extChartAt I α).target →
      HasDerivAt
        (fun s : ℝ => gradChartCoeffOnE (I := I) g α (f s) i y *
          chartDensityOnE (I := I) g α y)
        (gradChartCoeffOnE (I := I) g α
          (fun w : M => deriv (fun s : ℝ => f s w) t) i y *
          chartDensityOnE (I := I) g α y) t := by
    intro i y hy
    exact (hcoeff i y hy).mul_const (chartDensityOnE (I := I) g α y)
  have hpd_joint : ∀ (j : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => partialDeriv (E := E) j
          (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2)
        (t, y) := by
    intro j y hy
    have hproj : ContDiffAt ℝ ∞ (fun q : (ℝ × E) × E => (q.1.1, q.2))
        ((t, y), y) := by
      exact contDiffAt_fst.fst.prodMk contDiffAt_snd
    have hf : ContDiffAt ℝ ∞ (Function.uncurry
        (fun (p : ℝ × E) => fun (z : E) => scalarOnE (I := I) α (f p.1) z))
        ((t, y), y) := by
      exact (hΦ y hy).comp ((t, y), y) hproj
    have hg : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (t, y) := contDiffAt_snd
    have hfd := ContDiffAt.fderiv
      (f := fun (p : ℝ × E) => fun (z : E) => scalarOnE (I := I) α (f p.1) z)
      (g := fun p : ℝ × E => p.2) hf hg (by simp)
    simpa [partialDeriv] using
      ((ContinuousLinearMap.apply ℝ ℝ (chartModelBasis E j)).contDiff.contDiffAt.comp
        (t, y) hfd)
  have hΨ : ∀ (i : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ (extChartAt I α).target →
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => gradChartCoeffOnE (I := I) g α (f p.1) i p.2 *
          chartDensityOnE (I := I) g α p.2)
        (t, y) := by
    intro i y hy
    have hsum_cd : ∀ j : Fin (Module.finrank ℝ E),
        ContDiffAt ℝ ∞
          (fun p : ℝ × E => chartInvGramOnE (I := I) g α i j p.2 *
            partialDeriv (E := E) j (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2)
          (t, y) := by
      intro j
      have hgram : ContDiffAt ℝ ∞ (fun p : ℝ × E => chartInvGramOnE (I := I) g α i j p.2)
          (t, y) := by
        change ContDiffAt ℝ ∞
          ((fun z : E => chartInvGramOnE (I := I) g α i j z) ∘
            (fun p : ℝ × E => p.2)) (t, y)
        refine ContDiffAt.comp (t, y) ?_ ?_
        · exact (chartInvGramOnE_contDiffOn (I := I) g α i j).contDiffAt
            ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)
        · exact (contDiffAt_snd : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (t, y))
      exact hgram.mul (hpd_joint j y hy)
    have hsumall_cd : ContDiffAt ℝ ∞
        (fun p : ℝ × E => ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i j p.2 *
            partialDeriv (E := E) j (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2)
        (t, y) := by
      exact ContDiffAt.sum (s := Finset.univ) (fun j _ => hsum_cd j)
    have hρ : ContDiffAt ℝ ∞ (fun p : ℝ × E => chartDensityOnE (I := I) g α p.2)
        (t, y) := by
      change ContDiffAt ℝ ∞
        ((fun z : E => chartDensityOnE (I := I) g α z) ∘
          (fun p : ℝ × E => p.2)) (t, y)
      refine ContDiffAt.comp (t, y) ?_ ?_
      · exact (chartDensityOnE_contDiffOn (I := I) g α).contDiffAt
          ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)
      · exact (contDiffAt_snd : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (t, y))
    have hprod_cd : ContDiffAt ℝ ∞
        (fun p : ℝ × E =>
          (∑ j : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j p.2 *
              partialDeriv (E := E) j (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2) *
            chartDensityOnE (I := I) g α p.2)
        (t, y) := hsumall_cd.mul hρ
    simpa [gradChartCoeffOnE_def] using hprod_cd
  have hpartial : ∀ i : Fin (Module.finrank ℝ E),
      HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) i
          (chartVossWeylIntegrand (I := I) g α (f s) i) ((extChartAt I α) x))
        (partialDeriv (E := E) i
          (chartVossWeylIntegrand (I := I) g α
            (fun w : M => deriv (fun s : ℝ => f s w) t) i) ((extChartAt I α) x)) t := by
    intro i
    have hy : (extChartAt I α) x ∈ (extChartAt I α).target := hxtarget
    have hc := fderiv_deriv_hasDerivAt_comm
      (fun p : ℝ × E => gradChartCoeffOnE (I := I) g α (f p.1) i p.2 *
        chartDensityOnE (I := I) g α p.2) t
      ((extChartAt I α) x) (chartModelBasis E i) (hΨ i ((extChartAt I α) x) hy)
    have hc1 : HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) i
          (fun z : E => gradChartCoeffOnE (I := I) g α (f s) i z *
            chartDensityOnE (I := I) g α z) ((extChartAt I α) x))
        (fderiv ℝ (fun z : E => deriv (fun s : ℝ =>
          gradChartCoeffOnE (I := I) g α (f s) i z * chartDensityOnE (I := I) g α z) t)
          ((extChartAt I α) x) (chartModelBasis E i)) t := by
      simpa [partialDeriv] using hc
    have hfun : (fun z : E => deriv (fun s : ℝ =>
        gradChartCoeffOnE (I := I) g α (f s) i z * chartDensityOnE (I := I) g α z) t) =ᶠ[𝓝 ((extChartAt I α) x)]
        fun z : E => gradChartCoeffOnE (I := I) g α
          (fun w : M => deriv (fun s : ℝ => f s w) t) i z * chartDensityOnE (I := I) g α z := by
      have hh : ∀ z : E, z ∈ (extChartAt I α).target →
          deriv (fun s : ℝ =>
            gradChartCoeffOnE (I := I) g α (f s) i z * chartDensityOnE (I := I) g α z) t =
            gradChartCoeffOnE (I := I) g α
              (fun w : M => deriv (fun s : ℝ => f s w) t) i z * chartDensityOnE (I := I) g α z := by
        intro z hz
        exact (hint i z hz).deriv
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨(extChartAt I α).target, ?_, ?_⟩
      · exact (isOpen_extChartAt_target (I := I) α).mem_nhds hxtarget
      · intro z hz
        exact hh z hz
    have hval2 : (fderiv ℝ (fun z : E => deriv (fun s : ℝ =>
          gradChartCoeffOnE (I := I) g α (f s) i z * chartDensityOnE (I := I) g α z) t)
          ((extChartAt I α) x)) (chartModelBasis E i) =
        partialDeriv (E := E) i
          (fun z : E => gradChartCoeffOnE (I := I) g α
            (fun w : M => deriv (fun s : ℝ => f s w) t) i z *
            chartDensityOnE (I := I) g α z) ((extChartAt I α) x) := by
      rw [Filter.EventuallyEq.fderiv_eq hfun]
      unfold partialDeriv
      rfl
    have hc1'' : HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) i
          (fun z : E => gradChartCoeffOnE (I := I) g α (f s) i z *
            chartDensityOnE (I := I) g α z) ((extChartAt I α) x))
        (partialDeriv (E := E) i
          (fun z : E => gradChartCoeffOnE (I := I) g α
            (fun w : M => deriv (fun s : ℝ => f s w) t) i z *
            chartDensityOnE (I := I) g α z) ((extChartAt I α) x)) t := by
      change HasDerivAt
        (fun s : ℝ => partialDeriv (E := E) i
          (fun z : E => gradChartCoeffOnE (I := I) g α (f s) i z *
            chartDensityOnE (I := I) g α z) ((extChartAt I α) x))
        ((fderiv ℝ (fun z : E => gradChartCoeffOnE (I := I) g α
            (fun w : M => deriv (fun s : ℝ => f s w) t) i z *
            chartDensityOnE (I := I) g α z) ((extChartAt I α) x))
          (chartModelBasis E i)) t
      have hval2' : (fderiv ℝ (fun z : E => deriv (fun s : ℝ =>
            gradChartCoeffOnE (I := I) g α (f s) i z * chartDensityOnE (I := I) g α z) t)
            ((extChartAt I α) x)) (chartModelBasis E i) =
          (fderiv ℝ (fun z : E => gradChartCoeffOnE (I := I) g α
            (fun w : M => deriv (fun s : ℝ => f s w) t) i z *
            chartDensityOnE (I := I) g α z) ((extChartAt I α) x))
            (chartModelBasis E i) := by
        simpa [partialDeriv] using hval2
      rw [← hval2']
      exact hc1
    change HasDerivAt
      (fun s : ℝ => partialDeriv (E := E) i
        (fun z : E => gradChartCoeffOnE (I := I) g α (f s) i z *
          chartDensityOnE (I := I) g α z) ((extChartAt I α) x))
      (partialDeriv (E := E) i
        (fun z : E => gradChartCoeffOnE (I := I) g α
          (fun w : M => deriv (fun s : ℝ => f s w) t) i z *
          chartDensityOnE (I := I) g α z) ((extChartAt I α) x)) t
    exact hc1''
  have hsumall : HasDerivAt
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α (f s) i)
          ((extChartAt I α) x))
      (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α
          (fun w : M => deriv (fun s : ℝ => f s w) t) i) ((extChartAt I α) x)) t := by
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hpartial i)
  have hdiv : HasDerivAt
      (fun s : ℝ => (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α (f s) i)
          ((extChartAt I α) x)) / chartDensity (I := I) g α x)
      ((∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α
          (fun w : M => deriv (fun s : ℝ => f s w) t) i) ((extChartAt I α) x)) /
        chartDensity (I := I) g α x) t := by
    exact hsumall.div_const (chartDensity (I := I) g α x)
  have hvw : ∀ s : ℝ, chartVossWeylLaplacian (I := I) g α (f s) x =
      (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartVossWeylIntegrand (I := I) g α (f s) i)
          ((extChartAt I α) x)) / chartDensity (I := I) g α x := by
    intro s
    rfl
  have hgoal : HasDerivAt
      (fun s : ℝ => chartVossWeylLaplacian (I := I) g α (f s) x)
      (chartVossWeylLaplacian (I := I) g α
        (fun w : M => deriv (fun s : ℝ => f s w) t) x) t := by
    simpa [chartVossWeylLaplacian_def, chartVossWeylIntegrand_def] using hdiv
  have hslice_mdiff : ∀ s : ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f s) := by
    intro s
    exact hf.comp (contMDiff_const.prodMk contMDiff_id)
  have htarget_mdiff : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun w : M => deriv (fun s : ℝ => f s w) t) := by
    exact hft.comp ((contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => t)).prodMk contMDiff_id)
  have hmain : HasDerivAt
      (fun s : ℝ => Δ_g (I := I) g (smoothScalarSlice (I := I) g f hf s).smooth x)
      (Δ_g (I := I) g
        (smoothScalarSlice (I := I) g (fun _ : ℝ => fun y : M => deriv (fun σ : ℝ => f σ y) t) hft t).smooth x)
      t := by
    have hw : ∀ s : ℝ, Δ_g (I := I) g (smoothScalarSlice (I := I) g f hf s).smooth x =
        chartVossWeylLaplacian (I := I) g α (f s) x := by
      intro s
      exact voss_weyl_laplacian_formula_pointwise (I := I) g α
        (hslice_mdiff s) hxsrc
    have hw' : Δ_g (I := I) g
        (smoothScalarSlice (I := I) g (fun _ : ℝ => fun y : M => deriv (fun σ : ℝ => f σ y) t) hft t).smooth x =
        chartVossWeylLaplacian (I := I) g α
          (fun w : M => deriv (fun s : ℝ => f s w) t) x := by
      exact voss_weyl_laplacian_formula_pointwise (I := I) g α htarget_mdiff hxsrc
    have hfun_eq : (fun s : ℝ => Δ_g (I := I) g (smoothScalarSlice (I := I) g f hf s).smooth x) =
        fun s : ℝ => chartVossWeylLaplacian (I := I) g α (f s) x := by
      funext s
      exact hw s
    rw [hfun_eq, hw']
    exact hgoal
  exact hmain.deriv

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem time_deriv_slice_contMDiff
    (f : ℝ → M → ℝ)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2))
    (t : ℝ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => deriv (fun s : ℝ => f s x) t) := by
  classical
  intro x₀
  rw [contMDiffAt_iff]
  set α : M := x₀ with hα
  have hx₀target : (extChartAt I α) x₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (mem_extChartAt_source (I := I) α)
  have hΦ : ContDiffAt ℝ ∞
      (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2) (t, (extChartAt I α) x₀) :=
    scalarOnE_jointContDiffAt (I := I) (M := M) f hf α hx₀target
  have hcd_slice : ContDiffAt ℝ ∞
      (fun y : E => deriv (fun s : ℝ => scalarOnE (I := I) α (f s) y) t)
      ((extChartAt I α) x₀) := by
    have hswap : ContDiffAt ℝ ∞ (fun p : E × ℝ => (p.2, p.1))
        ((extChartAt I α) x₀, t) :=
      contDiffAt_snd.prodMk contDiffAt_fst
    have hf' : ContDiffAt ℝ ∞ (Function.uncurry
        (fun (y : E) => fun (s : ℝ) => scalarOnE (I := I) α (f s) y))
        ((extChartAt I α) x₀, t) := by
      exact hΦ.comp ((extChartAt I α) x₀, t) hswap
    have hg : ContDiffAt ℝ ∞ (fun _ : E => (t : ℝ)) ((extChartAt I α) x₀) := contDiffAt_const
    have hfd := ContDiffAt.fderiv
      (f := fun (y : E) => fun (s : ℝ) => scalarOnE (I := I) α (f s) y)
      (g := fun _ : E => (t : ℝ)) hf' hg (by simp)
    have hcd0 : ContDiffAt ℝ ∞
        (fun y : E => (fderiv ℝ (fun s : ℝ => scalarOnE (I := I) α (f s) y) t) (1 : ℝ))
        ((extChartAt I α) x₀) := by
      simpa using
        ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).contDiff.contDiffAt.comp
          ((extChartAt I α) x₀) hfd)
    change ContDiffAt ℝ ∞
        (fun y : E => deriv (fun s : ℝ => scalarOnE (I := I) α (f s) y) t)
        ((extChartAt I α) x₀)
    exact hcd0
  have hpull : ContDiffAt ℝ ∞
      (scalarOnE (I := I) α (fun x : M => deriv (fun s : ℝ => f s x) t))
      ((extChartAt I α) x₀) := by
    simpa [scalarOnE_def] using hcd_slice
  constructor
  · have hcont_pull : ContinuousAt
        (scalarOnE (I := I) α (fun x : M => deriv (fun s : ℝ => f s x) t))
        ((extChartAt I α) x₀) := hpull.continuousAt
    have hw_eq : (fun x : M => deriv (fun s : ℝ => f s x) t) =ᶠ[𝓝 x₀]
        (scalarOnE (I := I) α (fun x : M => deriv (fun s : ℝ => f s x) t)) ∘
          (extChartAt I α) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨(extChartAt I α).source,
        (isOpen_extChartAt_source (I := I) α).mem_nhds (mem_extChartAt_source (I := I) α), ?_⟩
      intro y hy
      have hlinv : (extChartAt I α).symm ((extChartAt I α) y) = y :=
        (extChartAt I α).left_inv hy
      change deriv (fun s : ℝ => f s y) t =
        deriv (fun s : ℝ => f s ((extChartAt I α).symm ((extChartAt I α) y))) t
      rw [hlinv]
    exact (hcont_pull.comp (continuousAt_extChartAt α)).congr_of_eventuallyEq hw_eq
  · have hcd_w : ContDiffWithinAt ℝ ∞
        (scalarOnE (I := I) α (fun x : M => deriv (fun s : ℝ => f s x) t))
        Set.univ ((extChartAt I α) x₀) := hpull.contDiffWithinAt
    have hcomp_eq : (extChartAt 𝓘(ℝ, ℝ) (deriv (fun s : ℝ => f s x₀) t) ∘
        (fun x : M => deriv (fun s : ℝ => f s x) t) ∘
          (extChartAt I α).symm) =
        scalarOnE (I := I) α (fun x : M => deriv (fun s : ℝ => f s x) t) := by
      funext z
      simp only [Function.comp_def, extChartAt_coe_symm, α]
      change scalarOnE (I := I) α (fun x : M => deriv (fun s : ℝ => f s x) t) z =
        scalarOnE (I := I) α (fun x : M => deriv (fun s : ℝ => f s x) t) z
      rfl
    rw [hcomp_eq]
    simpa [ModelWithCorners.range_eq_univ I, α] using hcd_w

theorem liYauQuantity_evolution_identity
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (hpde : ∀ t x, deriv (fun s => u s x) t =
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x)
    (hq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => liYauQuantity g (fun τ y => Real.log (u τ y)) p.1 p.2))
    (t : ℝ) (x : M) :
    deriv (fun s => liYauQuantity g (fun τ y => Real.log (u τ y)) s x) t -
        Δ_g (I := I) g (smoothScalarSlice (I := I) g
          (fun τ y => liYauQuantity g (fun σ z => Real.log (u σ z)) τ y) hq t).smooth x =
      2 * g.inner x
            (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
            (gradientFun (I := I) g (fun y => liYauQuantity g (fun σ z => Real.log (u σ z)) t y) x) -
        2 * chartHessFrobeniusSq (I := I) g (fun y => Real.log (u t y)) x -
        2 * ricciTensor (I := I) g x
            (gradFun (I := I) g (fun y => Real.log (u t y)) x)
            (gradFun (I := I) g (fun y => Real.log (u t y)) x) := by
  classical
  let f : ℝ → M → ℝ := fun τ y => Real.log (u τ y)
  let hlog : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) := Moser.contMDiff_log_of_pos hu hpos
  let q : ℝ → M → ℝ := fun τ y => liYauQuantity g f τ y
  let hq' : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => q p.1 p.2) := hq
  have hqid : ∀ τ y, q τ y = -Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog τ).smooth y :=
    fun τ y => liYauQuantity_eq_neg_laplacian (I := I) (M := M) g u hu hpos (hpde τ y)
  have hft : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) t) := by
    have hs : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => deriv (fun s : ℝ => f s x) t) :=
      time_deriv_slice_contMDiff f hlog t
    exact hs.comp (contMDiff_snd : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => p.2))
  have hlap_t : deriv (fun s : ℝ => Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog s).smooth x) t =
      Δ_g (I := I) g
        (smoothScalarSlice (I := I) g (fun _ : ℝ => fun y : M => deriv (fun σ : ℝ => f σ y) t) hft t).smooth x :=
    laplacian_time_deriv (I := I) (M := M) g f hlog t hft x
  have hdq : deriv (fun s : ℝ => q s x) t =
      -Δ_g (I := I) g
        (smoothScalarSlice (I := I) g (fun _ : ℝ => fun y : M => deriv (fun σ : ℝ => f σ y) t) hft t).smooth x := by
    have hfun_eq : (fun s : ℝ => q s x) = fun s : ℝ => -Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog s).smooth x := by
      funext s
      exact hqid s x
    rw [hfun_eq]
    rw [show deriv (fun s : ℝ => -Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog s).smooth x) t =
        -deriv (fun s : ℝ => Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog s).smooth x) t from
      deriv.neg (f := fun s : ℝ => Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog s).smooth x)]
    exact congrArg Neg.neg hlap_t
  have hdq_laplacian : Δ_g (I := I) g (smoothScalarSlice (I := I) g q hq' t).smooth x =
      -Δ_g (I := I) g (Δ_g_contMDiff (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth) x := by
    have heq : (smoothScalarSlice (I := I) g q hq' t).toFun =ᶠ[𝓝 x]
        (fun y : M => -Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth y) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      intro y hy
      rw [smoothScalarSlice_toFun]
      exact hqid t y
    have hneg : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun y : M => -Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth y) :=
      ContMDiff.neg (Δ_g_contMDiff (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth)
    have hcongr := Δ_g_congr_of_eventuallyEq (I := I) g
      (smoothScalarSlice (I := I) g q hq' t).smooth hneg heq
    rw [hcongr]
    exact Δ_g_neg (I := I) g (Δ_g_contMDiff (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth) (x := x)
  have hheq : ∀ y, deriv (fun s : ℝ => f s y) t -
      Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth y =
      normGradSqFun (I := I) g (smoothScalarSlice (I := I) g f hlog t).toFun y := by
    intro y
    have hle := heatSolution_log_evolution (I := I) (M := M) g u hu hpos (hpde t y)
    have hle' : deriv (fun s : ℝ => f s y) t =
        Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth y +
          g.inner y (gradientFun (I := I) g (f t) y) (gradientFun (I := I) g (f t) y) := by
      simpa [f] using hle
    have hnorm : g.inner y (gradientFun (I := I) g (f t) y) (gradientFun (I := I) g (f t) y) =
        normGradSqFun (I := I) g (smoothScalarSlice (I := I) g f hlog t).toFun y := by
      have hvec : ∀ h : M → ℝ, gradientFun (I := I) g h y = gradFun (I := I) g h y := by
        intro h
        apply (metricFlatEquiv (I := I) g y).injective
        ext w
        change g.inner y (gradientFun (I := I) g h y) w = g.inner y (gradFun (I := I) g h y) w
        rw [inner_gradientFun (I := I) g h y w]
        rw [inner_gradFun (I := I) g h y w]
      rw [normGradSqFun]
      rw [hvec (f t)]
      rw [show (smoothScalarSlice (I := I) g f hlog t).toFun = f t by
        funext z
        rfl]
    have hle'' : deriv (fun s : ℝ => f s y) t =
        Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth y +
          normGradSqFun (I := I) g (smoothScalarSlice (I := I) g f hlog t).toFun y := by
      rw [← hnorm]
      exact hle'
    linarith
  have hftslice : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => deriv (fun s : ℝ => f s y) t) :=
    time_deriv_slice_contMDiff f hlog t
  have hmain : deriv (fun s : ℝ => q s x) t -
      Δ_g (I := I) g (smoothScalarSlice (I := I) g q hq' t).smooth x =
      -Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g
        (smoothScalarSlice (I := I) g f hlog t).smooth) x := by
    rw [hdq, hdq_laplacian]
    have hsub_fun : (fun y : M => deriv (fun s : ℝ => f s y) t -
          Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth y) =ᶠ[𝓝 x]
        (fun y : M => normGradSqFun (I := I) g (smoothScalarSlice (I := I) g f hlog t).toFun y) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      intro y hy
      exact hheq y
    have hΔsub : Δ_g (I := I) g
        (hftslice.sub (Δ_g_contMDiff (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth)) x =
        Δ_g (I := I) g hftslice x -
          Δ_g (I := I) g (Δ_g_contMDiff (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth) x := by
      have h1 := Δ_g_add (I := I) g hftslice
        (ContMDiff.neg (Δ_g_contMDiff (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth)) x
      have h2 := Δ_g_neg (I := I) g (Δ_g_contMDiff (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth) (x := x)
      have hsub_eq : (fun y : M => deriv (fun s : ℝ => f s y) t -
            Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth y) =ᶠ[𝓝 x]
          (fun y : M => deriv (fun s : ℝ => f s y) t +
            -(Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth y)) := by
        rw [Filter.eventuallyEq_iff_exists_mem]
        refine ⟨Set.univ, Filter.univ_mem, ?_⟩
        intro y hy
        ring
      have hbridge := Δ_g_congr_of_eventuallyEq (I := I) g
        (hftslice.sub (Δ_g_contMDiff (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth))
        (hftslice.add (ContMDiff.neg (Δ_g_contMDiff (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth)))
        hsub_eq
      rw [hbridge, h1, h2]
      ring
    have hΔnorm : Δ_g (I := I) g
        (hftslice.sub (Δ_g_contMDiff (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth)) x =
        Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g
          (smoothScalarSlice (I := I) g f hlog t).smooth) x :=
      Δ_g_congr_of_eventuallyEq (I := I) g
        (hftslice.sub (Δ_g_contMDiff (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth))
        (normGradSqFun_contMDiff (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth) hsub_fun
    have hdft_slice : Δ_g (I := I) g
        (smoothScalarSlice (I := I) g (fun _ : ℝ => fun y : M => deriv (fun σ : ℝ => f σ y) t) hft t).smooth x =
        Δ_g (I := I) g hftslice x :=
      Δ_g_congr_of_eventuallyEq (I := I) g
        (smoothScalarSlice (I := I) g (fun _ : ℝ => fun y : M => deriv (fun σ : ℝ => f σ y) t) hft t).smooth
        hftslice (by
          rw [Filter.eventuallyEq_iff_exists_mem]
          refine ⟨Set.univ, Filter.univ_mem, ?_⟩
          intro y hy
          rw [smoothScalarSlice_toFun]
          )
    rw [hdft_slice]
    have hstep : Δ_g (I := I) g hftslice x -
        Δ_g (I := I) g (Δ_g_contMDiff (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth) x =
        Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g
          (smoothScalarSlice (I := I) g f hlog t).smooth) x :=
      hΔsub.symm.trans hΔnorm
    linarith
  have hbochner := bochner_pointwise_concrete_metric_unconditional (I := I) g
    (smoothScalarSlice (I := I) g f hlog t).smooth x
  have hvecg : ∀ h : M → ℝ, gradientFun (I := I) g h x = gradFun (I := I) g h x := by
    intro h
    apply (metricFlatEquiv (I := I) g x).injective
    ext w
    change g.inner x (gradientFun (I := I) g h x) w = g.inner x (gradFun (I := I) g h x) w
    rw [inner_gradientFun (I := I) g h x w]
    rw [inner_gradFun (I := I) g h x w]
  have hgrad : 2 * g.inner x
        (gradFun (I := I) g (fun y => Real.log (u t y)) x)
        (gradFun (I := I) g (fun y => liYauQuantity g (fun σ z => Real.log (u σ z)) t y) x) =
      2 * g.inner x (gradFun (I := I) g (f t) x)
         (gradFun (I := I) g (fun y => -Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth y) x) := by
    rw [show (fun y : M => Real.log (u t y)) = f t by
      funext y
      rfl]
    rw [show (fun y : M => liYauQuantity g (fun σ z => Real.log (u σ z)) t y) =
        (fun y : M => -Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth y) by
      funext y
      exact hqid t y]
  have hmain' : deriv (fun s : ℝ => q s x) t -
      Δ_g (I := I) g (smoothScalarSlice (I := I) g q hq' t).smooth x =
      -2 * chartHessFrobeniusSq (I := I) g (smoothScalarSlice (I := I) g f hlog t).toFun x -
        2 * ricciTensor (I := I) g x
          (gradFun (I := I) g (smoothScalarSlice (I := I) g f hlog t).toFun x)
          (gradFun (I := I) g (smoothScalarSlice (I := I) g f hlog t).toFun x) -
        2 * g.inner x (gradFun (I := I) g (smoothScalarSlice (I := I) g f hlog t).toFun x)
          (gradFun (I := I) g (Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth) x) := by
    rw [hmain, hbochner]
    ring
  rw [hvecg (fun y : M => Real.log (u t y))]
  rw [hvecg (fun y : M => liYauQuantity g (fun σ z => Real.log (u σ z)) t y)]
  rw [hgrad]
  rw [show (fun y : M => Real.log (u t y)) =
      (smoothScalarSlice (I := I) g f hlog t).toFun by
    funext y
    rfl]
  rw [hmain']
  have hinner_eq : 2 * g.inner x (gradFun (I := I) g (f t) x)
        (gradFun (I := I) g (fun y : M => -Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth y) x) =
      -2 * g.inner x (gradFun (I := I) g (smoothScalarSlice (I := I) g f hlog t).toFun x)
        (gradFun (I := I) g (Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth) x) := by
    have hfun : (f t) = (smoothScalarSlice (I := I) g f hlog t).toFun := by
      funext y
      rfl
    have hgradneg : gradFun (I := I) g
        (fun y : M => -Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth y) x =
        -gradFun (I := I) g (Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth) x := by
      have hneg : gradientFun (I := I) g
          (fun y : M => -Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth y) x =
          -gradientFun (I := I) g (Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth) x :=
        gradientFun_neg g
          ((Δ_g_contMDiff (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth).mdifferentiableAt (by simp))
      calc
        gradFun (I := I) g
            (fun y : M => -Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth y) x
            = gradientFun (I := I) g
                (fun y : M => -Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth y) x :=
              (hvecg (fun y : M => -Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth y)).symm
        _ = -gradientFun (I := I) g (Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth) x := hneg
        _ = -gradFun (I := I) g (Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth) x := by
              rw [hvecg (Δ_g (I := I) g (smoothScalarSlice (I := I) g f hlog t).smooth)]
    rw [hfun, hgradneg]
    rw [map_neg]
    ring
  rw [hinner_eq]
  ring

theorem liYauQuantity_evolution_inequality
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) {K : ℝ}
    (hK : 0 ≤ K)
    (hRic : ∀ x v, -K * g.inner x v v ≤ ricciTensor (I := I) g x v v)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (hpde : ∀ t x, deriv (fun s => u s x) t =
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x)
    (hq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => liYauQuantity g (fun τ y => Real.log (u τ y)) p.1 p.2))
    (t : ℝ) (x : M) :
    deriv (fun s => liYauQuantity g (fun τ y => Real.log (u τ y)) s x) t -
        Δ_g (I := I) g (smoothScalarSlice (I := I) g
          (fun τ y => liYauQuantity g (fun σ z => Real.log (u σ z)) τ y) hq t).smooth x ≤
      2 * g.inner x
            (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
            (gradientFun (I := I) g (fun y => liYauQuantity g (fun σ z => Real.log (u σ z)) t y) x) -
        (2 / (Module.finrank ℝ E : ℝ)) *
          (liYauQuantity g (fun σ z => Real.log (u σ z)) t x)^2 +
        2 * K * g.inner x
            (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
            (gradientFun (I := I) g (fun y => Real.log (u t y)) x) := by
  classical
  let hlog : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => Real.log (u p.1 p.2)) := Moser.contMDiff_log_of_pos hu hpos
  let logut : M → ℝ := fun y => Real.log (u t y)
  have hvecg : ∀ h : M → ℝ, gradientFun (I := I) g h x = gradFun (I := I) g h x := by
    intro h
    apply (metricFlatEquiv (I := I) g x).injective
    ext w
    change g.inner x (gradientFun (I := I) g h x) w = g.inner x (gradFun (I := I) g h x) w
    rw [inner_gradientFun (I := I) g h x w]
    rw [inner_gradFun (I := I) g h x w]
  have hid := liYauQuantity_evolution_identity (I := I) (M := M) g u hu hpos hpde hq t x
  have htrace0 := laplacian_sq_le_dim_mul_hessianFrobeniusSq_of_boundaryless (I := I) g
    (smoothScalarSlice (I := I) g (fun s : ℝ => fun y : M => Real.log (u s y)) hlog t).smooth x
  have hn : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  have hle0 : (Δ_g (I := I) g (smoothScalarSlice (I := I) g (fun s : ℝ => fun y : M => Real.log (u s y)) hlog t).smooth x)^2 ≤
      chartHessFrobeniusSq (I := I) g (smoothScalarSlice (I := I) g (fun s : ℝ => fun y : M => Real.log (u s y)) hlog t).toFun x *
        (Module.finrank ℝ E : ℝ) := by
    rw [mul_comm] at htrace0
    exact htrace0
  have hdiv : (Δ_g (I := I) g (smoothScalarSlice (I := I) g (fun s : ℝ => fun y : M => Real.log (u s y)) hlog t).smooth x)^2 /
        (Module.finrank ℝ E : ℝ) ≤ chartHessFrobeniusSq (I := I) g logut x := by
    change (Δ_g (I := I) g (smoothScalarSlice (I := I) g (fun s : ℝ => fun y : M => Real.log (u s y)) hlog t).smooth x)^2 /
        (Module.finrank ℝ E : ℝ) ≤ chartHessFrobeniusSq (I := I) g
          (smoothScalarSlice (I := I) g (fun s : ℝ => fun y : M => Real.log (u s y)) hlog t).toFun x
    exact (div_le_iff₀ hn).2 hle0
  have htrace' : -2 * chartHessFrobeniusSq (I := I) g logut x ≤
      -(2 / (Module.finrank ℝ E : ℝ)) *
        (Δ_g (I := I) g (smoothScalarSlice (I := I) g (fun s : ℝ => fun y : M => Real.log (u s y)) hlog t).smooth x)^2 := by
    have hstep : -2 * chartHessFrobeniusSq (I := I) g logut x ≤
        -2 * ((Δ_g (I := I) g (smoothScalarSlice (I := I) g (fun s : ℝ => fun y : M => Real.log (u s y)) hlog t).smooth x)^2 /
          (Module.finrank ℝ E : ℝ)) := by
      nlinarith [hdiv]
    have hring : -2 * ((Δ_g (I := I) g (smoothScalarSlice (I := I) g (fun s : ℝ => fun y : M => Real.log (u s y)) hlog t).smooth x)^2 /
          (Module.finrank ℝ E : ℝ)) =
        -(2 / (Module.finrank ℝ E : ℝ)) *
          (Δ_g (I := I) g (smoothScalarSlice (I := I) g (fun s : ℝ => fun y : M => Real.log (u s y)) hlog t).smooth x)^2 := by
      ring_nf
    rwa [← hring]
  have hRic' : -2 * ricciTensor (I := I) g x (gradFun (I := I) g logut x) (gradFun (I := I) g logut x) ≤
      2 * K * g.inner x (gradientFun (I := I) g logut x) (gradientFun (I := I) g logut x) := by
    have hr := hRic x (gradFun (I := I) g logut x)
    have hin : g.inner x (gradientFun (I := I) g logut x) (gradientFun (I := I) g logut x) =
        g.inner x (gradFun (I := I) g logut x) (gradFun (I := I) g logut x) := by
      rw [hvecg logut]
    nlinarith [hr, hin]
  have hqsq : (liYauQuantity g (fun σ z => Real.log (u σ z)) t x)^2 =
      (Δ_g (I := I) g (smoothScalarSlice (I := I) g (fun s : ℝ => fun y : M => Real.log (u s y)) hlog t).smooth x)^2 := by
    have hqid := liYauQuantity_eq_neg_laplacian (I := I) (M := M) g u hu hpos (hpde t x)
    rw [hqid]
    ring
  rw [hid]
  rw [hqsq]
  nlinarith [htrace', hRic']

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem partialDeriv_joint_contDiffAt
    (Φ : ℝ → E → ℝ)
    {t₀ : ℝ} {y₀ : E}
    (hΦ : ContDiffAt ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) (t₀, y₀))
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × E => partialDeriv (E := E) i (fun z : E => Φ p.1 z) p.2)
      (t₀, y₀) := by
  classical
  have hfd := ContDiffAt.fderiv
    (m := (⊤ : ℕ∞))
    (f := fun p : ℝ × E => fun z : E => Φ p.1 z)
    (g := fun p : ℝ × E => p.2) (by
      change ContDiffAt ℝ ∞ (fun q : (ℝ × E) × E => Φ q.1.1 q.2) ((t₀, y₀), y₀)
      exact hΦ.comp ((t₀, y₀), y₀) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    ) contDiffAt_snd (by simp)
  have happly : ContDiffAt ℝ ∞
      (fun p : ℝ × E => (fderiv ℝ (fun z : E => Φ p.1 z) p.2) (chartModelBasis E i))
      (t₀, y₀) := by
    let evalMap : (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
      { toFun := fun L => L (chartModelBasis E i)
        map_add' := by intro L M; rfl
        map_smul' := by intro a L; rfl }
    have hev : ContDiffAt ℝ ∞
        (fun p : ℝ × E => evalMap (fderiv ℝ (fun z : E => Φ p.1 z) p.2)) (t₀, y₀) :=
      evalMap.contDiff.contDiffAt.comp (t₀, y₀) hfd
    change ContDiffAt ℝ ∞
        (fun p : ℝ × E => evalMap (fderiv ℝ (fun z : E => Φ p.1 z) p.2)) (t₀, y₀)
    exact hev
  simpa [partialDeriv] using happly

omit [T2Space M] [SigmaCompactSpace M] in
theorem normGradSqFun_eq_chartInvGram_sum
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    normGradSqFun (I := I) g f x =
      ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x k i *
          partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) *
          partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  have hxsrc : x ∈ (chartAt H α).source := by
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) α] using hx
  have hx_int : (extChartAt I α) x ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source
      (by rw [extChartAt_source_eq_chartAt_source (I := I) α]; exact hxsrc)
  have hg : gradChartLocal (I := I) g α f x = gradFun (I := I) g f x :=
    gradChartLocal_eq_gradFun (I := I) g α (hf.mdifferentiableAt (x := x) (by simp)) hx hx_int
  have hinner : g.inner x (gradChartLocal (I := I) g α f x) (gradChartLocal (I := I) g α f x) =
      ∑ k : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α f k x *
          partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
    nth_rewrite 2 [show gradChartLocal (I := I) g α f x =
        ∑ k : Fin (Module.finrank ℝ E),
          gradChartCoeff (I := I) g α f k x • chartBasisVecFiber (I := I) α k x by
        rfl]
    have hlin : (g.inner x (gradChartLocal (I := I) g α f x))
        (∑ k : Fin (Module.finrank ℝ E),
          gradChartCoeff (I := I) g α f k x • chartBasisVecFiber (I := I) α k x) =
        ∑ k : Fin (Module.finrank ℝ E),
          gradChartCoeff (I := I) g α f k x *
            (g.inner x (gradChartLocal (I := I) g α f x)) (chartBasisVecFiber (I := I) α k x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [map_smul, smul_eq_mul]
    rw [hlin]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [inner_gradChartLocal_chartBasis (I := I) g α f hx k]
  have hcoeff : ∀ k : Fin (Module.finrank ℝ E),
      gradChartCoeff (I := I) g α f k x =
        ∑ i : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α x k i *
            partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) :=
    fun k => rfl
  calc
    normGradSqFun (I := I) g f x
        = g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) := by
            rw [normGradSqFun]
    _ = g.inner x (gradChartLocal (I := I) g α f x) (gradChartLocal (I := I) g α f x) := by
            rw [hg]
    _ = ∑ k : Fin (Module.finrank ℝ E),
          gradChartCoeff (I := I) g α f k x *
            partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := hinner
    _ = ∑ k : Fin (Module.finrank ℝ E),
          ∑ i : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α x k i *
              partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) *
              partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [hcoeff k]
            rw [Finset.sum_mul]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem timeDeriv_joint_contDiffAt
    (Φ : ℝ → E → ℝ)
    {t₀ : ℝ} {y₀ : E}
    (hΦ : ContDiffAt ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) (t₀, y₀)) :
    ContDiffAt ℝ ∞ (fun p : ℝ × E => deriv (fun s : ℝ => Φ s p.2) p.1) (t₀, y₀) := by
  classical
  have hfd := ContDiffAt.fderiv
    (m := (⊤ : ℕ∞))
    (f := fun p : ℝ × E => fun s : ℝ => Φ s p.2)
    (g := fun p : ℝ × E => p.1) (by
      change ContDiffAt ℝ ∞ (fun q : (ℝ × E) × ℝ => Φ q.2 q.1.2) ((t₀, y₀), t₀)
      exact hΦ.comp ((t₀, y₀), t₀) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
    ) (contDiffAt_fst : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.1) (t₀, y₀)) (by simp)
  have happly : ContDiffAt ℝ ∞
      (fun p : ℝ × E => (fderiv ℝ (fun s : ℝ => Φ s p.2) p.1) (1 : ℝ)) (t₀, y₀) := by
    let evalMap : (ℝ →L[ℝ] ℝ) →L[ℝ] ℝ :=
      { toFun := fun L => L (1 : ℝ)
        map_add' := by intro L M; rfl
        map_smul' := by intro a L; rfl }
    have hev : ContDiffAt ℝ ∞
        (fun p : ℝ × E => evalMap (fderiv ℝ (fun s : ℝ => Φ s p.2) p.1)) (t₀, y₀) :=
      evalMap.contDiff.contDiffAt.comp (t₀, y₀) hfd
    change ContDiffAt ℝ ∞
        (fun p : ℝ × E => evalMap (fderiv ℝ (fun s : ℝ => Φ s p.2) p.1)) (t₀, y₀)
    exact hev
  change ContDiffAt ℝ ∞
      (fun p : ℝ × E => (fderiv ℝ (fun s : ℝ => Φ s p.2) p.1) (1 : ℝ)) (t₀, y₀)
  exact happly

omit [T2Space M] [SigmaCompactSpace M] in
theorem liYauQuantity_contMDiff
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => liYauQuantity g (fun τ y => Real.log (u τ y)) p.1 p.2) := by
  classical
  let f : ℝ → M → ℝ := fun τ y => Real.log (u τ y)
  let hlog : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) := Moser.contMDiff_log_of_pos hu hpos
  have hly_def : ∀ (t : ℝ) (y : M), liYauQuantity g f t y =
      normGradSqFun (I := I) g (f t) y - deriv (fun s : ℝ => f s y) t := by
    intro t y
    unfold liYauQuantity
    have hvec : gradientFun (I := I) g (f t) y = gradFun (I := I) g (f t) y := by
      apply (metricFlatEquiv (I := I) g y).injective
      ext w
      change g.inner y (gradientFun (I := I) g (f t) y) w = g.inner y (gradFun (I := I) g (f t) y) w
      rw [inner_gradientFun (I := I) g (f t) y w]
      rw [inner_gradFun (I := I) g (f t) y w]
    rw [hvec]
    rw [normGradSqFun]
  intro p₀
  rcases p₀ with ⟨t₀, x₀⟩
  rw [contMDiffAt_iff]
  set α : M := x₀ with hα
  have hy₀ : (extChartAt I α) x₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (mem_extChartAt_source (I := I) α)
  have hΦ : ContDiffAt ℝ ∞
      (fun r : ℝ × E => scalarOnE (I := I) α (f r.1) r.2) (t₀, (extChartAt I α) x₀) :=
    scalarOnE_jointContDiffAt (I := I) (M := M) f hlog α hy₀
  have hpd : ∀ i : Fin (Module.finrank ℝ E), ContDiffAt ℝ ∞
      (fun p : ℝ × E => partialDeriv (E := E) i (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2)
      (t₀, (extChartAt I α) x₀) :=
    fun i => partialDeriv_joint_contDiffAt (fun t z => scalarOnE (I := I) α (f t) z) hΦ i
  have hgram : ∀ (i j : Fin (Module.finrank ℝ E)), ContDiffAt ℝ ∞
      (fun p : ℝ × E => chartInvGramOnE (I := I) g α i j p.2) (t₀, (extChartAt I α) x₀) := by
    intro i j
    change ContDiffAt ℝ ∞
        ((fun z : E => chartInvGramOnE (I := I) g α i j z) ∘
          (fun p : ℝ × E => p.2)) (t₀, (extChartAt I α) x₀)
    refine ContDiffAt.comp (t₀, (extChartAt I α) x₀) ?_ contDiffAt_snd
    exact (chartInvGramOnE_contDiffOn (I := I) g α i j).contDiffAt
      ((isOpen_extChartAt_target (I := I) α).mem_nhds hy₀)
  have hdt : ContDiffAt ℝ ∞
      (fun p : ℝ × E => deriv (fun s : ℝ => f s ((extChartAt I α).symm p.2)) p.1)
      (t₀, (extChartAt I α) x₀) := by
    have htd := timeDeriv_joint_contDiffAt
      (fun t z => scalarOnE (I := I) α (f t) z) hΦ
    change ContDiffAt ℝ ∞
        (fun p : ℝ × E => deriv (fun s : ℝ => scalarOnE (I := I) α (f s) p.2) p.1)
        (t₀, (extChartAt I α) x₀)
    exact htd
  have hnorm_pull : ∀ (t : ℝ) (y : E), y ∈ (extChartAt I α).target →
      normGradSqFun (I := I) g (f t) ((extChartAt I α).symm y) =
        ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k i y *
            partialDeriv (E := E) i (scalarOnE (I := I) α (f t)) y *
            partialDeriv (E := E) k (scalarOnE (I := I) α (f t)) y := by
    intro t y hy
    have hx : (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) α] using
        (extChartAt I α).map_target hy
    have hformula := normGradSqFun_eq_chartInvGram_sum (I := I) g α
      (hf := (smoothScalarSlice (I := I) g f hlog t).smooth)
      ((extChartAt I α).symm y) hx
    rw [show (smoothScalarSlice (I := I) g f hlog t).toFun = f t by
      funext z
      rfl] at hformula
    rw [hformula]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => ?_))
    rw [← (chartInvGramOnE_def (I := I) g α k i y)]
    rw [(extChartAt I α).right_inv hy]
  have hqformula : ∀ (t : ℝ) (y : E), y ∈ (extChartAt I α).target →
      liYauQuantity g f t ((extChartAt I α).symm y) =
        (∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k i y *
            partialDeriv (E := E) i (fun z : E => scalarOnE (I := I) α (f t) z) y *
            partialDeriv (E := E) k (fun z : E => scalarOnE (I := I) α (f t) z) y) -
          deriv (fun s : ℝ => f s ((extChartAt I α).symm y)) t := by
    intro t y hy
    rw [hly_def t ((extChartAt I α).symm y)]
    rw [hnorm_pull t y hy]
  have hqpull : ContDiffAt ℝ ∞
      (fun p : ℝ × E => liYauQuantity g f p.1 ((extChartAt I α).symm p.2))
      (t₀, (extChartAt I α) x₀) := by
    have hsum : ContDiffAt ℝ ∞
        (fun p : ℝ × E =>
          (∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k i p.2 *
              partialDeriv (E := E) i (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2 *
              partialDeriv (E := E) k (fun z : E => scalarOnE (I := I) α (f p.1) z) p.2) -
            deriv (fun s : ℝ => f s ((extChartAt I α).symm p.2)) p.1)
        (t₀, (extChartAt I α) x₀) := by
      refine (ContDiffAt.sum (s := Finset.univ) (fun k _ => ?_)).sub hdt
      refine ContDiffAt.sum (s := Finset.univ) (fun i _ => ?_)
      exact ((hgram k i).mul (hpd i)).mul (hpd k)
    exact hsum.congr_of_eventuallyEq (by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Set.univ ×ˢ (extChartAt I α).target,
        (isOpen_univ.prod (isOpen_extChartAt_target (I := I) α)).mem_nhds ⟨Set.mem_univ _, hy₀⟩, ?_⟩
      intro z hz
      exact hqformula z.1 z.2 hz.2)
  constructor
  · have hcont_pull : ContinuousAt
        (fun p : ℝ × E => liYauQuantity g f p.1 ((extChartAt I α).symm p.2))
        (t₀, (extChartAt I α) x₀) := hqpull.continuousAt
    have hw_eq : (fun p : ℝ × M => liYauQuantity g f p.1 p.2) =ᶠ[𝓝 (t₀, x₀)]
        (fun p : ℝ × E => liYauQuantity g f p.1 ((extChartAt I α).symm p.2)) ∘
          (fun p : ℝ × M => (p.1, (extChartAt I α) p.2)) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Set.univ ×ˢ (extChartAt I α).source,
        (isOpen_univ.prod (isOpen_extChartAt_source (I := I) α)).mem_nhds
          ⟨Set.mem_univ _, mem_extChartAt_source (I := I) α⟩, ?_⟩
      intro y hy
      change liYauQuantity g f y.1 y.2 =
        liYauQuantity g f y.1 ((extChartAt I α).symm ((extChartAt I α) y.2))
      rw [(extChartAt I α).left_inv hy.2]
    have hcomp : ContinuousAt
        ((fun p : ℝ × E => liYauQuantity g f p.1 ((extChartAt I α).symm p.2)) ∘
          (fun p : ℝ × M => (p.1, (extChartAt I α) p.2))) (t₀, x₀) :=
      ContinuousAt.comp
        (f := fun p : ℝ × M => (p.1, (extChartAt I α) p.2))
        (x := (t₀, x₀)) hcont_pull (by
        refine (continuousAt_fst : ContinuousAt (fun p : ℝ × M => p.1) (t₀, x₀)).prodMk ?_
        show ContinuousAt (fun p : ℝ × M => (extChartAt I α) p.2) (t₀, x₀)
        exact ContinuousAt.comp
          (f := fun p : ℝ × M => p.2) (x := (t₀, x₀))
          (continuousAt_extChartAt x₀) continuousAt_snd)
    have hc := hcomp.congr_of_eventuallyEq hw_eq
    simpa [f] using hc
  · have hcd_pull : ContDiffWithinAt ℝ ∞
        (fun p : ℝ × E => liYauQuantity g f p.1 ((extChartAt I α).symm p.2))
        Set.univ (t₀, (extChartAt I α) x₀) := hqpull.contDiffWithinAt
    have hcomp_eq : (extChartAt 𝓘(ℝ, ℝ) (liYauQuantity g f t₀ x₀) ∘
        (fun p : ℝ × M => liYauQuantity g f p.1 p.2) ∘
          (extChartAt (𝓘(ℝ, ℝ).prod I) (t₀, x₀)).symm) =
        (fun p : ℝ × E => liYauQuantity g f p.1 ((extChartAt I α).symm p.2)) := by
      funext z
      simp only [Function.comp_def, extChartAt_prod, extChartAt_coe_symm, α]
      change liYauQuantity g f z.1 ((extChartAt I x₀).symm z.2) =
        liYauQuantity g f z.1 ((extChartAt I x₀).symm z.2)
      rfl
    have hbase : (extChartAt (𝓘(ℝ, ℝ).prod I) (t₀, x₀)) (t₀, x₀) =
        (t₀, (extChartAt I α) x₀) := by
      rw [extChartAt_prod (x := (t₀, x₀))]
      simp [α]
    have hrange : range (𝓘(ℝ, ℝ).prod I) = Set.univ := by
      apply Set.Subset.antisymm
      · intro y hy
        trivial
      · intro y hy
        have hy2 : y.2 ∈ range I := by
          rw [ModelWithCorners.range_eq_univ I]
          trivial
        rcases hy2 with ⟨x₂, hx₂⟩
        exact ⟨(y.1, x₂), by simp [hx₂]⟩
    rw [hcomp_eq, hbase, hrange]
    exact hcd_pull


theorem liYau_estimate_of_nonnegative_ricci
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
    {t : ℝ} (ht : 0 < t) (x : M) :
    liYauQuantity g (fun τ y => Real.log (u τ y)) t x ≤
      (Module.finrank ℝ E : ℝ) / (2 * t) := by
  classical
  let f : ℝ → M → ℝ := fun τ y => Real.log (u τ y)
  let hlog : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) := Moser.contMDiff_log_of_pos hu hpos
  let q : ℝ → M → ℝ := fun τ y => liYauQuantity g f τ y
  let hq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => q p.1 p.2) := by
    simpa [f, q] using liYauQuantity_contMDiff (I := I) (M := M) g u hu hpos
  let n : ℝ := (Module.finrank ℝ E : ℝ)
  have hevol : ∀ (τ : ℝ) (y : M),
      deriv (fun s => q s y) τ -
        Δ_g (I := I) g (smoothScalarSlice (I := I) g q hq τ).smooth y ≤
        2 * g.inner y (gradientFun (I := I) g (f τ) y) (gradientFun (I := I) g (q τ) y) -
          (2 / n) * (q τ y)^2 := by
    intro τ y
    have hric0 : ∀ (x : M) (v : TangentSpace I x),
        -(0 : ℝ) * g.inner x v v ≤ ricciTensor (I := I) g x v v := by
      intro x v
      simpa using hRic x v
    simpa [f, q, n] using liYauQuantity_evolution_inequality (I := I) (M := M) g
      (K := 0) le_rfl hric0 u hu hpos hpde hq τ y
  let G : RealizedMetricFamily (I := I) (M := M) ℝ :=
    { metric := fun _ => g
      connection := fun _ => LeviCivita (I := I) g
      metricCompatible := fun _ =>
        leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g }
  let H : ℝ → ℝ → M → ℝ := fun eps τ y => τ * q τ y - n / 2 - eps * τ
  have hH_nonpos : ∀ eps : ℝ, 0 < eps → ∀ τ : ℝ, 0 < τ → ∀ y : M, H eps τ y ≤ 0 := by
    intro eps heps τ hτ y
    by_contra hH
    have hHpos : 0 < H eps τ y := lt_of_not_ge hH
    have hslab : IsCompact (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) :=
      (isCompact_Icc : IsCompact (Set.Icc 0 τ)).prod isCompact_univ
    have hcont : ContinuousOn (fun p : ℝ × M => H eps p.1 p.2)
        (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) := by
      -- H eps p.1 p.2 = p.1 * q p.1 p.2 - n/2 - eps*p.1
      have hqcont : ContinuousOn (fun p : ℝ × M => q p.1 p.2)
          (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) := by
        exact ContinuousOn.mono
          (s := Set.univ) (t := Set.Icc 0 τ ×ˢ (Set.univ : Set M))
          (Continuous.continuousOn hq.continuous) (by intro p hp; trivial)
      have hfst : ContinuousOn (fun p : ℝ × M => p.1)
          (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) := continuousOn_fst
      have hmult : ContinuousOn (fun p : ℝ × M => p.1 * q p.1 p.2)
          (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) := hfst.mul hqcont
      have hconst : ContinuousOn (fun p : ℝ × M => n / 2)
          (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) := continuousOn_const
      have hsub1 : ContinuousOn (fun p : ℝ × M => p.1 * q p.1 p.2 - n / 2)
          (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) := hmult.sub hconst
      have heps : ContinuousOn (fun p : ℝ × M => eps * p.1)
          (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) := continuousOn_const.mul hfst
      have hsub : ContinuousOn (fun p : ℝ × M => p.1 * q p.1 p.2 - n / 2 - eps * p.1)
          (Set.Icc 0 τ ×ˢ (Set.univ : Set M)) := hsub1.sub heps
      exact hsub.congr (by intro p hp; rfl)
    have hnonempty : (Set.Icc 0 τ ×ˢ (Set.univ : Set M)).Nonempty :=
      ⟨(τ, y), ⟨⟨le_of_lt hτ, le_rfl⟩, trivial⟩⟩
    obtain ⟨sx, hsx, hmax⟩ := hslab.exists_isMaxOn hnonempty hcont
    rcases sx with ⟨s, x₀⟩
    have hmax' : ∀ z : ℝ × M, z ∈ Set.Icc 0 τ ×ˢ Set.univ → H eps z.1 z.2 ≤ H eps s x₀ :=
      hmax
    have hmpos : 0 < H eps s x₀ := lt_of_lt_of_le hHpos (hmax' (τ, y) ⟨⟨le_of_lt hτ, le_rfl⟩, trivial⟩)
    have hsx0 : 0 ≤ s := hsx.1.1
    have hspos : 0 < s := by
      have hs_ne0 : s ≠ 0 := by
        intro hs0
        have hnnonneg : 0 ≤ n := by
          dsimp [n]
          exact_mod_cast Nat.zero_le _
        have h0 : H eps 0 x₀ ≤ 0 := by
          simp [H]
          linarith
        have : H eps s x₀ ≤ 0 := by
          simpa [hs0] using h0
        exact (not_lt_of_ge this) hmpos
      exact lt_of_le_of_ne hsx0 (Ne.symm hs_ne0)
    have hzmax : IsMaxOn (fun τ' : ℝ => H eps τ' x₀) (Set.Icc 0 s) s := by
      intro τ' hτ'
      exact hmax' (τ', x₀) ⟨⟨hτ'.1, hτ'.2.trans hsx.1.2⟩, trivial⟩
    have hval : deriv (fun τ' : ℝ => H eps τ' x₀) s =
        q s x₀ + s * deriv (fun τ' : ℝ => q τ' x₀) s - eps := by
      have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞ (fun τ' : ℝ => (τ', x₀)) :=
        contMDiff_id.prodMk contMDiff_const
      have hqτ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun τ' : ℝ => q τ' x₀) := hq.comp hc
      have hqτdiff : DifferentiableAt ℝ (fun τ' : ℝ => q τ' x₀) s :=
        ContDiff.differentiable (contMDiff_iff_contDiff.mp hqτ) (by norm_num) s
      have hlin : HasDerivAt (fun τ' : ℝ => τ' * q τ' x₀)
          (q s x₀ + s * deriv (fun τ' : ℝ => q τ' x₀) s) s := by
        simpa using (hasDerivAt_id s).mul hqτdiff.hasDerivAt
      have hconst : HasDerivAt (fun _ : ℝ => n / 2) 0 s := hasDerivAt_const s (n / 2)
      have heps : HasDerivAt (fun τ' : ℝ => eps * τ') eps s := by
        simpa using (hasDerivAt_id s).const_mul eps
      have hmain : HasDerivAt (fun τ' : ℝ => τ' * q τ' x₀ - n / 2 - eps * τ')
          (q s x₀ + s * deriv (fun τ' : ℝ => q τ' x₀) s - eps) s := by
        simpa using (hlin.sub hconst).sub heps
      simpa [H] using hmain.deriv
    have hder : HasDerivAt (fun τ' : ℝ => H eps τ' x₀)
        (deriv (fun τ' : ℝ => H eps τ' x₀) s) s := by
      have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞ (fun τ' : ℝ => (τ', x₀)) :=
        contMDiff_id.prodMk contMDiff_const
      have hqτ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun τ' : ℝ => q τ' x₀) := hq.comp hc
      have hqτdiff : DifferentiableAt ℝ (fun τ' : ℝ => q τ' x₀) s :=
        ContDiff.differentiable (contMDiff_iff_contDiff.mp hqτ) (by norm_num) s
      have hlin : HasDerivAt (fun τ' : ℝ => τ' * q τ' x₀)
          (q s x₀ + s * deriv (fun τ' : ℝ => q τ' x₀) s) s := by
        simpa using (hasDerivAt_id s).mul hqτdiff.hasDerivAt
      have hconst : HasDerivAt (fun _ : ℝ => n / 2) 0 s := hasDerivAt_const s (n / 2)
      have heps : HasDerivAt (fun τ' : ℝ => eps * τ') eps s := by
        simpa using (hasDerivAt_id s).const_mul eps
      have hmain : HasDerivAt (fun τ' : ℝ => τ' * q τ' x₀ - n / 2 - eps * τ')
          (q s x₀ + s * deriv (fun τ' : ℝ => q τ' x₀) s - eps) s := by
        simpa using (hlin.sub hconst).sub heps
      simpa [H, hval] using hmain
    have htime : 0 ≤ deriv (fun τ' : ℝ => H eps τ' x₀) s :=
      deriv_nonneg_at_right_endpoint_of_isMaxOn_Icc hspos hzmax hder
    have hxmax : IsLocalMax (H eps s) x₀ := by
      exact Filter.Eventually.of_forall (fun y => hmax' (s, y) ⟨⟨hsx.1.1, hsx.1.2⟩, trivial⟩)
    have hqslice_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (q s) :=
      hq.comp (contMDiff_const.prodMk contMDiff_id)
    have hslice_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (H eps s) := by
      have hmain : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun y : M => s * q s y - n / 2 - eps * s) := by
        exact ((contMDiff_const.mul hqslice_smooth).sub contMDiff_const).sub
          (contMDiff_const.mul contMDiff_const)
      simpa [H] using hmain
    have hlap : laplacianAt (I := I) G s (H eps s) x₀ ≤ 0 :=
      laplacianAt_nonpos_at_spatial_max (I := I) G s hxmax hslice_smooth
    have hgrad : gradientFun (I := I) g (H eps s) x₀ = 0 := by
      exact gradientFun_eq_zero_of_isLocalMax (I := I) g hxmax
        (hslice_smooth.mdifferentiableAt (x := x₀) (by simp))
    have hgradq : gradientFun (I := I) g (q s) x₀ = 0 := by
      have hgradH : gradientFun (I := I) g (H eps s) x₀ = 0 := hgrad
      have hqs_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (q s) x₀ :=
        hqslice_smooth.mdifferentiableAt (x := x₀) (by simp)
      have h1 : gradientFun (I := I) g (fun y : M => s * q s y) x₀ =
          s • gradientFun (I := I) g (q s) x₀ := by
        have hsmul : (fun y : M => s * q s y) = s • q s := rfl
        rw [hsmul]
        exact gradientFun_const_smul (I := I) g s hqs_mdiff
      have h2 : gradientFun (I := I) g (fun _ : M => n / 2 + eps * s) x₀ = 0 := by
        exact gradientFun_const (I := I) g (n / 2 + eps * s) x₀
      have hsub : gradientFun (I := I) g (fun y : M => s * q s y - (n / 2 + eps * s)) x₀ =
          gradientFun (I := I) g (fun y : M => s * q s y) x₀ -
            gradientFun (I := I) g (fun _ : M => n / 2 + eps * s) x₀ :=
          gradientFun_sub (I := I) g
            ((contMDiff_const.mul hqslice_smooth).mdifferentiableAt (x := x₀) (by simp))
            ((contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => n / 2 + eps * s)).mdifferentiableAt
              (x := x₀) (by norm_num))
      have hHdef : (H eps s) = fun y : M => s * q s y - (n / 2 + eps * s) := by
        funext y
        simp [H]
        ring
      rw [hHdef] at hgradH
      rw [hsub, h1, h2] at hgradH
      have hgradH' : s • gradientFun (I := I) g (q s) x₀ = 0 := by
        exact sub_eq_zero.mp hgradH
      exact (smul_eq_zero.mp hgradH').resolve_left (ne_of_gt hspos)
    have hgradq' : g.inner x₀ (gradientFun (I := I) g (f s) x₀) (gradientFun (I := I) g (q s) x₀) = 0 := by
      rw [hgradq]
      simp
    have hconn : G.connection s = LeviCivita (G.metric s) := by
      simp [G]
    have hev0 := hevol s x₀
    have hdq_Δq : deriv (fun τ' : ℝ => q τ' x₀) s - laplacianAt (I := I) G s (q s) x₀ ≤
        -(2 / n) * (q s x₀)^2 := by
      have hΔq : Δ_g (I := I) g (smoothScalarSlice (I := I) g q hq s).smooth x₀ =
          Δ_g (I := I) g hqslice_smooth x₀ := by
        exact Δ_g_congr_of_eventuallyEq (I := I) g
          (smoothScalarSlice (I := I) g q hq s).smooth hqslice_smooth (by
            rw [Filter.eventuallyEq_iff_exists_mem]
            refine ⟨Set.univ, Filter.univ_mem, ?_⟩
            intro y hy
            rw [smoothScalarSlice_toFun])
      have hlapeq : laplacianAt (I := I) G s (q s) x₀ = Δ_g (I := I) g hqslice_smooth x₀ := by
        rw [laplacianAt_eq_delta (I := I) G s hqslice_smooth hconn]
      have hcanc : 2 * g.inner x₀ (gradientFun (I := I) g (f s) x₀) (gradientFun (I := I) g (q s) x₀) = 0 := by
        rw [hgradq']
        ring
      have hev0' : deriv (fun τ' : ℝ => q τ' x₀) s - Δ_g (I := I) g hqslice_smooth x₀ ≤
          -(2 / n) * (q s x₀)^2 := by
        rw [hΔq] at hev0
        nlinarith [hev0, hcanc]
      rw [hlapeq]
      exact hev0'
    have hlapH : laplacianAt (I := I) G s (H eps s) x₀ =
        s * laplacianAt (I := I) G s (q s) x₀ := by
      have hHdef : (H eps s) = fun y : M => s • q s y - (n / 2 + eps * s) := by
        funext y
        simp [H]
        ring
      have hcq : laplacianAt (I := I) G s (fun _ : M => n / 2 + eps * s) x₀ = 0 := by
        rw [laplacianAt_eq_delta (I := I) G s contMDiff_const hconn]
        simpa [G] using (Δ_g_const (I := I) g (n / 2 + eps * s) x₀ :
          Δ_g (I := I) g (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞
            (fun _ : M => n / 2 + eps * s)) x₀ = 0)
      have hsub_cd : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun y : M => s • q s y - (n / 2 + eps * s)) := by
        have hscd : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => s • q s y) := by
          simpa [Pi.smul_apply] using contMDiff_const.mul hqslice_smooth
        exact hscd.sub contMDiff_const
      have hdiff : laplacianAt (I := I) G s
          (fun y : M => s • q s y - (n / 2 + eps * s)) x₀ =
          laplacianAt (I := I) G s (s • q s) x₀ - laplacianAt (I := I) G s
            (fun _ : M => n / 2 + eps * s) x₀ := by
        rw [laplacianAt_eq_delta (I := I) G s hsub_cd hconn]
        have hscd : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => s • q s y) := by
          simpa [Pi.smul_apply] using contMDiff_const.mul hqslice_smooth
        have hc_cd : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => n / 2 + eps * s) :=
          contMDiff_const
        change Δ_g (I := I) (G.metric s) hsub_cd x₀ =
          laplacianAt (I := I) G s (fun y : M => s • q s y) x₀ -
            laplacianAt (I := I) G s (fun _ : M => n / 2 + eps * s) x₀
        rw [laplacianAt_eq_delta (I := I) G s hscd hconn]
        rw [laplacianAt_eq_delta (I := I) G s hc_cd hconn]
        change Δ_g (I := I) g hsub_cd x₀ =
          Δ_g (I := I) g hscd x₀ - Δ_g (I := I) g hc_cd x₀
        have hsum := Δ_g_add (I := I) g hscd (ContMDiff.neg hc_cd) x₀
        have hneg := Δ_g_neg (I := I) g hc_cd (x := x₀)
        have hc' : Δ_g (I := I) g hc_cd x₀ = 0 := by
          change Δ_g (I := I) g (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞
            (fun _ : M => n / 2 + eps * s)) x₀ = 0
          exact Δ_g_const (I := I) g (n / 2 + eps * s) x₀
        have hc_eq : (fun y : M => s • q s y - (n / 2 + eps * s)) =ᶠ[𝓝 x₀]
            (fun y : M => s • q s y + -(n / 2 + eps * s)) := by
          rw [Filter.eventuallyEq_iff_exists_mem]
          refine ⟨Set.univ, Filter.univ_mem, ?_⟩
          intro y hy
          ring
        have hbridge := Δ_g_congr_of_eventuallyEq (I := I) g hsub_cd
          (hscd.add (ContMDiff.neg hc_cd)) hc_eq
        rw [hbridge]
        rw [hsum]
        rw [hneg]
        rw [hc']
        ring
      have hlapS : laplacianAt (I := I) G s (s • q s) x₀ =
          s * laplacianAt (I := I) G s (q s) x₀ := by
        exact laplacianAt_smul (I := I) G s s
          (fun y => hqslice_smooth.mdifferentiableAt (x := y) (by simp))
          (gradientFun_mdiffAt (I := I) (G.metric s) hqslice_smooth x₀)
      rw [hHdef, hdiff, hcq, hlapS]
      ring
    have hineq : deriv (fun τ' : ℝ => H eps τ' x₀) s -
        laplacianAt (I := I) G s (H eps s) x₀ ≤
        q s x₀ - (2 * s / n) * (q s x₀)^2 - eps := by
      rw [hval, hlapH]
      have hlin2 : s * (deriv (fun τ' : ℝ => q τ' x₀) s - laplacianAt (I := I) G s (q s) x₀) ≤
          s * (-(2 / n) * (q s x₀)^2) :=
        mul_le_mul_of_nonneg_left hdq_Δq hspos.le
      have hrewrite : s * (-(2 / n) * (q s x₀)^2) = -((2 * s / n) * (q s x₀)^2) := by
        field_simp [n, hspos.ne']
      rw [hrewrite] at hlin2
      linarith
    have hnonneg : 0 ≤ deriv (fun τ' : ℝ => H eps τ' x₀) s -
        laplacianAt (I := I) G s (H eps s) x₀ := by
      linarith [htime, hlap]
    have hqbig : n / (2 * s) < q s x₀ := by
      have hHpos' : 0 < s * q s x₀ - n / 2 - eps * s := by
        simpa [H] using hmpos
      have hn : 0 < n := by
        dsimp [n]
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
      have hs2 : 0 < 2 * s := mul_pos zero_lt_two hspos
      have hq_gt : n / (2 * s) + eps < q s x₀ := by
        have hmain : n / 2 + eps * s < s * q s x₀ := by linarith
        have hmain' : n / 2 + eps * s < q s x₀ * s := by nlinarith [hmain]
        have hdiv : (n / 2 + eps * s) / s < q s x₀ :=
          (div_lt_iff₀ hspos).mpr hmain'
        have hrewrite : (n / 2 + eps * s) / s = n / (2 * s) + eps := by
          field_simp [hspos.ne']
        simpa [hrewrite] using hdiv
      linarith
    have hneg : q s x₀ - (2 * s / n) * (q s x₀)^2 - eps < 0 := by
      have hn : 0 < n := by
        dsimp [n]
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
      have hqpos : 0 < q s x₀ := lt_trans
        (div_pos hn (mul_pos zero_lt_two hspos)) hqbig
      have h1 : 1 - (2 * s / n) * q s x₀ < 0 := by
        have hmul : (2 * s / n) * q s x₀ > (2 * s / n) * (n / (2 * s)) :=
          mul_lt_mul_of_pos_left hqbig
            (div_pos (mul_pos zero_lt_two hspos) hn)
        have hcancel : (2 * s / n) * (n / (2 * s)) = 1 := by
          field_simp [hspos.ne', hn.ne']
        have hmul' : 1 < (2 * s / n) * q s x₀ := by
          simpa [hcancel] using hmul
        linarith
      have hq_main : q s x₀ - (2 * s / n) * (q s x₀)^2 < 0 := by
        have hfactor : q s x₀ - (2 * s / n) * (q s x₀)^2 =
            q s x₀ * (1 - (2 * s / n) * q s x₀) := by ring
        rw [hfactor]
        exact mul_neg_of_pos_of_neg hqpos h1
      linarith
    exact (lt_irrefl (0 : ℝ))
      (lt_of_le_of_lt (le_trans hnonneg hineq) hneg)
  have hfin : ∀ eps : ℝ, 0 < eps → H eps t x ≤ 0 :=
    fun eps heps => hH_nonpos eps heps t ht x
  have hqt : liYauQuantity g f t x ≤ n / (2 * t) := by
    have htq_le : t * liYauQuantity g f t x - n / 2 ≤ 0 := by
      by_contra hnot
      have hpos : 0 < t * liYauQuantity g f t x - n / 2 := lt_of_not_ge hnot
      let eps : ℝ := (t * liYauQuantity g f t x - n / 2) / (2 * t)
      have heps_pos : 0 < eps := div_pos hpos (mul_pos zero_lt_two ht)
      have hfin_eps : H eps t x ≤ 0 := hfin eps heps_pos
      have hle : t * liYauQuantity g f t x - n / 2 ≤ eps * t := by
        simpa [H, eps] using hfin_eps
      have hrewrite : eps * t = (t * liYauQuantity g f t x - n / 2) / 2 := by
        dsimp [eps]
        field_simp [ht.ne']
      have heps_lt : eps * t < t * liYauQuantity g f t x - n / 2 := by
        rw [hrewrite]
        linarith
      exact (not_le_of_gt heps_lt) hle
    have htle : t * liYauQuantity g f t x ≤ n / 2 := by linarith
    have hq2 : liYauQuantity g f t x * (2 * t) ≤ n := by
      have h2tq : 2 * (t * liYauQuantity g f t x) ≤ n := by nlinarith [htle]
      have hring : liYauQuantity g f t x * (2 * t) = 2 * (t * liYauQuantity g f t x) := by ring
      rwa [hring]
    exact (le_div_iff₀ (mul_pos zero_lt_two ht)).mpr hq2
  simpa [f, q, n] using hqt

end DifferentialGeometry.Analysis.Parabolic.Harnack
