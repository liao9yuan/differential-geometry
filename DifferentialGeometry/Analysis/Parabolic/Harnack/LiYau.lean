import DifferentialGeometry.Analysis.Parabolic.Moser.LogEnergy
import DifferentialGeometry.Analysis.Calculus.TimeJetCommute
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Operator.Operators
import DifferentialGeometry.Geometry.Operator.VossWeyl
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
import DifferentialGeometry.Geometry.Operator.NormGradSq
import DifferentialGeometry.Geometry.Operator.HessianTraceInequality
import DifferentialGeometry.Geometry.Curvature.Bochner.BochnerConcrete
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

end DifferentialGeometry.Analysis.Parabolic.Harnack
