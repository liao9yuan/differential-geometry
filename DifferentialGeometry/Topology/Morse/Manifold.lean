import DifferentialGeometry.Topology.Morse.MorseLemma
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.LinearAlgebra.QuadraticForm.Real

namespace DifferentialGeometry.Topology.Morse

open Filter
open scoped Topology

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_fderiv_translate_of_contDiffOn (g : E → ℝ) (c : E) (r : ℝ)
    (hr : 0 < r) (hg : ContDiffOn ℝ 2 g (Metric.ball c r)) :
    fderiv ℝ (fderiv ℝ (fun z : E => g (z + c))) 0 = fderiv ℝ (fderiv ℝ g) c := by
  have hfun : (fun z : E => fderiv ℝ (fun z : E => g (z + c)) z) =ᶠ[nhds (0 : E)]
      fun z : E => fderiv ℝ g (z + c) := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with z hz
    have hmem : z + c ∈ Metric.ball c r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hdiff : DifferentiableAt ℝ g (z + c) := by
      have h1 : DifferentiableOn ℝ g (Metric.ball c r) :=
        hg.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
      exact (h1 (z + c) hmem).differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
    exact fderiv_translate g c z hdiff
  have hfder : fderiv ℝ (fun z : E => fderiv ℝ (fun z : E => g (z + c)) z) (0 : E) =
      fderiv ℝ (fun z : E => fderiv ℝ g (z + c)) (0 : E) := hfun.fderiv_eq
  have hd1 : ContDiffOn ℝ 1 (fderiv ℝ g) (Metric.ball c r) :=
    hg.fderiv_of_isOpen Metric.isOpen_ball (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
  have hd : DifferentiableAt ℝ (fderiv ℝ g) c := by
    have hmem : c ∈ Metric.ball c r := by
      simp [Metric.mem_ball, hr]
    have hd1' : DifferentiableWithinAt ℝ (fderiv ℝ g) (Metric.ball c r) c :=
      (hd1 c hmem).differentiableWithinAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    exact hd1'.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
  have hlast : fderiv ℝ (fun z : E => fderiv ℝ g (z + c)) (0 : E) = fderiv ℝ (fderiv ℝ g) c := by
    simpa using fderiv_translate (fderiv ℝ g) c (0 : E) (by simpa using hd)
  rw [hfder, hlast]

theorem hessian_linearPullback_at_critical {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → ℝ) (σ : F →L[ℝ] E) (hf : ContDiff ℝ 2 f)
    (u v : F) :
    (fderiv ℝ (fderiv ℝ (fun x : F => f (σ x))) (0 : F)) u v =
    (fderiv ℝ (fderiv ℝ f) 0) (σ u) (σ v) := by
  have hfun : (fun x : F => fderiv ℝ (fun x : F => f (σ x)) x) =
      fun x : F => (fderiv ℝ f (σ x)).comp σ := by
    funext x
    have hdσ : DifferentiableAt ℝ σ x := σ.differentiableAt
    have hdf : DifferentiableAt ℝ f (σ x) :=
      (hf.contDiffAt (x := σ x)).differentiableAt (by decide : (2 : WithTop ℕ∞) ≠ 0)
    have h := fderiv_comp x (g := f) (f := σ) (hg := hdf) (hf := hdσ)
    calc
      fderiv ℝ (fun x : F => f (σ x)) x = fderiv ℝ (f ∘ σ) x := rfl
      _ = (fderiv ℝ f (σ x)).comp (fderiv ℝ σ x) := h
      _ = (fderiv ℝ f (σ x)).comp σ := by rw [σ.fderiv]
  have hfder : fderiv ℝ (fun x : F => fderiv ℝ (fun x : F => f (σ x)) x) (0 : F) =
      fderiv ℝ (fun x : F => (fderiv ℝ f (σ x)).comp σ) (0 : F) := by rw [hfun]
  have hA : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) (0 : E) := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ f) Set.univ :=
      hf.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    have h1' : DifferentiableWithinAt ℝ (fderiv ℝ f) Set.univ (0 : E) :=
      (h1 (0 : E) (Set.mem_univ (0 : E))).differentiableWithinAt (by decide : (1 : WithTop ℕ∞) ≠ 0)
    exact h1'.differentiableAt Filter.univ_mem |> fun h => h.hasFDerivAt
  have hA0 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) (σ (0 : F)) := by
    simpa [map_zero] using hA
  have hg : HasFDerivAt (fun x : F => fderiv ℝ f (σ x))
      ((fderiv ℝ (fderiv ℝ f) 0).comp σ) (0 : F) :=
    HasFDerivAt.comp (x := (0 : F)) (g := fderiv ℝ f)
      (g' := fderiv ℝ (fderiv ℝ f) 0) (f := σ) (f' := σ) (hg := hA0)
      (hf := (σ.hasFDerivAt : HasFDerivAt σ σ (0 : F)))
  have hC : HasFDerivAt (fun L : E →L[ℝ] ℝ => L.comp σ)
      ((ContinuousLinearMap.compL ℝ F E ℝ).flip σ) (fderiv ℝ f (σ (0 : F))) := by
    have hh : HasFDerivAt ((ContinuousLinearMap.compL ℝ F E ℝ).flip σ)
      ((ContinuousLinearMap.compL ℝ F E ℝ).flip σ) (fderiv ℝ f (σ (0 : F))) :=
      ((ContinuousLinearMap.compL ℝ F E ℝ).flip σ).hasFDerivAt
    convert hh using 1
  have hcomp2 : HasFDerivAt (fun x : F => (fderiv ℝ f (σ x)).comp σ)
      (((ContinuousLinearMap.compL ℝ F E ℝ).flip σ).comp ((fderiv ℝ (fderiv ℝ f) 0).comp σ)) (0 : F) := by
    have hfun' : (fun x : F => (fderiv ℝ f (σ x)).comp σ) =
        (fun L : E →L[ℝ] ℝ => L.comp σ) ∘ (fun x : F => fderiv ℝ f (σ x)) := rfl
    simpa [hfun'] using (HasFDerivAt.comp (x := (0 : F))
      (g := fun L : E →L[ℝ] ℝ => L.comp σ)
      (g' := (ContinuousLinearMap.compL ℝ F E ℝ).flip σ)
      (f := fun x : F => fderiv ℝ f (σ x))
      (f' := (fderiv ℝ (fderiv ℝ f) 0).comp σ) (hg := hC) (hf := hg))
  have hder : fderiv ℝ (fun x : F => (fderiv ℝ f (σ x)).comp σ) (0 : F) =
      ((ContinuousLinearMap.compL ℝ F E ℝ).flip σ).comp ((fderiv ℝ (fderiv ℝ f) 0).comp σ) :=
    hcomp2.fderiv
  have hmain : ((((ContinuousLinearMap.compL ℝ F E ℝ).flip σ).comp
      ((fderiv ℝ (fderiv ℝ f) 0).comp σ)) u) v = (fderiv ℝ (fderiv ℝ f) 0) (σ u) (σ v) := by
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply]
  calc
    (fderiv ℝ (fderiv ℝ (fun x : F => f (σ x))) (0 : F)) u v
        = (fderiv ℝ (fun x : F => fderiv ℝ (fun x : F => f (σ x)) x) (0 : F)) u v := rfl
    _ = (fderiv ℝ (fun x : F => (fderiv ℝ f (σ x)).comp σ) (0 : F)) u v := by rw [hfder]
    _ = ((((ContinuousLinearMap.compL ℝ F E ℝ).flip σ).comp
          ((fderiv ℝ (fderiv ℝ f) 0).comp σ)) u) v := by rw [hder]
    _ = (fderiv ℝ (fderiv ℝ f) 0) (σ u) (σ v) := hmain

theorem associated_weightedSumSquares_apply {n : ℕ} (w : Fin n → ℝ) (u v : Fin n → ℝ) :
    QuadraticMap.associated (R := ℝ) (QuadraticMap.weightedSumSquares ℝ w) u v =
      ∑ i : Fin n, w i * u i * v i := by
  calc
    QuadraticMap.associated (R := ℝ) (QuadraticMap.weightedSumSquares ℝ w) u v
        = QuadraticMap.associated (R := ℝ)
            (∑ i : Fin n, w i • QuadraticMap.proj (R := ℝ) (n := Fin n) i i) u v := by
      rw [QuadraticMap.weightedSumSquares]
    _ = (∑ i : Fin n, w i • QuadraticMap.associated (R := ℝ)
          (QuadraticMap.proj (R := ℝ) (n := Fin n) i i)) u v := by
      simp [map_sum]
    _ = ∑ i : Fin n, w i • (QuadraticMap.associated (R := ℝ)
          (QuadraticMap.proj (R := ℝ) (n := Fin n) i i) u v) := by
      simp
    _ = ∑ i : Fin n, w i * u i * v i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hA : QuadraticMap.associated (R := ℝ)
          (QuadraticMap.proj (R := ℝ) (n := Fin n) i i) u v = u i * v i := by
        rw [QuadraticMap.proj]
        rw [QuadraticMap.associated_linMulLin]
        simp [LinearMap.proj_apply]
        ring_nf
      rw [hA]
      rw [smul_eq_mul]
      ring

theorem fderiv_fderiv_eq_associated_chartHessian (f : E → ℝ) (hf : ContDiff ℝ 2 f) (a b : E) :
    (fderiv ℝ (fderiv ℝ f) 0 a) b =
      QuadraticMap.associated (R := ℝ) (chartHessian f) a b := by
  have hQ : ∀ x : E, chartHessian f x = (fderiv ℝ (fderiv ℝ f) 0 x) x := by
    intro x
    rfl
  have hs : IsSymmSndFDerivAt ℝ f 0 := by
    exact hf.contDiffAt.isSymmSndFDerivAt (by norm_num [minSmoothness])
  have hsymm : (fderiv ℝ (fderiv ℝ f) 0 a) b = (fderiv ℝ (fderiv ℝ f) 0 b) a :=
    IsSymmSndFDerivAt.eq hs a b
  have htwoL : 2 * (fderiv ℝ (fderiv ℝ f) 0 a) b =
      (fderiv ℝ (fderiv ℝ f) 0 (a + b)) (a + b) - (fderiv ℝ (fderiv ℝ f) 0 a) a -
        (fderiv ℝ (fderiv ℝ f) 0 b) b := by
    have hba : (fderiv ℝ (fderiv ℝ f) 0 (a + b)) (a + b) =
        (fderiv ℝ (fderiv ℝ f) 0 a) a + (fderiv ℝ (fderiv ℝ f) 0 a) b +
          (fderiv ℝ (fderiv ℝ f) 0 b) a + (fderiv ℝ (fderiv ℝ f) 0 b) b := by
      simp [map_add]
      ring
    rw [hba, hsymm]
    ring
  have htwoR : 2 * QuadraticMap.associated (R := ℝ) (chartHessian f) a b =
      chartHessian f (a + b) - chartHessian f a - chartHessian f b := by
    have htwo := QuadraticMap.two_nsmul_associated (R := ℝ) (S := ℝ) (chartHessian f)
    have hxy : ((2 • QuadraticMap.associatedHom (R := ℝ) (S := ℝ) (chartHessian f)) a b) =
        ((chartHessian f).polarBilin a b) :=
      congrArg (fun F : LinearMap.BilinMap ℝ E ℝ => F a b) htwo
    rw [← smul_eq_mul]
    simp
  have hmain : 2 * (fderiv ℝ (fderiv ℝ f) 0 a) b =
      2 * QuadraticMap.associated (R := ℝ) (chartHessian f) a b := by
    rw [htwoR, hQ]
    exact htwoL
  exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hmain

theorem morseLemma {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    (f : M → ℝ) (p : M)
    (hg : ContDiffOn ℝ (n + 3) (fun y : MorseModel n => f ((extChartAt I p).symm y))
      (extChartAt I p).target)
    (hcrit : fderiv ℝ (fun y : MorseModel n => f ((extChartAt I p).symm y))
      (extChartAt I p p) = 0)
    (hnd : (QuadraticMap.associated (R := ℝ)
      (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p))).SeparatingLeft) :
    ∃ ψ : OpenPartialHomeomorph (MorseModel n) (MorseModel n),
      0 ∈ ψ.source ∧ 0 ∈ ψ.target ∧ ψ 0 = 0 ∧
      ∃ w : Fin n → ℝ,
        (∀ i, w i = -1 ∨ w i = 1) ∧
        {i : Fin n | w i < 0}.ncard =
          sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) ∧
        ∃ L : MorseModel n ≃ₗ[ℝ] MorseModel n,
          ∀ y ∈ ψ.target,
            f ((extChartAt I p).symm (extChartAt I p p + L.symm (ψ y))) =
              f p + (1 / 2) * ∑ i : Fin n, w i * y i * y i := by
  let gp : MorseModel n → ℝ := fun y => f ((extChartAt I p).symm y)
  let e : MorseModel n := extChartAt I p p
  let g₀ : MorseModel n → ℝ := fun z => gp (z + e)
  have he_mem : e ∈ (extChartAt I p).target := by
    dsimp [e]
    exact (extChartAt I p).map_source (mem_extChartAt_source p)
  have htarget_open : IsOpen (extChartAt I p).target := isOpen_extChartAt_target p
  rcases (Metric.isOpen_iff.mp htarget_open) e he_mem with ⟨r, hr, hball⟩
  have hg₀ : ∃ r : ℝ, 0 < r ∧ ContDiffOn ℝ (n + 3) g₀ (Metric.ball (0 : MorseModel n) r) := by
    refine ⟨r, hr, ?_⟩
    have htrans : ContDiffOn ℝ (n + 3) (fun z : MorseModel n => z + e)
        (Metric.ball (0 : MorseModel n) r) := by
      exact ((contDiff_id : ContDiff ℝ (n + 3) (fun z : MorseModel n => z)).add
        (contDiff_const : ContDiff ℝ (n + 3) fun _ : MorseModel n => e)).contDiffOn
    have hsub : Set.MapsTo (fun z : MorseModel n => z + e) (Metric.ball (0 : MorseModel n) r)
        (extChartAt I p).target := by
      intro x hx
      have hxe : x + e ∈ Metric.ball e r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hx
      exact hball hxe
    have hcomp' : ContDiffOn ℝ (n + 3) (fun z : MorseModel n => gp (z + e))
        (Metric.ball (0 : MorseModel n) r) :=
      hg.comp htrans hsub
    simpa [g₀, gp, Function.comp_def] using hcomp'
  have hcrit₀ : fderiv ℝ g₀ 0 = 0 := by
    have hd : DifferentiableAt ℝ gp e := by
      have h2 : ContDiffOn ℝ 2 gp (extChartAt I p).target :=
        hg.of_le (by exact_mod_cast (by omega : 2 ≤ n + 3))
      have hd1' : DifferentiableWithinAt ℝ gp (extChartAt I p).target e :=
        (h2 e he_mem).differentiableWithinAt (by decide : (2 : WithTop ℕ∞) ≠ 0)
      exact hd1'.differentiableAt (htarget_open.mem_nhds he_mem)
    have htr := fderiv_translate gp e (0 : MorseModel n) (by simpa using hd)
    have hmain : fderiv ℝ (fun z : MorseModel n => gp (z + e)) 0 = 0 := by
      rw [htr]
      simp
      simpa [gp] using hcrit
    simpa [g₀] using hmain
  rcases exists_smooth_extension (n + 3) g₀ hg₀ with ⟨g1, hg1, hg1Eq⟩
  have hcrit₁ : fderiv ℝ g1 0 = 0 := by
    have hfd : fderiv ℝ g1 0 = fderiv ℝ g₀ 0 := hg1Eq.fderiv_eq
    simpa [hcrit₀] using hfd
  have hchart₁ : chartHessian g1 = chartHessian g₀ := by
    have hS : {x : MorseModel n | g1 x = g₀ x} ∈ nhds (0 : MorseModel n) := hg1Eq
    rcases mem_nhds_iff.mp hS with ⟨U, hUg, hUopen, hU0⟩
    have hfd2 : fderiv ℝ (fun x : MorseModel n => fderiv ℝ g1 x) 0 =
        fderiv ℝ (fun x : MorseModel n => fderiv ℝ g₀ x) 0 := by
      have hfdU : ∀ x ∈ U, fderiv ℝ g1 x = fderiv ℝ g₀ x := by
        intro x hx
        have hgU : g1 =ᶠ[nhds x] g₀ := by
          simpa using (Filter.mem_of_superset (hUopen.mem_nhds hx) (by intro y hy; exact hUg hy))
        exact hgU.fderiv_eq
      have hfdEq : (fun x : MorseModel n => fderiv ℝ g1 x) =ᶠ[nhds (0 : MorseModel n)]
          fun x => fderiv ℝ g₀ x := by
        filter_upwards [hUopen.mem_nhds hU0] with x hx
        exact hfdU x hx
      exact hfdEq.fderiv_eq
    have hb : chartHessianBilinAt g1 0 = chartHessianBilinAt g₀ 0 := by
      apply LinearMap.ext
      intro y
      apply LinearMap.ext
      intro z
      have hc : (fderiv ℝ (fderiv ℝ g1) 0 y) z = (fderiv ℝ (fderiv ℝ g₀) 0 y) z := by
        rw [hfd2]
      simpa [chartHessianBilinAt] using hc
    change (chartHessianBilinAt g1 0).toQuadraticMap = (chartHessianBilinAt g₀ 0).toQuadraticMap
    rw [hb]
  have hchart₀ : chartHessian g₀ = chartHessianAt gp e := by
    have h2 : ContDiffOn ℝ 2 gp (Metric.ball e r) :=
      (hg.mono (by intro x hx; exact hball hx)).of_le (by exact_mod_cast (by omega : 2 ≤ n + 3))
    have htr := fderiv_fderiv_translate_of_contDiffOn gp e r hr h2
    have hb : chartHessianBilinAt (fun z : MorseModel n => gp (z + e)) 0 = chartHessianBilinAt gp e := by
      apply LinearMap.ext
      intro y
      apply LinearMap.ext
      intro z
      have hc : (fderiv ℝ (fderiv ℝ (fun z : MorseModel n => gp (z + e))) 0 y) z =
          (fderiv ℝ (fderiv ℝ gp) e y) z := by
        rw [htr]
      simpa [chartHessianBilinAt] using hc
    change chartHessianAt (fun z : MorseModel n => gp (z + e)) 0 = chartHessianAt gp e
    dsimp [chartHessianAt, chartHessian]
    rw [hb]
  have hnd₁ : (QuadraticMap.associated (R := ℝ) (chartHessian g1)).SeparatingLeft := by
    rw [hchart₁, hchart₀]
    simpa [gp] using hnd
  rcases chartHessian_weightedSumSquares_normalForm g1 hnd₁ with ⟨w', hw', hEq, hsig⟩
  rcases hEq with ⟨L0⟩
  have hfin : Module.finrank ℝ (MorseModel n) = n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  let e0 : Fin n ≃ Fin (Module.finrank ℝ (MorseModel n)) :=
    Equiv.cast (congrArg Fin hfin.symm)
  let w : Fin n → ℝ := fun i => w' (e0 i)
  have hw : ∀ i : Fin n, w i = -1 ∨ w i = 1 := by
    intro i
    dsimp [w]
    exact hw' (e0 i)
  let τ' : MorseModel n ≃ₗ[ℝ] (Fin (Module.finrank ℝ (MorseModel n)) → ℝ) :=
    LinearEquiv.funCongrLeft ℝ ℝ e0.symm
  let σe : MorseModel n ≃ₗ[ℝ] MorseModel n :=
    τ'.trans (L0.symm : (Fin (Module.finrank ℝ (MorseModel n)) → ℝ) ≃ₗ[ℝ] MorseModel n)
  let σ : MorseModel n →L[ℝ] MorseModel n :=
    σe.toContinuousLinearEquiv.toContinuousLinearMap
  let L : MorseModel n ≃ₗ[ℝ] MorseModel n := σe.symm
  let h : MorseModel n → ℝ := fun u => g1 (σ u)
  have hh : ContDiff ℝ (n + 3) h := by
    dsimp [h]
    exact hg1.comp (σ.contDiff : ContDiff ℝ (n + 3) σ)
  have hcrit_h : fderiv ℝ h 0 = 0 := by
    dsimp [h]
    have hdσ : DifferentiableAt ℝ σ 0 := σ.differentiableAt
    have hd1 : DifferentiableAt ℝ g1 (σ 0) :=
      (hg1.contDiffAt (x := σ (0 : MorseModel n))).differentiableAt
        (by exact_mod_cast (by omega : n + 3 ≠ 0))
    have hcomp' := fderiv_comp (x := (0 : MorseModel n)) (g := g1) (f := σ)
      (hg := hd1) (hf := hdσ)
    have hmain : fderiv ℝ (g1 ∘ σ) 0 = 0 := by
      rw [hcomp', σ.fderiv]
      have hσ0 : σ (0 : MorseModel n) = 0 := by simp
      rw [hσ0, hcrit₁]
      simp
    simpa [h, Function.comp_def] using hmain
  have hLσ : ∀ x : MorseModel n, L.symm x = σ x := by
    intro x
    dsimp [σ, L, σe]
    rfl
  have hg1₂ : ContDiff ℝ 2 g1 :=
    hg1.of_le (by exact_mod_cast (by omega : 2 ≤ n + 3))
  have hdiag_h : ∀ u v : MorseModel n,
      (fderiv ℝ (fderiv ℝ h) 0 u) v = ∑ i : Fin n, w i * u i * v i := by
    intro u v
    change (fderiv ℝ (fderiv ℝ (fun x : MorseModel n => g1 (σ x))) 0 u) v =
      ∑ i : Fin n, w i * u i * v i
    have hpb := hessian_linearPullback_at_critical g1 σ hg1₂ u v
    have h1 := fderiv_fderiv_eq_associated_chartHessian g1 hg1₂ (σ u) (σ v)
    have hmain : QuadraticMap.associated (R := ℝ) (chartHessian g1) (σ u) (σ v) =
        ∑ i : Fin n, w i * u i * v i := by
      have hq' : (QuadraticMap.weightedSumSquares ℝ w').comp L0.toLinearMap = chartHessian g1 := by
        apply QuadraticMap.ext
        intro x
        simp [QuadraticMap.comp_apply]
      have hc := QuadraticMap.associated_comp (R := ℝ) (S := ℝ)
        (Q := QuadraticMap.weightedSumSquares ℝ w') (f := L0.toLinearMap)
      have hc' : QuadraticMap.associated (R := ℝ) (chartHessian g1) =
          (QuadraticMap.associated (R := ℝ) (QuadraticMap.weightedSumSquares ℝ w')).compl₁₂
            L0.toLinearMap L0.toLinearMap := by
        have hq'' : QuadraticMap.associated (R := ℝ) (chartHessian g1) =
            QuadraticMap.associated (R := ℝ) ((QuadraticMap.weightedSumSquares ℝ w').comp L0.toLinearMap) :=
          (congrArg (QuadraticMap.associated (R := ℝ)) hq').symm
        rw [hq'']
        exact hc
      have hev := congrArg (fun F : LinearMap.BilinMap ℝ (MorseModel n) ℝ => F (σ u) (σ v)) hc'
      have hL0σ : ∀ x : MorseModel n, L0 (σ x) = τ' x := by
        intro x
        simp [σ, σe, LinearEquiv.trans_apply]
      have h1' : QuadraticMap.associated (R := ℝ) (chartHessian g1) (σ u) (σ v) =
          QuadraticMap.associated (R := ℝ) (QuadraticMap.weightedSumSquares ℝ w') (τ' u) (τ' v) := by
        simpa [LinearMap.compl₁₂_apply, hL0σ] using hev
      have hre : QuadraticMap.associated (R := ℝ) (QuadraticMap.weightedSumSquares ℝ w') (τ' u) (τ' v) =
          ∑ i : Fin n, w i * u i * v i := by
        have hre0 : (∑ i : Fin n, w i * u i * v i) =
            ∑ j : Fin (Module.finrank ℝ (MorseModel n)), w' j * (u (e0.symm j)) * (v (e0.symm j)) := by
          refine Fintype.sum_equiv e0 (fun i => w i * u i * v i)
            (fun j => w' j * (u (e0.symm j)) * (v (e0.symm j))) ?_
          intro i
          dsimp [w]
          rw [Equiv.symm_apply_apply e0 i]
        have has := associated_weightedSumSquares_apply w' (τ' u) (τ' v)
        rw [has]
        have hτu : ∀ j : Fin (Module.finrank ℝ (MorseModel n)), τ' u j = u (e0.symm j) := by
          intro j
          dsimp [τ', e0]
        have hτv : ∀ j : Fin (Module.finrank ℝ (MorseModel n)), τ' v j = v (e0.symm j) := by
          intro j
          dsimp [τ', e0]
        simp_rw [hτu, hτv]
        exact hre0.symm
      rw [h1', hre]
    rw [hpb]
    rw [h1]
    exact hmain
  rcases Completion.morseLemmaDiagonal n h hh hcrit_h w hw hdiag_h with ⟨ψ, hψsrc, hψtarget, hψ0, hψnorm⟩
  rcases mem_nhds_iff.mp hg1Eq with ⟨U, hUg, hUopen, hU0⟩
  let D : Set (MorseModel n) := ψ.target ∩ (fun y => σ (ψ y)) ⁻¹' U
  have hD : D ∈ nhds (0 : MorseModel n) := by
    dsimp [D]
    have h1 : ψ.target ∈ nhds (0 : MorseModel n) := IsOpen.mem_nhds ψ.open_target hψtarget
    have h2 : (fun y : MorseModel n => σ (ψ y)) ⁻¹' U ∈ nhds (0 : MorseModel n) := by
      have hσc : ContinuousAt σ (ψ (0 : MorseModel n)) := σ.cont.continuousAt
      have hcont : ContinuousAt (fun y : MorseModel n => σ (ψ y)) (0 : MorseModel n) :=
        (ContinuousAt.comp (g := σ) (f := ψ) (x := (0 : MorseModel n))
          (hσc : ContinuousAt σ (ψ (0 : MorseModel n))) (ψ.continuousAt hψsrc))
      have hval : U ∈ nhds (σ (ψ (0 : MorseModel n))) := by
        have hσ0 : σ (0 : MorseModel n) = 0 := by simp
        simpa [hψ0, hσ0] using (IsOpen.mem_nhds hUopen hU0)
      exact hcont.preimage_mem_nhds hval
    exact Filter.inter_mem h1 h2
  let φ : OpenPartialHomeomorph (MorseModel n) (MorseModel n) := ψ.restr (ψ ⁻¹' D)
  have hW : ψ ⁻¹' D ∈ nhds (0 : MorseModel n) := by
    have hD0 : D ∈ nhds (ψ (0 : MorseModel n)) := by
      simpa [hψ0] using hD
    exact (ψ.continuousAt hψsrc).preimage_mem_nhds hD0
  have hφsrc0 : (0 : MorseModel n) ∈ φ.source := by
    dsimp [φ]
    constructor
    · exact hψsrc
    · exact (mem_interior_iff_mem_nhds).2 hW
  have hψsymm0 : ψ.symm 0 = 0 := by
    have hrinv : ψ (ψ.symm 0) = 0 := ψ.right_inv hψtarget
    have hψeq : ψ (ψ.symm 0) = ψ 0 := by
      simpa [hψ0] using hrinv
    exact (ψ.injOn (ψ.map_target hψtarget) hψsrc hψeq)
  have hφtarget0 : (0 : MorseModel n) ∈ φ.target := by
    dsimp [φ]
    constructor
    · exact hψtarget
    · have hW0 : ψ ⁻¹' D ∈ nhds (ψ.symm (0 : MorseModel n)) := by
        simpa [hψsymm0] using hW
      exact (mem_interior_iff_mem_nhds).2 hW0
  have hφ0 : φ 0 = 0 := by
    calc
      φ 0 = ψ 0 := by rfl
      _ = 0 := hψ0
  have hsig' : {i : Fin n | w i < 0}.ncard =
      sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) := by
    have hn : {i : Fin n | w i < 0}.ncard =
        {j : Fin (Module.finrank ℝ (MorseModel n)) | w' j < 0}.ncard := by
      refine Set.ncard_congr (fun i _ => e0 i) ?_ ?_ ?_
      · intro i hi
        change w' (e0 i) < 0
        exact hi
      · intro a b _ _ h
        exact e0.injective h
      · intro j hj
        refine ⟨e0.symm j, ?_, ?_⟩
        · change w' (e0 (e0.symm j)) < 0
          rw [e0.apply_symm_apply]
          exact hj
        · exact e0.apply_symm_apply j
    rw [hn, ← hchart₀, ← hchart₁]
    simpa [gp] using hsig
  refine ⟨φ, hφsrc0, hφtarget0, hφ0, w, hw, hsig', ?_⟩
  refine ⟨L, ?_⟩
  intro y hy
  have hyAnd : y ∈ ψ.target ∧ ψ.symm y ∈ interior (ψ ⁻¹' D) := by
    dsimp [φ] at hy
    exact hy
  have hyD : y ∈ D := by
    have hWs : ψ.symm y ∈ ψ ⁻¹' D := interior_subset hyAnd.2
    have hΘsV : ψ (ψ.symm y) ∈ D := hWs
    have hΘs : ψ (ψ.symm y) = y := ψ.right_inv hyAnd.1
    rw [hΘs] at hΘsV
    exact hΘsV
  have hσψy : σ (ψ y) ∈ U := hyD.2
  have hpoint : extChartAt I p p + L.symm (φ y) = e + σ (ψ y) := by
    dsimp [e]
    have hφy : φ y = ψ y := by rfl
    rw [hφy, hLσ]
  have hnorm := hψnorm y hyAnd.1
  have h0 : h 0 = f p := by
    have hσ0 : σ (0 : MorseModel n) = 0 := by simp
    calc
      h 0 = g1 (σ 0) := rfl
      _ = g1 0 := by rw [hσ0]
      _ = g₀ 0 := hUg hU0
      _ = gp (0 + e) := rfl
      _ = gp e := by simp
      _ = f ((extChartAt I p).symm (extChartAt I p p)) := rfl
      _ = f p := by
        exact congrArg f ((extChartAt I p).left_inv (mem_extChartAt_source p))
  calc
    f ((extChartAt I p).symm (extChartAt I p p + L.symm (φ y)))
        = f ((extChartAt I p).symm (e + σ (ψ y))) := by rw [hpoint]
    _ = gp (e + σ (ψ y)) := rfl
    _ = g₀ (σ (ψ y)) := by
      dsimp [g₀]
      rw [add_comm]
    _ = g1 (σ (ψ y)) := (hUg hσψy).symm
    _ = h (ψ y) := rfl
    _ = h 0 + (1 / 2) * ∑ i : Fin n, w i * y i * y i := hnorm
    _ = f p + (1 / 2) * ∑ i : Fin n, w i * y i * y i := by rw [h0]

end
end DifferentialGeometry.Topology.Morse
