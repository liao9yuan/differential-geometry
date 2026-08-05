import DifferentialGeometry.Topology.Morse.Manifold
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

namespace DifferentialGeometry.Topology.Morse

open Manifold Set
open scoped Manifold

noncomputable section

variable {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ (MorseModel n) H}

theorem fderiv_ne_zero_iff_exists_coord (g : MorseModel n → ℝ) (y : MorseModel n)
    (h : fderiv ℝ g y ≠ 0) :
    ∃ i : Fin n, (fderiv ℝ g y) (Pi.single i (1 : ℝ)) ≠ 0 := by
  by_contra! hz
  apply h
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = ∑ i : Fin n, v i • (Pi.single i (1 : ℝ) : MorseModel n) := by
    ext i
    rw [Finset.sum_apply]
    simp [smul_eq_mul, Pi.single_apply]
  rw [hv]
  simp [hz]

private theorem chartRep_contDiffOn (I : ModelWithCorners ℝ (MorseModel n) H)
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f) (x₀ : M) :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun y : MorseModel n => f ((extChartAt I x₀).symm y))
      (extChartAt I x₀).target := by
  have hc : ContMDiffOn I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f Set.univ := by
    intro x hx
    exact hf x
  have hcsub : ContMDiffOn I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f (chartAt H x₀).source :=
    hc.mono (by intro x hx; trivial)
  have hc' : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞)
      (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀ '' (chartAt H x₀).source) :=
    (contMDiffOn_iff_source_of_mem_maximalAtlas (I := I) (I' := 𝓘(ℝ, ℝ))
    (n := (⊤ : WithTop ℕ∞)) (e := chartAt H x₀) (IsManifold.chart_mem_maximalAtlas x₀)
    (s := (chartAt H x₀).source) (hs := by intro x hx; exact hx)).1 hcsub
  have hcd : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (f ∘ (extChartAt I x₀).symm)
      (extChartAt I x₀ '' (chartAt H x₀).source) :=
    (contMDiffOn_iff_contDiffOn).1 hc'
  have hrange : extChartAt I x₀ '' (chartAt H x₀).source = (extChartAt I x₀).target := by
    exact (OpenPartialHomeomorph.extend_target_eq_image_source (f := chartAt H x₀) (I := I)).symm
  rw [show (fun y : MorseModel n => f ((extChartAt I x₀).symm y)) = f ∘ (extChartAt I x₀).symm by rfl]
  rwa [← hrange]

set_option backward.isDefEq.respectTransparency false in
theorem tangentTrivializationAt_apply (I : ModelWithCorners ℝ (MorseModel n) H)
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] (x₀ x : M)
    (hx : x ∈ (extChartAt I x₀).source) (v : TangentSpace I x) :
    (trivializationAt (MorseModel n) (TangentSpace I) x₀ ⟨x, v⟩).2 =
      (mfderiv I 𝓘(ℝ, MorseModel n) (extChartAt I x₀) x) v := by
  rw [TangentBundle.trivializationAt_apply]
  rw [mfderiv]
  have hmd : MDifferentiableAt I 𝓘(ℝ, MorseModel n) (extChartAt I x₀) x := by
    have hxsrc : x ∈ (chartAt H x₀).source := by
      rwa [extChartAt_source (I := I) (x := x₀)] at hx
    exact (contMDiffAt_extChartAt' (I := I) (n := (⊤ : WithTop ℕ∞)) (x := x₀) hxsrc).mdifferentiableAt (by norm_num)
  rw [if_pos hmd]
  change fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) v =
      fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) v
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem localUnitSpeedVectorField_at_noncritical (I : ModelWithCorners ℝ (MorseModel n) H)
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    {x₀ : M} (hcrit : ¬ IsCriticalPointAt I f x₀) :
    ∃ (i : Fin n),
      (fderiv ℝ (fun y : MorseModel n => f ((extChartAt I x₀).symm y)) (extChartAt I x₀ x₀))
          (Pi.single i (1 : ℝ)) ≠ 0 ∧
      ∃ W : (x : M) → TangentSpace I x,
        (∀ x ∈ (extChartAt I x₀).source,
          (fderiv ℝ (fun y : MorseModel n => f ((extChartAt I x₀).symm y)) (extChartAt I x₀ x))
              (Pi.single i (1 : ℝ)) ≠ 0 →
          (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (W x)) = -1) := by
  have hgOn : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun y : MorseModel n => f ((extChartAt I x₀).symm y))
      (extChartAt I x₀).target := chartRep_contDiffOn I f hf x₀
  have hmemx₀ : extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (mem_extChartAt_source x₀)
  have hcritChart : fderiv ℝ (fun y : MorseModel n => f ((extChartAt I x₀).symm y))
      (extChartAt I x₀ x₀) ≠ 0 := by
    have hiff := isCriticalPointAt_iff_chart_fderiv I f hf x₀
    intro hz
    exact hcrit (hiff.2 hz)
  rcases fderiv_ne_zero_iff_exists_coord (fun y : MorseModel n => f ((extChartAt I x₀).symm y))
    (extChartAt I x₀ x₀) hcritChart with ⟨i, hi⟩
  let e : PartialEquiv M (MorseModel n) := extChartAt I x₀
  let g : MorseModel n → ℝ := fun y => f (e.symm y)
  let a : M → ℝ := fun x => (fderiv ℝ g (e x)) (Pi.single i (1 : ℝ))
  let W : (x : M) → TangentSpace I x := fun x =>
    (mfderivWithin 𝓘(ℝ, MorseModel n) I e.symm (range I) (e x)) (-(a x)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel n))
  refine ⟨i, ?_, W, ?_⟩
  · simpa [g, e] using hi
  intro x hx hane
  have hane_g : (fderiv ℝ g (e x)) (Pi.single i (1 : ℝ)) ≠ 0 := by
    simpa [g, e] using hane
  have hepx : e.symm (e x) = x := e.left_inv hx
  have hmemx : e x ∈ (extChartAt I x₀).target := e.map_source hx
  have hmdg := ((hgOn (e x) hmemx).contDiffAt ((isOpen_extChartAt_target x₀).mem_nhds hmemx)).differentiableAt
    (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0)
  have hxsrc : x ∈ (chartAt H x₀).source := by
    rwa [extChartAt_source (I := I) (x := x₀)] at hx
  have hmdchart := (contMDiffAt_extChartAt' (I := I) (n := (⊤ : WithTop ℕ∞)) (x := x₀) hxsrc).mdifferentiableAt (by norm_num)
  have hcomp := mfderiv_comp (x := x) (g := g) (f := e) (hg := hmdg.mdifferentiableAt) (hf := hmdchart)
  have hfuneq : (fun y : M => f y) =ᶠ[nhds x] (fun y : M => g (e y)) := by
    have hsrcopen : IsOpen e.source := isOpen_extChartAt_source x₀
    exact Filter.eventuallyEq_of_mem (by simpa [e] using (hsrcopen.mem_nhds hx))
      (fun y hy => congrArg f (e.left_inv hy).symm)
  have heq := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) hfuneq
  have hge : mfderiv 𝓘(ℝ, MorseModel n) 𝓘(ℝ, ℝ) g (e x) = fderiv ℝ g (e x) := by
    exact (mfderiv_eq_fderiv (𝕜 := ℝ) (E := MorseModel n) (E' := ℝ) (f := g) (x := e x))
  have hid := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x₀)
    (y := e x) (by simpa [e] using hmemx)
  have hid' : (mfderiv I 𝓘(ℝ, MorseModel n) e x) ∘L
      (mfderivWithin 𝓘(ℝ, MorseModel n) I e.symm (range I) (e x)) =
      ContinuousLinearMap.id _ _ := by
    rw [hepx] at hid
    exact hid
  have hidapply : ∀ w : MorseModel n,
      (mfderiv I 𝓘(ℝ, MorseModel n) e x)
        ((mfderivWithin 𝓘(ℝ, MorseModel n) I e.symm (range I) (e x)) w) = w := by
    intro w
    change (((mfderiv I 𝓘(ℝ, MorseModel n) e x).comp
      (mfderivWithin 𝓘(ℝ, MorseModel n) I e.symm (range I) (e x)))) w = w
    rw [hid']
    simp
  have hchartW : ((mfderiv I 𝓘(ℝ, MorseModel n) e x) : TangentSpace I x →L[ℝ] MorseModel n) (W x) =
      -(a x)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel n) := by
    dsimp [W, a]
    exact hidapply (-(a x)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel n))
  have hfinal : (fderiv ℝ g (e x)) (-(a x)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel n)) = -1 := by
    rw [(fderiv ℝ g (e x)).map_smul]
    rw [smul_eq_mul]
    have haval : (fderiv ℝ g (e x)) (Pi.single i (1 : ℝ)) = a x := by
      dsimp [a]
    rw [← haval]
    field_simp [hane_g]
  have hmain : (mfderiv I 𝓘(ℝ, ℝ) f x) (W x) = (-1 : ℝ) := by
    rw [heq]
    have hfun : (fun y : M => g (e y)) = (g ∘ e) := by rfl
    rw [hfun, hcomp]
    change ((mfderiv 𝓘(ℝ, MorseModel n) 𝓘(ℝ, ℝ) g (e x) : MorseModel n →L[ℝ] ℝ))
        (((mfderiv I 𝓘(ℝ, MorseModel n) e x) : TangentSpace I x →L[ℝ] MorseModel n) (W x)) = (-1 : ℝ)
    rw [hge]
    rw [hchartW]
    exact hfinal
  have hts : (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (W x)) =
      (mfderiv I 𝓘(ℝ, ℝ) f x) (W x) := by
    rfl
  rw [hts]
  exact hmain

theorem exists_open_unitSpeedVectorField_at_noncritical (I : ModelWithCorners ℝ (MorseModel n) H)
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    {x₀ : M} (hcrit : ¬ IsCriticalPointAt I f x₀) :
    ∃ (U : Set M), x₀ ∈ U ∧ IsOpen U ∧
      ∃ W : (x : M) → TangentSpace I x,
        ∀ x ∈ U, (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (W x)) = -1 := by
  rcases localUnitSpeedVectorField_at_noncritical I f hf hcrit with ⟨i, hi₀, W, hW⟩
  let p : M → ℝ := fun x => (fderiv ℝ (fun y : MorseModel n => f ((extChartAt I x₀).symm y))
    (extChartAt I x₀ x)) (Pi.single i (1 : ℝ))
  have hgOn : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun y : MorseModel n => f ((extChartAt I x₀).symm y))
      (extChartAt I x₀).target := chartRep_contDiffOn I f hf x₀
  have hcont : ContinuousOn p (extChartAt I x₀).source := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ (fun y : MorseModel n => f ((extChartAt I x₀).symm y)))
        (extChartAt I x₀).target :=
      hgOn.fderiv_of_isOpen (isOpen_extChartAt_target x₀) (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ ⊤)
    have hcontfd : ContinuousOn (fderiv ℝ (fun y : MorseModel n => f ((extChartAt I x₀).symm y)))
        (extChartAt I x₀).target := hfd.continuousOn
    have hconte : ContinuousOn (extChartAt I x₀) (extChartAt I x₀).source := by
      simpa [extChartAt_source (I := I) (x := x₀)] using
        (contMDiffOn_extChartAt (I := I) (n := (⊤ : WithTop ℕ∞)) (x := x₀)).continuousOn
    have hcomp' : ContinuousOn (fun x : M =>
        (fderiv ℝ (fun y : MorseModel n => f ((extChartAt I x₀).symm y))) (extChartAt I x₀ x))
        (extChartAt I x₀).source :=
      hcontfd.comp hconte (by intro x hx; exact (extChartAt I x₀).map_source hx)
    have happly : Continuous (fun L : (MorseModel n →L[ℝ] ℝ) => L (Pi.single i (1 : ℝ))) :=
      (ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ)) : (MorseModel n →L[ℝ] ℝ) →L[ℝ] ℝ).cont
    simpa [p, Function.comp_def] using (happly.comp_continuousOn hcomp')
  have hmem : x₀ ∈ (extChartAt I x₀).source := mem_extChartAt_source x₀
  have hne₀ : p x₀ ≠ 0 := by
    simpa [p] using hi₀
  have hV : {x : M | p x ≠ 0} ∈ nhds x₀ := by
    have hcontAt : ContinuousAt p x₀ :=
      (hcont x₀ hmem).continuousAt ((isOpen_extChartAt_source x₀).mem_nhds hmem)
    exact hcontAt.preimage_mem_nhds (isOpen_ne.mem_nhds hne₀)
  rcases mem_nhds_iff.mp hV with ⟨V, hVsub, hVopen, hVx₀⟩
  let U : Set M := V ∩ (extChartAt I x₀).source
  refine ⟨U, ?_, ?_, W, ?_⟩
  · exact ⟨hVx₀, hmem⟩
  · exact hVopen.inter (isOpen_extChartAt_source x₀)
  · intro x hx
    have hxV : x ∈ V := hx.1
    have hpx : p x ≠ 0 := hVsub hxV
    exact hW x hx.2 (by simpa [p] using hpx)

end

end DifferentialGeometry.Topology.Morse
