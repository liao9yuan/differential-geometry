import DifferentialGeometry.Geometry.Coordinates.LocalDiffeoIFT

/-!
# Positive-start endpoint local inverse

This file applies the manifold inverse function theorem directly to a supplied
jointly smooth positive-start regularized L-family.  The family is parametrized
by its actual tangent velocity, so injectivity of the endpoint differential at
the central velocity gives a genuine smooth local inverse of the endpoint map.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set
open scoped ContDiff Manifold Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

omit [FiniteDimensional Real E] [I.Boundaryless] in
private theorem tail_written_inv
    {f : E → M} {u : E}
    (hf : MDifferentiableAt 𝓘(Real, E) I f u)
    (hinv : (mfderiv 𝓘(Real, E) I f u).IsInvertible) :
    (fderiv Real
      (writtenInExtChartAt 𝓘(Real, E) I u f)
      (extChartAt 𝓘(Real, E) u u)).IsInvertible := by
  have hf' : HasMFDerivAt 𝓘(Real, E) I f u
      (mfderiv 𝓘(Real, E) I f u) :=
    hf.hasMFDerivAt
  have hchart : HasMFDerivAt I 𝓘(Real, E) (extChartAt I (f u)) (f u)
      (ContinuousLinearMap.id Real E) := by
    have h :=
      (mdifferentiableAt_extChartAt (I := I)
        (mem_chart_source H (f u))).hasMFDerivAt
    rw [mfderiv_extChartAt_self (I := I) (x := f u)] at h
    exact h
  have hcomp : HasMFDerivAt 𝓘(Real, E) 𝓘(Real, E)
      ((extChartAt I (f u)) ∘ f) u
      ((ContinuousLinearMap.id Real E).comp
        (mfderiv 𝓘(Real, E) I f u)) :=
    hchart.comp u hf'
  rw [ContinuousLinearMap.id_comp] at hcomp
  have hwritten : HasFDerivAt
      (writtenInExtChartAt 𝓘(Real, E) I u f)
      (mfderiv 𝓘(Real, E) I f u)
      (extChartAt 𝓘(Real, E) u u) := by
    simpa only [writtenInExtChartAt, extChartAt_self_eq,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id_eq] using hasMFDerivAt_iff_hasFDerivAt.mp hcomp
  rw [hwritten.fderiv]
  exact hinv

omit [FiniteDimensional Real E] [I.Boundaryless] in
private theorem tail_prod_written_inv
    {f : E × Real → M × Real} {u : E × Real}
    (hf : MDifferentiableAt
      (𝓘(Real, E).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Real)) f u)
    (hinv : (mfderiv
      (𝓘(Real, E).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Real)) f u).IsInvertible) :
    (fderiv Real
      (writtenInExtChartAt
        (𝓘(Real, E).prod 𝓘(Real, Real))
        (I.prod 𝓘(Real, Real)) u f)
      (extChartAt
        (𝓘(Real, E).prod 𝓘(Real, Real)) u u)).IsInvertible := by
  have hf' : HasMFDerivAt
      (𝓘(Real, E).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Real)) f u
      (mfderiv
        (𝓘(Real, E).prod 𝓘(Real, Real))
        (I.prod 𝓘(Real, Real)) f u) :=
    hf.hasMFDerivAt
  have hchart : HasMFDerivAt
      (I.prod 𝓘(Real, Real))
      (𝓘(Real, E).prod 𝓘(Real, Real))
      (extChartAt (I.prod 𝓘(Real, Real)) (f u)) (f u)
      (ContinuousLinearMap.id Real (E × Real)) := by
    have h :=
      (mdifferentiableAt_extChartAt
        (I := I.prod 𝓘(Real, Real))
        (mem_chart_source (ModelProd H Real) (f u))).hasMFDerivAt
    rw [mfderiv_extChartAt_self
      (I := I.prod 𝓘(Real, Real)) (x := f u)] at h
    exact h
  have hcomp : HasMFDerivAt
      (𝓘(Real, E).prod 𝓘(Real, Real))
      (𝓘(Real, E).prod 𝓘(Real, Real))
      ((extChartAt (I.prod 𝓘(Real, Real)) (f u)) ∘ f) u
      ((ContinuousLinearMap.id Real (E × Real)).comp
        (mfderiv
          (𝓘(Real, E).prod 𝓘(Real, Real))
          (I.prod 𝓘(Real, Real)) f u)) :=
    hchart.comp u hf'
  rw [ContinuousLinearMap.id_comp] at hcomp
  have hwritten : HasFDerivAt
      (writtenInExtChartAt
        (𝓘(Real, E).prod 𝓘(Real, Real))
        (I.prod 𝓘(Real, Real)) u f)
      (mfderiv
        (𝓘(Real, E).prod 𝓘(Real, Real))
        (I.prod 𝓘(Real, Real)) f u)
      (extChartAt
        (𝓘(Real, E).prod 𝓘(Real, Real)) u u) := by
    simpa only [writtenInExtChartAt, extChartAt_self_eq,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id_eq] using
      hasMFDerivAt_iff_hasFDerivAt.mp hcomp
  rw [hwritten.fderiv]
  exact hinv

/-- A jointly smooth positive-start L-family whose endpoint differential is
injective at the central actual velocity has a smooth local endpoint inverse. -/
theorem lTail_localDiffeo
    {alpha : E × Real → M} {V : Set E} {K : Set Real}
    {A0 : E} {b : Real}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V) (hbK : b ∈ K)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hinj : Function.Injective fun B : E ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0 B) :
    IsLocalDiffeomorphAt 𝓘(Real, E) I ∞
      (fun A : E ↦ alpha (A, b)) A0 := by
  let f : E → M := fun A ↦ alpha (A, b)
  have hpair : ContMDiff 𝓘(Real, E)
      (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
      (fun A : E ↦ (A, b)) :=
    contMDiff_id.prodMk contMDiff_const
  have hfV : ContMDiffOn 𝓘(Real, E) I ∞ f V := by
    apply halpha.comp hpair.contMDiffOn
    intro A hAV
    exact ⟨hAV, hbK⟩
  have hfinj : Function.Injective (mfderiv 𝓘(Real, E) I f A0) := by
    simpa only [f] using hinj
  letI : FiniteDimensional Real (TangentSpace I (f A0)) :=
    inferInstanceAs (FiniteDimensional Real E)
  letI : FiniteDimensional Real
      (TangentSpace (modelWithCornersSelf Real E) A0) :=
    inferInstanceAs (FiniteDimensional Real E)
  have hfsurj : Function.Surjective (mfderiv 𝓘(Real, E) I f A0) :=
    LinearMap.surjective_of_injective hfinj
  let Df : E ≃L[Real] E :=
    ContinuousLinearEquiv.ofBijective (mfderiv 𝓘(Real, E) I f A0)
      (LinearMap.ker_eq_bot.mpr hfinj)
      (LinearMap.range_eq_top.mpr hfsurj)
  have hDinv : (mfderiv 𝓘(Real, E) I f A0).IsInvertible := by
    refine ⟨Df, ?_⟩
    rfl
  have hfA0 : MDifferentiableAt 𝓘(Real, E) I f A0 :=
    (hfV.contMDiffAt (hVopen.mem_nhds hA0V)).mdifferentiableAt (by simp)
  have hfdinv := tail_written_inv (I := I) hfA0 hDinv
  obtain ⟨Psi, hA0Psi, hPsiV, hEqPsi⟩ :=
    DifferentialGeometry.Coordinates.isLocalDiffeomorphAt_of_contMDiffOn'
      (I := 𝓘(Real, E)) (J := I) (n := 1) le_rfl
      (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤))
      hVopen hA0V (hfV.of_le (by exact_mod_cast le_top)) hfdinv
  have hfPsi : ContMDiffOn 𝓘(Real, E) I ∞ f Psi.source :=
    hfV.mono hPsiV
  have hinvPsi : ∀ A ∈ Psi.source,
      (fderiv Real
        (writtenInExtChartAt 𝓘(Real, E) I A f)
        (extChartAt 𝓘(Real, E) A A)).IsInvertible := by
    intro A hA
    have hloc : IsLocalDiffeomorphAt 𝓘(Real, E) I 1 f A :=
      ⟨Psi, hA, hEqPsi⟩
    have hmfdinv : (mfderiv 𝓘(Real, E) I f A).IsInvertible :=
      ⟨hloc.mfderivToContinuousLinearEquiv one_ne_zero,
        hloc.mfderivToContinuousLinearEquiv_coe one_ne_zero⟩
    have hfA : MDifferentiableAt 𝓘(Real, E) I f A :=
      (hfPsi.contMDiffAt (Psi.open_source.mem_nhds hA)).mdifferentiableAt
        (by simp)
    exact tail_written_inv (I := I) hfA hmfdinv
  obtain ⟨Phi, hA0Phi, _hPhiPsi, hEqPhi⟩ :=
    DifferentialGeometry.Coordinates.hlocAt_infty'
      (I := 𝓘(Real, E)) (J := I) Psi.open_source hA0Psi hfPsi hinvPsi
  exact ⟨Phi, hA0Phi, hEqPhi⟩

/-- Adjoining the varying terminal time to a jointly smooth positive-start
L-family gives a smooth local coordinate map when the fixed-time endpoint
differential is injective at the central velocity. -/
theorem lTailTime_local
    {alpha : E × Real → M} {V : Set E} {K : Set Real}
    {A0 : E} {b : Real}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hbK : b ∈ K)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hinj : Function.Injective fun B : E ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0 B) :
    IsLocalDiffeomorphAt
      (𝓘(Real, E).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Real)) ∞
      (fun p : E × Real ↦ (alpha p, p.2)) (A0, b) := by
  let J := 𝓘(Real, E).prod 𝓘(Real, Real)
  let L := I.prod 𝓘(Real, Real)
  let f : E × Real → M := alpha
  let F : E × Real → M × Real := fun p ↦ (f p, p.2)
  let U : Set (E × Real) := V ×ˢ K
  let z : E := A0
  have hUopen : IsOpen U := hVopen.prod hKopen
  have hzu : (z, b) ∈ U := ⟨hA0V, hbK⟩
  have hfU : ContMDiffOn J I ∞ f U := by
    simpa only [J, f, U] using halpha
  have hFU : ContMDiffOn J L ∞ F U := by
    exact hfU.prodMk contMDiffOn_snd
  have hFdiff : MDifferentiableAt J L F (z, b) :=
    (hFU.contMDiffAt (hUopen.mem_nhds hzu)).mdifferentiableAt (by simp)
  have hfdiff : MDifferentiableAt J I f (z, b) :=
    (hfU.contMDiffAt (hUopen.mem_nhds hzu)).mdifferentiableAt (by simp)
  have hsnddiff : MDifferentiableAt J 𝓘(Real, Real)
      (@Prod.snd E Real) (z, b) :=
    (show ContMDiffAt J 𝓘(Real, Real) ∞
        (@Prod.snd E Real) (z, b) from
      contMDiffAt_snd).mdifferentiableAt (by simp)
  have hFderiv := mfderiv_prodMk hfdiff hsnddiff
  have hDFinj : Function.Injective (mfderiv J L F (z, b)) := by
    apply LinearMap.ker_eq_bot.mp
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro hv
      have hpair :
          (mfderiv J I f (z, b) v,
            mfderiv J 𝓘(Real, Real) (@Prod.snd E Real)
              (z, b) v) = 0 := by
        have hv' : mfderiv J L (fun p : E × Real ↦ (f p, p.2))
            (z, b) v = 0 := by
          simpa only [F] using hv
        rw [hFderiv] at hv'
        exact hv'
      have hv2 : v.2 = 0 := by
        have h := congrArg Prod.snd hpair
        have hsndEq :
            mfderiv J 𝓘(Real, Real) (@Prod.snd E Real) (z, b) v =
              v.2 := by
          change (mfderiv
            (𝓘(Real, E).prod 𝓘(Real, Real)) 𝓘(Real, Real)
            (@Prod.snd E Real) (z, b)) v = v.2
          rw [mfderiv_snd]
          rfl
        rw [hsndEq] at h
        simpa only [Prod.snd_zero] using h
      have hfirst : mfderiv J I f (z, b) (v.1, 0) = 0 := by
        have h := congrArg Prod.fst hpair
        have hvEq : v = (v.1, 0) := Prod.ext rfl hv2
        rw [hvEq] at h
        simpa only [Prod.fst_zero] using h
      let g : E → E × Real := fun W ↦ (W, b)
      have hidC : ContMDiffAt 𝓘(Real, E) 𝓘(Real, E) ∞
          (fun W : E ↦ W) z := contMDiffAt_id
      have hconstC : ContMDiffAt 𝓘(Real, E) 𝓘(Real, Real) ∞
          (fun _ : E ↦ b) z := contMDiffAt_const
      have hidDiff : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, E)
          (fun W : E ↦ W) z := hidC.mdifferentiableAt (by simp)
      have hconstDiff : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
          (fun _ : E ↦ b) z := hconstC.mdifferentiableAt (by simp)
      have hgdiff : MDifferentiableAt 𝓘(Real, E) J g z :=
        (hidC.prodMk hconstC).mdifferentiableAt (by simp)
      have hcomp := mfderiv_comp z hfdiff hgdiff
      have hgderiv : mfderiv 𝓘(Real, E) J g z v.1 = (v.1, 0) := by
        have hprod := mfderiv_prodMk hidDiff hconstDiff
        rw [show (fun W : E ↦ W) = id from rfl, mfderiv_id,
          mfderiv_const] at hprod
        change mfderiv 𝓘(Real, E) J (fun W : E ↦ (W, b)) z v.1 = _
        rw [hprod]
        rfl
      have hfix :
          mfderiv 𝓘(Real, E) I (fun W : E ↦ alpha (W, b)) z v.1 =
            mfderiv J I f (z, b) (v.1, 0) := by
        have hcompVal := congrArg (fun Q ↦ Q v.1) hcomp
        have hfun : f ∘ g = fun W : E ↦ alpha (W, b) := by
          funext W
          rfl
        have hgz : g z = (z, b) := rfl
        rw [hfun, hgz] at hcompVal
        change
          mfderiv 𝓘(Real, E) I (fun W : E ↦ alpha (W, b)) z v.1 =
            ((mfderiv J I f (z, b)).comp
              (mfderiv 𝓘(Real, E) J g z)) v.1 at hcompVal
        rw [ContinuousLinearMap.comp_apply, hgderiv] at hcompVal
        exact hcompVal
      have hzero :
          mfderiv 𝓘(Real, E) I (fun W : E ↦ alpha (W, b)) z v.1 =
            0 := hfix.trans hfirst
      have hv1 : v.1 = 0 := by
        apply hinj
        exact hzero.trans (map_zero _).symm
      exact Prod.ext hv1 hv2
    · rintro rfl
      exact map_zero _
  letI : FiniteDimensional Real (TangentSpace J (z, b)) :=
    inferInstanceAs (FiniteDimensional Real (E × Real))
  letI : FiniteDimensional Real (TangentSpace L (F (z, b))) :=
    inferInstanceAs (FiniteDimensional Real (E × Real))
  have hDFsurj : Function.Surjective (mfderiv J L F (z, b)) :=
    LinearMap.surjective_of_injective hDFinj
  let DF : (E × Real) ≃L[Real] (E × Real) :=
    ContinuousLinearEquiv.ofBijective (mfderiv J L F (z, b))
      (LinearMap.ker_eq_bot.mpr hDFinj)
      (LinearMap.range_eq_top.mpr hDFsurj)
  have hDinv : (mfderiv J L F (z, b)).IsInvertible := by
    refine ⟨DF, ?_⟩
    rfl
  have hfdinv := tail_prod_written_inv (I := I) hFdiff hDinv
  obtain ⟨Psi, hzuPsi, hPsiU, hEqPsi⟩ :=
    DifferentialGeometry.Coordinates.isLocalDiffeomorphAt_of_contMDiffOn'
      (I := J) (J := L) (n := 1) le_rfl
      (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤))
      hUopen hzu (hFU.of_le (by exact_mod_cast le_top)) hfdinv
  have hFPsi : ContMDiffOn J L ∞ F Psi.source :=
    hFU.mono hPsiU
  have hinvPsi : ∀ p ∈ Psi.source,
      (fderiv Real (writtenInExtChartAt J L p F)
        (extChartAt J p p)).IsInvertible := by
    intro p hp
    have hloc : IsLocalDiffeomorphAt J L 1 F p :=
      ⟨Psi, hp, hEqPsi⟩
    have hmfdinv : (mfderiv J L F p).IsInvertible :=
      ⟨hloc.mfderivToContinuousLinearEquiv one_ne_zero,
        hloc.mfderivToContinuousLinearEquiv_coe one_ne_zero⟩
    have hFp : MDifferentiableAt J L F p :=
      (hFPsi.contMDiffAt (Psi.open_source.mem_nhds hp)).mdifferentiableAt
        (by simp)
    exact tail_prod_written_inv (I := I) hFp hmfdinv
  obtain ⟨Phi, hzuPhi, _hPhiPsi, hEqPhi⟩ :=
    DifferentialGeometry.Coordinates.hlocAt_infty'
      (I := J) (J := L) Psi.open_source hzuPsi hFPsi hinvPsi
  exact ⟨Phi, by simpa only [z] using hzuPhi,
    by simpa only [F, f, z] using hEqPhi⟩

/-- On the terminal-time slice, the spatial part of the joint endpoint-time
local inverse agrees near the central endpoint with the fixed-time inverse. -/
theorem lTailInv_slice
    {alpha : E × Real → M} {V : Set E} {K : Set Real}
    {A0 : E} {b : Real}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hbK : b ∈ K)
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hinj : Function.Injective fun B : E ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0 B) :
    let htime :=
      lTailTime_local hVopen hA0V hKopen hbK halpha hinj
    let hfixed :=
      lTail_localDiffeo hVopen hA0V hbK halpha hinj
    (fun y : M ↦ (htime.localInverse (y, b)).1) =ᶠ[nhds (alpha (A0, b))]
      hfixed.localInverse := by
  let F : E × Real → M × Real := fun p ↦ (alpha p, p.2)
  let endMap : E → M := fun A ↦ alpha (A, b)
  let q0 : M × Real := (alpha (A0, b), b)
  let htime := lTailTime_local hVopen hA0V hKopen hbK halpha hinj
  let hfixed := lTail_localDiffeo hVopen hA0V hbK halpha hinj
  have htime0 : htime.localInverse q0 = (A0, b) := by
    simpa only [htime, q0, F] using
      htime.localInverse_left_inv htime.localInverse_mem_target
  have hslice : ContinuousAt (fun y : M ↦ (y, b)) (alpha (A0, b)) :=
    continuousAt_id.prodMk continuousAt_const
  have hinv : ContinuousAt
      (fun y : M ↦ htime.localInverse (y, b)) (alpha (A0, b)) := by
    have htimeCont : ContinuousAt htime.localInverse
        (alpha (A0, b), b) := by
      simpa only [q0] using htime.localInverse_contMDiffAt.continuousAt
    exact ContinuousAt.comp'
      (f := fun y : M ↦ (y, b)) htimeCont hslice
  have hfirst : ContinuousAt
      (fun y : M ↦ (htime.localInverse (y, b)).1) (alpha (A0, b)) :=
    continuousAt_fst.comp hinv
  have htimeSrc :
      {y : M | (y, b) ∈ htime.localInverse.source} ∈
        nhds (alpha (A0, b)) := by
    apply hslice.preimage_mem_nhds
    exact htime.localInverse_open_source.mem_nhds
      htime.localInverse_mem_source
  have hfixedTgt :
      {y : M | (htime.localInverse (y, b)).1 ∈
        hfixed.localInverse.target} ∈ nhds (alpha (A0, b)) := by
    apply hfirst.preimage_mem_nhds
    rw [htime0]
    exact hfixed.localInverse.open_target.mem_nhds
      hfixed.localInverse_mem_target
  filter_upwards [htimeSrc, hfixedTgt] with y hyTime hyTarget
  let A : E := (htime.localInverse (y, b)).1
  have hright : F (htime.localInverse (y, b)) = (y, b) := by
    simpa only [F] using htime.localInverse_right_inv hyTime
  have htimeEq : (htime.localInverse (y, b)).2 = b :=
    congrArg Prod.snd hright
  have hend : endMap A = y := by
    have hfirstEq := congrArg Prod.fst hright
    have hpairEq : htime.localInverse (y, b) = (A, b) :=
      Prod.ext rfl htimeEq
    rw [hpairEq] at hfirstEq
    simpa only [F, endMap] using hfirstEq
  change A = hfixed.localInverse y
  rw [← hend]
  exact (hfixed.localInverse_left_inv hyTarget).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman
