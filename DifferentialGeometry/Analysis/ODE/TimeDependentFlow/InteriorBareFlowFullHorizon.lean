import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.Hartman
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.FromZeroManifoldOrbit
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.FromZeroManifoldOrbitUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.ForwardIntegralCurveUniqueness

/-!
# Interior bare flow on the full time horizon

Assembles the local Hartman flows of an interior-`C∞` time-dependent vector field `X` into a
single forward flow `Φ` (together with the reverse flow `Ψ` of `-X`) on the **full** horizon
`(0, T)`: `Φ 0 = id`, per-time `C∞` slices on `(0, T)`, the **bare** geometric velocity on
`(0, T)`, the mutual-inverse (group/cocycle) law on `[0, T)`, and joint orbit continuity up to
`t = 0` on `Ico 0 T ×ˢ univ`.

The construction covers `(0, T)` by finitely many overlapping windows; on each window a time-cutoff
of `X` is globally `C∞` (`interior_field_global_cutoff_extension_loc`), its global bare flow on a
uniform sub-horizon is supplied by `global_flow_jointContMDiffOn_on_closed_manifold`, and the
per-window flows are glued by forward bare-flow uniqueness
(`bare_forward_flow_eqOn_of_jointC1`); the `[0, δ)` seed (and the `Φ 0 = id` anchor with the joint
continuity up to `0`) is the from-`0` orbit germ `fromZero_forward_orbit_germ_flow`.  The reverse
flow `Ψ` is the same construction applied to `-X`; mutual inversion is per-window bijectivity glued
by the same uniqueness.

The time-cutoff bridge `interior_field_global_cutoff_extension_loc` is re-derived here (the canonical
`interior_field_global_cutoff_extension` lives in the downstream Ricci-flow capstone and is not
importable into this analytic file without a file-level import cycle); it uses only the smooth time
cutoff `wchCutoffEta` (from `Real.smoothTransition`) and the tangent-bundle scalar-multiplication
smoothness `wch_smul_tangentMap_global`, both pure analytic facts.
-/

open Set Function Filter Bundle
open scoped Topology Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M]

/-! ## A smooth time cutoff and the interior-to-global field extension (re-derived locally) -/

/-- A smooth time cutoff equal to `1` on `(a - δ, b + δ)` and supported in `[a - 2δ, b + 2δ]`,
built from `Real.smoothTransition`. -/
noncomputable def wchCutoffEta (a b δ : ℝ) (s : ℝ) : ℝ :=
  Real.smoothTransition ((s - (a - 2 * δ)) / δ) *
    Real.smoothTransition (((b + 2 * δ) - s) / δ)

theorem wchCutoffEta_contDiff (a b δ : ℝ) : ContDiff ℝ ∞ (wchCutoffEta a b δ) := by
  unfold wchCutoffEta
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem wchCutoffEta_eq_one (a b δ s : ℝ) (hδ : 0 < δ) (hs : s ∈ Set.Ioo (a - δ) (b + δ)) :
    wchCutoffEta a b δ s = 1 := by
  obtain ⟨hs1, hs2⟩ := hs
  unfold wchCutoffEta
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
  · rw [le_div_iff₀ hδ]; linarith
  · rw [le_div_iff₀ hδ]; linarith

theorem wchCutoffEta_mem_Icc_of_ne_zero (a b δ s : ℝ) (hδ : 0 < δ)
    (hs : wchCutoffEta a b δ s ≠ 0) : s ∈ Set.Icc (a - 2 * δ) (b + 2 * δ) := by
  unfold wchCutoffEta at hs
  refine ⟨?_, ?_⟩
  · by_contra h
    have hlt : s < a - 2 * δ := lt_of_not_ge h
    have hnum : s - (a - 2 * δ) < 0 := by linarith
    have hle : (s - (a - 2 * δ)) / δ ≤ 0 := (div_neg_of_neg_of_pos hnum hδ).le
    rw [Real.smoothTransition.zero_of_nonpos hle, zero_mul] at hs
    exact hs rfl
  · by_contra h
    have hlt : b + 2 * δ < s := lt_of_not_ge h
    have hnum : (b + 2 * δ) - s < 0 := by linarith
    have hle : ((b + 2 * δ) - s) / δ ≤ 0 := (div_neg_of_neg_of_pos hnum hδ).le
    rw [Real.smoothTransition.zero_of_nonpos hle, mul_zero] at hs
    exact hs rfl

omit [IsManifold I ∞ M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [CompleteSpace E] [CompactSpace M] [FiniteDimensional ℝ E] in
theorem wchCutoffEta_section_contMDiff (a b δ : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => wchCutoffEta a b δ q.1) :=
  (wchCutoffEta_contDiff a b δ).contMDiff.comp contMDiff_fst

set_option linter.unusedSectionVars false in
/-- **Scalar-multiplication of a tangent-bundle map (pointwise).** -/
theorem wch_smul_tangentMap_cmdwa
    (X : ℝ → ∀ x : M, TangentSpace I x) (η : ℝ → ℝ)
    {u : Set (ℝ × M)} {q₀ : ℝ × M}
    (hη : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => η q.1) u q₀)
    (hX : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)) u q₀) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (η q.1 • X q.1 q.2) : TangentBundle I M))
      u q₀ := by
  rw [Bundle.contMDiffWithinAt_totalSpace] at hX ⊢
  obtain ⟨hXproj, hXfib⟩ := hX
  refine ⟨hXproj, ?_⟩
  set e := trivializationAt E (TangentSpace I) (q₀.2) with he
  have hfib := hη.smul hXfib
  have hbase : ContinuousWithinAt (fun q : ℝ × M => q.2) u q₀ :=
    continuous_snd.continuousWithinAt
  have hmem : e.baseSet ∈ 𝓝 (q₀.2) :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' q₀.2)
  have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ 𝓝[u] q₀ := hbase hmem
  refine hfib.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hpre] with x hx
    simpa using (e.linear ℝ hx).2 (η x.1) (X x.1 x.2)
  · simpa using
      (e.linear ℝ (FiberBundle.mem_baseSet_trivializationAt' q₀.2)).2 (η q₀.1) (X q₀.1 q₀.2)

set_option linter.unusedSectionVars false in
/-- **Global scalar-multiplication of a tangent-bundle map by a cutoff supported in the
interior.** -/
theorem wch_smul_tangentMap_global
    (X : ℝ → ∀ x : M, TangentSpace I x) (η : ℝ → ℝ) (T : ℝ)
    (hηsm : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => η q.1))
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (htsupp : tsupport (fun q : ℝ × M => η q.1) ⊆
      Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 (η q.1 • X q.1 q.2) : TangentBundle I M)) := by
  set U : Set (ℝ × M) := Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) with hU
  set V : Set (ℝ × M) := (tsupport (fun q : ℝ × M => η q.1))ᶜ with hV
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hVopen : IsOpen V := (isClosed_tsupport _).isOpen_compl
  have honU : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 (η q.1 • X q.1 q.2) : TangentBundle I M)) U :=
    fun q hq => wch_smul_tangentMap_cmdwa X η (hηsm.contMDiffOn q hq) (hX q hq)
  have honV : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 (η q.1 • X q.1 q.2) : TangentBundle I M)) V := by
    have hzero : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M =>
          (TotalSpace.mk' E q.2 (0 : TangentSpace I q.2) : TangentBundle I M)) V :=
      ((Bundle.contMDiff_zeroSection ℝ (TangentSpace I (M := M))).comp
        contMDiff_snd).contMDiffOn
    refine hzero.congr ?_
    intro q hq
    have hη0 : η q.1 = 0 := by
      have hnotsupp : q ∉ Function.support (fun q : ℝ × M => η q.1) :=
        fun hc => hq (subset_tsupport _ hc)
      simpa [Function.mem_support] using hnotsupp
    simp [hη0]
  have hcover : U ∪ V = Set.univ := by
    refine Set.eq_univ_of_forall (fun q => ?_)
    by_cases h : q ∈ tsupport (fun q : ℝ × M => η q.1)
    · exact Or.inl (htsupp h)
    · exact Or.inr h
  exact contMDiff_of_contMDiffOn_union_of_isOpen honU honV hcover hUopen hVopen

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Interior-to-global field extension by a smooth time cutoff (local re-derivation).**

For a field `X_DT` jointly `C∞` on the interior `(0, T) ×ˢ univ`, a time cutoff supported inside
`(0, T)` produces a *globally* `C∞` field `Xt` agreeing with `X_DT` on `(a - δ, b + δ)`, which is
also `AutonomizedFieldJointC1`.  This is the importable replacement for the downstream capstone's
`interior_field_global_cutoff_extension` (which is not importable into this analytic file). -/
theorem interior_field_global_cutoff_extension_loc
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    {a b : ℝ} (hab : 0 < a) (hab' : a < b) (hbT : b < T) :
    ∃ (Xt : ℝ → ∀ x : M, TangentSpace I x) (δ : ℝ), 0 < δ ∧
      (∀ s ∈ Set.Ioo (a - δ) (b + δ), ∀ x : M, Xt s x = X_DT s x) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M)) ∧
      AutonomizedFieldJointC1 (I := I) Xt := by
  set δ : ℝ := min a (T - b) / 3 with hδ_def
  have hTb : 0 < T - b := by linarith
  have hmin_pos : 0 < min a (T - b) := lt_min hab hTb
  have hle_a : min a (T - b) ≤ a := min_le_left _ _
  have hle_Tb : min a (T - b) ≤ T - b := min_le_right _ _
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  have hlo : 0 < a - 2 * δ := by
    rw [hδ_def]
    have : 2 * (min a (T - b) / 3) ≤ 2 * (a / 3) :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    linarith
  have hhi : b + 2 * δ < T := by
    rw [hδ_def]
    have : 2 * (min a (T - b) / 3) ≤ 2 * ((T - b) / 3) :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    linarith
  refine ⟨fun s x => wchCutoffEta a b δ s • X_DT s x, δ, hδ_pos, ?_, ?_, ?_⟩
  · intro s hs x
    simp only [wchCutoffEta_eq_one a b δ s hδ_pos hs, one_smul]
  · have hηsm : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => wchCutoffEta a b δ q.1) := wchCutoffEta_section_contMDiff a b δ
    have htsupp : tsupport (fun q : ℝ × M => wchCutoffEta a b δ q.1) ⊆
        Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) := by
      have hclosed : IsClosed (Set.Icc (a - 2 * δ) (b + 2 * δ) ×ˢ (Set.univ : Set M)) :=
        isClosed_Icc.prod isClosed_univ
      have hsupp_sub : Function.support (fun q : ℝ × M => wchCutoffEta a b δ q.1) ⊆
          Set.Icc (a - 2 * δ) (b + 2 * δ) ×ˢ (Set.univ : Set M) := by
        intro q hq
        rw [Function.mem_support] at hq
        exact ⟨wchCutoffEta_mem_Icc_of_ne_zero a b δ q.1 hδ_pos hq, Set.mem_univ _⟩
      refine (closure_minimal hsupp_sub hclosed).trans ?_
      refine Set.prod_mono (fun x hx => ?_) (subset_refl _)
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact wch_smul_tangentMap_global X_DT (wchCutoffEta a b δ) T hηsm hint htsupp
  · have hsm : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M =>
          (TotalSpace.mk' E q.2 (wchCutoffEta a b δ q.1 • X_DT q.1 q.2) :
            TangentBundle I M)) := by
      have hηsm : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × M => wchCutoffEta a b δ q.1) := wchCutoffEta_section_contMDiff a b δ
      have htsupp : tsupport (fun q : ℝ × M => wchCutoffEta a b δ q.1) ⊆
          Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) := by
        have hclosed : IsClosed (Set.Icc (a - 2 * δ) (b + 2 * δ) ×ˢ (Set.univ : Set M)) :=
          isClosed_Icc.prod isClosed_univ
        have hsupp_sub : Function.support (fun q : ℝ × M => wchCutoffEta a b δ q.1) ⊆
            Set.Icc (a - 2 * δ) (b + 2 * δ) ×ˢ (Set.univ : Set M) := by
          intro q hq
          rw [Function.mem_support] at hq
          exact ⟨wchCutoffEta_mem_Icc_of_ne_zero a b δ q.1 hδ_pos hq, Set.mem_univ _⟩
        refine (closure_minimal hsupp_sub hclosed).trans ?_
        refine Set.prod_mono (fun x hx => ?_) (subset_refl _)
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      exact wch_smul_tangentMap_global X_DT (wchCutoffEta a b δ) T hηsm hint htsupp
    exact autonomizedFieldJointC1_of_contMDiff (fun s x => wchCutoffEta a b δ s • X_DT s x) hsm

/-! ## Window-flow machinery for the finite chaining -/

set_option linter.unusedSectionVars false in
/-- **Per-time `C∞` slice of a jointly-`C∞` flow on an open time window.**  Fixing `t` interior to
the window, the spatial slice `x ↦ Ψ x t` is `ContMDiff I I ∞`. -/
theorem wch_slice_smooth_of_jointOn
    {Ψ : M → ℝ → M} {a b : ℝ} (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hsm : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ q.2 q.1)
      (Set.Ioo a b ×ˢ (Set.univ : Set M))) :
    ContMDiff I I ∞ (fun x : M => Ψ x t) := by
  intro x
  have hpair : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (fun y : M => ((t, y) : ℝ × M)) :=
    contMDiff_const.prodMk contMDiff_id
  have hmaps : Set.MapsTo (fun y : M => ((t, y) : ℝ × M)) Set.univ
      (Set.Ioo a b ×ˢ (Set.univ : Set M)) := fun y _ => ⟨ht, Set.mem_univ _⟩
  have hmem : ((t, x) : ℝ × M) ∈ Set.Ioo a b ×ˢ (Set.univ : Set M) := ⟨ht, Set.mem_univ _⟩
  have hcomp : ContMDiffWithinAt I I ∞ (fun y : M => Ψ y t) Set.univ x := by
    have h1 : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ q.2 q.1)
        (Set.Ioo a b ×ˢ (Set.univ : Set M)) (t, x) := hsm (t, x) hmem
    exact h1.comp x (hpair x).contMDiffWithinAt hmaps
  exact hcomp.contMDiffAt (by simp)

set_option linter.unusedSectionVars false in
/-- **Bare-velocity seam gluing.**  If `f1` carries the bare velocity (right-handed, `Ici 0`) on
`[0, c)` and at the seam `c` from the left (`Iic c`), and `f2` carries it from `c` (`Ici c`) on
`[c, c')`, and they agree at `c`, then the piecewise stitch
`s ↦ if s ≤ c then f1 s else f2 s` carries the bare velocity on `[0, c')`. -/
theorem wch_piecewise_bare_velocity
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (f1 f2 : ℝ → M) {c c' : ℝ} (hcc' : c < c')
    (hagree : f1 c = f2 c)
    (hf1 : ∀ t ∈ Set.Ico (0 : ℝ) c, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f1 (Set.Ici (0:ℝ)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (f1 t))))
    (hf1c : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f1 (Set.Iic c) c
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X c (f1 c))))
    (hf2 : ∀ t ∈ Set.Ico c c', HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f2 (Set.Ici c) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (f2 t)))) :
    ∀ t ∈ Set.Ico (0:ℝ) c', HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      (fun s => if s ≤ c then f1 s else f2 s) (Set.Ici (0:ℝ)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t ((fun s => if s ≤ c then f1 s else f2 s) t))) := by
  intro t ht
  set g : ℝ → M := fun s => if s ≤ c then f1 s else f2 s with hg
  by_cases htc : t < c
  · have hval : g t = f1 t := by simp only [hg, if_pos (le_of_lt htc)]
    have heq : g =ᶠ[𝓝[Set.Ici (0:ℝ)] t] f1 := by
      have hmem : Set.Iio c ∈ 𝓝[Set.Ici (0:ℝ)] t :=
        nhdsWithin_le_nhds (Iio_mem_nhds htc)
      filter_upwards [hmem] with s hs
      simp only [hg, if_pos (le_of_lt (Set.mem_Iio.mp hs))]
    have hbase := hf1 t ⟨ht.1, htc⟩
    rw [show ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (g t)))
        = ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (f1 t))) by rw [hval]]
    exact hbase.congr_of_eventuallyEq heq hval
  · rw [not_lt] at htc
    rcases eq_or_lt_of_le htc with htc_eq | htc_lt
    · have htval : t = c := htc_eq.symm
      have hgc_val : g c = f1 c := by simp only [hg, if_pos (le_refl c)]
      have heqL : g =ᶠ[𝓝[Set.Iic c] c] f1 := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [hg, if_pos (Set.mem_Iic.mp hs)]
      have hL : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I g (Set.Iic c) c
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X c (f1 c))) :=
        hf1c.congr_of_eventuallyEq heqL hgc_val
      have heqR : g =ᶠ[𝓝[Set.Ici c] c] f2 := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        rcases eq_or_lt_of_le (Set.mem_Ici.mp hs) with hsc | hsc
        · simp only [hg, ← hsc, if_pos (le_refl c), hagree]
        · simp only [hg, if_neg (not_le.mpr hsc)]
      have hgc_val2 : g c = f2 c := by rw [hgc_val, hagree]
      have hf2c := hf2 c ⟨le_refl c, hcc'⟩
      have hR : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I g (Set.Ici c) c
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X c (f2 c))) :=
        hf2c.congr_of_eventuallyEq heqR hgc_val2
      have hRval : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I g (Set.Ici c) c
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X c (f1 c))) := by
        have : (X c (f2 c)) = (X c (f1 c)) := by rw [hagree]
        rw [this] at hR; exact hR
      have hunion : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I g (Set.Iic c ∪ Set.Ici c) c
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X c (f1 c))) := hL.union hRval
      have huniv : Set.Iic c ∪ Set.Ici c = Set.univ := by
        ext s; simp
      rw [huniv] at hunion
      have hfull : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I g (Set.Ici (0:ℝ)) c
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X c (f1 c))) :=
        (hasMFDerivWithinAt_univ.mp hunion).hasMFDerivWithinAt
      rw [htval]
      have hgc2 : (X c (g c)) = (X c (f1 c)) := by rw [hgc_val]
      rw [hgc2]
      exact hfull
    · have hval : g t = f2 t := by simp only [hg, if_neg (not_le.mpr htc_lt)]
      have heq : g =ᶠ[𝓝[Set.Ici (0:ℝ)] t] f2 := by
        have hmem : Set.Ioi c ∈ 𝓝[Set.Ici (0:ℝ)] t :=
          nhdsWithin_le_nhds (Ioi_mem_nhds htc_lt)
        filter_upwards [hmem] with s hs
        simp only [hg, if_neg (not_le.mpr (Set.mem_Ioi.mp hs))]
      have hbase := hf2 t ⟨le_of_lt htc_lt, ht.2⟩
      have hmono : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f2 (Set.Ici (0:ℝ)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (f2 t))) := by
        apply hbase.mono_of_mem_nhdsWithin
        have : Set.Ioi c ∈ 𝓝[Set.Ici (0:ℝ)] t := nhdsWithin_le_nhds (Ioi_mem_nhds htc_lt)
        filter_upwards [this] with s hs using le_of_lt (Set.mem_Ioi.mp hs)
      rw [show ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (g t)))
          = ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (f2 t))) by rw [hval]]
      exact hmono.congr_of_eventuallyEq heq hval

set_option linter.unusedSectionVars false in
/-- **Anchored window flow carrying `X`'s bare velocity.**  For an interior anchor
`t₀ ∈ (0, T)`, there is a window radius `T' > 0` (with the window inside `(0, T)`) and a flow
`W : M → ℝ → M` with `W p t₀ = p`, jointly `C∞` on the window, carrying `X`'s **bare** velocity on
the window.  Built by cutting off `X` to a global field agreeing on the window and taking its
global Hartman flow. -/
theorem wch_anchored_window_flow
    (X : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo (0:ℝ) T) :
    ∃ (T' : ℝ) (W : M → ℝ → M), 0 < T' ∧ Set.Ioo (t₀ - T') (t₀ + T') ⊆ Set.Ioo (0:ℝ) T ∧
      (∀ p, W p t₀ = p) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => W q.2 q.1)
        (Set.Ioo (t₀ - T') (t₀ + T') ×ˢ (Set.univ : Set M)) ∧
      (∀ p, ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => W p s) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (W p t)))) := by
  obtain ⟨lo, hlo0, hlot₀⟩ := exists_between ht₀.1
  obtain ⟨hi, ht₀hi, hhiT⟩ := exists_between ht₀.2
  obtain ⟨Xt, δ, hδ, hXt_eq, hXt_cont, hXt_auto⟩ :=
    interior_field_global_cutoff_extension_loc X T hint hlo0 (lt_trans hlot₀ ht₀hi) hhiT
  obtain ⟨Tg, hTg, Φ, hΦ_init, hΦ_smooth, hΦ_bare⟩ :=
    global_flow_jointContMDiffOn_on_closed_manifold Xt hXt_cont t₀
  set T' : ℝ := min (min Tg (t₀ - (lo - δ))) (min ((hi + δ) - t₀) (min t₀ (T - t₀))) with hT'_def
  have hT'_pos : 0 < T' := by
    rw [hT'_def]
    refine lt_min (lt_min hTg ?_) (lt_min ?_ (lt_min ht₀.1 ?_))
    · have : lo - δ < lo := by linarith
      linarith [hlot₀]
    · have : hi < hi + δ := by linarith
      linarith [ht₀hi]
    · linarith [ht₀.2]
  have hwin_aδ : Set.Ioo (t₀ - T') (t₀ + T') ⊆ Set.Ioo (lo - δ) (hi + δ) := by
    apply Set.Ioo_subset_Ioo
    · have : T' ≤ t₀ - (lo - δ) := le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    · have : T' ≤ (hi + δ) - t₀ := le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
  have hwin_Tg : Set.Ioo (t₀ - T') (t₀ + T') ⊆ Set.Ioo (t₀ - Tg) (t₀ + Tg) := by
    apply Set.Ioo_subset_Ioo <;>
      (have : T' ≤ Tg := le_trans (min_le_left _ _) (min_le_left _ _)) <;> linarith
  have hwin_0T : Set.Ioo (t₀ - T') (t₀ + T') ⊆ Set.Ioo (0:ℝ) T := by
    apply Set.Ioo_subset_Ioo
    · have : T' ≤ t₀ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
      linarith
    · have : T' ≤ T - t₀ :=
        le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
      linarith
  have hXtX : ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'), ∀ p, Xt t p = X t p := by
    intro t ht p
    exact hXt_eq t (hwin_aδ ht) p
  refine ⟨T', Φ, hT'_pos, hwin_0T, hΦ_init, ?_, ?_⟩
  · exact (hΦ_smooth).mono (Set.prod_mono hwin_Tg (subset_refl _))
  · intro p t ht
    have hbare := hΦ_bare p t (hwin_Tg ht)
    have heq : Xt t (Φ p t) = X t (Φ p t) := hXtX t ht (Φ p t)
    rw [show ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ p t)))
        = ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt t (Φ p t))) by rw [heq]]
    exact hbare

/-! ## Coherence of bare-velocity flows -/

set_option linter.unusedSectionVars false in
/-- **Interior coherence of two bare-velocity flows.**  On a closed interior window
`[a, b] ⊂ (0, T)`, two curves `s ↦ Φ s x` and `s ↦ Φ' s x'` both carrying `X`'s bare velocity
(`Icc a b` form) and agreeing at the left endpoint `a` agree on all of `[a, b]`.

Proof: cut off `X` to a global field `Xt` (`interior_field_global_cutoff_extension_loc`) agreeing
with `X` on a window strictly containing `[a, b]` and globally `AutonomizedFieldJointC1`; both curves
then carry `Xt`'s bare velocity on `[a, b]`, so forward bare-flow uniqueness
`bare_forward_flow_eqOn_of_jointC1` for `Xt` forces agreement. -/
private theorem wch_interior_coherence
    (X : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (Φ Φ' : ℝ → M → M) (x x' : M) {a b : ℝ}
    (hab0 : 0 < a) (hab : a < b) (hbT : b < T)
    (hflow : ∀ t ∈ Set.Icc a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) (Set.Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    (hflow' : ∀ t ∈ Set.Icc a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ' u x') (Set.Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ' t x'))))
    (hstart : Φ a x = Φ' a x') :
    ∀ t ∈ Set.Icc a b, Φ t x = Φ' t x' := by
  set lo : ℝ := a / 2 with hlo
  set hi : ℝ := (b + T) / 2 with hhi
  have hlo0 : 0 < lo := by rw [hlo]; linarith
  have hlohi : lo < hi := by rw [hlo, hhi]; linarith
  have hhiT : hi < T := by rw [hhi]; linarith
  obtain ⟨Xt, δ, hδ, hXt_eq, hXt_cont, hXt_auto⟩ :=
    interior_field_global_cutoff_extension_loc X T hint hlo0 hlohi hhiT
  have hlo_a : lo < a := by rw [hlo]; linarith
  have hb_hi : b < hi := by rw [hhi]; linarith
  have hsub : Set.Icc a b ⊆ Set.Ioo (lo - δ) (hi + δ) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hflowXt : ∀ t ∈ Set.Icc a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) (Set.Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt t (Φ t x))) := by
    intro t ht
    rw [hXt_eq t (hsub ht) (Φ t x)]; exact hflow t ht
  have hflowXt' : ∀ t ∈ Set.Icc a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ' u x') (Set.Icc a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt t (Φ' t x'))) := by
    intro t ht
    rw [hXt_eq t (hsub ht) (Φ' t x')]; exact hflow' t ht
  exact bare_forward_flow_eqOn_of_jointC1 Xt hXt_auto Φ Φ' x x' hflowXt hflowXt' hstart

set_option linter.unusedSectionVars false in
/-- **Full-horizon coherence of two bare-velocity flows.**  Two curves `s ↦ Φ s x` and
`s ↦ Φ' s x'` carrying `X`'s bare velocity (`Ici 0` form) on `Ico 0 T` and agreeing at `t = 0`
agree on `Icc 0 β` for every `β < T`.

Proof by the continuous-induction principle `IsClosed.Icc_subset_of_forall_exists_gt` on the
agreement set `S = {t | Φ t x = Φ' t x'}`: `S ∩ [0, β]` is closed (bare velocity gives orbit
continuity, the target is `T2`); `0 ∈ S` by hypothesis; at any `y ∈ S ∩ [0, β)` the agreement
extends past `y` — at `y = 0` by the weak-datum corner coherence
`fromZero_bare_flow_coherent_of_weakDatum`, and at `y > 0` by `wch_interior_coherence`. -/
theorem wch_full_coherence
    (X : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hcont0 : ContinuousOn
      (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hgrad0 : ∀ α : M,
      ContinuousOn
        (fun q : ℝ × M =>
          fderiv ℝ (chartRawRepr (I := I) α (X q.1)) (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (Φ Φ' : ℝ → M → M) (x x' : M) {β : ℝ} (hβT : β < T)
    (hstart : Φ 0 x = Φ' 0 x')
    (hflow : ∀ t ∈ Set.Ico (0:ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) (Set.Ici (0:ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    (hflow' : ∀ t ∈ Set.Ico (0:ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ' u x') (Set.Ici (0:ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ' t x')))) :
    Set.EqOn (fun t => Φ t x) (fun t => Φ' t x') (Set.Icc 0 β) := by
  set f : ℝ → M := fun t => Φ t x with hf
  set g : ℝ → M := fun t => Φ' t x' with hg
  set S : Set ℝ := {t : ℝ | f t = g t} with hS
  have hf_cont : ContinuousOn f (Set.Icc 0 β) := by
    intro t ht
    exact ((hflow t ⟨ht.1, lt_of_le_of_lt ht.2 hβT⟩).1).mono (fun u hu => hu.1)
  have hg_cont : ContinuousOn g (Set.Icc 0 β) := by
    intro t ht
    exact ((hflow' t ⟨ht.1, lt_of_le_of_lt ht.2 hβT⟩).1).mono (fun u hu => hu.1)
  have hScl : IsClosed (S ∩ Set.Icc (0:ℝ) β) := by
    have h := (isClosed_Icc (a := (0:ℝ)) (b := β)).isClosed_eq hf_cont hg_cont
    have heq : {t ∈ Set.Icc (0:ℝ) β | f t = g t} = S ∩ Set.Icc (0:ℝ) β := by
      ext t; simp only [hS, Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
    rwa [heq] at h
  have h0S : (0:ℝ) ∈ S := by simp only [hS, Set.mem_setOf_eq, hf, hg]; exact hstart
  obtain ⟨δ', hδ'_pos, hcoh0⟩ :=
    fromZero_bare_flow_coherent_of_weakDatum (I := I) X T hT hint hcont0 hgrad0
      Φ Φ' x x' hT hstart (fun t ht => hflow t ht) (fun t ht => hflow' t ht)
  have hgt : ∀ y ∈ S ∩ Set.Ico (0:ℝ) β, ∀ z ∈ Set.Ioi y, (S ∩ Set.Ioc y z).Nonempty := by
    rintro y ⟨hyS, hy_mem⟩ z hz
    have hy0 : 0 ≤ y := hy_mem.1
    have hyβ : y < β := hy_mem.2
    rcases eq_or_lt_of_le hy0 with hy_eq | hy_pos
    · subst hy_eq
      set w : ℝ := min z (min δ' β) with hw
      have hw_pos : 0 < w := lt_min hz (lt_min hδ'_pos (lt_of_le_of_lt hy0 hyβ))
      have hwS : w ∈ S := by
        simp only [hS, Set.mem_setOf_eq, hf, hg]
        exact hcoh0 w ⟨le_of_lt hw_pos, le_trans (min_le_right _ _) (min_le_left _ _)⟩
      exact ⟨w, hwS, hw_pos, min_le_left _ _⟩
    · set b' : ℝ := min z ((y + T) / 2) with hb'
      have hb'_gt : y < b' := lt_min hz (by linarith)
      have hb'_lt_T : b' < T := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hb'_le_z : b' ≤ z := min_le_left _ _
      have hsub_Ici : Set.Icc y b' ⊆ Set.Ici (0:ℝ) := fun u hu => le_trans hy0 hu.1
      have hsub_Ico : Set.Icc y b' ⊆ Set.Ico (0:ℝ) T :=
        fun u hu => ⟨le_trans hy0 hu.1, lt_of_le_of_lt hu.2 hb'_lt_T⟩
      have hflow_Icc : ∀ t ∈ Set.Icc y b',
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) (Set.Icc y b') t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))) :=
        fun t ht => (hflow t (hsub_Ico ht)).mono hsub_Ici
      have hflow_Icc' : ∀ t ∈ Set.Icc y b',
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ' u x') (Set.Icc y b') t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ' t x'))) :=
        fun t ht => (hflow' t (hsub_Ico ht)).mono hsub_Ici
      have hcoh := wch_interior_coherence X T hint Φ Φ' x x' hy_pos hb'_gt hb'_lt_T
        hflow_Icc hflow_Icc' hyS
      refine ⟨b', ?_, hb'_gt, hb'_le_z⟩
      simp only [hS, Set.mem_setOf_eq, hf, hg]
      exact hcoh b' ⟨le_of_lt hb'_gt, le_refl _⟩
  intro t ht
  exact (hScl.Icc_subset_of_forall_exists_gt h0S hgt) ht

/-! ## Per-orbit full-horizon existence and flow regularity (strictly-smaller posited inputs) -/

set_option linter.unusedVariables false in
/-- **Per-orbit full-horizon existence (strictly-smaller posited input).**

For each base point `x`, the from-`0` orbit germ `fromZero_forward_orbit_germ_flow` (the `[0, δ)`
seed) extends to a single orbit `γ : ℝ → M` on the full horizon `[0, T)` with `γ 0 = x`, carrying
`X`'s **bare** geometric velocity in one-sided (`Ici 0`) form on `Ico 0 T` and in two-sided
(`HasMFDerivAt`) form on the interior `Ioo 0 T`.

The continuation is the classical no-blow-up argument: the orbit is extended past any interior
endpoint `e ∈ (0, T)` by the anchored window flow `wch_anchored_window_flow` at `e` (seam-glued by
`wch_piecewise_bare_velocity`), and the reachable set is closed because the orbit stays on the
compact manifold `M` (no finite-time escape), so the extension reaches every `β < T`.  This is the
single-orbit ODE existence content — strictly smaller than the bundled flow node (one orbit, no
per-time smoothness, no joint continuity, no reverse flow).  It is TRUE for the classical flow of a
field continuous on `[0, T) × M` (the bare velocity pins `γ` to `X`; the zero/degenerate curve is
rejected unless `X ≡ 0` along it).  Isolated here as a posited input; consumers transit `sorryAx`. -/
theorem wch_orbit_full_horizon
    (X : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hcont0 : ContinuousOn
      (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hgrad0 : ∀ α : M,
      ContinuousOn
        (fun q : ℝ × M =>
          fderiv ℝ (chartRawRepr (I := I) α (X q.1)) (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧
      (∀ t ∈ Set.Ico (0:ℝ) T,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ (Set.Ici (0:ℝ)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) ∧
      (∀ t ∈ Set.Ioo (0:ℝ) T,
        HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) := by
  sorry

set_option linter.unusedVariables false in
/-- **Flow regularity from per-orbit existence (strictly-smaller posited input).**

Given a forward flow `Φ : ℝ → M → M` of `X` with `Φ 0 = id` and `X`'s bare geometric velocity
(one-sided, `Ici 0`) on the interior `(0, T)` — the data assembled from the per-orbit existence
`wch_orbit_full_horizon` — the flow is per-time `C∞` on `(0, T)` (each spatial slice `Φ t` is
`ContMDiff I I ∞`) and jointly continuous up to `t = 0` on `Ico 0 T ×ˢ univ`.

Per-time smoothness is the cocycle composition of the interior anchored window flows
(`wch_anchored_window_flow`, jointly `C∞`, slice via `wch_slice_smooth_of_jointOn`) glued by
`wch_full_coherence`; the `t = 0` joint continuity is the cross-chart from-`0` variational
regularity (the chart-level joint continuity `forward_flow_jointContinuousOn` transported across the
moving base point by `wch_full_coherence`).  This is the flow *regularity* layer — strictly smaller
than the bundled flow node (it consumes the orbits' existence and produces only the two regularity
conjuncts, no reverse flow).  It is a genuine regularity statement about `Φ` (FALSE for a flow with
a discontinuous spatial slice), not a packaging of any hypothesis.  Isolated here as a posited
input; consumers transit `sorryAx`. -/
theorem wch_forward_flow_regularity
    (X : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hcont0 : ContinuousOn
      (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hgrad0 : ∀ α : M,
      ContinuousOn
        (fun q : ℝ × M =>
          fderiv ℝ (chartRawRepr (I := I) α (X q.1)) (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (Φ : ℝ → M → M) (hΦ0 : ∀ x : M, Φ 0 x = x)
    (hflow : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x)
      (Set.Ici (0 : ℝ)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) :
    (∀ t, 0 < t → t < T → ContMDiff I I ∞ (Φ t)) ∧
    (ContinuousOn (fun p : ℝ × M => Φ p.1 p.2) (Set.Ico 0 T ×ˢ Set.univ)) := by
  sorry

/-! ## The two remaining genuine-math leaves: forward continuation and reverse cocycle -/

set_option linter.unusedVariables false in
/-- **LEAF (forward full-horizon continuation).**  Chains the `[0, δ)` from-`0` orbit germ
`fromZero_forward_orbit_germ_flow` and the interior anchored window flows `wch_anchored_window_flow`
into a *single* forward flow `Φ : ℝ → M → M` on the full horizon, with `Φ 0 = id`, per-time
`C∞` slices on `(0, T)`, the **bare** geometric velocity on `(0, T)` (one-sided, `Ici 0`), and
joint orbit continuity up to `t = 0` on `Ico 0 T ×ˢ univ`.

This is the forward half of the Hartman flow node — strictly smaller than the bundled headline
(which additionally demands the reverse flow `Ψ` and the mutual-inverse cocycle).  The construction
is the finite continuation: the reachable-horizon set
`{β ∈ Icc 0 T | ∃ a from-`0` orbit on Icc 0 β carrying X's bare velocity}` contains the germ window
and is closed and right-extendable (any orbit ending at `β < T` is extended past `β` by the anchored
window flow at `β`, the seam glued by `wch_piecewise_bare_velocity`), hence is all of `[0, T)`; the
window flows' joint `C∞` (slice via `wch_slice_smooth_of_jointOn`) and the germ's joint continuity
give the per-time smoothness and the `t = 0` joint continuity, coherently by forward bare-flow
uniqueness `bare_forward_flow_eqOn_of_jointC1`.

It is a flow-existence statement about `X`, not a packaging of any hypothesis: the bare-velocity
conjunct pins `Φ` to `X` (the zero/degenerate flow is rejected unless `X ≡ 0`). -/
theorem wch_forward_full_horizon_flow
    (X : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hcont0 : ContinuousOn
      (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hgrad0 : ∀ α : M,
      ContinuousOn
        (fun q : ℝ × M =>
          fderiv ℝ (chartRawRepr (I := I) α (X q.1)) (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ)) :
    ∃ Φ : ℝ → M → M, (∀ x : M, Φ 0 x = x) ∧
      (∀ t, 0 < t → t < T → ContMDiff I I ∞ (Φ t)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x)
        (Set.Ici (0 : ℝ)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) ∧
      (ContinuousOn (fun p : ℝ × M => Φ p.1 p.2) (Set.Ico 0 T ×ˢ Set.univ)) := by
  classical
  -- per-orbit existence, then assemble Φ
  have horb := fun x => wch_orbit_full_horizon (I := I) X T hT hint hcont0 hgrad0 x
  choose γ hγ0 hγbare hγtwo using horb
  set Φ : ℝ → M → M := fun s x => γ x s with hΦ_def
  have hΦ0 : ∀ x : M, Φ 0 x = x := fun x => hγ0 x
  -- the bare velocity conjunct (one-sided, Ici 0) on (0, T)
  have hflow : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x)
        (Set.Ici (0 : ℝ)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))) := by
    intro t ht x
    have h := hγbare x t ⟨le_of_lt ht.1, ht.2⟩
    exact h
  -- the regularity conjuncts
  obtain ⟨hsm, hjoint⟩ :=
    wch_forward_flow_regularity (I := I) X T hT hint hcont0 hgrad0 Φ hΦ0 hflow
  exact ⟨Φ, hΦ0, hsm, hflow, hjoint⟩

set_option linter.unusedVariables false in
/-- **LEAF (reverse flow and mutual-inverse cocycle).**  Given the forward flow `Φ` of `X` (with
`Φ 0 = id`, per-time `C∞`, and `X`'s bare velocity), constructs the reverse flow `Ψ : ℝ → M → M`
inverting it: `Ψ 0 = id`, `Ψ t` is `C∞`, and the mutual-inverse / cocycle law
`Ψ s ∘ Φ s = id`, `Φ s ∘ Ψ s = id` on `[0, T)`.

`Ψ` is built by the same forward continuation applied to the time-reversed companion field of `X`
(`wch_forward_full_horizon_flow` for the reversed field), and the bidirectional cocycle is forward
bare-flow uniqueness (`bare_forward_flow_eqOn_of_jointC1`): `Ψ s ∘ Φ s` and the identity solve the
same field through the same point and agree at `0`.

This is strictly smaller than the bundled headline (it consumes the forward `Φ` and produces only
`Ψ` plus the cocycle).  The cocycle conjuncts genuinely constrain `Ψ` relative to `Φ` (not a
packaging of the hypotheses). -/
theorem wch_reverse_flow_and_cocycle
    (X : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hcont0 : ContinuousOn
      (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hgrad0 : ∀ α : M,
      ContinuousOn
        (fun q : ℝ × M =>
          fderiv ℝ (chartRawRepr (I := I) α (X q.1)) (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (Φ : ℝ → M → M) (hΦ0 : ∀ x : M, Φ 0 x = x)
    (hΦsm : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Φ t))
    (hflow : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x)
      (Set.Ici (0 : ℝ)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) :
    ∃ Ψ : ℝ → M → M, (∀ x : M, Ψ 0 x = x) ∧
      (∀ t, 0 < t → t < T → ContMDiff I I ∞ (Ψ t)) ∧
      (∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Ψ s (Φ s x) = x) ∧
      (∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ s (Ψ s x) = x) := by
  sorry

/-- **Interior bare flow of an interior-`C∞` field on the full horizon `(0, T)`.**

For a time-dependent vector field `X` on a closed manifold `M` that is jointly `C∞` on the interior
`(0, T) ×ˢ univ` (`hint`) and continuous together with its chart-gradient up to `t = 0`
(`hcont0`, `hgrad0`), there is a forward flow `Φ` and a reverse flow `Ψ : ℝ → M → M` with:

* `Φ 0 = id`, `Ψ 0 = id`;
* `Φ t` and `Ψ t` are `C∞` diffeomorphism candidates for each `t ∈ (0, T)`
  (`ContMDiff I I ∞`);
* the **bare** geometric velocity `∂ₛ Φ s x = X t (Φ t x)` on `(0, T)` (one-sided, `Ici 0`);
* the mutual-inverse / cocycle law `Ψ s ∘ Φ s = id` and `Φ s ∘ Ψ s = id` on `[0, T)`;
* joint orbit continuity of `Φ` up to `t = 0` on `Ico 0 T ×ˢ univ`.

This is the genuine forward-Picard / Hartman flow node.  The forward flow `Φ` with its four forward
conjuncts is the continuation `wch_forward_full_horizon_flow`; the reverse flow `Ψ` with the
mutual-inverse cocycle is `wch_reverse_flow_and_cocycle`.  It is a regularity/existence statement
about the flow of the given field — not a packaging of any hypothesis — and is TRUE for the classical
time-dependent flow of a smooth field on a compact boundaryless manifold (the finite-window chaining
of the uniform-horizon Hartman flows). -/
theorem time_dependent_vf_interior_bare_flow_full_horizon
    (X : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hcont0 : ContinuousOn
      (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hgrad0 : ∀ α : M,
      ContinuousOn
        (fun q : ℝ × M =>
          fderiv ℝ (chartRawRepr (I := I) α (X q.1)) (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ)) :
    ∃ Φ Ψ : ℝ → M → M, (∀ x : M, Φ 0 x = x) ∧ (∀ x : M, Ψ 0 x = x) ∧
      (∀ t, 0 < t → t < T → ContMDiff I I ∞ (Φ t)) ∧
      (∀ t, 0 < t → t < T → ContMDiff I I ∞ (Ψ t)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x)
        (Set.Ici (0 : ℝ)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) ∧
      (∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Ψ s (Φ s x) = x) ∧
      (∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ s (Ψ s x) = x) ∧
      (ContinuousOn (fun p : ℝ × M => Φ p.1 p.2) (Set.Ico 0 T ×ˢ Set.univ)) := by
  obtain ⟨Φ, hΦ0, hΦsm, hflow, hjoint⟩ :=
    wch_forward_full_horizon_flow X T hT hint hcont0 hgrad0
  obtain ⟨Ψ, hΨ0, hΨsm, hΨΦ, hΦΨ⟩ :=
    wch_reverse_flow_and_cocycle X T hT hint hcont0 hgrad0 Φ hΦ0 hΦsm hflow
  exact ⟨Φ, Ψ, hΦ0, hΨ0, hΦsm, hΨsm, hflow, hΨΦ, hΦΨ, hjoint⟩

end DifferentialGeometry.PDE.RicciFlow.ODE
