import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.FlatIdentity
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.IntervalGlobalFlow
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.CorrectedChartAnchor
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.VariationalEquation.CorrectedVariationalEndpoint
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.FieldTimeExtension
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.BoundaryExtension.SeeleyTimeExtension
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.BoundaryExtension.FullIntervalFlow

/-!
# Forward (one-sided) flow of the DeTurck vector field

Produces the forward integral flow of the time-dependent DeTurck vector field on `[0, T)` from a
joint-`C¹` field hypothesis, together with the time-zero continuity extension used downstream.
-/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

set_option linter.unusedSectionVars false in
/-- **Right-continuity at `t = 0` of the bundle-valued moving spatial Jacobian, from joint
smoothness.**

For a flow `Φ` that is jointly `C∞` on an open product slab `Ioo lo hi ×ˢ univ` containing
`t = 0` (`lo < 0 < hi`), the tangent-bundle datum `s ↦ ⟨Φ s x, mfderiv I I (Φ s) x v⟩` — the moving
basepoint together with its spatial Jacobian, tracked coherently inside `TangentBundle I M` — is
right-continuous at `0`.

This is the unique SOUND time-continuity statement for the moving Jacobian: the *bare*
`E`-coercion `s ↦ (mfderiv I I (Φ s) x v : E)` of the fibre at the MOVING basepoint `Φ s x` is in
general discontinuous (the trivialization at `Φ s x` jumps as the basepoint drifts across charts),
so it is replaced by the trivialization-free bundle reading.

The proof is the bundled tangent map of the joint flow.  Writing `c := extChartAt I y₀` for the
fixed chart centred at `y₀ := Φ 0 x`, the chart-conjugated spatial derivative
`P s := inTangentCoordinates I I (fun _ => x) (fun s => Φ s x) (fun s => mfderiv I I (Φ s) x) 0 s v`
is continuous at `0` by `ContMDiffAt.mfderiv` (degree `0`).  The bundle-valued path
`s ↦ ⟨c (Φ s x), P s⟩ : TangentBundle 𝓘(ℝ, E) E` is then continuous at `0` (orbit continuity ×
`P` continuity through the model-space homeomorphism), and the *fixed* chart-inverse map `c.symm`
has a continuous bundled tangent map on the open `c.target`
(`ContMDiffOn.continuousOn_tangentMapWithin`); composing the two gives continuity at `0` of
`s ↦ tangentMapWithin 𝓘(ℝ, E) I c.symm c.target ⟨c (Φ s x), P s⟩`.  That tangent map equals the
target datum `⟨Φ s x, mfderiv I I (Φ s) x v⟩` on the chart neighbourhood (base by the chart
round-trip `c.symm (c (Φ s x)) = Φ s x`; fibre by `inTangentCoordinates_eq_mfderiv_comp` cancelling
the `c`-derivative against the `c.symm`-derivative), so continuity transfers by `congr`. -/
private theorem flow_mfderiv_continuousWithinAt_zero_of_jointSmooth
    (Φ : ℝ → M → M) {lo hi : ℝ} (hlo : lo < 0) (hhi : 0 < hi)
    (hΦsm : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2)
      (Set.Ioo lo hi ×ˢ (Set.univ : Set M)))
    (x : M) (v : TangentSpace I x) :
    ContinuousWithinAt (fun s : ℝ =>
        (⟨Φ s x, mfderiv I I (fun y : M => Φ s y) x v⟩ : TangentBundle I M))
      (Set.Ici (0 : ℝ)) 0 := by
  classical
  -- Source chart centred at `x`, target chart centred at `y₀ := Φ 0 x` (both fixed).
  set y₀ : M := Φ 0 x with hy₀
  set c : PartialEquiv M E := extChartAt I y₀ with hc
  have hmem0 : ((0 : ℝ), x) ∈ Set.Ioo lo hi ×ˢ (Set.univ : Set M) :=
    ⟨⟨hlo, hhi⟩, Set.mem_univ _⟩
  have hopen : IsOpen (Set.Ioo lo hi ×ˢ (Set.univ : Set M)) := isOpen_Ioo.prod isOpen_univ
  have hf : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) (0, x) :=
    (hΦsm _ hmem0).contMDiffAt (hopen.mem_nhds hmem0)
  have hg : ContMDiffAt 𝓘(ℝ, ℝ) I 0 (fun _ : ℝ => x) 0 := contMDiffAt_const
  -- The chart-conjugated spatial derivative is continuous at `0` (`ContMDiffAt.mfderiv`, degree 0).
  have hP : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E →L[ℝ] E) 0
      (inTangentCoordinates I I (fun _ : ℝ => x) (fun s : ℝ => Φ s x)
        (fun s : ℝ => mfderiv I I (fun y : M => Φ s y) x) 0) 0 :=
    hf.mfderiv (fun s y => Φ s y) (fun _ => x) hg (by norm_num)
  -- … hence its application to the fixed vector `v` is continuous at `0`.
  set P : ℝ → E := fun s => inTangentCoordinates I I (fun _ : ℝ => x) (fun s : ℝ => Φ s x)
      (fun s : ℝ => mfderiv I I (fun y : M => Φ s y) x) 0 s v with hP_def
  have hPcont : ContinuousAt P 0 := hP.continuousAt.clm_apply continuousAt_const
  -- The orbit is continuous at `0` (the joint flow composed with `s ↦ (s, x)`).
  have horbit_cont : ContinuousAt (fun s : ℝ => Φ s x) 0 := by
    have hpair : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞ (fun s : ℝ => (s, x)) 0 :=
      contMDiffAt_id.prodMk contMDiffAt_const
    exact (hf.comp 0 hpair).continuousAt
  -- Near `0`, the orbit stays in the target chart source.
  have hsrc_nhds : (fun s : ℝ => Φ s x) ⁻¹' (chartAt H y₀).source ∈ nhds (0 : ℝ) :=
    horbit_cont.preimage_mem_nhds ((chartAt H y₀).open_source.mem_nhds (mem_chart_source H y₀))
  -- The bundle-valued target datum `⟨Φ s x, mfderiv I I (Φ s) x v⟩` is, on the chart
  -- neighbourhood of `0`, the bundled tangent map of the fixed chart-inverse `c.symm` applied to
  -- the continuous bundle path `s ↦ ⟨c (Φ s x), P s⟩` — the base by the chart round-trip
  -- `c.symm (c (Φ s x)) = Φ s x`, the fibre by `inTangentCoordinates_eq_mfderiv_comp` cancelling
  -- the `c`-derivative against the `c.symm`-derivative.
  have hctgt_open : IsOpen c.target := isOpen_extChartAt_target (I := I) y₀
  have hc0_tgt : c (Φ 0 x) ∈ c.target := by
    rw [show Φ 0 x = y₀ from rfl]; exact mem_extChartAt_target (I := I) y₀
  -- base of the bundle path is continuous at `0` and stays in `c.target` near `0`.
  have hbase_cont : ContinuousAt (fun s : ℝ => c (Φ s x)) 0 := by
    have hcont_c : ContinuousAt c (Φ 0 x) := by
      rw [show Φ 0 x = y₀ from rfl]
      exact continuousAt_extChartAt (I := I) y₀
    exact ContinuousAt.comp (g := fun y : M => c y) (f := fun s : ℝ => Φ s x) hcont_c horbit_cont
  have hbase_nhds : (fun s : ℝ => c (Φ s x)) ⁻¹' c.target ∈ nhds (0 : ℝ) :=
    hbase_cont.preimage_mem_nhds (hctgt_open.mem_nhds hc0_tgt)
  -- Per-point fibre identity (bare `E`): the tangent-map fibre equals the bare moving Jacobian.
  have hfib : ∀ s : ℝ, Φ s x ∈ (chartAt H y₀).source →
      mfderivWithin 𝓘(ℝ, E) I c.symm c.target (c (Φ s x)) (P s)
        = mfderiv I I (fun y : M => Φ s y) x v := by
    intro s hs
    have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
    have hΦsrc : Φ s x ∈ (chartAt H y₀).source := hs
    -- `inTangentCoordinates` written as a composition of chart derivatives.
    have hcomp := inTangentCoordinates_eq_mfderiv_comp (I := I) (I' := I)
      (f := fun _ : ℝ => x) (g := fun s : ℝ => Φ s x)
      (ϕ := fun s : ℝ => mfderiv I I (fun y : M => Φ s y) x) (x₀ := 0) (x := s) hxsrc hΦsrc
    -- the source chart-inverse derivative is the identity (chart centred at the basepoint)
    have hS₀ : mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) (extChartAt I x x)
        = ContinuousLinearMap.id ℝ (TangentSpace I x) :=
      mfderivWithin_range_extChartAt_symm (I := I) (x := x)
    have hPval : P s = mfderiv I 𝓘(ℝ, E) c (Φ s x) (mfderiv I I (fun y : M => Φ s y) x v) := by
      have hap := congrArg (fun L : E →L[ℝ] E => L v) hcomp
      simp only [hP_def, hS₀] at hap ⊢
      rw [hap]
      rfl
    -- replace `c.target` by `range I` (open, so the within-derivatives agree near `Φ s x`).
    have hΦtgt : c (Φ s x) ∈ c.target := by
      rw [hc]; exact (extChartAt I y₀).map_source (by rw [extChartAt_source]; exact hΦsrc)
    have heqd : mfderivWithin 𝓘(ℝ, E) I c.symm c.target (c (Φ s x))
        = mfderivWithin 𝓘(ℝ, E) I c.symm (Set.range I) (c (Φ s x)) := by
      rw [mfderivWithin_of_isOpen hctgt_open hΦtgt,
        mfderivWithin_of_mem_nhds (Filter.mem_of_superset (hctgt_open.mem_nhds hΦtgt)
          (extChartAt_target_subset_range y₀))]
    rw [heqd, hPval]
    -- cancel `c.symm`-derivative against `c`-derivative (chart round-trip at `Φ s x`)
    have hΦsrc' : Φ s x ∈ (extChartAt I y₀).source := by rw [extChartAt_source]; exact hΦsrc
    have hcancel := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I) (x := y₀)
      (y := Φ s x) hΦsrc'
    have := congrArg (fun L : TangentSpace I (Φ s x) →L[ℝ] TangentSpace I (Φ s x) =>
        L (mfderiv I I (fun y : M => Φ s y) x v)) hcancel
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hc] using this
  -- Eventually-equal bundle datum: `⟨Φ s x, mfderiv …⟩ = tangentMapWithin c.symm c.target ⟨c (Φ s x), P s⟩`.
  have hrecon : (fun s : ℝ =>
        (⟨Φ s x, mfderiv I I (fun y : M => Φ s y) x v⟩ : TangentBundle I M))
      =ᶠ[nhds (0 : ℝ)]
      (fun s : ℝ => tangentMapWithin 𝓘(ℝ, E) I c.symm c.target
        (TotalSpace.mk' E (c (Φ s x)) (P s))) := by
    filter_upwards [hsrc_nhds] with s hs
    have hbase : c.symm (c (Φ s x)) = Φ s x := by
      rw [hc]; exact (extChartAt I y₀).left_inv (by rw [extChartAt_source]; exact hs)
    -- `tangentMapWithin c.symm c.target ⟨c (Φ s x), P s⟩ = ⟨c.symm (c (Φ s x)), mfderivWithin … (P s)⟩`.
    change (⟨Φ s x, mfderiv I I (fun y : M => Φ s y) x v⟩ : TangentBundle I M)
      = ⟨c.symm (c (Φ s x)), mfderivWithin 𝓘(ℝ, E) I c.symm c.target (c (Φ s x)) (P s)⟩
    refine Bundle.TotalSpace.ext (x := ⟨Φ s x, mfderiv I I (fun y : M => Φ s y) x v⟩)
      (y := ⟨c.symm (c (Φ s x)), mfderivWithin 𝓘(ℝ, E) I c.symm c.target (c (Φ s x)) (P s)⟩)
      hbase.symm ?_
    -- both fibres are the same element of `E` (`TangentSpace I _` is the constant `E`); the only
    -- residual is the chart-inverse-vs-bare Jacobian identity `hfib`.
    exact heq_of_eq (hfib s hs).symm
  -- Continuity of the RHS: the bundled tangent map of the fixed map `c.symm` is continuous on
  -- `c.target` (`ContMDiffOn.continuousOn_tangentMapWithin`), precomposed with the continuous
  -- bundle-valued path `s ↦ ⟨c (Φ s x), P s⟩` (whose base stays in `c.target` near `0`).
  have hRHScont : ContinuousAt
      (fun s : ℝ => tangentMapWithin 𝓘(ℝ, E) I c.symm c.target
        (TotalSpace.mk' E (c (Φ s x)) (P s))) 0 := by
    -- continuity of the bundled tangent map of the fixed map `c.symm` on the open `c.target`
    have hcsm : ContMDiffOn 𝓘(ℝ, E) I 1 c.symm c.target :=
      (contMDiffOn_extChartAt_symm (I := I) (n := ∞) y₀).of_le (by
        exact le_of_lt (by exact_mod_cast ENat.coe_lt_top 1))
    have htm : ContinuousOn (tangentMapWithin 𝓘(ℝ, E) I c.symm c.target)
        (Bundle.TotalSpace.proj ⁻¹' c.target) :=
      hcsm.continuousOn_tangentMapWithin le_rfl hctgt_open.uniqueMDiffOn
    -- the bundle-valued path `s ↦ ⟨c (Φ s x), P s⟩`, continuous via the model-space homeomorphism
    have hpath : ContinuousAt
        (fun s : ℝ => (TotalSpace.mk' E (c (Φ s x)) (P s) : TangentBundle 𝓘(ℝ, E) E)) 0 := by
      have hpair : ContinuousAt (fun s : ℝ => ((c (Φ s x), P s) : ModelProd E E)) 0 :=
        hbase_cont.prodMk hPcont
      exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E) (H := E)).symm.continuous.continuousAt.comp
        hpair
    -- the path lands in `π ⁻¹' c.target` near `0`, so `htm` restricts to a `ContinuousAt`.
    have htgt_nhds : Bundle.TotalSpace.proj ⁻¹' c.target ∈
        nhds (TotalSpace.mk' E (c (Φ 0 x)) (P 0) : TangentBundle 𝓘(ℝ, E) E) :=
      (hctgt_open.preimage (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E)))).mem_nhds
        hc0_tgt
    have htm_at : ContinuousAt (tangentMapWithin 𝓘(ℝ, E) I c.symm c.target)
        (TotalSpace.mk' E (c (Φ 0 x)) (P 0)) := htm.continuousAt htgt_nhds
    exact ContinuousAt.comp'
      (g := tangentMapWithin 𝓘(ℝ, E) I c.symm c.target)
      (f := fun s : ℝ => (TotalSpace.mk' E (c (Φ s x)) (P s) : TangentBundle 𝓘(ℝ, E) E))
      htm_at hpath
  exact (hRHScont.congr hrecon.symm).continuousWithinAt

/-- A time-dependent field `X_DT` that is jointly `C∞` up to AND across `t = 0` on the
CLOSED slab `Icc 0 T ×ˢ univ` (`hsmooth0`) admits a single forward flow `Φ : ℝ → M → M`
with `Φ 0 = id`, per-time diffeomorphisms on `(0,T)`, the bare geometric velocity
`∂ₛ Φ s x = X_DT t (Φ t x)` on `(0,T)`, `t = 0` right-continuity of the orbit `s ↦ Φ s x`, and
`t = 0` right-continuity of the bundle-valued moving spatial Jacobian
`s ↦ ⟨Φ s x, mfderiv I I (Φ s) x v⟩`.  The single closed-slab smoothness `hsmooth0` subsumes the
former interior-`C∞` + `C⁰`-to-`0` + `C¹`-chart-gradient-to-`0` trio.

The whole theorem is proven sorry-free.  The flow `Φ` (and its reverse `Ψ`) is CONSTRUCTED by
smoothly extending the field across `t = 0` (`seeley_time_extend`) and running the closed-manifold
full-interval flow-with-reverse engine (`global_flow_full_interval_with_reverse_on_closed_manifold`):

* `Φ 0 = id`, the bare geometric velocity on `(0,T)`, and the orbit right-continuity at `0` are
  read off from the engine's output;
* the per-time diffeomorphism witnesses on `(0,T)` are assembled by
  `time_dependent_vf_diffeomorph_slice_of_smooth_bijective` from the per-slice smoothness of `Φ t`
  (joint smoothness restricted to a slice) and `Ψ t` together with the two engine mutual-inverse
  identities `Ψ t (Φ t x) = x`, `Φ t (Ψ t x) = x` (valid on `Ico 0 hi ⊇ Ioo 0 T`);
* the bundle-valued moving-Jacobian right-continuity is
  `flow_mfderiv_continuousWithinAt_zero_of_jointSmooth` (the bundled tangent map of the joint flow).

The bundle-valued Jacobian conjunct is the unique SOUND time-continuity statement at the moving
basepoint `Φ s x`: the bare `E`-coercion of the fibre is discontinuous (the trivialization at
`Φ s x` jumps across charts), so the basepoint and its Jacobian are tracked coherently inside
`TangentBundle I M`. -/
theorem forward_flow_existence_onesided_of_jointsmooth_field
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hsmooth0 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ)) :
    ∃ Φ : ℝ → M → M, (∀ x : M, Φ 0 x = x) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x)
        (Set.Ici (0 : ℝ)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φ t x)))) ∧
      (∀ x : M, ContinuousWithinAt (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) 0) ∧
      (∀ (x : M) (v : TangentSpace I x),
        ContinuousWithinAt (fun s : ℝ =>
            (⟨Φ s x, mfderiv I I (fun y : M => Φ s y) x v⟩ : TangentBundle I M))
          (Set.Ici (0 : ℝ)) 0) := by
  obtain ⟨Xext, hXsm, hXeq⟩ := seeley_time_extend X_DT T hT hsmooth0
  obtain ⟨Φ, Ψ, lo, hi, hlo, hhi, hΦ0, hΦsm, hΦvel, hΨsm, hΨΦ, hΦΨ⟩ :=
    global_flow_full_interval_with_reverse_on_closed_manifold Xext hXsm T hT
  -- `Ioo 0 T ⊆ Ioo lo hi` (from `lo < 0` and `T < hi`).
  have hsub : Set.Ioo (0 : ℝ) T ⊆ Set.Ioo lo hi := fun t ht =>
    ⟨lt_trans hlo ht.1, lt_trans ht.2 hhi⟩
  -- The orbit velocity, with `Xext` rewritten to `X_DT` on the closed slab.
  have hvel_eq : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φ t x))) := by
    intro t ht x
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hat : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Xext t (Φ t x))) := hΦvel t (hsub ht) x
    have hrw : Xext t (Φ t x) = X_DT t (Φ t x) := hXeq t htIcc (Φ t x)
    rw [hrw] at hat
    exact hat.hasMFDerivWithinAt
  -- Each slice `Φ t` (for `t ∈ Ioo lo hi`) is smooth: the joint smoothness restricted to the
  -- slice `{t} × M`.
  have hΦ_slice : ∀ t ∈ Set.Ioo lo hi, ContMDiff I I ∞ (Φ t) := by
    intro t ht x
    have hmem : ((t, x) : ℝ × M) ∈ Set.Ioo lo hi ×ˢ (Set.univ : Set M) :=
      ⟨ht, Set.mem_univ _⟩
    have hxsm : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2)
        (Set.Ioo lo hi ×ˢ (Set.univ : Set M)) (t, x) := hΦsm _ hmem
    have hpair : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞ (fun y : M => ((t, y) : ℝ × M)) x :=
      contMDiffAt_const.prodMk contMDiffAt_id
    have hmaps : Set.MapsTo (fun y : M => ((t, y) : ℝ × M)) (Set.univ : Set M)
        (Set.Ioo lo hi ×ˢ (Set.univ : Set M)) := fun y _ => ⟨ht, Set.mem_univ _⟩
    have hcomp := hxsm.comp x hpair.contMDiffWithinAt hmaps
    simpa using hcomp.contMDiffAt Filter.univ_mem
  refine ⟨Φ, hΦ0, ?_, hvel_eq, ?_, ?_⟩
  · -- C2: per-time diffeomorphisms on `(0,T)`, assembled from per-slice smoothness of `Φ t` / `Ψ t`
    -- and the engine's two mutual-inverse identities (`t ∈ Ioo 0 T ⊆ Ico 0 hi`).
    intro t ht
    have ht0 : 0 < t := ht.1
    have htHi : t < hi := lt_trans ht.2 hhi
    have htIco : t ∈ Set.Ico (0 : ℝ) hi := ⟨ht0.le, htHi⟩
    obtain ⟨d, hd_fwd, _hd_rev⟩ :=
      time_dependent_vf_diffeomorph_slice_of_smooth_bijective (Φ t) (Ψ t)
        (hΦ_slice t (hsub ht)) (hΨsm t ht0 htHi)
        (fun x => hΨΦ t htIco x) (fun x => hΦΨ t htIco x)
    exact ⟨d, hd_fwd⟩
  · -- C4: `t = 0` right-continuity of the orbit.
    intro x
    have hmem : ((0 : ℝ), x) ∈ Set.Ioo lo hi ×ˢ (Set.univ : Set M) :=
      ⟨⟨hlo, lt_trans hT hhi⟩, Set.mem_univ _⟩
    have hopen : IsOpen (Set.Ioo lo hi ×ˢ (Set.univ : Set M)) := isOpen_Ioo.prod isOpen_univ
    have hjoint : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) (0, x) :=
      (hΦsm _ hmem).contMDiffAt (hopen.mem_nhds hmem)
    have hpair : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun s : ℝ => (s, x)) 0 := contMDiffAt_id.prodMk contMDiffAt_const
    have horbit : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun s : ℝ => Φ s x) 0 :=
      hjoint.comp 0 hpair
    exact horbit.continuousAt.continuousWithinAt
  · -- C5: `t = 0` right-continuity of the moving spatial Jacobian.
    intro x v
    exact flow_mfderiv_continuousWithinAt_zero_of_jointSmooth Φ hlo (lt_trans hT hhi) hΦsm x v

end DifferentialGeometry.PDE.RicciFlow
