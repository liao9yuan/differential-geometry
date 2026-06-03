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
/-- **Right-continuity at `t = 0` of the moving spatial Jacobian, from joint smoothness.**

For a flow `Φ` that is jointly `C∞` on an open product slab `Ioo lo hi ×ˢ univ` containing
`t = 0` (`lo < 0 < hi`), the `E`-valued moving spatial Jacobian
`s ↦ (mfderiv I I (Φ s) x v : E)` is right-continuous at `0`.

The proof reconstructs the bare Jacobian from the chart-conjugated derivative supplied by
`ContMDiffAt.mfderiv`.  Writing `c := extChartAt I x` (a fixed chart, centred at the basepoint
`x = Φ 0 x`), the conjugated quantity
`P s := inTangentCoordinates I I (fun _ => x) (fun s => Φ s x) (fun s => mfderiv I I (Φ s) x) 0 s`
is continuous at `0` by `ContMDiffAt.mfderiv` (degree `0`).  Through
`inTangentCoordinates_eq_mfderiv_comp` the bare Jacobian applied to `v` equals
`mfderiv c.symm (c (Φ s x)) (P s w₀)` with the *fixed* vector `w₀ := mfderiv c x v` — the source
chart-derivative factor is constant in `s`, while the target factor is the derivative of the
*fixed* chart-inverse map `c.symm` at the moving point `c (Φ s x)`, which is continuous in `s`
because `s ↦ Φ s x` is continuous and the derivative of a fixed `C∞` map depends continuously on
its basepoint.  Applying a continuous family of maps to a continuous family of vectors is
continuous, giving the result. -/
private theorem flow_mfderiv_continuousWithinAt_zero_of_jointSmooth
    (Φ : ℝ → M → M) {lo hi : ℝ} (hlo : lo < 0) (hhi : 0 < hi)
    (hΦsm : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2)
      (Set.Ioo lo hi ×ˢ (Set.univ : Set M)))
    (x : M) (v : TangentSpace I x) :
    ContinuousWithinAt (fun s : ℝ => (mfderiv I I (fun y : M => Φ s y) x v : E))
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
  -- Reconstruct the bare Jacobian: `B s = (D s)⁻¹ (P s)`, expressed through the *bundled* tangent
  -- map of the fixed chart-inverse `c.symm`, on the chart neighbourhood of `0`.
  have hrecon : (fun s : ℝ => (mfderiv I I (fun y : M => Φ s y) x v : E))
      =ᶠ[nhds (0 : ℝ)]
      (fun s : ℝ => (tangentMapWithin 𝓘(ℝ, E) I c.symm (Set.range I)
        (TotalSpace.mk' E (c (Φ s x)) (P s))).2) := by
    filter_upwards [hsrc_nhds] with s hs
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
    rw [hPval]
    change mfderiv I I (fun y : M => Φ s y) x v
      = mfderivWithin 𝓘(ℝ, E) I c.symm (Set.range I) (c (Φ s x))
          (mfderiv I 𝓘(ℝ, E) c (Φ s x) (mfderiv I I (fun y : M => Φ s y) x v))
    -- cancel `c.symm`-derivative against `c`-derivative (chart round-trip at `Φ s x`)
    have hΦsrc' : Φ s x ∈ (extChartAt I y₀).source := by rw [extChartAt_source]; exact hΦsrc
    have hcancel := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I) (x := y₀)
      (y := Φ s x) hΦsrc'
    have := congrArg (fun L : TangentSpace I (Φ s x) →L[ℝ] TangentSpace I (Φ s x) =>
        L (mfderiv I I (fun y : M => Φ s y) x v)) hcancel
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hc] using this.symm
  -- Continuity of the RHS: the bundled tangent map of the fixed map `c.symm` is continuous on
  -- `c.target` (`ContMDiffOn.continuousOn_tangentMapWithin`), precomposed with the continuous
  -- bundle-valued path `s ↦ ⟨c (Φ s x), P s⟩` (whose base stays in `c.target` near `0`), then
  -- read off the fibre through the fixed trivialization at `y₀`.
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
  have hRHScont : ContinuousAt
      (fun s : ℝ => (tangentMapWithin 𝓘(ℝ, E) I c.symm (Set.range I)
        (TotalSpace.mk' E (c (Φ s x)) (P s))).2) 0 := by
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
    -- (`htm` composed with `hpath` gives joint continuity of the bundled tangent map along the
    -- path; what remains is the bare-fibre reading below.)
    -- THE REMAINING GAP: read off the fibre coordinate `(·).2 : TangentBundle I M → E` as a
    -- *bare* `E`-valued continuous map.  The bundle topology makes `(·).2` continuous only after
    -- trivialising at the (moving) basepoint `Φ s x`; the bare coercion `(p.2 : E)` (the def-eq
    -- `TangentSpace I (Φ s x) = E`) differs from that trivialised reading by the target
    -- coordinate change `tangentCoordChange I (Φ s x) y₀ (Φ s x)`, which is the genuine
    -- moving-target-chart factor.  Establishing continuity of the bare fibre reading is the
    -- single irreducible analytic step (a fixed-target-chart Euclidean `ContDiffOn.fderivWithin`
    -- computation), isolated here as the lemma's sole `sorry`.
    have hcomp_ctgt : ContinuousAt (fun s : ℝ => (tangentMapWithin 𝓘(ℝ, E) I c.symm c.target
        (TotalSpace.mk' E (c (Φ s x)) (P s))).2) 0 := by
      sorry
    -- switch the within-set `c.target → range I` pointwise near `0` (they agree on `c.target`).
    refine hcomp_ctgt.congr ?_
    filter_upwards [hbase_nhds] with s hs
    have heqd : mfderivWithin 𝓘(ℝ, E) I c.symm c.target (c (Φ s x))
        = mfderivWithin 𝓘(ℝ, E) I c.symm (Set.range I) (c (Φ s x)) := by
      rw [mfderivWithin_of_isOpen hctgt_open hs,
        mfderivWithin_of_mem_nhds (Filter.mem_of_superset (hctgt_open.mem_nhds hs)
          (extChartAt_target_subset_range y₀))]
    change (tangentMapWithin 𝓘(ℝ, E) I c.symm c.target (TotalSpace.mk' E (c (Φ s x)) (P s))).2
      = (tangentMapWithin 𝓘(ℝ, E) I c.symm (Set.range I) (TotalSpace.mk' E (c (Φ s x)) (P s))).2
    rw [tangentMapWithin_snd, tangentMapWithin_snd, heqd]
  have hBcont : ContinuousAt (fun s : ℝ => (mfderiv I I (fun y : M => Φ s y) x v : E)) 0 :=
    hRHScont.congr hrecon.symm
  exact hBcont.continuousWithinAt

/-- A time-dependent field `X_DT` that is jointly `C∞` up to AND across `t = 0` on the
CLOSED slab `Icc 0 T ×ˢ univ` (`hsmooth0`) admits a single forward flow `Φ : ℝ → M → M`
with `Φ 0 = id`, per-time diffeomorphisms on `(0,T)`, the bare geometric velocity
`∂ₛ Φ s x = X_DT t (Φ t x)` on `(0,T)`, and `t = 0` right-continuity of both the orbit
`s ↦ Φ s x` and the moving spatial Jacobian `s ↦ mfderiv I I (Φ s) x v`.  The single
closed-slab smoothness `hsmooth0` subsumes the former interior-`C∞` + `C⁰`-to-`0` +
`C¹`-chart-gradient-to-`0` trio.

The flow `Φ` is CONSTRUCTED (sorry-free) by smoothly extending the field across `t = 0`
(`seeley_time_extend`) and running the closed-manifold full-interval flow engine
(`global_flow_full_interval_on_closed_manifold`).  The basepoint fixing `Φ 0 = id`, the bare
geometric velocity on `(0,T)`, and the orbit right-continuity at `0` are all discharged from that
construction; the moving-Jacobian right-continuity is `flow_mfderiv_continuousWithinAt_zero_of_jointSmooth`.

TWO obligations remain isolated as `sorry` (so this theorem still transitively depends on
`sorryAx`): (i) the per-time diffeomorphism witnesses on `(0,T)`, which need a genuine *reverse
flow* (the time-`t→0` backward map) and its mutual inverse with `Φ t` — a standalone two-parameter
/ autonomous-group construction extending the engine's output; (ii) inside the moving-Jacobian
lemma, the bare `E`-valued fibre reading of a bundled tangent map (the moving-target-chart factor),
a fixed-target-chart Euclidean `fderivWithin` step. -/
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
        ContinuousWithinAt (fun s : ℝ => (mfderiv I I (fun y : M => Φ s y) x v : E))
          (Set.Ici (0 : ℝ)) 0) := by
  obtain ⟨Xext, hXsm, hXeq⟩ := seeley_time_extend X_DT T hT hsmooth0
  obtain ⟨Φ, lo, hi, hlo, hhi, hΦ0, hΦsm, hΦvel⟩ :=
    global_flow_full_interval_on_closed_manifold Xext hXsm T hT
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
  refine ⟨Φ, hΦ0, ?_, hvel_eq, ?_, ?_⟩
  · -- C2: per-time diffeomorphisms on `(0,T)` (reverse-flow mutual inverse).
    sorry
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
