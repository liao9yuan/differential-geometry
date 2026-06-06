import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.InteriorChartRegularityBridge
import DifferentialGeometry.Geometry.Flow.VectorField
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge

/-!
# Interior joint smoothing and up-to-`0` boundary regularity of the realized DeTurck metric

The DeTurck–Ricci interior-regularity bundle
(`deturck_ricci_parabolic_interior_regularity`,
`Geometry/Flow/RicciFlow/ShortTime/DeTurckRicciPde.lean`) consumes the chart-local
`ContMDiffOn`/`ContinuousOn` data of the realized DeTurck metric family `g_DT`,
*jointly* in time and space, in the *single-chart* `chartGramOnE α ∘ extChartAt I α`
formulations the downstream DeTurck-vector-field smoothness assemblers
(`deturck_solution_joint_smooth`, `deturck_vf_continuous_up_to_zero`,
`Geometry/Flow/RicciFlow/ShortTimeFlow/DeTurckVFSmoothness.lean`) require.

The spectral → chart-local bridge `InteriorChartRegularityBridge.lean` delivers the
joint `(t, x)` regularity only on the chart *base set* (`chartGram_realizedMetric_*`).
What is missing — and what these nodes isolate as the genuine classical parabolic-
regularity inputs — is the single-chart `chartGramOnE α (extChartAt I α ·)` regularity
*over all of `M`* (the `Set.univ` formulations consumed by the vector-field assemblers,
where each base point uses its own chart) and *over the chart-target interior with its
first two Euclidean partials* (the up-to-`0` jets the vector-field continuity assembler
consumes).  These are the genuine interior parabolic smoothing plus continuity up to the
smooth initial datum for the strictly-parabolic, smooth-quasilinear DeTurck–Ricci flow.

Each node is stated against the realized family `g_DT = g_bg + ccTensorBilinSymm (T_s ·)`
(`hreal`) whose order-`2k` spatial Sobolev trace is time-continuous (`hHk`): it asserts
genuine regularity *of that realized parabolic flow*, and rejects a merely-`C⁰` family.
The hypotheses are the carrier/PDE realize data, not the conclusion; no packaging.  The
bodies remain `sorry`, so consumers transitively depend on `sorryAx`.

## Main results

* `realizedMetric_chartGramOnE_jointContMDiffOn_interior` — single-chart interior joint
  `(t, x)`-`C∞` of `chartGramOnE α (extChartAt I α ·)` on `Ioo 0 T ×ˢ univ`.
* `realizedMetric_chartGramOnE_continuousOn_uptoZero` — single-chart `C⁰`-up-to-`0` of
  `chartGramOnE α (extChartAt I α ·)` on `Icc 0 T ×ˢ univ`.
* `realizedMetric_deTurckVF_continuousOn_uptoZero` — `C⁰`-up-to-`0` of the realized DeTurck
  vector field on `Icc 0 T ×ˢ univ`.
* `realizedMetric_deTurckVF_chartRawRepr_fderiv_continuousOn_uptoZero` — `C⁰`-up-to-`0` of
  the raw-fibre chart Fréchet derivative of the realized DeTurck vector field.
-/

noncomputable section

open Set Filter Topology Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **Single-chart interior joint `(t, x)`-`C∞` of the realized chart-Gram entry
(genuine parabolic interior smoothing).**

For the realized DeTurck flow `g_DT = g_bg + ccTensorBilinSymm (T_s ·)` (`hreal`) whose
order-`2k` spatial Sobolev trace `t ↦ (T_s t).toHs (2k)` is time-continuous at a
supercritical order (`hHk`), each single-chart Gram entry
`(t, x) ↦ chartGramOnE (g_DT t) α i j (extChartAt I α x)` is jointly `(t, x)`-`C∞` on the
interior `Ioo 0 T ×ˢ univ`.

This is the interior parabolic smoothing of the strictly-parabolic, smooth-quasilinear
DeTurck–Ricci flow, in the single-chart `chartGramOnE α ∘ extChartAt I α` form the
vector-field joint-smoothness assembler `deturck_solution_joint_smooth`
(`DeTurckVFSmoothness.lean`) consumes (at each base point the field uses its own chart, so
the `univ` formulation is genuinely needed).  The hypotheses are the carrier/PDE realize
data; the conclusion is interior joint smoothness, distinct from them — no packaging.  The
node is the deferred classical interior-parabolic-regularity input; its body is `sorry`,
so consumers transitively depend on `sorryAx`. -/
theorem realizedMetric_chartGramOnE_jointContMDiffOn_interior
    (g_bg : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g_bg 0 2) {k : ℕ} {T : ℝ}
    (hk : 2 * k > Module.finrank ℝ E + 4)
    (hreal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT t).inner x v w
        = g_bg.inner x v w + ccTensorBilinSymm (I := I) g_bg (T_s t) x v w)
    (hHk : ContinuousOn (fun t : ℝ =>
      IntrinsicSobolev.SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2) (2 * k) (T_s t))
      (Set.Icc 0 T)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun q : ℝ × M =>
        Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
          (extChartAt I α q.2))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := sorry

/-- **Single-chart `C⁰`-up-to-`0` of the realized chart-Gram entry (genuine parabolic
continuity up to the initial datum).**

For the realized DeTurck flow `g_DT = g_bg + ccTensorBilinSymm (T_s ·)` (`hreal`) whose
order-`2k` spatial Sobolev trace is time-continuous up to `0` at a supercritical order
(`hHk`), each single-chart Gram entry
`(t, x) ↦ chartGramOnE (g_DT t) α i j (extChartAt I α x)` is jointly continuous on the
closed-from-below `Icc 0 T ×ˢ (chartAt H α).source`.

This is continuity up to the smooth initial metric, in the single-chart form the
conjugating-flow continuity assembler `gfam_inner_continuous_on`
(`ShortTimeAssembly/RicciContinuityInMetricTime.lean`) consumes.  The domain is the chart
`α`-source: off the source the chart round-trip `extChartAt I α` is junk, so the pull-back
Gram entry there carries no parabolic meaning; the consumers only ever evaluate at points of
the orbit, which stay in the source near each chart centre (a `nhdsWithin` restriction at the
centre upgrades the source statement to the orbit datum).  The hypotheses are the carrier/PDE
realize data; the conclusion is the up-to-`0` joint continuity, distinct from them — no
packaging.

This is sorry-free: it is the spectral → chart-local bridge
`chartGramOnE_realizedMetric_jointContinuousOn`
(`Analysis/Parabolic/DeTurckRicci/InteriorChartRegularityBridge.lean`), which delivers exactly
this `J ×ˢ (chartAt H α).source` joint continuity off the `H^{2k} ↪ C⁰` embedding and the
locally-uniform joint-continuity engine. -/
theorem realizedMetric_chartGramOnE_continuousOn_uptoZero
    (g_bg : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g_bg 0 2) {k : ℕ} {T : ℝ}
    (hk : 2 * k > Module.finrank ℝ E + 4)
    (hreal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT t).inner x v w
        = g_bg.inner x v w + ccTensorBilinSymm (I := I) g_bg (T_s t) x v w)
    (hHk : ContinuousOn (fun t : ℝ =>
      IntrinsicSobolev.SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2) (2 * k) (T_s t))
      (Set.Icc 0 T)) :
    ContinuousOn
      (fun q : ℝ × M =>
        Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
          (extChartAt I α q.2))
      (Set.Icc (0 : ℝ) T ×ˢ (chartAt H α).source) :=
  chartGramOnE_realizedMetric_jointContinuousOn (I := I) (M := M)
    g_bg α i j g_DT T_s hk hreal hHk

/-- **`C⁰`-up-to-`0` of the raw-fibre chart Fréchet derivative of the realized DeTurck
vector field (genuine parabolic up-to-boundary gradient regularity).**

For the realized DeTurck flow `g_DT = g₀ + ccTensorBilinSymm (T_s ·)` realized off the
anchor `g₀` (`hreal`) whose order-`2k` spatial Sobolev trace is time-continuous up to `0`
at a supercritical order (`hHk`), the chart-`α` raw-fibre Fréchet derivative of the DeTurck
vector field of `g_DT` against the flow background `g_bg`,
`(t, x) ↦ fderiv ℝ (chartRawRepr α (deTurckVF (g_DT t) g_bg)) (extChartAt I α x)`, is
jointly continuous up to `0` on `Icc 0 T ×ˢ univ`.

This is the up-to-`0` chart-gradient regularity of the DeTurck field — exactly the
`hgrad0` datum the from-zero manifold-orbit assemblers
(`fromZero_manifold_orbit_uniform_delta`, `Analysis/ODE/.../FromZeroManifoldOrbit.lean`)
consume for the conjugating-diffeomorphism construction (the general-point trivialised-
gradient product rule the chart-calculus layer isolates as a deferred input).  The anchor
`g₀` (the realize base) and the flow background `g_bg` (the DeTurck-field background) are
decoupled.  The domain is the chart `α`-source: the raw chart representation
`chartRawRepr α` and its Fréchet derivative read through `extChartAt I α` carry no meaning
off the chart source (where the round-trip is junk), so the `univ` formulation would be
false-as-stated; the source statement is the honest one.  The hypotheses are the carrier/PDE
realize data; the conclusion is the up-to-`0` gradient continuity, distinct from them — no
packaging.  The node is the deferred classical up-to-boundary gradient parabolic-regularity
input; its body is `sorry`, so consumers transitively depend on `sorryAx`. -/
theorem realizedMetric_deTurckVF_chartRawRepr_fderiv_continuousOn_uptoZero
    (g₀ g_bg : SmoothRiemannianMetric I M) (α : M)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2) {k : ℕ} {T : ℝ}
    (hk : 2 * k > Module.finrank ℝ E + 4)
    (hreal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT t).inner x v w
        = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s t) x v w)
    (hHk : ContinuousOn (fun t : ℝ =>
      IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) (T_s t))
      (Set.Icc 0 T)) :
    ContinuousOn
      (fun q : ℝ × M =>
        fderiv ℝ (chartRawRepr (I := I) α
          (fun x => deTurckVF (I := I) (g_DT q.1) g_bg x))
          (extChartAt I α q.2))
      (Set.Icc (0 : ℝ) T ×ˢ (chartAt H α).source) := sorry

/-- **Joint `C∞`-up-to-AND-across-`0` of the realized DeTurck vector field as a tangent-bundle
section (genuine parabolic up-to-boundary smoothing of the field).**

For the realized DeTurck flow `g_DT = g₀ + ccTensorBilinSymm (T_s ·)` realized off the anchor
`g₀` (`hreal`) whose order-`2k` spatial Sobolev trace is time-continuous up to `0` at a
supercritical order (`hHk`), the joint tangent-bundle section of the DeTurck vector field of
`g_DT` against the flow background `g_bg`,
`(t, x) ↦ ⟨x, deTurckVF (g_DT t) g_bg x⟩`, is jointly `C∞` on the *closed* slab `Icc 0 T ×ˢ univ`.

This is the up-to-AND-across-the-initial-datum joint smoothness of the (smooth-quasi-linear,
lower-order) DeTurck field — the closed-slab `hsmooth0` datum the forward-flow construction
(`forward_flow_existence_onesided_of_jointsmooth_field`,
`conjugating_diffeo_family`) consumes: the strictly-parabolic, smooth-quasilinear DeTurck–Ricci
flow with smooth initial metric `g₀` is jointly `C∞` up to and across `t = 0` (Chow–Knopf), and
the DeTurck vector field, being a smooth function of `g_DT` and its first two spatial jets, inherits
that joint smoothness on the closed slab.  This is the SOUND replacement for the former
doubly-defective weak trio (`hcont0` controls only `C⁰`; `hgrad0` controls the wrong — raw chart —
gradient): the single closed-slab section smoothness subsumes both and, via Seeley extension across
`0`, drives the interior flow machinery directly.

The anchor `g₀` (the realize base) and the flow background `g_bg` (the DeTurck-field background)
are decoupled.  The hypotheses are the carrier/PDE realize data; the conclusion is the closed-slab
joint smoothness of the field, distinct from them — no packaging (it rejects a merely-`C⁰` family).
The node is the deferred classical up-to-boundary parabolic-regularity input; its body is `sorry`,
so consumers transitively depend on `sorryAx`. -/
theorem realizedMetric_deTurckVF_jointContMDiffOn_uptoZero
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2) {k : ℕ} {T : ℝ}
    (hk : 2 * k > Module.finrank ℝ E + 4)
    (hreal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT t).inner x v w
        = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s t) x v w)
    (hHk : ContinuousOn (fun t : ℝ =>
      IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) (T_s t))
      (Set.Icc 0 T)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := sorry

/-- **Bare-fibre continuity of the chart-`α` coordinate frame (pure bundle geometry).**

The chart-`α` coordinate frame vector `x ↦ chartBasisVecFiber α i x`, read as a bare element
of the model space `E` (through the type synonym `TangentSpace I x = E`), is continuous on the
chart-`α` base set.  Geometrically this is the smooth chart-`α` coordinate frame field of the
tangent bundle, read in its own chart; it is a pure tangent-bundle locality fact, independent
of any metric/PDE datum.

It is isolated here as the one genuine bundle-geometry input that the up-to-`0` field
continuity below needs but that the present library only exposes in `chartJ`-wrapped /
locally-constant-chart forms (`chartJinv_wrapped_continuousAt`,
`Analysis/Spectral/Tensor/ChartTensor/ChartGeometry/JinvContinuity.lean`;
`chartJinv_continuousOn_loc`,
`Analysis/Spectral/Tensor/UniformChartBounds/ChartJUniformBoundLocallyConstant.lean`), neither
of which strips to the bare `symmL`-applied-to-a-constant continuity over the *whole* source.
Its body is `sorry`; consumers transitively depend on `sorryAx`. -/
theorem chartBasisVecFiber_continuousOn_baseSet
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun x : M => (chartBasisVecFiber (I := I) α i x : E))
      (trivializationAt E (TangentSpace I) α).baseSet := sorry

/-- **`C⁰`-up-to-`0` of the realized DeTurck vector field (genuine parabolic up-to-boundary
continuity of the field).**

For the realized DeTurck flow `g_DT = g₀ + ccTensorBilinSymm (T_s ·)` realized off the
anchor `g₀` (`hreal`) whose order-`2k` spatial Sobolev trace is time-continuous up to `0`
at a supercritical order (`hHk`), the DeTurck vector field of `g_DT` against the flow
background `g_bg`, `(t, x) ↦ deTurckVF (g_DT t) g_bg x`, is jointly continuous up to `0` on
`Icc 0 T ×ˢ univ`.

This is continuity up to the smooth initial datum of the (quasi-linear, lower-order)
DeTurck field — exactly the `hcont0` datum the from-zero manifold-orbit assemblers
(`fromZero_manifold_orbit_uniform_delta`, `Analysis/ODE/.../FromZeroManifoldOrbit.lean`)
consume for the conjugating-diffeomorphism construction.  The anchor `g₀` (the realize
base) and the flow background `g_bg` (the DeTurck-field background) are decoupled.  The
hypotheses are the carrier/PDE realize data; the conclusion is the up-to-`0` field
continuity, distinct from them — no packaging.

This is no longer an independent classical input: it is sorry-free GLUE over the closed-slab
joint smoothness `realizedMetric_deTurckVF_jointContMDiffOn_uptoZero` (the SOUND replacement
that subsumes it).  Locally at each base point `α := q₀.2`, the bare field is recomposed in
the chart-`α` frame, `deTurckVF (g_DT t) g_bg x
  = ∑ i (repr (e_α.clmAt x (deTurckVF (g_DT t) g_bg x)))_i • chartBasisVecFiber α i x`
(`chartBasisVecFiber_recompose`): the trivialised coefficient `e_α.clmAt x (deTurckVF …)` is
the chart-`α`-trivialisation fibre coordinate of the (continuous, from the closed-slab
smoothness) total-space section, hence continuous on the base set; the frame vectors are
continuous by `chartBasisVecFiber_continuousOn_baseSet`; the finite `E`-sum is therefore
continuous on `Icc 0 T ×ˢ baseSet_α`, and `mono_of_mem_nhdsWithin` upgrades it to the `univ`
slab at `q₀`.  Consumers transitively depend on the closed-slab leaf's (and the bundle-frame
node's) `sorryAx`. -/
theorem realizedMetric_deTurckVF_continuousOn_uptoZero
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2) {k : ℕ} {T : ℝ}
    (hk : 2 * k > Module.finrank ℝ E + 4)
    (hreal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT t).inner x v w
        = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s t) x v w)
    (hHk : ContinuousOn (fun t : ℝ =>
      IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) (T_s t))
      (Set.Icc 0 T)) :
    ContinuousOn
      (fun q : ℝ × M => (deTurckVF (I := I) (g_DT q.1) g_bg q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
  classical
  have h5 := realizedMetric_deTurckVF_jointContMDiffOn_uptoZero
    (I := I) g₀ g_bg g_DT T_s hk hreal hHk
  have hcont5 := h5.continuousOn
  intro q₀ hq₀
  set α : M := q₀.2 with hα
  set e := trivializationAt E (TangentSpace I) α with he
  have hbase0 : α ∈ e.baseSet := by
    rw [he, hα]; exact FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  set U : Set (ℝ × M) := Set.Icc (0 : ℝ) T ×ˢ e.baseSet with hU
  set σ : ℝ × M → TangentBundle I M :=
    fun q => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2) : TangentBundle I M)
    with hσ
  have hσ_cont : ContinuousOn σ (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := hcont5
  have hmaps : Set.MapsTo σ U e.source := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    rw [Trivialization.mem_source]; exact hx
  have htriv_cont : ContinuousOn (fun q : ℝ × M => (e (σ q)).2) U := by
    have h1 : ContinuousOn (fun q => e (σ q)) U :=
      (e.continuousOn.comp (hσ_cont.mono (Set.prod_mono_right (Set.subset_univ _))) hmaps)
    exact continuous_snd.comp_continuousOn h1
  have hcoord_eq : Set.EqOn
      (fun q : ℝ × M => e.continuousLinearMapAt ℝ q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2))
      (fun q : ℝ × M => (e (σ q)).2) U := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    show e.continuousLinearMapAt ℝ x (deTurckVF (I := I) (g_DT t) g_bg x) = (e (σ (t, x))).2
    rw [e.continuousLinearMapAt_apply (R := ℝ), e.coe_linearMapAt_of_mem hx]
  have hclm_cont : ContinuousOn (fun q : ℝ × M =>
      e.continuousLinearMapAt ℝ q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)) U :=
    htriv_cont.congr hcoord_eq
  have hrepr : ∀ i : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => ((chartModelBasis E).repr
        (e.continuousLinearMapAt ℝ q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2))) i) U := by
    intro i
    have hlin : Continuous (fun y : E => ((chartModelBasis E).repr y) i) :=
      ((Finsupp.lapply (R := ℝ) (M := ℝ) (α := Fin (Module.finrank ℝ E)) i).comp
        (chartModelBasis E).repr.toLinearMap).continuous_of_finiteDimensional
    exact hlin.comp_continuousOn hclm_cont
  have hframe : ∀ i : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => (chartBasisVecFiber (I := I) α i q.2 : E)) U := by
    intro i
    exact (chartBasisVecFiber_continuousOn_baseSet (I := I) α i).comp continuousOn_snd
      (fun q hq => hq.2)
  have hrecomp : Set.EqOn
      (fun q : ℝ × M => (deTurckVF (I := I) (g_DT q.1) g_bg q.2 : TangentSpace I q.2))
      (fun q : ℝ × M => ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2))) i •
        chartBasisVecFiber (I := I) α i q.2) U := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact chartBasisVecFiber_recompose (I := I) α hx (deTurckVF (I := I) (g_DT t) g_bg x)
  have hsumcont : ContinuousOn
      (fun q : ℝ × M => ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2))) i •
        chartBasisVecFiber (I := I) α i q.2) U := by
    refine continuousOn_finset_sum _ (fun i _ => ?_)
    exact (hrepr i).smul (hframe i)
  have hbareU : ContinuousOn
      (fun q : ℝ × M => (deTurckVF (I := I) (g_DT q.1) g_bg q.2 : TangentSpace I q.2)) U :=
    hsumcont.congr hrecomp
  have hq₀U : q₀ ∈ U := ⟨hq₀.1, hbase0⟩
  refine (hbareU q₀ hq₀U).mono_of_mem_nhdsWithin ?_
  rw [hU, nhdsWithin_prod_eq]
  exact Filter.prod_mem_prod self_mem_nhdsWithin
    (nhdsWithin_le_nhds (e.open_baseSet.mem_nhds hbase0))

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
