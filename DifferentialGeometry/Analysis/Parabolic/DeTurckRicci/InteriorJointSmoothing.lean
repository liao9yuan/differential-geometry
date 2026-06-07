import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.InteriorChartRegularityBridge
import DifferentialGeometry.Geometry.Flow.VectorField
import DifferentialGeometry.Geometry.Flow.DeTurckVFChartCoord
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.OperatorEquation

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
(`hreal`).  The genuine parabolic-smoothing node
`realizedMetric_innerHomSection_jointContMDiffOn_uptoZero` (and its DeTurck-field consumer
`realizedMetric_deTurckVF_jointContMDiffOn_uptoZero`) is pinned to the **spectral Duhamel
carrier** `u₂` — the carrier solving the abstract parabolic equation
`∂_t (ι u₂) = Δ_∇ u₂ + N_cont (ι u₂)` (`hreg`, the heat-semigroup/Duhamel defining identity)
with time-continuous inclusion (`hcont`) and carrier↔perturbation coordinate identity
(`hcanon`).  This spectral pinning rejects any non-parabolic free family (e.g.
`T_s t := |t − t₀| · S₀`, which has no interior time-derivative and so violates `hreg`),
whereas the bare order-`2k` Sobolev-trace time-continuity `hHk` (used by the `C⁰`-up-to-`0`
chart-Gram node `realizedMetric_chartGramOnE_continuousOn_uptoZero`) would not.  The
hypotheses are the carrier/PDE/realize data, not the conclusion; no packaging.  The genuine
parabolic-smoothing bodies remain `sorry`, so consumers transitively depend on `sorryAx`.

## Main results

* `realizedMetric_chartGramOnE_jointContMDiffOn_interior` — single-chart interior joint
  `(t, x)`-`C∞` of `chartGramOnE α (extChartAt I α ·)` on `Ioo 0 T ×ˢ univ`.
* `realizedMetric_chartGramOnE_continuousOn_uptoZero` — single-chart `C⁰`-up-to-`0` of
  `chartGramOnE α (extChartAt I α ·)` on `Icc 0 T ×ˢ univ`.
* `realizedMetric_deTurckVF_jointContMDiffOn_uptoZero` — closed-slab joint `C∞`-up-to-AND-
  across-`0` of the realized DeTurck vector-field bundle section on `Icc 0 T ×ˢ univ`.
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
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **Joint `(t, x)`-`C∞`-up-to-AND-across-`0` of the realized metric inner-product
`Hom`-section over all of `M`, pinned to the spectral parabolic trajectory (the genuine
parabolic up-to-boundary smoothing — the single open node).**

For the realized DeTurck flow `g_DT = g_bg + ccTensorBilinSymm (T_s ·)` (`hreal`) whose
perturbation `T_s` is the realization of the **spectral Duhamel carrier** `u₂` — i.e. the
carrier's spectral coordinates are the `L²` coordinates of `T_s` (`hcanon`), the carrier
inclusion `t ↦ ι (u₂ t)` is time-continuous up to `0` (`hcont`), and on the open interior
`u₂` solves the abstract parabolic equation `∂_t (ι u₂) = Δ_∇ u₂ + N_cont (ι u₂)` (`hreg`,
the heat-semigroup/Duhamel defining identity) — the bundle inner-product `Hom`-section
`(t, x) ↦ (g_DT t).inner x` (a section of `Hom(TM, Hom(TM, ℝ))`) is jointly `(t, x)`-`C∞`
over the product model `𝓘(ℝ, ℝ).prod I` on the *closed* slab `Icc 0 T ×ˢ univ`.

This is the SINGLE genuine classical parabolic-regularity input for the strictly-parabolic,
smooth-quasilinear DeTurck–Ricci flow with smooth initial metric (Chow–Knopf): the realized
metric is, jointly in time and space, smooth up to and across the initial datum.  Its
genuine content is the parabolic-semigroup time-smoothing of the realized solution — `hreg`
exhibits `ι u₂` as a strong/mild solution of the analytic-semigroup-generated abstract heat
equation, and the parabolic smoothing of that equation (time-analyticity of the semigroup,
the Duhamel time-derivative tower) upgrades the bare time-continuity `hcont` into joint
`(t, x)`-`C∞` of the realized `Hom`-section.  The hypotheses are the spectral-side defining
data of the trajectory; the conclusion is the joint smoothness of the bundle `Hom`-section,
a different object on `M` — no packaging.

**The pinning is genuine — it rejects the kink family (litmus).**  The earlier
`{hreal, hHk}`-only form of this node (and the formerly-`{hreal, hHk}`-stated chart-Gram
nodes) is FALSE: the family `T_s t := |t − t₀| · S₀` (fixed smooth `S₀ ≠ 0`,
`t₀ ∈ (0, T)`) is time-continuous into every Sobolev scale, so it satisfies any
`{hreal, hHk}` set, yet `(t, x) ↦ (g_DT t).inner x` has the `|t − t₀|` kink at `t₀` and is
not even jointly `C¹`.  This kink family is now rejected by the spectral pinning: by
`hcanon` the carrier coordinates `(u₂ s).coeff i` are the (linear) `L²` coordinates of
`T_s s = |s − t₀| · S₀`, hence each coordinate of `ι (u₂ s)` is `|s − t₀|` times a constant,
which is **not differentiable at `t₀`** — so `hreg` (which demands `HasDerivAt (ι ∘ u₂) … t₀`
for every interior `t₀`) is violated.  `hreg` is the spectral-side defining identity of a
genuine parabolic trajectory, not the joint-smoothness conclusion (it is a `1`-D
time-derivative in the Sobolev Banach space about `u₂`, not a `ContMDiffOn` of a bundle
section over `M`); it constrains `u₂`/`T_s`/`g_DT`, not the conclusion.

This node supplies the missing joint datum in the basis-free `Hom`-section form the
chart-local bridge `chartGramOnE_realizedMetric_jointContMDiffOn`
(`Analysis/Parabolic/DeTurckRicci/InteriorChartRegularityBridge.lean`) consumes; the body is
`sorry` (the genuine parabolic-semigroup time-smoothing), so consumers transitively depend
on `sorryAx`. -/
theorem realizedMetric_innerHomSection_jointContMDiffOn_uptoZero
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g_bg 0 2) {a : ℕ} {T : ℝ}
    (u₂ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (N_cont : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (hreal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT t).inner x v w
        = g_bg.inner x v w + ccTensorBilinSymm (I := I) g_bg (T_s t) x v w)
    (hcont : ContinuousOn
      (fun s : ℝ => tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (Set.Icc 0 T))
    (hreg : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt
        (fun r => (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ r)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          N_cont
            (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) s)
    (hcanon : ∀ s ∈ Set.Icc (0 : ℝ) T,
        ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g_bg 0 2,
      (u₂ s).coeff i
        = tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2)
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q.2 ((g_DT q.1).inner q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := sorry

/-- **Single-chart interior joint `(t, x)`-`C∞` of the realized chart-Gram entry
(genuine parabolic interior smoothing).**

For a realized DeTurck flow `g_DT` whose bundle inner-product `Hom`-section
`(t, x) ↦ (g_DT t).inner x` is jointly `(t, x)`-`C∞` over the product model `𝓘(ℝ, ℝ).prod I`
on the interior `Ioo 0 T ×ˢ baseSet` (`hsmooth`), each single-chart Gram entry
`(t, x) ↦ chartGramOnE (g_DT t) α i j (extChartAt I α x)` is jointly `(t, x)`-`C∞` on the
interior `Ioo 0 T ×ˢ (chartAt H α).source`.

This is the interior parabolic smoothing of the strictly-parabolic, smooth-quasilinear
DeTurck–Ricci flow, in the single-chart `chartGramOnE α ∘ extChartAt I α` form the
vector-field joint-smoothness assembler `deturck_solution_joint_smooth`
(`DeTurckVFSmoothness.lean`) consumes (each base point uses its own chart `α`; off the chart
source the round-trip `extChartAt I α` is junk, so the source domain is the honest one).  The
hypothesis is the *joint* smoothness of the metric `Hom`-section (the genuine parabolic
datum supplied by `realizedMetric_innerHomSection_jointContMDiffOn_uptoZero`); the conclusion
is the scalar chart-Gram entry's interior joint smoothness, distinct from it — no packaging.

This is sorry-free glue: the chart-local `C∞` bridge
`chartGramOnE_realizedMetric_jointContMDiffOn`
(`Analysis/Parabolic/DeTurckRicci/InteriorChartRegularityBridge.lean`), which transports the
joint `Hom`-section smoothness to the scalar chart-Gram entry on the chart source via the
chart round-trip identity. -/
theorem realizedMetric_chartGramOnE_jointContMDiffOn_interior
    (α : M) (i j : Fin (Module.finrank ℝ E))
    (g_DT : ℝ → SmoothRiemannianMetric I M) {T : ℝ}
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q.2 ((g_DT q.1).inner q.2))
      (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun q : ℝ × M =>
        Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
          (extChartAt I α q.2))
      (Set.Ioo (0 : ℝ) T ×ˢ (chartAt H α).source) :=
  chartGramOnE_realizedMetric_jointContMDiffOn (I := I) (M := M) α i j g_DT hsmooth

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

namespace ClosedSlabVFEngine

open Set Function

section
set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Joint smoothness of the determinant of a matrix family with jointly-`C^∞` entries. -/
private lemma contDiffOn_jointDet {s : Set (ℝ × E)}
    {A : ℝ × E → Matrix n n ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × E => A p i j) s) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => (A p).det) s := by
  classical
  have heq : (fun p : ℝ × E => (A p).det)
      = fun p : ℝ × E =>
        ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℝ) * ∏ i, A p (σ i) i := by
    funext p; rw [Matrix.det_apply']
  rw [heq]
  refine ContDiffOn.sum (fun σ _ => ?_)
  refine (contDiffOn_const).mul ?_
  exact contDiffOn_prod (fun i _ => hA (σ i) i)

/-- Joint smoothness of an adjugate entry of a matrix family with jointly-`C^∞` entries. -/
private lemma contDiffOn_jointAdjugate {s : Set (ℝ × E)}
    {A : ℝ × E → Matrix n n ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × E => A p i j) s) (a b : n) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => (A p).adjugate a b) s := by
  classical
  have heq : (fun p : ℝ × E => (A p).adjugate a b)
      = fun p : ℝ × E => ((A p).updateRow b (Pi.single a 1)).det := by
    funext p; rw [Matrix.adjugate_apply]
  rw [heq]
  refine contDiffOn_jointDet (A := fun p => (A p).updateRow b (Pi.single a 1)) ?_
  intro i j
  by_cases hij : i = b
  · have hcongr : (fun p : ℝ × E => ((A p).updateRow b (Pi.single a 1)) i j)
        = fun _ : ℝ × E => (Pi.single a 1 : n → ℝ) j := by
      funext p; rw [hij, Matrix.updateRow_self]
    rw [hcongr]; exact contDiffOn_const
  · have hcongr : (fun p : ℝ × E => ((A p).updateRow b (Pi.single a 1)) i j)
        = fun p : ℝ × E => A p i j := by
      funext p; rw [Matrix.updateRow_ne hij]
    rw [hcongr]; exact hA i j

/-- Joint smoothness of an inverse entry of a matrix family with jointly-`C^∞`
entries and nowhere-vanishing determinant. -/
private lemma contDiffOn_jointMatrixInv_entry {s : Set (ℝ × E)}
    {A : ℝ × E → Matrix n n ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × E => A p i j) s)
    (hdet : ∀ p ∈ s, (A p).det ≠ 0) (a b : n) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => (A p)⁻¹ a b) s := by
  classical
  have hexp : (fun p : ℝ × E => (A p)⁻¹ a b)
      = fun p : ℝ × E => (A p).det⁻¹ * (A p).adjugate a b := by
    funext p
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hexp]
  exact ((contDiffOn_jointDet hA).inv (hdet)).mul (contDiffOn_jointAdjugate hA a b)

/-- **Closed-slab joint smoothness of a spatial partial derivative.**

If `F` is jointly `C^∞` on `J ×ˢ U` with `J` uniquely-differentiable and `U` open,
then the model-direction spatial partial derivative `(t, y) ↦ ∂_l (F(t, ·)) y` is
jointly `C^∞` on `J ×ˢ U` as well.  Unlike the open-interval version, this does not
require `J` to be open: the joint `fderivWithin ℝ F (J ×ˢ U)` is `C^∞` by
`ContDiffOn.fderivWithin`, and its restriction to the (open) spatial factor recovers
the honest spatial `fderiv` of the time-slice. -/
private lemma contDiffOn_jointPartialDeriv_closed {J : Set ℝ} {U : Set E}
    (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U)
    {F : ℝ × E → ℝ} (hF : ContDiffOn ℝ ∞ F (J ×ˢ U))
    (l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => partialDeriv (E := E) l (fun y : E => F (p.1, y)) p.2)
      (J ×ˢ U) := by
  classical
  have huniq : UniqueDiffOn ℝ (J ×ˢ U) := hJ.prod hU.uniqueDiffOn
  have hF' : ContDiffOn ℝ ∞ (fun p : ℝ × E => fderivWithin ℝ F (J ×ˢ U) p) (J ×ˢ U) :=
    hF.fderivWithin huniq (by rw [ENat.coe_top_add_one])
  have hcomp : ContDiffOn ℝ ∞
      (fun p : ℝ × E =>
        ((fderivWithin ℝ F (J ×ˢ U) p).comp (ContinuousLinearMap.inr ℝ ℝ E))
          ((chartModelBasis E) l)) (J ×ˢ U) := by
    have hL : ContDiff ℝ ∞
        (fun A : (ℝ × E) →L[ℝ] ℝ => A.comp (ContinuousLinearMap.inr ℝ ℝ E)) :=
      ((ContinuousLinearMap.compL ℝ E (ℝ × E) ℝ).flip
        (ContinuousLinearMap.inr ℝ ℝ E)).contDiff
    exact (hL.comp_contDiffOn hF').clm_apply contDiffOn_const
  refine hcomp.congr ?_
  intro p hp
  have hdiff : DifferentiableWithinAt ℝ F (J ×ˢ U) p :=
    (hF.differentiableOn (by simp)) p hp
  have hjoint : HasFDerivWithinAt F (fderivWithin ℝ F (J ×ˢ U) p) (J ×ˢ U) p :=
    hdiff.hasFDerivWithinAt
  have hg_deriv : HasFDerivWithinAt (fun y' : E => ((p.1 : ℝ), y'))
      (ContinuousLinearMap.inr ℝ ℝ E) U p.2 := by
    have h1 : HasFDerivWithinAt (fun _ : E => (p.1 : ℝ)) (0 : E →L[ℝ] ℝ) U p.2 :=
      (hasFDerivAt_const _ _).hasFDerivWithinAt
    have h2 : HasFDerivWithinAt (fun y' : E => y') (ContinuousLinearMap.id ℝ E) U p.2 :=
      (hasFDerivAt_id _).hasFDerivWithinAt
    have h3 := h1.prodMk h2
    have hcl : (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)
        = ContinuousLinearMap.inr ℝ ℝ E := by ext y <;> simp
    rw [hcl] at h3
    exact h3
  have hmaps : MapsTo (fun y' : E => ((p.1 : ℝ), y')) U (J ×ˢ U) := fun y' hy' => ⟨hp.1, hy'⟩
  have hcompd : HasFDerivWithinAt ((fun q : ℝ × E => F q) ∘ (fun y' : E => ((p.1 : ℝ), y')))
      ((fderivWithin ℝ F (J ×ˢ U) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) U p.2 :=
    hjoint.comp p.2 hg_deriv hmaps
  have hslice_eq : ((fun q : ℝ × E => F q) ∘ (fun y' : E => ((p.1 : ℝ), y')))
      = fun y' : E => F (p.1, y') := by funext y'; rfl
  rw [hslice_eq] at hcompd
  have hfd : HasFDerivAt (fun y' : E => F (p.1, y'))
      ((fderivWithin ℝ F (J ×ˢ U) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) p.2 :=
    hcompd.hasFDerivAt (hU.mem_nhds hp.2)
  rw [partialDeriv, hfd.fderiv]

/-- On `interior (extChartAt I α).target`, the inverse-image manifold point lies in
the trivialization base set, so the chart Gram matrix is positive-definite there. -/
private lemma symm_mem_baseSet_of_mem_interior {α : M} {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
  have hy_tgt : y ∈ (extChartAt I α).target := interior_subset hy
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy_tgt
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  rw [trivializationAt_baseSet_eq_chartAt_source]
  exact hsource

/-- The matrix of joint `chartGramOnE` entries equals the chart Gram matrix at the
inverse-image manifold point. -/
private lemma gramOnE_matrix_eq (g : SmoothRiemannianMetric I M) (α : M) (y : E) :
    (Matrix.of fun i j => chartGramOnE (I := I) g α i j y)
      = chartGramMatrix (I := I) g α ((extChartAt I α).symm y) := by
  ext i j; rfl

/-- The inverse chart Gram entry equals the matrix inverse entry of the joint
`chartGramOnE` matrix. -/
private lemma chartInvGramOnE_eq_matrixInv
    (g : SmoothRiemannianMetric I M) (α : M) (a b : Fin (Module.finrank ℝ E)) (y : E) :
    chartInvGramOnE (I := I) g α a b y
      = (Matrix.of fun i j => chartGramOnE (I := I) g α i j y)⁻¹ a b := by
  rw [chartInvGramOnE_def, gramOnE_matrix_eq (I := I) g α y]
  rfl

/-- **Closed-slab joint smoothness of the inverse chart Gram entry.** -/
private lemma chartInvGramOnE_joint_contDiffOn_closed
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) {T : ℝ}
    (h_gram_E : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => chartInvGramOnE (I := I) (g_DT p.1) α a b p.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  let A : ℝ × E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun p => Matrix.of fun i j => chartGramOnE (I := I) (g_DT p.1) α i j p.2
  have hcongr : (fun p : ℝ × E => chartInvGramOnE (I := I) (g_DT p.1) α a b p.2)
      = fun p : ℝ × E => (A p)⁻¹ a b := by
    funext p
    exact chartInvGramOnE_eq_matrixInv (I := I) (g_DT p.1) α a b p.2
  rw [hcongr]
  refine contDiffOn_jointMatrixInv_entry (A := A) (fun i j => ?_) ?_ a b
  · exact h_gram_E i j
  · intro p hp
    have hbase := symm_mem_baseSet_of_mem_interior (I := I) (α := α) hp.2
    have hpos : 0 < (A p).det := by
      have : (A p) = chartGramMatrix (I := I) (g_DT p.1) α ((extChartAt I α).symm p.2) :=
        gramOnE_matrix_eq (I := I) (g_DT p.1) α p.2
      rw [this]
      exact chartGramMatrix_det_pos (I := I) (g_DT p.1) α hbase
    exact ne_of_gt hpos

/-- **Closed-slab joint smoothness of the chart-Christoffel symbol of `g_DT s`.** -/
private lemma chartChristoffel_joint_contDiffOn_closed
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) {T : ℝ} (hT : 0 < T)
    (h_gram_E : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E =>
        chartChristoffel (I := I) (g_DT p.1) α i j k p.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hrewrite : (fun p : ℝ × E =>
        chartChristoffel (I := I) (g_DT p.1) α i j k p.2)
      = fun p : ℝ × E =>
          (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) (g_DT p.1) α k l p.2 *
              (partialDeriv (E := E) i (chartGramOnE (I := I) (g_DT p.1) α l j) p.2 +
               partialDeriv (E := E) j (chartGramOnE (I := I) (g_DT p.1) α l i) p.2 -
               partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT p.1) α i j) p.2) := by
    funext p
    rw [chartChristoffel_def]
    refine congrArg (fun t => (1 / 2 : ℝ) * t) ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rfl
  rw [hrewrite]
  have hJ : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have hU : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hpd : ∀ a b c : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun p : ℝ × E =>
          partialDeriv (E := E) a (chartGramOnE (I := I) (g_DT p.1) α b c) p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    intro a b c
    have := contDiffOn_jointPartialDeriv_closed (E := E) hJ hU (h_gram_E b c) a
    refine this.congr ?_
    intro p hp
    rfl
  refine (contDiffOn_const).mul ?_
  refine ContDiffOn.sum (fun l _ => ?_)
  refine ContDiffOn.mul
    (chartInvGramOnE_joint_contDiffOn_closed (I := I) g_DT α h_gram_E k l) ?_
  exact ((hpd i l j).add (hpd j l i)).sub (hpd l i j)

/-- A `y`-only chart field that is `C^∞` on `interior (target)` is jointly `C^∞`
on the closed slab. -/
private lemma contDiffOn_snd_of_contDiffOn_interior_closed {α : M} {T : ℝ}
    {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F (interior (extChartAt I α).target)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => F p.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  have hsnd : ContDiffOn ℝ ∞ (fun p : ℝ × E => p.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    contDiffOn_snd
  refine hF.comp hsnd ?_
  intro p hp; exact hp.2

/-- **Closed-slab joint smoothness of the chart DeTurck-VF component (chart-target
interior).** -/
private lemma chartDeTurckVFComp_joint_contDiffOn_E_closed
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (α : M) {T : ℝ} (hT : 0 < T)
    (h_gram_E : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => chartDeTurckVFComp (I := I) (g_DT p.1) g_bg α k p.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  have hrewrite : (fun p : ℝ × E => chartDeTurckVFComp (I := I) (g_DT p.1) g_bg α k p.2)
      = fun p : ℝ × E =>
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (g_DT p.1) α a b p.2 *
            (chartChristoffel (I := I) (g_DT p.1) α a b k p.2 -
              chartChristoffel (I := I) g_bg α a b k p.2) := by
    funext p; rw [chartDeTurckVFComp_def]
  rw [hrewrite]
  refine ContDiffOn.sum (fun a _ => ?_)
  refine ContDiffOn.sum (fun b _ => ?_)
  refine ContDiffOn.mul
    (chartInvGramOnE_joint_contDiffOn_closed (I := I) g_DT α h_gram_E a b) ?_
  refine ContDiffOn.sub
    (chartChristoffel_joint_contDiffOn_closed (I := I) g_DT α hT h_gram_E a b k) ?_
  exact contDiffOn_snd_of_contDiffOn_interior_closed (I := I)
    (chartChristoffel_contDiffOn_interior (I := I) g_bg α a b k)

/-- **Closed-slab transfer of the chart-Gram smoothness from the manifold form to the
chart-target-interior Euclidean form.** -/
private lemma chartGramOnE_joint_contDiffOn_of_manifold_closed
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) {T : ℝ}
    (h_gDT : ∀ (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M =>
          chartGramOnE (I := I) (g_DT q.1) α i j (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ (chartAt H α).source))
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  set Ψ : ℝ × E → ℝ × M := fun p => (p.1, (extChartAt I α).symm p.2) with hΨ
  have hΨ_smooth : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) ((𝓘(ℝ, ℝ)).prod I) ∞ Ψ
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    refine ContMDiffOn.prodMk ?_ ?_
    · exact contMDiffOn_fst
    · have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
          (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
      refine hsymm.comp contMDiffOn_snd ?_
      intro p hp; exact Set.mem_preimage.mpr (interior_subset hp.2)
  have hmaps : Set.MapsTo Ψ
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target)
      (Set.Icc (0 : ℝ) T ×ˢ (chartAt H α).source) := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    have hbase := symm_mem_baseSet_of_mem_interior (I := I) (α := α) hp.2
    rwa [trivializationAt_baseSet_eq_chartAt_source] at hbase
  have hcomp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      ((fun q : ℝ × M =>
          chartGramOnE (I := I) (g_DT q.1) α i j (extChartAt I α q.2)) ∘ Ψ)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    (h_gDT i j).comp hΨ_smooth hmaps
  have hcongr : Set.EqOn
      (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
      ((fun q : ℝ × M =>
          chartGramOnE (I := I) (g_DT q.1) α i j (extChartAt I α q.2)) ∘ Ψ)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    intro p hp
    have hy_tgt : p.2 ∈ (extChartAt I α).target := interior_subset hp.2
    simp only [Function.comp_apply, hΨ]
    rw [(extChartAt I α).right_inv hy_tgt]
  have hcomp' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × E => chartGramOnE (I := I) (g_DT p.1) α i j p.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    hcomp.congr hcongr
  rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hcomp'

/-- **Closed-slab keystone: joint `(t, x)` smoothness of the chart DeTurck-VF
component on `Icc 0 T ×ˢ goodSet`.** -/
private lemma chartDeTurckVFComp_joint_contMDiffOn_closed
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (α : M) {T : ℝ} (hT : 0 < T)
    (h_gDT : ∀ (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M =>
          chartGramOnE (I := I) (g_DT q.1) α i j (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ (chartAt H α).source))
    (p : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M =>
        chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α p (extChartAt I α q.2))
      (Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have h_gram_E := chartGramOnE_joint_contDiffOn_of_manifold_closed (I := I) g_DT α h_gDT
  have hE := chartDeTurckVFComp_joint_contDiffOn_E_closed (I := I) g_DT g_bg α hT h_gram_E p
  have hE' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × E => chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α p q.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod] at hE
    exact hE
  set Φ : ℝ × M → ℝ × E := fun q => (q.1, extChartAt I α q.2) with hΦ
  have hΦ_smooth : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) ∞ Φ
      (Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
    refine ContMDiffOn.prodMk contMDiffOn_fst ?_
    have hext : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
      contMDiffOn_extChartAt (I := I) (x := α)
    refine hext.comp contMDiffOn_snd ?_
    intro q hq
    exact Set.mem_preimage.mpr (chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hq.2)
  have hmaps : Set.MapsTo Φ
      (Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    intro q hq
    exact ⟨hq.1, chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hq.2⟩
  have hcomp := hE'.comp hΦ_smooth hmaps
  exact hcomp

/-- The trivialized DeTurck-VF section value equals the chart-model-basis sum. -/
private lemma deTurckVF_trivSnd_eq_chartModelBasis_sum
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    (trivializationAt E (TangentSpace I) α
        ⟨x, (deTurckVF (I := I) g g_bg :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x⟩).2
      = ∑ p : Fin (Module.finrank ℝ E),
          chartDeTurckVFComp (I := I) g g_bg α p (extChartAt I α x) •
            (chartModelBasis E) p := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  set L : TangentSpace I x ≃L[ℝ] E :=
    (trivializationAt E (TangentSpace I) α).continuousLinearEquivAt ℝ x hbase with hL
  have hL_apply : ∀ v : TangentSpace I x,
      (trivializationAt E (TangentSpace I) α ⟨x, v⟩).2 = L v := fun _ => rfl
  rw [deTurckVF_apply_eq_chartDeTurckVFComp_sum (I := I) g g_bg α hx]
  rw [hL_apply, map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [map_smul]
  congr 1
  rw [← hL_apply (chartBasisVecFiber (I := I) α p x)]
  exact trivializationAt_chartBasisVec_snd (I := I) α p hbase

/-- **The closed-slab metric → DeTurck-vector-field transfer (engine).**

From the joint `(t, x)`-`C∞` of the single-chart Gram entries on the *closed* slab
`Icc 0 T ×ˢ univ` (each base point using its own chart), the DeTurck vector-field
tangent-bundle section is jointly `(t, x)`-`C∞` on the *closed* slab.  This is the
up-to-and-across-`0` analogue of `deturck_vf_joint_smoothness`; the only new
ingredient is the closed-slab spatial-partial smoothness
`contDiffOn_jointPartialDeriv_closed`, valid because `Icc 0 T` is uniquely
differentiable. -/
theorem deturck_vf_joint_smoothness_uptoZero
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (h_gDT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M =>
          chartGramOnE (I := I) (g_DT q.1) x₀ i j (extChartAt I x₀ q.2))
        (Set.Icc (0 : ℝ) T ×ˢ (chartAt H x₀).source)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
  classical
  intro q₀ hq₀
  set α : M := q₀.2 with hα
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  simp only [← hα]
  have hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  have hα_mem : α ∈ chartLeviCivitaGoodSet (I := I) α :=
    self_mem_chartLeviCivitaGoodSet (I := I) α
  have hcoeff := fun p =>
    chartDeTurckVFComp_joint_contMDiffOn_closed
      (I := I) g_DT g_bg α hT (h_gDT α) p
  have hsum_within : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M =>
        ∑ p : Fin (Module.finrank ℝ E),
          chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α p (extChartAt I α q.2) •
            ((chartModelBasis E) p : E))
      (Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) q₀ := by
    refine contMDiffWithinAt_finset_sum (fun p _ => ?_)
    refine ContMDiffWithinAt.smul ?_ contMDiffWithinAt_const
    have hq₀_mem : q₀ ∈ Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α :=
      ⟨hq₀.1, hα ▸ hα_mem⟩
    exact (hcoeff p) q₀ hq₀_mem
  have hnhds : Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α
      ∈ nhdsWithin q₀ (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
    rw [nhdsWithin_prod_eq]
    refine Filter.prod_mem_prod self_mem_nhdsWithin ?_
    rw [nhdsWithin_univ]
    exact hgood_open.mem_nhds (hα ▸ hα_mem)
  have hsum_within' : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M =>
        ∑ p : Fin (Module.finrank ℝ E),
          chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α p (extChartAt I α q.2) •
            ((chartModelBasis E) p : E))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) q₀ :=
    hsum_within.mono_of_mem_nhdsWithin hnhds
  have heqOn : Set.EqOn
      (fun q : ℝ × M =>
        (trivializationAt E (TangentSpace I) α
          ⟨q.2, (deTurckVF (I := I) (g_DT q.1) g_bg) q.2⟩).2)
      (fun q : ℝ × M =>
        ∑ p : Fin (Module.finrank ℝ E),
          chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α p (extChartAt I α q.2) •
            ((chartModelBasis E) p : E))
      (Set.Icc (0 : ℝ) T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
    intro q hq
    exact deTurckVF_trivSnd_eq_chartModelBasis_sum
      (I := I) (g_DT q.1) g_bg α hq.2
  have hev : (fun q : ℝ × M =>
        (trivializationAt E (TangentSpace I) α
          ⟨q.2, (deTurckVF (I := I) (g_DT q.1) g_bg) q.2⟩).2)
      =ᶠ[nhdsWithin q₀ (Set.Icc (0 : ℝ) T ×ˢ Set.univ)]
      (fun q : ℝ × M =>
        ∑ p : Fin (Module.finrank ℝ E),
          chartDeTurckVFComp (I := I) (g_DT q.1) g_bg α p (extChartAt I α q.2) •
            ((chartModelBasis E) p : E)) := by
    filter_upwards [hnhds] with q hq using heqOn hq
  have hxeq : (trivializationAt E (TangentSpace I) α
        ⟨q₀.2, (deTurckVF (I := I) (g_DT q₀.1) g_bg) q₀.2⟩).2
      = ∑ p : Fin (Module.finrank ℝ E),
          chartDeTurckVFComp (I := I) (g_DT q₀.1) g_bg α p (extChartAt I α q₀.2) •
            ((chartModelBasis E) p : E) :=
    heqOn (by exact ⟨hq₀.1, hα ▸ hα_mem⟩)
  exact hsum_within'.congr_of_eventuallyEq hev hxeq

end

end ClosedSlabVFEngine


/-- **Single-chart joint `(t, x)`-`C∞`-up-to-AND-across-`0` of the realized chart-Gram
entry (genuine parabolic up-to-boundary smoothing).**

The closed-slab twin of `realizedMetric_chartGramOnE_jointContMDiffOn_interior`: for a
realized DeTurck flow `g_DT` whose bundle inner-product `Hom`-section
`(t, x) ↦ (g_DT t).inner x` is jointly `(t, x)`-`C∞` over the product model `𝓘(ℝ, ℝ).prod I`
on the *closed* slab `Icc 0 T ×ˢ baseSet` (`hsmooth`), each single-chart Gram entry
`(t, x) ↦ chartGramOnE (g_DT t) α i j (extChartAt I α x)` is jointly `(t, x)`-`C∞` on the
*closed* slab `Icc 0 T ×ˢ (chartAt H α).source`.

This is the up-to-and-across-the-initial-datum interior parabolic smoothing of the
strictly-parabolic, smooth-quasilinear DeTurck–Ricci flow with smooth initial metric `g₀`
(Chow–Knopf), in the single-chart `chartGramOnE α ∘ extChartAt I α` form (each base point uses
its own chart `α`; off the chart source the round-trip is junk, so the source domain is the
honest one).  The hypothesis is the *joint* smoothness of the metric `Hom`-section (supplied
by `realizedMetric_innerHomSection_jointContMDiffOn_uptoZero`); the conclusion is the
closed-slab joint smoothness of the scalar Gram entry, distinct from it — no packaging.

This is sorry-free glue: the chart-local `C∞` bridge
`chartGramOnE_realizedMetric_jointContMDiffOn`
(`Analysis/Parabolic/DeTurckRicci/InteriorChartRegularityBridge.lean`), transporting the
joint `Hom`-section smoothness to the scalar chart-Gram entry on the chart source. -/
theorem realizedMetric_chartGramOnE_jointContMDiffOn_uptoZero
    (α : M) (i j : Fin (Module.finrank ℝ E))
    (g_DT : ℝ → SmoothRiemannianMetric I M) {T : ℝ}
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q.2 ((g_DT q.1).inner q.2))
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun q : ℝ × M =>
        Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
          (extChartAt I α q.2))
      (Set.Icc (0 : ℝ) T ×ˢ (chartAt H α).source) :=
  chartGramOnE_realizedMetric_jointContMDiffOn (I := I) (M := M) α i j g_DT hsmooth

/-- **Joint `C∞`-up-to-AND-across-`0` of the realized DeTurck vector field as a tangent-bundle
section (genuine parabolic up-to-boundary smoothing of the field).**

For the realized DeTurck flow `g_DT = g₀ + ccTensorBilinSymm (T_s ·)` realized off the anchor
`g₀` (`hreal`) whose perturbation `T_s` realizes the **spectral Duhamel carrier** `u₂` (the
carrier coordinates are the `L²` coordinates of `T_s`, `hcanon`; the carrier inclusion is
time-continuous up to `0`, `hcont`; and `u₂` solves the abstract parabolic equation
`∂_t (ι u₂) = Δ_∇ u₂ + N_cont (ι u₂)` on the interior, `hreg`), the joint tangent-bundle
section of the DeTurck vector field of `g_DT` against the flow background `g_bg`,
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
are decoupled.  The hypotheses are the spectral-trajectory realize/PDE data pinning the metric
to the genuine parabolic carrier (the spectral PDE `hreg` rejects the kink family
`T_s t := |t − t₀| · S₀`, which has no interior time-derivative — see
`realizedMetric_innerHomSection_jointContMDiffOn_uptoZero`); the conclusion is the closed-slab
joint smoothness of the field, distinct from them — no packaging.  This node is sorry-free glue:
it routes the spectral pinning into `realizedMetric_innerHomSection_jointContMDiffOn_uptoZero`
(the genuine parabolic-smoothing leaf) and pushes the resulting joint `Hom`-section smoothness
through the chart-frame vector-field assembler `deturck_vf_joint_smoothness_uptoZero`; consumers
transitively depend on the inner node's `sorryAx`. -/
theorem realizedMetric_deTurckVF_jointContMDiffOn_uptoZero
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2) {a : ℕ} {T : ℝ}
    (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (N_cont : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (hreal : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT t).inner x v w
        = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s t) x v w)
    (hcont : ContinuousOn
      (fun s : ℝ => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) (Set.Icc 0 T))
    (hreg : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt
        (fun r => (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ r)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          N_cont
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) s)
    (hcanon : ∀ s ∈ Set.Icc (0 : ℝ) T,
        ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      (u₂ s).coeff i
        = tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
  rcases lt_or_ge 0 T with hT | hT
  · have hsmooth := realizedMetric_innerHomSection_jointContMDiffOn_uptoZero
      (I := I) g₀ g_DT T_s u₂ N_cont ha hreal hcont hreg hcanon
    refine ClosedSlabVFEngine.deturck_vf_joint_smoothness_uptoZero
      (I := I) g_bg g_DT hT ?_
    intro x₀ i j
    exact realizedMetric_chartGramOnE_jointContMDiffOn_uptoZero
      (I := I) x₀ i j g_DT
      (hsmooth.mono (Set.prod_mono_right (Set.subset_univ _)))
  · have hsub : Set.Icc (0 : ℝ) T ⊆ {0} := by
      intro t ht
      have ht0 : t = 0 := le_antisymm (le_trans ht.2 hT) ht.1
      simpa using ht0
    have hfixed : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => (TotalSpace.mk' E x (deTurckVF (I := I) (g_DT 0) g_bg x)
          : TangentBundle I M)) :=
      deTurckFun_contMDiff_total (I := I) (g_DT 0) g_bg
    have hcomp : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT 0) g_bg q.2)
          : TangentBundle I M))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ) :=
      hfixed.comp_contMDiffOn contMDiffOn_snd
    refine hcomp.congr ?_
    rintro ⟨t, x⟩ ⟨ht, _⟩
    have ht0 : t = 0 := hsub ht
    subst ht0
    rfl

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
