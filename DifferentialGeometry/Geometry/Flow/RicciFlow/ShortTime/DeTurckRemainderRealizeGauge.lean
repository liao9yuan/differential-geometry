import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRicciRHSSymmetric
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedGramDiff
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckG0RealizeSectionLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.WeylEigenvalueCountingBound

/-! # The decoupled (`g₀`-anchored, `g_bg`-background) Ricci–DeTurck remainder gauge

This file constructs the *concrete* `g₀`-anchored, `g_bg`-background Ricci–DeTurck
gauge section consumed by the open frontier node
`deTurck_g0_decoupled_principal_match` (`DeTurckG0RealizeFrontier.lean`), and isolates
the single genuinely-open *decoupled* principal-part / Lipschitz datum about it.

For the anchor metric `g₀` and a flow background `g_bg`, the gauge

  `deTurckRemainderRealizeSection g₀ g_bg u
     := deTurckRHSSection g_bg (g₀ + ccTensorBilinSymm g₀ (gateSmoothRep u))
          −  Δ_∇^{g₀} (gateSmoothRep u)`

(re-tagged from the `g_bg` type tag to the `g₀` type tag, since the metric tag is a
pure type-level parameter — see `SmoothCcTensor` and `deTurckRHSSectionBg`) is the
decoupled analogue of `deTurckRemainderSection`: the `g₀`-realized metric
`g₀ + ccTensorBilinSymm g₀ (gateSmoothRep u)` drives the *background* `g_bg`
Ricci–DeTurck right-hand side, minus the `g₀`-rough-Laplacian of the realized
perturbation `gateSmoothRep u`.

## The gate-based realization (handling infinite spectral support)

The smooth representative `gateSmoothRep u` is produced by the **unconditional spectral
smooth-representative gate** `spectralSmoothRealizesAsSmooth_of_eigenvalueTailSummable`
(`SpectralChartRegularityAnyOrder.lean`), whose Weyl-type spectral input
`EigenvalueTailSummable` is supplied from the local Weyl counting bound
`weyl_eigenvalue_counting_bound_of_closed` through
`eigenvalueTailSummable_of_countingBound`.  Every `L²` tensor lying in *every* `Hˢ`
(`MemAllTensorHs`) thus admits a genuine `SmoothCcTensor` representative — in particular
the maximal-regularity Duhamel carrier, which is generically *infinitely supported*.
This replaces the earlier finite-support gate `realizableAt` (which is false for the
engine carrier, as it demands `(Function.support u.coeff).Finite`): the validity domain
is now `realizableAtGate`, requiring `MemAllTensorHs` of `u`'s `L²` class plus the same
`g₀`-fibre-smallness `< 1` that makes `g₀ + ccTensorBilinSymm g₀ (gateSmoothRep u)` an
honest positive-definite smooth metric.  Off that domain the gauge is the zero section.

The single open datum about the concrete gate-based gauge is
`deTurckRemainderRealize_geomMatch_lipschitz`:

* the *decoupled* principal-part match (`hNsec_geom`) — for every realize family
  `g_DT`/`u₂`/`T_s` with the realize identity, the smooth-coordinate identity, the
  canonical-smooth-representative `L²` identity, **and the honest `realizableAtGate`
  membership of the carrier inclusion**, the `g₀`-rough-Laplacian of the carrier `T_s s`
  plus the `g₀`-`ccTensorBilinSymm` of the gauge of the carrier equals
  `deTurckRicciRHS g_bg (g_DT s)`.  This is the integrated decoupled analogue of the
  symbol-level cancellation `deTurckNonlinearitySpectral_principalPart_cancels`, reconciled
  with `deTurckRicciRHS g_bg (g_DT s)` through the sorry-free bridge
  `deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS` (the carrier `T_s s` is the
  canonical smooth representative of the realized perturbation).
* the concrete-gauge `Hᵃ`-Lipschitz certificate (`hNsec_lip`) — the gauge's
  `deTurckG0SectionDiffHa`-difference is Lipschitz in the realize input, via the
  chart-coordinate DeTurck-RHS Lipschitz tower and the resolvent/eigenbasis Parseval
  identity (`tensorHs.norm_sq_eq_tsum`).

Both are genuine, well-posed, non-vacuous statements about the realized concrete gauge;
neither packages the existential of `deTurck_g0_decoupled_principal_match`, and the
principal-part premises (`hreal`/`hsmoothrepr`/`hcanon`/`hgate`) are honest data, not the
conclusion.  The body is `sorry`, so consumers transitively depend on `sorryAx`. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **`L²`-image determinacy of a smooth compactly-supported tensor section.**
The canonical embedding `SmoothCcTensor.toL2` is injective: a smooth, compactly
supported `(r, s)`-tensor section whose `L²`-class vanishes is the zero section
(the `L²` seminorm separates *continuous* sections, the integrand being a
continuous nonnegative function whose integral against the full-support
Riemannian volume vanishes only when it vanishes identically).  Posited child. -/
theorem smoothCcTensor_toL2_injective (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Function.Injective (Integral.L2.SmoothCcTensor.toL2 (g := g) (r := r) (s := s)) :=
  sorry

/-- **Metric extensionality from the fibrewise inner product.**
Two smooth Riemannian metrics with the same fibrewise inner product on every
fibre are equal: the `inner` fields agree by fibrewise continuous-bilinear
extensionality, and the remaining structure fields (symmetry, positivity,
von-Neumann boundedness, smoothness) are propositions, hence equal by proof
irrelevance. -/
theorem smoothRiemannianMetric_eq_of_inner
    (g g' : SmoothRiemannianMetric I M)
    (h : ∀ (x : M) (v w : TangentSpace I x), g.inner x v w = g'.inner x v w) :
    g = g' := by
  have hinner : g.inner = g'.inner := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    exact h x v w
  cases g
  cases g'
  congr

/-- **The spectral smooth-representative gate for rank-`(0,2)` tensors on `(M, g₀)`.**
The unconditional gate `SpectralSmoothRealizesAsSmooth g₀ 0 2`, whose Weyl-type
spectral input is supplied from the local Weyl counting bound
`weyl_eigenvalue_counting_bound_of_closed` through
`eigenvalueTailSummable_of_countingBound`: every `L²` tensor lying in every `Hˢ`
admits a genuine `C^∞` representative.  (Transits the single Weyl node.) -/
theorem deTurckRealizeGate (g₀ : SmoothRiemannianMetric I M) :
    SpectralSmoothRealizesAsSmooth (I := I) (M := M) g₀ 0 2 :=
  spectralSmoothRealizesAsSmooth_of_eigenvalueTailSummable (I := I) (M := M) g₀ 0 2
    (eigenvalueTailSummable_of_countingBound (I := I) (M := M) g₀ 0 2
      (weyl_eigenvalue_counting_bound_of_closed (I := I) (M := M) g₀ 0 2))

/-- **Every smooth compactly-supported tensor lies in every spectral Sobolev space.**
For a `SmoothCcTensor T`, its `L²` class `SmoothCcTensor.toL2 T` lies in
`tensorHs g₀ 0 2 σ` (via the chart-locality-free realization) for *every* exponent
`σ ≥ 0`: the spectral element synthesized from the eigenbasis coordinates
`tensorL2Coeff (toL2 T)` is weighted-square-summable at every order
(`smoothCcTensor_tensorL2Coeff_weighted_summable`), and its `tensorHsToL2` realization
recovers `toL2 T` (same eigenbasis coordinates).  This is exactly the gate antecedent
`MemAllTensorHs`. -/
theorem smoothCcTensor_memAllTensorHs (g₀ : SmoothRiemannianMetric I M)
    (T : Integral.L2.SmoothCcTensor g₀ 0 2) :
    MemAllTensorHs (I := I) (M := M) g₀ 0 2 (Integral.L2.SmoothCcTensor.toL2 T) := by
  classical
  intro σ hσ
  refine ⟨Analysis.Parabolic.MaximalRegularity.timeModeSynthesisPointwise
      (g := g₀) (r := 0) (s := 2) (b := σ)
      (fun i => tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (Integral.L2.SmoothCcTensor.toL2 T) i)
      (smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M)
        g₀ σ T (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)), ?_⟩
  set v := Analysis.Parabolic.MaximalRegularity.timeModeSynthesisPointwise
      (g := g₀) (r := 0) (s := 2) (b := σ)
      (fun i => tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (Integral.L2.SmoothCcTensor.toL2 T) i)
      (smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M)
        g₀ σ T (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)) with hv_def
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) with hb_def
  apply b.repr.injective
  ext i
  have hlhs : (b.repr (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) hσ v)) i =
      v.coeff i := by
    rw [show (b.repr (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) hσ v)) i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) hσ v) i from rfl,
      tensorHsToL2_tensorL2Coeff (I := I) (M := M) hσ v i]
  have hrhs : (b.repr (Integral.L2.SmoothCcTensor.toL2 T)) i = v.coeff i := by
    rw [show (b.repr (Integral.L2.SmoothCcTensor.toL2 T)) i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (Integral.L2.SmoothCcTensor.toL2 T) i from rfl, hv_def,
      Analysis.Parabolic.MaximalRegularity.timeModeSynthesisPointwise_coeff]
  rw [hlhs, hrhs]

/-- **The gate-produced `C^∞` representative of a gate element.**
For `u : tensorHs g₀ 0 2 σ` (`σ ≥ 0`) whose `L²` class `tensorHsToL2 u` lies in every
`Hˢ` (`h_mem`), `gateSmoothRep g₀ u hσ h_mem` is the smooth compactly-supported
`(0,2)`-tensor representative produced by the spectral gate `deTurckRealizeGate`.  Its
`L²` class equals `tensorHsToL2 u` (`gateSmoothRep_toL2`). -/
noncomputable def gateSmoothRep (g₀ : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : tensorHs (I := I) (M := M) g₀ 0 2 σ) (hσ : 0 ≤ σ)
    (h_mem : MemAllTensorHs (I := I) (M := M) g₀ 0 2
      (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) hσ u)) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  Classical.choose (deTurckRealizeGate (I := I) (M := M) g₀
    (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) hσ u) h_mem)

/-- The defining spec of `gateSmoothRep`: its `L²` class is `tensorHsToL2 u`. -/
theorem gateSmoothRep_toL2 (g₀ : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : tensorHs (I := I) (M := M) g₀ 0 2 σ) (hσ : 0 ≤ σ)
    (h_mem : MemAllTensorHs (I := I) (M := M) g₀ 0 2
      (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) hσ u)) :
    Integral.L2.SmoothCcTensor.toL2 (gateSmoothRep (I := I) g₀ u hσ h_mem) =
      tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) hσ u :=
  Classical.choose_spec (deTurckRealizeGate (I := I) (M := M) g₀
    (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) hσ u) h_mem)

/-- **The gate validity-domain predicate.**  `u : tensorHs g₀ 0 2 σ` is *gate
realizable* when `σ ≥ 0`, its `L²` class lies in every `Hˢ` (`MemAllTensorHs`, so the
spectral gate yields a `C^∞` representative `gateSmoothRep u` for the — generically
infinite — spectral support), and the extracted symmetric form of that representative is
`g₀`-fibre small with some constant `< 1` (so `g₀ + ccTensorBilinSymm g₀ (gateSmoothRep u)`
is an honest positive-definite smooth metric).  This is the gate analogue of
`realizableAt`, with the false finite-support requirement replaced by `MemAllTensorHs`. -/
def realizableAtGate (g₀ : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : tensorHs (I := I) (M := M) g₀ 0 2 σ) : Prop :=
  ∃ (hσ : 0 ≤ σ) (h_mem : MemAllTensorHs (I := I) (M := M) g₀ 0 2
        (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) hσ u))
      (δ' : ℝ), δ' < 1 ∧
    gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (gateSmoothRep (I := I) g₀ u hσ h_mem)) δ'

/-- **The maximal-regularity carrier inclusion is gate realizable.**
For the realized `g₀`-anchored flow at a fixed interior time `s`, the carrier inclusion
`ι (u₂ s) : tensorHs g₀ 0 2 (a+1)` is `realizableAtGate`, given:

* `hsmoothrepr` — the carrier coordinates are the `L²` coordinates of its smooth
  representative `T_s s` (so `ι (u₂ s)`'s `L²` class equals `T_s s`'s `L²` class, hence
  lies in every `Hˢ` by `smoothCcTensor_memAllTensorHs` — discharging the `MemAllTensorHs`
  half of the gate);
* `hfibre` — the realized perturbation `ccTensorBilinSymm g₀ (T_s s)` is `g₀`-fibre small
  with some constant `< 1` (discharging the metric-positivity half: the gate
  representative `gateSmoothRep (ι (u₂ s)) = T_s s` by `L²`-injectivity, so its extracted
  form is `g₀`-fibre small).

This packages the gate-internals of the discharge consumed by the assembler. -/
theorem realizableAtGate_carrierInclusion (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2) {s : ℝ}
    (hsmoothrepr : ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        (u₂ s).coeff i
          = tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i)
    (hfibre : ∃ δ' : ℝ, δ' < 1 ∧
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (T_s s)) δ') :
    realizableAtGate (I := I) g₀
      (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) := by
  classical
  set hcompact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) :=
    tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s) with hu_def
  have hσ : (0 : ℝ) ≤ (a : ℝ) + 1 := by positivity
  -- The inclusion's `L²` class coincides with the smooth representative's `L²` class.
  have hclass :
      tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hcompact hσ u
        = Integral.L2.SmoothCcTensor.toL2 (T_s s) := by
    set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hcompact with hb
    apply b.repr.injective
    ext i
    have hlhs :
        (b.repr (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            hcompact hσ u)) i = (u₂ s).coeff i := by
      rw [show (b.repr (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            hcompact hσ u)) i =
          tensorL2Coeff (I := I) (M := M) hcompact
            (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              hcompact hσ u) i from rfl,
        tensorHsToL2_tensorL2Coeff (I := I) (M := M) hσ u i, hu_def,
        tensorHsInclusion_coeff_apply]
    have hrhs :
        (b.repr (Integral.L2.SmoothCcTensor.toL2 (T_s s))) i = (u₂ s).coeff i := by
      rw [show (b.repr (Integral.L2.SmoothCcTensor.toL2 (T_s s))) i =
          tensorL2Coeff (I := I) (M := M) hcompact
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i from rfl]
      exact (hsmoothrepr i).symm
    rw [hlhs, hrhs]
  have h_mem : MemAllTensorHs (I := I) (M := M) g₀ 0 2
      (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hcompact hσ u) := by
    rw [hclass]; exact smoothCcTensor_memAllTensorHs (I := I) g₀ (T_s s)
  -- The gate representative coincides with `T_s s`, so its fibre-smallness is `hfibre`.
  have hgate_eq : gateSmoothRep (I := I) g₀ u hσ h_mem = T_s s := by
    apply smoothCcTensor_toL2_injective (I := I) (M := M) g₀ 0 2
    rw [gateSmoothRep_toL2 (I := I) g₀ u hσ h_mem, hclass]
  obtain ⟨δ', hδ'_lt, hδ'⟩ := hfibre
  exact ⟨hσ, h_mem, δ', hδ'_lt, by rw [hgate_eq]; exact hδ'⟩

open scoped Classical in
/-- **The decoupled (`g₀`-anchored, `g_bg`-background) Ricci–DeTurck remainder gauge
as a smooth compactly-supported `(0,2)`-tensor section.**

On the gate validity domain `realizableAtGate`, with the gate-produced smooth
representative `gateSmoothRep u` and `g₀`-realized metric
`g₀ + ccTensorBilinSymm g₀ (gateSmoothRep u)` (assembled via `tensorSectionRealizeMetric`
from the fibre-smallness in the gate), this is

  `deTurckRHSSection g_bg (g₀ + ccTensorBilinSymm g₀ (gateSmoothRep u))
     − rawTensorConnLapSmooth g₀ 0 2 (gateSmoothRep u)`

(re-tagged from the `g_bg` type tag to the `g₀` type tag, the metric tag being a pure
type-level parameter).  Off the validity domain it is the zero section.

This is the gate-based decoupled analogue of `deTurckRemainderSection`, the concrete
gauge `repr = Nsec` returned by `deTurck_g0_decoupled_principal_match`. -/
noncomputable def deTurckRemainderRealizeSection (g₀ g_bg : SmoothRiemannianMetric I M)
    {σ : ℝ} (u : tensorHs (I := I) (M := M) g₀ 0 2 σ) :
    SmoothCcTensor g₀ 0 2 :=
  if h : realizableAtGate (I := I) g₀ u then
    { toSection :=
        (deTurckRHSSection (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀
            (gateSmoothRep (I := I) g₀ u h.choose h.choose_spec.choose)
            h.choose_spec.choose_spec.choose_spec.1
            h.choose_spec.choose_spec.choose_spec.2)).toSection
      hasCompactSupport :=
        (deTurckRHSSection (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀
            (gateSmoothRep (I := I) g₀ u h.choose h.choose_spec.choose)
            h.choose_spec.choose_spec.choose_spec.1
            h.choose_spec.choose_spec.choose_spec.2)).hasCompactSupport }
      - rawTensorConnLapSmooth (I := I) g₀ 0 2
          (gateSmoothRep (I := I) g₀ u h.choose h.choose_spec.choose)
  else
    0

/-- The extracted symmetric bilinear form `ccTensorBilinSymm` depends only on the
underlying smooth section (the metric tag is a pure type-level phantom): two
smooth `(0,2)`-tensor sections `S`, `S'` with the same underlying section data
have the same `ccTensorBilinSymm`. -/
private theorem ccTensorBilinSymm_eq_of_toSection_eq
    {g g' : SmoothRiemannianMetric I M}
    {S : SmoothCcTensor g 0 2} {S' : SmoothCcTensor g' 0 2}
    (hSS : S.toSection = S'.toSection) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g S x v w = ccTensorBilinSymm (I := I) g' S' x v w := by
  rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply, ccTensorBilin_apply,
    ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply]
  unfold ccTensorModel ccTensorMultilinear
  rw [hSS]

/-- In the gate-realizable branch, the extracted symmetric form of the concrete gauge
splits as `deTurckRicciRHS g_bg (g₀ + ccTensorBilinSymm g₀ (gateSmoothRep u))` minus the
`g₀`-rough Laplacian of the gate representative — the `deTurckRHS` summand transported to
the `g_bg` tag and reconciled through the sorry-free bridge
`deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS`. -/
private theorem gauge_realizableGate_ccTensorBilinSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u : tensorHs (I := I) (M := M) g₀ 0 2 σ}
    (h : realizableAtGate (I := I) g₀ u) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₀ (deTurckRemainderRealizeSection (I := I) g₀ g_bg u)
        x v w
      = deTurckRicciRHS (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀
            (gateSmoothRep (I := I) g₀ u h.choose h.choose_spec.choose)
            h.choose_spec.choose_spec.choose_spec.1
            h.choose_spec.choose_spec.choose_spec.2) x v w
        - ccTensorBilinSymm (I := I) g₀
            (rawTensorConnLapSmooth (I := I) g₀ 0 2
              (gateSmoothRep (I := I) g₀ u h.choose h.choose_spec.choose))
            x v w := by
  rw [deTurckRemainderRealizeSection, dif_pos h, ccTensorBilinSymm_sub]
  congr 1
  rw [show ccTensorBilinSymm (I := I) g₀
          ((⟨(deTurckRHSSection (I := I) g_bg
                (tensorSectionRealizeMetric (I := I) g₀
                  (gateSmoothRep (I := I) g₀ u h.choose h.choose_spec.choose)
                  h.choose_spec.choose_spec.choose_spec.1
                  h.choose_spec.choose_spec.choose_spec.2)).toSection,
              (deTurckRHSSection (I := I) g_bg
                (tensorSectionRealizeMetric (I := I) g₀
                  (gateSmoothRep (I := I) g₀ u h.choose h.choose_spec.choose)
                  h.choose_spec.choose_spec.choose_spec.1
                  h.choose_spec.choose_spec.choose_spec.2)).hasCompactSupport⟩ :
            SmoothCcTensor g₀ 0 2)) x v w
        = ccTensorBilinSymm (I := I) g_bg
            (deTurckRHSSectionBg (I := I) g_bg
              (tensorSectionRealizeMetric (I := I) g₀
                (gateSmoothRep (I := I) g₀ u h.choose h.choose_spec.choose)
                h.choose_spec.choose_spec.choose_spec.1
                h.choose_spec.choose_spec.choose_spec.2)) x v w from
      ccTensorBilinSymm_eq_of_toSection_eq rfl x v w,
    deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS]

/-- **`Hᵃ`-Lipschitz certificate of the concrete `g₀`-anchored gate-based gauge.**
The `deTurckG0SectionDiffHa`-difference of the concrete gauge
`deTurckRemainderRealizeSection g₀ g_bg` is `Hᵃ`-Lipschitz in the `Hᵃ⁺¹` realize
input (chart-coordinate DeTurck-RHS Lipschitz tower transported across the
resolvent/eigenbasis Parseval identity `tensorHs.norm_sq_eq_tsum`).  Posited
child. -/
theorem deTurckRemainderRealize_gauge_ha_lipschitz
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ K : ℝ≥0, ∀ u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1),
        ‖deTurckG0SectionDiffHa (I := I) (M := M) g₀ a
            (deTurckRemainderRealizeSection (I := I) g₀ g_bg) u u'‖
          ≤ (K : ℝ) * dist u u' :=
  sorry

/-- **The decoupled principal-part match and `Hᵃ`-Lipschitz certificate of the
concrete `g₀`-anchored, `g_bg`-background gate-based Ricci–DeTurck remainder gauge (open
analytic datum).**

For the concrete gate-based gauge `deTurckRemainderRealizeSection g₀ g_bg`:

* (`hNsec_lip`) the gauge's `deTurckG0SectionDiffHa`-difference is `Hᵃ`-Lipschitz in the
  realize input (posited child `deTurckRemainderRealize_gauge_ha_lipschitz`);
* (`hNsec_geom`) for every realize family `g_DT`/`u₂`/`T_s` whose realized metric is the
  linear realize `g_DT s = g₀ + ccTensorBilinSymm g₀ (T_s s)` (`hreal`), whose carrier
  coordinates are the `L²` coordinates of `T_s s` (`hsmoothrepr`), whose `T_s s` is the
  canonical smooth representative of the carrier — its `L²` class is the
  `tensorHsToL2`-realization of `u₂ s` (`hcanon`) — **and whose carrier inclusion
  `ι (u₂ s)` is `realizableAtGate` (`hgate`: lies in every `Hˢ` and is `g₀`-fibre small)**,
  the `g₀`-rough-Laplacian of `T_s s` plus the `g₀`-`ccTensorBilinSymm` of the gauge of
  `u₂ s` equals `deTurckRicciRHS g_bg (g_DT s)`.

The match is the integrated decoupled analogue of
`deTurckNonlinearitySpectral_principalPart_cancels`, reconciled through the sorry-free
bridge `deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS`.  On the gate domain the
gate representative coincides with `T_s s` as a smooth section
(`gateSmoothRep (ι (u₂ s)) = T_s s`, since their `L²`-classes have the same eigenbasis
coordinates and `SmoothCcTensor.toL2` is injective), so the two `g₀`-rough-Laplacian
terms cancel; the gate-realized metric coincides with `g_DT s`; and the residual
`deTurckRHSSection` summand reduces to `deTurckRicciRHS g_bg (g_DT s)`.  `hgate` is the
honest gate the gated gauge requires (NOT the conclusion folded in: it is the
`MemAllTensorHs` + fibre-small validity datum, true for the maximal-regularity carrier and
discharged at the assembler).  The body is `sorry`, so consumers transitively depend on
`sorryAx`. -/
theorem deTurckRemainderRealize_geomMatch_lipschitz
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    (∃ K : ℝ≥0, ∀ u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1),
        ‖deTurckG0SectionDiffHa (I := I) (M := M) g₀ a
            (deTurckRemainderRealizeSection (I := I) g₀ g_bg) u u'‖
          ≤ (K : ℝ) * dist u u') ∧
      (∀ (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
          (u₂ : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
          (T_s : ℝ → Integral.L2.SmoothCcTensor g₀ 0 2),
        (∀ s ∈ Set.Ico (0 : ℝ) T,
          realizableAtGate (I := I) g₀
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) →
        (∀ s ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
          (g_DT s).inner x v w
            = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_s s) x v w) →
        (∀ s ∈ Set.Ico (0 : ℝ) T,
            ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
          (u₂ s).coeff i
            = tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i) →
        (∀ s ∈ Set.Ico (0 : ℝ) T,
          Integral.L2.SmoothCcTensor.toL2 (T_s s) =
            tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (show (0 : ℝ) ≤ (a : ℝ) + 2 by positivity) (u₂ s)) →
        ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ (x' : M) (v' w' : TangentSpace I x'),
          ccTensorBilinSymm (I := I) g₀
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T_s s)) x' v' w'
            + ccTensorBilinSymm (I := I) g₀
                (deTurckRemainderRealizeSection (I := I) g₀ g_bg
                  (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) x' v' w'
            = deTurckRicciRHS (I := I) g_bg (g_DT s) x' v' w') := by
  classical
  refine ⟨deTurckRemainderRealize_gauge_ha_lipschitz (I := I) (M := M) g₀ g_bg a, ?_⟩
  intro T g_DT u₂ T_s hgate hreal hsmoothrepr hcanon s hs x' v' w'
  set hcompact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set u : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) :=
    tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s) with hu_def
  have hg : realizableAtGate (I := I) g₀ u := hgate s hs
  -- The gate-produced representative's `L²` class is `tensorHsToL2 u`.
  have hgateL2 :
      Integral.L2.SmoothCcTensor.toL2 (gateSmoothRep (I := I) g₀ u hg.choose hg.choose_spec.choose)
        = Integral.L2.SmoothCcTensor.toL2 (T_s s) := by
    rw [gateSmoothRep_toL2 (I := I) g₀ u hg.choose hg.choose_spec.choose]
    -- `tensorHsToL2 (ι (u₂ s)) = tensorHsToL2 (u₂ s) = toL2 (T_s s)`, all by eigenbasis coords.
    set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hcompact with hb
    apply b.repr.injective
    ext i
    have hlhs :
        (b.repr (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            hcompact hg.choose u)) i = (u₂ s).coeff i := by
      rw [show (b.repr (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            hcompact hg.choose u)) i =
          tensorL2Coeff (I := I) (M := M) hcompact
            (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              hcompact hg.choose u) i from rfl,
        tensorHsToL2_tensorL2Coeff (I := I) (M := M) hg.choose u i, hu_def,
        tensorHsInclusion_coeff_apply]
    have hrhs :
        (b.repr (Integral.L2.SmoothCcTensor.toL2 (T_s s))) i = (u₂ s).coeff i := by
      rw [show (b.repr (Integral.L2.SmoothCcTensor.toL2 (T_s s))) i =
          tensorL2Coeff (I := I) (M := M) hcompact
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i from rfl]
      exact (hsmoothrepr s hs i).symm
    rw [hlhs, hrhs]
  have hgate_eq : gateSmoothRep (I := I) g₀ u hg.choose hg.choose_spec.choose = T_s s :=
    smoothCcTensor_toL2_injective (I := I) (M := M) g₀ 0 2 hgateL2
  -- The gate-realized metric equals `g_DT s`.
  have hmetric :
      tensorSectionRealizeMetric (I := I) g₀
        (gateSmoothRep (I := I) g₀ u hg.choose hg.choose_spec.choose)
        hg.choose_spec.choose_spec.choose_spec.1
        hg.choose_spec.choose_spec.choose_spec.2 = g_DT s := by
    refine smoothRiemannianMetric_eq_of_inner (I := I) (M := M) _ (g_DT s) ?_
    intro x v w
    rw [tensorSectionRealizeMetric_inner (I := I) g₀
        (gateSmoothRep (I := I) g₀ u hg.choose hg.choose_spec.choose)
        hg.choose_spec.choose_spec.choose_spec.1
        hg.choose_spec.choose_spec.choose_spec.2 x v w, hgate_eq, (hreal s hs x v w)]
  -- Split the gauge's symmetric form via the gate-realizable-branch identity, then
  -- cancel the two `g₀`-rough-Laplacian terms (`gateSmoothRep = T_s s`) and rewrite the
  -- gate-realized metric to `g_DT s`.
  rw [gauge_realizableGate_ccTensorBilinSymm (I := I) g₀ g_bg hg x' v' w',
    hmetric, hgate_eq]
  ring

end DifferentialGeometry.PDE.RicciFlow
