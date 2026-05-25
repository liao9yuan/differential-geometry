import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Continuous inclusion `H^{k+1} → H^k` of intrinsic Sobolev Hilbert spaces

For a closed Riemannian manifold `(M, g)`, the intrinsic `H^{k+1}` Sobolev
Hilbert space of `(r, s)`-tensor fields embeds continuously into `H^k` with
operator norm at most `1`. The inclusion is induced by the fact that the
Hilbert-Schmidt partition-of-unity-weighted chart-Sobolev norm is monotone
in the regularity order (`tensorPouSobolevHsNorm_le_succ`).

## Main definitions

* `inclusionHk_succ g r s k` — the continuous linear inclusion
  `TensorPouSobolevHilbert g r s (k+1) →L[ℝ] TensorPouSobolevHilbert g r s k`.

## Main results

* `inclusionHk_succ_opNorm_le_one` — its operator norm is bounded by `1`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSobolev

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Identity as a linear map on the smooth wrapper -/

set_option linter.unusedSectionVars false in
/-- The identity map `SmoothCcTensorHs g r s (k+1) →ₗ[ℝ] SmoothCcTensorHs g
r s k` viewed as a linear map between the two pre-Hilbert spaces (on the
same underlying additive group, but with different norms). -/
noncomputable def smoothInclusionHsSuccLin
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    SmoothCcTensorHs g r s (k + 1) →ₗ[ℝ] SmoothCcTensorHs g r s k where
  toFun S := ⟨S.toCcTensor⟩
  map_add' S T := by
    change (⟨(S + T).toCcTensor⟩ : SmoothCcTensorHs g r s k) =
      (⟨S.toCcTensor⟩ : SmoothCcTensorHs g r s k) +
        (⟨T.toCcTensor⟩ : SmoothCcTensorHs g r s k)
    rw [SmoothCcTensorHs.toCcTensor_add]
    rfl
  map_smul' c S := by
    change (⟨(c • S).toCcTensor⟩ : SmoothCcTensorHs g r s k) =
      c • (⟨S.toCcTensor⟩ : SmoothCcTensorHs g r s k)
    rw [SmoothCcTensorHs.toCcTensor_smul]
    rfl

/-! ## Finiteness of `tensorPouSobolevNorm` on smooth compactly-supported sections

The partition-of-unity-weighted chart-Sobolev `ℝ≥0∞`-valued norm of a smooth
compactly-supported tensor section is finite. The proof reduces the
chart-aggregating `tsum` to a finite sum over the (locally-finite) chart-atlas
partition-of-unity support, and bounds each per-chart integral by the volume
of the compact `chartImagePOUTsupport α` times an `L^∞`-bound on the smooth
integrand on that compact set.

This lemma is needed locally to compare `(tensorPouSobolevNorm g k T).toReal`
across two consecutive regularity orders, as the inclusion
`SmoothCcTensorHs g r s (k+1) →ₗ[ℝ] SmoothCcTensorHs g r s k` requires. -/

/-- Bound for the per-`(α, IJ, j)` Lebesgue integral inside
`tensorPouSobolevNorm`. The integrand is pointwise zero off the compact set
`chartImagePOUTsupport α` (because the partition-of-unity weight pulled back
to the chart target vanishes there), and is bounded by the continuous function
`y ↦ ‖iteratedFDeriv ℝ j (raw ∘ extChartAt.symm) (toEuclidean.symm y)‖²` on the
compact set. The set has finite Lebesgue measure, and the integrand is bounded
on it, hence the integral is finite. -/
private lemma tensorPouSobolevNorm_inner_integral_lt_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) :
    (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖ ^ 2)
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) < ⊤ := by
  classical
  -- Key bound: the integrand is bounded above pointwise by a CONSTANT `C`
  -- (depending on `α, Idx, Jdx, j, T`, but not on `y`).
  -- Choose:
  --   `Mvol := (volume (chartTargetEuclid α)).toNNReal`  (could be ∞ — bad!)
  --   `C := 1 * supC` where `supC` is bound for `|D^j (raw ∘ pull)|²` on the
  --                  chart target. Could also be ∞.
  --
  -- The safe path: bound by indicator * constant on the compact set
  -- `chartImagePOUTsupport α ⊆ chartTargetEuclid α`.
  -- The POU weight in the integrand pulls back to a function on EuclN that
  -- vanishes off `chartImagePOUTsupport α` (essentially by definition).
  --
  -- We split the integral and bound each piece:
  --   ∫⁻ y in chartTargetEuclid, f y = ∫⁻ y in chartImagePOUTsupport, f y
  -- because `f y = 0` on the complement (POU is zero there).
  set K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartImagePOUTsupport (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  -- Define the integrand f : EuclN → ℝ≥0∞.
  set f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ≥0∞ :=
    fun y =>
      ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ‖iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ∘ (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2) with hf_def
  -- The integrand vanishes on `chartTargetEuclid \ K`.
  have hf_zero_off_K : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      y ∉ K → f y = 0 := by
    intro y hy_target hy_off
    -- Off `K`, the POU pulled back to chart target equals 0 — this is the
    -- content of `chartPushed_eq_zero_off_chartImagePOUTsupport` applied to
    -- the constant-1 scalar (whose chart-pushed version is just the POU
    -- pulled back).
    have hpush_zero :
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
          α (fun _ : M => (1 : ℝ)) y = 0 :=
      chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M)
        α (fun _ => 1) hy_target hy_off
    -- `chartPushed ρ α (fun _ => 1) y = ρ α (pull(y)) * 1 = ρ α (pull(y))`.
    have hpush_unfold :
        chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
            α (fun _ : M => (1 : ℝ)) y =
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
      simp [chartPushed]
    have hPOU_y : (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
      rw [← hpush_unfold]; exact hpush_zero
    -- The integrand is `ENNReal.ofReal (0 * _) = 0`.
    change ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) * _) = 0
    rw [hPOU_y, zero_mul, ENNReal.ofReal_zero]
  -- The integral over `chartTargetEuclid` equals the integral over `K`.
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hT_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hsplit :
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α, f y
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) =
      ∫⁻ y in K, f y
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
    rw [← MeasureTheory.lintegral_indicator hT_meas,
        ← MeasureTheory.lintegral_indicator hK_meas]
    refine MeasureTheory.lintegral_congr (fun y => ?_)
    by_cases hyK : y ∈ K
    · have hyT : y ∈ chartTargetEuclid (I := I) (M := M) α := hK_sub hyK
      simp [Set.indicator_of_mem, hyK, hyT]
    · by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
      · -- y in chartTarget, off K: integrand is 0.
        have hf0 : f y = 0 := hf_zero_off_K y hyT hyK
        rw [Set.indicator_of_mem hyT, Set.indicator_of_notMem hyK, hf0]
      · simp [Set.indicator_of_notMem, hyK, hyT]
  rw [hsplit]
  -- Now bound `∫⁻ y in K, f y` by a constant times `volume K`.
  -- `K` is compact, hence has finite Lebesgue measure.
  have hK_vol : (volume :
      Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) K < ⊤ :=
    hK_compact.measure_lt_top
  -- Bound the integrand on K by a constant. We need an NNReal `C` such that
  -- f y ≤ C for all y ∈ K. The integrand is `ENNReal.ofReal (POU * D²)`.
  -- `POU` is bounded by `1`, `D²` is bounded by `(sup_K D)²` (continuous on
  -- a compact set), so `POU * D² ≤ (sup_K D)²`. Pick any such bound.
  -- Continuity argument: `iteratedFDeriv ℝ j (raw ∘ extChartAt.symm)` is
  -- `ContinuousOn` on `extChartAt.target`, so the composition with
  -- `toEuclidean.symm` is `ContinuousOn` on `chartTargetEuclid`. On the
  -- compact subset `K ⊆ chartTargetEuclid`, it is bounded.
  -- A simpler bound: |D^j(.)| is a real, hence at any point has some value;
  -- the SUPREMUM over `K` (compact) is finite by continuity. Adding
  -- `‖POU(pull y)‖ ≤ 1` gives an overall bound.
  --
  -- We use `setLIntegral_lt_top_of_le_nnreal` with `s := K` (finite vol)
  -- and `f y ≤ y_bound` for some NNReal bound on K.
  --
  -- Choosing the bound: since the integrand is `ENNReal.ofReal _` and the
  -- inner expression is a real ≥ 0, we can pick `y_bound` as the (NNReal)
  -- of the sup of the inner expression over `y ∈ K`. The inner expression
  -- is a continuous function of `y` on `chartTargetEuclid α` (open), and
  -- `K ⊆ chartTargetEuclid α` compact, so it is bounded by a constant.
  --
  -- The exact identification of the constant is complex, so we use a CRUDE
  -- bound via the supremum on K. Pick:
  --   ψ(y) := POU(pull(y)) * ‖D^j(...)‖²,
  -- continuous on `chartTargetEuclid α` (and hence on K, a subset),
  -- bounded on K by some `M ≥ 0`. Then `f(y) = ENNReal.ofReal ψ(y) ≤ ofReal M`.
  refine MeasureTheory.setLIntegral_lt_top_of_le_nnreal hK_vol.ne ?_
  -- We need: ∃ y_bnd : ℝ≥0, ∀ y ∈ K, f y ≤ y_bnd.
  -- Since the integrand `ENNReal.ofReal _` is bounded by `ENNReal.ofReal M`
  -- for some real `M`, we take `y_bnd := M.toNNReal`.
  -- The continuous function `ψ : EuclN → ℝ` defined by the inner expression
  -- needs to be continuous on `K` to apply boundedness; this requires the
  -- `iteratedFDeriv` to be continuous on K.
  --
  -- Build ψ as a continuous-on-K function and apply `IsCompact.bddAbove`.
  -- The continuity of `ψ` on K (a subset of chart target) follows from:
  --   - POU is C∞ on M, pullback is continuous on chart target
  --   - `iteratedFDeriv ℝ j` of a smooth function is continuous
  --   - composition with `toEuclidean.symm` is continuous (linear iso)
  --   - composition with `extChartAt.symm` is continuous on chart target
  --
  -- We use a SUPER CRUDE approach: instead of computing ψ continuously, we
  -- bound EACH FACTOR:
  --   * `POU(pull(y)) ≤ 1` (POU is a partition of unity weight ∈ [0,1]).
  --   * `‖D^j(...)‖²` on K is bounded by some NNReal (by continuity on K).
  -- Multiplying, ψ ≤ (some NNReal) on K.
  --
  -- Implementation: define `B := some bound for |D^j(...)|² on K`, then
  -- `f y ≤ ofReal B`. Take `y_bnd := B.toNNReal`.
  --
  -- Actually, the cleanest approach uses continuity of the inner expression
  -- on chartTargetEuclid (open) and IsCompact.image / IsCompact.bddAbove.
  -- Here we sidestep the explicit `B` and just exhibit "some NNReal bound".
  -- Define ψ : EuclN → ℝ.
  set ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ := fun y =>
    ((chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
      ‖iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y)‖ ^ 2 with hψ_def
  -- The function ψ is continuous on `chartTargetEuclid α` because:
  --   * POU pulled back to chartTarget is continuous (POU is C∞, pull is
  --     continuous on its domain),
  --   * iteratedFDeriv of a function smooth on chartSource is continuous
  --     on chartTarget (after pulling back).
  --   * Multiplication and norm-squared are continuous.
  -- On the compact subset K, ψ is bounded.
  -- We extract bounded-ness via a uniform-on-K bound using the
  -- norm of `iteratedFDeriv` evaluated at the image-points of K under
  -- `toEuclidean.symm ∘ chart.symm` (which lies in chart.source, a
  -- compact image of K).
  --
  -- Direct route: enumerate `K`'s elements and just bound.
  -- The most concise tactic: since ψ y ≥ 0 for all y, and there is SOME
  -- finite bound on K (because K is compact and the integrand vanishes
  -- nicely outside POU-support), exists is automatic with ENNReal.coe_one.
  --
  -- Actually, we proceed by a clean structural argument using the
  -- following continuity facts:
  --
  -- 1. The function `gT : EuclN → ℝ` defined by
  --    `y ↦ ‖iteratedFDeriv ℝ j (raw ∘ extChartAt.symm) (toEuclidean.symm y)‖²`
  --    is continuous on `chartTargetEuclid α`.
  -- 2. The POU weight pulled back to EuclN is bounded by `1` everywhere on
  --    EuclN (the chart-atlas POU has values in `[0, 1]`).
  -- 3. Their product is bounded on `K ⊆ chartTargetEuclid α` by
  --    `sup_K gT` (a finite real, by compactness).
  --
  -- We isolate the continuity of `gT` (the only nontrivial step) and apply
  -- `IsCompact.bddAbove_image`. Since this is a chain of compositions of
  -- continuous maps on open sets, with K contained in those open sets, we
  -- get the bound. We package the whole thing as a continuous-on-K version.
  --
  -- For brevity, we use the boundedness of ψ on the compact `K` via a
  -- WEAKER but still sufficient bound: since each contributing factor is
  -- finite at each point, the supremum on K is some real ≥ 0.
  -- However, to FORMALLY produce an NNReal witness, we use the following
  -- elementary fact: a continuous-on-`s` non-negative real function on a
  -- compact `s` attains its maximum at some point, hence is bounded above
  -- by `‖f‖_∞` (a finite real).
  --
  -- We provide an explicit witness using `ContinuousOn.bddAbove_image_of_isCompact`.
  -- Equivalent: `(hK_compact.image_of_continuousOn hψ_contOn_K).bddAbove`.
  have hψ_contOn :
      ContinuousOn ψ (chartTargetEuclid (I := I) (M := M) α) := by
    -- POU∘pull is continuous on the chart target, and D^j(raw∘pull)
    -- is continuous on the chart target. Their product and norm are
    -- continuous compositions.
    have hPOU_smooth :
        ContMDiff I (𝓘(ℝ, ℝ)) ∞
          (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) :=
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
    -- Continuity of POU∘pull on chartTargetEuclid:
    have hPOU_pull_cont :
        ContinuousOn (fun y : EuclideanSpace ℝ
              (Fin (Module.finrank ℝ E)) =>
            (chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm
                ((toEuclidean (E := E)).symm y)))
          (chartTargetEuclid (I := I) (M := M) α) := by
      have hPOU_cont :
          Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
        hPOU_smooth.continuous
      have hSymmCont : ContinuousOn ((extChartAt I α).symm)
          (extChartAt I α).target :=
        continuousOn_extChartAt_symm α
      have h_toEucl_cont : Continuous
          ((toEuclidean (E := E)).symm : _ → _) :=
        (toEuclidean (E := E)).symm.continuous
      -- Composition
      have h_inner : ContinuousOn
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTargetEuclid (I := I) (M := M) α) := by
        refine hSymmCont.comp h_toEucl_cont.continuousOn ?_
        intro y hy
        -- `y ∈ chartTargetEuclid α ↔ toEuclidean.symm y ∈ chartAt.target`
        unfold chartTargetEuclid at hy
        obtain ⟨z, hz_tgt, hz_eq⟩ := hy
        rw [← hz_eq]
        -- `toEuclidean.symm (toEuclidean z) = z`
        change (toEuclidean (E := E)).symm
            ((toEuclidean (E := E)) z) ∈ (extChartAt I α).target
        rw [(toEuclidean (E := E)).symm_apply_apply]
        exact hz_tgt
      exact hPOU_cont.comp_continuousOn' h_inner
    -- Continuity of D^j(raw∘pull) on chartTargetEuclid via raw smoothness.
    have h_raw_smoothOn : ContMDiffOn I (𝓘(ℝ, ℝ)) ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)
        ((chartAt H α).source) :=
      tensorChartComponentRaw_contMDiffOn_chart_source
        (I := I) (M := M) g r s T α Idx Jdx
    have h_raw_pull_contDiffOn :
        ContDiffOn ℝ ∞
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm)
          (extChartAt I α).target := by
      -- ContMDiffOn (raw) on chart source pulls back via extChartAt.symm
      -- to a ContDiffOn on (extChartAt I α).target.
      have h_extSymm : ContMDiffOn 𝓘(ℝ, E) I ∞
          ((extChartAt I α).symm : E → M) (extChartAt I α).target :=
        contMDiffOn_extChartAt_symm α
      have h_comp_mdiff : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, ℝ)) ∞
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm)
          (extChartAt I α).target := by
        refine h_raw_smoothOn.comp h_extSymm ?_
        intro y hy
        change (extChartAt I α).symm y ∈ (chartAt H α).source
        rw [← extChartAt_source (I := I)]
        exact (extChartAt I α).map_target hy
      exact h_comp_mdiff.contDiffOn
    -- iteratedFDeriv ℝ j of a ContDiffOn ∞ function is ContinuousOn.
    have h_iter_contOn : ContinuousOn
        (iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm))
        (extChartAt I α).target := by
      -- For ContDiff ℝ ∞ on an open set (extChartAt I α).target,
      -- the iteratedFDeriv is continuous on the same set.
      -- The cleanest tactic: use `ContDiffOn.continuousOn_iteratedFDerivWithin`
      -- and bridge to global `iteratedFDeriv` via openness of the set.
      have h_open : IsOpen (extChartAt I α).target :=
        isOpen_extChartAt_target α
      -- ContDiff∞ on an open set ⇒ ContDiff∞ at every point of the set.
      have h_cd_at : ∀ y ∈ (extChartAt I α).target,
          ContDiffAt ℝ ∞
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm) y :=
        fun y hy => h_raw_pull_contDiffOn.contDiffAt
          (h_open.mem_nhds hy)
      -- Now use that iteratedFDeriv of ContDiff∞ at y is continuous at y.
      intro y hy
      have h_cd : ContDiffAt ℝ ∞
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm) y := h_cd_at y hy
      have h_cont_iter : ContinuousAt
          (iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm)) y := by
        exact h_cd.continuousAt_iteratedFDeriv (k := j) (by exact_mod_cast le_top)
      exact h_cont_iter.continuousWithinAt
    -- Pull back through toEuclidean.symm to chartTargetEuclid.
    have h_iter_pull_contOn : ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_toEucl_cont : Continuous
          ((toEuclidean (E := E)).symm : _ → _) :=
        (toEuclidean (E := E)).symm.continuous
      refine h_iter_contOn.comp h_toEucl_cont.continuousOn ?_
      intro y hy
      unfold chartTargetEuclid at hy
      obtain ⟨z, hz_tgt, hz_eq⟩ := hy
      rw [← hz_eq]
      change (toEuclidean (E := E)).symm
          ((toEuclidean (E := E)) z) ∈ (extChartAt I α).target
      rw [(toEuclidean (E := E)).symm_apply_apply]
      exact hz_tgt
    -- Take norm and square.
    have h_norm_sq_contOn : ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          ‖iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ∘ (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2)
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_norm : ContinuousOn
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            ‖iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖)
          (chartTargetEuclid (I := I) (M := M) α) :=
        h_iter_pull_contOn.norm
      exact h_norm.pow 2
    -- Multiply by POU ∘ pull.
    exact hPOU_pull_cont.mul h_norm_sq_contOn
  -- ψ is bounded on the compact K.
  have hψ_contOn_K : ContinuousOn ψ K := hψ_contOn.mono hK_sub
  have hψ_bdd : ∃ M : ℝ, ∀ y ∈ K, ψ y ≤ M := by
    obtain ⟨M, hM⟩ := (hK_compact.image_of_continuousOn hψ_contOn_K).bddAbove
    refine ⟨M, fun y hy => ?_⟩
    exact hM ⟨y, hy, rfl⟩
  obtain ⟨B, hB⟩ := hψ_bdd
  -- Pick the NNReal witness.
  refine ⟨B.toNNReal, fun y hy => ?_⟩
  -- f y = ofReal (ψ y) ≤ ↑(B.toNNReal).
  rw [hf_def]
  -- ENNReal.ofReal (ψ y) ≤ ↑(B.toNNReal) iff (with B ≥ ψ y ≥ 0)
  --   ψ y ≤ B.toNNReal.toReal = max B 0 ≥ B ≥ ψ y.
  refine ENNReal.ofReal_le_of_le_toReal ?_
  change ψ y ≤ (B.toNNReal : ℝ≥0∞).toReal
  rw [ENNReal.coe_toReal, Real.coe_toNNReal']
  exact (hB y hy).trans (le_max_left _ _)

theorem tensorPouSobolevNorm_ne_top
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevNorm (I := I) (M := M) g k T ≠ ⊤ := by
  classical
  suffices h : tensorPouSobolevNorm (I := I) (M := M) g k T < ⊤ from h.ne
  rw [tensorPouSobolevNorm_eq]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  -- Collapse `tsum` to a finite sum over the chart-atlas POU support.
  have htsum_eq :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ
                  (Fin (Module.finrank ℝ E))))) =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ
                  (Fin (Module.finrank ℝ E)))) := by
    refine tsum_eq_sum ?_
    intro α hα
    have hPOU_zero : ∀ x : M, (chartAtlasPOU I M α : M → ℝ) x = 0 :=
      fun x => chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
    refine Finset.sum_eq_zero ?_
    intro IJ _
    refine Finset.sum_eq_zero ?_
    intro j _
    -- Integrand vanishes pointwise on chartTargetEuclid α: POU = 0 ⇒ integrand = 0.
    have h_integrand_zero :
        ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α
                      IJ.1 IJ.2
                    ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2) = 0 := by
      intro y _
      rw [hPOU_zero, zero_mul, ENNReal.ofReal_zero]
    rw [MeasureTheory.setLIntegral_congr_fun
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
      h_integrand_zero]
    simp
  rw [htsum_eq]
  refine (ENNReal.sum_lt_top.mpr ?_).ne
  intro α _
  refine ENNReal.sum_lt_top.mpr ?_
  intro IJ _
  refine ENNReal.sum_lt_top.mpr ?_
  intro j _
  exact tensorPouSobolevNorm_inner_integral_lt_top
    (I := I) (M := M) g r s T α IJ.1 IJ.2 j

/-! ## Finiteness of `tensorPouSobolevHsNorm` on smooth compactly-supported sections

Parallel finiteness lemma for the Hilbert-Schmidt aggregation
`tensorPouSobolevHsNorm`. The argument is identical in shape to the
operator-norm version, but the inner integrand is now bounded via
`|D^j(f)(basis_tuple)|² ≤ ‖D^j(f)‖² · ∏ᵢ ‖basis_i‖² = ‖D^j(f)‖²`
(using that `EuclideanSpace.basisFun` is an orthonormal basis), so each
per-basis-tuple integral is bounded by the corresponding op-norm integral
for the EuclN-pulled function. Continuity of the iterated derivative on the
compact subset of the chart target then gives finiteness. -/

/-- The function `(raw ∘ extChart.symm ∘ toEuclidean.symm) : EuclN → ℝ` is
`ContDiffOn` of any order on `chartTargetEuclid α`. -/
private lemma tensorChartComponentRaw_euclidPull_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- Step 1: `(raw ∘ extChart.symm) : E → ℝ` is `ContDiffOn ∞` on
  -- `(extChartAt I α).target`.
  have h_raw_smoothOn : ContMDiffOn I (𝓘(ℝ, ℝ)) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)
      ((chartAt H α).source) :=
    tensorChartComponentRaw_contMDiffOn_chart_source
      (I := I) (M := M) g r s T α Idx Jdx
  have h_raw_pull_contDiffOn :
      ContDiffOn ℝ ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm)
        (extChartAt I α).target := by
    have h_extSymm : ContMDiffOn 𝓘(ℝ, E) I ∞
        ((extChartAt I α).symm : E → M) (extChartAt I α).target :=
      contMDiffOn_extChartAt_symm α
    have h_comp_mdiff : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, ℝ)) ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm)
        (extChartAt I α).target := by
      refine h_raw_smoothOn.comp h_extSymm ?_
      intro y hy
      change (extChartAt I α).symm y ∈ (chartAt H α).source
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I α).map_target hy
    exact h_comp_mdiff.contDiffOn
  -- Step 2: compose with `toEuclidean.symm : EuclN → E` (smooth as CLE).
  have h_toEucl_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
    ContinuousLinearEquiv.contDiff _
  have h_maps : Set.MapsTo ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α)
      (extChartAt I α).target := by
    intro y hy
    rcases hy with ⟨z, hz_tgt, hz_eq⟩
    have h_eq : (toEuclidean (E := E)).symm y = z := by
      rw [← hz_eq]; exact (toEuclidean (E := E)).symm_apply_apply z
    rw [h_eq]; exact hz_tgt
  exact h_raw_pull_contDiffOn.comp
    h_toEucl_symm_smooth.contDiffOn h_maps

/-- Bound for the per-`(α, IJ, j, basisIdx)` Lebesgue integral inside
`tensorPouSobolevHsNorm`. The integrand vanishes off the compact set
`chartImagePOUTsupport α` (POU pulled back to the chart target is zero
there), and on the compact set the integrand is bounded by a continuous
function. -/
private lemma tensorPouSobolevHsNorm_inner_integral_lt_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) :
    (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) < ⊤ := by
  classical
  -- Mirror the structure of `tensorPouSobolevNorm_inner_integral_lt_top`.
  set K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartImagePOUTsupport (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  set f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ≥0∞ :=
    fun y =>
      ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm)
                y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2) with hf_def
  have hf_zero_off_K : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      y ∉ K → f y = 0 := by
    intro y hy_target hy_off
    have hpush_zero :
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
          α (fun _ : M => (1 : ℝ)) y = 0 :=
      chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M)
        α (fun _ => 1) hy_target hy_off
    have hpush_unfold :
        chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
            α (fun _ : M => (1 : ℝ)) y =
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
      simp [chartPushed]
    have hPOU_y : (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
      rw [← hpush_unfold]; exact hpush_zero
    change ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) * _) = 0
    rw [hPOU_y, zero_mul, ENNReal.ofReal_zero]
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hT_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hsplit :
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α, f y
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) =
      ∫⁻ y in K, f y
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
    rw [← MeasureTheory.lintegral_indicator hT_meas,
        ← MeasureTheory.lintegral_indicator hK_meas]
    refine MeasureTheory.lintegral_congr (fun y => ?_)
    by_cases hyK : y ∈ K
    · have hyT : y ∈ chartTargetEuclid (I := I) (M := M) α := hK_sub hyK
      simp [Set.indicator_of_mem, hyK, hyT]
    · by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
      · have hf0 : f y = 0 := hf_zero_off_K y hyT hyK
        rw [Set.indicator_of_mem hyT, Set.indicator_of_notMem hyK, hf0]
      · simp [Set.indicator_of_notMem, hyK, hyT]
  rw [hsplit]
  have hK_vol : (volume :
      Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) K < ⊤ :=
    hK_compact.measure_lt_top
  -- Continuity of the integrand on `chartTargetEuclid α`.
  set ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ := fun y =>
    ((chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
      |(iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm)
            y)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 with hψ_def
  have hψ_contOn :
      ContinuousOn ψ (chartTargetEuclid (I := I) (M := M) α) := by
    -- POU∘pull continuous on chart target.
    have hPOU_smooth :
        ContMDiff I (𝓘(ℝ, ℝ)) ∞
          (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) :=
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
    have hPOU_pull_cont :
        ContinuousOn (fun y : EuclideanSpace ℝ
              (Fin (Module.finrank ℝ E)) =>
            (chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm
                ((toEuclidean (E := E)).symm y)))
          (chartTargetEuclid (I := I) (M := M) α) := by
      have hPOU_cont :
          Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
        hPOU_smooth.continuous
      have hSymmCont : ContinuousOn ((extChartAt I α).symm)
          (extChartAt I α).target :=
        continuousOn_extChartAt_symm α
      have h_toEucl_cont : Continuous
          ((toEuclidean (E := E)).symm : _ → _) :=
        (toEuclidean (E := E)).symm.continuous
      have h_inner : ContinuousOn
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTargetEuclid (I := I) (M := M) α) := by
        refine hSymmCont.comp h_toEucl_cont.continuousOn ?_
        intro y hy
        unfold chartTargetEuclid at hy
        obtain ⟨z, hz_tgt, hz_eq⟩ := hy
        rw [← hz_eq]
        change (toEuclidean (E := E)).symm
            ((toEuclidean (E := E)) z) ∈ (extChartAt I α).target
        rw [(toEuclidean (E := E)).symm_apply_apply]
        exact hz_tgt
      exact hPOU_cont.comp_continuousOn' h_inner
    -- Continuity of `iteratedFDeriv ℝ j (raw∘pull∘toEucl.symm)` on chart target.
    have h_iter_contOn : ContinuousOn
        (iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm
            ∘ (toEuclidean (E := E)).symm))
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
        chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_cdOn :
          ContDiffOn ℝ ∞
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm)
            (chartTargetEuclid (I := I) (M := M) α) :=
        tensorChartComponentRaw_euclidPull_contDiffOn
          (I := I) (M := M) g r s T α Idx Jdx
      intro y hy
      have h_cd : ContDiffAt ℝ ∞
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm
            ∘ (toEuclidean (E := E)).symm) y :=
        h_cdOn.contDiffAt (h_open.mem_nhds hy)
      have h_cont_iter : ContinuousAt
          (iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm)) y :=
        h_cd.continuousAt_iteratedFDeriv (k := j) (by exact_mod_cast le_top)
      exact h_cont_iter.continuousWithinAt
    -- Multilinear evaluation of `iteratedFDeriv` at a fixed argument tuple.
    have h_eval_contOn : ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ∘ (extChartAt I α).symm
                ∘ (toEuclidean (E := E)).symm)
              y)
            (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)))
        (chartTargetEuclid (I := I) (M := M) α) := by
      -- `apply` of a continuous family of multilinear maps at a fixed
      -- argument is continuous via the `ContinuousEvalConst` instance on
      -- `ContinuousMultilinearMap`.
      have h_apply : Continuous
          fun A : ContinuousMultilinearMap ℝ
              (fun _ : Fin j => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ℝ =>
            A (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) :=
        continuous_eval_const _
      exact h_apply.comp_continuousOn h_iter_contOn
    -- `|·|² ∘ eval` continuous on chart target.
    have h_abs_sq_contOn : ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm)
                y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_abs : ContinuousOn
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))|)
          (chartTargetEuclid (I := I) (M := M) α) :=
        h_eval_contOn.abs
      exact h_abs.pow 2
    exact hPOU_pull_cont.mul h_abs_sq_contOn
  have hψ_contOn_K : ContinuousOn ψ K := hψ_contOn.mono hK_sub
  have hψ_bdd : ∃ M : ℝ, ∀ y ∈ K, ψ y ≤ M := by
    obtain ⟨M, hM⟩ := (hK_compact.image_of_continuousOn hψ_contOn_K).bddAbove
    refine ⟨M, fun y hy => ?_⟩
    exact hM ⟨y, hy, rfl⟩
  obtain ⟨B, hB⟩ := hψ_bdd
  refine MeasureTheory.setLIntegral_lt_top_of_le_nnreal hK_vol.ne ?_
  refine ⟨B.toNNReal, fun y hy => ?_⟩
  rw [hf_def]
  refine ENNReal.ofReal_le_of_le_toReal ?_
  change ψ y ≤ (B.toNNReal : ℝ≥0∞).toReal
  rw [ENNReal.coe_toReal, Real.coe_toNNReal']
  exact (hB y hy).trans (le_max_left _ _)

private lemma tensorPouSobolevHsNorm_ne_top
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevHsNorm (I := I) (M := M) g k T ≠ ⊤ := by
  classical
  suffices h : tensorPouSobolevHsNorm (I := I) (M := M) g k T < ⊤ from h.ne
  rw [tensorPouSobolevHsNorm_eq]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  -- Collapse `tsum` to a finite sum over the chart-atlas POU support.
  have htsum_eq :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α
                              IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α
                              IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E)))) := by
    refine tsum_eq_sum ?_
    intro α hα
    have hPOU_zero : ∀ x : M, (chartAtlasPOU I M α : M → ℝ) x = 0 :=
      fun x => chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
    refine Finset.sum_eq_zero ?_
    intro IJ _
    refine Finset.sum_eq_zero ?_
    intro j _
    refine Finset.sum_eq_zero ?_
    intro basisIdx _
    have h_integrand_zero :
        ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α
                        IJ.1 IJ.2
                      ∘ (extChartAt I α).symm
                      ∘ (toEuclidean (E := E)).symm)
                    y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2) = 0 := by
      intro y _
      rw [hPOU_zero, zero_mul, ENNReal.ofReal_zero]
    rw [MeasureTheory.setLIntegral_congr_fun
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
      h_integrand_zero]
    simp
  rw [htsum_eq]
  refine (ENNReal.sum_lt_top.mpr ?_).ne
  intro α _
  refine ENNReal.sum_lt_top.mpr ?_
  intro IJ _
  refine ENNReal.sum_lt_top.mpr ?_
  intro j _
  refine ENNReal.sum_lt_top.mpr ?_
  intro basisIdx _
  exact tensorPouSobolevHsNorm_inner_integral_lt_top
    (I := I) (M := M) g r s T α IJ.1 IJ.2 j basisIdx

set_option linter.unusedSectionVars false in
/-- The norm bound `‖smoothInclusionHsSuccLin g r s k S‖ ≤ 1 * ‖S‖`,
expressing that the `H^k` norm is dominated by the `H^{k+1}` norm on the
smooth dense subspace. -/
lemma smoothInclusionHsSuccLin_norm_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (S : SmoothCcTensorHs g r s (k + 1)) :
    ‖smoothInclusionHsSuccLin (I := I) (M := M) g r s k S‖ ≤ 1 * ‖S‖ := by
  -- The inclusion map is the identity on the underlying section, so the
  -- norm of its image equals the `H^k` norm of `S.toCcTensor`. Likewise,
  -- the source norm equals the `H^{k+1}` norm of `S.toCcTensor`. The
  -- comparison then reduces to `tensorPouSobolevHsNorm_le_succ`, monotonicity
  -- of the Hilbert-Schmidt partition-of-unity-weighted chart-Sobolev norm
  -- in `k`.
  rw [one_mul]
  set T : SmoothCcTensor g r s := S.toCcTensor
  have h_inclusion :
      smoothInclusionHsSuccLin (I := I) (M := M) g r s k S =
        (⟨T⟩ : SmoothCcTensorHs g r s k) := rfl
  rw [h_inclusion]
  -- LHS: bring the (k)-wrapper norm into the completion via `norm_coe`,
  -- then use `tensorPouSobolevHilbert_norm_eq`.
  have h_lhs_coe :
      ‖(⟨T⟩ : SmoothCcTensorHs g r s k)‖ =
        ‖((⟨T⟩ : SmoothCcTensorHs g r s k) :
          UniformSpace.Completion (SmoothCcTensorHs g r s k))‖ :=
    (UniformSpace.Completion.norm_coe (⟨T⟩ : SmoothCcTensorHs g r s k)).symm
  have h_lhs_eq :
      ‖((⟨T⟩ : SmoothCcTensorHs g r s k) :
        UniformSpace.Completion (SmoothCcTensorHs g r s k))‖ =
      (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal := by
    change ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) k T‖ =
        (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal
    exact tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g k T
  have h_rhs_coe :
      ‖S‖ = ‖((⟨T⟩ : SmoothCcTensorHs g r s (k + 1)) :
        UniformSpace.Completion (SmoothCcTensorHs g r s (k + 1)))‖ := by
    have hS : S = (⟨T⟩ : SmoothCcTensorHs g r s (k + 1)) := by
      cases S; rfl
    calc ‖S‖
        = ‖(⟨T⟩ : SmoothCcTensorHs g r s (k + 1))‖ := by rw [hS]
      _ = ‖((⟨T⟩ : SmoothCcTensorHs g r s (k + 1)) :
            UniformSpace.Completion (SmoothCcTensorHs g r s (k + 1)))‖ :=
          (UniformSpace.Completion.norm_coe
            (⟨T⟩ : SmoothCcTensorHs g r s (k + 1))).symm
  have h_rhs_eq :
      ‖((⟨T⟩ : SmoothCcTensorHs g r s (k + 1)) :
        UniformSpace.Completion (SmoothCcTensorHs g r s (k + 1)))‖ =
      (tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T).toReal := by
    change ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (k + 1) T‖ =
        (tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T).toReal
    exact tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g (k + 1) T
  -- Combine all four identities and reduce to monotonicity of `.toReal`.
  rw [h_lhs_coe, h_lhs_eq, h_rhs_coe, h_rhs_eq]
  -- It now suffices to show
  --   (tensorPouSobolevHsNorm g k T).toReal ≤
  --     (tensorPouSobolevHsNorm g (k+1) T).toReal,
  -- which follows from `tensorPouSobolevHsNorm_le_succ` and
  -- `ENNReal.toReal_mono` once we know the `(k+1)`-value is finite
  -- (private lemma above).
  exact ENNReal.toReal_mono
    (tensorPouSobolevHsNorm_ne_top (I := I) (M := M) g (k + 1) T)
    (tensorPouSobolevHsNorm_le_succ (I := I) (M := M) g k T)

set_option linter.unusedSectionVars false in
/-- The continuous linear inclusion `SmoothCcTensorHs g r s (k+1) →L[ℝ]
SmoothCcTensorHs g r s k` on the smooth dense subspace, with operator norm
at most `1`. -/
noncomputable def smoothInclusionHsSucc
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    SmoothCcTensorHs g r s (k + 1) →L[ℝ] SmoothCcTensorHs g r s k :=
  (smoothInclusionHsSuccLin (I := I) (M := M) g r s k).mkContinuous 1
    (fun S => smoothInclusionHsSuccLin_norm_le (I := I) (M := M) g r s k S)

/-! ## Lifting the inclusion to the completion

The smooth-level inclusion `smoothInclusionHsSucc` is uniformly continuous
and lifts canonically to a continuous linear map on the Hilbert-space
completions via the `ContinuousLinearMap.extend` along the dense uniform
embedding `UniformSpace.Completion.toComplL`. -/

set_option linter.unusedSectionVars false in
/-- The smooth-level inclusion composed with the completion embedding on the
codomain side: a continuous linear map `SmoothCcTensorHs g r s (k+1) →L[ℝ]
TensorPouSobolevHilbert g r s k`, sending each smooth section into the
intrinsic `H^k` Hilbert space. -/
noncomputable def smoothInclusionHsSuccToHkCompl
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    SmoothCcTensorHs g r s (k + 1) →L[ℝ]
      TensorPouSobolevHilbert g r s k :=
  (UniformSpace.Completion.toComplL :
    SmoothCcTensorHs g r s k →L[ℝ] TensorPouSobolevHilbert g r s k).comp
    (smoothInclusionHsSucc (I := I) (M := M) g r s k)

set_option linter.unusedSectionVars false in
/-- The continuous linear inclusion
`TensorPouSobolevHilbert g r s (k+1) →L[ℝ] TensorPouSobolevHilbert g r s k`,
expressing the standard `H^{k+1} ↪ H^k` embedding at intrinsic Sobolev
regularity, with operator norm bounded by `1`.

Defined as the continuous linear extension of the smooth-level inclusion
along the dense uniform embedding `UniformSpace.Completion.toComplL`. -/
noncomputable def inclusionHk_succ
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    TensorPouSobolevHilbert g r s (k + 1) →L[ℝ]
      TensorPouSobolevHilbert g r s k :=
  ContinuousLinearMap.extend
    (smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k)
    (UniformSpace.Completion.toComplL :
      SmoothCcTensorHs g r s (k + 1) →L[ℝ]
        TensorPouSobolevHilbert g r s (k + 1))

set_option linter.unusedSectionVars false in
/-- The operator norm of the intrinsic `H^{k+1} ↪ H^k` inclusion is at
most `1`. -/
theorem inclusionHk_succ_opNorm_le_one
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ‖inclusionHk_succ (I := I) (M := M) g r s k‖ ≤ 1 := by
  -- Use `ContinuousLinearMap.opNorm_extend_le` with `N = 1`:
  -- the dense embedding `toComplL` is a linear isometry, so it expands the
  -- norm by exactly the factor `1`, and the extension's operator norm is
  -- bounded by `1 * ‖smoothInclusionHsSuccToHkCompl‖`.
  -- It then suffices to bound `‖smoothInclusionHsSuccToHkCompl‖ ≤ 1`.
  have h_dense :
      DenseRange
        (UniformSpace.Completion.toComplL :
          SmoothCcTensorHs g r s (k + 1) →L[ℝ]
            TensorPouSobolevHilbert g r s (k + 1)) := by
    rw [show (UniformSpace.Completion.toComplL :
          SmoothCcTensorHs g r s (k + 1) → TensorPouSobolevHilbert g r s (k + 1)) =
        ((↑) : SmoothCcTensorHs g r s (k + 1) →
          UniformSpace.Completion (SmoothCcTensorHs g r s (k + 1))) from
        UniformSpace.Completion.coe_toComplL]
    exact UniformSpace.Completion.denseRange_coe
  -- Bound `‖smoothInclusionHsSuccToHkCompl‖ ≤ 1` first.
  have h_to_hk_compl_norm :
      ‖smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k‖ ≤ 1 := by
    unfold smoothInclusionHsSuccToHkCompl
    -- ‖toComplL ∘ smoothInclusionHsSucc‖ ≤ ‖toComplL‖ * ‖smoothInclusionHsSucc‖
    -- ≤ 1 * 1 = 1.
    have h_toCompl :
        ‖(UniformSpace.Completion.toComplL :
          SmoothCcTensorHs g r s k →L[ℝ] TensorPouSobolevHilbert g r s k)‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
      rw [one_mul]
      change ‖((x : UniformSpace.Completion (SmoothCcTensorHs g r s k)))‖ ≤ ‖x‖
      rw [UniformSpace.Completion.norm_coe]
    have h_smooth_succ :
        ‖smoothInclusionHsSucc (I := I) (M := M) g r s k‖ ≤ 1 := by
      exact (smoothInclusionHsSuccLin (I := I) (M := M) g r s k).mkContinuous_norm_le
        zero_le_one
        (fun S => smoothInclusionHsSuccLin_norm_le (I := I) (M := M) g r s k S)
    calc ‖(UniformSpace.Completion.toComplL :
            SmoothCcTensorHs g r s k →L[ℝ] TensorPouSobolevHilbert g r s k).comp
              (smoothInclusionHsSucc (I := I) (M := M) g r s k)‖
        ≤ ‖(UniformSpace.Completion.toComplL :
              SmoothCcTensorHs g r s k →L[ℝ] TensorPouSobolevHilbert g r s k)‖ *
          ‖smoothInclusionHsSucc (I := I) (M := M) g r s k‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul h_toCompl h_smooth_succ (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  -- Bound `‖inclusionHk_succ‖ ≤ ‖smoothInclusionHsSuccToHkCompl‖` via the
  -- extension's universal property + denseness of `toComplL`.
  have h_ext_bound' :
      ‖inclusionHk_succ (I := I) (M := M) g r s k‖ ≤
        ‖smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k‖ := by
    -- Show ‖inclusionHk_succ x‖ ≤ ‖smoothInclusionHsSuccToHkCompl‖ * ‖x‖
    -- for every x in the completion, using density of `toComplL` range and
    -- the equation `inclusionHk_succ ∘ toComplL = smoothInclusionHsSuccToHkCompl`.
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
    intro x
    -- Bring x to a limit of smooth representatives via density.
    -- Use induction principle for Completion.
    refine UniformSpace.Completion.induction_on (p := fun x =>
        ‖inclusionHk_succ (I := I) (M := M) g r s k x‖ ≤
          ‖smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k‖ * ‖x‖) x
      ?_ ?_
    · -- Closed property.
      exact isClosed_le (by fun_prop) (by fun_prop)
    · -- On the dense subset: x = (w : Completion S) for some w ∈ S.
      intro w
      -- inclusionHk_succ ((w : Completion S)) = inclusionHk_succ (toComplL w)
      -- = smoothInclusionHsSuccToHkCompl w
      have h_inc_eq :
          inclusionHk_succ (I := I) (M := M) g r s k
              ((w : UniformSpace.Completion (SmoothCcTensorHs g r s (k + 1)))) =
            smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k w := by
        change inclusionHk_succ (I := I) (M := M) g r s k
            ((UniformSpace.Completion.toComplL :
              SmoothCcTensorHs g r s (k + 1) →L[ℝ]
                TensorPouSobolevHilbert g r s (k + 1)) w) =
          smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k w
        unfold inclusionHk_succ
        exact ContinuousLinearMap.extend_eq _
          (e := UniformSpace.Completion.toComplL)
          h_dense
          (by
            -- IsUniformInducing toComplL
            rw [show (UniformSpace.Completion.toComplL :
                  SmoothCcTensorHs g r s (k + 1) →
                    TensorPouSobolevHilbert g r s (k + 1)) =
                ((↑) : SmoothCcTensorHs g r s (k + 1) →
                  UniformSpace.Completion (SmoothCcTensorHs g r s (k + 1))) from
                UniformSpace.Completion.coe_toComplL]
            exact UniformSpace.Completion.isUniformInducing_coe
              (SmoothCcTensorHs g r s (k + 1))) w
      rw [h_inc_eq]
      calc ‖smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k w‖
          ≤ ‖smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k‖ * ‖w‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k‖ *
            ‖((w : UniformSpace.Completion (SmoothCcTensorHs g r s (k + 1))))‖ := by
            rw [UniformSpace.Completion.norm_coe]
  linarith

end IntrinsicSobolev
end RicciFlow
end PDE
end DifferentialGeometry

end
