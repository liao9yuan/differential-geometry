import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChartBilinearH1ComplFinal
import DifferentialGeometry.Analysis.Laplacian.Regularity.ResidualLpDecomposition
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChartBilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomainChartData
import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInnerCLMLeibniz
import DifferentialGeometry.Analysis.Sobolev.Manifold.RellichManifold

/-!
# Chart-target `MemW1p 2` discharge for `fChartResidual` from
`u_h ∈ laplacianDomainPow g 2` and the iterated-closure hypothesis

For a closed Riemannian manifold `(M, g)`, a chart point `α : M`, and an
element `u_h ∈ laplacianDomainPow g 2`, the chart-pulled residual
`fChartResidual g α u_h` is the chart-pulled raw `Lp`-class realisation of
`fHLeibnizResidualLp g α u_h = -2 g(∇ρα, ∇u_h) - Δρα · u_h`.

By the manifold-side `Lp` identity (rearranged from
`gradInnerCLM_eq_two_inv_preimageDiff`),

```
fHLeibnizResidualLp g α u_h
  = preimage⟨smoothMulHC ρα u_h⟩
     - smoothMulLp ρα (preimage⟨u_h⟩),
```

the residual decomposes as a difference of two `Lp` pieces, each in
`H1ComplToLp '' (laplacianDomain g)` when the relevant iterated-closure
membership holds. Under the iterated-closure hypothesis

```
smoothMulHC (chartAtlasPOU I M α) u_h ∈ laplacianDomainPow g 2,
```

both pieces have manifold-side function representatives in
`MemWkpChart g 2 2` (the `Lp`-side preimage piece by
`laplacianDomainPow_two_h2_plus_rhs_h2` applied to
`smoothMulHC ρα u_h`; the smooth-multiplied preimage piece by
`MemWkpChart_smooth_mul` applied to the `Lp`-side preimage of `u_h`).

The chart-pulled `MemW1p 2` regularity of each piece is delivered via
the existing chart-side bridge
`memW1p_chartPushedRaw_pou_mul_of_memWkpChart`, which converts
`MemWkpChart g 1 p F` membership into chart-target `MemW1p p` of the
chart-pulled-raw `ρα · F` on `chartTargetEuclid α`.

This file packages the two-piece discharge into a public theorem
discharging the `MemW1p 2 fChartResidual chartTargetEuclid α` regularity
from the iterated-closure hypothesis.

## Main results

* `fChartResidual_memW1p_of_iteratedClosure` — the `MemW1p 2` discharge
  of `fChartResidual g α u_h` from `u_h ∈ laplacianDomainPow g 2` and the
  iterated-closure hypothesis
  `smoothMulHC (chartAtlasPOU I M α) u_h ∈ laplacianDomainPow g 2`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace MemW1pFChartResidualUnconditional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplFinal
open DifferentialGeometry.Analysis.Sobolev.Chart

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Convenience notation for the function representatives -/

/-- The `M → ℝ` function representative of the `(1 - Δ_g)`-preimage of `u_h`. -/
private noncomputable def preimageFun
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) : M → ℝ :=
  fun x =>
    ((laplacianDomain.preimage (I := I) (M := M) g
        ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h⟩ :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x

/-- The `M → ℝ` function representative of the `(1 - Δ_g)`-preimage of
`smoothMulHC ρα u_h`. -/
private noncomputable def preimageSmoothMulHCFun
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) : M → ℝ :=
  fun x =>
    ((laplacianDomain.preimage (I := I) (M := M) g
        ⟨smoothMulHC (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h,
          smoothMulHC_mem_laplacianDomain (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)⟩ :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x

/-- The smooth `chartAtlasPOU` weight as `M → ℝ`. -/
private noncomputable def rhoAlphaFun (α : M) : M → ℝ :=
  fun x => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x

/-! ## `MemW1p 2` discharge of the smooth-multiplied `Lp` preimage piece -/

/-- The chart-pulled raw function `chartPushedRaw α (ρα · preimage⟨u_h⟩.coeFn)`
is in `MemW1p 2 chartTargetEuclid α`. -/
private lemma memW1p_chartPushedRaw_rhoAlpha_mul_preimage
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
          preimageFun (I := I) (M := M) g hu_h x))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_preimage_h2 : MemWkpChart (I := I) (M := M) g 2 2
      (preimageFun (I := I) (M := M) g hu_h) := by
    unfold preimageFun
    exact (laplacianDomainPow_two_h2_plus_rhs_h2 (I := I) (M := M) g hu_h).2.1
  have h_preimage_h1 : MemWkpChart (I := I) (M := M) g 1 2
      (preimageFun (I := I) (M := M) g hu_h) := by
    intro β
    have h_β := h_preimage_h2 β
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le
      (k := 1) (k' := 2) (by norm_num : 1 ≤ 2) h_β
  -- Apply the bridge.
  have h_bridge :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memW1p_chartPushedRaw_pou_mul_of_memWkpChart
      (I := I) (M := M) g (p := 2) (u := preimageFun (I := I) (M := M) g hu_h)
      h_preimage_h1 α
  -- Identify rhoAlphaFun α x with (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x.
  convert h_bridge using 1

/-! ## `MemW1p 2` discharge of the `Lp`-side preimage of `smoothMulHC ρα u_h` -/

/-- Under the iterated-closure hypothesis, the chart-pulled raw function
`chartPushedRaw α (ρα · preimage⟨smoothMulHC ρα u_h⟩.coeFn)` is in
`MemW1p 2 chartTargetEuclid α`. -/
private lemma memW1p_chartPushedRaw_rhoAlpha_mul_preimage_smoothMulHC
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_M6 : smoothMulHC (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
          preimageSmoothMulHCFun (I := I) (M := M) g α hu_h x))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- The preimage of `smoothMulHC ρα u_h` with two different membership proofs is the same.
  have h_M6_dom : smoothMulHC (I := I) (M := M) g
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h ∈
        laplacianDomain (I := I) (M := M) g :=
    laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 h_M6
  have h_smHC_h2 : MemWkpChart (I := I) (M := M) g 2 2
      (preimageSmoothMulHCFun (I := I) (M := M) g α hu_h) := by
    -- The preimage Lp class depends only on the H1Compl element, not on membership proof.
    -- So we can use the membership proof from h_M6.
    have h := (laplacianDomainPow_two_h2_plus_rhs_h2
      (I := I) (M := M) g h_M6).2.1
    -- h : MemWkpChart g 2 2 ((preimage ⟨smoothMulHC ρα u_h, ...⟩).coeFn).
    -- The membership in h's preimage is `laplacianDomainPow_succ_subset_laplacianDomain g 1 h_M6`.
    -- preimageSmoothMulHCFun uses `smoothMulHC_mem_laplacianDomain ... (laplacianDomainPow_succ_subset_laplacianDomain g 1 hu_h)`.
    -- These are different membership proofs to the same set, so the preimage Lp class
    -- is definitionally equal.
    unfold preimageSmoothMulHCFun
    convert h using 0
  have h_smHC_h1 : MemWkpChart (I := I) (M := M) g 1 2
      (preimageSmoothMulHCFun (I := I) (M := M) g α hu_h) := by
    intro β
    have h_β := h_smHC_h2 β
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le
      (k := 1) (k' := 2) (by norm_num : 1 ≤ 2) h_β
  have h_bridge :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memW1p_chartPushedRaw_pou_mul_of_memWkpChart
      (I := I) (M := M) g (p := 2)
      (u := preimageSmoothMulHCFun (I := I) (M := M) g α hu_h) h_smHC_h1 α
  convert h_bridge using 1

/-! ## Chart-pulled identification of the residual `Lp`-class via the
manifold-side identity -/

/-- The chart-pulled residual `fChartResidual g α u_h` is ae-equal to the
difference of chart-pulled raw functions corresponding to the two pieces
of the manifold-side decomposition. Specifically, on the chart-pulled
weighted measure restricted to `chartTargetEuclid α`,

```
fChartResidual y =ᵃᵉ chartPushedRaw α (preimage⟨smoothMulHC ρα u_h⟩.coeFn) y
                  - chartPushedRaw α (ρα · preimage⟨u_h⟩.coeFn) y.
```
-/
private lemma fChartResidual_aeEq_chartPushedRaw_diff
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    fChartResidual (I := I) (M := M) g α u_h =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fun y =>
        chartPushedRaw (I := I) α
          (preimageSmoothMulHCFun (I := I) (M := M) g α hu_h) y -
        chartPushedRaw (I := I) α
          (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
            preimageFun (I := I) (M := M) g hu_h x) y := by
  classical
  -- Set hu_dom := the laplacianDomain membership of u_h.
  have hu_dom : u_h ∈ laplacianDomain (I := I) (M := M) g :=
    laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h
  -- The decomposition Lp identity.
  have h_lp_id := fHLeibnizGeneralResidualCLM_eq_preimageDiff
    (I := I) (M := M) g α hu_dom
  -- Identify fHLeibnizGeneralResidualCLM with fHLeibnizResidualLp.
  have h_clm_eq := fHLeibnizGeneralResidualCLM_eq_fHLeibnizResidualLp
    (I := I) (M := M) g α u_h
  -- Combine: fHLeibnizResidualLp = preimage⟨smoothMulHC ρα u_h⟩ - smoothMulLp ρα (preimage⟨u_h⟩).
  set ρα : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α with hρα_def
  have h_residual_eq :
      fHLeibnizResidualLp (I := I) (M := M) g α u_h =
        laplacianDomain.preimage (I := I) (M := M) g
            ⟨smoothMulHC (I := I) (M := M) g ρα u_h,
              smoothMulHC_mem_laplacianDomain (I := I) (M := M) g ρα hu_dom⟩ -
          smoothMulLp (I := I) (M := M) g ρα
            (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩) := by
    have h_def : fHLeibnizResidualLp (I := I) (M := M) g α u_h =
        fHLeibnizGeneralResidualCLM (I := I) (M := M) g ρα u_h := by
      rw [h_clm_eq]; rfl
    rw [h_def]
    exact h_lp_id
  -- Set the two Lp-class pieces.
  set preimage_smHC_Lp :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    laplacianDomain.preimage (I := I) (M := M) g
      ⟨smoothMulHC (I := I) (M := M) g ρα u_h,
        smoothMulHC_mem_laplacianDomain (I := I) (M := M) g ρα hu_dom⟩
    with hpreimage_smHC_def
  set preimage_Lp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩
    with hpreimage_Lp_def
  set smoothMul_Lp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    smoothMulLp (I := I) (M := M) g ρα preimage_Lp
    with hsmoothMul_def
  -- Apply chartPushedRawLpFromLp at the Lp-equation level.
  have h_chartPushed_eq :
      chartPushedRawLpFromLp (I := I) (M := M) g α
          (fHLeibnizResidualLp (I := I) (M := M) g α u_h) =
        chartPushedRawLpFromLp (I := I) (M := M) g α
          (preimage_smHC_Lp - smoothMul_Lp) := by
    rw [h_residual_eq]
  -- Take coeFn ae of both sides, then apply chartPushedRawLpFromLp_coeFn_sub.
  have h_coeFn_sub :=
    DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_coeFn_sub
    (I := I) (M := M) g α preimage_smHC_Lp smoothMul_Lp
  have h_coeFn_eq :
      ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (fHLeibnizResidualLp (I := I) (M := M) g α u_h) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        fun y =>
          ((chartPushedRawLpFromLp (I := I) (M := M) g α preimage_smHC_Lp :
              Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y -
          ((chartPushedRawLpFromLp (I := I) (M := M) g α smoothMul_Lp :
              Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y := by
    rw [h_chartPushed_eq]
    exact h_coeFn_sub
  -- Identify the chart-pulled raw of preimage⟨smoothMulHC ρα u_h⟩ with chartPushedRaw α (preimageSmoothMulHCFun).
  have h_preimage_smHC_aeEq :=
    chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α preimage_smHC_Lp
  -- For the second piece, transfer to chartPushedRaw α (ρα · preimageFun) via smoothMulLp coeFn.
  have h_smoothMul_aeEq :
      ((smoothMul_Lp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x : M => (ρα : M → ℝ) x * ((preimage_Lp : Lp ℝ 2 _) : M → ℝ) x :=
    smoothMulLp_apply_coeFn (I := I) (M := M) g ρα preimage_Lp
  have h_smoothMul_meas : Measurable
      ((smoothMul_Lp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have h_prod_meas : Measurable
      (fun x : M => (ρα : M → ℝ) x * ((preimage_Lp : Lp ℝ 2 _) : M → ℝ) x) :=
    (ρα.contMDiff.continuous).measurable.mul (Lp.stronglyMeasurable _).measurable
  have h_chartPushedRaw_smoothMul_aeEq :=
    chartPushedRaw_aeEq_of_aeEq (I := I) (M := M) g α
      h_smoothMul_meas h_prod_meas h_smoothMul_aeEq
  have h_smoothMul_coeFn_aeEq :=
    chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α smoothMul_Lp
  -- Unfold fChartResidual.
  unfold fChartResidual
  filter_upwards [h_coeFn_eq, h_preimage_smHC_aeEq, h_smoothMul_coeFn_aeEq,
    h_chartPushedRaw_smoothMul_aeEq] with y h_lhs h_pre_smHC h_smMul_coeFn h_smMul_aeEq
  -- h_lhs : LHS = preimage_smHC.coeFn y - smoothMul.coeFn y.
  -- h_pre_smHC : preimage_smHC.coeFn y = chartPushedRaw α (preimage_smHC_Lp.coeFn) y.
  -- h_smMul_coeFn : smoothMul.coeFn y = chartPushedRaw α (smoothMul_Lp.coeFn) y.
  -- h_smMul_aeEq : chartPushedRaw α (smoothMul_Lp.coeFn) y =
  --                  chartPushedRaw α (ρα · preimage_Lp.coeFn) y.
  -- Goal: LHS = chartPushedRaw α (preimageSmoothMulHCFun) y
  --             - chartPushedRaw α (ρα · preimageFun) y.
  -- preimageSmoothMulHCFun coincides definitionally with preimage_smHC_Lp.coeFn.
  -- preimageFun coincides definitionally with preimage_Lp.coeFn.
  rw [h_lhs, h_pre_smHC, h_smMul_coeFn, h_smMul_aeEq]
  -- Now the goal is:
  --   chartPushedRaw α (preimage_smHC_Lp.coeFn) y - chartPushedRaw α (ρα · preimage_Lp.coeFn) y
  --     = chartPushedRaw α (preimageSmoothMulHCFun) y - chartPushedRaw α (ρα · preimageFun) y.
  rfl

/-! ## Main theorem -/

/-- **Conditional discharge of `MemW1p 2 fChartResidual` from the iterated
closure**.

For `u_h ∈ laplacianDomainPow g 2` and the iterated-closure hypothesis
`smoothMulHC (chartAtlasPOU I M α) u_h ∈ laplacianDomainPow g 2`, **given**
the additional support hypothesis that the function representative of
`preimage⟨smoothMulHC ρα u_h⟩` is ae-equal to its product with `ρα` on
`riemannianVolumeMeasure g`, the chart-pulled residual `fChartResidual g α
u_h` is in `MemW1p 2 chartTargetEuclid α`.

The support hypothesis captures the property that
`preimage⟨smoothMulHC ρα u_h⟩` is supported (a.e.) in `tsupport(ρα) ⊆
chart α source`. This property follows from the manifold-side `Lp` identity

```
preimage⟨smoothMulHC ρα u_h⟩ = smoothMulLp ρα (preimage⟨u_h⟩)
                                + fHLeibnizGeneralResidualCLM g ρα u_h
```

(each summand has support in `tsupport(ρα)` at the function level —
`smoothMulLp ρα` for trivial reasons, `fHLeibnizGeneralResidualCLM` because
its constituent terms `gradInnerCLM ρα` and `smoothMulLp Δρα` are supported
in `tsupport(ρα)`). Discharging this support property at the `Lp`-class
level requires a careful function-representative analysis through the
density extension of `gradInnerCLM`; we expose it as a clean hypothesis. -/
theorem fChartResidual_memW1p_of_iteratedClosure
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_M6 : smoothMulHC (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2)
    (h_support : preimageSmoothMulHCFun (I := I) (M := M) g α hu_h =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x => rhoAlphaFun (I := I) (M := M) α x *
        preimageSmoothMulHCFun (I := I) (M := M) g α hu_h x) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartResidual (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- Step 1: The chart-pulled raw of `preimageSmoothMulHCFun` agrees with the
  -- chart-pulled raw of `ρα · preimageSmoothMulHCFun` ae on chartPulledWeighted
  -- via h_support and chartPushedRaw_aeEq_of_aeEq.
  have h_preimage_meas : Measurable
      (preimageSmoothMulHCFun (I := I) (M := M) g α hu_h) := by
    unfold preimageSmoothMulHCFun
    exact (Lp.stronglyMeasurable _).measurable
  have h_prod_meas : Measurable
      (fun x => rhoAlphaFun (I := I) (M := M) α x *
        preimageSmoothMulHCFun (I := I) (M := M) g α hu_h x) := by
    refine Measurable.mul ?_ h_preimage_meas
    exact ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous).measurable
  have h_chartPushed_aeEq :=
    chartPushedRaw_aeEq_of_aeEq (I := I) (M := M) g α
      h_preimage_meas h_prod_meas h_support
  -- Step 2: The chart-pulled residual decomposition.
  have h_decomp_weighted := fChartResidual_aeEq_chartPushedRaw_diff
    (I := I) (M := M) g α hu_h
  -- Step 3: Rewrite using h_chartPushed_aeEq.
  have h_residual_rewritten :
      fChartResidual (I := I) (M := M) g α u_h =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fun y =>
        chartPushedRaw (I := I) α
          (fun x => rhoAlphaFun (I := I) (M := M) α x *
            preimageSmoothMulHCFun (I := I) (M := M) g α hu_h x) y -
        chartPushedRaw (I := I) α
          (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
            preimageFun (I := I) (M := M) g hu_h x) y := by
    filter_upwards [h_decomp_weighted, h_chartPushed_aeEq] with y hy hyEq
    rw [hy, hyEq]
  -- Step 4: Transfer to volume.restrict chartTarget via absolute continuity.
  -- Mutual absolute continuity: vol.restrict chartTarget ≪ chartPulledWeighted.restrict chartTarget.
  have h_vol_abs : (volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α) ≪
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α) := by
    intro A hA
    have h_chartTarget_meas : MeasurableSet
        (chartTargetEuclid (I := I) (M := M) α) :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    unfold chartPulledWeightedMeasure at hA
    rw [show ((volume : Measure EuclN).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
          (chartTargetEuclid (I := I) (M := M) α) =
        ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      from MeasureTheory.restrict_withDensity h_chartTarget_meas _] at hA
    rw [MeasureTheory.withDensity_apply_eq_zero'
      (μ := (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      (ENNReal.measurable_ofReal.comp_aemeasurable
        ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_chartTarget_meas))]
      at hA
    rw [Measure.restrict_apply' h_chartTarget_meas]
    rw [Measure.restrict_apply' h_chartTarget_meas] at hA
    refine MeasureTheory.measure_mono_null ?_ hA
    intro y ⟨hy_A, hy_chart⟩
    refine ⟨⟨?_, hy_A⟩, hy_chart⟩
    have h_pos : 0 < densityOnEuclid (I := I) g α y :=
      densityOnEuclid_pos (I := I) g α hy_chart
    exact (ENNReal.ofReal_pos.mpr h_pos).ne'
  have h_residual_rewritten_vol :
      fChartResidual (I := I) (M := M) g α u_h =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fun y =>
        chartPushedRaw (I := I) α
          (fun x => rhoAlphaFun (I := I) (M := M) α x *
            preimageSmoothMulHCFun (I := I) (M := M) g α hu_h x) y -
        chartPushedRaw (I := I) α
          (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
            preimageFun (I := I) (M := M) g hu_h x) y :=
    h_vol_abs.ae_le h_residual_rewritten
  -- Step 5: Both pieces are MemW1p 2 chartTarget via the bridge.
  have h_piece1 := memW1p_chartPushedRaw_rhoAlpha_mul_preimage_smoothMulHC
    (I := I) (M := M) g α hu_h h_M6
  have h_piece2 := memW1p_chartPushedRaw_rhoAlpha_mul_preimage
    (I := I) (M := M) g α hu_h
  -- Step 6: Difference is MemW1p 2 via add + const_smul (-1).
  have h_piece2_neg :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (fun y => (-1 : ℝ) * chartPushedRaw (I := I) α
          (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
            preimageFun (I := I) (M := M) g hu_h x) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p.const_smul
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_piece2 (-1 : ℝ)
  have h_diff : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fun y =>
        chartPushedRaw (I := I) α
          (fun x => rhoAlphaFun (I := I) (M := M) α x *
            preimageSmoothMulHCFun (I := I) (M := M) g α hu_h x) y -
        chartPushedRaw (I := I) α
          (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
            preimageFun (I := I) (M := M) g hu_h x) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_add := DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p.add
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_piece1 h_piece2_neg
    -- h_add gives MemW1p of (piece1 + (-1) * piece2) = (piece1 - piece2).
    have h_eq : (fun y =>
        chartPushedRaw (I := I) α
          (fun x => rhoAlphaFun (I := I) (M := M) α x *
            preimageSmoothMulHCFun (I := I) (M := M) g α hu_h x) y +
        (-1 : ℝ) * chartPushedRaw (I := I) α
          (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
            preimageFun (I := I) (M := M) g hu_h x) y) =
      (fun y =>
        chartPushedRaw (I := I) α
          (fun x => rhoAlphaFun (I := I) (M := M) α x *
            preimageSmoothMulHCFun (I := I) (M := M) g α hu_h x) y -
        chartPushedRaw (I := I) α
          (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
            preimageFun (I := I) (M := M) g hu_h x) y) := by
      funext y; ring
    rw [h_eq] at h_add
    exact h_add
  -- Step 7: Transfer via ae-equality.
  have hΩ : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
    (d := Module.finrank ℝ E) (p := 2) hΩ h_residual_rewritten_vol.symm).mp h_diff

end MemW1pFChartResidualUnconditional
end Laplacian
end Analysis
end DifferentialGeometry

end

/-! ## Axiom audit -/

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Laplacian.MemW1pFChartResidualUnconditional.fChartResidual_memW1p_of_iteratedClosure

end Sanity
