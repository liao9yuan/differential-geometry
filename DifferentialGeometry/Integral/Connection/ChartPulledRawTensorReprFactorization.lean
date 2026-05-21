import DifferentialGeometry.Integral.Connection.RawTensorConnLapNormSqChartPulledReprBound
import DifferentialGeometry.Integral.Connection.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Integral.Connection.TensorRSChartFiberForwardOpNorm
import DifferentialGeometry.Integral.Connection.TensorRSChartReprNormBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Linear chart-pulled-representation bound for the raw tensor connection
Laplacian by orders 0, 1, 2 of the iterated Fréchet derivatives of the
chart-pulled representation of `T`

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, ranks
`r, s : ℕ`, and a smooth compactly supported `(r, s)`-tensor section `T`, this
file ships the unsquared (linear) pointwise bound

```
‖tensorRSChartE_section_repr r s α
    (fun y => (rawTensorConnLapSmooth g r s T).toSection y) b‖ ≤
  K * (∑ j : Fin 3,
        ‖iteratedFDeriv ℝ j.val
          ((tensorRSChartE_section_repr r s α (fun y => T.toSection y)) ∘
            (extChartAt I α).symm) (extChartAt I α b)‖)
```

valid for every `b` in the intersection of the chart-`α` partition-of-unity
tsupport and the chart-`α` Levi-Civita good set. The constant `K` depends on
`g`, the chart at `α`, the chart-atlas locality hypotheses, and the ranks
`r`, `s`; it is independent of `T` and `b`.

## Strategy

The previously established squared bound

```
‖rawTensorConnLap g r s (fun y => T.toSection y) b‖^2 ≤
  K_sq * (V^2 + F^2 + I^2)
```

where `V, F, I` are the chart-pulled representation norms at orders `0, 1, 2`
respectively, can be turned into the unsquared

```
‖rawTensorConnLap g r s (fun y => T.toSection y) b‖ ≤ √K_sq * (V + F + I)
```

via the bound `V^2 + F^2 + I^2 ≤ (V + F + I)^2` valid for non-negative `V, F,
I`. The forward fibre-norm bound

```
‖tensorRSChartE_section_repr r s α (raw T) b‖ ≤ C_fwd * ‖rawTensorConnLap g r s
  (fun y => T.toSection y) b‖
```

valid on the partition-of-unity tsupport (a compact subset of the chart-`α`
source) then yields the desired linear bound on the chart-pulled representation.
Finally, `V = ‖iteratedFDeriv ℝ 0 ...‖` and `F = ‖iteratedFDeriv ℝ 1 ...‖` via
`norm_iteratedFDeriv_zero` and `norm_iteratedFDeriv_one`; on the good set
`(extChartAt I α).symm (extChartAt I α b) = b`, so the order-zero value agrees
with the chart-pulled representation at `b`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Arithmetic step: `V^2 + F^2 + I^2 ≤ (V + F + I)^2` for non-negative `V, F, I` -/

private lemma sum_sq_le_sq_sum_of_nonneg (V F I2 : ℝ)
    (hV : 0 ≤ V) (hF : 0 ≤ F) (hI2 : 0 ≤ I2) :
    V ^ 2 + F ^ 2 + I2 ^ 2 ≤ (V + F + I2) ^ 2 := by
  nlinarith [mul_nonneg hV hF, mul_nonneg hV hI2, mul_nonneg hF hI2]

/-! ## Sqrt step: take the square root of the chart-pulled representation
squared bound to obtain a linear bound on `‖rawTensorConnLap (T) b‖` -/

private lemma rawTensorConnLap_norm_le_chartPulledRepr_data_on_pou_tsupport_goodSet
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖rawTensorConnLap (I := I) g r s
            (fun y : M => T.toSection y) b‖ ≤
          K * (‖tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) b‖ +
              ‖fderiv ℝ
                 (tensorRSChartE_section_repr (I := I) r s α
                    (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                 (extChartAt I α b)‖ +
              ‖iteratedFDeriv ℝ 2
                 (tensorRSChartE_section_repr (I := I) r s α
                    (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                 (extChartAt I α b)‖) := by
  classical
  -- Extract the squared headline.
  obtain ⟨K_sq, hK_sq_nn, hK_sq_bound⟩ :=
    rawTensorConnLap_norm_sq_le_chartPulledRepr_data_on_pou_tsupport_goodSet
      (I := I) (M := M) h_atlas h_atlas_strong g r s α
  -- Set K_lin := √K_sq.
  set K_lin : ℝ := Real.sqrt K_sq with hK_lin_def
  have hK_lin_nn : 0 ≤ K_lin := Real.sqrt_nonneg _
  refine ⟨K_lin, hK_lin_nn, ?_⟩
  intro T b hb
  set V : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) b‖ with hV_def
  set Fnorm : ℝ := ‖fderiv ℝ
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖ with hFnorm_def
  set I2norm : ℝ := ‖iteratedFDeriv ℝ 2
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖ with hI2norm_def
  have hV_nn : 0 ≤ V := norm_nonneg _
  have hF_nn : 0 ≤ Fnorm := norm_nonneg _
  have hI2_nn : 0 ≤ I2norm := norm_nonneg _
  have hVFI2_nn : 0 ≤ V + Fnorm + I2norm := by linarith
  -- Apply the squared bound.
  have h_sq := hK_sq_bound T hb
  -- Re-write into our notation.
  change ‖rawTensorConnLap (I := I) g r s
        (fun y : M => T.toSection y) b‖ ^ 2 ≤
      K_sq * (V ^ 2 + Fnorm ^ 2 + I2norm ^ 2) at h_sq
  -- Strengthen the inner sum: V^2 + F^2 + I^2 ≤ (V + F + I)^2.
  have h_inner_le : V ^ 2 + Fnorm ^ 2 + I2norm ^ 2 ≤ (V + Fnorm + I2norm) ^ 2 :=
    sum_sq_le_sq_sum_of_nonneg V Fnorm I2norm hV_nn hF_nn hI2_nn
  have h_step : K_sq * (V ^ 2 + Fnorm ^ 2 + I2norm ^ 2) ≤
      K_sq * (V + Fnorm + I2norm) ^ 2 :=
    mul_le_mul_of_nonneg_left h_inner_le hK_sq_nn
  have h_sq2 : ‖rawTensorConnLap (I := I) g r s
      (fun y : M => T.toSection y) b‖ ^ 2 ≤ K_sq * (V + Fnorm + I2norm) ^ 2 :=
    le_trans h_sq h_step
  -- K_sq * (V + F + I)^2 = (√K_sq * (V + F + I))^2.
  have h_rhs_sq : K_sq * (V + Fnorm + I2norm) ^ 2 =
      (K_lin * (V + Fnorm + I2norm)) ^ 2 := by
    rw [hK_lin_def, mul_pow, Real.sq_sqrt hK_sq_nn]
  rw [h_rhs_sq] at h_sq2
  -- Take square roots: ‖raw T b‖ ≤ K_lin * (V + F + I).
  have h_raw_nn : 0 ≤ ‖rawTensorConnLap (I := I) g r s
      (fun y : M => T.toSection y) b‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ K_lin * (V + Fnorm + I2norm) :=
    mul_nonneg hK_lin_nn hVFI2_nn
  -- abs_le_of_sq_le_sq : a^2 ≤ b^2 ∧ 0 ≤ b → |a| ≤ b.
  have h_abs := abs_le_of_sq_le_sq (a := ‖rawTensorConnLap (I := I) g r s
      (fun y : M => T.toSection y) b‖) (b := K_lin * (V + Fnorm + I2norm))
    h_sq2 h_rhs_nn
  rw [abs_of_nonneg h_raw_nn] at h_abs
  exact h_abs

/-! ## Forward fibre-norm bound on `tsupport (chartAtlasPOU I M α)` -/

private lemma tensorRSChartE_section_repr_norm_le_on_pou_tsupport
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Π b : M, TensorRSSpace r s I b),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖tensorRSChartE_section_repr (I := I) r s α S b‖ ≤ C * ‖S b‖ := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    tensorRSChartFiberToModel_opNorm_isBounded_on_compact
      (I := I) (M := M) (h_atlas := h_atlas) (r := r) (s := s) (α := α)
      (hK := hK_compact) (hKsub := hK_sub)
  refine ⟨C, hC_pos, ?_⟩
  intro S b hb
  have h := hC_bound b hb (S b)
  change ‖tensorRSChartE_section_repr (I := I) r s α S b‖ ≤ C * ‖S b‖
  exact h

/-! ## Iterated-Fréchet-derivative identifications: V = ‖iteratedFDeriv 0‖,
F = ‖iteratedFDeriv 1‖ -/

/-- The chart-pulled representation `V` at `b ∈` good set equals the order-0
iterated Fréchet-derivative norm of `T_repr ∘ symm` at `extChartAt I α b`. -/
private lemma V_eq_iteratedFDeriv_zero_norm
    (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ‖tensorRSChartE_section_repr (I := I) r s α S b‖ =
      ‖iteratedFDeriv ℝ 0
        ((tensorRSChartE_section_repr (I := I) r s α S) ∘
            (extChartAt I α).symm)
        (extChartAt I α b)‖ := by
  have hb_chart_src : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good
  have hb_extsrc : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hb_chart_src
  have hsymm_eq : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_extsrc
  rw [norm_iteratedFDeriv_zero]
  change ‖tensorRSChartE_section_repr (I := I) r s α S b‖ =
    ‖tensorRSChartE_section_repr (I := I) r s α S
      ((extChartAt I α).symm (extChartAt I α b))‖
  rw [hsymm_eq]

/-- The chart-pulled `fderiv ℝ` norm of `T_repr ∘ symm` at the chart point
equals the order-1 iterated Fréchet-derivative norm there. -/
private lemma F_eq_iteratedFDeriv_one_norm
    (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b) (b : M) :
    ‖fderiv ℝ
        ((tensorRSChartE_section_repr (I := I) r s α S) ∘
            (extChartAt I α).symm)
        (extChartAt I α b)‖ =
      ‖iteratedFDeriv ℝ 1
        ((tensorRSChartE_section_repr (I := I) r s α S) ∘
            (extChartAt I α).symm)
        (extChartAt I α b)‖ := by
  rw [norm_iteratedFDeriv_one]

/-! ## V + F + I2 reformulated as `∑ j : Fin 3, ‖iteratedFDeriv ℝ j.val ...‖` -/

private lemma sum_VFI2_eq_finSum
    (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ‖tensorRSChartE_section_repr (I := I) r s α S b‖ +
      ‖fderiv ℝ
        ((tensorRSChartE_section_repr (I := I) r s α S) ∘
            (extChartAt I α).symm)
        (extChartAt I α b)‖ +
      ‖iteratedFDeriv ℝ 2
        ((tensorRSChartE_section_repr (I := I) r s α S) ∘
            (extChartAt I α).symm)
        (extChartAt I α b)‖ =
      ∑ j : Fin 3,
        ‖iteratedFDeriv ℝ j.val
          ((tensorRSChartE_section_repr (I := I) r s α S) ∘
              (extChartAt I α).symm)
          (extChartAt I α b)‖ := by
  rw [V_eq_iteratedFDeriv_zero_norm (I := I) (M := M) r s α S (b := b) hb_good]
  rw [F_eq_iteratedFDeriv_one_norm (I := I) (M := M) r s α S b]
  -- Sum over Fin 3 = a_0 + a_1 + a_2.
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]

/-! ## Headline -/

/-- **Linear (unsquared) chart-pulled-representation bound for the bundled raw
tensor connection Laplacian by orders 0, 1, 2 of the iterated Fréchet
derivatives of the chart-pulled representation of `T`.**

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, and ranks
`r, s : ℕ`, there is a constant `K ≥ 0` such that for every smooth compactly
supported `(r, s)`-tensor section `T` and every `b` in the intersection of the
chart-`α` partition-of-unity tsupport with the chart-`α` Levi-Civita good set,

```
‖tensorRSChartE_section_repr r s α
    (fun y => (rawTensorConnLapSmooth g r s T).toSection y) b‖ ≤
  K * (∑ j : Fin 3,
        ‖iteratedFDeriv ℝ j.val
          ((tensorRSChartE_section_repr r s α (fun y => T.toSection y)) ∘
            (extChartAt I α).symm) (extChartAt I α b)‖)
```

The constant `K` depends on `g`, the chart at `α`, the chart-atlas locality
hypotheses, and the ranks `r`, `s`; it is independent of `T` and `b`. -/
theorem rawTensorConnLap_chartPulledRepr_norm_le_sum_iteratedFDeriv_repr
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => (rawTensorConnLapSmooth (I := I) g r s T).toSection y)
            b‖ ≤
          K *
            (∑ j : Fin 3,
              ‖iteratedFDeriv ℝ j.val
                  ((tensorRSChartE_section_repr (I := I) r s α
                      (fun y : M => T.toSection y)) ∘ (extChartAt I α).symm)
                  (extChartAt I α b)‖) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  -- Step 1: linear (unsquared) bound on ‖raw T b‖.
  obtain ⟨K_lin, hK_lin_nn, hK_lin_bound⟩ :=
    rawTensorConnLap_norm_le_chartPulledRepr_data_on_pou_tsupport_goodSet
      (I := I) (M := M) h_atlas h_atlas_strong g r s α
  -- Step 2: forward fibre-norm bound on POU tsupport.
  obtain ⟨C_fwd, hCfwd_pos, hCfwd_bound⟩ :=
    tensorRSChartE_section_repr_norm_le_on_pou_tsupport
      (I := I) (M := M) h_atlas r s α
  have hCfwd_nn : 0 ≤ C_fwd := le_of_lt hCfwd_pos
  -- Combine into final constant K := C_fwd · K_lin.
  set K_final : ℝ := C_fwd * K_lin with hK_final_def
  have hK_final_nn : 0 ≤ K_final := mul_nonneg hCfwd_nn hK_lin_nn
  refine ⟨K_final, hK_final_nn, ?_⟩
  intro T b hb
  obtain ⟨hb_pou, hb_good⟩ := hb
  -- Notation for V, F, I2.
  set V : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) b‖ with hV_def
  set Fnorm : ℝ := ‖fderiv ℝ
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖ with hFnorm_def
  set I2norm : ℝ := ‖iteratedFDeriv ℝ 2
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖ with hI2norm_def
  have hV_nn : 0 ≤ V := norm_nonneg _
  have hF_nn : 0 ≤ Fnorm := norm_nonneg _
  have hI2_nn : 0 ≤ I2norm := norm_nonneg _
  have hVFI2_nn : 0 ≤ V + Fnorm + I2norm := by linarith
  -- Step 1 result: ‖raw T b‖ ≤ K_lin · (V + F + I2).
  have h_raw_le := hK_lin_bound T ⟨hb_pou, hb_good⟩
  change ‖rawTensorConnLap (I := I) g r s
      (fun y : M => T.toSection y) b‖ ≤
    K_lin * (V + Fnorm + I2norm) at h_raw_le
  -- Step 2 result: ‖tensorRSChartE_section_repr (raw T) b‖ ≤ C_fwd · ‖raw T b‖.
  have h_fwd_le := hCfwd_bound
    (fun y : M => (rawTensorConnLapSmooth (I := I) g r s T).toSection y) hb_pou
  -- Use rawTensorConnLapSmooth_toSection_apply to identify the section value.
  have h_section_eq : (fun y : M =>
        (rawTensorConnLapSmooth (I := I) g r s T).toSection y) b =
      rawTensorConnLap (I := I) g r s
        (fun y : M => T.toSection y) b := by
    exact rawTensorConnLapSmooth_toSection_apply (I := I) g r s T b
  rw [h_section_eq] at h_fwd_le
  -- Chain: ‖repr (raw T) b‖ ≤ C_fwd · ‖raw T b‖ ≤ C_fwd · K_lin · (V + F + I2)
  --       = K_final · (V + F + I2).
  have h_chain_le :
      ‖tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => (rawTensorConnLapSmooth (I := I) g r s T).toSection y) b‖
        ≤ K_final * (V + Fnorm + I2norm) := by
    have h_a :
        C_fwd * ‖rawTensorConnLap (I := I) g r s
            (fun y : M => T.toSection y) b‖ ≤
          C_fwd * (K_lin * (V + Fnorm + I2norm)) :=
      mul_le_mul_of_nonneg_left h_raw_le hCfwd_nn
    have h_b :
        C_fwd * (K_lin * (V + Fnorm + I2norm)) =
          K_final * (V + Fnorm + I2norm) := by
      rw [hK_final_def]; ring
    linarith
  -- Convert (V + F + I2) into the Fin-3 sum.
  have h_sum_eq := sum_VFI2_eq_finSum (I := I) (M := M) r s α
    (S := fun y : M => T.toSection y) (b := b) hb_good
  change V + Fnorm + I2norm =
    ∑ j : Fin 3,
      ‖iteratedFDeriv ℝ j.val
        ((tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y)) ∘ (extChartAt I α).symm)
        (extChartAt I α b)‖ at h_sum_eq
  rw [h_sum_eq] at h_chain_le
  exact h_chain_le

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.rawTensorConnLap_chartPulledRepr_norm_le_sum_iteratedFDeriv_repr
end Sanity
