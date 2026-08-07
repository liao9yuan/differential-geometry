import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorr0TraceRadiusFree
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Lowered

/-!
# Class-first finite-window bound for the DLa coefficient

This module keeps the fixed-background connection tower abstract.  A
nonnegative cap for its first three jets is selected before any metric varies;
all coefficient constants are then selected before the metrics.  The final
producer exposes only the two output orders consumed by the dimension-three
`H1` grid integrator.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DLaUniformInternal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedVariables false in
private theorem kernel_grid_of_conn
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (F : ℕ → ℝ) (hF : ∀ j, 0 ≤ F j) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₀ g_bg : SmoothRiemannianMetric I M),
        (∀ j, j < 3 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 1 2 j
                (connDiffSection (I := I) g_bg g₀)).toSection x) ≤ F j) →
        ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
          (htie : ∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
          {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
          (hbound : gFibreOpBound (I := I) (M := M) g₀
            (ccTensorBilinSymm (I := I) g₀ T) δ)
          (i : ℕ), i < 2 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 3 i
                (dlaKernel (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
            C i * dLaGridWin
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := connDiff_grid_unif (I := I) (M := M) hδ₀
  let CQ1 : ℕ → ℝ := fun j => appCcGdiag (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * CA i' *
      ∑ l ∈ Finset.range (j + 1 - i'), CA l * dlaPairCount (i' + 2) (l + 2)
  let CQ2 : ℕ → ℝ := fun j => appCcGdiag (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * F i' *
      ∑ l ∈ Finset.range (j + 1 - i'), CA l * dlaPairCount (i' + 2) (l + 2)
  let CQ3 : ℕ → ℝ := fun j => appCcGdiag (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * CA i' *
      ∑ l ∈ Finset.range (j + 1 - i'), F l * dlaPairCount (i' + 2) (l + 2)
  have hCQ1_nn : ∀ j, 0 ≤ CQ1 j := by
    intro j
    exact mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (Finset.sum_nonneg fun i' _ => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (hCA_nn i'))
        (Finset.sum_nonneg fun l _ => mul_nonneg (hCA_nn l) (pair_nonneg _ _)))
  have hCQ2_nn : ∀ j, 0 ≤ CQ2 j := by
    intro j
    exact mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (Finset.sum_nonneg fun i' _ => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (hF i'))
        (Finset.sum_nonneg fun l _ => mul_nonneg (hCA_nn l) (pair_nonneg _ _)))
  have hCQ3_nn : ∀ j, 0 ≤ CQ3 j := by
    intro j
    exact mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (Finset.sum_nonneg fun i' _ => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (hCA_nn i'))
        (Finset.sum_nonneg fun l _ => mul_nonneg (hF l) (pair_nonneg _ _)))
  refine ⟨fun i =>
      2 * (2 * (2 * (2 * (2 * (2 * (2 * CA (i + 1) + 2 * F (i + 1)) + 2 * CQ1 i)
        + 2 * CQ2 i) + 2 * CQ1 i) + 2 * CQ3 i) + 2 * CQ1 i) + 2 * CQ3 i,
    fun i => by
      have := hCA_nn (i + 1)
      have := hF (i + 1)
      have := hCQ1_nn i
      have := hCQ2_nn i
      have := hCQ3_nn i
      positivity, ?_⟩
  intro g₀ g_bg hfix g₁ T htie δ hδ_le hδ_nonneg hbound i hi x
  let b : ℕ → ℝ := fun l =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)
  have hb : ∀ l, 0 ≤ b l := fun l =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  let W : ℝ := dLaGridWin b (i + 3)
  have hW_ge1 : 1 ≤ W := grid_one_le b hb (by omega)
  have harm : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 1 2 i'
          (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      CA i' * dLaGridWin b (i' + 2) := by
    intro i' _
    simpa only [dLaGridWin, b] using
      hCA g₀ g₁ T htie hδ_le hδ_nonneg hbound i' x
  have hfixWin : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 1 2 i'
          (connDiffSection (I := I) g_bg g₀)).toSection x) ≤
      F i' * dLaGridWin b (i' + 2) := by
    intro i' hi'
    refine (hfix i' (by omega) x).trans ?_
    have hone : (1 : ℝ) ≤ dLaGridWin b (i' + 2) := grid_one_le b hb (by omega)
    nlinarith [hF i']
  have hQ1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dlaQuad (I := I) (M := M) g₀ g₁ g₁)).toSection x) ≤ CQ1 i * W :=
    quad_tower (I := I) (M := M) g₀ g₁ g₁ i x b hb
      CA CA hCA_nn hCA_nn harm harm
  have hQ2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dlaQuad (I := I) (M := M) g₀ g_bg g₁)).toSection x) ≤ CQ2 i * W :=
    quad_tower (I := I) (M := M) g₀ g_bg g₁ i x b hb
      F CA hF hCA_nn hfixWin harm
  have hQ3 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dlaQuad (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ CQ3 i * W :=
    quad_tower (I := I) (M := M) g₀ g₁ g_bg i x b hb
      CA F hCA_nn hF harm hfixWin
  have hrs_eq : ∀ (σ : Equiv.Perm (Fin 3)) (A : SmoothCcTensor g₀ 1 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ A)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i A).toSection x) := by
    intro σ A
    exact rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr
      (I := I) (M := M) g₀ 1 3 σ A
      (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ A)
      (fun y d => by rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x
  have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2
          (connDiffSection (I := I) g₁ g₀))).toSection x) ≤ CA (i + 1) * W := by
    rw [rfns_iteratedCovGrad_covGrad_comm_rs
      (I := I) (M := M) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀) x]
    simpa only [W, dLaGridWin, b] using
      hCA g₀ g₁ T htie hδ_le hδ_nonneg hbound (i + 1) x
  have hA2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2
          (connDiffSection (I := I) g_bg g₀))).toSection x) ≤ F (i + 1) * W := by
    rw [rfns_iteratedCovGrad_covGrad_comm_rs
      (I := I) (M := M) g₀ 1 2 i (connDiffSection (I := I) g_bg g₀) x]
    refine (hfix (i + 1) (by omega) x).trans ?_
    nlinarith [hF (i + 1), hW_ge1]
  let A1 := covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)
  let A2 := covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀)
  let Q11 := dlaQuad (I := I) (M := M) g₀ g₁ g₁
  let Qbg1 := dlaQuad (I := I) (M := M) g₀ g_bg g₁
  let Q1bg := dlaQuad (I := I) (M := M) g₀ g₁ g_bg
  let P1 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2) Q11
  let P2 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2) Q1bg
  let P3 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) Q11
  let P4 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) Q1bg
  have hP1_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P1).toSection x) ≤ CQ1 i * W :=
    le_of_eq_of_le (hrs_eq (Equiv.swap (0 : Fin 3) 2) Q11) hQ1
  have hP2_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P2).toSection x) ≤ CQ3 i * W :=
    le_of_eq_of_le (hrs_eq (Equiv.swap (0 : Fin 3) 2) Q1bg) hQ3
  have hP3_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P3).toSection x) ≤ CQ1 i * W :=
    le_of_eq_of_le (hrs_eq (finRotate 3) Q11) hQ1
  have hP4_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P4).toSection x) ≤ CQ3 i * W :=
    le_of_eq_of_le (hrs_eq (finRotate 3) Q1bg) hQ3
  have t1 := rfns_sub (I := I) (M := M) g₀ 1 3 i A1 A2 x
  have t2 := rfns_add (I := I) (M := M) g₀ 1 3 i (A1 - A2) Q11 x
  have t3 := rfns_sub (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11) Qbg1 x
  have t4 := rfns_sub (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11 - Qbg1) P1 x
  have t5 := rfns_add (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11 - Qbg1 - P1) P2 x
  have t6 := rfns_sub (I := I) (M := M) g₀ 1 3 i
    (A1 - A2 + Q11 - Qbg1 - P1 + P2) P3 x
  have t7 := rfns_add (I := I) (M := M) g₀ 1 3 i
    (A1 - A2 + Q11 - Qbg1 - P1 + P2 - P3) P4 x
  have hKK : dlaKernel (I := I) (M := M) g₀ g₁ g_bg =
      A1 - A2 + Q11 - Qbg1 - P1 + P2 - P3 + P4 := rfl
  rw [hKK]
  linarith [t1, t2, t3, t4, t5, t6, t7, hA1, hA2, hQ1, hQ2, hQ3,
    hP1_le, hP2_le, hP3_le, hP4_le]

set_option linter.unusedVariables false in
private theorem lowered_grid_of_conn
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (F : ℕ → ℝ) (hF : ∀ j, 0 ≤ F j) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₀ g_bg : SmoothRiemannianMetric I M),
        (∀ j, j < 3 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 1 2 j
                (connDiffSection (I := I) g_bg g₀)).toSection x) ≤ F j) →
        ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
          (htie : ∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
          {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
          (hbound : gFibreOpBound (I := I) (M := M) g₀
            (ccTensorBilinSymm (I := I) g₀ T) δ)
          (i : ℕ), i < 2 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i
                (dlaLowered (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
            C i * dLaGridWin
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  obtain ⟨C, hC_nn, hC⟩ := kernel_grid_of_conn (I := I) (M := M) hδ₀ F hF
  refine ⟨C, hC_nn, ?_⟩
  intro g₀ g_bg hfix g₁ T htie δ hδ_le hδ_nonneg hbound i hi x
  have hbridge : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dlaLowered (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (dlaKernel (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
    have h := rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq
      (I := I) (M := M) g₀ 2
      (dlaLowered (I := I) (M := M) g₀ g₁ g_bg) i x
    rw [lower_raise (I := I) (M := M) g₀ g₁ g_bg] at h
    exact h.symm
  rw [hbridge]
  exact hC g₀ g_bg hfix g₁ T htie hδ_le hδ_nonneg hbound i hi x

set_option linter.unusedVariables false in
private theorem sym_grid_of_conn
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (F : ℕ → ℝ) (hF : ∀ j, 0 ≤ F j) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₀ g_bg : SmoothRiemannianMetric I M),
        (∀ j, j < 3 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 1 2 j
                (connDiffSection (I := I) g_bg g₀)).toSection x) ≤ F j) →
        ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
          (htie : ∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
          {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
          (hbound : gFibreOpBound (I := I) (M := M) g₀
            (ccTensorBilinSymm (I := I) g₀ T) δ)
          (i : ℕ), i < 2 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i
                (dlaSym (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
            C i * dLaGridWin
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  classical
  obtain ⟨CL, hCL_nn, hCL⟩ := lowered_grid_of_conn (I := I) (M := M) hδ₀ F hF
  let fr : ℝ := Module.finrank ℝ E
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  let CP : ℕ → ℝ := fun _ => fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1)
  have hCP_nn : ∀ i', 0 ≤ CP i' := by
    intro i'
    dsimp only [CP]
    positivity
  let CLT : ℕ → ℝ := fun i => appCcGdiag (E := E) i * ∑ i' ∈ Finset.range (i + 1),
    CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
      CL l * dlaPairCount (i' + 1) (l + 3)
  have hCLT_nn : ∀ i, 0 ≤ CLT i := by
    intro i
    exact mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hCP_nn i')
        (Finset.sum_nonneg fun l _ => mul_nonneg (hCL_nn l) (pair_nonneg _ _)))
  refine ⟨fun i => 4 * (2 * CL i + 2 * CLT i),
    fun i => by
      have := hCL_nn i
      have := hCLT_nn i
      positivity, ?_⟩
  intro g₀ g_bg hfix g₁ T htie δ hδ_le hδ_nonneg hbound i hi x
  let b : ℕ → ℝ := fun l =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)
  have hb : ∀ l, 0 ≤ b l := fun l =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  let W : ℝ := dLaGridWin b (i + 3)
  have hPfac : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
        ((iteratedCovGrad (I := I) g₀ 4 4 i'
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (dlaPerturb (I := I) (M := M) g₀ T))).toSection x) ≤
      CP i' * dLaGridWin b (i' + 1) := by
    intro i' _
    refine (insert_rfns (I := I) (M := M) g₀ T i' x).trans ?_
    have hfr3_nn : (0 : ℝ) ≤ fr ^ 3 := by positivity
    match i' with
    | 0 =>
        have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (symmS (I := I) (M := M) g₀ T)).toSection x) ≤ fr ^ 2 * δ ^ 2 := by
          rw [iteratedCovGrad_zero]
          exact symmC0_rfns_le (I := I) (M := M) g₀ T hδ_nonneg hbound x
        have hδsq : δ ^ 2 ≤ δ₀ ^ 2 := by nlinarith [hδ_nonneg, hδ_le]
        have hwin1 : (1 : ℝ) ≤ dLaGridWin b (0 + 1) := grid_one_le b hb (by omega)
        have hle1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (symmS (I := I) (M := M) g₀ T)).toSection x) ≤ fr ^ 2 * δ₀ ^ 2 :=
          h0.trans (mul_le_mul_of_nonneg_left hδsq (by positivity))
        calc
          fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
                ((iteratedCovGrad (I := I) g₀ 0 2 0
                  (symmS (I := I) (M := M) g₀ T)).toSection x)
              ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2) := mul_le_mul_of_nonneg_left hle1 hfr3_nn
          _ ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) := by
                refine mul_le_mul_of_nonneg_left ?_ hfr3_nn
                linarith
          _ ≤ (fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1)) * dLaGridWin b (0 + 1) := by
                refine le_mul_of_one_le_right ?_ hwin1
                positivity
          _ = CP 0 * dLaGridWin b (0 + 1) := rfl
    | (m + 1) =>
        have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (m + 1)
              (symmS (I := I) (M := M) g₀ T)).toSection x) ≤ b (m + 1) :=
          symm_rfns (I := I) (M := M) g₀ T (m + 1) x
        have h2 : b (m + 1) ≤ Combinatorics.antidiagonalTupleGrid b (m + 1) :=
          grid_single_le b hb (m + 1) (by omega)
        have h3 : Combinatorics.antidiagonalTupleGrid b (m + 1) ≤
            dLaGridWin b ((m + 1) + 1) := grid_term_le b hb (by omega)
        have hfac1 : (1 : ℝ) ≤ fr ^ 2 * δ₀ ^ 2 + 1 :=
          le_add_of_nonneg_left (by positivity)
        have hwin_nn : 0 ≤ dLaGridWin b ((m + 1) + 1) := dLaGridWin_nonneg b hb _
        calc
          fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + 1)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (m + 1)
                  (symmS (I := I) (M := M) g₀ T)).toSection x)
              ≤ fr ^ 3 * dLaGridWin b ((m + 1) + 1) := by
                refine mul_le_mul_of_nonneg_left ?_ hfr3_nn
                exact h1.trans (h2.trans h3)
          _ ≤ CP (m + 1) * dLaGridWin b ((m + 1) + 1) := by
                refine mul_le_mul_of_nonneg_right ?_ hwin_nn
                calc
                  fr ^ 3 = fr ^ 3 * 1 := by ring
                  _ ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) :=
                    mul_le_mul_of_nonneg_left hfac1 hfr3_nn
  have hLT : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dlaLoweredPerturb (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
      CLT i * W := by
    refine (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ i 0 4 4
      (slotInsertEndoCc (I := I) (M := M) g₀ 3
        (dlaPerturb (I := I) (M := M) g₀ T))
      (dlaLowered (I := I) (M := M) g₀ g₁ g_bg) x).trans ?_
    have hcell : ∀ i' ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
            ((iteratedCovGrad (I := I) g₀ 4 4 i'
              (slotInsertEndoCc (I := I) (M := M) g₀ 3
                (dlaPerturb (I := I) (M := M) g₀ T))).toSection x) *
          ∑ l ∈ Finset.range (i + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (dlaLowered (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
          CL l * dlaPairCount (i' + 1) (l + 3)) * W := by
      intro i' hi'
      rw [Finset.mem_range] at hi'
      have hi'_le : i' ≤ i := by omega
      have hA1 := hPfac i' hi'_le
      have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (dlaLowered (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1 - i'), CL l * dLaGridWin b (l + 3) := by
        refine Finset.sum_le_sum fun l hl => ?_
        rw [Finset.mem_range] at hl
        exact hCL g₀ g_bg hfix g₁ T htie hδ_le hδ_nonneg hbound l (by omega) x
      have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (dlaLowered (I := I) (M := M) g₀ g₁ g_bg)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _
      have hA1_rhs_nn : 0 ≤ CP i' * dLaGridWin b (i' + 1) :=
        mul_nonneg (hCP_nn i') (dLaGridWin_nonneg b hb (i' + 1))
      refine (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn).trans ?_
      rw [Finset.mul_sum]
      rw [show (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
          CL l * dlaPairCount (i' + 1) (l + 3)) * W =
          ∑ l ∈ Finset.range (i + 1 - i'),
            (CP i' * (CL l * dlaPairCount (i' + 1) (l + 3))) * W by
        rw [Finset.mul_sum, Finset.sum_mul]]
      refine Finset.sum_le_sum fun l hl => ?_
      rw [Finset.mem_range] at hl
      have hpair : dLaGridWin b (i' + 1) * dLaGridWin b (l + 3) ≤
          dlaPairCount (i' + 1) (l + 3) * dLaGridWin b (i + 3) :=
        grid_mul_le b hb (i' + 1) (l + 3) (i + 3) (by omega)
      calc
        CP i' * dLaGridWin b (i' + 1) * (CL l * dLaGridWin b (l + 3)) =
            (CP i' * CL l) * (dLaGridWin b (i' + 1) * dLaGridWin b (l + 3)) := by ring
        _ ≤ (CP i' * CL l) *
            (dlaPairCount (i' + 1) (l + 3) * dLaGridWin b (i + 3)) := by
              exact mul_le_mul_of_nonneg_left hpair (mul_nonneg (hCP_nn i') (hCL_nn l))
        _ = (CP i' * (CL l * dlaPairCount (i' + 1) (l + 3))) * W := by
              dsimp only [W]
              ring
    calc
      appCcGdiag (E := E) i *
          ∑ i' ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
                ((iteratedCovGrad (I := I) g₀ 4 4 i'
                  (slotInsertEndoCc (I := I) (M := M) g₀ 3
                    (dlaPerturb (I := I) (M := M) g₀ T))).toSection x) *
              ∑ l ∈ Finset.range (i + 1 - i'),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 l
                    (dlaLowered (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        appCcGdiag (E := E) i *
          ∑ i' ∈ Finset.range (i + 1),
            (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
              CL l * dlaPairCount (i' + 1) (l + 3)) * W :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
          (appCcGdiag_nonneg (E := E) i)
      _ = CLT i * W := by
        dsimp only [CLT]
        rw [← Finset.sum_mul, ← mul_assoc]
  have hL0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dlaLowered (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ CL i * W :=
    hCL g₀ g_bg hfix g₁ T htie hδ_le hδ_nonneg hbound i hi x
  have hLG1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dlaLoweredG1 (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
      2 * (CL i * W) + 2 * (CLT i * W) := by
    refine (rfns_add (I := I) (M := M) g₀ 0 4 i
      (dlaLowered (I := I) (M := M) g₀ g₁ g_bg)
      (dlaLoweredPerturb (I := I) (M := M) g₀ T g₁ g_bg) x).trans ?_
    linarith [hL0, hLT]
  have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (dlaLoweredG1 (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i
          (dlaLoweredG1 (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 4) 1)
      (dlaLoweredG1 (I := I) (M := M) g₀ T g₁ g_bg) i x
  refine (rfns_add (I := I) (M := M) g₀ 0 4 i
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (dlaLoweredG1 (I := I) (M := M) g₀ T g₁ g_bg))
    (dlaLoweredG1 (I := I) (M := M) g₀ T g₁ g_bg) x).trans ?_
  rw [hperm]
  linarith [hLG1]

set_option linter.unusedVariables false in
private theorem pair_trace_grid_unif
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ), j < 2 → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 6 2 j
              (dlaPairTrace (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C j * dLaGridWin
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (j + 1) := by
  classical
  obtain ⟨C2, hC2_nn, hC2⟩ := trace_grid_unif (I := I) (M := M) 2 hδ₀
  obtain ⟨C4, hC4_nn, hC4⟩ := trace_grid_unif (I := I) (M := M) 4 hδ₀
  refine ⟨fun j => appCcGdiag (E := E) j * ∑ i' ∈ Finset.range (j + 1),
      C2 i' * ∑ l ∈ Finset.range (j + 1 - i'),
        C4 l * dlaPairCount (i' + 1) (l + 1),
    fun j => mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hC2_nn i')
        (Finset.sum_nonneg fun l _ => mul_nonneg (hC4_nn l) (pair_nonneg _ _))), ?_⟩
  intro g₀ g₁ T htie δ hδ_le hδ_nonneg hbound j _ x
  let b : ℕ → ℝ := fun l =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)
  have hb : ∀ l, 0 ≤ b l := fun l =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  let W : ℝ := dLaGridWin b (j + 1)
  rw [pair_trace_def (I := I) (M := M) g₀ g₁]
  refine (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ j 6 4 2
    (pureTrace (I := I) (M := M) g₀ g₁ 2)
    (pureTrace (I := I) (M := M) g₀ g₁ 4) x).trans ?_
  have hpure2 : ∀ q : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 4 2 q
            (pureTrace (I := I) (M := M) g₀ g₁ 2)).toSection x) ≤
        C2 q * dLaGridWin b (q + 1) := by
    intro q
    have h := hC2 g₀ g₁ T htie hδ_le hδ_nonneg hbound (Equiv.refl _) q x
    rw [lc0TraceRF, rfns_iteratedCovGrad_reindexCoeffGen_eq
      (I := I) (M := M) g₀ (2 + 2) 2
        (pureTrace (I := I) (M := M) g₀ g₁ 2) (Equiv.refl _) q x] at h
    simpa only [dLaGridWin, b] using h
  have hpure4 : ∀ q : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + q) x
          ((iteratedCovGrad (I := I) g₀ 6 4 q
            (pureTrace (I := I) (M := M) g₀ g₁ 4)).toSection x) ≤
        C4 q * dLaGridWin b (q + 1) := by
    intro q
    have h := hC4 g₀ g₁ T htie hδ_le hδ_nonneg hbound (Equiv.refl _) q x
    rw [lc0TraceRF, rfns_iteratedCovGrad_reindexCoeffGen_eq
      (I := I) (M := M) g₀ (4 + 2) 4
        (pureTrace (I := I) (M := M) g₀ g₁ 4) (Equiv.refl _) q x] at h
    simpa only [dLaGridWin, b] using h
  have hcell : ∀ i' ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 4 2 i'
            (pureTrace (I := I) (M := M) g₀ g₁ 2)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 6 4 l
              (pureTrace (I := I) (M := M) g₀ g₁ 4)).toSection x) ≤
      (C2 i' * ∑ l ∈ Finset.range (j + 1 - i'),
        C4 l * dlaPairCount (i' + 1) (l + 1)) * W := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 := hpure2 i'
    have hA2 : (∑ l ∈ Finset.range (j + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 6 4 l
            (pureTrace (I := I) (M := M) g₀ g₁ 4)).toSection x)) ≤
        ∑ l ∈ Finset.range (j + 1 - i'), C4 l * dLaGridWin b (l + 1) :=
      Finset.sum_le_sum fun l _ => hpure4 l
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 6 4 l
            (pureTrace (I := I) (M := M) g₀ g₁ 4)).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (4 + l) x _
    have hA1_rhs_nn : 0 ≤ C2 i' * dLaGridWin b (i' + 1) :=
      mul_nonneg (hC2_nn i') (dLaGridWin_nonneg b hb (i' + 1))
    refine (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn).trans ?_
    rw [Finset.mul_sum]
    rw [show (C2 i' * ∑ l ∈ Finset.range (j + 1 - i'),
        C4 l * dlaPairCount (i' + 1) (l + 1)) * W =
        ∑ l ∈ Finset.range (j + 1 - i'),
          (C2 i' * (C4 l * dlaPairCount (i' + 1) (l + 1))) * W by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have hpair : dLaGridWin b (i' + 1) * dLaGridWin b (l + 1) ≤
        dlaPairCount (i' + 1) (l + 1) * dLaGridWin b (j + 1) :=
      grid_mul_le b hb (i' + 1) (l + 1) (j + 1) (by omega)
    calc
      C2 i' * dLaGridWin b (i' + 1) * (C4 l * dLaGridWin b (l + 1)) =
          (C2 i' * C4 l) * (dLaGridWin b (i' + 1) * dLaGridWin b (l + 1)) := by ring
      _ ≤ (C2 i' * C4 l) *
          (dlaPairCount (i' + 1) (l + 1) * dLaGridWin b (j + 1)) := by
            exact mul_le_mul_of_nonneg_left hpair (mul_nonneg (hC2_nn i') (hC4_nn l))
      _ = (C2 i' * (C4 l * dlaPairCount (i' + 1) (l + 1))) * W := by
            dsimp only [W]
            ring
  calc
    appCcGdiag (E := E) j *
        ∑ i' ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 4 2 i'
                (pureTrace (I := I) (M := M) g₀ g₁ 2)).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 6 4 l
                  (pureTrace (I := I) (M := M) g₀ g₁ 4)).toSection x) ≤
      appCcGdiag (E := E) j *
        ∑ i' ∈ Finset.range (j + 1),
          (C2 i' * ∑ l ∈ Finset.range (j + 1 - i'),
            C4 l * dlaPairCount (i' + 1) (l + 1)) * W :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
        (appCcGdiag_nonneg (E := E) j)
    _ = _ := by
      rw [← Finset.sum_mul, ← mul_assoc]

set_option linter.unusedVariables false in
/-- A cap for the first three fixed-background connection-difference jets
fixes the two-order DLa coefficient grid before any metric varies.  The cap is
kept as a raw, operator-independent tower so later coefficient factories can
reuse the same class input. -/
theorem dla_grid_of_conn
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (F : ℕ → ℝ) (hF : ∀ j, 0 ≤ F j) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₀ g_bg : SmoothRiemannianMetric I M),
        (∀ j, j < 3 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 1 2 j
                (connDiffSection (I := I) g_bg g₀)).toSection x) ≤ F j) →
        ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
          (htie : ∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
          {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
          (hbound : gFibreOpBound (I := I) (M := M) g₀
            (ccTensorBilinSymm (I := I) g₀ T) δ)
          (i : ℕ), i < 2 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
            C i * ∑ k ∈ Finset.range (i + 3),
              ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ := pair_trace_grid_unif (I := I) (M := M) hδ₀
  obtain ⟨CX, hCX_nn, hCX⟩ := sym_grid_of_conn (I := I) (M := M) hδ₀ F hF
  let fr : ℝ := Module.finrank ℝ E
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => appCcGdiag (E := E) i * ∑ i' ∈ Finset.range (i + 1),
      CPT i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * CX l)) * dlaPairCount (i' + 1) (l + 3),
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hCPT_nn i')
        (Finset.sum_nonneg fun l _ => mul_nonneg
          (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCX_nn l))) (pair_nonneg _ _))), ?_⟩
  intro g₀ g_bg hfix g₁ T htie δ hδ_le hδ_nonneg hbound i hi x
  let b : ℕ → ℝ := fun l =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)
  have hb : ∀ l, 0 ≤ b l := fun l =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  let W : ℝ := dLaGridWin b (i + 3)
  have hXtower : ∀ l, l ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (dlaSym (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
      CX l * dLaGridWin b (l + 3) := by
    intro l hl
    exact hCX g₀ g_bg hfix g₁ T htie hδ_le hδ_nonneg hbound l (by omega) x
  have hWtower : ∀ l, l ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 dlaSigma
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dlaSym (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) ≤
      (fr * (fr * CX l)) * dLaGridWin b (l + 3) := by
    intro l hl
    have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 dlaSigma
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dlaSym (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dlaSym (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) :=
      rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr
        (I := I) (M := M) g₀ 2 6 dlaSigma
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (dlaSym (I := I) (M := M) g₀ T g₁ g_bg))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 dlaSigma
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dlaSym (I := I) (M := M) g₀ T g₁ g_bg)))
        (fun y d => by rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) l x
    rw [hperm]
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dlaSym (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 5 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 1
              (dlaSym (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) :=
      rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1
          (dlaSym (I := I) (M := M) g₀ T g₁ g_bg)) l x
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 5 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 1
            (dlaSym (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (dlaSym (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) :=
      rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        (dlaSym (I := I) (M := M) g₀ T g₁ g_bg) l x
    have h3 := hXtower l hl
    calc
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dlaSym (I := I) (M := M) g₀ T g₁ g_bg))).toSection x)
          ≤ fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 5 l
                (slotExtendIter (I := I) (M := M) g₀ 0 4 1
                  (dlaSym (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) := h1
      _ ≤ fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (dlaSym (I := I) (M := M) g₀ T g₁ g_bg)).toSection x)) :=
        mul_le_mul_of_nonneg_left h2 hfr_nn
      _ ≤ fr * (fr * (CX l * dLaGridWin b (l + 3))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hfr_nn) hfr_nn
      _ = (fr * (fr * CX l)) * dLaGridWin b (l + 3) := by ring
  have hlift : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2
            (dlaPairTrace (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 dlaSigma
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (dlaSym (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) := by
    rw [dla_field_eq (I := I) (M := M) g₀ g_bg g₁ T htie]
    rw [iter_smul]
    rw [show (((-1 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 6 2
          (dlaPairTrace (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 dlaSigma
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dlaSym (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) =
        (-1 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2
            (dlaPairTrace (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 dlaSigma
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (dlaSym (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [rfns_smul (I := I) (M := M) g₀ 2 (2 + i) x]
    ring
  rw [hlift]
  refine (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ i 2 6 2
    (dlaPairTrace (I := I) (M := M) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 dlaSigma
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (dlaSym (I := I) (M := M) g₀ T g₁ g_bg))) x).trans ?_
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 6 2 i'
            (dlaPairTrace (I := I) (M := M) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 dlaSigma
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (dlaSym (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) ≤
      (CPT i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * CX l)) * dlaPairCount (i' + 1) (l + 3)) * W := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 6 2 i'
          (dlaPairTrace (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CPT i' * dLaGridWin b (i' + 1) :=
      hCPT g₀ g₁ T htie hδ_le hδ_nonneg hbound i' (by omega) x
    have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 dlaSigma
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (dlaSym (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - i'),
          (fr * (fr * CX l)) * dLaGridWin b (l + 3) := by
      refine Finset.sum_le_sum fun l hl => ?_
      rw [Finset.mem_range] at hl
      exact hWtower l (by omega)
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 dlaSigma
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (dlaSym (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _
    have hA1_rhs_nn : 0 ≤ CPT i' * dLaGridWin b (i' + 1) :=
      mul_nonneg (hCPT_nn i') (dLaGridWin_nonneg b hb (i' + 1))
    refine (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn).trans ?_
    rw [Finset.mul_sum]
    rw [show (CPT i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * CX l)) * dlaPairCount (i' + 1) (l + 3)) * W =
        ∑ l ∈ Finset.range (i + 1 - i'),
          (CPT i' * ((fr * (fr * CX l)) * dlaPairCount (i' + 1) (l + 3))) * W by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have hpair : dLaGridWin b (i' + 1) * dLaGridWin b (l + 3) ≤
        dlaPairCount (i' + 1) (l + 3) * dLaGridWin b (i + 3) :=
      grid_mul_le b hb (i' + 1) (l + 3) (i + 3) (by omega)
    calc
      CPT i' * dLaGridWin b (i' + 1) *
            ((fr * (fr * CX l)) * dLaGridWin b (l + 3)) =
          (CPT i' * (fr * (fr * CX l))) *
            (dLaGridWin b (i' + 1) * dLaGridWin b (l + 3)) := by ring
      _ ≤ (CPT i' * (fr * (fr * CX l))) *
          (dlaPairCount (i' + 1) (l + 3) * dLaGridWin b (i + 3)) := by
            exact mul_le_mul_of_nonneg_left hpair
              (mul_nonneg (hCPT_nn i')
                (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCX_nn l))))
      _ = (CPT i' * ((fr * (fr * CX l)) * dlaPairCount (i' + 1) (l + 3))) * W := by
            dsimp only [W]
            ring
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) i)).trans ?_
  rw [← Finset.sum_mul, ← mul_assoc]
  beta_reduce
  rfl

end DifferentialGeometry.Integral.Connection

end
