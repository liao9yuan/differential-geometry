import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSZeroRefold
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffDiffRadiusFree
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorr0CoeffDiffRadiusFree
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H3BoundedGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoeffDiffRadiusFree

/-!
# Tame H2 bounds for the refolded Ricci--DeTurck coefficients

This module retains the single metric `H4` head in the order-zero coefficient
and controls every lower bounded-factor window from the metric `H3` jet.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
      [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem edgePair_eq_mono
    (g g1 : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (sigma : Equiv.Perm (Fin 4)) :
    edgePairMono (I := I) (M := M) g g1 G sigma =
      refoldKernelContractionMonomialField
        (I := I) (M := M) g g1 G sigma := by
  rw [edgePairMono,
    refoldKernelContractionMonomialField_eq_mvPairTraceRefold]
  rfl

private theorem edgePair_smul
    (g g1 : SmoothRiemannianMetric I M) (a : Real)
    (G : SmoothCcTensor g 0 4) (sigma : Equiv.Perm (Fin 4)) :
    edgePairMono (I := I) (M := M) g g1 (a • G) sigma =
      a • edgePairMono (I := I) (M := M) g g1 G sigma := by
  apply SmoothCcTensor.ext
  apply DFunLike.coe_injective
  funext x
  rfl

omit [BoundarylessManifold I M] in
private theorem bilin_smul
    (g : SmoothRiemannianMetric I M) (a : Real)
    (A : SmoothCcTensor g 0 2) (x : M)
    (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g (a • A) x v w =
      a * ccTensorBilin (I := I) g A x v w := by
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]

private theorem h2_add_le
    (g : SmoothRiemannianMetric I M) {r s : Nat}
    (A B : SmoothCcTensor g r s) :
    (∑ i ∈ Finset.range 3,
      norm (iteratedCovGrad (I := I) g r s i (A + B)) ^ 2) <=
        2 * (∑ i ∈ Finset.range 3,
          norm (iteratedCovGrad (I := I) g r s i A) ^ 2) +
        2 * (∑ i ∈ Finset.range 3,
          norm (iteratedCovGrad (I := I) g r s i B) ^ 2) := by
  have hterm : ∀ i ∈ Finset.range 3,
      norm (iteratedCovGrad (I := I) g r s i (A + B)) ^ 2 <=
        2 * norm (iteratedCovGrad (I := I) g r s i A) ^ 2 +
          2 * norm (iteratedCovGrad (I := I) g r s i B) ^ 2 := by
    intro i _
    rw [iteratedCovGrad_add (I := I) g r s i A B]
    have htri := norm_add_le
      (iteratedCovGrad (I := I) g r s i A)
      (iteratedCovGrad (I := I) g r s i B)
    have hnnA : 0 <= norm (iteratedCovGrad (I := I) g r s i A) :=
      norm_nonneg _
    have hnnB : 0 <= norm (iteratedCovGrad (I := I) g r s i B) :=
      norm_nonneg _
    have hnnAB : 0 <=
        norm (iteratedCovGrad (I := I) g r s i A +
          iteratedCovGrad (I := I) g r s i B) :=
      norm_nonneg _
    nlinarith [sq_nonneg
      (norm (iteratedCovGrad (I := I) g r s i A) -
        norm (iteratedCovGrad (I := I) g r s i B))]
  calc
    (∑ i ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g r s i (A + B)) ^ 2)
        <= ∑ i ∈ Finset.range 3,
          (2 * norm (iteratedCovGrad (I := I) g r s i A) ^ 2 +
            2 * norm (iteratedCovGrad (I := I) g r s i B) ^ 2) :=
      Finset.sum_le_sum hterm
    _ = 2 * (∑ i ∈ Finset.range 3,
          norm (iteratedCovGrad (I := I) g r s i A) ^ 2) +
        2 * (∑ i ∈ Finset.range 3,
          norm (iteratedCovGrad (I := I) g r s i B) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private theorem h2_smul_le
    (g : SmoothRiemannianMetric I M) {r s : Nat}
    (a : Real) (A : SmoothCcTensor g r s) (ha : |a| <= 1) :
    (∑ i ∈ Finset.range 3,
      norm (iteratedCovGrad (I := I) g r s i (a • A)) ^ 2) <=
        ∑ i ∈ Finset.range 3,
          norm (iteratedCovGrad (I := I) g r s i A) ^ 2 := by
  have ha_sq : |a| ^ 2 <= 1 := by
    nlinarith [abs_nonneg a]
  refine Finset.sum_le_sum ?_
  intro i _
  rw [iteratedCovGrad_smul, norm_smul, Real.norm_eq_abs]
  calc
    (|a| * norm (iteratedCovGrad (I := I) g r s i A)) ^ 2 =
        |a| ^ 2 * norm (iteratedCovGrad (I := I) g r s i A) ^ 2 := by
      ring
    _ <= 1 * norm (iteratedCovGrad (I := I) g r s i A) ^ 2 :=
      mul_le_mul_of_nonneg_right ha_sq (sq_nonneg _)
    _ = norm (iteratedCovGrad (I := I) g r s i A) ^ 2 := one_mul _

private theorem edgeLie_eq_sum
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (q : Fin 3 -> Equiv.Perm (Fin 4)) (epsilon : Fin 3 -> Real)
    (s : Real) :
    edgeLiePairFam (I := I) (M := M) g T hdelta hdeltaZ q epsilon s =
      ∑ i : Fin 3, epsilon i • ((1 / 2 : Real) •
        (refoldKernelContractionMonomialField (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hdelta hdeltaZ s)
            (iteratedCovGrad (I := I) g 0 2 2 (s • T)) (q i) +
          refoldKernelContractionMonomialField (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hdelta hdeltaZ s)
            (iteratedCovGrad (I := I) g 0 2 2 (s • T))
            ((q i).trans (Equiv.swap (0 : Fin 4) 1)))) := by
  rw [edgeLiePairFam]
  simp_rw [← edgePair_eq_mono]
  rw [iteratedCovGrad_smul]
  simp_rw [edgePair_smul]
  module

/-- A single Palatini pair-trace monomial has a uniform intrinsic `H2` tame
bound.  The permutation is arbitrary, so the same constants control all six
monomials in the DeTurck Lie pair. -/
theorem mono_h2_tame
    (hDim : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M) {delta0 : Real}
    (hdelta0_lt : delta0 < 1) :
    ∃ Ctop : Nat -> Real, (∀ i, 0 <= Ctop i) ∧
      ∃ B : Real -> Real, (∀ A, 0 <= A -> 0 <= B A) ∧
        ∀ (g1 : SmoothRiemannianMetric I M)
          (P : SmoothCcTensor g 0 2)
          {delta : Real} (sigma : Equiv.Perm (Fin 4)) (A : Real),
          (∀ (y : M) (v w : TangentSpace I y),
            g1.inner y v w =
              g.inner y v w + ccTensorBilinSymm (I := I) g P y v w) ->
          (∀ (x : M) (v w : TangentSpace I x),
            ccTensorBilin (I := I) g P x v w =
              ccTensorBilin (I := I) g P x w v) ->
          delta <= delta0 ->
          0 <= delta ->
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g P) delta ->
          0 <= A ->
          (∑ j ∈ Finset.range 4,
            norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2) <= A ^ 2 ->
          (∑ i ∈ Finset.range 3,
            norm (iteratedCovGrad (I := I) g 2 2 i
              (refoldKernelContractionMonomialField
                (I := I) (M := M) g g1
                (iteratedCovGrad (I := I) g 0 2 2 P) sigma)) ^ 2) <=
              (∑ i ∈ Finset.range 3,
                Ctop i *
                  norm (iteratedCovGrad (I := I) g 0 2 (i + 2) P) ^ 2) +
                (B A) ^ 2 := by
  obtain ⟨K, hK, hraw⟩ :=
    rfns_iteratedCovGrad_refoldKernelContractionMonomialField_topSeparated_and_lowerWindow_le
      (I := I) (M := M) g hdelta0_lt
  let Ctop : Nat -> Real := fun _ =>
    2 * (((1 / (1 - delta0)) ^ 2) ^ 2)
  let C : Nat -> Real := fun i => 2 * K i
  have hCtop : ∀ i, 0 <= Ctop i := fun _ => by
    exact mul_nonneg (by norm_num) (sq_nonneg _)
  have hC : ∀ i, 0 <= C i := fun i => by
    exact mul_nonneg (by norm_num) (hK i)
  obtain ⟨B, hB, hint⟩ :=
    h2_of_bfg5_top (I := I) (M := M) hDim g Ctop C hC
  refine ⟨Ctop, hCtop, B, hB, ?_⟩
  intro g1 P delta sigma A htie hPsymm hdelta_le hdelta_nonneg hbound hA hPjet
  have hsymm :
      symmS (I := I) (M := M) g P = P :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g P hPsymm
  exact hint P
    (refoldKernelContractionMonomialField
      (I := I) (M := M) g g1
      (iteratedCovGrad (I := I) g 0 2 2 P) sigma)
    A hA hPjet (fun i hi x => by
      let V : TensorRSSpace 2 (2 + i) I x :=
        (iteratedCovGrad (I := I) g 2 2 i
          (refoldKernelContractionMonomialField
            (I := I) (M := M) g g1
            (iteratedCovGrad (I := I) g 0 2 2
              (symmS (I := I) (M := M) g P)) sigma)).toSection x
      let Htop : TensorRSSpace 2 (2 + i) I x :=
        (appCcRS (I := I) (M := M) g 2 (6 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g 6 2
            (mvPairTraceOp (I := I) (M := M) g g1) i i)
          (iteratedCovGrad (I := I) g 2 6 i
            (rsDomDomCongrSection (I := I) (M := M) g 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 4) 2 *
                    Equiv.swap (1 : Fin 4) 3 * sigma)
                  (iteratedCovGrad (I := I) g 0 2 2
                    (symmS (I := I) (M := M) g P))))))).toSection x
      let head : Real :=
        riemannianFiberNormSq (I := I) (M := M) g 0
          (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g 0 2 (i + 2) P).toSection x)
      let window : Real :=
        Combinatorics.boundedFactorGridWindow
          (fun l => riemannianFiberNormSq (I := I) (M := M) g 0
            (2 + l) x
            ((iteratedCovGrad (I := I) g 0 2 l P).toSection x))
          (i + 1) (i + 3)
      have hparts :=
        hraw g1 P htie hdelta_le hdelta_nonneg hbound sigma i x
      change
        riemannianFiberNormSq (I := I) (M := M) g 2 (2 + i) x Htop <=
            ((1 / (1 - delta0)) ^ 2) ^ 2 * head ∧
          riemannianFiberNormSq (I := I) (M := M) g 2 (2 + i) x
              (V - Htop) <= K i * window at hparts
      have hadd :=
        riemannianFiberNormSq_add_le
          (I := I) (M := M) g 2 (2 + i) x (V - Htop) Htop
      rw [sub_add_cancel] at hadd
      have hV :
          riemannianFiberNormSq (I := I) (M := M) g 2 (2 + i) x V <=
            Ctop i * head + C i * window := by
        calc
          riemannianFiberNormSq (I := I) (M := M) g 2 (2 + i) x V
              <= 2 * riemannianFiberNormSq
                    (I := I) (M := M) g 2 (2 + i) x (V - Htop) +
                  2 * riemannianFiberNormSq
                    (I := I) (M := M) g 2 (2 + i) x Htop := hadd
          _ <= 2 * (K i * window) +
                2 * ((((1 / (1 - delta0)) ^ 2) ^ 2) * head) :=
            add_le_add
              (mul_le_mul_of_nonneg_left hparts.2 (by norm_num))
              (mul_le_mul_of_nonneg_left hparts.1 (by norm_num))
          _ = Ctop i * head + C i * window := by
            dsimp only [Ctop, C]
            ring
      simpa only [V, hsymm] using hV)

/-- Along the realized metric segment, the complete DeTurck Lie pair has an
intrinsic `H2` tame bound with constants independent of the path parameter and
of all six slot permutations. -/
theorem liePair_h2_tame
    (hDim : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M) {delta0 : Real}
    (hdelta0_nonneg : 0 <= delta0) (hdelta0_lt : delta0 < 1) :
    ∃ Ctop : Nat -> Real, (∀ i, 0 <= Ctop i) ∧
      ∃ B : Real -> Real, (∀ A, 0 <= A -> 0 <= B A) ∧
        ∀ (T : SmoothCcTensor g 0 2) {delta : Real},
          (∀ (x : M) (v w : TangentSpace I x),
            ccTensorBilin (I := I) g T x v w =
              ccTensorBilin (I := I) g T x w v) ->
          delta <= delta0 ->
          0 <= delta ->
          (hdelta : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) delta) ->
          (hdeltaZ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g
              (0 : SmoothCcTensor g 0 2)) delta) ->
          ∀ (q : Fin 3 -> Equiv.Perm (Fin 4))
            (epsilon : Fin 3 -> Real),
          (∀ i, |epsilon i| <= 1) ->
          ∀ (s : Real), s ∈ Set.Icc (0 : Real) 1 ->
          ∀ (A : Real), 0 <= A ->
          (∑ j ∈ Finset.range 4,
            norm (iteratedCovGrad (I := I) g 0 2 j (s • T)) ^ 2) <= A ^ 2 ->
          (∑ i ∈ Finset.range 3,
            norm (iteratedCovGrad (I := I) g 2 2 i
              (edgeLiePairFam (I := I) (M := M) g T hdelta hdeltaZ
                q epsilon s)) ^ 2) <=
              (∑ i ∈ Finset.range 3,
                Ctop i *
                  norm (iteratedCovGrad (I := I) g 0 2
                    (i + 2) (s • T)) ^ 2) +
                (B A) ^ 2 := by
  classical
  obtain ⟨Cmono, hCmono, Bmono, hBmono, hmono⟩ :=
    mono_h2_tame (I := I) (M := M) hDim g hdelta0_lt
  let Ctop : Nat -> Real := fun i => 40 * Cmono i
  let B : Real -> Real := fun A => 40 * Bmono A
  have hCtop : ∀ i, 0 <= Ctop i := fun i =>
    mul_nonneg (by norm_num) (hCmono i)
  have hB : ∀ A, 0 <= A -> 0 <= B A := fun A hA =>
    mul_nonneg (by norm_num) (hBmono A hA)
  refine ⟨Ctop, hCtop, B, hB, ?_⟩
  intro T delta hTsymm hdelta_le hdelta_nonneg hdelta hdeltaZ
    q epsilon hepsilon s hs A hA hPjet
  let P : SmoothCcTensor g 0 2 := s • T
  let g1 : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hdelta hdeltaZ s
  have hdelta_lt : delta < 1 :=
    lt_of_le_of_lt hdelta_le hdelta0_lt
  have hs_mem : s ∈ realizedSmallSet (δ := delta) (δ' := delta) :=
    Icc_subset_realizedSmallSet hdelta_lt hdelta_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g1.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g P y v w := by
    intro y v w
    rw [← show convexPerturbation (I := I) g T 0 s = P by
      rw [convexPerturbation, smul_zero, zero_add]
      rfl]
    exact realizedFam_inner_of_mem
      (I := I) g T 0 hdelta hdeltaZ hs_mem y v w
  have hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g P x v w =
        ccTensorBilin (I := I) g P x w v := by
    intro x v w
    dsimp only [P]
    rw [bilin_smul (I := I) (M := M),
      bilin_smul (I := I) (M := M), hTsymm x v w]
  have hs_abs : |s| <= 1 := by
    rw [abs_of_nonneg hs.1]
    exact hs.2
  have hscaled_le : |s| * delta <= delta0 := by
    have hscaled_delta : |s| * delta <= delta := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hs_abs hdelta_nonneg
    exact hscaled_delta.trans hdelta_le
  have hscaled_nonneg : 0 <= |s| * delta :=
    mul_nonneg (abs_nonneg s) hdelta_nonneg
  have hboundP :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g P) (|s| * delta) := by
    simpa only [P] using
      gFibreOpBound_ccTensorBilinSymm_smul
        (I := I) (M := M) g s T hdelta
  let mono : Equiv.Perm (Fin 4) -> SmoothCcTensor g 2 2 := fun sigma =>
    refoldKernelContractionMonomialField (I := I) (M := M) g g1
      (iteratedCovGrad (I := I) g 0 2 2 P) sigma
  let pair : Fin 3 -> SmoothCcTensor g 2 2 := fun i =>
    mono (q i) + mono ((q i).trans (Equiv.swap (0 : Fin 4) 1))
  let term : Fin 3 -> SmoothCcTensor g 2 2 := fun i =>
    epsilon i • ((1 / 2 : Real) • pair i)
  let head : Real :=
    ∑ i ∈ Finset.range 3,
      Cmono i * norm (iteratedCovGrad (I := I) g 0 2
        (i + 2) P) ^ 2
  let D : Real := head + (Bmono A) ^ 2
  have hmono_le : ∀ sigma : Equiv.Perm (Fin 4),
      (∑ i ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g 2 2 i (mono sigma)) ^ 2) <= D := by
    intro sigma
    simpa only [mono, g1, P, head, D] using
      hmono g1 P (delta := |s| * delta) sigma A
        htie hPsymm hscaled_le hscaled_nonneg hboundP hA hPjet
  have hpair_le : ∀ i : Fin 3,
      (∑ j ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g 2 2 j (pair i)) ^ 2) <=
          4 * D := by
    intro i
    calc
      (∑ j ∈ Finset.range 3,
          norm (iteratedCovGrad (I := I) g 2 2 j (pair i)) ^ 2)
          <= 2 * (∑ j ∈ Finset.range 3,
              norm (iteratedCovGrad (I := I) g 2 2 j
                (mono (q i))) ^ 2) +
            2 * (∑ j ∈ Finset.range 3,
              norm (iteratedCovGrad (I := I) g 2 2 j
                (mono ((q i).trans (Equiv.swap (0 : Fin 4) 1)))) ^ 2) := by
        simpa only [pair] using h2_add_le (I := I) g
          (mono (q i))
          (mono ((q i).trans (Equiv.swap (0 : Fin 4) 1)))
      _ <= 2 * D + 2 * D :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hmono_le (q i)) (by norm_num))
          (mul_le_mul_of_nonneg_left
            (hmono_le ((q i).trans (Equiv.swap (0 : Fin 4) 1)))
            (by norm_num))
      _ = 4 * D := by ring
  have hterm_le : ∀ i : Fin 3,
      (∑ j ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g 2 2 j (term i)) ^ 2) <=
          4 * D := by
    intro i
    calc
      (∑ j ∈ Finset.range 3,
          norm (iteratedCovGrad (I := I) g 2 2 j (term i)) ^ 2)
          <= ∑ j ∈ Finset.range 3,
            norm (iteratedCovGrad (I := I) g 2 2 j
              ((1 / 2 : Real) • pair i)) ^ 2 := by
        simpa only [term] using h2_smul_le
          (I := I) g (epsilon i) ((1 / 2 : Real) • pair i)
          (hepsilon i)
      _ <= ∑ j ∈ Finset.range 3,
            norm (iteratedCovGrad (I := I) g 2 2 j (pair i)) ^ 2 :=
        h2_smul_le (I := I) g (1 / 2 : Real) (pair i) (by norm_num)
      _ <= 4 * D := hpair_le i
  have hsum :
      (∑ j ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g 2 2 j
          (term 0 + term 1 + term 2)) ^ 2) <= 40 * D := by
    calc
      (∑ j ∈ Finset.range 3,
          norm (iteratedCovGrad (I := I) g 2 2 j
            (term 0 + term 1 + term 2)) ^ 2)
          <= 2 * (∑ j ∈ Finset.range 3,
              norm (iteratedCovGrad (I := I) g 2 2 j
                (term 0 + term 1)) ^ 2) +
            2 * (∑ j ∈ Finset.range 3,
              norm (iteratedCovGrad (I := I) g 2 2 j (term 2)) ^ 2) :=
        h2_add_le (I := I) g (term 0 + term 1) (term 2)
      _ <= 2 * (2 * (∑ j ∈ Finset.range 3,
                norm (iteratedCovGrad (I := I) g 2 2 j (term 0)) ^ 2) +
              2 * (∑ j ∈ Finset.range 3,
                norm (iteratedCovGrad (I := I) g 2 2 j (term 1)) ^ 2)) +
            2 * (∑ j ∈ Finset.range 3,
              norm (iteratedCovGrad (I := I) g 2 2 j (term 2)) ^ 2) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (h2_add_le (I := I) g (term 0) (term 1)) (by norm_num))
          (le_refl _)
      _ <= 2 * (2 * (4 * D) + 2 * (4 * D)) + 2 * (4 * D) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (add_le_add
              (mul_le_mul_of_nonneg_left (hterm_le 0) (by norm_num))
              (mul_le_mul_of_nonneg_left (hterm_le 1) (by norm_num)))
            (by norm_num))
          (mul_le_mul_of_nonneg_left (hterm_le 2) (by norm_num))
      _ = 40 * D := by ring
  rw [edgeLie_eq_sum, Fin.sum_univ_three]
  change
    (∑ i ∈ Finset.range 3,
      norm (iteratedCovGrad (I := I) g 2 2 i
        (term 0 + term 1 + term 2)) ^ 2) <=
      (∑ i ∈ Finset.range 3,
        Ctop i * norm (iteratedCovGrad (I := I) g 0 2
          (i + 2) P) ^ 2) + (B A) ^ 2
  calc
    (∑ i ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g 2 2 i
          (term 0 + term 1 + term 2)) ^ 2)
        <= 40 * D := hsum
    _ = 40 * head + 40 * (Bmono A) ^ 2 := by
      dsimp only [D]
      ring
    _ <= 40 * head + (40 * Bmono A) ^ 2 := by
      gcongr
      nlinarith [sq_nonneg (Bmono A)]
    _ = (∑ i ∈ Finset.range 3,
          Ctop i * norm (iteratedCovGrad (I := I) g 0 2
            (i + 2) P) ^ 2) + (B A) ^ 2 := by
      dsimp only [head, Ctop, B]
      rw [Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i _
        ring
      · rfl

/-- In dimension three, the Ricci connection-difference coefficient has a
tame intrinsic `H2` bound: the bounded-factor remainder depends only on the
metric `H3` jet, while the single head is linear in the metric `H4` jet. -/
theorem ricciConn_h2_tame
    (hDim : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M) {delta0 : Real}
    (hdelta0_lt : delta0 < 1) (hdelta0_half : delta0 <= 1 / 2) :
    ∃ Ctop : Nat -> Real, (forall i, 0 <= Ctop i) ∧
      ∃ B : Real -> Real, (forall A, 0 <= A -> 0 <= B A) ∧
        forall (g1 : SmoothRiemannianMetric I M)
          (P : SmoothCcTensor g 0 2)
          {delta : Real} (A : Real),
          (forall (y : M) (v w : TangentSpace I y),
            g1.inner y v w =
              g.inner y v w + ccTensorBilinSymm (I := I) g P y v w) ->
          delta <= delta0 ->
          0 <= delta ->
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g P) delta ->
          0 <= A ->
          (∑ j ∈ Finset.range 4,
            norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2) <= A ^ 2 ->
          (∑ i ∈ Finset.range 3,
            norm (iteratedCovGrad (I := I) g 2 2 i
              (linearizedRicciConnDiffOrder0CoeffField
                (I := I) (M := M) g g1)) ^ 2) <=
              (∑ i ∈ Finset.range 3,
                Ctop i *
                  norm (iteratedCovGrad (I := I) g 0 2 (i + 2) P) ^ 2) +
                (B A) ^ 2 := by
  obtain ⟨C, hC, hpoint⟩ :=
    rfns_iteratedCovGrad_linearizedRicciConnDiffOrder0CoeffField_topAmplitude_le
      (I := I) (M := M) g hdelta0_lt hdelta0_half
  let Ctop : Nat -> Real := fun _ =>
    ((21 / 4 : Real) * (Module.finrank Real E : Real) *
      (1 / (1 - delta0)) ^ 2) ^ 2
  have hCtop : forall i, 0 <= Ctop i := fun _ => by
    exact sq_nonneg _
  obtain ⟨B, hB, hint⟩ :=
    h2_of_bfg5_top (I := I) (M := M) hDim g Ctop C hC
  refine ⟨Ctop, hCtop, B, hB, ?_⟩
  intro g1 P delta A htie hdelta_le hdelta_nonneg hbound hA hPjet
  exact hint P
    (linearizedRicciConnDiffOrder0CoeffField
      (I := I) (M := M) g g1) A hA hPjet
    (fun i hi x => by
      simpa only [Ctop] using
        hpoint g1 P htie hdelta_le hdelta_nonneg hbound i x)

/-- In dimension three, the Palatini kernel left by the exact Ricci field
refold has the same tame `H2` shape as the connection-difference coefficient.
Only the fourth metric jet remains explicit. -/
theorem ricciKer_h2_tame
    (hDim : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M) {delta0 : Real}
    (hdelta0_lt : delta0 < 1) (hdelta0_half : delta0 <= 1 / 2) :
    ∃ Ctop : Nat -> Real, (∀ i, 0 <= Ctop i) ∧
      ∃ B : Real -> Real, (∀ A, 0 <= A -> 0 <= B A) ∧
        ∀ (g1 : SmoothRiemannianMetric I M)
          (P : SmoothCcTensor g 0 2)
          {delta : Real} (A : Real),
          (∀ (y : M) (v w : TangentSpace I y),
            g1.inner y v w =
              g.inner y v w + ccTensorBilinSymm (I := I) g P y v w) ->
          (∀ (x : M) (v w : TangentSpace I x),
            ccTensorBilin (I := I) g P x v w =
              ccTensorBilin (I := I) g P x w v) ->
          delta <= delta0 ->
          0 <= delta ->
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g P) delta ->
          0 <= A ->
          (∑ j ∈ Finset.range 4,
            norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2) <= A ^ 2 ->
          (∑ i ∈ Finset.range 3,
            norm (iteratedCovGrad (I := I) g 2 2 i
              (refoldKernelContractionField (I := I) (M := M) g g1
                (iteratedCovGrad (I := I) g 0 2 2 P)
                (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
                (Equiv.swap (0 : Fin 4) 2 *
                  Equiv.swap (1 : Fin 4) 3) 1)) ^ 2) <=
              (∑ i ∈ Finset.range 3,
                Ctop i *
                  norm (iteratedCovGrad (I := I) g 0 2 (i + 2) P) ^ 2) +
                (B A) ^ 2 := by
  obtain ⟨C, hC, hpoint⟩ :=
    rfns_iteratedCovGrad_refoldKernelContractionField_symmSSecondGradient_topAmplitude_le
      (I := I) (M := M) g hdelta0_lt hdelta0_half
  let Ctop : Nat -> Real := fun _ =>
    ((23 / 20 : Real) * (Module.finrank Real E : Real) *
      (1 / (1 - delta0)) ^ 2) ^ 2
  have hCtop : ∀ i, 0 <= Ctop i := fun _ => by
    exact sq_nonneg _
  obtain ⟨B, hB, hint⟩ :=
    h2_of_bfg5_top (I := I) (M := M) hDim g Ctop C hC
  refine ⟨Ctop, hCtop, B, hB, ?_⟩
  intro g1 P delta A htie hPsymm hdelta_le hdelta_nonneg hbound hA hPjet
  have hsymm :
      symmS (I := I) (M := M) g P = P :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g P hPsymm
  exact hint P
    (refoldKernelContractionField (I := I) (M := M) g g1
      (iteratedCovGrad (I := I) g 0 2 2 P)
      (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)
    A hA hPjet
    (fun i hi x => by
      simpa only [Ctop, hsymm] using
        hpoint g1 P htie hdelta_le hdelta_nonneg hbound i x)

/-- The Ricci base curvature coefficient has an intrinsic `H2` tame bound.
The fourth metric jet remains as one explicit head, while the lower part
depends only on the first four metric jets. -/
theorem ricciBase_h2_tame
    (g : SmoothRiemannianMetric I M) {delta0 : Real}
    (hdelta0_lt : delta0 < 1) :
    ∃ Ktop : Real, 0 <= Ktop ∧
      ∃ B : Real -> Real, (forall A, 0 <= A -> 0 <= B A) ∧
        forall (g1 : SmoothRiemannianMetric I M)
          (P : SmoothCcTensor g 0 2)
          {delta : Real} (A : Real),
          delta <= delta0 ->
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g P) delta ->
          (forall (y : M) (v w : TangentSpace I y),
            g1.inner y v w =
              g.inner y v w + ccTensorBilinSymm (I := I) g P y v w) ->
          0 <= A ->
          (∑ j ∈ Finset.range 4,
            norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2) <= A ^ 2 ->
          (∑ i ∈ Finset.range 3,
            norm (iteratedCovGrad (I := I) g 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g g1 -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g g1)) ^ 2) <=
              Ktop * norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 +
                (B A) ^ 2 := by
  classical
  obtain ⟨Ktop, hKtop, Klow, hKlow, hbase⟩ :=
    ricciArmOrder0BaseCoeff_summed_l2_radiusFree
      (I := I) (M := M) g 2 hdelta0_lt
  let B : Real -> Real := fun A =>
    Real.sqrt (Ktop * A ^ 2 + Klow * (1 + A ^ 2))
  have hB : forall A, 0 <= A -> 0 <= B A := fun A _ =>
    Real.sqrt_nonneg _
  refine ⟨Ktop, hKtop, B, hB, ?_⟩
  intro g1 P delta A hdelta_le hbound htie hA hPjet
  have hsymm : forall j,
      norm (iteratedCovGrad (I := I) g 0 2 j
          (symmS (I := I) (M := M) g P)) ^ 2 <=
        norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2 := by
    intro j
    have hnorm :=
      norm_iteratedCovGrad_symmS_le (I := I) (M := M) g P j
    nlinarith [norm_nonneg (iteratedCovGrad (I := I) g 0 2 j
      (symmS (I := I) (M := M) g P)),
      norm_nonneg (iteratedCovGrad (I := I) g 0 2 j P)]
  have hlow :
      (∑ j ∈ Finset.range 4,
        norm (iteratedCovGrad (I := I) g 0 2 j
          (symmS (I := I) (M := M) g P)) ^ 2) <= A ^ 2 :=
    (Finset.sum_le_sum fun j _ => hsymm j).trans hPjet
  have htop :
      (∑ j ∈ Finset.range 5,
        norm (iteratedCovGrad (I := I) g 0 2 j
          (symmS (I := I) (M := M) g P)) ^ 2) <=
        A ^ 2 + norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 := by
    rw [show 5 = 4 + 1 by omega, Finset.sum_range_succ]
    exact add_le_add hlow (hsymm 4)
  have hraw := hbase g1 P hdelta_le hbound htie
  have hinner :
      0 <= Ktop * A ^ 2 + Klow * (1 + A ^ 2) := by
    exact add_nonneg (mul_nonneg hKtop (sq_nonneg A))
      (mul_nonneg hKlow (by nlinarith [sq_nonneg A]))
  calc
    (∑ i ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g g1 -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g g1)) ^ 2)
        <= Ktop * (∑ j ∈ Finset.range 5,
              norm (iteratedCovGrad (I := I) g 0 2 j
                (symmS (I := I) (M := M) g P)) ^ 2) +
            Klow * (1 + ∑ j ∈ Finset.range 4,
              norm (iteratedCovGrad (I := I) g 0 2 j
                (symmS (I := I) (M := M) g P)) ^ 2) := hraw
    _ <= Ktop *
          (A ^ 2 + norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2) +
        Klow * (1 + A ^ 2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left htop hKtop)
        (mul_le_mul_of_nonneg_left (by nlinarith [hlow]) hKlow)
    _ = Ktop * norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 +
        (B A) ^ 2 := by
      rw [show (B A) ^ 2 = Ktop * A ^ 2 + Klow * (1 + A ^ 2) by
        exact Real.sq_sqrt hinner]
      ring

/-- The `DLa` part of the DeTurck coefficient has an intrinsic `H2` tame
bound without a supercritical Sobolev-index assumption.  Fibre smallness fixes
the zeroth-order grid radius; the fourth metric jet remains explicit. -/
theorem dLa_h2_tame
    (g g_bg : SmoothRiemannianMetric I M) {delta0 : Real}
    (hdelta0_nonneg : 0 <= delta0) (hdelta0_lt : delta0 < 1) :
    ∃ C4 : Real, 0 <= C4 ∧
      ∃ B : Real -> Real, (∀ A, 0 <= A -> 0 <= B A) ∧
        ∀ (g1 : SmoothRiemannianMetric I M)
          (P : SmoothCcTensor g 0 2)
          {delta : Real} (A : Real),
          (∀ (y : M) (v w : TangentSpace I y),
            g1.inner y v w =
              g.inner y v w + ccTensorBilinSymm (I := I) g P y v w) ->
          delta <= delta0 ->
          0 <= delta ->
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g P) delta ->
          0 <= A ->
          (∑ j ∈ Finset.range 4,
            norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2) <= A ^ 2 ->
          (∑ i ∈ Finset.range 3,
            norm (iteratedCovGrad (I := I) g 2 2 i
              (deTurckLieDLaCoeffField
                (I := I) (M := M) g g1 g_bg)) ^ 2) <=
              C4 * norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 +
                (B A) ^ 2 := by
  classical
  have hLambda :
      0 <= (Module.finrank Real E : Real) * delta0 :=
    mul_nonneg (Nat.cast_nonneg _) hdelta0_nonneg
  obtain ⟨Ktop, hKtop, Flow, hFlow, hper⟩ :=
    dLaField_perOrder_rf (I := I) (M := M) g g_bg hdelta0_lt hLambda
  let Kt : Real := ∑ i ∈ Finset.range 3, Ktop i
  let Kl : Real := ∑ i ∈ Finset.range 3, Flow i
  have hKt : 0 <= Kt := by
    exact Finset.sum_nonneg (fun i _ => hKtop i)
  have hKl : 0 <= Kl := by
    exact Finset.sum_nonneg (fun i _ => hFlow i)
  let C4 : Real := Kt + Kl
  have hC4 : 0 <= C4 := add_nonneg hKt hKl
  let B : Real -> Real := fun A =>
    Real.sqrt (Kt * A ^ 2 + Kl * (1 + A ^ 2))
  have hB : ∀ A, 0 <= A -> 0 <= B A :=
    fun A _ => Real.sqrt_nonneg _
  refine ⟨C4, hC4, B, hB, ?_⟩
  intro g1 P delta A htie hdelta_le hdelta_nonneg hbound hA hPjet
  let Ps : SmoothCcTensor g 0 2 := symmS (I := I) (M := M) g P
  have htieS : ∀ (y : M) (v w : TangentSpace I y),
      g1.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g Ps y v w := by
    intro y v w
    simpa only [Ps, ccTensorBilinSymm_symmS_apply] using htie y v w
  have hboundS :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g Ps) delta := by
    simpa only [Ps] using
      gFibreOpBound_symmS (I := I) (M := M) g P hbound
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (Ps.toSection x) <=
        ((Module.finrank Real E : Real) * delta0) ^ 2 := by
    intro x
    simpa only [Ps] using
      rfns_symmS_zero_le_fibreSmall (I := I) (M := M) g
        hdelta0_nonneg P hdelta_le hdelta_nonneg hbound x
  have hperS : ∀ i,
      norm (iteratedCovGrad (I := I) g 2 2 i
          (deTurckLieDLaCoeffField
            (I := I) (M := M) g g1 g_bg)) ^ 2 <=
        Ktop i * norm (iteratedCovGrad (I := I) g 0 2 (i + 2) Ps) ^ 2 +
          Flow i * (1 + ∑ j ∈ Finset.range (i + 3),
            norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2) :=
    fun i => hper g1 Ps htieS hdelta_le hdelta_nonneg hboundS hsup i
  have hsymm : ∀ j,
      norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2 <=
        norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2 := by
    intro j
    have hnorm :=
      norm_iteratedCovGrad_symmS_le (I := I) (M := M) g P j
    dsimp only [Ps]
    nlinarith [norm_nonneg
      (iteratedCovGrad (I := I) g 0 2 j
        (symmS (I := I) (M := M) g P)),
      norm_nonneg (iteratedCovGrad (I := I) g 0 2 j P)]
  have hlow :
      (∑ j ∈ Finset.range 4,
        norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2) <= A ^ 2 :=
    (Finset.sum_le_sum fun j _ => hsymm j).trans hPjet
  have hfull :
      (∑ j ∈ Finset.range 5,
        norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2) <=
        A ^ 2 + norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 := by
    rw [show 5 = 4 + 1 by omega, Finset.sum_range_succ]
    exact add_le_add hlow (hsymm 4)
  have hterm : ∀ i ∈ Finset.range 3,
      norm (iteratedCovGrad (I := I) g 2 2 i
          (deTurckLieDLaCoeffField
            (I := I) (M := M) g g1 g_bg)) ^ 2 <=
        Ktop i *
            (A ^ 2 + norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2) +
          Flow i *
            (1 + (A ^ 2 +
              norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2)) := by
    intro i hi
    have hi3 : i < 3 := Finset.mem_range.mp hi
    have htop :
        norm (iteratedCovGrad (I := I) g 0 2 (i + 2) Ps) ^ 2 <=
          A ^ 2 + norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 := by
      exact (Finset.single_le_sum
        (f := fun j =>
          norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2)
        (fun j _ => sq_nonneg _)
        (Finset.mem_range.mpr (by omega))).trans hfull
    have hwindow :
        (∑ j ∈ Finset.range (i + 3),
          norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2) <=
            A ^ 2 + norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 := by
      exact (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (by omega))
        (fun j _ _ => sq_nonneg _)).trans hfull
    exact (hperS i).trans (add_le_add
      (mul_le_mul_of_nonneg_left htop (hKtop i))
      (mul_le_mul_of_nonneg_left
        (by linarith [hwindow]) (hFlow i)))
  have hsum :
      (∑ i ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g 2 2 i
          (deTurckLieDLaCoeffField
            (I := I) (M := M) g g1 g_bg)) ^ 2) <=
        ∑ i ∈ Finset.range 3,
          (Ktop i *
              (A ^ 2 +
                norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2) +
            Flow i *
              (1 + (A ^ 2 +
                norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2))) :=
    Finset.sum_le_sum hterm
  have hinner :
      0 <= Kt * A ^ 2 + Kl * (1 + A ^ 2) :=
    add_nonneg (mul_nonneg hKt (sq_nonneg A))
      (mul_nonneg hKl (by nlinarith [sq_nonneg A]))
  calc
    (∑ i ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g 2 2 i
          (deTurckLieDLaCoeffField
            (I := I) (M := M) g g1 g_bg)) ^ 2)
        <= ∑ i ∈ Finset.range 3,
          (Ktop i *
              (A ^ 2 +
                norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2) +
            Flow i *
              (1 + (A ^ 2 +
                norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2))) := hsum
    _ = C4 * norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 +
        (Kt * A ^ 2 + Kl * (1 + A ^ 2)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      change Kt *
          (A ^ 2 + norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2) +
        Kl *
          (1 + (A ^ 2 +
            norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2)) =
        C4 * norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 +
          (Kt * A ^ 2 + Kl * (1 + A ^ 2))
      dsimp only [C4]
      ring
    _ = C4 * norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 +
        (B A) ^ 2 := by
      rw [show (B A) ^ 2 = Kt * A ^ 2 + Kl * (1 + A ^ 2) by
        exact Real.sq_sqrt hinner]

/-- The `DLb` part of the DeTurck coefficient has an intrinsic `H2` tame
bound without a theorem-facing high-index hypothesis.  The all-order producer
is used at one fixed background-dependent supercritical index, while only
orders zero through two are consumed. -/
theorem dLb_h2_tame
    (g g_bg : SmoothRiemannianMetric I M) {delta0 : Real}
    (hdelta0_nonneg : 0 <= delta0) (hdelta0_lt : delta0 < 1) :
    ∃ C4 : Real, 0 <= C4 ∧
      ∃ B : Real -> Real, (∀ A, 0 <= A -> 0 <= B A) ∧
        ∀ (g1 : SmoothRiemannianMetric I M)
          (P : SmoothCcTensor g 0 2)
          {delta : Real} (A : Real),
          (∀ (y : M) (v w : TangentSpace I y),
            g1.inner y v w =
              g.inner y v w + ccTensorBilinSymm (I := I) g P y v w) ->
          delta <= delta0 ->
          0 <= delta ->
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g P) delta ->
          0 <= A ->
          (∑ j ∈ Finset.range 4,
            norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2) <= A ^ 2 ->
          (∑ i ∈ Finset.range 3,
            norm (iteratedCovGrad (I := I) g 2 2 i
              (deTurckLieDLbCoeffField
                (I := I) (M := M) g g1 g_bg)) ^ 2) <=
              C4 * norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 +
                (B A) ^ 2 := by
  classical
  let aStar : Nat := 2 * Module.finrank Real E + 10
  have haStar : 2 * Module.finrank Real E + 10 <= aStar := le_rfl
  have hLambda :
      0 <= (Module.finrank Real E : Real) * delta0 :=
    mul_nonneg (Nat.cast_nonneg _) hdelta0_nonneg
  obtain ⟨Ktop, hKtop, Flow, hFlow, hper⟩ :=
    dLbField_perOrder_rf (I := I) (M := M) g g_bg
      aStar haStar hdelta0_lt hLambda
  let Kt : Real := ∑ _i ∈ Finset.range 3, Ktop
  let Kl : Real := ∑ i ∈ Finset.range 3, Flow i
  have hKt : 0 <= Kt := by
    exact Finset.sum_nonneg (fun _ _ => hKtop)
  have hKl : 0 <= Kl := by
    exact Finset.sum_nonneg (fun i _ => hFlow i)
  let C4 : Real := Kt + Kl
  have hC4 : 0 <= C4 := add_nonneg hKt hKl
  let B : Real -> Real := fun A =>
    Real.sqrt (Kt * A ^ 2 + Kl * (1 + A ^ 2))
  have hB : ∀ A, 0 <= A -> 0 <= B A :=
    fun A _ => Real.sqrt_nonneg _
  refine ⟨C4, hC4, B, hB, ?_⟩
  intro g1 P delta A htie hdelta_le hdelta_nonneg hbound hA hPjet
  let Ps : SmoothCcTensor g 0 2 := symmS (I := I) (M := M) g P
  have htieS : ∀ (y : M) (v w : TangentSpace I y),
      g1.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g Ps y v w := by
    intro y v w
    simpa only [Ps, ccTensorBilinSymm_symmS_apply] using htie y v w
  have hboundS :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g Ps) delta := by
    simpa only [Ps] using
      gFibreOpBound_symmS (I := I) (M := M) g P hbound
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (Ps.toSection x) <=
        ((Module.finrank Real E : Real) * delta0) ^ 2 := by
    intro x
    simpa only [Ps] using
      rfns_symmS_zero_le_fibreSmall (I := I) (M := M) g
        hdelta0_nonneg P hdelta_le hdelta_nonneg hbound x
  have hperS : ∀ i, i < 3 ->
      norm (iteratedCovGrad (I := I) g 2 2 i
          (deTurckLieDLbCoeffField
            (I := I) (M := M) g g1 g_bg)) ^ 2 <=
        Ktop * norm (iteratedCovGrad (I := I) g 0 2 (i + 2) Ps) ^ 2 +
          Flow i * (1 + ∑ j ∈ Finset.range (i + 3),
            norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2) := by
    intro i hi
    exact hper g1 Ps htieS hdelta_le hdelta_nonneg hboundS hsup i
      (by dsimp only [aStar]; omega)
  have hsymm : ∀ j,
      norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2 <=
        norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2 := by
    intro j
    have hnorm :=
      norm_iteratedCovGrad_symmS_le (I := I) (M := M) g P j
    dsimp only [Ps]
    nlinarith [norm_nonneg
      (iteratedCovGrad (I := I) g 0 2 j
        (symmS (I := I) (M := M) g P)),
      norm_nonneg (iteratedCovGrad (I := I) g 0 2 j P)]
  have hlow :
      (∑ j ∈ Finset.range 4,
        norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2) <= A ^ 2 :=
    (Finset.sum_le_sum fun j _ => hsymm j).trans hPjet
  have hfull :
      (∑ j ∈ Finset.range 5,
        norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2) <=
        A ^ 2 + norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 := by
    rw [show 5 = 4 + 1 by omega, Finset.sum_range_succ]
    exact add_le_add hlow (hsymm 4)
  have hterm : ∀ i ∈ Finset.range 3,
      norm (iteratedCovGrad (I := I) g 2 2 i
          (deTurckLieDLbCoeffField
            (I := I) (M := M) g g1 g_bg)) ^ 2 <=
        Ktop *
            (A ^ 2 + norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2) +
          Flow i *
            (1 + (A ^ 2 +
              norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2)) := by
    intro i hi
    have hi3 : i < 3 := Finset.mem_range.mp hi
    have htop :
        norm (iteratedCovGrad (I := I) g 0 2 (i + 2) Ps) ^ 2 <=
          A ^ 2 + norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 := by
      exact (Finset.single_le_sum
        (f := fun j =>
          norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2)
        (fun j _ => sq_nonneg _)
        (Finset.mem_range.mpr (by omega))).trans hfull
    have hwindow :
        (∑ j ∈ Finset.range (i + 3),
          norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2) <=
            A ^ 2 + norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 := by
      exact (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (by omega))
        (fun j _ _ => sq_nonneg _)).trans hfull
    exact (hperS i hi3).trans (add_le_add
      (mul_le_mul_of_nonneg_left htop hKtop)
      (mul_le_mul_of_nonneg_left
        (by linarith [hwindow]) (hFlow i)))
  have hsum :
      (∑ i ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g 2 2 i
          (deTurckLieDLbCoeffField
            (I := I) (M := M) g g1 g_bg)) ^ 2) <=
        ∑ i ∈ Finset.range 3,
          (Ktop *
              (A ^ 2 +
                norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2) +
            Flow i *
              (1 + (A ^ 2 +
                norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2))) :=
    Finset.sum_le_sum hterm
  have hinner :
      0 <= Kt * A ^ 2 + Kl * (1 + A ^ 2) :=
    add_nonneg (mul_nonneg hKt (sq_nonneg A))
      (mul_nonneg hKl (by nlinarith [sq_nonneg A]))
  calc
    (∑ i ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g 2 2 i
          (deTurckLieDLbCoeffField
            (I := I) (M := M) g g1 g_bg)) ^ 2)
        <= ∑ i ∈ Finset.range 3,
          (Ktop *
              (A ^ 2 +
                norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2) +
            Flow i *
              (1 + (A ^ 2 +
                norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2))) := hsum
    _ = C4 * norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 +
        (Kt * A ^ 2 + Kl * (1 + A ^ 2)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      change Kt *
          (A ^ 2 + norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2) +
        Kl *
          (1 + (A ^ 2 +
            norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2)) =
        C4 * norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 +
          (Kt * A ^ 2 + Kl * (1 + A ^ 2))
      dsimp only [C4]
      ring
    _ = C4 * norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 +
        (B A) ^ 2 := by
      rw [show (B A) ^ 2 = Kt * A ^ 2 + Kl * (1 + A ^ 2) by
        exact Real.sq_sqrt hinner]

/-- The lower `lieCorr0` coefficient has an intrinsic `H2` tame bound with
uniform lower-order constants.  The supercritical order required by the
all-order producer is fixed inside the proof and is absent from this API. -/
theorem lieCorr_h2_tame
    (g g_bg : SmoothRiemannianMetric I M) {delta0 : Real}
    (hdelta0_nonneg : 0 <= delta0) (hdelta0_lt : delta0 < 1) :
    ∃ C4 : Real, 0 <= C4 ∧
      ∃ B : Real -> Real, (∀ A, 0 <= A -> 0 <= B A) ∧
        ∀ (g1 : SmoothRiemannianMetric I M)
          (P : SmoothCcTensor g 0 2)
          {delta : Real} (A : Real),
          (∀ (y : M) (v w : TangentSpace I y),
            g1.inner y v w =
              g.inner y v w + ccTensorBilinSymm (I := I) g P y v w) ->
          delta <= delta0 ->
          0 <= delta ->
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g P) delta ->
          0 <= A ->
          (∑ j ∈ Finset.range 4,
            norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2) <= A ^ 2 ->
          (∑ i ∈ Finset.range 3,
            norm (iteratedCovGrad (I := I) g 2 2 i
              (lieCorr0Field (I := I) (M := M) g g1 g_bg)) ^ 2) <=
              C4 * norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 +
                (B A) ^ 2 := by
  classical
  let aStar : Nat := 2 * Module.finrank Real E + 10
  have haStar : 2 * Module.finrank Real E + 10 <= aStar := le_rfl
  have hLambda :
      0 <= (Module.finrank Real E : Real) * delta0 :=
    mul_nonneg (Nat.cast_nonneg _) hdelta0_nonneg
  obtain ⟨Atop, hAtop, Alow, hAlow, hper⟩ :=
    lieCorr0Field_perOrder_l2_radiusFree
      (I := I) (M := M) g g_bg aStar haStar hdelta0_lt hLambda
  let Kt : Real := ∑ i ∈ Finset.range 3, Atop i
  let Kl : Real := ∑ i ∈ Finset.range 3, Alow i
  have hKt : 0 <= Kt := by
    exact Finset.sum_nonneg (fun i _ => hAtop i)
  have hKl : 0 <= Kl := by
    exact Finset.sum_nonneg (fun i _ => hAlow i)
  let C4 : Real := Kt
  have hC4 : 0 <= C4 := hKt
  let B : Real -> Real := fun A =>
    Real.sqrt (Kt * A ^ 2 + Kl * (1 + A ^ 2))
  have hB : ∀ A, 0 <= A -> 0 <= B A :=
    fun A _ => Real.sqrt_nonneg _
  refine ⟨C4, hC4, B, hB, ?_⟩
  intro g1 P delta A htie hdelta_le hdelta_nonneg hbound hA hPjet
  let Ps : SmoothCcTensor g 0 2 := symmS (I := I) (M := M) g P
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (Ps.toSection x) <=
        ((Module.finrank Real E : Real) * delta0) ^ 2 := by
    intro x
    simpa only [Ps] using
      rfns_symmS_zero_le_fibreSmall (I := I) (M := M) g
        hdelta0_nonneg P hdelta_le hdelta_nonneg hbound x
  have hperS : ∀ i, i < 3 ->
      norm (iteratedCovGrad (I := I) g 2 2 i
          (lieCorr0Field (I := I) (M := M) g g1 g_bg)) ^ 2 <=
        Atop i * norm (iteratedCovGrad (I := I) g 0 2 (i + 2) Ps) ^ 2 +
          Alow i * (1 + ∑ j ∈ Finset.range (i + 2),
            norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2) := by
    intro i hi
    simpa only [Ps] using
      hper g1 P hdelta_le hdelta_nonneg hbound htie hsup i
        (by dsimp only [aStar]; omega)
  have hsymm : ∀ j,
      norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2 <=
        norm (iteratedCovGrad (I := I) g 0 2 j P) ^ 2 := by
    intro j
    have hnorm :=
      norm_iteratedCovGrad_symmS_le (I := I) (M := M) g P j
    dsimp only [Ps]
    nlinarith [norm_nonneg
      (iteratedCovGrad (I := I) g 0 2 j
        (symmS (I := I) (M := M) g P)),
      norm_nonneg (iteratedCovGrad (I := I) g 0 2 j P)]
  have hlow :
      (∑ j ∈ Finset.range 4,
        norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2) <= A ^ 2 :=
    (Finset.sum_le_sum fun j _ => hsymm j).trans hPjet
  have hfull :
      (∑ j ∈ Finset.range 5,
        norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2) <=
        A ^ 2 + norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 := by
    rw [show 5 = 4 + 1 by omega, Finset.sum_range_succ]
    exact add_le_add hlow (hsymm 4)
  have hterm : ∀ i ∈ Finset.range 3,
      norm (iteratedCovGrad (I := I) g 2 2 i
          (lieCorr0Field (I := I) (M := M) g g1 g_bg)) ^ 2 <=
        Atop i *
            (A ^ 2 + norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2) +
          Alow i * (1 + A ^ 2) := by
    intro i hi
    have hi3 : i < 3 := Finset.mem_range.mp hi
    have htop :
        norm (iteratedCovGrad (I := I) g 0 2 (i + 2) Ps) ^ 2 <=
          A ^ 2 + norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 := by
      exact (Finset.single_le_sum
        (f := fun j =>
          norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2)
        (fun j _ => sq_nonneg _)
        (Finset.mem_range.mpr (by omega))).trans hfull
    have hwindow :
        (∑ j ∈ Finset.range (i + 2),
          norm (iteratedCovGrad (I := I) g 0 2 j Ps) ^ 2) <= A ^ 2 := by
      exact (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (by omega))
        (fun j _ _ => sq_nonneg _)).trans hlow
    exact (hperS i hi3).trans (add_le_add
      (mul_le_mul_of_nonneg_left htop (hAtop i))
      (mul_le_mul_of_nonneg_left
        (by linarith [hwindow]) (hAlow i)))
  have hsum :
      (∑ i ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g 2 2 i
          (lieCorr0Field (I := I) (M := M) g g1 g_bg)) ^ 2) <=
        ∑ i ∈ Finset.range 3,
          (Atop i *
              (A ^ 2 +
                norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2) +
            Alow i * (1 + A ^ 2)) :=
    Finset.sum_le_sum hterm
  have hinner :
      0 <= Kt * A ^ 2 + Kl * (1 + A ^ 2) :=
    add_nonneg (mul_nonneg hKt (sq_nonneg A))
      (mul_nonneg hKl (by nlinarith [sq_nonneg A]))
  calc
    (∑ i ∈ Finset.range 3,
        norm (iteratedCovGrad (I := I) g 2 2 i
          (lieCorr0Field (I := I) (M := M) g g1 g_bg)) ^ 2)
        <= ∑ i ∈ Finset.range 3,
          (Atop i *
              (A ^ 2 +
                norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2) +
            Alow i * (1 + A ^ 2)) := hsum
    _ = C4 * norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 +
        (Kt * A ^ 2 + Kl * (1 + A ^ 2)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      change Kt *
          (A ^ 2 + norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2) +
        Kl * (1 + A ^ 2) =
          C4 * norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 +
            (Kt * A ^ 2 + Kl * (1 + A ^ 2))
      dsimp only [C4]
      ring
    _ = C4 * norm (iteratedCovGrad (I := I) g 0 2 4 P) ^ 2 +
        (B A) ^ 2 := by
      rw [show (B A) ^ 2 = Kt * A ^ 2 + Kl * (1 + A ^ 2) by
        exact Real.sq_sqrt hinner]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
