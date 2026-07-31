import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCurvatureJetOne
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifDeTurckRHSZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCovSumN3
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivArityBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCurvatureJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVFEndoInsertTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicciTowerTrace
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.RoughLaplacianAppCcCommutation
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.NormBound

/-!
# The class-uniform static Ricci--DeTurck field bound at order one

This module closes the `j = 1` fibre bound needed by the static forcing
estimate.  The Ricci term is controlled by the first curvature jet.  For the
Lie term, the forward metric-jet hypotheses first give the reverse metric
jets through order three; the intrinsic connection-difference jet tower then
controls the second covariant derivative of the DeTurck covector.
-/

set_option autoImplicit false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.HCGCompactness

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
private theorem centeredBasis
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      (∀ i, basis i = smoothOrthoFrame (I := I) g x i x) ∧
      ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
  classical
  have horth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x)
          (smoothOrthoFrame (I := I) g x j x) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hli : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) => smoothOrthoFrame (I := I) g x i x) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk
    have hzero : g.inner x (smoothOrthoFrame (I := I) g x k x)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g x j x) = 0 := by
      rw [hsum]
      simp
    rw [map_sum] at hzero
    have hpull : ∀ j ∈ fs,
        g.inner x (smoothOrthoFrame (I := I) g x k x)
            (c j • smoothOrthoFrame (I := I) g x j x) =
          c j * g.inner x (smoothOrthoFrame (I := I) g x k x)
            (smoothOrthoFrame (I := I) g x j x) := by
      intro j _
      rw [(g.inner x (smoothOrthoFrame (I := I) g x k x)).map_smul,
        smul_eq_mul]
    rw [Finset.sum_congr rfl hpull] at hzero
    have hpull' : ∀ j ∈ fs,
        c j * g.inner x (smoothOrthoFrame (I := I) g x k x)
            (smoothOrthoFrame (I := I) g x j x) =
          c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [horth k j]
    rw [Finset.sum_congr rfl hpull'] at hzero
    rw [Finset.sum_eq_single_of_mem k hk] at hzero
    · simpa using hzero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard :
      Fintype.card (Fin (Module.finrank ℝ E)) =
        Module.finrank ℝ E := by
    rw [Fintype.card_fin]
  let basis := basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨basis, ?_, ?_⟩
  · intro i
    dsimp [basis]
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  · intro i j
    rw [show basis i = smoothOrthoFrame (I := I) g x i x by
        dsimp [basis]
        rw [coe_basisOfLinearIndependentOfCardEqFinrank],
      show basis j = smoothOrthoFrame (I := I) g x j x by
        dsimp [basis]
        rw [coe_basisOfLinearIndependentOfCardEqFinrank]]
    exact horth i j

set_option linter.unusedSectionVars false in
private theorem cometricTrace_eq
    (g : SmoothRiemannianMetric I M) (p : ℕ) (x : M)
    (D : Tensor0SSpace (p + 2) I x) :
    cometricDoubleTraceFib (I := I) g p x D =
      metricTraceFirstTwo0STensor (I := I) g D := by
  classical
  obtain ⟨basis, hbasis, horth⟩ := centeredBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ E))) := by
    simpa [identityInvMetric, diagonalInvMetric] using
      metricInverseInBasis_of_orthonormal (I := I) g basis horth
  apply tensor0SSpace_ext (𝕜 := ℝ) p x
  intro tail
  rw [cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g p x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) D]
  rw [metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ E))) hinv D tail]
  simp only [tensor0SSpace_sum_apply]
  simp [metricTrace0S2InBasis, identityInvMetric, diagonalInvMetric, hbasis]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_trace31
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3) (k : ℕ) :
    ∃ e : Fin (3 + k) ≃ Fin ((1 + k) + 2),
      iterCov (I := I) g 1
          (metricTraceFirstTwoField (I := I) (M := M) g A) k =
        metricTraceFirstTwoField (I := I) (M := M) g
          (MultilinearSection.domDomCongr (𝕜 := ℝ) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞) e
            (iterCov (I := I) g 3 A k)) := by
  classical
  induction k with
  | zero =>
      refine ⟨Equiv.refl _, ?_⟩
      change metricTraceFirstTwoField (I := I) (M := M) g A =
        metricTraceFirstTwoField (I := I) (M := M) g
          (MultilinearSection.domDomCongr (𝕜 := ℝ) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞) (Equiv.refl (Fin 3)) A)
      rw [MultilinearSection.domDomCongr_refl]
  | succ k ih =>
      obtain ⟨e, he⟩ := ih
      let cov := leviCivitaConnectionOfMetric (I := I) g
      have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1 := by
        exact leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
          (I := I) (M := M) g
      have hmc : IsMetricCompatible_gen (I := I) cov g := by
        exact leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
      have hA := iterCov_realizes (I := I) g A k
      have hreindex := totalNabla0SRealizes_domDomCongr (I := I) cov e _ _ hA
      have htrace := nablaRealizes_metricTraceFirstTwo (I := I) (M := M)
        (s := 1 + k) cov hcov g hmc _ _ hreindex
      rw [← he] at htrace
      have hout₀ := iterCov_realizes (I := I) g
        (metricTraceFirstTwoField (I := I) (M := M) g A) k
      have hout := Tensor0SBundle.totalNabla0SRealizes_unique (I := I) hout₀ htrace
      refine ⟨(frontExtendEquiv e).trans (traceNablaShuffle (1 + k)), ?_⟩
      rw [← MultilinearSection.domDomCongr_trans]
      exact hout

private theorem trace31_norm_le
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3) (k : ℕ) (x : M) :
    normSq0S (I := I) g x (1 + k)
        (iterCov (I := I) g 1
          (metricTraceFirstTwoField (I := I) (M := M) g A) k x) ≤
      (Module.finrank ℝ E : ℝ) ^ ((1 + k) + 2) *
        normSq0S (I := I) g x (3 + k)
          (iterCov (I := I) g 3 A k x) := by
  classical
  obtain ⟨e, he⟩ := exists_trace31 (I := I) g A k
  rw [he]
  have htrace := trace_normSq_rank_le (I := I) g
    ((MultilinearSection.domDomCongr (𝕜 := ℝ) (F := E) (IB := I)
      (E := TangentSpace I) (∞ : WithTop ℕ∞) e
      (iterCov (I := I) g 3 A k)) x)
  rw [MultilinearSection.domDomCongr_apply] at htrace
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric
        (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h' i j
  have hperm :
      normSq0S (I := I) g x ((1 + k) + 2)
          ((iterCov (I := I) g 3 A k x).domDomCongr e) =
        normSq0S (I := I) g x (3 + k)
          (iterCov (I := I) g 3 A k x) :=
    normSq0S_domDomCongr (I := I) g x basis hinv e
      (iterCov (I := I) g 3 A k x)
  rw [metricTraceFirstTwoField_apply]
  exact htrace.trans_eq
    (congrArg
      (fun z => (Module.finrank ℝ E : ℝ) ^ ((1 + k) + 2) * z) hperm)

set_option linter.unusedSectionVars false in
private theorem covStep_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    covStep (I := I) g s 0 = 0 := by
  have h := covStep_add (I := I) g s 0 0
  rw [add_zero] at h
  have h' : covStep (I := I) g s 0 + covStep (I := I) g s 0 =
      covStep (I := I) g s 0 + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h'

set_option backward.isDefEq.respectTransparency false in
private theorem iterCov_metric_zero
    (g : SmoothRiemannianMetric I M) (a : ℕ) :
    iterCov (I := I) g 2 (metricTensorField (I := I) g) (a + 1) = 0 := by
  induction a with
  | zero =>
      refine DFunLike.ext _ _ (fun x => ?_)
      refine ContinuousMultilinearMap.ext (fun slots => ?_)
      obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at_gen (I := I) (F := E)
        (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (slots 0)
      have hslots : slots = Fin.cons (X x) (Fin.tail slots) := by
        rw [hX]
        exact (Fin.cons_self_tail slots).symm
      rw [show iterCov (I := I) g 2 (metricTensorField (I := I) g) 1 =
          covStep (I := I) g 2 (metricTensorField (I := I) g) from rfl]
      rw [covStep_apply, hslots,
        totalNabla0SFun_apply_section (𝕜 := ℝ) (E := E) (H := H)
          (I := I) (M := M) 2 _ X (metricTensorField (I := I) g) x _,
        nabla_metric_zero (I := I) _ g
          (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g) X x]
      simp
  | succ a ih =>
      rw [show iterCov (I := I) g 2 (metricTensorField (I := I) g) (a + 1 + 1) =
          covStep (I := I) g (2 + (a + 1))
            (iterCov (I := I) g 2 (metricTensorField (I := I) g) (a + 1)) from rfl]
      rw [ih, covStep_zero]

private theorem iterCov_one_eq
    (g₁ g₂ : SmoothRiemannianMetric I M) (r : ℕ)
    (T : Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) :
    iterCov (I := I) g₁ r T 1 =
      iterCov (I := I) g₂ r T 1 + diffStep (I := I) g₁ g₂ r T := by
  rw [iterCov_telescoping (I := I) g₁ g₂ r T 1]
  congr 1
  change telescAccum (I := I) g₁ g₂ r T 1 = diffStep (I := I) g₁ g₂ r T
  simp only [telescAccum]
  rw [covStep_zero, zero_add]
  rfl

set_option linter.unusedSectionVars false in
private theorem metric_self_norm
    (g : SmoothRiemannianMetric I M) (x : M) :
    normSq0S (I := I) g x 2 (metricTensorField (I := I) g x) =
      (Module.finrank ℝ E : ℝ) := by
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    simpa [identityInvMetric, diagonalInvMetric] using
      metricInverseInBasis_of_orthonormal (I := I) g basis hON
  simpa using normSq0S_metricTensor0S_eq_card (I := I) g basis
    (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) hinv

set_option linter.unusedSectionVars false in
private theorem sqrt_normSq_zero
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ) :
    Real.sqrt (normSq0S (I := I) g x s
      (0 : Tensor0SSpace s I x)) = 0 := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    intro i j
    constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv]
  rw [show (∑ slots : Fin s → Fin (Module.finrank ℝ (TangentSpace I x)),
      (component0S (I := I) basis (0 : Tensor0SSpace s I x) slots) ^ 2) = 0 from ?_]
  · exact Real.sqrt_zero
  · refine Finset.sum_eq_zero (fun slots _ => ?_)
    rw [component0S_apply]
    simp

set_option linter.unusedSectionVars false in
private theorem metric_self_sum
    (g : SmoothRiemannianMetric I M) (x : M) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1),
        Real.sqrt (normSq0S (I := I) g x (2 + k)
          (iterCov (I := I) g 2 (metricTensorField (I := I) g) k x)) =
      Real.sqrt (Module.finrank ℝ E : ℝ) := by
  classical
  rw [Finset.sum_eq_single 0]
  · change Real.sqrt
        (normSq0S (I := I) g x 2 (metricTensorField (I := I) g x)) =
      Real.sqrt (Module.finrank ℝ E : ℝ)
    rw [metric_self_norm (I := I) g x]
  · intro k hk hk0
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    rw [iterCov_metric_zero (I := I) g a]
    exact sqrt_normSq_zero (I := I) g x _
  · simp

private theorem reverseJetOne
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀ C := by
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hEq.1
  let C : ℝ :=
    2 * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) *
      ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ)) *
      (Real.sqrt (Λ ^ 2) * Real.sqrt (Module.finrank ℝ E : ℝ))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC0, ?_⟩
  intro x _
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g₀ x
  have hinv : MetricInverseInBasis_gen (I := I) g₀ x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) :=
    metricInverseInBasis_of_orthonormal (I := I) g₀ basis hON
  rw [metricCovDerivNorm_eq_iterCov (I := I) gBase g₀ 1 basis hinv]
  have htel := iterCov_one_eq (I := I) gBase g₀ 2
    (metricTensorField (I := I) gBase)
  have hself := iterCov_metric_zero (I := I) gBase 0
  rw [hself] at htel
  have hfield :
      iterCov (I := I) g₀ 2 (metricTensorField (I := I) gBase) 1 =
        -diffStep (I := I) gBase g₀ 2
          (metricTensorField (I := I) gBase) :=
    eq_neg_of_add_eq_zero_left htel.symm
  have hneg :
      iterCov (I := I) g₀ 2 (metricTensorField (I := I) gBase) 1 x =
        -(diffStep (I := I) gBase g₀ 2 (metricTensorField (I := I) gBase) x) := by
    exact congrArg (fun S => S x) hfield
  rw [hneg, normSq0S_neg]
  have hstep := diffStep_jet_one_le (I := I) gBase g₀ 2
    (metricTensorField (I := I) gBase) hEq hjet1 (Set.mem_univ x)
  have hmetric := sqrt_normSq0S_comp (I := I) hEq (Set.mem_univ x) 2
    (metricTensorField (I := I) gBase x)
  rw [metric_self_norm (I := I) gBase x] at hmetric
  refine hstep.trans ?_
  dsimp [C]
  exact mul_le_mul_of_nonneg_left hmetric (by positivity)

private theorem reverseJetTwo
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      MetricCovDerivOrderBoundOn (I := I) Set.univ 2 gBase g₀ C := by
  obtain ⟨C₁, _hC₁0, hrev1⟩ := reverseJetOne (I := I) gBase g₀ hEq hjet1
  let L₁ : ℝ := max C₁ Λ
  have hrev1' :
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀ L₁ :=
    fun x hx => (hrev1 x hx).trans (le_max_left _ _)
  have hfwd1' :
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase L₁ :=
    fun x hx => (hjet1 x hx).trans (le_max_right _ _)
  let D : ℝ :=
    Dtower (Module.finrank ℝ E)
      ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * L₁)) 2
      (fun m => if m = 1 then
        (2 : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (2 + 2)) *
          (3 / 2 * Λ ^ 4 * (Λ + Λ * L₁ ^ 2) +
            (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * L₁))
        else 0) 2
  let C : ℝ :=
    max 0 (Real.sqrt (Λ ^ 4) *
      (D * Real.sqrt (Module.finrank ℝ E : ℝ)))
  refine ⟨C, le_max_left _ _, ?_⟩
  intro x _
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g₀ x
  have hinv : MetricInverseInBasis_gen (I := I) g₀ x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) :=
    metricInverseInBasis_of_orthonormal (I := I) g₀ basis hON
  rw [metricCovDerivNorm_eq_iterCov (I := I) gBase g₀ 2 basis hinv]
  have hcomp := sqrt_normSq0S_comp (I := I) hEq (Set.mem_univ x) 4
    (iterCov (I := I) g₀ 2 (metricTensorField (I := I) gBase) 2 x)
  have htwo := iterCovG1_two (I := I) g₀ gBase 2
    (metricTensorField (I := I) gBase) x
    (metricUniformEquivalentOn_symm (I := I) hEq)
    hrev1' hfwd1' hjet2 (Set.mem_univ x)
  rw [metric_self_sum (I := I) gBase x 2] at htwo
  have htwo' :
      Real.sqrt (normSq0S (I := I) gBase x 4
        (iterCov (I := I) g₀ 2 (metricTensorField (I := I) gBase) 2 x)) ≤
        D * Real.sqrt (Module.finrank ℝ E : ℝ) := by
    simpa [D, L₁] using htwo
  refine hcomp.trans ((mul_le_mul_of_nonneg_left htwo'
    (Real.sqrt_nonneg _)).trans ?_)
  exact le_max_right _ _

private theorem reverseJetThree
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      MetricCovDerivOrderBoundOn (I := I) Set.univ 3 gBase g₀ C := by
  obtain ⟨C₁, _hC₁0, hrev1⟩ := reverseJetOne (I := I) gBase g₀ hEq hjet1
  let L₁ : ℝ := max C₁ Λ
  have hrev1' :
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀ L₁ :=
    fun x hx => (hrev1 x hx).trans (le_max_left _ _)
  have hfwd1' :
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase L₁ :=
    fun x hx => (hjet1 x hx).trans (le_max_right _ _)
  obtain ⟨D, hD0, hD⟩ := iterCovG1_three (I := I) (K := Set.univ)
    g₀ gBase 2 (metricUniformEquivalentOn_symm (I := I) hEq)
      hrev1' hfwd1' hjet2 hjet3
  let C : ℝ := Real.sqrt (Λ ^ 5) *
    (D * Real.sqrt (Module.finrank ℝ E : ℝ))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC0, ?_⟩
  intro x _
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g₀ x
  have hinv : MetricInverseInBasis_gen (I := I) g₀ x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) :=
    metricInverseInBasis_of_orthonormal (I := I) g₀ basis hON
  rw [metricCovDerivNorm_eq_iterCov (I := I) gBase g₀ 3 basis hinv]
  have hcomp := sqrt_normSq0S_comp (I := I) hEq (Set.mem_univ x) 5
    (iterCov (I := I) g₀ 2 (metricTensorField (I := I) gBase) 3 x)
  have hthree := hD (metricTensorField (I := I) gBase) x (Set.mem_univ x)
  rw [metric_self_sum (I := I) gBase x 3] at hthree
  have hthree' :
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) g₀ 2 (metricTensorField (I := I) gBase) 3 x)) ≤
        D * Real.sqrt (Module.finrank ℝ E : ℝ) := by
    simpa using hthree
  refine hcomp.trans ?_
  simpa [C] using
    (mul_le_mul_of_nonneg_left hthree' (Real.sqrt_nonneg (Λ ^ 5)))

set_option linter.unusedSectionVars false in
private theorem metricDiff_rfns_zero
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * g₀.inner x v v ≤ gBase.inner x v v ∧
        gBase.inner x v v ≤ Λ * g₀.inner x v v)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((metricDifferenceCcTensor (I := I) (M := M) g₀ gBase).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * (Λ - 1)) ^ 2 := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
  have hnorm := metricDiff_order0_bound (I := I) g₀ gBase hΛ hcomp x
  have hbridge := norm_toSection_eq_sqrt_riemannianFiberNormSq
    (I := I) (M := M) g₀ 0 2 x
      (metricDifferenceCcTensor (I := I) (M := M) g₀ gBase)
  have hroot :
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((metricDifferenceCcTensor (I := I) (M := M) g₀ gBase).toSection x)) ≤
        (Module.finrank ℝ E : ℝ) * (Λ - 1) := by
    rw [← hbridge]
    exact hnorm
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
  rwa [Real.sq_sqrt
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x _)] at hp

set_option linter.unusedSectionVars false in
private theorem metricDiff_rfns_pos
    (gBase g₀ : SmoothRiemannianMetric I M) (a : ℕ) {C : ℝ}
    (hjet : MetricCovDerivOrderBoundOn (I := I) Set.univ (a + 1)
      gBase g₀ C)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (a + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (a + 1)
          (metricDifferenceCcTensor (I := I) (M := M) g₀ gBase)).toSection x) ≤
      C ^ 2 := by
  letI : Bundle.RiemannianBundle
      (fun b : M => TensorRSSpace 0 (2 + (a + 1)) I b) :=
    tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + (a + 1))
  have hnorm := metricDiff_orderPos_bound (I := I) g₀ gBase a hjet x
  have hbridge := norm_toSection_eq_sqrt_riemannianFiberNormSq
    (I := I) (M := M) g₀ 0 (2 + (a + 1)) x
      (iteratedCovGrad (I := I) g₀ 0 2 (a + 1)
        (metricDifferenceCcTensor (I := I) (M := M) g₀ gBase))
  have hroot :
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀
        0 (2 + (a + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (a + 1)
            (metricDifferenceCcTensor (I := I) (M := M) g₀ gBase)).toSection x)) ≤
        C := by
    rw [← hbridge]
    exact hnorm
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
  rwa [Real.sq_sqrt
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀
      0 (2 + (a + 1)) x _)] at hp

private theorem unifConnDiffTwo
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (hΛ2 : Λ < 2)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 2) x
          ((iteratedCovGrad (I := I) g₀ 1 2 2
            (connDiffSection (I := I) gBase g₀)).toSection x) ≤ K := by
  classical
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ :=
    ⟨hΛ, fun x _ v => hcomp x v⟩
  have hEq' := metricUniformEquivalentOn_symm (I := I) hEq
  have hcomp' : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * g₀.inner x v v ≤ gBase.inner x v v ∧
        gBase.inner x v v ≤ Λ * g₀.inner x v v :=
    fun x v => hEq'.2 x (Set.mem_univ x) v
  obtain ⟨C₁, hC₁0, hrev1⟩ :=
    reverseJetOne (I := I) gBase g₀ hEq hjet1
  obtain ⟨C₂, hC₂0, hrev2⟩ :=
    reverseJetTwo (I := I) gBase g₀ hEq hjet1 hjet2
  obtain ⟨C₃, hC₃0, hrev3⟩ :=
    reverseJetThree (I := I) gBase g₀ hEq hjet1 hjet2 hjet3
  have hδtop : Λ - 1 < 1 := by linarith
  have hδ0 : 0 ≤ Λ - 1 := by linarith
  obtain ⟨CA, hCA0, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid
      (I := I) (M := M) g₀ hδtop
  have hbound := metricDiff_gFibreOpBound (I := I) g₀ gBase hΛ hcomp'
  let B₀ : ℝ := (Module.finrank ℝ E : ℝ) * (Λ - 1)
  let Q : ℝ := max 1 (B₀ ^ 2 + C₁ ^ 2 + C₂ ^ 2 + C₃ ^ 2)
  have hQ1 : 1 ≤ Q := le_max_left _ _
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ1
  let F : ℝ := Q ^ 3
  have hF0 : 0 ≤ F := pow_nonneg hQ0 _
  let cnt : ℝ :=
    ∑ k ∈ Finset.range 4, ∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)
  have hcnt0 : 0 ≤ cnt := by
    dsimp [cnt]
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
      (fun _ _ => Nat.cast_nonneg _))
  let K : ℝ := CA 2 * (cnt * F)
  have hK0 : 0 ≤ K :=
    mul_nonneg (hCA0 2) (mul_nonneg hcnt0 hF0)
  refine ⟨K, hK0, ?_⟩
  intro x
  let b : ℕ → ℝ := fun j =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j
        (metricDifferenceCcTensor (I := I) (M := M) g₀ gBase)).toSection x)
  have hb0 : ∀ j, 0 ≤ b j := fun j =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hbQ : ∀ j, j ≤ 3 → b j ≤ Q := by
    intro j hj
    have hsumQ :
        B₀ ^ 2 + C₁ ^ 2 + C₂ ^ 2 + C₃ ^ 2 ≤ Q :=
      le_max_right _ _
    interval_cases j
    · have h := metricDiff_rfns_zero (I := I) gBase g₀ hΛ hcomp' x
      change b 0 ≤ B₀ ^ 2 at h
      exact h.trans (by
        calc
          B₀ ^ 2 ≤ B₀ ^ 2 + C₁ ^ 2 + C₂ ^ 2 + C₃ ^ 2 := by
            nlinarith [sq_nonneg C₁, sq_nonneg C₂, sq_nonneg C₃]
          _ ≤ Q := hsumQ)
    · have h := metricDiff_rfns_pos (I := I) gBase g₀ 0 hrev1 x
      change b 1 ≤ C₁ ^ 2 at h
      exact h.trans (by
        calc
          C₁ ^ 2 ≤ B₀ ^ 2 + C₁ ^ 2 + C₂ ^ 2 + C₃ ^ 2 := by
            nlinarith [sq_nonneg B₀, sq_nonneg C₂, sq_nonneg C₃]
          _ ≤ Q := hsumQ)
    · have h := metricDiff_rfns_pos (I := I) gBase g₀ 1 hrev2 x
      change b 2 ≤ C₂ ^ 2 at h
      exact h.trans (by
        calc
          C₂ ^ 2 ≤ B₀ ^ 2 + C₁ ^ 2 + C₂ ^ 2 + C₃ ^ 2 := by
            nlinarith [sq_nonneg B₀, sq_nonneg C₁, sq_nonneg C₃]
          _ ≤ Q := hsumQ)
    · have h := metricDiff_rfns_pos (I := I) gBase g₀ 2 hrev3 x
      change b 3 ≤ C₃ ^ 2 at h
      exact h.trans (by
        calc
          C₃ ^ 2 ≤ B₀ ^ 2 + C₁ ^ 2 + C₂ ^ 2 + C₃ ^ 2 := by
            nlinarith [sq_nonneg B₀, sq_nonneg C₁, sq_nonneg C₂]
          _ ≤ Q := hsumQ)
  have hprod : ∀ k ∈ Finset.range 4, ∀ n ∈ Finset.range (k + 1),
      ∀ e ∈ Finset.Nat.antidiagonalTuple n k,
        (∏ m : Fin n, b (e m)) ≤ F := by
    intro k hk n hn e he
    have hk3 : k ≤ 3 := by
      rw [Finset.mem_range] at hk
      omega
    have hn3 : n ≤ 3 := by
      rw [Finset.mem_range] at hn
      omega
    have hsum_e : (∑ m : Fin n, e m) = k :=
      Finset.Nat.mem_antidiagonalTuple.mp he
    have hem : ∀ m : Fin n, e m ≤ 3 := by
      intro m
      have hle : e m ≤ ∑ i : Fin n, e i :=
        Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ m)
      omega
    have hstep : (∏ m : Fin n, b (e m)) ≤ ∏ _m : Fin n, Q :=
      Finset.prod_le_prod
        (fun m _ => hb0 (e m))
        (fun m _ => hbQ (e m) (hem m))
    refine hstep.trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    change Q ^ n ≤ Q ^ 3
    exact pow_le_pow_right₀ hQ1 hn3
  have hgrid :
      (∑ k ∈ Finset.range 4, Combinatorics.antidiagonalTupleGrid b k) ≤
        cnt * F := by
    change (∑ k ∈ Finset.range 4, ∑ n ∈ Finset.range (k + 1),
      ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
        ∏ m : Fin n, b (e m)) ≤ cnt * F
    rw [show cnt = ∑ k ∈ Finset.range 4, ∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ) from rfl, Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun n hn => ?_)
    calc
      (∑ e ∈ Finset.Nat.antidiagonalTuple n k, ∏ m : Fin n, b (e m))
          ≤ ∑ _e ∈ Finset.Nat.antidiagonalTuple n k, F :=
        Finset.sum_le_sum (fun e he => hprod k hk n hn e he)
      _ = (Finset.Nat.antidiagonalTuple n k).card • F :=
        Finset.sum_const F
      _ = ((Finset.Nat.antidiagonalTuple n k).card : ℝ) * F :=
        nsmul_eq_mul _ _
  have hraw := hCA gBase
    (metricDifferenceCcTensor (I := I) (M := M) g₀ gBase)
    (metricDiff_tie (I := I) g₀ gBase) (δ := Λ - 1)
    le_rfl hδ0 hbound 2 x
  have hraw' :
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 2) x
          ((iteratedCovGrad (I := I) g₀ 1 2 2
            (connDiffSection (I := I) gBase g₀)).toSection x) ≤
        CA 2 * ∑ k ∈ Finset.range 4,
          Combinatorics.antidiagonalTupleGrid b k := by
    simpa [b] using hraw
  exact hraw'.trans
    ((mul_le_mul_of_nonneg_left hgrid (hCA0 2)).trans_eq rfl)

private theorem connLow_self_zero
    (g : SmoothRiemannianMetric I M) :
    connDiffLoweredCc (I := I) g g = 0 := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  change unitModel (I := I) (M := M) g 3
      (connDiffLoweredCc (I := I) g g) x m = 0
  rw [connDiffLoweredCc_unitModel_apply']
  rw [PDE.DeTurck.connDiff_self]
  simp

private theorem wXi_base_eq
    (gBase g₀ : SmoothRiemannianMetric I M) :
    wXi (I := I) (M := M) g₀ g₀ gBase =
      -connDiffLoweredCc (I := I) g₀ gBase := by
  unfold wXi
  rw [connLow_self_zero (I := I) g₀, zero_sub]

private theorem cometricCast_self
    (g : SmoothRiemannianMetric I M) :
    cometricCastG0 (I := I) g g =
      cometricDoubleTraceField (I := I) g 1 := by
  apply SmoothCcTensor.ext
  rfl

private theorem wOmega_base_eq
    (gBase g₀ : SmoothRiemannianMetric I M) :
    wOmega (I := I) (M := M) g₀ g₀ gBase =
      appCc (I := I) (M := M) g₀ 3 1
        (cometricDoubleTraceField (I := I) g₀ 1)
        (-connDiffLoweredCc (I := I) g₀ gBase) := by
  unfold wOmega
  rw [wXi_base_eq (I := I) gBase g₀, cometricCast_self (I := I) g₀]

private theorem wOmega_trace
    (gBase g₀ : SmoothRiemannianMetric I M) :
    ccUnitField (I := I) g₀ 1
        (wOmega (I := I) (M := M) g₀ g₀ gBase) =
      metricTraceFirstTwoField (I := I) (M := M) g₀
        (ccUnitField (I := I) g₀ 3
          (-connDiffLoweredCc (I := I) g₀ gBase)) := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [wOmega_base_eq (I := I) gBase g₀]
  rw [ccUnitField_apply, appCc_toSection, ContinuousLinearMap.comp_apply,
    metricTraceFirstTwoField_apply, ccUnitField_apply,
    cometricDoubleTraceField_toSection]
  exact cometricTrace_eq (I := I) g₀ 1 x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (-connDiffLoweredCc (I := I) g₀ gBase).toSection x)
      (unitZeroSec (I := I) (M := M) x))

private theorem wAlphaA_shift
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i
          (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 1 (i + 1)
          (wOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
  calc
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i
          (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i
          (covGrad (I := I) (M := M) g₀ 0 1
            (wOmega (I := I) (M := M) g₀ g₁ g_bg))).toSection x) := by
          rw [wAlphaA]
          exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
            (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1)
            (covGrad (I := I) (M := M) g₀ 0 1
              (wOmega (I := I) (M := M) g₀ g₁ g_bg)) i x
    _ =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 1 (i + 1)
          (wOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x) :=
      rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 1 i
        (wOmega (I := I) (M := M) g₀ g₁ g_bg) x

set_option linter.unusedSectionVars false in
private theorem rfns_neg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise
      (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise
      (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
      (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

set_option linter.unusedSectionVars false in
private theorem unifOmegaTwo
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (hΛ2 : Λ < 2)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 1 2
          (wOmega (I := I) (M := M) g₀ g₀ gBase)).toSection x) ≤ K ^ 2 := by
  obtain ⟨KC, hKC0, hC⟩ :=
    unifConnDiffTwo (I := I) gBase g₀ hΛ hΛ2 hcomp hjet1 hjet2 hjet3
  let d : ℝ := Module.finrank ℝ E
  let K : ℝ := Real.sqrt (d ^ 5 * KC)
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK0, ?_⟩
  intro x
  rw [rfns_iterCovGrad_eq (I := I) g₀ 1 2
    (wOmega (I := I) (M := M) g₀ g₀ gBase) x,
    wOmega_trace (I := I) gBase g₀]
  calc
    normSq0S (I := I) g₀ x (1 + 2)
        (iterCov (I := I) g₀ 1
          (metricTraceFirstTwoField (I := I) (M := M) g₀
            (ccUnitField (I := I) g₀ 3
              (-connDiffLoweredCc (I := I) g₀ gBase))) 2 x)
        ≤ d ^ 5 *
          normSq0S (I := I) g₀ x (3 + 2)
            (iterCov (I := I) g₀ 3
              (ccUnitField (I := I) g₀ 3
                (-connDiffLoweredCc (I := I) g₀ gBase)) 2 x) := by
          simpa [d] using trace31_norm_le (I := I) g₀
            (ccUnitField (I := I) g₀ 3
              (-connDiffLoweredCc (I := I) g₀ gBase)) 2 x
    _ = d ^ 5 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 2) x
          ((iteratedCovGrad (I := I) g₀ 0 3 2
            (-connDiffLoweredCc (I := I) g₀ gBase)).toSection x) := by
          rw [rfns_iterCovGrad_eq (I := I) g₀ 3 2
            (-connDiffLoweredCc (I := I) g₀ gBase) x]
    _ = d ^ 5 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 2) x
          ((iteratedCovGrad (I := I) g₀ 0 3 2
            (connDiffLoweredCc (I := I) g₀ gBase)).toSection x) := by
          congr 1
          rw [iteratedCovGrad_neg]
          rw [show
            ((-(iteratedCovGrad (I := I) g₀ 0 3 2
              (connDiffLoweredCc (I := I) g₀ gBase))).toSection x) =
              -((iteratedCovGrad (I := I) g₀ 0 3 2
                (connDiffLoweredCc (I := I) g₀ gBase)).toSection x) from by
                rw [SmoothCcTensor.toSection_neg]
                rfl]
          exact rfns_neg (I := I) g₀ 0 (3 + 2) x _
    _ = d ^ 5 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 2) x
          ((iteratedCovGrad (I := I) g₀ 1 2 2
            (connDiffSection (I := I) gBase g₀)).toSection x) := by
          rw [connLow_rfns (I := I) (M := M) g₀ gBase 2 x]
    _ ≤ d ^ 5 * KC :=
      mul_le_mul_of_nonneg_left (hC x) (pow_nonneg hd0 5)
    _ = K ^ 2 := by
      dsimp [K]
      rw [Real.sq_sqrt (mul_nonneg (pow_nonneg hd0 5) hKC0)]

set_option linter.unusedSectionVars false in
private theorem unifAlphaOne
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (hΛ2 : Λ < 2)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1
          (wAlphaA (I := I) (M := M) g₀ g₀ gBase)).toSection x) ≤ K ^ 2 := by
  obtain ⟨K, hK0, hK⟩ :=
    unifOmegaTwo (I := I) gBase g₀ hΛ hΛ2 hcomp hjet1 hjet2 hjet3
  refine ⟨K, hK0, ?_⟩
  intro x
  rw [wAlphaA_shift (I := I) g₀ g₀ gBase 1 x]
  simpa using hK x

set_option linter.unusedSectionVars false in
private theorem unifRicOne
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (hΛ2 : Λ < 2)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1
          (ccOfField (I := I) g₀ 2
            (metricRicci (I := I) (M := M) g₀))).toSection x) ≤ K ^ 2 := by
  obtain ⟨KR, _hKR0, hRm⟩ :=
    unifRmSecOne (I := I) (M := M) gBase g₀
      hΛ hΛ2 hcomp hjet1 hjet2 hjet3
  let d : ℝ := Module.finrank ℝ E
  let K : ℝ := Real.sqrt (d ^ 5 * KR ^ 2)
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK0, ?_⟩
  intro x
  have hcan :
      metricRicci (I := I) (M := M) g₀ =
        trace04Field (I := I) (M := M) g₀
          (metricRm04 (I := I) (M := M) g₀) := by
    simpa [metricRicci, metricRm04, metricCov] using
      (canRicField (I := I) (M := M) g₀)
  rw [rfns_iterCovGrad_eq (I := I) g₀ 2 1
      (ccOfField (I := I) g₀ 2
        (metricRicci (I := I) (M := M) g₀)) x,
    ccOfField_unit, hcan]
  calc
    normSq0S (I := I) g₀ x (2 + 1)
        (iterCov (I := I) g₀ 2
          (trace04Field (I := I) (M := M) g₀
            (metricRm04 (I := I) (M := M) g₀)) 1 x)
        ≤ d ^ 5 *
          normSq0S (I := I) g₀ x (4 + 1)
            (iterCov (I := I) g₀ 4
              (metricRm04 (I := I) (M := M) g₀) 1 x) := by
          simpa [d] using
            (iterRic_normSq_le (I := I) g₀
              (metricRm04 (I := I) (M := M) g₀) 1 x)
    _ = d ^ 5 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 4 1
            (rmSection (I := I) (M := M) g₀)).toSection x) := by
          rw [rfns_rmSection_eq (I := I) g₀ 1 x]
    _ ≤ d ^ 5 * KR ^ 2 :=
      mul_le_mul_of_nonneg_left (hRm x) (pow_nonneg hd0 5)
    _ = K ^ 2 := by
      dsimp [K]
      rw [Real.sq_sqrt (mul_nonneg (pow_nonneg hd0 5) (sq_nonneg KR))]

end RicciFlow
end PDE
end DifferentialGeometry

end
