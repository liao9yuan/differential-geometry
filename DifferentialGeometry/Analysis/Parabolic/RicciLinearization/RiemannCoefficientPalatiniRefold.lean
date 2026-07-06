import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs

/-!
# Palatini refold of the Riemann and Lie coefficients along the Ricci-linearization path

The second-gradient refold of the moving order-zero coefficients along the realized metric
path at second endpoint zero: the covariant-gradient-of-connection-difference content of the
moving Riemann coefficient (and of the DeTurck Lie arms) is re-expressed as a rank-`(4,2)`
coefficient acting on the two-step gradient of the moving tensor, with the remaining
background-curvature, quadratic connection-difference, and one-jet sharp-gradient content
collected into a rank-`(2,2)` part acting on the zeroth gradient.

The constructed second-gradient families (`riemannPalatiniRefoldC2Family`) instantiate the
generic folded four-monomial kernel calculus of
`Geometry/Connection/TensorNabla/OperatorFieldSecondGradientRefold` at the realized metric
family, with the moving tensor's unit value as coefficient weight.

The refold identities and their estimates are posited here as clearly-labelled deferred
inputs (`sorry`) with consumer-minimal statements: they are the children of the frozen
Riemann-arm (`RA`) and Lie-correction (`LC`) refold data statements of the DeTurck remainder
tame-Lipschitz development, per the leader-signed RA/LC fill-architecture dossier. Every
consumer transitively depends on `sorryAx` until they land.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The unit value section of a rank-`(0,2)` coefficient tensor: the rank-two tensor field
obtained by feeding the unit rank-zero tensor into the coefficient, fibrewise. This is the
section-level carrier of `unitModel`. -/
def ccTensorUnitValueSection (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    Π y : M, Tensor0SSpace 2 I y :=
  fun y =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from T.toSection y)
      (unitZeroSec (I := I) (M := M) y)

theorem ccTensorUnitValueSection_contMDiff (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) y
        (ccTensorUnitValueSection (I := I) (M := M) g T y)) := by
  exact ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel 2 ℝ E)
    (E₁ := fun z : M => Tensor0SSpace 0 I z)
    (E₂ := fun z : M => Tensor0SSpace 2 I z)
    (IM := I) (IB := I) (b := id)
    (ϕ := fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from T.toSection y))
    (v := fun y : M => unitZeroSec (I := I) (M := M) y)
    T.toSection.contMDiff (unitZeroSec (I := I) (M := M)).contMDiff

/-- The constructed second-gradient refold family for the Riemann arm at second endpoint
zero: the moving tensor's unit value weights the folded four-monomial second-Bianchi kernel
at the realized metric's orthonormal frames, averaged over the two symmetrization slot
conventions `qA`, `qB` (the `symmS` partner bookkeeping) and scaled by the path parameter
(the connection-difference rate at second endpoint zero). The exact permutation quadruples
are pinned by the refold identity child below. -/
def riemannPalatiniRefoldC2Family (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) (s : ℝ) : SmoothCcTensor g₀ 4 2 :=
  s • ((1 / 2 : ℝ) •
    (curvatureRefoldKernelCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
        (qA 0) (qA 1) (qA 2) (qA 3)
      + curvatureRefoldKernelCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
        (qB 0) (qB 1) (qB 2) (qB 3)))

set_option linter.unusedSectionVars false in
/-- The constructed second-gradient family vanishes at path parameter zero: the refold
carries the connection-difference rate, which vanishes at the path's first endpoint. -/
@[simp] lemma riemannPalatiniRefoldC2Family_zero (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) :
    riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB 0 = 0 := by
  rw [riemannPalatiniRefoldC2Family, zero_smul]

/-- The `symmS` partner pairing of two slot-pattern quadruples for the folded four-monomial
refold kernel: each pattern of the second quadruple is the frame-pair swap of the
corresponding pattern of the first, where `Equiv.swap 0 1` acts on the two leading argument
slots — the slots that receive the orthonormal frame pair. Under this pairing the half-sum
of the two kernels sees the weight tensor only through its symmetrization: by
`curvatureRefoldMonomialFib_toModel`, the monomial at pattern `σ` and frames `(q, p)` equals
the monomial at pattern `Equiv.swap 0 1 * σ` and frames `(p, q)`, so the `a ↔ b` reindex of
the double frame sum averages the weight over its two slots, i.e. replaces the raw moving
tensor by `ccTensorBilinSymm`. This is the structural condition under which the
connection-difference-rate caps of the refold estimates hold; unpaired quadruple pairs see
the raw antisymmetric weight content, which the symmetrized smallness `gFibreOpBound`
hypothesis does not control. -/
def IsFramePairPartner (qA qB : Fin 4 → Equiv.Perm (Fin 4)) : Prop :=
  ∀ k : Fin 4, qB k = Equiv.swap (0 : Fin 4) 1 * qA k

/-- Vacuity litmus: the partner pairing rejects every diagonal witness — no quadruple is its
own partner. In particular the unpaired convention `qA = qB` behind the antisymmetric-weight
refutation of the ∀-independent estimate forms is excluded. -/
lemma not_isFramePairPartner_self (q : Fin 4 → Equiv.Perm (Fin 4)) :
    ¬ IsFramePairPartner q q := by
  intro h
  have h0 : Equiv.swap (0 : Fin 4) 1 = 1 := right_eq_mul.mp (h 0)
  have h1 : (Equiv.swap (0 : Fin 4) 1) 0 = (1 : Equiv.Perm (Fin 4)) 0 := by rw [h0]
  rw [Equiv.swap_apply_left, Equiv.Perm.one_apply] at h1
  exact absurd h1 (by decide)

/-- The covariant-derivative arm of the DeTurck Lie coefficient as a standalone smooth
compactly supported `(2,2)` coefficient field (the `dLaBiContrFib` bi-contraction). -/
def deTurckLieCovDerivArmField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (dLaBiContrFib (I := I) g₁ g_bg x))
      contMDiff_toFun := dLaBiContrFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem deTurckLieCovDerivArmField_toSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieCovDerivArmField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (dLaBiContrFib (I := I) g₁ g_bg x)) := rfl

/-- The vector-field endomorphism arm of the DeTurck Lie coefficient as a standalone smooth
compactly supported `(2,2)` coefficient field (the slot-inserted `deTurckLieWEndo`). -/
def deTurckLieEndoArmField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x))
      contMDiff_toFun := deTurckLieDLbFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem deTurckLieEndoArmField_toSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x)) := rfl

set_option linter.unusedSectionVars false in
/-- The DeTurck Lie coefficient decomposes as the sum of its covariant-derivative arm and
its vector-field endomorphism arm. -/
theorem deTurckLieCoeffField_eq_covDerivArm_add_endoArm
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieCovDerivArmField (I := I) (M := M) g₀ g₁ g_bg
        + deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg := by
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    deTurckLieCoeffField_toSection, deTurckLieCovDerivArmField_toSection,
    deTurckLieEndoArmField_toSection]
  rfl

set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- Dossier row RA-3b (conjunct 5 of the frozen Riemann-arm refold data): pointwise
fibre-norm sup for the moving order-zero Riemann coefficient along the realized path,
uniform over the moving tensor's `a + 2`-jet ball. The moving coefficient splits as the
background coefficient plus the background difference; the difference is capped at grid
order zero by the background-difference diagonal-product grid of
`CurvatureCoefficientDifferenceJetTower`, whose grid cells (jets of the convex-perturbation
tensor up to order two) are absorbed pointwise by the `Csob` convex-perturbation `C²`
Sobolev bound on the jet ball, while the background part is capped by the compact-manifold
uniform fibre-norm bound. -/
theorem exists_ricciArmOrder0RiemannCoeff_realizedFam_rfns_ballUniform_sq
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) ≤ Λ ^ 2 := by
  classical
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ (max_lt hδ₀ one_pos)
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_Csob_convexPerturbation_pointwise_C2_le (I := I) (M := M) g₀ a ha_super
  obtain ⟨Kbg, hKbg_nn, hKbg_bd⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
  set F : ℝ := (1 + (Csob * R) ^ 2) ^ 2 with hF_def
  have hF_nn : (0 : ℝ) ≤ F := by positivity
  set cnt : ℝ := ∑ k ∈ Finset.range 3, ∑ n ∈ Finset.range (k + 1),
    ((Finset.Nat.antidiagonalTuple n k).card : ℝ) with hcnt_def
  have hcnt_nn : (0 : ℝ) ≤ cnt :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun n _ => Nat.cast_nonneg _
  have hsum_nn : (0 : ℝ) ≤ 2 * (CD 0 * (cnt * F)) + 2 * Kbg := by
    have h1 : (0 : ℝ) ≤ CD 0 * (cnt * F) :=
      mul_nonneg (hCD_nn 0) (mul_nonneg hcnt_nn hF_nn)
    linarith
  refine ⟨Real.sqrt (2 * (CD 0 * (cnt * F)) + 2 * Kbg), Real.sqrt_nonneg _, ?_⟩
  intro T δ hδ_le hδ hδZ hTball s hs x
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    abs_convex_smallConstant_lt_one hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
  set m : ℝ := max δ₀ 0 with hm_def
  have hm0 : (0 : ℝ) ≤ m := le_max_right _ _
  have hδs_raw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s
  obtain ⟨hs0, hs1⟩ := hs
  have habs_eq : |1 - s| * δ + |s| * δ = (1 - s) * δ + s * δ := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
  have hsmall_le : (1 - s) * δ + s * δ ≤ m := by
    have hδ₀_le : δ₀ ≤ m := le_max_left _ _
    have heq : (1 - s) * δ + s * δ = δ := by ring
    linarith
  have hδP : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) m := by
    intro y v w
    refine le_trans (hδs_raw y v w) ?_
    have hprod : 0 ≤ Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hle' : |1 - s| * δ + |s| * δ ≤ m := by rw [habs_eq]; exact hsmall_le
    nlinarith [hle', hprod]
  have hCD0 := hCD (realizedFam (I := I) g₀ T 0 hδ hδZ s)
    (convexPerturbation (I := I) g₀ T 0 s) htie (le_of_eq hm_def) hm0 hδP 0 x
  have hicg0 : ∀ j : ℕ,
      iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) = 0 := by
    intro j
    have h := iteratedCovGrad_sub (I := I) g₀ 0 2 j T T
    simp only [sub_self] at h
    exact h
  have hZball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j _
    rw [hicg0 j, norm_zero]
    exact hR
  have hCsob_sum := hCsob T 0 hR hTball hZball s ⟨hs0, hs1⟩ x
  have hterm_nn : ∀ j ∈ Finset.range 3, 0 ≤
      (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
      ‖(iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T 0 s)).toSection x‖) := by
    intro j _
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
    exact norm_nonneg _
  have hcell : ∀ j : ℕ, j < 3 →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j
            (convexPerturbation (I := I) g₀ T 0 s)).toSection x) ≤
        1 + (Csob * R) ^ 2 := by
    intro j hj
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
    have hbridge := norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M)
      g₀ 0 (2 + j) x
      (iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T 0 s))
    have hnorm_le : ‖((iteratedCovGrad (I := I) g₀ 0 2 j
        (convexPerturbation (I := I) g₀ T 0 s)).toSection x :
          TensorRSSpace 0 (2 + j) I x)‖ ≤ Csob * R :=
      le_trans (Finset.single_le_sum hterm_nn (Finset.mem_range.mpr hj)) hCsob_sum
    have hsq : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T 0 s)).toSection x) =
        ‖((iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T 0 s)).toSection x :
            TensorRSSpace 0 (2 + j) I x)‖ ^ 2 := by
      rw [hbridge, Real.sq_sqrt
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _)]
    rw [hsq]
    have h1 : ‖((iteratedCovGrad (I := I) g₀ 0 2 j
        (convexPerturbation (I := I) g₀ T 0 s)).toSection x :
          TensorRSSpace 0 (2 + j) I x)‖ ^ 2 ≤ (Csob * R) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
    linarith
  have hprodcell : ∀ k ∈ Finset.range 3, ∀ n ∈ Finset.range (k + 1),
      ∀ e ∈ Finset.Nat.antidiagonalTuple n k,
      (∏ m' : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m') x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m')
          (convexPerturbation (I := I) g₀ T 0 s)).toSection x)) ≤ F := by
    intro k hk n hn e he
    have hk2 : k ≤ 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hn2 : n ≤ 2 := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) hk2
    have hsum_e : (∑ i : Fin n, e i) = k := Finset.Nat.mem_antidiagonalTuple.mp he
    have hem : ∀ m' : Fin n, e m' < 3 := by
      intro m'
      have hle : e m' ≤ k := by
        calc e m' ≤ ∑ i : Fin n, e i :=
              Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ m')
          _ = k := hsum_e
      omega
    have hstep : (∏ m' : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m') x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m')
          (convexPerturbation (I := I) g₀ T 0 s)).toSection x)) ≤
        ∏ _m' : Fin n, (1 + (Csob * R) ^ 2) :=
      Finset.prod_le_prod
        (fun m' _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e m') x _)
        (fun m' _ => hcell (e m') (hem m'))
    refine le_trans hstep ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hF_def]
    exact pow_le_pow_right₀ (le_add_of_nonneg_right (sq_nonneg (Csob * R))) hn2
  have hgrid_le : (∑ k ∈ Finset.range 3, ∑ n ∈ Finset.range (k + 1),
      ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
        ∏ m' : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m') x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m')
            (convexPerturbation (I := I) g₀ T 0 s)).toSection x)) ≤ cnt * F := by
    rw [hcnt_def, Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun n hn => ?_)
    calc (∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m' : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m') x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m')
              (convexPerturbation (I := I) g₀ T 0 s)).toSection x))
        ≤ ∑ _e ∈ Finset.Nat.antidiagonalTuple n k, F :=
          Finset.sum_le_sum (fun e he => hprodcell k hk n hn e he)
      _ = (Finset.Nat.antidiagonalTuple n k).card • F := Finset.sum_const F
      _ = ((Finset.Nat.antidiagonalTuple n k).card : ℝ) * F := nsmul_eq_mul _ _
  have hdiff_le : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) ≤
      CD 0 * (cnt * F) :=
    le_trans hCD0 (mul_le_mul_of_nonneg_left hgrid_le (hCD_nn 0))
  have hbg_le : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) ≤ Kbg :=
    hKbg_bd x
  have hsplit : (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x =
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) +
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) := by
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
    abel
  have hfin : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) ≤
      2 * (CD 0 * (cnt * F)) + 2 * Kbg := by
    rw [hsplit]
    have htri := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x)
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x)
    linarith
  rw [Real.sq_sqrt hsum_nn]
  exact hfin

set_option linter.unusedVariables false in
/-- Deferred input (dossier row RA-1, conjunct 3 of the frozen Riemann-arm refold data
bundled with the order-zero-part conjuncts 1, 4, 7; pattern class: `riemannSec_difference`
Palatini split + the exact path linearizations at second endpoint zero + the
`appCc`/`unitModel` evaluation calculus + fixed-frame neighbourhood gluing, with the
order-zero part `C0ra := bgRComm + arm0AA + (∇♯)K`-residual + Ricci-fold remainder): the
per-parameter refold identity for the moving order-zero Riemann coefficient, with the
second-gradient part the CONSTRUCTED folded four-monomial kernel family
`riemannPalatiniRefoldC2Family` at existentially pinned, PARTNER-PAIRED permutation
quadruples (`IsFramePairPartner` — the leader-sanctioned posit-layer strengthening restoring
the dossier's `symmS` partner bookkeeping; it is what the paired refold estimates below
consume at these witnesses), and an order-zero family carrying joint smoothness, a
ball-uniform pointwise fibre-norm sup, and the two-step jet window. Every consumer
transitively depends on `sorryAx` until this lands. -/
theorem exists_riemannPalatini_refold_identity_data
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∃ qA qB : Fin 4 → Equiv.Perm (Fin 4),
      IsFramePairPartner qA qB ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ C0ra : ℝ → SmoothCcTensor g₀ 2 2,
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0ra (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            appCc (I := I) (M := M) g₀ 2 2
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s))
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              appCc (I := I) (M := M) g₀ 2 2 (C0ra s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                appCc (I := I) (M := M) g₀ 4 2
                  (riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0ra s).toSection x) ≤
              Λ ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0ra s)‖ ^ 2 ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) :=
  sorry

private theorem jointTotalSpaceRS_add_local {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

private theorem jointTotalSpaceRS_sub_local {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

private theorem jointTotalSpaceRS_const_smul_local {r s : ℕ} {S : Set ℝ} (a : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (a • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := a)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul a (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      a (A p₀)

private theorem jointTotalSpaceRS_smulFun_local {r s : ℕ} {S : Set ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (A : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (f p.2 • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hfm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.2) :=
    hf.contMDiff.comp contMDiff_snd
  have hfj : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => f p.2) ((Set.univ : Set M) ×ˢ S) p₀ :=
    (hfm.contMDiffAt).contMDiffWithinAt
  refine (hfj.smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul (f p.2) (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      (f p₀.2) (A p₀)

private noncomputable def outerPairBilinChartα (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (chartInvGramMatrix (I := I) g α x k l * K X (chartBasisVecFiber (I := I) α k x)) •
          (ContinuousLinearMap.flip Dd (chartBasisVecFiber (I := I) α l x))
      map_add' := fun X X' => by
        ext Y'
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_add, smul_eq_mul]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring
      map_smul' := fun c X => by
        ext Y'
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring }

set_option linter.unusedSectionVars false in
private lemma outerPairBilinChartα_apply (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (X X' : TangentSpace I x) :
    outerPairBilinChartα (I := I) g α K Dd X X' =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x k l *
          (K X (chartBasisVecFiber (I := I) α k x) *
            Dd X' (chartBasisVecFiber (I := I) α l x)) := by
  rw [outerPairBilinChartα, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.flip_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

private lemma double_frame_bilin_trace_chartα
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g α x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g α x k l *
          (K (chartBasisVecFiber (I := I) α m x) (chartBasisVecFiber (I := I) α k x) *
            Dd (chartBasisVecFiber (I := I) α n x) (chartBasisVecFiber (I := I) α l x))) := by
  classical
  have hinner : ∀ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      outerPairBilinChartα (I := I) g α K Dd (B a) (B a) := by
    intro a
    rw [outerPairBilinChartα_apply]
    have h := orthonormal_basis_bilin_trace_chartα (I := I) g α hxbase
      (innerPairBilin (I := I) x K Dd (B a)) B hB
    simp only [innerPairBilin_apply, smul_eq_mul] at h
    rw [h]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  have hout := orthonormal_basis_bilin_trace_chartα (I := I) g α hxbase
    (outerPairBilinChartα (I := I) g α K Dd) B hB
  simp only [smul_eq_mul] at hout
  rw [hout]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [outerPairBilinChartα_apply]

private def toModelEvalCLM (s : ℕ) (x : M) (v : Fin s → E) :
    Tensor0SSpace s I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace s I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Tensor0SSpace.toModel (𝕜 := ℝ) D v
      map_add' := fun D₁ D₂ => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul]
        rfl }

set_option linter.unusedSectionVars false in
private lemma toModelEvalCLM_apply (s : ℕ) (x : M) (v : Fin s → E)
    (D : Tensor0SSpace s I x) :
    toModelEvalCLM (I := I) (M := M) s x v D = Tensor0SSpace.toModel (𝕜 := ℝ) D v := rfl

private def pairFeedScalarCLM (s : ℕ) (x : M) (G : Tensor0SSpace (s + 2) I x)
    (v : Fin s → E) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (toModelEvalCLM (I := I) (M := M) s x v).comp
        (tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) s x
          ((tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) (s + 1) x G) p))
      map_add' := fun p p' => by
        rw [map_add, map_add, ContinuousLinearMap.comp_add]
      map_smul' := fun c p => by
        rw [map_smul, map_smul, RingHom.id_apply]
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          map_smul] }

set_option linter.unusedSectionVars false in
private lemma pairFeedScalarCLM_apply (s : ℕ) (x : M) (G : Tensor0SSpace (s + 2) I x)
    (v : Fin s → E) (p q : TangentSpace I x) :
    pairFeedScalarCLM (I := I) (M := M) s x G v p q =
      Tensor0SSpace.toModel (𝕜 := ℝ) G (Fin.cons (p : E) (Fin.cons (q : E) v)) := by
  rw [pairFeedScalarCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, toModelEvalCLM_apply,
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) (s + 1) x G) p) (v0 := q) (vs := v),
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := G) (v0 := p) (vs := Fin.cons (q : E) v)]

private lemma curvatureRefoldMonomialBiContrFib_toModel_chartα
    (g : SmoothRiemannianMetric I M) (W : Π b : M, Tensor0SSpace 2 I b)
    (σp : Equiv.Perm (Fin 4)) (α : M) {x : M}
    (hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (G : Tensor0SSpace 4 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        (curvatureRefoldMonomialBiContrFib (I := I) (M := M) g W σp x G) v =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g α x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g α x k l *
          (Tensor0SSpace.toModel (𝕜 := ℝ) (W x)
              ![(chartBasisVecFiber (I := I) α m x : E),
                (chartBasisVecFiber (I := I) α k x : E)] *
            Tensor0SSpace.toModel (𝕜 := ℝ) G
              (fun i => (Fin.cons ((chartBasisVecFiber (I := I) α n x : E))
                (Fin.cons ((chartBasisVecFiber (I := I) α l x : E)) v) : Fin 4 → E)
                (σp i)))) := by
  classical
  have hBf_on : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x) =
        if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  rw [show curvatureRefoldMonomialBiContrFib (I := I) (M := M) g W σp x =
      curvatureRefoldMonomialFibFixedFrame (I := I) (M := M) W σp
        (smoothOrthoFrame (I := I) g x) x from rfl,
    curvatureRefoldMonomialFibFixedFrame_toModel]
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel (𝕜 := ℝ) (W x)
          ![(smoothOrthoFrame (I := I) g x a x : E), (smoothOrthoFrame (I := I) g x b x : E)] *
        Tensor0SSpace.toModel (𝕜 := ℝ) G
          (fun i => (Fin.cons ((smoothOrthoFrame (I := I) g x a x : E))
            (Fin.cons ((smoothOrthoFrame (I := I) g x b x : E)) v) : Fin 4 → E) (σp i)) =
      pairFeedScalarCLM (I := I) (M := M) 0 x (W x) ![]
          (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x b x) *
        pairFeedScalarCLM (I := I) (M := M) 2 x
          (slotPerm4Fib (I := I) (M := M) x σp G) v
          (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x b x) := by
    intro a b
    rw [pairFeedScalarCLM_apply, pairFeedScalarCLM_apply, slotPerm4Fib_toModel,
      ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hsummand a b))]
  rw [double_frame_bilin_trace_chartα (I := I) g α hxbase
    (pairFeedScalarCLM (I := I) (M := M) 0 x (W x) ![])
    (pairFeedScalarCLM (I := I) (M := M) 2 x (slotPerm4Fib (I := I) (M := M) x σp G) v)
    (fun a => smoothOrthoFrame (I := I) g x a x) hBf_on]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  refine congrArg (fun t => chartInvGramMatrix (I := I) g α x m n * t) ?_
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine congrArg (fun t => chartInvGramMatrix (I := I) g α x k l * t) ?_
  rw [pairFeedScalarCLM_apply, pairFeedScalarCLM_apply, slotPerm4Fib_toModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rfl

private lemma curvatureRefoldMonomialBiContrFibAppY_chartCoord_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (W : Π b : M, Tensor0SSpace 2 I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) b (W b)))
    (σp : Equiv.Perm (Fin 4))
    (Y : Cₛ^∞⟮I; Tensor0SModel 4 ℝ E, fun x : M => Tensor0SSpace 4 I x⟯)
    (α : M) (σc : Fin 2 → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => Tensor0SSpace.toModel
        (curvatureRefoldMonomialBiContrFib (I := I) (M := M)
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) W σp p.1 (Y p.1))
        ![(chartBasisVecFiber (I := I) α (σc 0) p.1 : E),
          (chartBasisVecFiber (I := I) α (σc 1) p.1 : E)])
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
  classical
  have htuple : ∀ (y : M) (n l : Fin (Module.finrank ℝ E)) (j : Fin 4),
      (Fin.cons ((chartBasisVecFiber (I := I) α n y : E))
        (Fin.cons ((chartBasisVecFiber (I := I) α l y : E))
          ![(chartBasisVecFiber (I := I) α (σc 0) y : E),
            (chartBasisVecFiber (I := I) α (σc 1) y : E)]) : Fin 4 → E) j =
      ((chartBasisVecFiber (I := I) α
        ((Fin.cons n (Fin.cons l ![σc 0, σc 1]) : Fin 4 → Fin (Module.finrank ℝ E)) j)
        y : E)) := by
    intro y n l j
    fin_cases j <;> rfl
  have hYtuple : ∀ w : Fin 4 → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Tensor0SSpace.toModel (𝕜 := ℝ) (Y p.1)
          (fun i => (chartBasisVecFiber (I := I) α (w i) p.1 : E)))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    intro w p₀ hp₀
    have hYon : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
          (E := fun z : M => Tensor0SSpace 4 I z) p.1 (Y p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
      (Y.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
    have hv : ∀ i : Fin 4, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
          (chartBasisVecFiber (I := I) α (w i) p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) p₀ := fun i =>
      (chartBasisVec_jointContMDiffOn (I := I) α (w i) p₀
        ⟨hp₀.1, Set.mem_univ _⟩).mono (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
    exact TensorMultilinear.contMDiffWithinAt_section_apply_prod (I := I) 4
      (fun b : M => Y b) (hYon p₀ hp₀)
      (fun i => fun b : M => chartBasisVecFiber (I := I) α (w i) b) hv
  have hWpair : ∀ m k : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Tensor0SSpace.toModel (𝕜 := ℝ) (W p.1)
          ![(chartBasisVecFiber (I := I) α m p.1 : E),
            (chartBasisVecFiber (I := I) α k p.1 : E)])
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    intro m k p₀ hp₀
    have hWon : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) p.1 (W p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
      (hW.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
    have hv : ∀ i : Fin 2, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
          (chartBasisVecFiber (I := I) α
            ((![m, k] : Fin 2 → Fin (Module.finrank ℝ E)) i) p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) p₀ := fun i =>
      (chartBasisVec_jointContMDiffOn (I := I) α
        ((![m, k] : Fin 2 → Fin (Module.finrank ℝ E)) i) p₀
        ⟨hp₀.1, Set.mem_univ _⟩).mono (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
    have happly := TensorMultilinear.contMDiffWithinAt_section_apply_prod (I := I) 2
      (fun b : M => W b) (hWon p₀ hp₀)
      (fun i => fun b : M => chartBasisVecFiber (I := I) α
        ((![m, k] : Fin 2 → Fin (Module.finrank ℝ E)) i) b) hv
    refine happly.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q _
      congr 1
      funext i
      fin_cases i <;> rfl
    · congr 1
      funext i
      fin_cases i <;> rfl
  have hcomb : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => ∑ m, ∑ n, chartInvGramMatrix (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) α p.1 m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I)
            (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) α p.1 k l *
          (Tensor0SSpace.toModel (𝕜 := ℝ) (W p.1)
              ![(chartBasisVecFiber (I := I) α m p.1 : E),
                (chartBasisVecFiber (I := I) α k p.1 : E)] *
            Tensor0SSpace.toModel (𝕜 := ℝ) (Y p.1)
              (fun i => (Fin.cons ((chartBasisVecFiber (I := I) α n p.1 : E))
                (Fin.cons ((chartBasisVecFiber (I := I) α l p.1 : E))
                  ![(chartBasisVecFiber (I := I) α (σc 0) p.1 : E),
                    (chartBasisVecFiber (I := I) α (σc 1) p.1 : E)]) : Fin 4 → E)
                (σp i)))))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    refine contMDiffOn_finset_sum (fun m _ => contMDiffOn_finset_sum (fun n _ => ?_))
    refine (realizedFam_chartInvGramMatrix_jointContMDiffOn_free (I := I) g₀ T 0
      hδ hδZ α m n).mul ?_
    refine contMDiffOn_finset_sum (fun k _ => contMDiffOn_finset_sum (fun l _ => ?_))
    refine (realizedFam_chartInvGramMatrix_jointContMDiffOn_free (I := I) g₀ T 0
      hδ hδZ α k l).mul ?_
    refine (hWpair m k).mul ?_
    refine (hYtuple (fun i => (Fin.cons n (Fin.cons l ![σc 0, σc 1]) :
      Fin 4 → Fin (Module.finrank ℝ E)) (σp i))).congr (fun p _ => ?_)
    congr 1
    funext i
    exact htuple p.1 n l (σp i)
  refine hcomb.congr (fun p hp => ?_)
  have hxbase : p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hp.1
  rw [curvatureRefoldMonomialBiContrFib_toModel_chartα (I := I) (M := M)
    (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) W σp α hxbase]

private lemma curvatureRefoldMonomialBiContrFibAppY_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (W : Π b : M, Tensor0SSpace 2 I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) b (W b)))
    (σp : Equiv.Perm (Fin 4))
    (Y : Cₛ^∞⟮I; Tensor0SModel 4 ℝ E, fun x : M => Tensor0SSpace 4 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) p.1
        (curvatureRefoldMonomialBiContrFib (I := I) (M := M)
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) W σp p.1 (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  set gfam : ℝ → SmoothRiemannianMetric I M :=
    fun s => realizedFam (I := I) g₀ T 0 hδ hδZ s with hgfam
  set S := realizedSmallSet (δ := δ) (δ' := δ) with hS
  intro p₀ hp₀
  set α := p₀.1 with hα
  set e := trivializationAt (Tensor0SModel 2 ℝ E)
    (fun z : M => Tensor0SSpace 2 I z) α with he
  set Bcmm := continuousMultilinearMap_basis (𝕜 := ℝ) (F := E) (chartModelBasis E) 2 with hBcmm
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  have hαsrc : α ∈ (chartAt H α).source := mem_chart_source H α
  have hαbase : α ∈ e.baseSet := by
    rw [he]; exact mem_baseSet_trivializationAt _ _ α
  have hnhd : (chartAt H α).source ×ˢ S ∈ nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S) := by
    refine mem_nhdsWithin.mpr ⟨(chartAt H α).source ×ˢ S,
      (chartAt H α).open_source.prod realizedSmallSet_isOpen, ⟨hαsrc, hp₀.2⟩, fun q hq => hq.1⟩
  have hcoordEach : ∀ σc : Fin 2 → Fin (Module.finrank ℝ E),
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Bcmm.repr
          (e ⟨p.1, curvatureRefoldMonomialBiContrFib (I := I) (M := M)
            (gfam p.2) W σp p.1 (Y p.1)⟩).2 σc)
        ((Set.univ : Set M) ×ˢ S) p₀ := by
    intro σc
    have hscal := curvatureRefoldMonomialBiContrFibAppY_chartCoord_jointContMDiffOn
      (I := I) (M := M) g₀ T hδ hδZ W hW σp Y α σc
    have hscalAt := (hscal p₀ ⟨hαsrc, hp₀.2⟩).mono_of_mem_nhdsWithin hnhd
    have hreadout : ∀ {q : M × ℝ}, q.1 ∈ e.baseSet →
        Bcmm.repr (e ⟨q.1, curvatureRefoldMonomialBiContrFib (I := I) (M := M)
            (gfam q.2) W σp q.1 (Y q.1)⟩).2 σc =
          Tensor0SSpace.toModel (curvatureRefoldMonomialBiContrFib (I := I) (M := M)
              (gfam q.2) W σp q.1 (Y q.1))
            ![(chartBasisVecFiber (I := I) α (σc 0) q.1 : E),
              (chartBasisVecFiber (I := I) α (σc 1) q.1 : E)] := by
      intro q hqbase
      rw [continuousMultilinearMap_basis_repr]
      have hcoe : (e ⟨q.1, curvatureRefoldMonomialBiContrFib (I := I) (M := M)
          (gfam q.2) W σp q.1 (Y q.1)⟩).2 =
          (e.linearMapAt ℝ q.1) (curvatureRefoldMonomialBiContrFib (I := I) (M := M)
            (gfam q.2) W σp q.1 (Y q.1)) :=
        (congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e) hqbase) _).symm
      rw [hcoe]
      have happly := TensorMultilinear.tensor0SBundle_linearMapAt_apply_of_mem (I := I) α q.1
        hqbase
        (curvatureRefoldMonomialBiContrFib (I := I) (M := M) (gfam q.2) W σp q.1 (Y q.1))
        (fun j => (chartModelBasis E) (σc j))
      rw [tensor0SSpace_continuousLinearEquiv_symm_apply] at happly
      rw [happly]
      change Tensor0SSpace.toModel (curvatureRefoldMonomialBiContrFib (I := I) (M := M)
          (gfam q.2) W σp q.1 (Y q.1))
          (fun j => (trivializationAt E (TangentSpace I) α).symmL ℝ q.1
            ((chartModelBasis E) (σc j))) = _
      congr 1
      funext j
      fin_cases j <;> rfl
    refine hscalAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hnhd] with q hq
      have hqbaseT : q.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hq.1
      have hqbase : q.1 ∈ e.baseSet := by rw [he]; exact hqbaseT
      exact hreadout hqbase
    · exact hreadout hαbase
  have hcoordVec : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun p : M × ℝ => fun σc : Fin 2 → Fin (Module.finrank ℝ E) =>
        Bcmm.repr (e ⟨p.1, curvatureRefoldMonomialBiContrFib (I := I) (M := M)
          (gfam p.2) W σp p.1 (Y p.1)⟩).2 σc)
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    contMDiffWithinAt_pi_space.mpr (fun σc => hcoordEach σc)
  have hfinal : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SModel 2 ℝ E) ∞
      (fun p : M × ℝ => (e ⟨p.1, curvatureRefoldMonomialBiContrFib (I := I) (M := M)
        (gfam p.2) W σp p.1 (Y p.1)⟩).2)
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hequiv := (Bcmm.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt
      (x := Bcmm.equivFun
        (e ⟨p₀.1, curvatureRefoldMonomialBiContrFib (I := I) (M := M)
          (gfam p₀.2) W σp p₀.1 (Y p₀.1)⟩).2)).comp_contMDiffWithinAt
      p₀ hcoordVec
    refine hequiv.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q _
      exact (Bcmm.equivFun.symm_apply_apply _).symm
    · exact (Bcmm.equivFun.symm_apply_apply _).symm
  exact hfinal

private theorem curvatureRefoldMonomialCoeffField_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (W : Π b : M, Tensor0SSpace 2 I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) b (W b)))
    (σp : Equiv.Perm (Fin 4)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        ((curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) W hW σp).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
  have hCLM := contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SSpace 4 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => curvatureRefoldMonomialBiContrFib (I := I) (M := M)
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) W σp p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
    (fun Y => curvatureRefoldMonomialBiContrFibAppY_realizedFam_jointContMDiffOn
      (I := I) (M := M) g₀ T hδ hδZ W hW σp Y)
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [curvatureRefoldMonomialCoeffField_toSection]
  rfl

set_option linter.unusedVariables false in
/-- Dossier row RA-2 (conjunct 2 of the frozen Riemann-arm refold data): joint smoothness
of the constructed second-gradient refold family, for every permutation-quadruple
convention. The family is the path-parameter multiple of the half-sum of two folded
four-monomial kernels at the realized metric; each frame-summed monomial coefficient is
jointly smooth because on a chart it is the double inverse-Gram contraction of the
metric-free weight and argument data (`double_frame_bilin_trace` in chart form), with the
realized family's inverse Gram matrix jointly smooth in the path parameter. -/
theorem riemannPalatiniRefoldC2Family_threeArmHjoint
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB)
      (δ := δ) (δ' := δ) := by
  classical
  have hmono : ∀ σp : Equiv.Perm (Fin 4),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
          ((curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ p.2)
            (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
            (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) σp).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
    fun σp => curvatureRefoldMonomialCoeffField_realizedFam_jointContMDiffOn
      (I := I) (M := M) g₀ T hδ hδZ
      (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) σp
  have hker : ∀ q : Fin 4 → Equiv.Perm (Fin 4),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
          ((curvatureRefoldKernelCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ p.2)
            (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
            (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
            (q 0) (q 1) (q 2) (q 3)).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    intro q
    have hadd := jointTotalSpaceRS_add_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ (hmono (q 0)) (hmono (q 1))
    have hsub1 := jointTotalSpaceRS_sub_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hadd (hmono (q 2))
    have hsub2 := jointTotalSpaceRS_sub_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hsub1 (hmono (q 3))
    have hhalf := jointTotalSpaceRS_const_smul_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) (1 / 2 : ℝ) _ hsub2
    refine hhalf.congr (fun p _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
    rw [curvatureRefoldKernelCoeffField, SmoothCcTensor.toSection_smul,
      SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub,
      SmoothCcTensor.toSection_add, ContMDiffSection.coe_smul, Pi.smul_apply,
      ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
      ContMDiffSection.coe_add, Pi.add_apply]
  have hsum := jointTotalSpaceRS_add_local (I := I) (M := M) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ (hker qA) (hker qB)
  have hhalf := jointTotalSpaceRS_const_smul_local (I := I) (M := M) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ)) (1 / 2 : ℝ) _ hsum
  have hfam := jointTotalSpaceRS_smulFun_local (I := I) (M := M) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ)) (f := fun t => t) contDiff_id _ hhalf
  refine hfam.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [riemannPalatiniRefoldC2Family, SmoothCcTensor.toSection_smul,
    SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_smul, Pi.smul_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContMDiffSection.coe_add, Pi.add_apply]

set_option linter.unusedVariables false in
/-- Deferred input (dossier row RA-3a, conjunct 6 of the frozen Riemann-arm refold data;
pattern class: Koszul-sharp `δ/(1−δ)` fibre bounds — `ConnectionDifferenceFibreBound` and
the `rfns` bi-contraction bounds of `RicciThreeArmCorrectionFieldBound`, with the frame and
weight conversions absorbed into the dimensional fibre constant; small literals checked at
`n = 1, 2, 3` at fill): the pointwise fibre-norm cap for the constructed second-gradient
refold family at the FOLDED FOUR-MONOMIAL literal `4`, for every PARTNER-PAIRED
permutation-quadruple convention (`IsFramePairPartner`; the pairing makes the double frame
sum see only the symmetrized weight `ccTensorBilinSymm`, which `hδ` caps — the earlier
∀-independent form was false: an antisymmetric moving tensor at `δ = 0` defeats the cap
through the raw unpaired weight). Every consumer transitively depends on `sorryAx` until
this lands. -/
theorem riemannPalatiniRefoldC2Family_rfns_le
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (hq : IsFramePairPartner qA qB) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB s).toSection
          x) ≤
      (max (4 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0) ^ 2 :=
  sorry

set_option linter.unusedVariables false in
/-- Deferred input (dossier row RA-4, conjunct 8 of the frozen Riemann-arm refold data;
pattern class: tame-envelope technique of the curvature-coefficient jet towers with
ball-absorption `K·(1 + Σ)` weakening; the coefficient carries the moving tensor at the
zero jet and metric raisings at the zero jet, so `∇ⁱ` stays inside the `range (i + 2)`
window; the pointwise fibre-norm cap of `riemannPalatiniRefoldC2Family_rfns_le` rides as
the companion sup anchor): the two-step jet window for the constructed second-gradient
refold family, for every PARTNER-PAIRED permutation-quadruple convention
(`IsFramePairPartner`; the anchor conjunct is exactly the paired cap of
`riemannPalatiniRefoldC2Family_rfns_le`, which is false without the pairing). Every
consumer transitively depends on `sorryAx` until this lands. -/
theorem exists_riemannPalatiniRefoldC2Family_l2JetWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (hq : IsFramePairPartner qA qB) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB
              s).toSection x) ≤
          (max (4 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0) ^ 2) ∧
        (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB s)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) :=
  sorry

/-- The constructed second-gradient refold family for the covariant-derivative arm of the
DeTurck Lie coefficient at second endpoint zero: the moving tensor's unit value weights the
three sharp-Koszul-gradient monomials at the realized metric's orthonormal frames, each
monomial partner-paired with its leading-frame-slot swap at half weight (so the effective
coefficient weight is the symmetrized moving tensor -- the `symmS` average carried by the
construction itself, never by independent quantifiers), with signed monomial weights of
magnitude at most one and an overall path-parameter scale (the connection-difference rate
at second endpoint zero). Three monomials at half weight over partner pairs give the three
ledger copies of the frozen cap literal `3`. The exact permutations and signs are pinned by
the refold identity child below. -/
def deTurckLieCovDerivRefoldC2Family (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ) (s : ℝ) : SmoothCcTensor g₀ 4 2 :=
  s • ∑ i : Fin 3, ε i • ((1 / 2 : ℝ) •
    (curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) (q i)
      + curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
        ((q i).trans (Equiv.swap (0 : Fin 4) 1))))

set_option linter.unusedSectionVars false in
/-- The constructed covariant-derivative-arm second-gradient family vanishes at path
parameter zero: the refold carries the connection-difference rate, which vanishes at the
path's first endpoint. -/
@[simp] lemma deTurckLieCovDerivRefoldC2Family_zero (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ) :
    deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε 0 = 0 := by
  rw [deTurckLieCovDerivRefoldC2Family, zero_smul]


set_option linter.unusedSectionVars false in
/-- The unit-value carrier of a slot-swapped rank-two coefficient tensor is the slot-swapped
unit-value carrier. -/
lemma toModel_ccTensorUnitValueSection_domDomCongrSection_swap
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (x : M)
    (p q' : TangentSpace I x) :
    Tensor0SSpace.toModel (ccTensorUnitValueSection (I := I) (M := M) g₀
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) x)
        ![(p : E), (q' : E)] =
      Tensor0SSpace.toModel (ccTensorUnitValueSection (I := I) (M := M) g₀ T x)
        ![(q' : E), (p : E)] := by
  have hbridge : ∀ (S : SmoothCcTensor g₀ 0 2),
      Tensor0SSpace.toModel (ccTensorUnitValueSection (I := I) (M := M) g₀ S x) =
        unitModel (I := I) (M := M) g₀ 2 S x := fun S => rfl
  rw [hbridge, hbridge, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

set_option linter.unusedSectionVars false in
/-- Leading-frame-slot partner transport for the frame-summed refold monomial at unit-value
weights: precomposing the slot pattern with the swap of the two leading (frame) slots is the
same coefficient as loading the slot-swapped weight tensor at the unswapped pattern — the
double frame sum reindexes. This is the identity through which the partner-paired family
`deTurckLieCovDerivRefoldC2Family` carries the symmetrized moving tensor as its effective
weight. -/
theorem curvatureRefoldMonomialCoeffField_unitValue_trans_swap
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (σ : Equiv.Perm (Fin 4)) :
    curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
        (σ.trans (Equiv.swap (0 : Fin 4) 1)) =
      curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)) σ := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [curvatureRefoldMonomialCoeffField_toSection, curvatureRefoldMonomialCoeffField_toSection]
  refine congrArg TensorRSSpace.ofCLM ?_
  refine ContinuousLinearMap.ext (fun G => ?_)
  refine Tensor0SSpace.toModel_injective ?_
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [curvatureRefoldMonomialBiContrFib, curvatureRefoldMonomialBiContrFib,
    curvatureRefoldMonomialFibFixedFrame_toModel, curvatureRefoldMonomialFibFixedFrame_toModel]
  have hcons : ∀ (p q' : TangentSpace I x) (j : Fin 4),
      (Fin.cons (p : E) (Fin.cons (q' : E) v) : Fin 4 → E) ((Equiv.swap (0 : Fin 4) 1) j) =
        (Fin.cons (q' : E) (Fin.cons (p : E) v) : Fin 4 → E) j := by
    intro p q' j
    fin_cases j <;> rfl
  have hstep : ∀ a b : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel (𝕜 := ℝ) (ccTensorUnitValueSection (I := I) (M := M) g₀ T x)
          ![(smoothOrthoFrame (I := I) g₁ x a x : E), (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        Tensor0SSpace.toModel (𝕜 := ℝ) G
          (fun i => (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : E))
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : E)) v) : Fin 4 → E)
            ((σ.trans (Equiv.swap (0 : Fin 4) 1)) i)) =
      Tensor0SSpace.toModel (𝕜 := ℝ) (ccTensorUnitValueSection (I := I) (M := M) g₀ T x)
          ![(smoothOrthoFrame (I := I) g₁ x a x : E), (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        Tensor0SSpace.toModel (𝕜 := ℝ) G
          (fun i => (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : E))
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : E)) v) : Fin 4 → E) (σ i)) := by
    intro a b
    congr 1
    refine congrArg _ ?_
    funext i
    exact hcons _ _ (σ i)
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hstep a b))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [toModel_ccTensorUnitValueSection_domDomCongrSection_swap]


set_option linter.unusedSectionVars false in
/-- Additivity of the unit-value carrier in the coefficient tensor. -/
lemma ccTensorUnitValueSection_add (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (y : M) :
    ccTensorUnitValueSection (I := I) (M := M) g₀ (S + S') y =
      ccTensorUnitValueSection (I := I) (M := M) g₀ S y +
        ccTensorUnitValueSection (I := I) (M := M) g₀ S' y := by
  have h : ((S + S').toSection y : TensorRSSpace 0 2 I y) =
      (S.toSection y : TensorRSSpace 0 2 I y) + (S'.toSection y : TensorRSSpace 0 2 I y) := by
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  rw [ccTensorUnitValueSection, ccTensorUnitValueSection, ccTensorUnitValueSection, h]
  rfl

set_option linter.unusedSectionVars false in
/-- Homogeneity of the unit-value carrier in the coefficient tensor. -/
lemma ccTensorUnitValueSection_smul (g₀ : SmoothRiemannianMetric I M) (c : ℝ)
    (S : SmoothCcTensor g₀ 0 2) (y : M) :
    ccTensorUnitValueSection (I := I) (M := M) g₀ (c • S) y =
      c • ccTensorUnitValueSection (I := I) (M := M) g₀ S y := by
  have h : ((c • S).toSection y : TensorRSSpace 0 2 I y) =
      c • (S.toSection y : TensorRSSpace 0 2 I y) := by
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [ccTensorUnitValueSection, ccTensorUnitValueSection, h]
  rfl

set_option linter.unusedSectionVars false in
/-- Additivity of the frame-summed refold monomial in its unit-value weight. -/
theorem curvatureRefoldMonomialCoeffField_unitValue_add
    (g₀ g₁ : SmoothRiemannianMetric I M) (S S' : SmoothCcTensor g₀ 0 2)
    (σ : Equiv.Perm (Fin 4)) :
    curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (S + S'))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ (S + S')) σ =
      curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S) σ
        + curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S')
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S') σ := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    curvatureRefoldMonomialCoeffField_toSection, curvatureRefoldMonomialCoeffField_toSection,
    curvatureRefoldMonomialCoeffField_toSection]
  refine tensorRSSpace_ext 4 2 x (fun G => ?_)
  refine Tensor0SSpace.toModel_injective ?_
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  have hadd : (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (TensorRSSpace.ofCLM (curvatureRefoldMonomialBiContrFib (I := I) (M := M) g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x)
        + TensorRSSpace.ofCLM (curvatureRefoldMonomialBiContrFib (I := I) (M := M) g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S') σ x))) G =
      curvatureRefoldMonomialBiContrFib (I := I) (M := M) g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x G
        + curvatureRefoldMonomialBiContrFib (I := I) (M := M) g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S') σ x G := rfl
  rw [hadd]
  simp only [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    TensorRSSpace.ofCLM]
  rw [curvatureRefoldMonomialBiContrFib, curvatureRefoldMonomialBiContrFib,
    curvatureRefoldMonomialBiContrFib, curvatureRefoldMonomialFibFixedFrame_toModel,
    curvatureRefoldMonomialFibFixedFrame_toModel, curvatureRefoldMonomialFibFixedFrame_toModel]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [ccTensorUnitValueSection_add]
  simp only [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [add_mul]

set_option linter.unusedSectionVars false in
/-- Homogeneity of the frame-summed refold monomial in its unit-value weight. -/
theorem curvatureRefoldMonomialCoeffField_unitValue_smul
    (g₀ g₁ : SmoothRiemannianMetric I M) (c : ℝ) (S : SmoothCcTensor g₀ 0 2)
    (σ : Equiv.Perm (Fin 4)) :
    curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (c • S))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ (c • S)) σ =
      c • curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S) σ := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    curvatureRefoldMonomialCoeffField_toSection, curvatureRefoldMonomialCoeffField_toSection]
  refine tensorRSSpace_ext 4 2 x (fun G => ?_)
  refine Tensor0SSpace.toModel_injective ?_
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  have hsmul : (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (c • TensorRSSpace.ofCLM (curvatureRefoldMonomialBiContrFib (I := I) (M := M) g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x))) G =
      c • curvatureRefoldMonomialBiContrFib (I := I) (M := M) g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x G := rfl
  rw [hsmul]
  simp only [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    TensorRSSpace.ofCLM]
  rw [curvatureRefoldMonomialBiContrFib, curvatureRefoldMonomialBiContrFib,
    curvatureRefoldMonomialFibFixedFrame_toModel, curvatureRefoldMonomialFibFixedFrame_toModel]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [ccTensorUnitValueSection_smul]
  simp only [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

set_option linter.unusedSectionVars false in
/-- The partner-paired half sum of refold monomials carries the SYMMETRIZED moving tensor
as its effective unit-value weight: the pairing baked into the constructed family is
exactly the `symmS` average, so the `gFibreOpBound` hypothesis on the symmetrized tensor
controls the paired coefficient — the certificate that universal quantification over the
permutation-and-sign conventions is sound for the partner-paired construction. -/
theorem curvatureRefoldMonomialCoeffField_unitValue_pair_eq_symmS
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (σ : Equiv.Perm (Fin 4)) :
    (1 / 2 : ℝ) •
      (curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) σ
        + curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
          (σ.trans (Equiv.swap (0 : Fin 4) 1))) =
      curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (symmS (I := I) (M := M) g₀ T)) σ := by
  rw [show curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (symmS (I := I) (M := M) g₀ T)) σ =
      curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ ((1 / 2 : ℝ) •
          (T + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ ((1 / 2 : ℝ) •
          (T + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T))) σ from by
    congr 1]
  rw [curvatureRefoldMonomialCoeffField_unitValue_smul,
    curvatureRefoldMonomialCoeffField_unitValue_add,
    curvatureRefoldMonomialCoeffField_unitValue_trans_swap]


set_option linter.unusedSectionVars false in
/-- The constructed covariant-derivative-arm family carries the SYMMETRIZED moving tensor
as its effective weight: the partner pairing in the definition is the `symmS` average.
This is the birth certificate that the family's estimate package is sound for every
permutation-and-sign convention — the fibre-norm cap is controlled by the `gFibreOpBound`
hypothesis on the symmetrized tensor. -/
theorem deTurckLieCovDerivRefoldC2Family_eq_symmS_weight (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ) (s : ℝ) :
    deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε s =
      s • ∑ i : Fin 3, ε i •
        curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          (ccTensorUnitValueSection (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ T))
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
            (symmS (I := I) (M := M) g₀ T)) (q i) := by
  rw [deTurckLieCovDerivRefoldC2Family]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  exact curvatureRefoldMonomialCoeffField_unitValue_pair_eq_symmS (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (q i)

set_option linter.unusedVariables false in
/-- Deferred input (dossier row LC-1, identity core with the order-zero-part shares of rows
LC-4/LC-5/LC-6; pattern class: connection-difference cocycle `sub_add_sub` at the realized
path plus the endpoint exact fibre linearization
`covDerivConnDiff_realizedFam_zero_endpoint_eq_smul_covDerivSharp`, the lower-slot symmetry
of the connection difference (`connDiff_symm`, which folds the raw-weight frame sum onto
the partner-paired constructed family), and the `appCc`/`unitModel` evaluation calculus
with fixed-frame neighbourhood gluing; the order-zero family carries the background
connection-difference leg, the quadratic connection-difference corrections, and the one-jet
sharp-gradient residual): the per-parameter refold identity for the covariant-derivative
arm of the DeTurck Lie coefficient, with the second-gradient part the CONSTRUCTED
partner-paired family `deTurckLieCovDerivRefoldC2Family` at existentially pinned
permutations and signs, and an order-zero family carrying joint smoothness, a ball-uniform
pointwise fibre-norm sup, and the two-step jet window. Every consumer transitively depends
on `sorryAx` until this lands. -/
theorem exists_deTurckLieCovDerivArm_refold_identity_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∃ (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ), (∀ i, |ε i| ≤ 1) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ C0da : ℝ → SmoothCcTensor g₀ 2 2,
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0da (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            appCc (I := I) (M := M) g₀ 2 2
                (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg)
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              appCc (I := I) (M := M) g₀ 2 2 (C0da s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                appCc (I := I) (M := M) g₀ 4 2
                  (deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0da s).toSection x) ≤
              Λ ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0da s)‖ ^ 2 ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) :=
  sorry

set_option linter.unusedVariables false in
/-- Deferred input (dossier rows LC-4/LC-5/LC-6, constructed-family shares at the frozen cap
literal `3`; pattern class: joint smoothness of the realized-family coefficient
constructions through the fixed-frame patching of the refold kernel calculus; the
Koszul-sharp `δ/(1−δ)` fibre-norm class for the cap -- the partner pairing inside the family
definition symmetrizes the coefficient weight, so the weight is controlled by the
`gFibreOpBound` hypothesis on the symmetrized moving tensor for EVERY permutation-and-sign
convention (the construction carries the pairing, so the universal quantification over
conventions is sound, unlike independent-quadruple forms); and the tame-envelope technique
with ball absorption for the two-step window -- the coefficient carries the moving tensor
and the metric raisings at the zero jet, so `∇ⁱ` stays inside `range (i + 2)`; small
literals checked at `n = 1, 2, 3` at fill): joint smoothness, the pointwise fibre-norm cap
at the three-copy literal `3`, and the two-step jet window for the constructed
covariant-derivative-arm second-gradient family. Every consumer transitively depends on
`sorryAx` until this lands. -/
theorem exists_deTurckLieCovDerivRefoldC2Family_cap_l2JetWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
          (deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε)
          (δ := δ) (δ' := δ) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε
              s).toSection x) ≤
          (max (3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0) ^ 2) ∧
        (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε s)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) :=
  sorry

set_option linter.unusedVariables false in
/-- Deferred input (dossier row LC-1 with its arm shares of rows LC-4/LC-5/LC-6, at cap
literal `3`; pattern class: connection-difference cocycle `sub_add_sub` + the exact path
linearizations at second endpoint zero, refolding the moving-endpoint
covariant-gradient-of-connection-difference content of the `dLaBiContrFib` bi-contraction
onto the second gradient at three ledger copies, with the background leg and the one-jet
sharp-gradient residual riding the order-zero part; sup anchors and two-step windows as in
the Riemann-arm rows): the refold data package for the covariant-derivative arm of the
DeTurck Lie coefficient along the realized path. Every consumer transitively depends on
`sorryAx` until this lands. -/
theorem exists_deTurckLieCovDerivArm_curvatureRefold_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ (C0da : ℝ → SmoothCcTensor g₀ 2 2) (C2da : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0da (δ := δ) (δ' := δ) ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 C2da (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            appCc (I := I) (M := M) g₀ 2 2
                (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg)
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              appCc (I := I) (M := M) g₀ 2 2 (C0da s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                appCc (I := I) (M := M) g₀ 4 2 (C2da s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0da s).toSection x) ≤
              Λ ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((C2da s).toSection x) ≤
              (max (3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0)
                ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0da s)‖ ^ 2 ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 4 2 i (C2da s)‖ ^ 2 ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨Λ, hΛ, KA, hKA, q, ε, hε, hmain⟩ :=
    exists_deTurckLieCovDerivArm_refold_identity_data (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨KB, hKB, hfam⟩ :=
    exists_deTurckLieCovDerivRefoldC2Family_cap_l2JetWindow (I := I) (M := M) g₀ a
      ha_super hR hδ₀ q ε hε
  refine ⟨Λ, hΛ, fun i => max (KA i) (KB i),
    fun i => le_trans (hKA i) (le_max_left _ _), ?_⟩
  intro T δ hδ_le hδ hδZ hball
  obtain ⟨C0da, hjoint0, hid, hsup0, henv0⟩ := hmain T hδ_le hδ hδZ hball
  obtain ⟨hjoint2, hcap2, henv2⟩ := hfam T hδ_le hδ hδZ hball
  refine ⟨C0da, deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε,
    hjoint0, hjoint2, hid, hsup0, hcap2, ?_, ?_⟩
  · intro i s hs
    refine le_trans (henv0 i s hs) (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    positivity
  · intro i s hs
    refine le_trans (henv2 i s hs) (mul_le_mul_of_nonneg_right (le_max_right _ _) ?_)
    positivity

set_option linter.unusedVariables false in
/-- Deferred input (dossier row LC-2 with its arm shares of rows LC-4/LC-5/LC-6: ONE GENERIC
child in the free background parameter `gB`, at cap literal `3` PER INSTANTIATION; pattern
class: `deTurckLieWEndo`/`slotInsertEndoFib` calculus with the inverse-Gram-traced,
sharp-raised leading-feed endomorphism loaded from the argument; at second endpoint zero the
moving-metric connection-difference leg of the DeTurck vector field carries the three-monomial
sharp-Koszul rate and refolds at three ledger copies, while the `gB`-background leg is
constant in the moving tensor and rides the order-zero part together with the inverse-Gram
one-jet content; sup anchors and two-step windows as in the Riemann-arm rows): the refold
data package for the vector-field endomorphism arm of the DeTurck Lie coefficient along the
realized path, in a free background metric. The full-subject assembly instantiates this child
TWICE — at `gB := g_bg` (the Lie coefficient's own endomorphism arm) and at `gB := g₀` (the
correction insert arm's endomorphism content) — the dossier row's `{3 + 3}` copy count across
the two uses. Every consumer transitively depends on `sorryAx` until this lands. -/
theorem exists_deTurckLieEndoArm_curvatureRefold_data
    (g₀ gB : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ (C0db : ℝ → SmoothCcTensor g₀ 2 2) (C2db : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0db (δ := δ) (δ' := δ) ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 C2db (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            appCc (I := I) (M := M) g₀ 2 2
                (deTurckLieEndoArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) gB)
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              appCc (I := I) (M := M) g₀ 2 2 (C0db s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                appCc (I := I) (M := M) g₀ 4 2 (C2db s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0db s).toSection x) ≤
              Λ ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((C2db s).toSection x) ≤
              (max (3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0)
                ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0db s)‖ ^ 2 ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 4 2 i (C2db s)‖ ^ 2 ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) :=
  sorry

set_option linter.unusedVariables false in
/-- Public re-derivation, at second endpoint zero and first path parameter zero, of the
exact fibre linearization of the covariant gradient of the connection difference along the
realized path (the private `covDerivConnDiff_realizedFam_eq_smul_covDerivSharp` of the
path-Palatini development is stated for interior first parameters only; this is the
endpoint version its refold consumers need, with the private sharp-Koszul field spelled
out). Resolves dossier item OPEN-2 as a public wrapper: the connection difference is the
path-parameter multiple of the sharp-Koszul field (`connDiff_realizedFam_eq_smul_sharp`),
and the scalar rate exits the covariant derivative by linearity. -/
theorem covDerivConnDiff_realizedFam_zero_endpoint_eq_smul_covDerivSharp
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    covDerivConnDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (fun b => X b) (fun b => Y b) (fun b => Z b) x =
      s •
        ((LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)).toFun
            (fun b : M =>
              metricSharp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
                (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
                  (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b))) x (X x)
          - metricSharp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
              (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) x (Z x)
              (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
                (fun b => X b) (fun b => Y b) x))
          - metricSharp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) x
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
              (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) x
              (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
                (fun b => X b) (fun b => Z b) x) (Y x))) := by
  classical
  have h0_mem : (0 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt ⟨le_refl (0 : ℝ), zero_le_one⟩
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hexpand : covDerivConnDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (fun b => X b) (fun b => Y b) (fun b => Z b) x =
      (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)).toFun
          (diffSec (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
            (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s))
            (fun b => Y b) (fun b => Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (realizedFam (I := I) g₀ T 0 hδ hδZ 0) x (Z x)
            (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
              (fun b => X b) (fun b => Y b) x)
        - PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (realizedFam (I := I) g₀ T 0 hδ hδZ 0) x
            (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
              (fun b => X b) (fun b => Z b) x) (Y x) := rfl
  rw [hexpand]
  have hpoint : ∀ (b : M) (u ζ : TangentSpace I b),
      PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b u ζ =
      s • metricSharp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
        (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
          (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b u ζ) := by
    intro b u ζ
    have h := connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T 0 hδ_lt hδ hδ_lt hδZ
      h0_mem hs_mem b u ζ
    rwa [sub_zero] at h
  by_cases hs0 : s = 0
  · subst hs0
    have hconn0 : ∀ (b : M) (u ζ : TangentSpace I b),
        PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
          (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b u ζ = 0 := by
      intro b u ζ
      rw [PDE.DeTurck.connDiff_self]
      rfl
    have hdz : diffSec (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
        (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
        (fun b => Y b) (fun b => Z b) =
        (0 : ℝ) • fun b : M => X b := by
      funext b
      rw [Pi.smul_apply, zero_smul]
      exact hconn0 b (Z b) (Y b)
    rw [hdz]
    have hσX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (X b)) x :=
      (X.contMDiff x).mdifferentiableAt (by simp)
    have hsmul := (LeviCivita (I := I)
      (realizedFam (I := I) g₀ T 0 hδ hδZ 0)).isCovariantDerivativeOnUniv.smul_const
      (σ := fun b => X b) (x := x) (0 : ℝ) hσX (Set.mem_univ x)
    rw [hsmul, ContinuousLinearMap.smul_apply]
    rw [hconn0 x (Z x) (covApply (LeviCivita (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ 0)) (fun b => X b) (fun b => Y b) x),
      hconn0 x (covApply (LeviCivita (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ 0)) (fun b => X b) (fun b => Z b) x) (Y x)]
    rw [zero_smul, zero_smul]
    simp
  · have hconn_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b))) :=
      PDE.DeTurck.connDiff_contMDiff (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
        Z.contMDiff Y.contMDiff
    have hΨ_eq : (fun b : M =>
        metricSharp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
            (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b))) =
        (fun b : M => s⁻¹ •
          PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)) := by
      funext b
      rw [hpoint b (Z b) (Y b), smul_smul, inv_mul_cancel₀ hs0, one_smul]
    have hΨ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (metricSharp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
              (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)))) := by
      have hsmul' := ContMDiff.smul_section
        (f := fun _ : M => s⁻¹)
        (s := fun b : M =>
          PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b))
        contMDiff_const hconn_smooth
      refine hsmul'.congr (fun b => ?_)
      refine congrArg (TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b) ?_
      change metricSharp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
            (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)) =
        s⁻¹ • PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)
      exact congrFun hΨ_eq b
    have hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (metricSharp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
              (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)))) x :=
      (hΨ_smooth x).mdifferentiableAt (by simp)
    have hdiffSec : diffSec (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
        (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (fun b => Y b) (fun b => Z b) =
        s • (fun b : M =>
          metricSharp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
              (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b))) := by
      funext b
      rw [Pi.smul_apply]
      exact hpoint b (Z b) (Y b)
    rw [hdiffSec]
    have hsmul := (LeviCivita (I := I)
      (realizedFam (I := I) g₀ T 0 hδ hδZ 0)).isCovariantDerivativeOnUniv.smul_const
      (σ := fun b : M =>
        metricSharp (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
            (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)))
      (x := x) s hσ (Set.mem_univ x)
    rw [hsmul, ContinuousLinearMap.smul_apply]
    rw [hpoint x (Z x) (covApply (LeviCivita (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ 0)) (fun b => X b) (fun b => Y b) x),
      hpoint x (covApply (LeviCivita (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ 0)) (fun b => X b) (fun b => Z b) x) (Y x)]
    module

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
