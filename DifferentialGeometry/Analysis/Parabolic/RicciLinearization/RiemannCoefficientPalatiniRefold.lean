import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
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
/-- Deferred input (dossier row RA-3b, conjunct 5 of the frozen Riemann-arm refold data;
pattern class: `RiemannCoeff` ball-uniform sups — `RicciThreeArmCorrectionFieldBound`
`@259`/`@812` with `T′ := 0` via `hδZ`, triangle with the background-difference
diagonal-product grid at order zero, `Csob` convex-perturbation pointwise `C²`, and the
background uniform fibre-norm bound): pointwise fibre-norm sup for the moving order-zero
Riemann coefficient along the realized path, uniform over the moving tensor's `a + 2`-jet
ball. Every consumer transitively depends on `sorryAx` until this lands. -/
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
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) ≤ Λ ^ 2 :=
  sorry

set_option linter.unusedVariables false in
/-- Deferred input (dossier row RA-1, conjunct 3 of the frozen Riemann-arm refold data
bundled with the order-zero-part conjuncts 1, 4, 7; pattern class: `riemannSec_difference`
Palatini split + the exact path linearizations at second endpoint zero + the
`appCc`/`unitModel` evaluation calculus + fixed-frame neighbourhood gluing, with the
order-zero part `C0ra := bgRComm + arm0AA + (∇♯)K`-residual + Ricci-fold remainder): the
per-parameter refold identity for the moving order-zero Riemann coefficient, with the
second-gradient part the CONSTRUCTED folded four-monomial kernel family
`riemannPalatiniRefoldC2Family` at existentially pinned permutation quadruples, and an
order-zero family carrying joint smoothness, a ball-uniform pointwise fibre-norm sup, and
the two-step jet window. Every consumer transitively depends on `sorryAx` until this
lands. -/
theorem exists_riemannPalatini_refold_identity_data
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∃ qA qB : Fin 4 → Equiv.Perm (Fin 4),
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

set_option linter.unusedVariables false in
/-- Deferred input (dossier row RA-2, conjunct 2 of the frozen Riemann-arm refold data;
pattern class: joint smoothness of the realized-family coefficient constructions —
`CovGradParametricJointSmooth` class plus the fixed-frame patching of the refold kernel
calculus, jointly in the path parameter): joint smoothness of the constructed
second-gradient refold family, for every permutation-quadruple convention. Every consumer
transitively depends on `sorryAx` until this lands. -/
theorem riemannPalatiniRefoldC2Family_threeArmHjoint
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB)
      (δ := δ) (δ' := δ) :=
  sorry

set_option linter.unusedVariables false in
/-- Deferred input (dossier row RA-3a, conjunct 6 of the frozen Riemann-arm refold data;
pattern class: Koszul-sharp `δ/(1−δ)` fibre bounds — `ConnectionDifferenceFibreBound` and
the `rfns` bi-contraction bounds of `RicciThreeArmCorrectionFieldBound`, with the frame and
weight conversions absorbed into the dimensional fibre constant; small literals checked at
`n = 1, 2, 3` at fill): the pointwise fibre-norm cap for the constructed second-gradient
refold family at the FOLDED FOUR-MONOMIAL literal `4`, for every permutation-quadruple
convention. Every consumer transitively depends on `sorryAx` until this lands. -/
theorem riemannPalatiniRefoldC2Family_rfns_le
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) :
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
refold family, for every permutation-quadruple convention. Every consumer transitively
depends on `sorryAx` until this lands. -/
theorem exists_riemannPalatiniRefoldC2Family_l2JetWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (qA qB : Fin 4 → Equiv.Perm (Fin 4)) :
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
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) :=
  sorry

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
