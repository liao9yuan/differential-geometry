import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmOrder1KoszulTameEnvelope

/-!
# Per-order L² tame envelopes for the order-one connection-difference coefficient

The four-trace `appCcRS` refold of the order-one connection-difference Ricci-linearization
coefficient field: `linearizedRicciConnDiffOrder1CoeffField g₀ g₁` factors as the four-trace
cometric cast field (rank `(4,2)`) applied against the order-one connection-difference Leibniz
kernel field (rank `(3,4)`), mirroring `ricciArmOrder1KoszulCoeff_eq_appCcRS`. On top of the
refold, the generic ball-uniform order-0 sup bounds and all-order per-order L² tame jet
envelopes for the two arms feed the diagonal-product-grid calculus exactly as in
`ricciArmOrder1KoszulCoeff_perOrder_l2_tameEnvelope_generic`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
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

set_option linter.unusedSectionVars false in
/-- Smoothness of the four-trace cometric fiber family `x ↦ ricciCometricFourTraceCLM g₁ x`
viewed as a rank-`(4,2)` tensor section. -/
theorem ricciCometricFourTraceCastG0Fib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from
          ricciCometricFourTraceCLM (I := I) g₁ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun x : M => ricciCometricFourTraceCLM (I := I) g₁ x)
  intro Y
  have hCK := ricciCometricFourTraceCLM_field_contMDiff (I := I) g₁ (fun x => Y x) Y.contMDiff
  refine hCK.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) rfl

set_option linter.unusedSectionVars false in
/-- Smoothness of the order-one connection-difference Leibniz kernel fiber family
`x ↦ linearizedRicciConnDiffOrder1CLM x (A x)`, `A = connDiffSection g₁ g₀`, viewed as a
rank-`(3,4)` tensor section. -/
theorem linearizedRicciConnDiffOrder1KernelFib_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 4 I z) x
        (show Tensor0SBundle.TensorRSSpace 3 4 I x from
          linearizedRicciConnDiffOrder1CLM (I := I) x
            ((connDiffSection (I := I) g₁ g₀).toSection x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z)
    (φ := fun x : M => linearizedRicciConnDiffOrder1CLM (I := I) x
      ((connDiffSection (I := I) g₁ g₀).toSection x))
  intro Y
  have hE1 := linearizedRicciConnDiffOrder1CLM_field_contMDiff (I := I) g₀ g₁
    (fun x => Y x) Y.contMDiff
  refine hE1.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x t) rfl

/-- The four-trace cometric cast field: the fiber family `ricciCometricFourTraceCLM g₁` of the
perturbed metric `g₁`, cast as a rank-`(4,2)` smooth compactly supported tensor over the base
metric `g₀`. The `p = 2` four-trace analogue of `cometricCastG0`. -/
def ricciCometricFourTraceCastG0 (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from
          ricciCometricFourTraceCLM (I := I) g₁ x)
      contMDiff_toFun := ricciCometricFourTraceCastG0Fib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- The order-one connection-difference Leibniz kernel field: the fiber family
`x ↦ linearizedRicciConnDiffOrder1CLM x (A x)` with `A = connDiffSection g₁ g₀`, as a
rank-`(3,4)` smooth compactly supported tensor over `g₀`. -/
def linearizedRicciConnDiffOrder1KernelField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 3 4 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 3 4 I x from
          linearizedRicciConnDiffOrder1CLM (I := I) x
            ((connDiffSection (I := I) g₁ g₀).toSection x))
      contMDiff_toFun := linearizedRicciConnDiffOrder1KernelFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem ricciCometricFourTraceCastG0_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciCometricFourTraceCastG0 (I := I) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from
        ricciCometricFourTraceCLM (I := I) g₁ x) := rfl

set_option linter.unusedSectionVars false in
@[simp] theorem linearizedRicciConnDiffOrder1KernelField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 4 I x from
        linearizedRicciConnDiffOrder1CLM (I := I) x
          ((connDiffSection (I := I) g₁ g₀).toSection x)) := rfl

set_option linter.unusedSectionVars false in
/-- The four-trace `appCcRS` refold: the order-one connection-difference coefficient field is
the composition of the four-trace cometric cast field against the order-one Leibniz kernel
field, mirroring `ricciArmOrder1KoszulCoeff_eq_appCcRS`. -/
theorem linearizedRicciConnDiffOrder1CoeffField_eq_appCcRS
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g₀ g₁ =
      appCcRS (I := I) (M := M) g₀ 3 4 2
        (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
        (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

set_option linter.unusedVariables false in
/-- Ball-uniform order-0 sup bound and all-order per-order L² tame jet envelope for the
four-trace cometric cast field, generic in a perturbed metric `g₁ = g₀ + P`.

POSITED CHILD (`sorry`): requires the `p = 2` background + slot-insert-correction cast
decomposition and the argument-slot permutation jet calculus for the four-trace combination.
Consumers transitively depend on `sorryAx` until this lands. -/
theorem ricciCometricFourTraceCastG0_order0sup_perOrder_l2_tameEnvelope_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (K : ℕ → ℝ), 0 ≤ Λ ∧ (∀ q, 0 ≤ K q) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((ricciCometricFourTraceCastG0 (I := I) g₀ g₁).toSection x) ≤ Λ ^ 2) ∧
        ∀ (q : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 4 2 q
              (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤
            K q * (1 + ∑ j ∈ Finset.range (q + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := sorry

set_option linter.unusedVariables false in
/-- Ball-uniform order-0 sup bound and all-order per-order L² tame jet envelope for the
order-one connection-difference Leibniz kernel field, generic in `g₁ = g₀ + P`.

POSITED CHILD (`sorry`): requires the covariant-Leibniz calculus for the `connContrCLM`
core against the connection-difference jets, with the surrounding slot-permutation jet
invariances. Consumers transitively depend on `sorryAx` until this lands. -/
theorem linearizedRicciConnDiffOrder1KernelField_order0sup_perOrder_l2_tameEnvelope_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (K : ℕ → ℝ), 0 ≤ Λ ∧ (∀ l, 0 ≤ K l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
            ((linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁).toSection x) ≤ Λ ^ 2) ∧
        ∀ (l : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
              (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ^ 2 ≤
            K l * (1 + ∑ j ∈ Finset.range (l + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := sorry

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
