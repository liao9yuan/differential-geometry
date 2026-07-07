import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureRefoldMonomialFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldInputSlotSymmetrization

/-!
# Residual coefficient fields of the arm-zero generic-endpoint Palatini fold

The constructive residual coefficient fields of the generic-`g₁` Palatini fold of the moving
arm-zero Ricci-linearization coefficients: the inverse-Gram quadratic residual
(`gInvDiffQuadResidualField`, the connection-difference bi-contraction at the swapped metric
pair), the shared sharp-gradient Koszul residual and Ricci-fold remainder fields
(`ricciArmSharpGradKoszulResidualField`, `ricciArmRicciFoldRemainderField`), and the
background-curvature difference and refold remainder (`bgRDiffRefoldRemainderField`), each a
pinned construction with a proven vanish-at-base litmus lemma.

The closing sym-sector cancellation equation
(`linearizedRicciConnDiffOrder0RiemannHalfBackgroundDifferenceCombinationInputSymm_eq_residualFieldSum`),
splitting the input-slot-symmetrized moving arm-zero combination onto these fields, is posited
here as a clearly-labelled deferred input (`sorry`); every consumer transitively depends on
`sorryAx` until it lands.

These fields feed the capped grid-window towers of
`Analysis/Sobolev/TensorHilbert/RicciArmResidualFieldGridWindow`; this file sits upstream of
the tame-envelope import cone
(`Analysis/Parabolic/RicciLinearization/RicciThreeArmCorrectionFieldTameEnvelope`), so the
envelope side may import the towers without an import cycle.
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

/-! ### Arm-0 residual coefficient fields of the generic-`g₁` Palatini fold (M-dossier §ii)

The pinned constructed residual fields of the leader-signed M-dossier: DEF-1
(`gInvDiffQuadResidualField`, the mechanism-B `A ⋆ A` quadratic residual, the generic-`g₁`
field-level analogue of `arm0AAField`), the two SHARED remainder fields of the fold
derivation map (`ricciArmSharpGradKoszulResidualField`, `ricciArmRicciFoldRemainderField` —
named once, serving both the RA-1 subtree and the M-child's held C-EQ), and DEF-2
(`bgRDiffRefoldRemainderField`, the bg-R trace difference plus the shared remainders at the
metric-difference weight). Every field is a pinned construction with a proven vacuity
litmus (`connDiff g₀ g₀ = 0` diagonal kill for DEF-1; `sub_self` plus the zero-weight kills
for DEF-2), certified in scratch before materialization per the leader's condition. -/

/-- The pointwise rank-`(0,2)` tensor carrying the inner product of a metric `g`. -/
def metricCcTensorFib (g : SmoothRiemannianMetric I M) (x : M) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun m => g.inner x (m 0) (m 1)
      map_update_add' := by
        have h01 : (0 : Fin 2) ≠ 1 := by decide
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h10, not_false_eq_true, map_add,
            ContinuousLinearMap.add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 2) ≠ 1 := by decide
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h10, not_false_eq_true, map_smul,
            ContinuousLinearMap.smul_apply]
      cont := ((g.inner x).continuous.comp (continuous_apply 0)).clm_apply
        (continuous_apply 1) }
    : Tensor0SSpace 2 I x)

set_option linter.unusedSectionVars false in
@[simp] lemma metricCcTensorFib_apply (g : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 2 → TangentSpace I x) :
    metricCcTensorFib (I := I) g x m = g.inner x (m 0) (m 1) := rfl

set_option linter.unusedSectionVars false in
theorem metricCcTensorFib_section_contMDiff (g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x (metricCcTensorFib (I := I) g x)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (metricCcTensorFib (I := I) g x :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g.inner x (Y (σ 0) x) (Y (σ 1) x)) x₀ :=
    (contMDiff_g_inner_of_smooth_sections (I := I) g (Y (σ 0)) (Y (σ 1))).contMDiffAt
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframeEq : ∀ k : Fin 2, e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
    intro k
    rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change g.inner x (e₁.symmL ℝ x (b (σ 0))) (e₁.symmL ℝ x (b (σ 1))) = _
  rw [hframeEq 0, hframeEq 1]

/-- A metric `g` as a smooth compactly supported rank-`(0,2)` coefficient tensor over a
background metric `g₀`. -/
def metricCcTensor (g₀ g : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞
      (letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I)
        (M := M) 2
       (⟨fun x => metricCcTensorFib (I := I) g x,
         metricCcTensorFib_section_contMDiff (I := I) g⟩ :
        Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2))
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- The difference of two metrics as a smooth compactly supported rank-`(0,2)` coefficient
tensor over the first: the canonical weight datum of the generic-`g₁` Palatini fold. -/
def metricDifferenceCcTensor (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  metricCcTensor (I := I) (M := M) g₀ g₁ - metricCcTensor (I := I) (M := M) g₀ g₀

/-- Vacuity litmus for the difference datum: it rejects the diagonal witness. -/
@[simp] theorem metricDifferenceCcTensor_self (g₀ : SmoothRiemannianMetric I M) :
    metricDifferenceCcTensor (I := I) (M := M) g₀ g₀ = 0 :=
  sub_self _

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

set_option linter.unusedSectionVars false in
private theorem metricCcTensor_ccTensorBilin (g₀ g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀ (metricCcTensor (I := I) (M := M) g₀ g) x v w =
      g.inner x v w := by
  have hround : ccTensorMultilinear (I := I) g₀ (metricCcTensor (I := I) (M := M) g₀ g) x =
      metricCcTensorFib (I := I) g x := by
    unfold ccTensorMultilinear metricCcTensor
    rw [MixedSection.toMultilinearSection_fromMultilinearSection]
    rfl
  rw [ccTensorBilin_apply]
  unfold ccTensorModel
  rw [hround]
  rfl

/-- DEF-1 (M-dossier §ii): the mechanism-B quadratic residual coefficient field at a generic
perturbed metric `g₁` — the `A ⋆ A` connection-difference bi-contraction with its `g₁⁻¹`
raisings, the field-level generic-`g₁` analogue of the realized-family `arm0AAField`. -/
def gInvDiffQuadResidualField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  connDiffBiContrCoeffField (I := I) (M := M) g₁ g₀ g₁ g₀

set_option linter.unusedSectionVars false in
@[simp] theorem gInvDiffQuadResidualField_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) :
    (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) g₁ g₀ g₁ g₀ x)) := rfl

set_option linter.unusedSectionVars false in
/-- Vacuity litmus for DEF-1: the quadratic residual field rejects the diagonal witness
`g₁ = g₀` — both connection-difference legs vanish. -/
theorem gInvDiffQuadResidualField_self (g₀ : SmoothRiemannianMetric I M) :
    gInvDiffQuadResidualField (I := I) (M := M) g₀ g₀ = 0 := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [gInvDiffQuadResidualField_toSection]
  have hzero : connDiffBiContrFib (I := I) g₀ g₀ g₀ g₀ x = 0 := by
    apply ContinuousLinearMap.ext
    intro D
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [show connDiffBiContrFib (I := I) g₀ g₀ g₀ g₀ x =
        connDiffBiContrFibFixedFrame (I := I) g₀ g₀ g₀ g₀
          (smoothOrthoFrame (I := I) g₀ x) x from rfl]
    rw [connDiffBiContrFibFixedFrame_toModel]
    have hconn : PDE.DeTurck.connDiff (I := I) g₀ g₀ = 0 :=
      PDE.DeTurck.connDiff_self (I := I) g₀
    simp only [hconn, Pi.zero_apply, ContinuousLinearMap.zero_apply, map_zero,
      zero_mul, Finset.sum_const_zero,
      Tensor0SSpace.toModel_zero, ContinuousMultilinearMap.zero_apply]
  rw [hzero]
  rfl

/-! ### Stage A′ — the antisymmetrized `A ⋆ A` commutator coefficient field (Form B Q_true) -/

/-- The bilinear kernel of the antisymmetrized connection-difference commutator arm at a
fixed frame pair `(p, q)`: with `A := connDiff g₁ g₀` in the `(ARGUMENT)(DIRECTION)`
application order of `connDiff_apply`, the kernel is the two-monomial difference
`g₁(A[A[q; p]; v₀], v₁) − g₁(A[A[q; v₀]; p], v₁)` — the quadratic `A ⋆ A` bi-contraction
content of the corrected arm-zero fold (Form B `Q_true`), with the curvature-style
antisymmetrization exchanging the frame direction and the first input direction. One-jet
in each connection-difference leg; the `g₁`-inner is a zero-jet algebraic leg. -/
def connDiffAACommKernelBilin (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 =>
        g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) v0)
          - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) p)
      map_add' := fun v0 v0' => by
        simp only [map_add, ContinuousLinearMap.add_apply]
        abel
      map_smul' := fun c v0 => by
        rw [RingHom.id_apply]
        simp only [map_smul, ContinuousLinearMap.smul_apply]
        rw [smul_sub] }

set_option linter.unusedSectionVars false in
@[simp] lemma connDiffAACommKernelBilin_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (p q v0 v1 : TangentSpace I x) :
    connDiffAACommKernelBilin (I := I) g₀ g₁ x p q v0 v1 =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) v0) v1
        - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) p) v1 := by
  rw [connDiffAACommKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearMap.sub_apply]

/-- The antisymmetrized `A ⋆ A` commutator kernel repackaged as a bilinear form in the
frame pair, for the orthonormal-frame trace-independence patching. -/
def frameConnDiffAACommKernel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p =>
        haveI : FiniteDimensional ℝ (TangentSpace I x) :=
          inferInstanceAs (FiniteDimensional ℝ E)
        LinearMap.toContinuousLinearMap
          { toFun := fun q => connDiffAACommKernelBilin (I := I) g₀ g₁ x p q v0 v1
            map_add' := fun q q' => by
              rw [connDiffAACommKernelBilin_apply, connDiffAACommKernelBilin_apply,
                connDiffAACommKernelBilin_apply]
              simp only [map_add, ContinuousLinearMap.add_apply]
              ring
            map_smul' := fun c q => by
              rw [RingHom.id_apply, connDiffAACommKernelBilin_apply,
                connDiffAACommKernelBilin_apply]
              simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
              ring }
      map_add' := fun p p' => by
        apply ContinuousLinearMap.ext
        intro q
        rw [ContinuousLinearMap.add_apply, LinearMap.coe_toContinuousLinearMap',
          LinearMap.coe_toContinuousLinearMap', LinearMap.coe_toContinuousLinearMap']
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [connDiffAACommKernelBilin_apply, connDiffAACommKernelBilin_apply,
          connDiffAACommKernelBilin_apply]
        simp only [map_add, ContinuousLinearMap.add_apply]
        ring
      map_smul' := fun c p => by
        rw [RingHom.id_apply]
        apply ContinuousLinearMap.ext
        intro q
        rw [ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap',
          LinearMap.coe_toContinuousLinearMap']
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [connDiffAACommKernelBilin_apply, connDiffAACommKernelBilin_apply]
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring }

set_option linter.unusedSectionVars false in
@[simp] lemma frameConnDiffAACommKernel_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (v0 v1 p q : TangentSpace I x) :
    frameConnDiffAACommKernel (I := I) g₀ g₁ x v0 v1 p q =
      connDiffAACommKernelBilin (I := I) g₀ g₁ x p q v0 v1 := by
  rw [frameConnDiffAACommKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

/-- Summand of the antisymmetrized `A ⋆ A` commutator arm at a frame pair: the input datum
evaluated at the frame pair weights the kernel bilinear form. -/
def connDiffAACommSummandFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (connDiffAACommKernelBilin (I := I) g₀ g₁ x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

set_option linter.unusedSectionVars false in
@[simp] lemma connDiffAACommSummandFib_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connDiffAACommSummandFib (I := I) g₀ g₁ x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        connDiffAACommKernelBilin (I := I) g₀ g₁ x p q (v 0) (v 1) := by
  rw [connDiffAACommSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply, smul_eq_mul]
  rfl

/-- The antisymmetrized `A ⋆ A` commutator bi-contraction at a fixed frame family. -/
def connDiffAACommBiContrFibFixedFrame (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x)

set_option linter.unusedSectionVars false in
lemma connDiffAACommBiContrFibFixedFrame_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        (connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁ B x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)]) *
          connDiffAACommKernelBilin (I := I) g₀ g₁ x (B a x) (B b x) (v 0) (v 1) := by
  classical
  rw [connDiffAACommBiContrFibFixedFrame, ContinuousLinearMap.sum_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, connDiffAACommSummandFib_toModel]

theorem connDiffAACommKernelBilin_homSection_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x
        (connDiffAACommKernelBilin (I := I) g₀ g₁ x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => connDiffAACommKernelBilin (I := I) g₀ g₁ x (p x) (q x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => connDiffAACommKernelBilin (I := I) g₀ g₁ x (p x) (q x) (V0 x))
  intro W
  have hAqp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (p b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hq hp
  have hAAqpV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (p b)) (V0 b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hAqp V0.contMDiff
  have hAqV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (V0 b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hq V0.contMDiff
  have hAAqVp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (V0 b)) (p b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hAqV hp
  have hs1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (q x) (p x)) (V0 x)) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (p b)) (V0 b), hAAqpV⟩
      ⟨fun b => W b, W.contMDiff⟩
  have hs2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (q x) (V0 x)) (p x)) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (V0 b)) (p b), hAAqVp⟩
      ⟨fun b => W b, W.contMDiff⟩
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (q x) (p x)) (V0 x)) (W x)
        - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (q x) (V0 x)) (p x)) (W x)) :=
    hs1.sub hs2
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change connDiffAACommKernelBilin (I := I) g₀ g₁ y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [connDiffAACommKernelBilin_apply]
  rfl

theorem connDiffAACommBiContrFibFixedFrame_apply_section_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁ B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b' => Y b') Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => connDiffAACommKernelBilin (I := I) g₀ g₁ x (B a x) (B b x))
      (connDiffAACommKernelBilin_homSection_contMDiff (I := I) g₀ g₁ (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x : M =>
        Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set T2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M =>
          connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hT2_def
  have hcoe1 : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), T2 a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
            Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), T2 a b) Finset.univ
  have hcoe2 : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), T2 a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((T2 a b : Π z : M, Tensor0SSpace 2 I z)) :=
    fun a => map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => T2 a b) Finset.univ
  have hStot := (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    T2 a b).contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  have hval : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x) := by
    have h1 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) x =
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          T2 a b : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
            Π z : M, Tensor0SSpace 2 I z) x := rfl
    rw [h1, hcoe1, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoe2 a, Finset.sum_apply]
    rfl
  rw [connDiffAACommBiContrFibFixedFrame, ContinuousLinearMap.sum_apply]
  rw [show ∑ a : Fin (Module.finrank ℝ E), (∑ b : Fin (Module.finrank ℝ E),
      connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x)) (Y x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x) from
    Finset.sum_congr rfl (fun a _ => ContinuousLinearMap.sum_apply _ _ _)]
  rw [← hval]

theorem connDiffAACommBiContrFibFixedFrame_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM
          (connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁ B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁ B x)
  intro Y
  exact connDiffAACommBiContrFibFixedFrame_apply_section_contMDiff
    (I := I) g₀ g₁ B hB Y

/-- The antisymmetrized `A ⋆ A` commutator bi-contraction at the moving `g₁`-orthonormal
frames: the Form B `Q_true` fibre. -/
def connDiffAACommBiContrFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₁ x) x

set_option linter.unusedSectionVars false in
/-- Fibre evaluation (the `Q_true` kernel shape at the moving `g₁`-orthonormal frames):
the datum evaluated at the frame pair weights the antisymmetrized `A ⋆ A` kernel. -/
lemma connDiffAACommBiContrFib_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connDiffAACommBiContrFib (I := I) g₀ g₁ x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)]) *
          connDiffAACommKernelBilin (I := I) g₀ g₁ x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1) := by
  rw [connDiffAACommBiContrFib, connDiffAACommBiContrFibFixedFrame_toModel]

theorem connDiffAACommBiContrFib_eq_fixedFrame_on_nbhd
    (g₀ g₁ : SmoothRiemannianMetric I M) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    connDiffAACommBiContrFib (I := I) g₀ g₁ y =
      connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁
        (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [connDiffAACommBiContrFib, connDiffAACommBiContrFibFixedFrame_toModel,
    connDiffAACommBiContrFibFixedFrame_toModel]
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)]) *
          connDiffAACommKernelBilin (I := I) g₀ g₁ y (Bf a) (Bf b) (v 0) (v 1) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameConnDiffAACommKernel (I := I) g₀ g₁ y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameConnDiffAACommKernel_apply,
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rw [mul_comm]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameConnDiffAACommKernel (I := I) g₀ g₁ y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

theorem connDiffAACommBiContrFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffAACommBiContrFib (I := I) g₀ g₁ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    connDiffAACommBiContrFibFixedFrame_contMDiff (I := I) g₀ g₁
      (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (connDiffAACommBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₀ g₁ x₀ hy))

/-- The Form B `Q_true` field: the antisymmetrized `A ⋆ A` commutator coefficient field at
a generic perturbed metric `g₁` — the `g₁`-orthonormal double contraction of the quadratic
connection-difference commutator kernel
`g₁(A[A[B̃_b; B̃_a]; v₀] − A[A[B̃_b; v₀]; B̃_a], v₁)`, `A := connDiff g₁ g₀` in the
`(ARGUMENT)(DIRECTION)` order of `connDiff_apply`. Pure `A ⋆ A` content (no moving-metric
curvature); one-jet in each connection-difference leg; the two `g₁`-frame legs and the
`g₁`-inner are zero-jet algebraic legs. -/
def ricciArmOrder0AACommCoeffField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connDiffAACommBiContrFib (I := I) g₀ g₁ x))
      contMDiff_toFun := connDiffAACommBiContrFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem ricciArmOrder0AACommCoeffField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffAACommBiContrFib (I := I) g₀ g₁ x)) := rfl

set_option linter.unusedSectionVars false in
/-- Vacuity litmus at the fibre (zero-perturbation kill): the antisymmetrized `A ⋆ A`
commutator fibre rejects the diagonal witness `g₁ = g₀` — both connection-difference legs
of each kernel monomial vanish. -/
theorem connDiffAACommBiContrFib_self (g₀ : SmoothRiemannianMetric I M) (x : M) :
    connDiffAACommBiContrFib (I := I) g₀ g₀ x = 0 := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [connDiffAACommBiContrFib, connDiffAACommBiContrFibFixedFrame_toModel]
  have hconn : PDE.DeTurck.connDiff (I := I) g₀ g₀ = 0 :=
    PDE.DeTurck.connDiff_self (I := I) g₀
  rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      (Tensor0SSpace.toModel D
        ![(smoothOrthoFrame (I := I) g₀ x a x : E),
          (smoothOrthoFrame (I := I) g₀ x b x : E)]) *
        connDiffAACommKernelBilin (I := I) g₀ g₀ x
          (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₀ x b x)
          (v 0) (v 1)) = 0 from
    Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => by
      rw [connDiffAACommKernelBilin_apply]
      simp only [hconn, Pi.zero_apply, ContinuousLinearMap.zero_apply, map_zero,
        sub_self, mul_zero]))]
  simp only [ContinuousLinearMap.zero_apply, Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply]

set_option linter.unusedSectionVars false in
/-- Vacuity litmus for the Form B `Q_true` field: it rejects the diagonal witness
`g₁ = g₀` — the connection difference vanishes, killing both quadratic legs. -/
theorem ricciArmOrder0AACommCoeffField_self (g₀ : SmoothRiemannianMetric I M) :
    ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₀ = 0 := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [ricciArmOrder0AACommCoeffField_toSection, connDiffAACommBiContrFib_self]
  rfl

/-! ### Stage B — the (∇♯)K sharp-gradient Koszul residual field (shared, per fold map E6) -/

private lemma vec3_upd_zero {F : Type*} (a b c z : F) :
    Function.update ![a, b, c] 0 z = ![z, b, c] := by
  funext k
  fin_cases k <;> simp [Function.update]

private lemma vec3_upd_one {F : Type*} (a b c z : F) :
    Function.update ![a, b, c] 1 z = ![a, z, c] := by
  funext k
  fin_cases k <;> simp [Function.update]

private lemma vec3_upd_two {F : Type*} (a b c z : F) :
    Function.update ![a, b, c] 2 z = ![a, b, z] := by
  funext k
  fin_cases k <;> simp [Function.update]

set_option linter.unusedSectionVars false in
/-- Additivity of the linearized Koszul covector in its first argument slot. -/
lemma linearizedKoszulCovec_add_fst (g' : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g' 0 2) (x : M) (u u' ζ : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g' S x (u + u') ζ =
      linearizedKoszulCovec (I := I) g' S x u ζ +
        linearizedKoszulCovec (I := I) g' S x u' ζ := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.add_apply, linearizedKoszulCovec_apply, linearizedKoszulCovec_apply,
    linearizedKoszulCovec_apply]
  set G := unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x with hG
  have h1 : G ![ζ, u + u', z] = G ![ζ, u, z] + G ![ζ, u', z] := by
    have h := G.map_update_add ![ζ, u, z] 1 u u'
    rwa [vec3_upd_one, vec3_upd_one, vec3_upd_one] at h
  have h2 : G ![u + u', ζ, z] = G ![u, ζ, z] + G ![u', ζ, z] := by
    have h := G.map_update_add ![u, ζ, z] 0 u u'
    rwa [vec3_upd_zero, vec3_upd_zero, vec3_upd_zero] at h
  have h3 : G ![z, ζ, u + u'] = G ![z, ζ, u] + G ![z, ζ, u'] := by
    have h := G.map_update_add ![z, ζ, u] 2 u u'
    rwa [vec3_upd_two, vec3_upd_two, vec3_upd_two] at h
  rw [h1, h2, h3]
  ring

set_option linter.unusedSectionVars false in
/-- Homogeneity of the linearized Koszul covector in its first argument slot. -/
lemma linearizedKoszulCovec_smul_fst (g' : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g' 0 2) (x : M) (c : ℝ) (u ζ : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g' S x (c • u) ζ =
      c • linearizedKoszulCovec (I := I) g' S x u ζ := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.smul_apply, linearizedKoszulCovec_apply, linearizedKoszulCovec_apply]
  set G := unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x with hG
  have h1 : G ![ζ, c • u, z] = c • G ![ζ, u, z] := by
    have h := G.map_update_smul ![ζ, u, z] 1 c u
    rwa [vec3_upd_one, vec3_upd_one] at h
  have h2 : G ![c • u, ζ, z] = c • G ![u, ζ, z] := by
    have h := G.map_update_smul ![u, ζ, z] 0 c u
    rwa [vec3_upd_zero, vec3_upd_zero] at h
  have h3 : G ![z, ζ, c • u] = c • G ![z, ζ, u] := by
    have h := G.map_update_smul ![z, ζ, u] 2 c u
    rwa [vec3_upd_two, vec3_upd_two] at h
  rw [h1, h2, h3]
  simp only [smul_eq_mul]
  ring

set_option linter.unusedSectionVars false in
/-- Additivity of the linearized Koszul covector in its second argument slot. -/
lemma linearizedKoszulCovec_add_snd (g' : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g' 0 2) (x : M) (u ζ ζ' : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g' S x u (ζ + ζ') =
      linearizedKoszulCovec (I := I) g' S x u ζ +
        linearizedKoszulCovec (I := I) g' S x u ζ' := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.add_apply, linearizedKoszulCovec_apply, linearizedKoszulCovec_apply,
    linearizedKoszulCovec_apply]
  set G := unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x with hG
  have h1 : G ![ζ + ζ', u, z] = G ![ζ, u, z] + G ![ζ', u, z] := by
    have h := G.map_update_add ![ζ, u, z] 0 ζ ζ'
    rwa [vec3_upd_zero, vec3_upd_zero, vec3_upd_zero] at h
  have h2 : G ![u, ζ + ζ', z] = G ![u, ζ, z] + G ![u, ζ', z] := by
    have h := G.map_update_add ![u, ζ, z] 1 ζ ζ'
    rwa [vec3_upd_one, vec3_upd_one, vec3_upd_one] at h
  have h3 : G ![z, ζ + ζ', u] = G ![z, ζ, u] + G ![z, ζ', u] := by
    have h := G.map_update_add ![z, ζ, u] 1 ζ ζ'
    rwa [vec3_upd_one, vec3_upd_one, vec3_upd_one] at h
  rw [h1, h2, h3]
  ring

set_option linter.unusedSectionVars false in
/-- Homogeneity of the linearized Koszul covector in its second argument slot. -/
lemma linearizedKoszulCovec_smul_snd (g' : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g' 0 2) (x : M) (c : ℝ) (u ζ : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g' S x u (c • ζ) =
      c • linearizedKoszulCovec (I := I) g' S x u ζ := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.smul_apply, linearizedKoszulCovec_apply, linearizedKoszulCovec_apply]
  set G := unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x with hG
  have h1 : G ![c • ζ, u, z] = c • G ![ζ, u, z] := by
    have h := G.map_update_smul ![ζ, u, z] 0 c ζ
    rwa [vec3_upd_zero, vec3_upd_zero] at h
  have h2 : G ![u, c • ζ, z] = c • G ![u, ζ, z] := by
    have h := G.map_update_smul ![u, ζ, z] 1 c ζ
    rwa [vec3_upd_one, vec3_upd_one] at h
  have h3 : G ![z, c • ζ, u] = c • G ![z, ζ, u] := by
    have h := G.map_update_smul ![z, ζ, u] 1 c ζ
    rwa [vec3_upd_one, vec3_upd_one] at h
  rw [h1, h2, h3]
  simp only [smul_eq_mul]
  ring

set_option linter.unusedSectionVars false in
/-- The linearized Koszul covector of the zero weight vanishes (zero-weight kill). -/
lemma linearizedKoszulCovec_zero_weight (g' : SmoothRiemannianMetric I M) (x : M)
    (u ζ : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g' (0 : SmoothCcTensor g' 0 2) x u ζ = 0 := by
  apply LinearMap.ext
  intro z
  rw [linearizedKoszulCovec_apply, LinearMap.zero_apply]
  have hzero : covGrad (I := I) (M := M) g' 0 2 (0 : SmoothCcTensor g' 0 2) = 0 :=
    covGrad_zero (I := I) (M := M) g' 0 2
  rw [hzero]
  have hunit : ∀ v : Fin 3 → TangentSpace I x,
      unitModel (I := I) (M := M) g' 3 (0 : SmoothCcTensor g' 0 3) x v = 0 := by
    intro v
    rw [unitModel]
    have h0 : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (0 : SmoothCcTensor g' 0 3).toSection x) = 0 := rfl
    rw [h0, ContinuousLinearMap.zero_apply, Tensor0SSpace.toModel_zero]
    rfl
  rw [hunit ![ζ, u, z], hunit ![u, ζ, z], hunit ![z, ζ, u]]
  ring

/-- The `g₁`-sharp raise of the `g₀`-Koszul covector of a weight `S` — the mixed-metric
raised Koszul vector whose fold-pair commutator content the sharp-gradient residual field
carries. The metric raisings sit at the zero jet; the weight enters through its one-jet. -/
def sharpRaisedKoszulVec (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (u ζ : TangentSpace I x) : TangentSpace I x :=
  metricSharp (I := I) g₁ x (linearizedKoszulCovec (I := I) g₀ S x u ζ)

set_option linter.unusedSectionVars false in
lemma sharpRaisedKoszulVec_add_fst (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (u u' ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ S x (u + u') ζ =
      sharpRaisedKoszulVec (I := I) g₀ g₁ S x u ζ +
        sharpRaisedKoszulVec (I := I) g₀ g₁ S x u' ζ := by
  rw [sharpRaisedKoszulVec, sharpRaisedKoszulVec, sharpRaisedKoszulVec,
    linearizedKoszulCovec_add_fst, metricSharp_def, metricSharp_def, metricSharp_def, map_add]

set_option linter.unusedSectionVars false in
lemma sharpRaisedKoszulVec_smul_fst (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (c : ℝ) (u ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ S x (c • u) ζ =
      c • sharpRaisedKoszulVec (I := I) g₀ g₁ S x u ζ := by
  rw [sharpRaisedKoszulVec, sharpRaisedKoszulVec, linearizedKoszulCovec_smul_fst,
    metricSharp_def, metricSharp_def, map_smul]

set_option linter.unusedSectionVars false in
lemma sharpRaisedKoszulVec_add_snd (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (u ζ ζ' : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ S x u (ζ + ζ') =
      sharpRaisedKoszulVec (I := I) g₀ g₁ S x u ζ +
        sharpRaisedKoszulVec (I := I) g₀ g₁ S x u ζ' := by
  rw [sharpRaisedKoszulVec, sharpRaisedKoszulVec, sharpRaisedKoszulVec,
    linearizedKoszulCovec_add_snd, metricSharp_def, metricSharp_def, metricSharp_def, map_add]

set_option linter.unusedSectionVars false in
lemma sharpRaisedKoszulVec_smul_snd (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (c : ℝ) (u ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ S x u (c • ζ) =
      c • sharpRaisedKoszulVec (I := I) g₀ g₁ S x u ζ := by
  rw [sharpRaisedKoszulVec, sharpRaisedKoszulVec, linearizedKoszulCovec_smul_snd,
    metricSharp_def, metricSharp_def, map_smul]

set_option linter.unusedSectionVars false in
lemma sharpRaisedKoszulVec_zero_weight (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (u ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ (0 : SmoothCcTensor g₀ 0 2) x u ζ = 0 := by
  rw [sharpRaisedKoszulVec, linearizedKoszulCovec_zero_weight, metricSharp_def, map_zero]

/-- The bilinear kernel of the sharp-gradient Koszul residual arm at a fixed frame pair
`(p, q)`: the fold-pair antisymmetrized `(∇⁰♯_{g₁})K_S` content, written through the
lowered-connection-difference identity
`g₁((∇⁰_X ♯_{g₁})ω, z) = −g₁(A(X, ♯_{g₁}ω), z) − g₁(♯_{g₁}ω, A(X, z))`
(`A := connDiff g₁ g₀`, `∇⁰g₀ = 0`), so that the metric raisings sit at the zero jet. -/
def sharpGradKoszulKernelBilin (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 =>
        (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p
            (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q v0))
          + (g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q v0)).comp
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p))
        - (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0
            (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q p))
          + (g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q p)).comp
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0))
      map_add' := fun v0 v0' => by
        rw [sharpRaisedKoszulVec_add_snd, map_add, map_add, map_add,
          ContinuousLinearMap.add_comp,
          show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v0 + v0') =
            PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 +
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0' from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).map_add v0 v0',
          ContinuousLinearMap.add_apply, map_add, ContinuousLinearMap.comp_add]
        abel
      map_smul' := fun c v0 => by
        rw [RingHom.id_apply, sharpRaisedKoszulVec_smul_snd, map_smul, map_smul, map_smul,
          ContinuousLinearMap.smul_comp,
          show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (c • v0) =
            c • PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).map_smul c v0,
          ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.comp_smul]
        rw [smul_sub, smul_add, smul_add] }

set_option linter.unusedSectionVars false in
@[simp] lemma sharpGradKoszulKernelBilin_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q v0 v1 : TangentSpace I x) :
    sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x p q v0 v1 =
      (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p
          (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q v0)) v1
        + g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q v0)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v1))
      - (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0
          (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q p)) v1
        + g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q p)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 v1)) := by
  rw [sharpGradKoszulKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]

/-- The sharp-gradient Koszul kernel repackaged as a bilinear form in the frame pair, for
the orthonormal-frame trace-independence patching. -/
def frameSharpGradKoszulKernel (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p =>
        haveI : FiniteDimensional ℝ (TangentSpace I x) :=
          inferInstanceAs (FiniteDimensional ℝ E)
        LinearMap.toContinuousLinearMap
          { toFun := fun q => sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x p q v0 v1
            map_add' := fun q q' => by
              rw [sharpGradKoszulKernelBilin_apply, sharpGradKoszulKernelBilin_apply,
                sharpGradKoszulKernelBilin_apply, sharpRaisedKoszulVec_add_fst,
                sharpRaisedKoszulVec_add_fst]
              simp only [map_add, ContinuousLinearMap.add_apply]
              ring
            map_smul' := fun c q => by
              rw [RingHom.id_apply, sharpGradKoszulKernelBilin_apply,
                sharpGradKoszulKernelBilin_apply, sharpRaisedKoszulVec_smul_fst,
                sharpRaisedKoszulVec_smul_fst]
              simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
              ring }
      map_add' := fun p p' => by
        apply ContinuousLinearMap.ext
        intro q
        rw [ContinuousLinearMap.add_apply, LinearMap.coe_toContinuousLinearMap',
          LinearMap.coe_toContinuousLinearMap', LinearMap.coe_toContinuousLinearMap']
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [sharpGradKoszulKernelBilin_apply, sharpGradKoszulKernelBilin_apply,
          sharpGradKoszulKernelBilin_apply, sharpRaisedKoszulVec_add_snd,
          show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (p + p') =
            PDE.DeTurck.connDiff (I := I) g₁ g₀ x p +
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x p' from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).map_add p p']
        simp only [map_add, ContinuousLinearMap.add_apply]
        ring
      map_smul' := fun c p => by
        rw [RingHom.id_apply]
        apply ContinuousLinearMap.ext
        intro q
        rw [ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap',
          LinearMap.coe_toContinuousLinearMap']
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [sharpGradKoszulKernelBilin_apply, sharpGradKoszulKernelBilin_apply,
          sharpRaisedKoszulVec_smul_snd,
          show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (c • p) =
            c • PDE.DeTurck.connDiff (I := I) g₁ g₀ x p from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).map_smul c p]
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring }

set_option linter.unusedSectionVars false in
@[simp] lemma frameSharpGradKoszulKernel_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v0 v1 p q : TangentSpace I x) :
    frameSharpGradKoszulKernel (I := I) g₀ g₁ S x v0 v1 p q =
      sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x p q v0 v1 := by
  rw [frameSharpGradKoszulKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

/-- Summand of the sharp-gradient Koszul residual arm at a frame pair: the input datum
evaluated at the frame pair weights the kernel bilinear form. -/
def sharpGradKoszulSummandFib (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

set_option linter.unusedSectionVars false in
@[simp] lemma sharpGradKoszulSummandFib_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q : TangentSpace I x)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (sharpGradKoszulSummandFib (I := I) g₀ g₁ S x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x p q (v 0) (v 1) := by
  rw [sharpGradKoszulSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply, smul_eq_mul]
  rfl

/-- The sharp-gradient Koszul residual bi-contraction at a fixed frame family, with the
donor's factor `2`. -/
def sharpGradKoszulBiContrFibFixedFrame (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    sharpGradKoszulSummandFib (I := I) g₀ g₁ S x (B a x) (B b x)

set_option linter.unusedSectionVars false in
lemma sharpGradKoszulBiContrFibFixedFrame_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        (sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S B x D) v =
      (2 : ℝ) * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)]) *
          sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x (B a x) (B b x) (v 0) (v 1) := by
  classical
  rw [sharpGradKoszulBiContrFibFixedFrame, ContinuousLinearMap.smul_apply,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, sharpGradKoszulSummandFib_toModel]

private lemma unitValueCovGrad3_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SSpace 3 I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
          (covGrad (I := I) (M := M) g₀ 0 2 S).toSection y)
          (unitZeroSec (I := I) (M := M) y))) := by
  exact ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel 3 ℝ E)
    (E₁ := fun z : M => Tensor0SSpace 0 I z)
    (E₂ := fun z : M => Tensor0SSpace 3 I z)
    (IM := I) (IB := I) (b := id)
    (ϕ := fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
        (covGrad (I := I) (M := M) g₀ 0 2 S).toSection y))
    (v := fun y : M => unitZeroSec (I := I) (M := M) y)
    (covGrad (I := I) (M := M) g₀ 0 2 S).toSection.contMDiff
    (unitZeroSec (I := I) (M := M)).contMDiff

private lemma linearizedKoszulCovec_basis_contMDiffOn_generic
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        linearizedKoszulCovec (I := I) g₀ S b (Z b) (Y b)
          (chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  classical
  set W₃ : ∀ b : M, Tensor0SSpace 3 I b := fun b =>
    (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 3 I b from
      (covGrad (I := I) (M := M) g₀ 0 2 S).toSection b)
      (unitZeroSec (I := I) (M := M) b) with hW₃def
  have hW₃ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SSpace 3 I z) y (W₃ y)) :=
    unitValueCovGrad3_contMDiff (I := I) (M := M) g₀ S
  intro b hb
  have hb_open : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hb
  have hbasisAt : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y => chartBasisVecFiber (I := I) α j y)) b := by
    have h := chartBasisVec_contMDiffOn (I := I) α j
    have hopen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
      (trivializationAt E (TangentSpace I) α).open_baseSet
    exact (h b hb_base).contMDiffAt (hopen.mem_nhds hb_base)
  have hEval : ∀ (v : Fin 3 → ∀ y : M, TangentSpace I y)
      (_ : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (T% (v i)) b),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y : M => Tensor0SSpace.toModel (W₃ y) (fun i : Fin 3 => v i y)) b :=
    fun v hv => TensorMultilinear.contMDiffAt_section_apply (n := 3) W₃
      (hW₃.contMDiffAt) v hv
  have h1 := hEval ![fun y => Y y, fun y => Z y, fun y => chartBasisVecFiber (I := I) α j y]
    (by
      intro i
      fin_cases i
      · exact Y.contMDiff.contMDiffAt
      · exact Z.contMDiff.contMDiffAt
      · exact hbasisAt)
  have h2 := hEval ![fun y => Z y, fun y => Y y, fun y => chartBasisVecFiber (I := I) α j y]
    (by
      intro i
      fin_cases i
      · exact Z.contMDiff.contMDiffAt
      · exact Y.contMDiff.contMDiffAt
      · exact hbasisAt)
  have h3 := hEval ![fun y => chartBasisVecFiber (I := I) α j y, fun y => Y y, fun y => Z y]
    (by
      intro i
      fin_cases i
      · exact hbasisAt
      · exact Y.contMDiff.contMDiffAt
      · exact Z.contMDiff.contMDiffAt)
  have hcomb : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => (1 / 2 : ℝ) *
        (Tensor0SSpace.toModel (W₃ y)
            (fun i : Fin 3 => (![fun y' => Y y', fun y' => Z y',
              fun y' => chartBasisVecFiber (I := I) α j y'] : Fin 3 → ∀ y' : M,
                TangentSpace I y') i y)
          + Tensor0SSpace.toModel (W₃ y)
              (fun i : Fin 3 => (![fun y' => Z y', fun y' => Y y',
                fun y' => chartBasisVecFiber (I := I) α j y'] : Fin 3 → ∀ y' : M,
                  TangentSpace I y') i y)
          - Tensor0SSpace.toModel (W₃ y)
              (fun i : Fin 3 => (![fun y' => chartBasisVecFiber (I := I) α j y',
                fun y' => Y y', fun y' => Z y'] : Fin 3 → ∀ y' : M,
                  TangentSpace I y') i y))) b :=
    ContMDiffAt.mul contMDiffAt_const ((h1.add h2).sub h3)
  refine (hcomb.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards with y
  rw [linearizedKoszulCovec_apply]
  have hUM : ∀ v : Fin 3 → TangentSpace I y,
      unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) y v =
        Tensor0SSpace.toModel (W₃ y) v := fun _ => rfl
  rw [hUM, hUM, hUM]
  congr 1
  congr 1
  · congr 1
    · congr 1
      funext i
      fin_cases i <;> rfl
    · congr 1
      funext i
      fin_cases i <;> rfl
  · congr 1
    funext i
    fin_cases i <;> rfl

set_option linter.unusedSectionVars false in
/-- Smoothness of the mixed-metric sharp-raised Koszul vector along smooth section
arguments. -/
lemma sharpRaisedKoszulVec_section_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (U Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S b (U b) (Z b))) := by
  apply metricSharp_contMDiff_total (I := I) g₁
    (cv := fun b : M => linearizedKoszulCovec (I := I) g₀ S b (U b) (Z b))
  intro α j
  exact linearizedKoszulCovec_basis_contMDiffOn_generic (I := I) (M := M) g₀ S Z U α j

theorem sharpGradKoszulKernelBilin_homSection_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x
        (sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x (p x) (q x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x (p x) (q x) (V0 x))
  intro W
  have hΨqV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (V0 b))) := by
    have h := sharpRaisedKoszulVec_section_contMDiff (I := I) (M := M) g₀ g₁ S
      ⟨fun b => q b, hq⟩ ⟨fun b => V0 b, V0.contMDiff⟩
    exact h
  have hΨqp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (p b))) := by
    have h := sharpRaisedKoszulVec_section_contMDiff (I := I) (M := M) g₀ g₁ S
      ⟨fun b => q b, hq⟩ ⟨fun b => p b, hp⟩
    exact h
  have hApΨ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (p b)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (V0 b)))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hp hΨqV
  have hApW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (p b) (W b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hp W.contMDiff
  have hAVΨ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (V0 b)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (p b)))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ V0.contMDiff hΨqp
  have hAVW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (V0 b) (W b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ V0.contMDiff W.contMDiff
  have hs1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (p x)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (V0 x))) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (p b)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (V0 b)), hApΨ⟩
      ⟨fun b => W b, W.contMDiff⟩
  have hs2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (V0 x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (p x) (W x))) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (V0 b), hΨqV⟩
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (p b) (W b), hApW⟩
  have hs3 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (V0 x)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (p x))) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (V0 b)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (p b)), hAVΨ⟩
      ⟨fun b => W b, W.contMDiff⟩
  have hs4 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (p x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (V0 x) (W x))) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (p b), hΨqp⟩
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (V0 b) (W b), hAVW⟩
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (p x)
          (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (V0 x))) (W x)
        + g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (V0 x))
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (p x) (W x)))
        - (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (V0 x)
            (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (p x))) (W x)
          + g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (p x))
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (V0 x) (W x)))) :=
    (hs1.add hs2).sub (hs3.add hs4)
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change sharpGradKoszulKernelBilin (I := I) g₀ g₁ S y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [sharpGradKoszulKernelBilin_apply]
  rfl

theorem sharpGradKoszulBiContrFibFixedFrame_apply_section_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (sharpGradKoszulSummandFib (I := I) g₀ g₁ S x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b' => Y b') Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x (B a x) (B b x))
      (sharpGradKoszulKernelBilin_homSection_contMDiff (I := I) g₀ g₁ S (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x : M =>
        Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set T2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => sharpGradKoszulSummandFib (I := I) g₀ g₁ S x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hT2_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b with hStot_def
  have hfinal := ContMDiff.smul_section (f := fun _ : M => (2 : ℝ))
    contMDiff_const Stot.contMDiff
  refine hfinal.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  have hcoe1 : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), T2 a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
            Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), T2 a b) Finset.univ
  have hcoe2 : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), T2 a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((T2 a b : Π z : M, Tensor0SSpace 2 I z)) :=
    fun a => map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => T2 a b) Finset.univ
  have hval : Stot x = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      sharpGradKoszulSummandFib (I := I) g₀ g₁ S x (B a x) (B b x) (Y x) := by
    have h1 : Stot x = ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        T2 a b : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) x := rfl
    rw [h1, hcoe1, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoe2 a, Finset.sum_apply]
    rfl
  have hgoal : sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S B x (Y x) =
      (2 : ℝ) • Stot x := by
    rw [hval, sharpGradKoszulBiContrFibFixedFrame, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact ContinuousLinearMap.sum_apply _ _ _
  rw [hgoal]
  rfl

theorem sharpGradKoszulBiContrFibFixedFrame_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S B x)
  intro Y
  exact sharpGradKoszulBiContrFibFixedFrame_apply_section_contMDiff
    (I := I) g₀ g₁ S B hB Y

/-- The sharp-gradient Koszul residual bi-contraction at the moving orthonormal frames. -/
def sharpGradKoszulBiContrFib (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S (smoothOrthoFrame (I := I) g₁ x) x

theorem sharpGradKoszulBiContrFib_eq_fixedFrame_on_nbhd
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    sharpGradKoszulBiContrFib (I := I) g₀ g₁ S y =
      sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S
        (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [sharpGradKoszulBiContrFib, sharpGradKoszulBiContrFibFixedFrame_toModel,
    sharpGradKoszulBiContrFibFixedFrame_toModel]
  congr 1
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)]) *
          sharpGradKoszulKernelBilin (I := I) g₀ g₁ S y (Bf a) (Bf b) (v 0) (v 1) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameSharpGradKoszulKernel (I := I) g₀ g₁ S y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameSharpGradKoszulKernel_apply,
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rw [mul_comm]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameSharpGradKoszulKernel (I := I) g₀ g₁ S y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

theorem sharpGradKoszulBiContrFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (sharpGradKoszulBiContrFib (I := I) g₀ g₁ S x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    sharpGradKoszulBiContrFibFixedFrame_contMDiff (I := I) g₀ g₁ S
      (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (sharpGradKoszulBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₀ g₁ S x₀ hy))

/-- The `(∇♯)K`-residual coefficient field (fold map gap item 4, shared by the RA-1 subtree
and the M-child's C-EQ): the frame bi-contraction of the fold-pair antisymmetrized
`(∇⁰♯_{g₁})K_S` content, generic in the perturbed metric `g₁` and the weight `S`. One-jet
in `S`; metric raisings at the zero jet. -/
def ricciArmSharpGradKoszulResidualField (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (sharpGradKoszulBiContrFib (I := I) g₀ g₁ S x))
      contMDiff_toFun := sharpGradKoszulBiContrFib_contMDiff (I := I) g₀ g₁ S }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem ricciArmSharpGradKoszulResidualField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M) :
    (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁ S).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (sharpGradKoszulBiContrFib (I := I) g₀ g₁ S x)) := rfl

set_option linter.unusedSectionVars false in
/-- Vacuity litmus (zero-weight kill): the `(∇♯)K`-residual field rejects the zero weight. -/
theorem ricciArmSharpGradKoszulResidualField_zero_weight
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
      (0 : SmoothCcTensor g₀ 0 2) = 0 := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [ricciArmSharpGradKoszulResidualField_toSection]
  have hzero : sharpGradKoszulBiContrFib (I := I) g₀ g₁ (0 : SmoothCcTensor g₀ 0 2) x = 0 := by
    apply ContinuousLinearMap.ext
    intro D
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [sharpGradKoszulBiContrFib, sharpGradKoszulBiContrFibFixedFrame_toModel]
    have hker : ∀ p q : TangentSpace I x,
        sharpGradKoszulKernelBilin (I := I) g₀ g₁ (0 : SmoothCcTensor g₀ 0 2) x p q
          (v 0) (v 1) = 0 := by
      intro p q
      rw [sharpGradKoszulKernelBilin_apply, sharpRaisedKoszulVec_zero_weight,
        sharpRaisedKoszulVec_zero_weight]
      simp only [map_zero, ContinuousLinearMap.zero_apply]
      ring
    rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E), (smoothOrthoFrame (I := I) g₁ x b x : E)]) *
          sharpGradKoszulKernelBilin (I := I) g₀ g₁ (0 : SmoothCcTensor g₀ 0 2) x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1)) = 0 from
      Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => by
        rw [hker]
        ring))]
    rw [mul_zero]
    simp only [ContinuousLinearMap.zero_apply, Tensor0SSpace.toModel_zero,
      ContinuousMultilinearMap.zero_apply]
  rw [hzero]
  rfl

/-! ### Stage C — the Ricci-fold remainder field (shared, per fold map E6) -/

set_option linter.unusedSectionVars false in
lemma ccTensorBilin_zero_weight (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v w = 0 := by
  rw [ccTensorBilin_apply, ccTensorModel]
  rw [show (ccTensorMultilinear (I := I) g (0 : SmoothCcTensor g 0 2) x :
      Tensor0SSpace 2 I x) =
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      (0 : SmoothCcTensor g 0 2).toSection x)
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      (0 : SmoothCcTensor g 0 2).toSection x) = 0 from rfl]
  rw [ContinuousLinearMap.zero_apply, Tensor0SSpace.toModel_zero]
  rfl

/-- The bilinear kernel of the Ricci-fold remainder arm at a fixed frame pair `(p, q)`: the
background-curvature commutator action on the weight `S`, from the Ricci-identity fold of
the antisymmetrized second-gradient pair (the `½` is the fold-pair coefficient). Zero-jet
in `S` against the background curvature. -/
def ricciFoldKernelBilin (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 =>
        (-(1 / 2) : ℝ) •
          (ccTensorBilin (I := I) g₀ S x
              (riemannOp (LeviCivita (I := I) g₀) x v0 p q)
            + (ccTensorBilin (I := I) g₀ S x q).comp
                (riemannOp (LeviCivita (I := I) g₀) x v0 p))
      map_add' := fun v0 v0' => by
        rw [show riemannOp (LeviCivita (I := I) g₀) x (v0 + v0') =
            riemannOp (LeviCivita (I := I) g₀) x v0 +
              riemannOp (LeviCivita (I := I) g₀) x v0' from
          (riemannOp (LeviCivita (I := I) g₀) x).map_add v0 v0']
        simp only [ContinuousLinearMap.add_apply, map_add, ContinuousLinearMap.comp_add,
          smul_add]
        abel
      map_smul' := fun c v0 => by
        rw [RingHom.id_apply,
          show riemannOp (LeviCivita (I := I) g₀) x (c • v0) =
            c • riemannOp (LeviCivita (I := I) g₀) x v0 from
          (riemannOp (LeviCivita (I := I) g₀) x).map_smul c v0]
        simp only [ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.comp_smul]
        rw [← smul_add, smul_comm] }

set_option linter.unusedSectionVars false in
@[simp] lemma ricciFoldKernelBilin_apply (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q v0 v1 : TangentSpace I x) :
    ricciFoldKernelBilin (I := I) g₀ S x p q v0 v1 =
      (-(1 / 2) : ℝ) *
        (ccTensorBilin (I := I) g₀ S x
            (riemannOp (LeviCivita (I := I) g₀) x v0 p q) v1
          + ccTensorBilin (I := I) g₀ S x q
              (riemannOp (LeviCivita (I := I) g₀) x v0 p v1)) := by
  rw [ricciFoldKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]

/-- The Ricci-fold kernel repackaged as a bilinear form in the frame pair. -/
def frameRicciFoldKernel (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (-(1 / 2) : ℝ) •
    ((ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x) ℝ
        ((ccTensorBilin (I := I) g₀ S x).flip v1)).comp
        (riemannOp (LeviCivita (I := I) g₀) x v0)
      + (ccTensorBilin (I := I) g₀ S x).flip.comp
          ((riemannOp (LeviCivita (I := I) g₀) x v0).flip v1))

set_option linter.unusedSectionVars false in
@[simp] lemma frameRicciFoldKernel_apply (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v0 v1 p q : TangentSpace I x) :
    frameRicciFoldKernel (I := I) g₀ S x v0 v1 p q =
      ricciFoldKernelBilin (I := I) g₀ S x p q v0 v1 := by
  rw [ricciFoldKernelBilin_apply, frameRicciFoldKernel]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul]

/-- Summand of the Ricci-fold remainder arm at a frame pair. -/
def ricciFoldSummandFib (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (ricciFoldKernelBilin (I := I) g₀ S x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

set_option linter.unusedSectionVars false in
@[simp] lemma ricciFoldSummandFib_toModel (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q : TangentSpace I x)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (ricciFoldSummandFib (I := I) g₀ S x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        ricciFoldKernelBilin (I := I) g₀ S x p q (v 0) (v 1) := by
  rw [ricciFoldSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply, smul_eq_mul]
  rfl

/-- The Ricci-fold remainder bi-contraction at a fixed frame family. -/
def ricciFoldBiContrFibFixedFrame (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    ricciFoldSummandFib (I := I) g₀ S x (B a x) (B b x)

set_option linter.unusedSectionVars false in
lemma ricciFoldBiContrFibFixedFrame_toModel (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (ricciFoldBiContrFibFixedFrame (I := I) g₀ S B x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)]) *
          ricciFoldKernelBilin (I := I) g₀ S x (B a x) (B b x) (v 0) (v 1) := by
  classical
  rw [ricciFoldBiContrFibFixedFrame, ContinuousLinearMap.sum_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, ricciFoldSummandFib_toModel]

theorem ricciFoldKernelBilin_homSection_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x
        (ricciFoldKernelBilin (I := I) g₀ S x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => ricciFoldKernelBilin (I := I) g₀ S x (p x) (q x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => ricciFoldKernelBilin (I := I) g₀ S x (p x) (q x) (V0 x))
  intro W
  have hs1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ccTensorBilin (I := I) g₀ S x
        (riemannSec (LeviCivita (I := I) g₀) V0 p q x) (W x)) :=
    ccTensorBilin_scalar_contMDiff (I := I) g₀ S
      ⟨fun b => riemannSec (LeviCivita (I := I) g₀) V0 p q b,
        riemannSec_contMDiff (cov := LeviCivita (I := I) g₀) V0.contMDiff hp hq⟩
      ⟨fun b => W b, W.contMDiff⟩
  have hs2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ccTensorBilin (I := I) g₀ S x (q x)
        (riemannSec (LeviCivita (I := I) g₀) V0 p W x)) :=
    ccTensorBilin_scalar_contMDiff (I := I) g₀ S
      ⟨fun b => q b, hq⟩
      ⟨fun b => riemannSec (LeviCivita (I := I) g₀) V0 p W b,
        riemannSec_contMDiff (cov := LeviCivita (I := I) g₀) V0.contMDiff hp W.contMDiff⟩
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => (-(1 / 2) : ℝ) *
        (ccTensorBilin (I := I) g₀ S x
            (riemannSec (LeviCivita (I := I) g₀) V0 p q x) (W x)
          + ccTensorBilin (I := I) g₀ S x (q x)
              (riemannSec (LeviCivita (I := I) g₀) V0 p W x))) :=
    contMDiff_const.mul (hs1.add hs2)
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change ricciFoldKernelBilin (I := I) g₀ S y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [ricciFoldKernelBilin_apply,
    riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀) V0.contMDiff hp hq,
    riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀) V0.contMDiff hp W.contMDiff]
  rfl

theorem ricciFoldBiContrFibFixedFrame_apply_section_contMDiff
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (ricciFoldBiContrFibFixedFrame (I := I) g₀ S B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (ricciFoldSummandFib (I := I) g₀ S x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b' => Y b') Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => ricciFoldKernelBilin (I := I) g₀ S x (B a x) (B b x))
      (ricciFoldKernelBilin_homSection_contMDiff (I := I) g₀ S (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x : M =>
        Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set T2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => ricciFoldSummandFib (I := I) g₀ S x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hT2_def
  have hcoe1 : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), T2 a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
            Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), T2 a b) Finset.univ
  have hcoe2 : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), T2 a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((T2 a b : Π z : M, Tensor0SSpace 2 I z)) :=
    fun a => map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => T2 a b) Finset.univ
  have hStot := (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    T2 a b).contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  have hval : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ricciFoldSummandFib (I := I) g₀ S x (B a x) (B b x) (Y x) := by
    have h1 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) x =
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          T2 a b : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
            Π z : M, Tensor0SSpace 2 I z) x := rfl
    rw [h1, hcoe1, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoe2 a, Finset.sum_apply]
    rfl
  rw [ricciFoldBiContrFibFixedFrame, ContinuousLinearMap.sum_apply]
  rw [show ∑ a : Fin (Module.finrank ℝ E), (∑ b : Fin (Module.finrank ℝ E),
      ricciFoldSummandFib (I := I) g₀ S x (B a x) (B b x)) (Y x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ricciFoldSummandFib (I := I) g₀ S x (B a x) (B b x) (Y x) from
    Finset.sum_congr rfl (fun a _ => ContinuousLinearMap.sum_apply _ _ _)]
  rw [← hval]

theorem ricciFoldBiContrFibFixedFrame_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (ricciFoldBiContrFibFixedFrame (I := I) g₀ S B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => ricciFoldBiContrFibFixedFrame (I := I) g₀ S B x)
  intro Y
  exact ricciFoldBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₀ S B hB Y

/-- The Ricci-fold remainder bi-contraction at the moving orthonormal frames. -/
def ricciFoldBiContrFib (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) : Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ricciFoldBiContrFibFixedFrame (I := I) g₀ S (smoothOrthoFrame (I := I) g₁ x) x

theorem ricciFoldBiContrFib_eq_fixedFrame_on_nbhd (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    ricciFoldBiContrFib (I := I) g₀ g₁ S y =
      ricciFoldBiContrFibFixedFrame (I := I) g₀ S (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ricciFoldBiContrFib, ricciFoldBiContrFibFixedFrame_toModel,
    ricciFoldBiContrFibFixedFrame_toModel]
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)]) *
          ricciFoldKernelBilin (I := I) g₀ S y (Bf a) (Bf b) (v 0) (v 1) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameRicciFoldKernel (I := I) g₀ S y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameRicciFoldKernel_apply,
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rw [mul_comm]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameRicciFoldKernel (I := I) g₀ S y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

theorem ricciFoldBiContrFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (ricciFoldBiContrFib (I := I) g₀ g₁ S x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (ricciFoldBiContrFibFixedFrame (I := I) g₀ S
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    ricciFoldBiContrFibFixedFrame_contMDiff (I := I) g₀ S
      (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (ricciFoldBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₀ g₁ S x₀ hy))

/-- The Ricci-fold remainder coefficient field (fold map gap item 5, shared by the RA-1
subtree and the M-child's C-EQ): the frame bi-contraction of the background-curvature
commutator action on the weight `S`, at the moving orthonormal frames. Zero-jet in `S`. -/
def ricciArmRicciFoldRemainderField (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (ricciFoldBiContrFib (I := I) g₀ g₁ S x))
      contMDiff_toFun := ricciFoldBiContrFib_contMDiff (I := I) g₀ g₁ S }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem ricciArmRicciFoldRemainderField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M) :
    (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ S).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (ricciFoldBiContrFib (I := I) g₀ g₁ S x)) := rfl

set_option linter.unusedSectionVars false in
/-- Vacuity litmus (zero-weight kill): the Ricci-fold remainder field rejects the zero
weight. -/
theorem ricciArmRicciFoldRemainderField_zero_weight (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
      (0 : SmoothCcTensor g₀ 0 2) = 0 := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [ricciArmRicciFoldRemainderField_toSection]
  have hzero : ricciFoldBiContrFib (I := I) g₀ g₁ (0 : SmoothCcTensor g₀ 0 2) x = 0 := by
    apply ContinuousLinearMap.ext
    intro D
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [ricciFoldBiContrFib, ricciFoldBiContrFibFixedFrame_toModel]
    rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E), (smoothOrthoFrame (I := I) g₁ x b x : E)]) *
          ricciFoldKernelBilin (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1)) = 0 from
      Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => by
        rw [ricciFoldKernelBilin_apply, ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
        ring))]
    simp only [ContinuousLinearMap.zero_apply, Tensor0SSpace.toModel_zero,
      ContinuousMultilinearMap.zero_apply]
  rw [hzero]
  rfl

/-! ### Stage D — DEF-2 and its vacuity litmus; tower statement elaboration checks -/

/-- DEF-2′ (Form B): the background-curvature-difference and refold-remainder coefficient
field at a generic perturbed metric `g₁` — the bg-R commutator difference PRECOMPOSED with
the input-slot swap (the `Wᵀ` transposition of the corrected fold identity, absorbed as
`appCcRS` against `ccSlotSwapField` so the bracket stays one applied `(2,2)` coefficient
and the `ccInputSymm` sector algebra sees the swap through its own simp set), plus HALF
the shared `(∇♯)K`-residual and MINUS the Ricci-fold remainder, the latter two at the
metric-difference weight. -/
def bgRDiffRefoldRemainderField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  appCcRS (I := I) (M := M) g₀ 2 2 2
      (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
        - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀)
      (ccSlotSwapField (I := I) (M := M) g₀)
    + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
        (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)
    - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
        (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)

set_option linter.unusedSectionVars false in
/-- Vacuity litmus for DEF-2′: the field rejects the diagonal witness `g₁ = g₀` — the
slot-swapped bg-R difference cancels and both shared remainder fields die on the zero
weight. -/
theorem bgRDiffRefoldRemainderField_self (g₀ : SmoothRiemannianMetric I M) :
    bgRDiffRefoldRemainderField (I := I) (M := M) g₀ g₀ = 0 := by
  rw [bgRDiffRefoldRemainderField, metricDifferenceCcTensor_self, sub_self,
    appCcRS_zero_left, ricciArmSharpGradKoszulResidualField_zero_weight,
    ricciArmRicciFoldRemainderField_zero_weight, smul_zero, add_zero, sub_zero]

set_option linter.unusedVariables false in
/-- The shared field-level C₂-EXPOSED generic-`g₁` Palatini fold of the moving order-zero
Riemann coefficient, in the CORRECTED Form B
`L = Q_true + ΔbgRComm[Wᵀ] − RF + ½·SGK + kernel`
(the single source of fold truth for the Riemann-arm refold identity RA-1' and the
M-dossier sym-sector cancellation C-EQ): for a generic perturbed metric `g₁ = g₀ + P` (the
`htie` idiom) with symmetric perturbation `P` (chain-suppliable at every wired consumer:
the realized path supplies `s • T` under `hTsymm`; the metric difference is symmetric by
metric symmetry), the half background difference of the moving Riemann-arm coefficient
applied to an arbitrary rank-`(0, 2)` argument `W` (ALL `W` — no symmetry hypothesis on
`W`) splits onto the pinned residual coefficient fields: the antisymmetrized `A ⋆ A`
commutator field (`ricciArmOrder0AACommCoeffField`, the corrected quadratic residual),
the background-curvature commutator difference PRECOMPOSED with the input-slot swap
(`appCcRS … (ccSlotSwapField g₀)` — the `Wᵀ` transposition forced by the second-Bianchi
completion, which lands the curvature vector in the kernel's SECOND slot while the bg-R
kernel feeds the FIRST), plus HALF the shared `(∇♯)K`-residual and MINUS the Ricci-fold
remainder at weight `P` (the bracket is definitionally `bgRDiffRefoldRemainderField` at
`P := metricDifferenceCcTensor`) — plus the folded four-monomial second-Bianchi refold
kernel at the DERIVED quadruple
`σ₁ = swap 0 2, σ₂ = swap 1 3, σ₃ = swap 0 2 * swap 1 3, σ₄ = 1`, in the
DERIVATION-FAITHFUL placement: the kernel WEIGHT is the applied argument `W` and the
second gradient falls on the metric-difference tensor `P` (coefficient exactly `1`:
donor `2` × Koszul `½` × kernel-internal `½`).
Recorded corrections riding the corrected mechanism: the defect-(3) conversion of the
eventual marathon fill targets the fold `R⁰`-block `T1R0`, NOT the donor `T1`; the refold
identity is calibrated live in curved `g₀` (the covariant-vanishing calibration, not a
flat-model reading); the connection-difference slot convention throughout is
`connDiff_apply`'s `(ARGUMENT)(DIRECTION)` application order.
Every consumer transitively depends on `sorryAx` until this lands. -/
theorem ricciArmOrder0RiemannHalfBackgroundDifference_appCc_eq_residualFieldSum_add_refoldKernelSecondGradient
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ P x v w = ccTensorBilin (I := I) g₀ P x w v)
    (W : SmoothCcTensor g₀ 0 2) :
    (1 / 2 : ℝ) •
        (appCc (I := I) (M := M) g₀ 2 2
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁) W
          - appCc (I := I) (M := M) g₀ 2 2
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) W) =
      appCc (I := I) (M := M) g₀ 2 2
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
            + (appCcRS (I := I) (M := M) g₀ 2 2 2
                  (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₁
                    - ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g₀)
                  (ccSlotSwapField (I := I) (M := M) g₀)
                + (1 / 2 : ℝ) •
                    ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁ P
                - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ P)) W
        + appCc (I := I) (M := M) g₀ 4 2
            (curvatureRefoldKernelCoeffField (I := I) (M := M) g₀ g₁
              (ccTensorUnitValueSection (I := I) (M := M) g₀ W)
              (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ W)
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)
            (iteratedCovGrad (I := I) g₀ 0 2 2 P) :=
  sorry

/-! ### Stage E — the sym-sector cancellation equation (M-dossier C-EQ, kernel-field form) -/

set_option linter.unusedSectionVars false in
/-- M-dossier child C-EQ (CAND-A, in the leader-ruled KERNEL-FIELD form, restated on the
CONFIRMED Form B): the generic-`g₁` field-level Palatini split of the
input-slot-symmetrized moving arm-0 combination onto the two pinned residual coefficient
fields. The linear `∇²`-content of the order-zero arm and of the half Riemann-arm
difference annihilate on the `ccInputSymm` sector (the certified mechanism-A cancellation
`Order0∇ = -(1/2) • RmArm∇`, symmetric-sector-ONLY — the antisymmetric free-Koszul witness
`E₀₁ − E₁₀ ↦ 7949 ≠ 0` kills every full-field predecessor), so only the antisymmetrized
`A ⋆ A` commutator field (`ricciArmOrder0AACommCoeffField`, the Form B `Q_true`) and the
corrected background-curvature-difference and refold remainder (DEF-2′, carrying the
input-slot-swapped bg-R difference, half the `(∇♯)K`-residual and minus the Ricci-fold
remainder) survive on the right.

KERNEL-FIELD FORM (fold derivation map E2/E4, leader-ruled; weight placement TRUTH-FIXED
per the Form B derivation): the `C₂` term of this equation's fold derivation is
`curvatureRefoldKernelCoeffField` at the DERIVED second-Bianchi quadruple
`σ₁ = Equiv.swap 0 2, σ₂ = Equiv.swap 1 3, σ₃ = Equiv.swap 0 2 * Equiv.swap 1 3, σ₄ = 1`
(partner quadruple `qB = Equiv.swap 0 1 * qA ·`, `IsFramePairPartner`-paired,
`not_isFramePairPartner_self` rejecting the diagonal), at coefficient EXACTLY `1`
(donor `2` × Koszul `½` × kernel-internal `½` closes), with the kernel WEIGHT the unit
value of the APPLIED ARGUMENT `W` (`ccTensorUnitValueSection` of the datum the coefficient
is applied to) and the SECOND GRADIENT falling on the metric-difference tensor `P` — the
derivation-faithful placement of the shared fold primitive
`ricciArmOrder0RiemannHalfBackgroundDifference_appCc_eq_residualFieldSum_add_refoldKernelSecondGradient` —
NOT the `½`-partner-averaged `riemannPalatiniRefoldC2Family` wrapper and NOT a
metric-difference-weighted kernel. Hence the RA-1 defect D1 (the family carries HALF the
fold) is NOT inherited — no `½`-family average appears in the derivation — and D2 (the
mixed `α`-sector escape) is VOID: the metric-difference tensor is symmetric by
construction, so no antisymmetric weight sector exists at field level.

COMPOSITION WALK (dossier §vi assembly map, on Form B): under this equation the frozen
M-child capped-grid target assembles as
`ccInputSymm (comb) = ccInputSymm (ricciArmOrder0AACommCoeffField) + ccInputSymm (bgRDiffRefoldRemainderField)` [C-EQ]
`⟹ rfns (icg^i (LHS)) ≤ 2·rfns (icg^i ccInputSymm Q_true) + 2·rfns (icg^i ccInputSymm BGR)`
[`iteratedCovGrad_add` + `riemannianFiberNormSq_add_le`]
`⟹ ≤ (2·C_QTRUE i + 2·C_BGR i) · boundedFactorGridWindow (P-jets) (i+1) (i+3)`
[the C-BGR capped grid-window tower of `RicciArmResidualFieldGridWindow`, re-derived on
DEF-2′, plus the pending `Q_true` `ccInputSymm` tower twin — the C-QUAD program re-run on
`ricciArmOrder0AACommCoeffField` through the same proven engines] — the
`ccInputSymm_add`/`riemannianFiberNormSq_add_le` glue of the committed successor peel.

VACUITY: both right-hand fields are PINNED constructions with proven diagonal litmuses
(`ricciArmOrder0AACommCoeffField_self`, `bgRDiffRefoldRemainderField_self`), and the
kernel pin sits at the pinned derived quadruple — this is a field EQUATION over named
constructed objects, not an `∃`-residual child (the lane-T vacuity class is excluded by
construction).

DEFERRED INPUT (`sorry`): the marathon leaf — the `riemannSec_difference` Palatini fold at
field level on Form B (the R8 symbolic derivation is the fill road map: the on-disk
`order0CLM` / `ricciCometricFourTraceCLM` evaluation shapes plus the two hand-bridge
upgrades, the Koszul-derivative `DA ↔ K` identity at a general connection difference and
the moving-frame raise, with the second-Bianchi completion forcing the `Wᵀ` transposition),
per the fold derivation map. Every consumer transitively depends on `sorryAx` until it
lands. -/
theorem linearizedRicciConnDiffOrder0RiemannHalfBackgroundDifferenceCombinationInputSymm_eq_residualFieldSum
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ccInputSymm (I := I) (M := M) g₀
        (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) • (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
              - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)) =
      ccInputSymm (I := I) (M := M) g₀
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
        + ccInputSymm (I := I) (M := M) g₀
            (bgRDiffRefoldRemainderField (I := I) (M := M) g₀ g₁) := sorry

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
