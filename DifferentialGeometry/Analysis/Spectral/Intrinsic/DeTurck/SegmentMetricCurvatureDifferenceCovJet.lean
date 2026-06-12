import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricCurvatureDifferenceOpDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Geometry.Connection.TensorNabla.LiftedSectionCovariantRealizeBridge
import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceQuadraticTraceProduct
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParallelRankReducingContractionGrid
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
import DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Tensor.RSTensor.BundleTrivialization.Tensor0SBundleLocalityIdentities
import DifferentialGeometry.Tensor.Multilinear.Comp
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomTensorRSRiemannian
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Slot0SliceFiberNormDomination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LoweredConnectionDifferenceCovariantDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CrossCorrectionParallelContraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricCurvatureDifferenceCrossTraceProduct
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotExtendCovariantParallelism

/-! # The curvature-trace covariant-jet reduction of the sealed Ricci–DeTurck curvature difference

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the **curvature-trace covariant-jet reduction** beneath the
curvature difference-arm Core-II covariant-jet leaf of the Ricci–DeTurck right-hand-side expansion
(`SegmentMetricRHSCovJetExpansion.lean`).

The sealed curvature nonlinearity `-2 • Ric(g)` is the trace of the Levi-Civita curvature operator
(`RicciConnection.lean`).  Its segment difference normalises (at order zero,
`SegmentMetricCurvatureDifferenceOpDecomposition.lean`) into the concrete linear-in-difference section
`linearSection g₀ g₁ g₂`, whose fibre value is the model-basis trace of the linear (`∇₀ D`) order of
the per-metric Ricci difference (`D = connDiff gₖ g₀` the connection difference,
`ricciNeg2SectionDiffLinearEval`).  By the connection-difference cocycle
`connDiff g₁ g₂ = connDiff g₁ g₀ − connDiff g₂ g₀` the linear part carries the single difference factor
`connDiff g₁ g₂`, whose metrically-lowered Koszul form is the realized covariant derivative
`covDerivRealizeEval g₀ (T₁ − T₂)` of the perturbation difference
(`connDiffDiff_g0_lowered_koszul_diffFactor`) — i.e. the connection-level first covariant gradient
`R := covGrad g₀ 0 2 w` of the realized difference factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)`.

The genuine covariant-Faà-di-Bruno content beneath the curvature half of the segment-metric
right-hand-side expansion is carried by two **integrated two-arm `L²`** posits: the metric `L²`
norms of the order-`j` covariant jets of the cross-correction section difference
(`crossCorrectionSectionDiff_iteratedCovGrad_twoArm_l2Norm_le`) and of the quadratic Cross section
(`crossSection_iteratedCovGrad_twoArm_l2Norm_le`) are dominated by the Hamilton-tame two-arm sum
`Cd·∑_{i ≤ j+2}‖∇^i w‖ + Cd·‖(T₁−T₂).toHs a‖·∑_{l ≤ j+2}(‖∇^l T₁‖+‖∇^l T₂‖)`.  The POINTWISE
diagonal product-grid form of these posits (the previous architecture of this file) is **FALSE at
high order**: the Koszul-realized connection difference `connDiff = g₁⁻¹·(∇⁰h)` carries a Neumann
`k ≥ 2` layer injecting CUBIC jet monomials `(∇ᵃh)(∇ᵇh)(∇^{c+1}h)` into `∇^p D`, so no degree-2
pointwise product grid dominates (free-jet scaling certificate: `lhs_scale 2 = 8 > rhs_scale 2 = 4`);
and the earlier *pointwise two-arm* form was refuted twice over (the `g₀`-parallel small-volume
witness; the joint concentration bump at `j ≳ 2a`).  Only the integrated currency survives: the
`k = 1` bilinear layer is fed by the proven pointwise grids, the `k ≥ 2` cubic layer only by the
Gagliardo–Nirenberg absorption (`GagliardoNirenbergProductTwoArm.lean`), both inside the posits;
the `L²`-level consumer (`SegmentMetricRHSCovJetExpansion.lean`) reads the integrated forms
directly.

On top of the cross-correction posit the file proves the **integrated linear-section bound**
`ricciLinearSection_covGrad_twoArm_l2Norm_le`: through the parallel rank-reducing contraction `Φ`
and the principal-part identity
`exists_parallelTrace_linearSection_eq_koszulTriple_sub_crossCorrTriple`, the linear section splits
into the **Koszul arm** — bounded by `√(18·Φ.kappa)·‖∇^{j+2} w‖` via the integrated
trace-and-shift comparison and the pointwise `18`-domination of the traced Koszul jet, integrated —
and the **cross-correction arm**, the integrated posit through the trace-and-shift reduction.  Both
posits are **non-vacuous** (each carries the realized difference factor `w` up to `∇^{j+2} w` and
both fixed-pair endpoints; at `T₁ = T₂`, resp. `g₁ = g₂`, both sides vanish), carry no value-bounded
`Φ.op 0 2 w` shape (the refuted structural split), NO pointwise-`C^{>2}`-jet claim, NO pointwise
two-arm split, NO spectral-nonlinearity, and NO Weyl dependence. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Measure (chartModelBasis)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The connection-level rank-`3` Koszul triple of the realized difference factor.**  The clean
permuted-`covGrad` combination `R + permute (swap 0 1) R − permute c[0,2,1] R` on the once-differentiated
realized difference factor `R := covGrad g₀ 0 2 (realizeSymmCcTensor g₀ (T₁ − T₂))`, i.e. the three slot
readings of `covDerivRealizeEval g₀ (T₁ − T₂)` (the difference-arm building block of the `g₀`-lowered
Koszul connection-difference combination, `loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff`).
A `(0, 3)`-section, the input of the antisymmetrised permuted-trace pair's difference arm. -/
private def koszulTripleDiff (g₀ : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) : Integral.L2.SmoothCcTensor g₀ 0 3 :=
  Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))
    + DeTurck.permuteCcTensor (I := I) g₀ (Equiv.swap 0 1)
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))
    - DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1]
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))

/-- **The connection-level rank-`3` cross-correction difference.**  The fixed-pair cross piece
`2·crossCorrectionSection g₁ g₀ T₁ − 2·crossCorrectionSection g₂ g₀ T₂` of the `g₀`-lowered Koszul
connection-difference combination (`loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff`),
the nonlinear correction that rides on the fixed pair `T₁, T₂` and does not cancel pointwise. A
`(0, 3)`-section, the input of the antisymmetrised permuted-trace pair's cross arm. -/
private def crossCorrTripleDiff (g₀ : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ g₂ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 3 :=
  (2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
    - (2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂

/-- **The intrinsic `g₀⁻¹` double-trace operator field as a smooth compactly-supported
`(4 + a, 2 + a)`-tensor.**  The fibre value at `x` is `ricciModelTrace42Fib g₀ a x` (smooth by
`ricciModelTrace42Fib_contMDiff`); on the closed manifold it has compact support.  This is the smooth
operator field whose operator-field action contracts the leading two covariant slots against the
cometric `g₀⁻¹(x)` (scaled by `−2`). -/
noncomputable def ricciModelTrace42Field (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    Integral.L2.SmoothCcTensor g₀ (4 + a) (2 + a) where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace (4 + a) (2 + a) I x from
          ricciModelTrace42Fib (I := I) g₀ a x)
      contMDiff_toFun := ricciModelTrace42Fib_contMDiff (I := I) g₀ a }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- The underlying section value of `ricciModelTrace42Field g₀ a` at `x` is the fibre operator
`ricciModelTrace42Fib g₀ a x`.  Definitional. -/
@[simp] theorem ricciModelTrace42Field_toSection (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    (ricciModelTrace42Field (I := I) g₀ a).toSection x =
      (show Tensor0SBundle.TensorRSSpace (4 + a) (2 + a) I x from
        ricciModelTrace42Fib (I := I) g₀ a x) := rfl

/-- **The PASSENGER-PASSING intrinsic `g₀⁻¹` double-trace operator field at gradient-shift `a`**, a
smooth `(0, 4 + a) → (0, 2 + a)`-operator field defined as the `a`-fold passenger-slot extension
`slotExtendᵃ` of the **base** double-trace field `ricciModelTrace42Field g₀ 0` (which contracts the two
leading covariant slots `{0, 1}` against the cometric `g₀⁻¹`).  Each `slotExtend` prepends one leading
covariant passenger slot (read first, passed unchanged to the output, `slotExtendFib_apply_eval`), so
this field contracts the cometric `g₀⁻¹` against slots `{a, a + 1}` (the two curvature slots that sit
*after* the `a` accumulated leading gradient-passenger slots), passing the leading `a` slots.

The defining feature, **by construction**: `ricciModelTrace42FieldRec g₀ (a + 1) = slotExtend
(ricciModelTrace42FieldRec g₀ a)` (the `Nat`-equalities `(4 + a) + 1 = 4 + (a + 1)` and
`(2 + a) + 1 = 2 + (a + 1)` are definitional, as `Nat.add` recurses on the right).  This is what makes
the index-bump covariant Leibniz `ricciModelTrace42Op_covGrad` genuinely TRUE: the surviving operator
factor of the `appCcRS` B-rule (`covGrad_appCcRS_eq`), when the gradient differentiates the contracted
section, is exactly `slotExtend` of the operator field, which here advances `a → a + 1`.  At `a = 0` it
is `ricciModelTrace42Field g₀ 0` itself (contracting `{0, 1}`), so the order-zero operator `op 0` — and
the `linearSection` trace bridge that consumes it — is UNCHANGED. -/
noncomputable def ricciModelTrace42FieldRec (g₀ : SmoothRiemannianMetric I M) :
    ∀ a : ℕ, Integral.L2.SmoothCcTensor g₀ (4 + a) (2 + a)
  | 0 => ricciModelTrace42Field (I := I) g₀ 0
  | (a + 1) =>
    Integral.Connection.slotExtend (I := I) (M := M) g₀ (4 + a) (2 + a)
      (ricciModelTrace42FieldRec g₀ a)

set_option linter.unusedSectionVars false in
/-- The base of the passenger-passing field recursion is the leading-`{0,1}` double trace.  Definitional. -/
@[simp] theorem ricciModelTrace42FieldRec_zero (g₀ : SmoothRiemannianMetric I M) :
    ricciModelTrace42FieldRec (I := I) g₀ 0 = ricciModelTrace42Field (I := I) g₀ 0 := rfl

set_option linter.unusedSectionVars false in
/-- **The successor step of the passenger-passing field recursion is one `slotExtend`.**  This is the
key structural identity that makes the index-bump covariant Leibniz true: advancing the gradient-shift
`a → a + 1` is exactly prepending one leading passenger covariant slot.  Definitional (the rank
equalities `(4 + a) + 1 = 4 + (a + 1)`, `(2 + a) + 1 = 2 + (a + 1)` hold by `Nat.add`-on-the-right). -/
@[simp] theorem ricciModelTrace42FieldRec_succ (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ricciModelTrace42FieldRec (I := I) g₀ (a + 1) =
      Integral.Connection.slotExtend (I := I) (M := M) g₀ (4 + a) (2 + a)
        (ricciModelTrace42FieldRec (I := I) g₀ a) := rfl

/-- **The section-level `−2` intrinsic `g₀⁻¹` double-trace operator `(0, 4 + a) → (0, 2 + a)`.**  The
genuine building block of the antisymmetrised permuted-trace parallel contraction: the operator at
gradient-shift `a` that contracts the leading two of the `4 + a` covariant slots of a smooth
`(0, 4 + a)`-tensor against the cometric `g₀⁻¹` (the `g₀⁻¹` double trace `∑ᵢ D(♯eᵢ, ♯eᵢ, ·)`, with
`♯eᵢ` the `g₀`-raised `E`-orthonormal coframe) and scales by `−2`, producing a smooth
compactly-supported `(0, 2 + a)`-tensor.  This is a **divergence-type single-pattern** cometric
contraction (NOT by itself the `−2` intrinsic `g₀⁻¹` Ricci trace — that is the `½`-scaled
antisymmetrised two-pattern combination of its slot-permuted images,
`linearSection_eq_ricciModelTrace42_loweredConnDiffSub`); it is the rank-reducing parallel
contraction out of which the Ricci difference arm's trace pair is composed, and it depends on the
background metric `g₀` only through the cometric, with NO chart-selected ambient basis.

It is constructed concretely as the operator-field action `appCcRS` of the **passenger-passing** smooth
`g₀⁻¹` double-trace operator field `ricciModelTrace42FieldRec g₀ a = slotExtendᵃ (base)` (contracting
the cometric `g₀⁻¹` against the slots `{a, a + 1}` after the `a` leading gradient-passenger slots) on the
input `(0, 4 + a)`-tensor — the same smooth-section route as the algebraic trace `contractCcTensor` and
the curvature operator-field action `appCc`.  At `a = 0` the field is `ricciModelTrace42Field g₀ 0`
(contracting `{0, 1}`), so `op 0` is unchanged. -/
noncomputable def ricciModelTrace42Op (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    Integral.L2.SmoothCcTensor g₀ 0 (4 + a) → Integral.L2.SmoothCcTensor g₀ 0 (2 + a) :=
  fun T =>
    DifferentialGeometry.Integral.Connection.appCcRS (I := I) (M := M) g₀ 0 (4 + a) (2 + a)
      (ricciModelTrace42FieldRec (I := I) g₀ a) T

set_option linter.unusedSectionVars false in
/-- **The fibre value of `ricciModelTrace42Op` is the fibrewise composition of the passenger-passing
double-trace fibre operator with the input section.**  Definitional via `appCcRS_toSection`. -/
@[simp] theorem ricciModelTrace42Op_toSection (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (T : Integral.L2.SmoothCcTensor g₀ 0 (4 + a)) (x : M) :
    (ricciModelTrace42Op (I := I) g₀ a T).toSection x =
      (show Tensor0SBundle.Tensor0SSpace (4 + a) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a) I x from
        (ricciModelTrace42FieldRec (I := I) g₀ a).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (4 + a) I x from
          T.toSection x) := by
  rw [ricciModelTrace42Op,
    DifferentialGeometry.Integral.Connection.appCcRS_toSection (I := I) (M := M) g₀ 0 (4 + a) (2 + a)
      (ricciModelTrace42FieldRec (I := I) g₀ a) T x]

set_option linter.unusedSectionVars false in
/-- **Fibrewise `ℝ`-additivity of the section-level cometric double-trace operator.**  The
`−2` cometric double trace `ricciModelTrace42Op` distributes over a section difference: it is the
operator-field action `appCcRS` of the fixed double-trace field, and that action is additive in the
contracted section (via `appCcRS_add_right` / `appCcRS_smul_right`, the operator-field action being
fibrewise composition, additive in the right factor). -/
theorem ricciModelTrace42Op_sub (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (A B : Integral.L2.SmoothCcTensor g₀ 0 (4 + a)) :
    ricciModelTrace42Op (I := I) g₀ a (A - B) =
      ricciModelTrace42Op (I := I) g₀ a A - ricciModelTrace42Op (I := I) g₀ a B := by
  rw [ricciModelTrace42Op, ricciModelTrace42Op, ricciModelTrace42Op, sub_eq_add_neg,
    DifferentialGeometry.Integral.Connection.appCcRS_add_right,
    show (-B) = (-1 : ℝ) • B by rw [neg_one_smul],
    DifferentialGeometry.Integral.Connection.appCcRS_smul_right, neg_one_smul, ← sub_eq_add_neg]

set_option linter.unusedSectionVars false in
/-- **Leading-slot multilinear sum expansion.**  Evaluating a model `(0, s + 1)`-tensor on a tuple
whose leading entry is a finite sum expands the sum out of the leading slot (multilinearity, read
through the leading-slot curry equivalence). -/
private theorem model_cons_slot0_sum {s : ℕ} {ι : Type*} (fs : Finset ι)
    (T : Tensor0SBundle.Tensor0SModel (s + 1) ℝ E) (f : ι → E) (rest : Fin s → E) :
    T (Fin.cons (∑ i ∈ fs, f i) rest) = ∑ i ∈ fs, T (Fin.cons (f i) rest) := by
  have h : ∀ u : E, T (Fin.cons u rest) =
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1) => E) ℝ) T u) rest := by
    intro u
    rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [h, map_sum, ContinuousMultilinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => (h (f i)).symm

set_option linter.unusedSectionVars false in
/-- **Leading-slot multilinear scalar expansion.**  Evaluating a model `(0, s + 1)`-tensor on a tuple
whose leading entry is a scalar multiple pulls the scalar out of the leading slot. -/
private theorem model_cons_slot0_smul {s : ℕ} (c : ℝ) (u : E)
    (T : Tensor0SBundle.Tensor0SModel (s + 1) ℝ E) (rest : Fin s → E) :
    T (Fin.cons (c • u) rest) = c * T (Fin.cons u rest) := by
  have h : ∀ z : E, T (Fin.cons z rest) =
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1) => E) ℝ) T z) rest := by
    intro z
    rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [h, map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul, ← h]

set_option linter.unusedSectionVars false in
/-- **The smooth orthonormal frame is a tangent basis on its orthonormality neighbourhood.**  At any
point `y` of the orthonormality neighbourhood of the frame attached at `x`, the value family
`i ↦ smoothOrthoFrame g₀ x i y` is `g₀(y)`-orthonormal, hence linearly independent and (cardinality
`finrank`) a `Module.Basis` of `T_y M`.  This extends `smoothOrthoFrame_basis_witness` (the `y = x`
case) to the whole orthonormality neighbourhood. -/
private theorem smoothOrthoFrame_basis_at (g₀ : SmoothRiemannianMetric I M) (x : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x) :
    ∃ bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y),
      ∀ i, bse i = smoothOrthoFrame (I := I) g₀ x i y := by
  classical
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner y (smoothOrthoFrame (I := I) g₀ x a y)
        (smoothOrthoFrame (I := I) g₀ x b y) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal (I := I) g₀ x hy a b
  have he_li : LinearIndependent ℝ
      (fun i => smoothOrthoFrame (I := I) g₀ x i y) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g₀.inner y (smoothOrthoFrame (I := I) g₀ x k y)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g₀ x j y) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g₀.inner y (smoothOrthoFrame (I := I) g₀ x k y)
        (c j • smoothOrthoFrame (I := I) g₀ x j y) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g₀.inner y (smoothOrthoFrame (I := I) g₀ x k y)).map_smul (c j),
        smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E :=
    Fintype.card_fin _
  exact ⟨basisOfLinearIndependentOfCardEqFinrank he_li hcard,
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i⟩

set_option linter.unusedSectionVars false in
/-- **Orthonormal expansion in the smooth orthonormal frame.**  At any point `y` of the
orthonormality neighbourhood, every tangent vector expands against the `g₀(y)`-orthonormal frame
values with metric coefficients: `u = ∑ᵢ g₀(u, Bᵢ y) • Bᵢ y`. -/
private theorem smoothOrthoFrame_expansion_at (g₀ : SmoothRiemannianMetric I M) (x : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x) (u : TangentSpace I y) :
    u = ∑ i : Fin (Module.finrank ℝ E),
      g₀.inner y u (smoothOrthoFrame (I := I) g₀ x i y) •
        smoothOrthoFrame (I := I) g₀ x i y := by
  classical
  obtain ⟨bse, hbse⟩ := smoothOrthoFrame_basis_at (I := I) g₀ x hy
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner y (smoothOrthoFrame (I := I) g₀ x a y)
        (smoothOrthoFrame (I := I) g₀ x b y) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal (I := I) g₀ x hy a b
  have hcoeff : ∀ j : Fin (Module.finrank ℝ E),
      g₀.inner y u (smoothOrthoFrame (I := I) g₀ x j y) = bse.repr u j := by
    intro j
    rw [g₀.symm y u (smoothOrthoFrame (I := I) g₀ x j y)]
    conv_lhs => rw [← bse.sum_repr u]
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [(g₀.inner y (smoothOrthoFrame (I := I) g₀ x j y)).map_smul (bse.repr u i),
        smul_eq_mul, hbse i, horth j i])]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [if_pos rfl, mul_one]
    · intro i _ hij
      rw [if_neg (fun h => hij h.symm), mul_zero]
  calc u = ∑ i : Fin (Module.finrank ℝ E), bse.repr u i • bse i := (bse.sum_repr u).symm
    _ = ∑ i : Fin (Module.finrank ℝ E),
        g₀.inner y u (smoothOrthoFrame (I := I) g₀ x i y) •
          smoothOrthoFrame (I := I) g₀ x i y := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoeff i, hbse i]

set_option linter.unusedSectionVars false in
/-- **The cometric raise of the `k`-th dual-basis model covector pairs to the `k`-th basis
coordinate.**  `g₀(♯b^k, u) = repr(u)ₖ`: the defining inverse property of the cometric sharp
(`inverseMetricSharpFib_inner`), read on the model dual basis `b^k := cDualBasis k` of `finBasis`.
This is the form in which the cometric raise enters every raised-coframe trace — in particular it is
the `hP` input of the dual-pair trace conversion `sum_inner_dualPair_apply_eq_sum_chartBasis_repr`. -/
private theorem cometricLmodel_dualBasis_inner (g₀ : SmoothRiemannianMetric I M) (y : M)
    (k : Fin (Module.finrank ℝ E)) (u : TangentSpace I y) :
    g₀.inner y (cometricLmodel (I := I) g₀ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) u =
      (Module.finBasis ℝ E).repr (u : E) k := by
  have h1 : cometricLmodel (I := I) g₀ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) =
      inverseMetricSharpFib (I := I) g₀ y
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 y).symm
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) := rfl
  rw [h1, inverseMetricSharpFib_inner (I := I) g₀ y _ u, cotangentToDualLinear_apply,
    cotangentToDual_apply]
  have h2 : (((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 y).symm
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) (fun _ : Fin 1 => u) : ℝ) =
      Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k) (fun _ : Fin 1 => (u : E)) := rfl
  rw [h2, Tensor0SBundle.model_covectorOfCLM_apply]
  rw [show ((Module.finBasis ℝ E).cDualBasis k) =
      LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) from by
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    congr 1
    exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k]
  rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]

set_option linter.unusedSectionVars false in
/-- **The cometric dual-basis double trace equals the orthonormal-frame diagonal sum.**  At any
point `y` of the orthonormality neighbourhood of the frame attached at `x`, the frame-free cometric
double trace of a model `(0, s + 2)`-tensor `T` — slot `0` raised by the cometric `♯` of the model
dual-basis covectors, slot `1` contracted against the model basis — equals the `g₀(y)`-orthonormal
frame diagonal sum:
```
∑ₖ T(♯ b^k, b_k, mm) = ∑ᵢ T(Bᵢ y, Bᵢ y, mm).
```
Proved by the orthonormal expansion of the raised covectors (`♯ b^k = ∑ᵢ (repr (Bᵢ y) k) • Bᵢ y`,
since `g₀(♯ b^k, u) = b^k(u) = repr u k` by the inverse property of the sharp), swapping the two
finite sums, and re-collapsing the inner slot-`1` sum with the basis expansion
`∑ₖ repr v k • b_k = v`. -/
private theorem cometric_dualTrace_eq_orthoFrame_diag (g₀ : SmoothRiemannianMetric I M)
    {s : ℕ} (x : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x)
    (T : Tensor0SBundle.Tensor0SModel (s + 2) ℝ E) (mm : Fin s → E) :
    ∑ k : Fin (Module.finrank ℝ E),
        T (Fin.cons (cometricLmodel (I := I) g₀ y
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) mm)) =
      ∑ i : Fin (Module.finrank ℝ E),
        T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) mm)) := by
  classical
  -- The sharp of the `k`-th dual-basis model covector pairs to the `k`-th basis coordinate.
  have hsharp : ∀ (k : Fin (Module.finrank ℝ E)) (u : TangentSpace I y),
      g₀.inner y (cometricLmodel (I := I) g₀ y
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) u =
        (Module.finBasis ℝ E).repr (u : E) k :=
    fun k u => cometricLmodel_dualBasis_inner (I := I) g₀ y k u
  -- Orthonormal expansion of each raised dual-basis covector in the frame.
  have hexp : ∀ k : Fin (Module.finrank ℝ E),
      cometricLmodel (I := I) g₀ y
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr
              ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) •
            smoothOrthoFrame (I := I) g₀ x i y := by
    intro k
    conv_lhs => rw [smoothOrthoFrame_expansion_at (I := I) g₀ x hy
      (cometricLmodel (I := I) g₀ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)))]
    exact Finset.sum_congr rfl fun i _ => by
      rw [hsharp k (smoothOrthoFrame (I := I) g₀ x i y)]
  calc ∑ k : Fin (Module.finrank ℝ E),
      T (Fin.cons (cometricLmodel (I := I) g₀ y
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) mm))
      = ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr
              ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) *
            T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
                (Fin.cons ((Module.finBasis ℝ E) k) mm)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hexp k, model_cons_slot0_sum (E := E)]
        exact Finset.sum_congr rfl fun i _ => model_cons_slot0_smul (E := E) _ _ T _
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr
              ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) *
            T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
                (Fin.cons ((Module.finBasis ℝ E) k) mm)) := Finset.sum_comm
    _ = ∑ i : Fin (Module.finrank ℝ E),
          T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) mm)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hcurry : ∀ z : E,
            T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
                (Fin.cons z mm)) =
            ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 2) => E) ℝ) T
                ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E))
              (Fin.cons z mm) := by
          intro z
          rw [continuousMultilinearCurryLeftEquiv_apply]
        calc ∑ k : Fin (Module.finrank ℝ E),
            ((Module.finBasis ℝ E).repr
                ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) *
              T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
                  (Fin.cons ((Module.finBasis ℝ E) k) mm))
            = ∑ k : Fin (Module.finrank ℝ E),
                ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 2) => E) ℝ) T
                    ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E))
                  (Fin.cons (((Module.finBasis ℝ E).repr
                      ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) •
                    ((Module.finBasis ℝ E) k)) mm) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [model_cons_slot0_smul (E := E), ← hcurry]
          _ = ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 2) => E) ℝ) T
                  ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E))
                (Fin.cons (∑ k : Fin (Module.finrank ℝ E),
                  ((Module.finBasis ℝ E).repr
                      ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) k) •
                    ((Module.finBasis ℝ E) k)) mm) :=
              (model_cons_slot0_sum (E := E) Finset.univ _ _ mm).symm
          _ = T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) mm)) := by
              rw [(Module.finBasis ℝ E).sum_repr
                ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E), ← hcurry]

set_option linter.unusedSectionVars false in
/-- **The fibre value of the base `g₀⁻¹` double-trace field is the `−2`-scaled orthonormal-frame
diagonal double insertion.**  At any point `y` of the orthonormality neighbourhood of the frame
attached at `x`, the base double-trace fibre operator reads a `(0, 4)`-tensor `D` as
```
ricciModelTrace42Fib g₀ 0 y D = (−2) • ∑ᵢ curry₂ (curry₃ D (Bᵢ y)) (Bᵢ y),
```
the `g₀(y)`-orthonormal diagonal trace of the two leading covariant slots.  This is the frame
reading of the frame-free cometric double trace (`cometric_dualTrace_eq_orthoFrame_diag`). -/
private theorem ricciModelTrace42Fib_eq_orthoFrame_diag (g₀ : SmoothRiemannianMetric I M)
    (x : M) {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x)
    (D : Tensor0SBundle.Tensor0SSpace 4 I y) :
    ricciModelTrace42Fib (I := I) g₀ 0 y D =
      (-2 : ℝ) • ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 y
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 y D
            (smoothOrthoFrame (I := I) g₀ x i y))
          (smoothOrthoFrame (I := I) g₀ x i y) := by
  classical
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun mm => ?_
  beta_reduce
  rw [show Tensor0SBundle.Tensor0SSpace.toModel (ricciModelTrace42Fib (I := I) g₀ 0 y D) =
      (-2 : ℝ) • modelDoubleTrace (E := E) (2 + 0) (cometricLmodel (I := I) g₀ y)
        (modelRankCast (E := E) (by omega : (4 + 0) = (2 + 0) + 2)
          (Tensor0SBundle.Tensor0SSpace.toModel D)) from
    ricciModelTrace42Fib_toModel (I := I) g₀ 0 y D]
  rw [show (modelRankCast (E := E) (by omega : (4 + 0) = (2 + 0) + 2)
        (Tensor0SBundle.Tensor0SSpace.toModel D)) =
      Tensor0SBundle.Tensor0SSpace.toModel D from rfl]
  rw [ContinuousMultilinearMap.smul_apply,
    modelDoubleTrace_apply (E := E) (2 + 0) (cometricLmodel (I := I) g₀ y)
      (Tensor0SBundle.Tensor0SSpace.toModel D) mm]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 y
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 y D
              (smoothOrthoFrame (I := I) g₀ x i y))
            (smoothOrthoFrame (I := I) g₀ x i y)) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 y
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 y D
              (smoothOrthoFrame (I := I) g₀ x i y))
            (smoothOrthoFrame (I := I) g₀ x i y)) from
    map_sum (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 2 y) _ _]
  rw [ContinuousMultilinearMap.sum_apply]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ (s := 2) x hy
    (Tensor0SBundle.Tensor0SSpace.toModel D) mm]
  refine congrArg (fun z : ℝ => (-2 : ℝ) • z) (Finset.sum_congr rfl fun i _ => ?_)
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 y D
        (smoothOrthoFrame (I := I) g₀ x i y))
      (v0 := ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E)) (vs := mm),
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (T := D)
      (v0 := ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E))
      (vs := Fin.cons ((smoothOrthoFrame (I := I) g₀ x i y : TangentSpace I y) : E) mm)]

set_option linter.unusedSectionVars false in
/-- **The skew moving-frame correction cancels.**  The two correction sums of the orthonormal-frame
diagonal Leibniz expansion — the differentiated frame read into slot `0` against the frame in slot
`1`, plus the frame in slot `0` against the differentiated frame in slot `1` — cancel, by the
orthonormal expansion of the frame derivative and the connection skew-symmetry
`g₀(∇ᵥBᵢ, Bⱼ) = −g₀(Bᵢ, ∇ᵥBⱼ)` (`smoothOrthoFrame_cov_skew`, the metric compatibility on the
locally-constant frame pairing). -/
private theorem orthoFrame_skew_correction_cancel (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : E) (T : Tensor0SBundle.Tensor0SModel 4 ℝ E) (mm : Fin 2 → E) :
    (∑ i : Fin (Module.finrank ℝ E),
        T (Fin.cons (((LeviCivita (I := I) g₀).toFun
              (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm)))
      + (∑ i : Fin (Module.finrank ℝ E),
          T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
              (Fin.cons (((LeviCivita (I := I) g₀).toFun
                  (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E) mm))) = 0 := by
  classical
  set a : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i j =>
    g₀.inner x ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)
      (smoothOrthoFrame (I := I) g₀ x j x) with ha_def
  have haskew : ∀ i j, a i j = - a j i := by
    intro i j
    change g₀.inner x ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)
        (smoothOrthoFrame (I := I) g₀ x j x) =
      - g₀.inner x ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x j) x v)
        (smoothOrthoFrame (I := I) g₀ x i x)
    rw [smoothOrthoFrame_cov_skew (I := I) g₀ x i j v]
    rw [g₀.symm x (smoothOrthoFrame (I := I) g₀ x i x)
      ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x j) x v)]
  have hexp : ∀ i : Fin (Module.finrank ℝ E),
      (LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v =
        ∑ j : Fin (Module.finrank ℝ E), a i j • smoothOrthoFrame (I := I) g₀ x j x :=
    fun i => smoothOrthoFrame_expansion_at (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)
  have hS1 : (∑ i : Fin (Module.finrank ℝ E),
      T (Fin.cons (((LeviCivita (I := I) g₀).toFun
            (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (((LeviCivita (I := I) g₀).toFun
          (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E) =
        ((∑ j : Fin (Module.finrank ℝ E),
          a i j • smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E) from by
      rw [← hexp i]]
    rw [model_cons_slot0_sum (E := E)]
    exact Finset.sum_congr rfl fun j _ => model_cons_slot0_smul (E := E) _ _ T _
  have hS2 : (∑ i : Fin (Module.finrank ℝ E),
      T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
          (Fin.cons (((LeviCivita (I := I) g₀).toFun
              (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E) mm))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E) mm)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcurry : ∀ z : E,
        T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
            (Fin.cons z mm)) =
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => E) ℝ) T
            ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E))
          (Fin.cons z mm) := by
      intro z
      rw [continuousMultilinearCurryLeftEquiv_apply]
    rw [hcurry]
    rw [show (((LeviCivita (I := I) g₀).toFun
          (smoothOrthoFrame (I := I) g₀ x i) x v : TangentSpace I x) : E) =
        ((∑ j : Fin (Module.finrank ℝ E),
          a i j • smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E) from by
      rw [← hexp i]]
    rw [model_cons_slot0_sum (E := E)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [model_cons_slot0_smul (E := E), ← hcurry]
  rw [hS1, hS2]
  have h2 : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E) mm))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        -(a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [haskew j i, neg_mul]
  rw [h2]
  rw [show (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      -(a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm)))) =
      -(∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        a i j * T (Fin.cons ((smoothOrthoFrame (I := I) g₀ x j x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E) mm))) from by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_neg_distrib]]
  exact add_neg_cancel _

set_option linter.unusedSectionVars false in
/-- **The fibre-level skew correction sums cancel.**  The two moving-frame correction sums of the
orthonormal-frame diagonal Leibniz expansion cancel as `(0, 2)`-tensor fibre elements
(`orthoFrame_skew_correction_cancel` read through `toModel`-extensionality). -/
private theorem orthoFrame_corrections_sum_eq_zero (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : E) (W4 : Tensor0SBundle.Tensor0SSpace 4 I x) :
    (∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x W4
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v))
          (smoothOrthoFrame (I := I) g₀ x i x))
      + (∑ i : Fin (Module.finrank ℝ E),
          Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x W4
              (smoothOrthoFrame (I := I) g₀ x i x))
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)) = 0 := by
  classical
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun mm => ?_
  beta_reduce
  have heval : ∀ (z₁ z₂ : TangentSpace I x),
      Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x W4 z₁) z₂) mm =
        Tensor0SBundle.Tensor0SSpace.toModel W4
          (Fin.cons ((z₁ : TangentSpace I x) : E)
            (Fin.cons ((z₂ : TangentSpace I x) : E) mm)) := by
    intro z₁ z₂
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x W4 z₁)
      (v0 := ((z₂ : TangentSpace I x) : E)) (vs := mm)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (T := W4)
      (v0 := ((z₁ : TangentSpace I x) : E))
      (vs := Fin.cons ((z₂ : TangentSpace I x) : E) mm)]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_add]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x W4
              ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v))
            (smoothOrthoFrame (I := I) g₀ x i x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x W4
              ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v))
            (smoothOrthoFrame (I := I) g₀ x i x)) from
    map_sum (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 2 x) _ _]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x W4
              (smoothOrthoFrame (I := I) g₀ x i x))
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x W4
              (smoothOrthoFrame (I := I) g₀ x i x))
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)) from
    map_sum (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 2 x) _ _]
  rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.sum_apply]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    heval ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v)
      (smoothOrthoFrame (I := I) g₀ x i x))]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    heval (smoothOrthoFrame (I := I) g₀ x i x)
      ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v))]
  rw [Tensor0SBundle.Tensor0SSpace.toModel_zero, ContinuousMultilinearMap.zero_apply]
  exact orthoFrame_skew_correction_cancel (I := I) g₀ x v
    (Tensor0SBundle.Tensor0SSpace.toModel W4) mm

set_option linter.unusedSectionVars false in
/-- **The finite-sum additivity of the `(0, s)`-tensor covariant derivative.**  The bundled
Levi-Civita `(0, s)`-tensor covariant derivative distributes over a finite sum of smooth sections
(iterated `IsCovariantDerivativeOn.add` by `Finset` induction). -/
private theorem tensor0SCovDeriv_finset_sum (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    {ι : Type*} (fs : Finset ι)
    (σ : ι → Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel s ℝ E,
      (fun y : M => Tensor0SBundle.Tensor0SSpace s I y)⟯) (x : M) :
    Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g₀)
        (fun y : M => ∑ i ∈ fs, σ i y) x =
      ∑ i ∈ fs, Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g₀)
        (fun y : M => σ i y) x := by
  classical
  induction fs using Finset.cons_induction with
  | empty =>
    rw [show (fun y : M => ∑ i ∈ (∅ : Finset ι), σ i y) =
        (0 : Π y : M, Tensor0SBundle.Tensor0SSpace s I y) from
      funext fun y => Finset.sum_empty]
    rw [Finset.sum_empty]
    exact (Tensor0SNabla.tensor0SCovariantDerivative I M s
      (LeviCivita (I := I) g₀)).isCovariantDerivativeOnUniv.zero (Set.mem_univ x)
  | cons b fs' hb ih =>
    have hsum_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z) y (∑ i ∈ fs', σ i y)) := by
      refine (∑ i ∈ fs', σ i :
        Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel s ℝ E,
          (fun y : M => Tensor0SBundle.Tensor0SSpace s I y)⟯).contMDiff.congr fun y => ?_
      rw [ContMDiffSection.finset_sum_apply]
    have hadd := (Tensor0SNabla.tensor0SCovariantDerivative I M s
        (LeviCivita (I := I) g₀)).isCovariantDerivativeOnUniv.add
      (σ := fun y : M => σ b y) (σ' := fun y : M => ∑ i ∈ fs', σ i y) (x := x)
      (((σ b).contMDiff x).mdifferentiableAt (by norm_num))
      ((hsum_smooth x).mdifferentiableAt (by norm_num)) (Set.mem_univ x)
    rw [show (fun y : M => ∑ i ∈ Finset.cons b fs' hb, σ i y) =
        ((fun y : M => σ b y) + fun y : M => ∑ i ∈ fs', σ i y) from
      funext fun y => Finset.sum_cons hb]
    rw [hadd, ih, Finset.sum_cons]

set_option linter.unusedSectionVars false in
/-- **The orthonormal-frame diagonal Leibniz expansion of the double insertion.**  The directional
`(0, 2)`-tensor covariant derivative of the doubly-frame-inserted section
`y ↦ curry₂ (curry₃ (w y) (Bᵢ y)) (Bᵢ y)` splits by the leading-slot Hom-Leibniz
(`tensor0SCovariantDerivative_curriedSection_hom_leibniz`, applied twice) into the diagonal jet term
plus the two moving-frame corrections. -/
private theorem covDeriv_doubleInsert_leibniz (g₀ : SmoothRiemannianMetric I M)
    (w : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 4 ℝ E,
      (fun y : M => Tensor0SBundle.Tensor0SSpace 4 I y)⟯)
    (x : M) (i : Fin (Module.finrank ℝ E)) (v : E) :
    Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
        (fun y : M => (Tensor0SNabla.curriedSection I M
          (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
            (smoothOrthoFrame (I := I) g₀ x i z)) y)
          (smoothOrthoFrame (I := I) g₀ x i y)) x v =
      Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x
            (Tensor0SNabla.tensor0SCovariantDerivative I M 4 (LeviCivita (I := I) g₀)
              (fun y : M => w y) x v)
            (smoothOrthoFrame (I := I) g₀ x i x))
          (smoothOrthoFrame (I := I) g₀ x i x)
        + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x (w x)
              ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v))
            (smoothOrthoFrame (I := I) g₀ x i x)
        + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x (w x)
              (smoothOrthoFrame (I := I) g₀ x i x))
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v) := by
  classical
  have hCi_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        (smoothOrthoFrame (I := I) g₀ x i y)) :=
    smoothOrthoFrame_smooth (I := I) g₀ x i
  let Ci : ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    ⟨fun y : M => smoothOrthoFrame (I := I) g₀ x i y, hCi_smooth⟩
  -- the once-inserted `(0, 3)`-section and its smoothness
  have hu_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) y
        ((Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
          (smoothOrthoFrame (I := I) g₀ x i y))) := by
    have hcurried : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 3 ℝ E)
          (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I z) y
          (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)) :=
      fun y => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section
        (I := I) (M := M) (fun z' : M => w z') y (w.contMDiff y)
    exact ContMDiff.clm_bundle_apply (b := id) hcurried Ci.contMDiff
  have hu_at : TensorSectionMDiffAt (I := I) 3
      (fun y : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
        (smoothOrthoFrame (I := I) g₀ x i y)) x :=
    (hu_smooth x).mdifferentiableAt (by norm_num)
  have hw_at : TensorSectionMDiffAt (I := I) 4 (fun y : M => w y) x :=
    (w.contMDiff x).mdifferentiableAt (by norm_num)
  -- outer peel (`s = 2`), defeq-cast to the frame spelling
  have h1 : Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
        (fun y : M => (Tensor0SNabla.curriedSection I M
          (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
            (smoothOrthoFrame (I := I) g₀ x i z)) y)
          (smoothOrthoFrame (I := I) g₀ x i y)) x v =
      Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
          (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
            (fun y : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
              (smoothOrthoFrame (I := I) g₀ x i y)) x v)
          (smoothOrthoFrame (I := I) g₀ x i x)
        + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
            (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x (w x)
              (smoothOrthoFrame (I := I) g₀ x i x))
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v) :=
    Integral.Connection.tensor0SCovariantDerivative_curriedSection_hom_leibniz
      (I := I) (M := M) g₀ 2
      (fun y : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
        (smoothOrthoFrame (I := I) g₀ x i y)) (x := x) hu_at Ci v
  -- inner peel (`s = 3`), defeq-cast to the frame spelling
  have h2 : Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)
        (fun y : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
          (smoothOrthoFrame (I := I) g₀ x i y)) x v =
      Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x
          (Tensor0SNabla.tensor0SCovariantDerivative I M 4 (LeviCivita (I := I) g₀)
            (fun y : M => w y) x v)
          (smoothOrthoFrame (I := I) g₀ x i x)
        + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x (w x)
            ((LeviCivita (I := I) g₀).toFun (smoothOrthoFrame (I := I) g₀ x i) x v) :=
    Integral.Connection.tensor0SCovariantDerivative_curriedSection_hom_leibniz
      (I := I) (M := M) g₀ 3 (fun y : M => w y) (x := x) hw_at Ci v
  rw [h1, h2, map_add (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x),
    ContinuousLinearMap.add_apply]

set_option linter.unusedSectionVars false in
/-- **The cometric `∇₀`-parallelism base core: the leading-`{0,1}` `g₀⁻¹` double-trace field is
`∇₀`-parallel.**  The covariant gradient of the *base* intrinsic `g₀⁻¹` double-trace operator field
(`a = 0`, contracting the two leading covariant slots `{0, 1}` against the cometric, via the cometric
index-raise `♯ = inverseMetricSharpField` then the FRAME-FREE natural trace) vanishes:
```
covGrad g₀ 4 2 (ricciModelTrace42Field g₀ 0) = 0.
```
This is the genuine deep cometric-parallelism core `∇₀ g₀⁻¹ = 0`.

**Proof.**  It suffices that the directional covariant derivative of the field vanishes at every
base point and direction.  By the Hom-connection product rule (`tensorRSCovariantDerivative_apply`,
tested on a smooth section `w` through an arbitrary fibre value), this reduces to the intertwining
`∇₀ᵥ(Φ·w) = Φₓ(∇₀ᵥw)` — the covariant derivative commutes with the cometric double trace.  Near `x`
the frame-free cometric trace agrees with the `g₀`-orthonormal diagonal sum against the smooth
orthonormal frame attached at `x` (`ricciModelTrace42Fib_eq_orthoFrame_diag`, the value identity on
the orthonormality neighbourhood), so by locality (`IsCovariantDerivativeOn.congr_of_eventuallyEq`)
and finite-sum additivity the derivative passes to the per-frame-direction double insertions; the
leading-slot Hom-Leibniz (`covDeriv_doubleInsert_leibniz`, two peels) produces the diagonal jet term
`∑ᵢ (∇₀ᵥw)(Bᵢ, Bᵢ, ·)` — which is exactly `Φₓ(∇₀ᵥw)` by the value identity at `x` — plus the two
moving-frame corrections, which cancel by the orthonormal expansion and the connection
skew-symmetry `g₀(∇ᵥBᵢ, Bⱼ) = −g₀(Bᵢ, ∇ᵥBⱼ)` (`orthoFrame_skew_correction_cancel`, the cometric
skew core `∇₀ g₀⁻¹ = 0` read on the frame). -/
theorem ricciModelTrace42Field_covGrad_eq_zero (g₀ : SmoothRiemannianMetric I M) :
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 4 2
        (ricciModelTrace42Field (I := I) g₀ 0) = 0 := by
  classical
  have hdir : ∀ (x : M) (v : E),
      Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ 4 2
        (ricciModelTrace42Field (I := I) g₀ 0) x v = 0 := by
    intro x v
    apply ContinuousLinearMap.ext
    intro D
    obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := Tensor0SBundle.Tensor0SModel 4 ℝ E)
      (V := fun y : M => Tensor0SBundle.Tensor0SSpace 4 I y) (n := (⊤ : ℕ∞)) x D
    have hPR := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) 4 2
      (LeviCivita (I := I) g₀) (ricciModelTrace42Field (I := I) g₀ 0).toSection w x v
    rw [Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_def (I := I) (M := M) g₀ 4 2
      (ricciModelTrace42Field (I := I) g₀ 0) x v, ContinuousLinearMap.zero_apply, ← hw]
    refine Eq.trans hPR ?_
    rw [sub_eq_zero]
    -- the per-frame double insertions (as smooth sections)
    have hCi_smooth : ∀ i : Fin (Module.finrank ℝ E),
        ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
            (smoothOrthoFrame (I := I) g₀ x i y)) :=
      fun i => smoothOrthoFrame_smooth (I := I) g₀ x i
    have hu_smooth : ∀ i : Fin (Module.finrank ℝ E),
        ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
            (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) y
            ((Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)
              (smoothOrthoFrame (I := I) g₀ x i y))) := by
      intro i
      have hcurried : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 3 ℝ E)
            (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I z) y
            (Tensor0SNabla.curriedSection I M (fun z' : M => w z') y)) :=
        fun y => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section
          (I := I) (M := M) (fun z' : M => w z') y (w.contMDiff y)
      exact ContMDiff.clm_bundle_apply (b := id) hcurried (hCi_smooth i)
    have ht_smooth : ∀ i : Fin (Module.finrank ℝ E),
        ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
            (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) y
            ((Tensor0SNabla.curriedSection I M
              (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
                (smoothOrthoFrame (I := I) g₀ x i z)) y)
              (smoothOrthoFrame (I := I) g₀ x i y))) := by
      intro i
      have hcurried : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 2 ℝ E)
            (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I z) y
            (Tensor0SNabla.curriedSection I M
              (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
                (smoothOrthoFrame (I := I) g₀ x i z)) y)) :=
        fun y => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section
          (I := I) (M := M)
          (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
            (smoothOrthoFrame (I := I) g₀ x i z)) y (hu_smooth i y)
      exact ContMDiff.clm_bundle_apply (b := id) hcurried (hCi_smooth i)
    let ti : Fin (Module.finrank ℝ E) →
        Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 2 ℝ E,
          (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y)⟯ := fun i =>
      ⟨fun y : M => (Tensor0SNabla.curriedSection I M
          (fun z : M => (Tensor0SNabla.curriedSection I M (fun z' : M => w z') z)
            (smoothOrthoFrame (I := I) g₀ x i z)) y)
          (smoothOrthoFrame (I := I) g₀ x i y), ht_smooth i⟩
    -- the traced section is smooth
    have hP_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) y
          ((show Tensor0SBundle.Tensor0SSpace 4 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
            (ricciModelTrace42Field (I := I) g₀ 0).toSection y) (w y))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (ricciModelTrace42Field (I := I) g₀ 0).toSection.contMDiff w.contMDiff
    -- the comparison section
    set Q : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 2 ℝ E,
        (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y)⟯ :=
      (-2 : ℝ) • ∑ i : Fin (Module.finrank ℝ E), ti i with hQ_def
    have hQ_coe : ∀ y : M, Q y = (-2 : ℝ) • ∑ i : Fin (Module.finrank ℝ E), ti i y := by
      intro y
      rw [hQ_def]
      rw [show ((-2 : ℝ) • ∑ i : Fin (Module.finrank ℝ E), ti i :
          Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 2 ℝ E,
            (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)⟯) y =
        (-2 : ℝ) • ((∑ i : Fin (Module.finrank ℝ E), ti i :
          Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 2 ℝ E,
            (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)⟯) y) from rfl]
      rw [ContMDiffSection.finset_sum_apply]
    -- near `x` the traced section agrees with the frame diagonal sum
    have hagree : ∀ᶠ y in nhds x,
        (show Tensor0SBundle.Tensor0SSpace 4 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
          (ricciModelTrace42Field (I := I) g₀ 0).toSection y) (w y) = Q y := by
      filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x] with y hy
      rw [hQ_coe y]
      rw [show (show Tensor0SBundle.Tensor0SSpace 4 I y →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I y from
          (ricciModelTrace42Field (I := I) g₀ 0).toSection y) (w y) =
        ricciModelTrace42Fib (I := I) g₀ 0 y (w y) from rfl]
      rw [ricciModelTrace42Fib_eq_orthoFrame_diag (I := I) g₀ x hy (w y)]
      rfl
    -- locality, scalar, and finite-sum additivity
    have hcongr := (Tensor0SNabla.tensor0SCovariantDerivative I M 2
        (LeviCivita (I := I) g₀)).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (σ := fun y : M =>
        (show Tensor0SBundle.Tensor0SSpace 4 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
          (ricciModelTrace42Field (I := I) g₀ 0).toSection y) (w y))
      (σ' := fun y : M => Q y) (x := x)
      ((hP_smooth x).mdifferentiableAt (by norm_num))
      ((Q.contMDiff x).mdifferentiableAt (by norm_num)) Filter.univ_mem hagree
    have hsmul := (Tensor0SNabla.tensor0SCovariantDerivative I M 2
        (LeviCivita (I := I) g₀)).isCovariantDerivativeOnUniv.smul_const (x := x) (-2 : ℝ)
      (σ := fun y : M => ∑ i : Fin (Module.finrank ℝ E), ti i y)
      (((∑ i : Fin (Module.finrank ℝ E), ti i :
          Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 2 ℝ E,
            (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)⟯).contMDiff.congr (fun y => by
        rw [ContMDiffSection.finset_sum_apply]) x).mdifferentiableAt (by norm_num))
      (Set.mem_univ x)
    -- assemble: the directional derivative of the traced section
    have hQfun : (fun y : M => Q y) =
        ((-2 : ℝ) • fun y : M => ∑ i : Fin (Module.finrank ℝ E), ti i y) := by
      funext y
      rw [hQ_coe y]
      rfl
    have hfinal : (Tensor0SNabla.tensor0SCovariantDerivative I M 2
          (LeviCivita (I := I) g₀)).toFun
          (fun y : M =>
            (show Tensor0SBundle.Tensor0SSpace 4 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
              (ricciModelTrace42Field (I := I) g₀ 0).toSection y) (w y)) x v =
        (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          (ricciModelTrace42Field (I := I) g₀ 0).toSection x)
          ((Tensor0SNabla.tensor0SCovariantDerivative I M 4
            (LeviCivita (I := I) g₀)).toFun (fun y : M => w y) x v) := by
      calc (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)).toFun
            (fun y : M =>
              (show Tensor0SBundle.Tensor0SSpace 4 I y →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace 2 I y from
                (ricciModelTrace42Field (I := I) g₀ 0).toSection y) (w y)) x v
          = (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)).toFun
              (fun y : M => Q y) x v := by rw [hcongr]
        _ = ((-2 : ℝ) • (Tensor0SNabla.tensor0SCovariantDerivative I M 2
              (LeviCivita (I := I) g₀)).toFun
              (fun y : M => ∑ i : Fin (Module.finrank ℝ E), ti i y) x) v := by
            rw [hQfun, hsmul]
        _ = (-2 : ℝ) • ((Tensor0SNabla.tensor0SCovariantDerivative I M 2
              (LeviCivita (I := I) g₀)).toFun
              (fun y : M => ∑ i : Fin (Module.finrank ℝ E), ti i y) x v) := by
            rw [ContinuousLinearMap.smul_apply]
        _ = (-2 : ℝ) • ((∑ i : Fin (Module.finrank ℝ E),
              (Tensor0SNabla.tensor0SCovariantDerivative I M 2
                (LeviCivita (I := I) g₀)).toFun (fun y : M => ti i y) x) v) := by
            rw [tensor0SCovDeriv_finset_sum (I := I) g₀ 2 Finset.univ ti x]
        _ = (-2 : ℝ) • (∑ i : Fin (Module.finrank ℝ E),
              (Tensor0SNabla.tensor0SCovariantDerivative I M 2
                (LeviCivita (I := I) g₀)).toFun (fun y : M => ti i y) x v) := by
            rw [ContinuousLinearMap.sum_apply]
        _ = (-2 : ℝ) • (∑ i : Fin (Module.finrank ℝ E),
              (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
                  (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x
                    ((Tensor0SNabla.tensor0SCovariantDerivative I M 4
                      (LeviCivita (I := I) g₀)).toFun (fun y : M => w y) x v)
                    (smoothOrthoFrame (I := I) g₀ x i x))
                  (smoothOrthoFrame (I := I) g₀ x i x)
                + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
                    (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x (w x)
                      ((LeviCivita (I := I) g₀).toFun
                        (smoothOrthoFrame (I := I) g₀ x i) x v))
                    (smoothOrthoFrame (I := I) g₀ x i x)
                + Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
                    (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x (w x)
                      (smoothOrthoFrame (I := I) g₀ x i x))
                    ((LeviCivita (I := I) g₀).toFun
                      (smoothOrthoFrame (I := I) g₀ x i) x v))) := by
            refine congrArg (fun z => (-2 : ℝ) • z)
              (Finset.sum_congr rfl fun i _ => ?_)
            exact covDeriv_doubleInsert_leibniz (I := I) g₀ w x i v
        _ = (-2 : ℝ) • (∑ i : Fin (Module.finrank ℝ E),
              Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x
                (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 3 x
                  ((Tensor0SNabla.tensor0SCovariantDerivative I M 4
                    (LeviCivita (I := I) g₀)).toFun (fun y : M => w y) x v)
                  (smoothOrthoFrame (I := I) g₀ x i x))
                (smoothOrthoFrame (I := I) g₀ x i x)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, add_assoc,
              orthoFrame_corrections_sum_eq_zero (I := I) g₀ x v (w x), add_zero]
        _ = (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              (ricciModelTrace42Field (I := I) g₀ 0).toSection x)
              ((Tensor0SNabla.tensor0SCovariantDerivative I M 4
                (LeviCivita (I := I) g₀)).toFun (fun y : M => w y) x v) :=
            (ricciModelTrace42Fib_eq_orthoFrame_diag (I := I) g₀ x
              (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
              ((Tensor0SNabla.tensor0SCovariantDerivative I M 4
                (LeviCivita (I := I) g₀)).toFun (fun y : M => w y) x v)).symm
    exact hfinal
  -- assemble the section-level vanishing from the directional vanishing
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [Integral.L2.SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply,
    Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval
      (I := I) (M := M) g₀ 4 2 (ricciModelTrace42Field (I := I) g₀ 0) x D m,
    hdir x (m 0), ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply]

/-- **The cometric `∇₀`-parallelism core: the passenger-passing `g₀⁻¹` double-trace field is
`∇₀`-parallel.**  The covariant gradient of the passenger-passing intrinsic `g₀⁻¹` double-trace operator
field vanishes:
```
covGrad g₀ (4 + a) (2 + a) (ricciModelTrace42FieldRec g₀ a) = 0.
```

**Decomposition.**  Induction on the gradient-shift `a`.  At `a = 0` the field is the base double trace
`ricciModelTrace42Field g₀ 0`, whose parallelism is the genuine cometric core
`ricciModelTrace42Field_covGrad_eq_zero` (`∇₀ g₀⁻¹ = 0` via `cometric_skew_core`).  At `a + 1` the field
is `slotExtend g₀ (4 + a) (2 + a) (ricciModelTrace42FieldRec g₀ a)`
(`ricciModelTrace42FieldRec_succ`), and the covariant gradient annihilates the slot-extension of the
inductively-parallel field `ricciModelTrace42FieldRec g₀ a`
(`covGrad_slotExtend_eq_zero_of_covGrad_eq_zero`), so the vanishing propagates to every `a`.

**Non-vacuity.**  It asserts the genuine differential-geometric identity that the background cometric is
parallel; false for a non-parallel ambient frame. -/
theorem ricciModelTrace42FieldRec_covGrad_eq_zero (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ (4 + a) (2 + a)
        (ricciModelTrace42FieldRec (I := I) g₀ a) = 0 := by
  induction a with
  | zero =>
    rw [ricciModelTrace42FieldRec_zero]
    exact ricciModelTrace42Field_covGrad_eq_zero (I := I) g₀
  | succ a ih =>
    rw [ricciModelTrace42FieldRec_succ]
    exact covGrad_slotExtend_eq_zero_of_covGrad_eq_zero (I := I) g₀ (4 + a) (2 + a)
      (ricciModelTrace42FieldRec (I := I) g₀ a) ih

/-- **The exact parallel single-step covariant Leibniz of the intrinsic `g₀⁻¹` double trace.**  No
differentiated-operator cross term (the moving-coframe corrections cancel against the cometric
parallelism):
`∇₀(ricciModelTrace42Op a R) = (rank-cast) ricciModelTrace42Op (a+1) (∇₀ R)`, the new gradient slot
carried at the front, rank-cast from `2 + (a + 1)` to `(2 + a) + 1` by `castRankCc_db`.  This is
genuinely TRUE (the contraction is against the `∇₀`-parallel cometric `g₀⁻¹`, NOT a fixed,
non-`∇₀`-parallel ambient basis): the B-rule for the operator-field action splits `∇₀(op a R)` into
the differentiated-field cross term — which VANISHES by the cometric parallelism
`ricciModelTrace42FieldRec_covGrad_eq_zero` — plus the surviving `slotExtend`-of-field action on
`∇₀ R`, and `slotExtend (FieldRec a) = FieldRec (a+1)` advances the gradient-shift. -/
theorem ricciModelTrace42Op_covGrad (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (R : Integral.L2.SmoothCcTensor g₀ 0 (4 + a)) :
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 (2 + a)
        (ricciModelTrace42Op (I := I) g₀ a R) =
      Integral.Connection.castRankCc_db g₀ 0 (by omega : 2 + (a + 1) = (2 + a) + 1)
        (ricciModelTrace42Op (I := I) g₀ (a + 1)
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 (4 + a) R)) := by
  -- The B-rule for the operator-field action splits `∇₀(op a R)` into the differentiated-field cross
  -- term (which VANISHES by the cometric parallelism `covGrad (FieldRec a) = 0`) plus the surviving
  -- `slotExtend`-of-field action on `∇₀ R`; `slotExtend (FieldRec a) = FieldRec (a+1)` advances the
  -- gradient-shift, so the surviving term is exactly `op (a+1) (∇₀ R)` (the rank-cast is the identity,
  -- the rank equality `2 + (a+1) = (2+a)+1` being definitional).
  rw [ricciModelTrace42Op,
    DifferentialGeometry.Integral.Connection.covGrad_appCcRS_eq (I := I) (M := M) g₀ 0 (4 + a) (2 + a)
      (ricciModelTrace42FieldRec (I := I) g₀ a) R,
    ricciModelTrace42FieldRec_covGrad_eq_zero (I := I) g₀ a,
    DifferentialGeometry.Integral.Connection.appCcRS_zero_left (I := I) (M := M) g₀ 0 (4 + a)
      ((2 + a) + 1) R, zero_add]
  -- The surviving term, with `slotExtend (FieldRec a) = FieldRec (a+1)` (definitional) and the rank
  -- casts absorbed: it is `op (a+1) (∇₀ R)`, and the output rank-cast `castRankCc_db` is the identity
  -- on the definitionally-equal ranks.
  rw [← ricciModelTrace42FieldRec_succ (I := I) g₀ a]
  exact (eq_of_heq (Integral.Connection.castRankCc_db_heq g₀ 0
    (by omega : 2 + (a + 1) = (2 + a) + 1)
    (ricciModelTrace42Op (I := I) g₀ (a + 1)
      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 (4 + a) R)))).symm

set_option linter.unusedSectionVars false in
/-- **The post-composition fibre operator applied to `R.toSection x` is the fibre value of
`ricciModelTrace42Op` at `x`.**  For any fibrewise operator `A : (0, 4 + a)-tensor →L (0, 2 + a)-tensor`
that post-composes the passenger-passing `g₀⁻¹` double-trace fibre operator
`(ricciModelTrace42FieldRec g₀ a).toSection x` after the `(0, 4 + a)`-tensor (i.e.
`A v = ((ricciModelTrace42FieldRec g₀ a).toSection x).comp v` on every `(0, 4 + a)`-tensor
`v = Tensor0SSpace 0 →L Tensor0SSpace (4 + a)`), the image `A (R.toSection x)` is the fibre value
`(ricciModelTrace42Op g₀ a R).toSection x` of the operator-field action (`ricciModelTrace42Op_toSection`).
This exhibits the operator-field-action fibre value as a `g₀`-fibre Hom-bundle operator's action, the
bridge feeding the sharp `g`-operator-norm fibre-norm bound. -/
private theorem ricciModelTrace42Op_toSection_eq_postcomp (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (x : M)
    (R : Integral.L2.SmoothCcTensor g₀ 0 (4 + a))
    (A : Tensor0SBundle.TensorRSSpace 0 (4 + a) I x →L[ℝ] Tensor0SBundle.TensorRSSpace 0 (2 + a) I x)
    (hA : ∀ v : Tensor0SBundle.TensorRSSpace 0 (4 + a) I x,
      A v = (show Tensor0SBundle.Tensor0SSpace (4 + a) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a) I x from
        (ricciModelTrace42FieldRec (I := I) g₀ a).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (4 + a) I x from v)) :
    A (R.toSection x) = (ricciModelTrace42Op (I := I) g₀ a R).toSection x := by
  rw [hA (R.toSection x), ricciModelTrace42Op_toSection]

set_option linter.unusedSectionVars false in
/-- **The all-ranks frame witness of the intrinsic fibre norm.**  At a base point `x` there is a
single tangent frame `e` (with `n = finrank` directions, the `g₀(x)`-orthonormal frame internal to
`riemannianFiberNormSq`) representing the intrinsic `(0, s)` fibre norm as the frame double sum at
**every** covariant rank `s` simultaneously.  This is `tangent_orthonormalBasisS_witness` with the
rank quantified inside the existential (the internal construction does not depend on the rank). -/
private theorem rfns_allRanks_frame_witness (g₀ : SmoothRiemannianMetric I M) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      ∀ (s : ℕ) (S : Tensor0SBundle.TensorRSSpace 0 s I x),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x S =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
            Integral.Connection.fiberNormSqSummand (I := I) (M := M) g₀ x 0 s S n e K J := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g₀.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g₀.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g₀.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set eob : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _
    with heob_def
  exact ⟨n, fun i => eob i, rfl, fun s S => rfl⟩

set_option linter.unusedSectionVars false in
/-- **The leading-slot slice of the slot-extended double-trace action is the action on the slice.**
The slot-`0` curry of the slot-extended passenger-passing field's post-composition action, along a
frame direction `e b`, is the one-step-lower field's post-composition action on the slot-`0` curry of
the input (`slotExtendFib` reads the passenger slot first and passes it unchanged). -/
private theorem slot0Curry_fieldRec_postcomp (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (v : Tensor0SBundle.TensorRSSpace 0 (4 + (a + 1)) I x) (b : Fin n) :
    Integral.Connection.slot0Curry (I := I) (M := M) g₀ x (2 + a) e K₀
        ((show Tensor0SBundle.Tensor0SSpace (4 + (a + 1)) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (2 + (a + 1)) I x from
          (ricciModelTrace42FieldRec (I := I) g₀ (a + 1)).toSection x).comp
          (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (4 + (a + 1)) I x from v)) b =
      (show Tensor0SBundle.Tensor0SSpace (4 + a) I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (2 + a) I x from
        (ricciModelTrace42FieldRec (I := I) g₀ a).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (4 + a) I x from
          Integral.Connection.slot0Curry (I := I) (M := M) g₀ x (4 + a) e K₀ v b) := by
  classical
  apply ContinuousLinearMap.ext
  intro τ
  have hLHS : (Integral.Connection.slot0Curry (I := I) (M := M) g₀ x (2 + a) e K₀
        ((show Tensor0SBundle.Tensor0SSpace (4 + (a + 1)) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (2 + (a + 1)) I x from
          (ricciModelTrace42FieldRec (I := I) g₀ (a + 1)).toSection x).comp
          (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (4 + (a + 1)) I x from v)) b :
        Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a) I x) τ =
      Integral.Connection.tensor00Scalar (I := I) (M := M) x τ •
        ((show Tensor0SBundle.Tensor0SSpace (4 + a) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (2 + a) I x from
          (ricciModelTrace42FieldRec (I := I) g₀ a).toSection x)
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (4 + a) x
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (4 + (a + 1)) I x from v)
              ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
                (fun k => g₀.inner x (e (K₀ k)))))
            (e b))) := by
    rw [Integral.Connection.slot0Curry_apply]
    congr 1
  have hRHS : ((show Tensor0SBundle.Tensor0SSpace (4 + a) I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (2 + a) I x from
        (ricciModelTrace42FieldRec (I := I) g₀ a).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (4 + a) I x from
          Integral.Connection.slot0Curry (I := I) (M := M) g₀ x (4 + a) e K₀ v b)) τ =
      Integral.Connection.tensor00Scalar (I := I) (M := M) x τ •
        ((show Tensor0SBundle.Tensor0SSpace (4 + a) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (2 + a) I x from
          (ricciModelTrace42FieldRec (I := I) g₀ a).toSection x)
          (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (4 + a) x
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (4 + (a + 1)) I x from v)
              ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
                (fun k => g₀.inner x (e (K₀ k)))))
            (e b))) := by
    rw [ContinuousLinearMap.comp_apply, Integral.Connection.slot0Curry_apply, map_smul]
    rfl
  exact hLHS.trans hRHS.symm

set_option linter.unusedSectionVars false in
/-- **The order-uniform postcomposition envelope over the passenger-passing recursion.**  From the
base-level (`a = 0`) uniform fibre envelope, the same constant bounds the post-composition action of
the slot-extended field at **every** gradient-shift `a`: by induction, slicing the leading passenger
covariant slot with the all-ranks frame Parseval split
(`riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame`) and passing each slice through
`slot0Curry_fieldRec_postcomp` to the inductive hypothesis — the leading passenger slot is an
isometric ampliation for the intrinsic fibre envelope. -/
private theorem ricciModelTrace42_postcomp_rfns_le_aux (g₀ : SmoothRiemannianMetric I M) (κ₀ : ℝ)
    (hbase : ∀ (x : M) (v : Tensor0SBundle.TensorRSSpace 0 4 I x),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            (ricciModelTrace42FieldRec (I := I) g₀ 0).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 4 I x from v)) ≤
        κ₀ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x v) :
    ∀ (a : ℕ) (x : M) (v : Tensor0SBundle.TensorRSSpace 0 (4 + a) I x),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((show Tensor0SBundle.Tensor0SSpace (4 + a) I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (2 + a) I x from
            (ricciModelTrace42FieldRec (I := I) g₀ a).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (4 + a) I x from v)) ≤
        κ₀ * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + a) x v := by
  intro a
  induction a with
  | zero => exact hbase
  | succ a ih =>
    intro x v
    classical
    obtain ⟨n, e, hn, hrepr⟩ := rfns_allRanks_frame_witness (I := I) g₀ x
    -- slice the action and the input along the leading passenger slot
    have hL : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (a + 1)) x
          ((show Tensor0SBundle.Tensor0SSpace (4 + (a + 1)) I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (2 + (a + 1)) I x from
            (ricciModelTrace42FieldRec (I := I) g₀ (a + 1)).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (4 + (a + 1)) I x from v)) =
        ∑ b : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
            (Integral.Connection.slot0Curry (I := I) (M := M) g₀ x (2 + a) e
              (fun k => k.elim0)
              ((show Tensor0SBundle.Tensor0SSpace (4 + (a + 1)) I x →L[ℝ]
                  Tensor0SBundle.Tensor0SSpace (2 + (a + 1)) I x from
                (ricciModelTrace42FieldRec (I := I) g₀ (a + 1)).toSection x).comp
                (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                    Tensor0SBundle.Tensor0SSpace (4 + (a + 1)) I x from v)) b) :=
      Integral.Connection.riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame
        (I := I) (M := M) g₀ (2 + a) x e (fun k => k.elim0)
        (hrepr (2 + a)) (hrepr (2 + a + 1)) _
    have hR : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + (a + 1)) x v =
        ∑ b : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + a) x
            (Integral.Connection.slot0Curry (I := I) (M := M) g₀ x (4 + a) e
              (fun k => k.elim0) v b) :=
      Integral.Connection.riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame
        (I := I) (M := M) g₀ (4 + a) x e (fun k => k.elim0)
        (hrepr (4 + a)) (hrepr (4 + a + 1)) _
    rw [hL, hR, Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [slot0Curry_fieldRec_postcomp (I := I) g₀ a x e (fun k => k.elim0) v b]
    exact ih x (Integral.Connection.slot0Curry (I := I) (M := M) g₀ x (4 + a) e
      (fun k => k.elim0) v b)

/-- **The post-composition operator of the passenger-passing `g₀⁻¹` double-trace fibre operator**,
as a continuous-linear map on the `(0, 4 + a)`-tensor fibre: `v ↦ (FieldRec g₀ a).toSection x ∘ v`
(post-composition is `ℝ`-linear; closed to a continuous-linear map on the finite-dimensional
fibre). -/
private noncomputable def fieldRecPostcompCLM (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    Tensor0SBundle.TensorRSSpace 0 (4 + a) I x →L[ℝ]
      Tensor0SBundle.TensorRSSpace 0 (2 + a) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SBundle.TensorRSSpace 0 (4 + a) I x) :=
    inferInstanceAs (FiniteDimensional ℝ
      (Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (4 + a) I x))
  haveI : T2Space (Tensor0SBundle.TensorRSSpace 0 (4 + a) I x) :=
    inferInstanceAs (T2Space
      (Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (4 + a) I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun v =>
        (show Tensor0SBundle.Tensor0SSpace (4 + a) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (2 + a) I x from
          (ricciModelTrace42FieldRec (I := I) g₀ a).toSection x).comp
          (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (4 + a) I x from v)
      map_add' := fun _ _ => ContinuousLinearMap.comp_add _ _ _
      map_smul' := fun _ _ => ContinuousLinearMap.comp_smul _ _ _ }

set_option linter.unusedSectionVars false in
/-- Defining evaluation of `fieldRecPostcompCLM`: post-composition by the passenger-passing
double-trace fibre operator. -/
private theorem fieldRecPostcompCLM_apply (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (x : M)
    (v : Tensor0SBundle.TensorRSSpace 0 (4 + a) I x) :
    fieldRecPostcompCLM (I := I) g₀ a x v =
      (show Tensor0SBundle.Tensor0SSpace (4 + a) I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (2 + a) I x from
        (ricciModelTrace42FieldRec (I := I) g₀ a).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (4 + a) I x from v) := by
  haveI : FiniteDimensional ℝ (Tensor0SBundle.TensorRSSpace 0 (4 + a) I x) :=
    inferInstanceAs (FiniteDimensional ℝ
      (Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (4 + a) I x))
  haveI : T2Space (Tensor0SBundle.TensorRSSpace 0 (4 + a) I x) :=
    inferInstanceAs (T2Space
      (Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (4 + a) I x))
  exact congrFun (LinearMap.coe_toContinuousLinearMap' _) v

set_option linter.unusedSectionVars false in
/-- **(POSIT — the order-uniform `g₀`-Riemannian operator-norm-route mixed fibre envelope of the
slot-extended `g₀⁻¹` double trace.)**  There is a single nonnegative `κ₀`, **uniform over the
gradient-shift `a`**, the section `R`, and the base point `x`, together with a fibrewise post-composition
operator `A` (the `g₀`-fibre Hom-bundle operator `v ↦ ((ricciModelTrace42FieldRec g₀ a).toSection x).comp v`,
the passenger-passing `g₀⁻¹` double-trace fibre operator `(FieldRec g₀ a).toSection x = slotExtendᵃ(base x)`)
bounding the intrinsic squared fibre norm of the operator-field action through the **`g`-operator norm** of `A`:
```
rfns_{(0,2+a)}(A v) ≤ κ₀ · rfns_{(0,4+a)}(v),   A v = ((ricciModelTrace42FieldRec g₀ a).toSection x).comp v.
```

This is the genuine deep **`g`-OPERATOR-norm** content (NOT the HS route, which is *not* `a`-uniform: the
HS norm of `slotExtendᵃ` grows by a `dim`-factor per passenger slot).  The post-composition operator's
`g`-operator norm is `≤ ‖(ricciModelTrace42FieldRec g₀ a).toSection x‖_{g-op}` (post-composition
operator-norm submultiplicativity), and the `g`-operator norm of the passenger-passing fibre operator
`(ricciModelTrace42FieldRec g₀ a).toSection x = slotExtendᵃ(base x)` equals that of the fixed base field
`base x` — a leading passenger covariant slot is an **isometric ampliation** for the operator norm (it acts
as the identity in the passenger-`g`-orthonormal directions, independent of the passenger valence `a`); the
base field's `g`-operator norm is the cometric trace `≤ 2·∑ᵢ‖♯eᵢ(x)‖²_g`, uniformly bounded on the compact
`M` by `exists_uniform_cometricBilin_bound`, and the squared fibre-norm bound `rfns(A v) ≤ ‖A‖²·rfns(v)` is
the sharp intrinsic operator-norm fibre-norm bound `homTensorRS_riemannianFiberNormSq_clm_apply_le` (rank
`0`, no dimension factor).  The `g₀`-fibre Hom-bundle post-composition operator `A` is exposed here (rather
than constructed by `compL`) because its `g₀`-fibre normed structure is the installed Riemannian bundle
norm, distinct from the static carrier operator norm `tensorRSSpace_norm_eq_carrier_opNorm`.  It is
**non-vacuous** (a degenerate `κ₀ = 0` is rejected whenever `op a R ≠ 0`); its body is `sorry`: the
order-uniform `g`-operator-norm-route mixed fibre envelope of the slot-extended intrinsic `g₀⁻¹` double
trace. -/
theorem exists_uniform_ricciModelTrace42_postcomp_gOpNorm_rfns_le (g₀ : SmoothRiemannianMetric I M) :
    ∃ κ₀ : ℝ, 0 ≤ κ₀ ∧ ∀ (a : ℕ) (x : M),
      ∃ A : Tensor0SBundle.TensorRSSpace 0 (4 + a) I x →L[ℝ] Tensor0SBundle.TensorRSSpace 0 (2 + a) I x,
        (∀ v : Tensor0SBundle.TensorRSSpace 0 (4 + a) I x,
          A v = (show Tensor0SBundle.Tensor0SSpace (4 + a) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a) I x from
            (ricciModelTrace42FieldRec (I := I) g₀ a).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (4 + a) I x from v)) ∧
        ∀ v : Tensor0SBundle.TensorRSSpace 0 (4 + a) I x,
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (A v) ≤
            κ₀ * Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + a) x v := by
  classical
  obtain ⟨C, hC0, hC⟩ :=
    Integral.Connection.exists_uniform_riemannianFiberNormSq_appCcRS_le (I := I) (M := M)
      g₀ 0 4 2 (ricciModelTrace42FieldRec (I := I) g₀ 0)
  -- the base-level (`a = 0`) fibre-value envelope, from the uniform section envelope through a
  -- smooth section realizing an arbitrary fibre value
  have hbase : ∀ (x : M) (v : Tensor0SBundle.TensorRSSpace 0 4 I x),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            (ricciModelTrace42FieldRec (I := I) g₀ 0).toSection x).comp
            (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 4 I x from v)) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x v := by
    intro x v
    obtain ⟨σ, hσ⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := Tensor0SBundle.TensorRSModel 0 4 ℝ E)
      (V := fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) (n := (⊤ : ℕ∞)) x v
    have hW := hC ⟨σ, HasCompactSupport.of_compactSpace _⟩ x
    rw [Integral.Connection.appCcRS_toSection (I := I) (M := M) g₀ 0 4 2
      (ricciModelTrace42FieldRec (I := I) g₀ 0)
      ⟨σ, HasCompactSupport.of_compactSpace _⟩ x] at hW
    have hW' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I x from
          (ricciModelTrace42FieldRec (I := I) g₀ 0).toSection x).comp
          (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 4 I x from σ x)) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x (σ x) := hW
    rw [hσ] at hW'
    exact hW'
  refine ⟨C, hC0, fun a x => ?_⟩
  refine ⟨fieldRecPostcompCLM (I := I) g₀ a x,
    fun v => fieldRecPostcompCLM_apply (I := I) g₀ a x v, fun v => ?_⟩
  rw [fieldRecPostcompCLM_apply (I := I) g₀ a x v]
  exact ricciModelTrace42_postcomp_rfns_le_aux (I := I) g₀ C hbase a x v

set_option linter.unusedSectionVars false in
/-- **The order-uniform mixed `g₀`-operator-norm fibre envelope of the intrinsic `g₀⁻¹` double trace.**
For the passenger-passing double-trace field there is a single nonnegative `κ₀`, uniform over the
gradient-shift `a`, the section `R`, and the base point `x`, controlling the intrinsic squared fibre norm
of the operator-field action:
```
rfns_{(0,2+a)}((ricciModelTrace42Op g₀ a R).toSection x) ≤ κ₀ · rfns_{(0,4+a)}(R)(x).
```

**Decomposition.**  By the order-uniform `g`-operator-norm-route envelope
`exists_uniform_ricciModelTrace42_postcomp_gOpNorm_rfns_le` there is a single `κ₀` and, at each `(a, x)`, a
post-composition fibre operator `A` (acting as `v ↦ (ricciModelTrace42Fib g₀ a x).comp v`) with
`rfns(A v) ≤ κ₀ · rfns(v)` (the `g`-operator-norm route, the slot-extension being an isometric ampliation
of the cometric-bounded base operator — crucially *a*-uniform, unlike the HS bound `compRS_le_mul` whose
norm grows by a `dim`-factor per passenger slot).  The fibre value `(ricciModelTrace42Op g₀ a R).toSection x`
is exactly `A (R.toSection x)` (`ricciModelTrace42Op_toSection_eq_postcomp`), so the envelope applied at
`v = R.toSection x` is the claim.  It is **non-vacuous** (a degenerate `κ₀ = 0` is rejected whenever
`op a R ≠ 0`). -/
theorem exists_uniform_ricciModelTrace42Op_rfns_le (g₀ : SmoothRiemannianMetric I M) :
    ∃ κ₀ : ℝ, 0 ≤ κ₀ ∧ ∀ (a : ℕ) (R : Integral.L2.SmoothCcTensor g₀ 0 (4 + a)) (x : M),
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((ricciModelTrace42Op (I := I) g₀ a R).toSection x) ≤
        κ₀ * Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + a) x
          (R.toSection x) := by
  obtain ⟨κ₀, hκ₀0, hκ₀⟩ := exists_uniform_ricciModelTrace42_postcomp_gOpNorm_rfns_le (I := I) g₀
  refine ⟨κ₀, hκ₀0, fun a R x => ?_⟩
  obtain ⟨A, hAdef, hAbound⟩ := hκ₀ a x
  -- The fibre value is the post-composition operator `A` applied to `R.toSection x`.
  rw [← ricciModelTrace42Op_toSection_eq_postcomp (I := I) g₀ a x R A hAdef]
  exact hAbound (R.toSection x)

/-- **The `(0, 4) → (0, 2)` intrinsic `g₀⁻¹` double-trace parallel contraction.**  The parallel
rank-reducing single-section contraction realising the `−2` cometric double trace `g₀^{ij}·` of the
two leading covariant slots on the once-`∇₀`-differentiated rank-`4` Koszul operand, a
`ParallelRankReducingContraction g₀ 4 2`, assembled from its four genuinely-deep fields: the
section-level intrinsic `g₀⁻¹` double trace `ricciModelTrace42Op` (contracting the leading two
covariant slots against the cometric `g₀⁻¹`, NOT a chart-selected ambient basis), its exact parallel
single-step covariant Leibniz `ricciModelTrace42Op_covGrad` (the cometric parallelism `∇₀ g₀⁻¹ = 0`
via `cometric_skew_core`, carried through `castRankCc_db`), the order-uniform envelope constant `κ₀`
(the squared uniform cometric trace, `exists_uniform_ricciModelTrace42Op_rfns_le`), and its
single-value fibre envelope (value-locality of the trace).

This single-pattern contraction is a **divergence-type** trace, not by itself the linearized-Ricci
trace: the Ricci pattern is the `½`-scaled antisymmetrised combination of its two slot-permuted
images (`ricciAntisymTrace42`, `linearSection_eq_ricciModelTrace42_loweredConnDiffSub`).  The
contraction is **genuine** (non-degenerate): its envelope `kappa = κ₀ ≥ 0` is the value-local bound
genuinely using the section. -/
noncomputable def ricciModelTrace42 (g₀ : SmoothRiemannianMetric I M) :
    Integral.Connection.ParallelRankReducingContraction (I := I) (M := M) g₀ 4 2 where
  op := fun a => ricciModelTrace42Op (I := I) g₀ a
  covGrad_op := fun a R => ricciModelTrace42Op_covGrad (I := I) g₀ a R
  kappa := (exists_uniform_ricciModelTrace42Op_rfns_le (I := I) g₀).choose
  kappa_nonneg := (exists_uniform_ricciModelTrace42Op_rfns_le (I := I) g₀).choose_spec.1
  rfns_op_le := fun a R x =>
    (exists_uniform_ricciModelTrace42Op_rfns_le (I := I) g₀).choose_spec.2 a R x

set_option linter.unusedSectionVars false in
/-- **Fibrewise `ℝ`-linearity of the intrinsic `g₀⁻¹` double trace.**  The `op` of the `(0, 4) → (0, 2)`
intrinsic `g₀⁻¹` double-trace contraction `ricciModelTrace42` distributes over a section difference (it
is fibrewise `ℝ`-linear: a metric contraction is linear in the contracted section).  This is the
assembled instance's `op` unfolding to `ricciModelTrace42Op`, whose additivity is
`ricciModelTrace42Op_sub`. -/
theorem ricciModelTrace42_op_sub (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (A B : Integral.L2.SmoothCcTensor g₀ 0 (4 + a)) :
    (ricciModelTrace42 (I := I) g₀).op a (A - B) =
      (ricciModelTrace42 (I := I) g₀).op a A - (ricciModelTrace42 (I := I) g₀).op a B :=
  ricciModelTrace42Op_sub (I := I) g₀ a A B

set_option linter.unusedSectionVars false in
/-- **The single-step covariant gradient distributes over a section difference.**  `covGrad g₀ 0 s` is
`ℝ`-linear (`covGrad_add`, `covGrad_smul`), hence subtractive.  Local re-statement (the single-step
`covGrad_sub` is not on disk; the *iterated* `iteratedCovGrad_sub` is). -/
private theorem covGrad_sub_local (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : Integral.L2.SmoothCcTensor g₀ 0 s) :
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s (A - B) =
      Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s A
        - Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s B := by
  rw [sub_eq_add_neg, Analysis.Parabolic.TensorSpectral.covGrad_add,
    show (-B) = (-1 : ℝ) • B by rw [neg_one_smul],
    Analysis.Parabolic.TensorSpectral.covGrad_smul, neg_one_smul, ← sub_eq_add_neg]

set_option linter.unusedSectionVars false in
/-- **The model interior product reads its vector into the leading slot.**  `model_interior_product s v T`
evaluated on a `Fin s`-tuple `m` is `T` evaluated on `Fin.cons v m` (the vector `v` prepended into the
leading slot).  Definitional through the left-currying equivalence `continuousMultilinearCurryLeftEquiv`
and `ContinuousLinearMap.apply`. -/
private theorem model_interior_product_apply_eval (s : ℕ) (v : E)
    (T : Tensor0SBundle.Tensor0SModel (s + 1) ℝ E) (m : Fin s → E) :
    Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s v T m = T (Fin.cons v m) := rfl

set_option linter.unusedSectionVars false in
/-- **(The cometric double-trace unit evaluation of the base `g₀⁻¹` double trace.)**  At the unit
`(0, 0)`-tensor and a tangent pair `(v, w)`, the model fibre value of the base intrinsic `g₀⁻¹` double
trace `ricciModelTrace42Op g₀ 0 D` of a `(0, 4)`-tensor `D` is the `−2`-scaled genuine cometric double
trace — the two leading covariant slots of `D` contracted against the cometric `g₀⁻¹` via the FRAME-FREE
natural trace (raise slot `0` by `♯`, contract against the dual model basis):
```
toModel((ricciModelTrace42Op g₀ 0 D).toSection x (unit))![v, w]
  = −2 · ∑ₖ toModel(D.toSection x (unit)) (Fin.cons (♯b^k) (Fin.cons b_k ![v, w])),
```
with `b_k := finBasis k`, `b^k := cDualBasis k`, `♯ := cometricLmodel g₀ x`.  This is the unit-evaluated
form of the operator-field action fibre value `ricciModelTrace42Op_toSection`
(`(op 0 D).toSection x = (ricciModelTrace42Field g₀ 0).toSection x ∘ D.toSection x`) read through
`ricciModelTrace42Fib_toModel` and the defining evaluation `modelDoubleTrace_apply` (with `m := ![v, w]`).
It is **non-vacuous** (a zero right-hand side forces the cometric trace to vanish, false for a nonzero
`D` on the cometric). -/
theorem ricciModelTrace42Op_zero_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (D : Integral.L2.SmoothCcTensor g₀ 0 4) (x : M) (v w : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((ricciModelTrace42Op (I := I) g₀ 0 D).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] =
      (-2 : ℝ) * ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
          ((D.toSection x) (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          (Fin.cons (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) ![(v : E), (w : E)])) := by
  classical
  -- `(op 0 D).toSection x (unit) = (ricciModelTrace42Field g₀ 0).toSection x (D.toSection x (unit))`.
  rw [ricciModelTrace42Op_toSection, ricciModelTrace42FieldRec_zero, ContinuousLinearMap.comp_apply,
    ricciModelTrace42Field_toSection]
  -- Read through `ricciModelTrace42Fib_toModel` (the `−2 • modelDoubleTrace` model image) and the
  -- defining evaluation `modelDoubleTrace_apply` at `m := ![v, w]`.  At `a = 0` the `4 = 2 + 2` rank
  -- cast is the identity reindex (concrete naturals), so `modelRankCast _ (toModel D) = toModel D`.
  rw [ricciModelTrace42Fib_toModel, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [show (modelRankCast (E := E) (by omega : (4 : ℕ) + 0 = (2 + 0) + 2)
        (Tensor0SBundle.Tensor0SSpace.toModel
          ((D.toSection x) (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))))) =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((D.toSection x) (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) from rfl]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₀ x)
      (Tensor0SBundle.Tensor0SSpace.toModel
        ((D.toSection x) (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))) ![(v : E), (w : E)]]

set_option linter.unusedSectionVars false in
/-- **Unit-model evaluation of the once-`∇₀`-differentiated lowered connection-difference
difference.**  For tangent vectors `(u, a, b, c)` with `u` read into the leading (gradient) slot,
the `(0, 4)` unit model of `∇₀(2·lowered₁ − 2·lowered₂)` is the `g₀`-pairing of the per-metric
covariantly differentiated connection differences:
`T(u, a, b, c) = 2·g₀((∇₀_u D₁)(a, b), c) − 2·g₀((∇₀_u D₂)(a, b), c)`, by the covariant-gradient
leading-slot reading (`covGrad_toSection_apply_eval`), `ℝ`-linearity of the directional covariant
derivative in the section (`tensorCovDerivAt_add`/`tensorCovDerivAt_smul`), and the order-one
lowered-difference bridge `tensorCovDerivAt_loweredConnDiffSection_unitModel_eq` per metric arm. -/
private theorem covGradLoweredSub_unitModel_eval
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) (u a b c : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
            ((2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₁ g₀
              - (2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₂ g₀)).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
        (Fin.cons ((u : TangentSpace I x) : E)
          ![((a : TangentSpace I x) : E), ((b : TangentSpace I x) : E),
            ((c : TangentSpace I x) : E)]) =
      2 * g₀.inner x
          (covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
            (smoothExtensionTangent (I := I) x u) (smoothExtensionTangent (I := I) x a)
            (smoothExtensionTangent (I := I) x b) x) c
        - 2 * g₀.inner x
          (covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₂)
            (smoothExtensionTangent (I := I) x u) (smoothExtensionTangent (I := I) x a)
            (smoothExtensionTangent (I := I) x b) x) c := by
  classical
  rw [Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 3
    ((2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₁ g₀
      - (2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₂ g₀) x
    (ContinuousMultilinearMap.constOfIsEmpty ℝ
      (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
    (Fin.cons ((u : TangentSpace I x) : E)
      ![((a : TangentSpace I x) : E), ((b : TangentSpace I x) : E),
        ((c : TangentSpace I x) : E)])]
  have h0 : (Fin.cons ((u : TangentSpace I x) : E)
      ![((a : TangentSpace I x) : E), ((b : TangentSpace I x) : E),
        ((c : TangentSpace I x) : E)] : Fin 4 → TangentSpace I x) 0 = u := rfl
  have htail : Matrix.vecTail (Fin.cons ((u : TangentSpace I x) : E)
      ![((a : TangentSpace I x) : E), ((b : TangentSpace I x) : E),
        ((c : TangentSpace I x) : E)] : Fin 4 → TangentSpace I x) =
      ![((a : TangentSpace I x) : E), ((b : TangentSpace I x) : E),
        ((c : TangentSpace I x) : E)] :=
    Matrix.tail_cons _ _
  rw [h0, htail]
  have hsplit : Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ 0 3
        ((2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₁ g₀
          - (2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₂ g₀) x (u : E) =
      (2 : ℝ) • Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ 0 3
          (DeTurck.loweredConnDiffSection (I := I) g₁ g₀) x (u : E)
        + (-2 : ℝ) • Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ 0 3
          (DeTurck.loweredConnDiffSection (I := I) g₂ g₀) x (u : E) := by
    rw [show ((2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₁ g₀
          - (2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₂ g₀) =
        ((2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₁ g₀
          + (-2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₂ g₀) from by
      rw [sub_eq_add_neg, ← neg_smul]]
    rw [Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_add (I := I) (M := M) g₀ 0 3,
      Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_smul (I := I) (M := M) g₀ 0 3,
      Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_smul (I := I) (M := M) g₀ 0 3]
  rw [hsplit]
  have hdist : Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
        (2 : ℝ) • Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ 0 3
            (DeTurck.loweredConnDiffSection (I := I) g₁ g₀) x (u : E)
          + (-2 : ℝ) • Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ 0 3
            (DeTurck.loweredConnDiffSection (I := I) g₂ g₀) x (u : E))
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
      ![((a : TangentSpace I x) : E), ((b : TangentSpace I x) : E),
        ((c : TangentSpace I x) : E)] =
      2 * Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
            Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ 0 3
              (DeTurck.loweredConnDiffSection (I := I) g₁ g₀) x (u : E))
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          ![((a : TangentSpace I x) : E), ((b : TangentSpace I x) : E),
            ((c : TangentSpace I x) : E)]
        + (-2) * Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
            Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ 0 3
              (DeTurck.loweredConnDiffSection (I := I) g₂ g₀) x (u : E))
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          ![((a : TangentSpace I x) : E), ((b : TangentSpace I x) : E),
            ((c : TangentSpace I x) : E)] := rfl
  rw [hdist]
  rw [DeTurck.tensorCovDerivAt_loweredConnDiffSection_unitModel_eq (I := I) g₁ g₀ x u a b c,
    DeTurck.tensorCovDerivAt_loweredConnDiffSection_unitModel_eq (I := I) g₂ g₀ x u a b c]
  ring

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **The antisymmetrised cometric raised-coframe two-pattern trace of the once-differentiated
lowered connection difference equals the model-basis linear order term.**  The genuine scalar value
identity beneath the trace bridge: with `T := toModel(∇₀(2·lowered₁ − 2·lowered₂) x (unit))` the
`(0, 4)` unit model of the once-`∇₀`-differentiated `g₀`-lowered connection-difference difference,
the `−1`-scaled **antisymmetrised two-pattern** cometric raised-coframe trace — the gradient slot
paired against the output slot, minus the connection-difference direction slot paired against the
output slot —
```
(−1) · (∑ₖ T(♯b^k, v, w, b_k) − ∑ₖ T(v, ♯b^k, w, b_k)) = ricciNeg2SectionDiffLinearEval g₀ g₁ g₂ x v w
```
equals the linear-in-difference order-zero term (`= −2 ∑ᵢ repr(linearSummand₁ − linearSummand₂)ᵢ`).
This is the linearized-Ricci contracted-Bianchi pattern `∇_i δΓ^i_{vw} − ∇_v δΓ^i_{iw}`: the
single-pattern `(0,1)`-slot double trace is *not* this combination (it is false on a flat conformal
torus); the antisymmetrised two-pattern combination is.

**Proof.**  Per metric arm the unit model is the `g₀`-pairing of the covariantly differentiated
connection difference (`covGradLoweredSub_unitModel_eval`, over the order-one bridge
`tensorCovDerivAt_loweredConnDiffSection_unitModel_eq`).  The first pattern reads the raised coframe
through the *direction* slot only, packaged by the direction-linear `covDerivDiffDirCLM`; the second
reads it through a *multilinear* slot, packaged by the cometric-sharped continuous-bilinear slice of
`T` (NOT by extension-linearity — the smooth extension is choice-based and not linear in its seed),
identified against the chart basis through the `♯∘♭` roundtrip (`metricFlatLinear_injective`).  Both
arms convert to the model-basis coordinate trace by the dual-pair conversion
`sum_inner_dualPair_apply_eq_sum_chartBasis_repr` over the inverse property
`cometricLmodel_dualBasis_inner`, landing exactly on the two `ricciDiffLinearSummand` pieces.  It is
**non-vacuous** (it vanishes at `g₁ = g₂` consistently with `ricciNeg2SectionDiffLinearEval_self`). -/
theorem cometricRaisedTrace_covGradLoweredSub_eq_ricciNeg2SectionDiffLinearEval
    (g₀ : SmoothRiemannianMetric I M) (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (hr1 : ∀ (x : M) (v w : TangentSpace I x),
      g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w)
    (hr2 : ∀ (x : M) (v w : TangentSpace I x),
      g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w)
    (x : M) (v w : TangentSpace I x) :
    (-1 : ℝ) *
      ((∑ k : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel
            ((Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
                ((2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₁ g₀
                  - (2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₂ g₀)).toSection x
              (ContinuousMultilinearMap.constOfIsEmpty ℝ
                (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
            (Fin.cons (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ![((v : TangentSpace I x) : E), ((w : TangentSpace I x) : E),
                (((Module.finBasis ℝ E) k : TangentSpace I x) : E)]))
        - ∑ k : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel
            ((Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
                ((2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₁ g₀
                  - (2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₂ g₀)).toSection x
              (ContinuousMultilinearMap.constOfIsEmpty ℝ
                (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
            (Fin.cons ((v : TangentSpace I x) : E)
              ![(cometricLmodel (I := I) g₀ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)) : E),
                ((w : TangentSpace I x) : E),
                (((Module.finBasis ℝ E) k : TangentSpace I x) : E)])) =
      ricciNeg2SectionDiffLinearEval (I := I) g₀ g₁ g₂ x v w := by
  classical
  set Tm : Tensor0SBundle.Tensor0SModel 4 ℝ E :=
    Tensor0SBundle.Tensor0SSpace.toModel
      ((Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
          ((2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₁ g₀
            - (2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₂ g₀)).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) with hTm
  have hTval : ∀ u a b c : TangentSpace I x,
      Tm (Fin.cons ((u : TangentSpace I x) : E)
          ![((a : TangentSpace I x) : E), ((b : TangentSpace I x) : E),
            ((c : TangentSpace I x) : E)]) =
        2 * g₀.inner x
            (covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
              (smoothExtensionTangent (I := I) x u) (smoothExtensionTangent (I := I) x a)
              (smoothExtensionTangent (I := I) x b) x) c
          - 2 * g₀.inner x
            (covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₂)
              (smoothExtensionTangent (I := I) x u) (smoothExtensionTangent (I := I) x a)
              (smoothExtensionTangent (I := I) x b) x) c :=
    fun u a b c => covGradLoweredSub_unitModel_eval (I := I) g₀ g₁ g₂ x u a b c
  set F1 : TangentSpace I x →L[ℝ] TangentSpace I x :=
    (2 : ℝ) • covDerivDiffDirCLM (I := I)
        (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (smoothExtensionTangent (I := I) x v) (smoothExtensionTangent (I := I) x w) x
      - (2 : ℝ) • covDerivDiffDirCLM (I := I)
        (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₂)
        (smoothExtensionTangent (I := I) x v) (smoothExtensionTangent (I := I) x w) x with hF1
  have hDir : ∀ (gk : SmoothRiemannianMetric I M) (p : TangentSpace I x),
      covDerivDiffDirCLM (I := I) (LeviCivita (I := I) g₀) (LeviCivita (I := I) gk)
          (smoothExtensionTangent (I := I) x v) (smoothExtensionTangent (I := I) x w) x p =
        covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) gk)
          (smoothExtensionTangent (I := I) x p)
          (smoothExtensionTangent (I := I) x v) (smoothExtensionTangent (I := I) x w) x := by
    intro gk p
    conv_lhs => rw [show p = smoothExtensionTangent (I := I) x p x from
      (smoothExtensionTangent_eq (I := I) x p).symm]
    exact covDerivDiffDirCLM_apply (I := I)
      (LeviCivita (I := I) g₀) (LeviCivita (I := I) gk)
      (smoothExtensionTangent (I := I) x p)
      (smoothExtensionTangent (I := I) x v) (smoothExtensionTangent (I := I) x w) x
  have hF1val : ∀ p : TangentSpace I x,
      F1 p = (2 : ℝ) • covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
            (smoothExtensionTangent (I := I) x p)
            (smoothExtensionTangent (I := I) x v) (smoothExtensionTangent (I := I) x w) x
          - (2 : ℝ) • covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₂)
            (smoothExtensionTangent (I := I) x p)
            (smoothExtensionTangent (I := I) x v) (smoothExtensionTangent (I := I) x w) x := by
    intro p
    rw [hF1, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, hDir g₁ p, hDir g₂ p]
  set ψ : E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E :=
    (Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) 1 ((w : TangentSpace I x) : E)).comp
      ((Tensor0SBundle.model_interior_bilinear ℝ E 2).flip
        (Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) 3
          ((v : TangentSpace I x) : E) Tm)) with hψ
  set F2 : TangentSpace I x →L[ℝ] TangentSpace I x :=
    (inverseMetricSharpFib (I := I) g₀ x).comp
      ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1
          x).symm.toContinuousLinearMap.comp
        (show TangentSpace I x →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E from ψ)) with hF2
  have hF2pair : ∀ (p r : TangentSpace I x),
      g₀.inner x (F2 p) r = Tm (Fin.cons ((v : TangentSpace I x) : E)
        ![(p : E), ((w : TangentSpace I x) : E), (r : E)]) := by
    intro p r
    have h1 : F2 p = inverseMetricSharpFib (I := I) g₀ x
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm
          (ψ p)) := rfl
    rw [h1, inverseMetricSharpFib_inner (I := I) g₀ x _ r, cotangentToDualLinear_apply,
      cotangentToDual_apply]
    have h2 : (((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm
          (ψ p)) (fun _ : Fin 1 => r) : ℝ) = ψ p (fun _ : Fin 1 => (r : E)) := rfl
    rw [h2]
    have h3 : ψ p (fun _ : Fin 1 => (r : E)) =
        Tm (Fin.cons ((v : TangentSpace I x) : E)
          (Fin.cons (p : E) (Fin.cons ((w : TangentSpace I x) : E)
            (fun _ : Fin 1 => (r : E))))) := rfl
    rw [h3]
    congr 1
    funext j
    fin_cases j <;> rfl
  have harm1 : ∀ k : Fin (Module.finrank ℝ E),
      Tm (Fin.cons (cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ![((v : TangentSpace I x) : E), ((w : TangentSpace I x) : E),
            (((Module.finBasis ℝ E) k : TangentSpace I x) : E)]) =
        g₀.inner x (F1 (cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))))
          ((Module.finBasis ℝ E) k) := by
    intro k
    rw [hTval (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) v w ((Module.finBasis ℝ E) k)]
    rw [hF1val (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)))]
    rw [map_sub, map_smul, map_smul, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  have harm2 : ∀ k : Fin (Module.finrank ℝ E),
      Tm (Fin.cons ((v : TangentSpace I x) : E)
          ![(cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)) : E),
            ((w : TangentSpace I x) : E),
            (((Module.finBasis ℝ E) k : TangentSpace I x) : E)]) =
        g₀.inner x (F2 (cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))))
          ((Module.finBasis ℝ E) k) :=
    fun k => (hF2pair (cometricLmodel (I := I) g₀ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k))) ((Module.finBasis ℝ E) k)).symm
  have hP : ∀ (k : Fin (Module.finrank ℝ E)) (u : TangentSpace I x),
      g₀.inner x (cometricLmodel (I := I) g₀ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) u =
        (Module.finBasis ℝ E).repr (u : E) k :=
    fun k u => cometricLmodel_dualBasis_inner (I := I) g₀ x k u
  have htrace1 := sum_inner_dualPair_apply_eq_sum_chartBasis_repr (I := I) (M := M) g₀ x
    (fun k => cometricLmodel (I := I) g₀ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k))) hP F1
  have htrace2 := sum_inner_dualPair_apply_eq_sum_chartBasis_repr (I := I) (M := M) g₀ x
    (fun k => cometricLmodel (I := I) g₀ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k))) hP F2
  have hF2val : ∀ i : Fin (Module.finrank ℝ E),
      F2 ((chartModelBasis E) i) =
        (2 : ℝ) • covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x w) x
          - (2 : ℝ) • covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₂)
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x w) x := by
    intro i
    refine Integral.DivergenceTheorem.metricFlatLinear_injective (I := I) g₀ x ?_
    ext r
    rw [Integral.DivergenceTheorem.metricFlatLinear_apply,
      Integral.DivergenceTheorem.metricFlatLinear_apply]
    rw [hF2pair ((chartModelBasis E) i) r]
    rw [hTval v ((chartModelBasis E) i) w r]
    rw [map_sub, map_smul, map_smul, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  have hfinal : ∀ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr (F1 ((chartModelBasis E) i)) i
        - (chartModelBasis E).repr (F2 ((chartModelBasis E) i)) i =
      2 * (chartModelBasis E).repr
        (ricciDiffLinearSummand (I := I) g₀ g₁ x v w i
          - ricciDiffLinearSummand (I := I) g₀ g₂ x v w i) i := by
    intro i
    rw [hF1val ((chartModelBasis E) i), hF2val i]
    rw [← Finsupp.sub_apply, ← map_sub]
    rw [show ((2 : ℝ) • covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x v) (smoothExtensionTangent (I := I) x w) x
          - (2 : ℝ) • covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₂)
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x v) (smoothExtensionTangent (I := I) x w) x)
        - ((2 : ℝ) • covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x w) x
          - (2 : ℝ) • covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₂)
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x w) x) =
        (2 : ℝ) • (ricciDiffLinearSummand (I := I) g₀ g₁ x v w i
          - ricciDiffLinearSummand (I := I) g₀ g₂ x v w i) from by
      unfold ricciDiffLinearSummand
      rw [smul_sub, smul_sub, smul_sub]
      abel]
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun k _ => harm1 k), Finset.sum_congr rfl (fun k _ => harm2 k),
    htrace1, htrace2, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun i _ => hfinal i), ← Finset.mul_sum]
  unfold ricciNeg2SectionDiffLinearEval
  ring

set_option linter.unusedSectionVars false in
/-- **Reading a four-slot tuple through the cycle `(1 2 3)`.**  The `domDomCongr`-composed tuple of
`(y₀, y₁, y₂, y₃)` along `c[1, 2, 3]` is `(y₀, y₂, y₃, y₁)`: the leading slot is fixed and slot `1`
is sent to the trailing position — the first (gradient-against-output) trace pattern. -/
private theorem consTuple_read_cycle123 (y₀ y₁ y₂ y₃ : E) :
    (fun j => (Fin.cons y₀ (Fin.cons y₁ ![y₂, y₃]) : Fin 4 → E)
        ((c[(1 : Fin 4), 2, 3] : Equiv.Perm (Fin 4)) j)) =
      Fin.cons y₀ ![y₂, y₃, y₁] := by
  funext j
  fin_cases j <;> rfl

set_option linter.unusedSectionVars false in
/-- **Reading a four-slot tuple through the cycle `(0 2 3 1)`.**  The `domDomCongr`-composed tuple
of `(y₀, y₁, y₂, y₃)` along `c[0, 2, 3, 1]` is `(y₂, y₀, y₃, y₁)` — the second
(difference-direction-against-output) trace pattern. -/
private theorem consTuple_read_cycle0231 (y₀ y₁ y₂ y₃ : E) :
    (fun j => (Fin.cons y₀ (Fin.cons y₁ ![y₂, y₃]) : Fin 4 → E)
        ((c[(0 : Fin 4), 2, 3, 1] : Equiv.Perm (Fin 4)) j)) =
      Fin.cons y₂ ![y₀, y₃, y₁] := by
  funext j
  fin_cases j <;> rfl

/-- **The linearized-Ricci principal-part value identity, the irreducible trace bridge.**  The
linear-in-difference curvature section `linearSection g₀ g₁ g₂` is the `½`-scaled **antisymmetrised
slot-permuted pair** of `−2` cometric double traces `ricciModelTrace42.op 0` of the
**once-`∇₀`-differentiated** `g₀`-lowered connection-difference *difference*
`Q := ∇₀ (2·loweredConnDiffSection g₁ g₀ − 2·loweredConnDiffSection g₂ g₀)`: the double trace of the
`(x₀, x₂, x₃, x₁)`-reading of `Q` (gradient slot against output slot) minus the double trace of the
`(x₂, x₀, x₃, x₁)`-reading (difference-direction slot against output slot).  The single-pattern
`op 0 Q` alone is NOT `linearSection` (false on a flat conformal torus); the antisymmetrised
two-pattern combination is the linearized-Ricci contracted-Bianchi pattern.

**Decomposition.**  By unit-extensionality (`tensor0s_ext_unitZero`) it suffices to match the two
fibre values at the unit `(0, 0)`-tensor and an arbitrary tangent pair.  The left side's fibre value
is the linear order-zero term `ricciNeg2SectionDiffLinearEval` (`linearSection_toModel_apply`).  Each
right-side arm is the `−2` cometric double trace of the slot-permuted operand
(`ricciModelTrace42Op_zero_unitModel_apply`), whose unit model is the `domDomCongr`-reading of `Q`'s
(`permuteCcTensor_unitModel`, `consTuple_read_cycle123`/`consTuple_read_cycle0231`); the
antisymmetrised combination is the proven two-pattern trace identity
`cometricRaisedTrace_covGradLoweredSub_eq_ricciNeg2SectionDiffLinearEval`. -/
theorem linearSection_eq_ricciModelTrace42_loweredConnDiffSub
    (g₀ : SmoothRiemannianMetric I M) (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (hr1 : ∀ (x : M) (v w : TangentSpace I x),
      g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w)
    (hr2 : ∀ (x : M) (v w : TangentSpace I x),
      g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) :
    linearSection (I := I) g₀ g₁ g₂ =
      (2⁻¹ : ℝ) •
        ((ricciModelTrace42 (I := I) g₀).op 0
            (DeTurck.permuteCcTensor (I := I) g₀ c[(1 : Fin 4), 2, 3]
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
                ((2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₁ g₀
                  - (2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₂ g₀)))
          - (ricciModelTrace42 (I := I) g₀).op 0
            (DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 4), 2, 3, 1]
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
                ((2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₁ g₀
                  - (2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₂ g₀)))) := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply DifferentialGeometry.PDE.DeTurck.tensor0s_ext_unitZero (I := I) (M := M) (s := 2)
  -- It suffices to match the two fibre values on an arbitrary tangent pair, at the unit.
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro p
  beta_reduce
  -- The unit `(0,0)`-tensor is the canonical `constOfIsEmpty 1`.
  have hunit : (Integral.Connection.unitZeroSec (I := I) (M := M) x :
        Tensor0SBundle.Tensor0SSpace 0 I x) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := rfl
  rw [hunit]
  -- The pair `(p 0, p 1)`; `![p 0, p 1] = p`.
  have hpair : (![p 0, p 1] : Fin 2 → TangentSpace I x) = p := by
    funext i; fin_cases i <;> rfl
  -- LHS = linear order-zero term `ricciNeg2SectionDiffLinearEval` (the fibre value of `linearSection`).
  rw [← hpair, linearSection_toModel_apply (I := I) g₀ g₁ g₂ x (p 0) (p 1)]
  -- Abbreviate the once-differentiated rank-`4` operand.
  set Q : Integral.L2.SmoothCcTensor g₀ 0 4 :=
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
      ((2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₁ g₀
        - (2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₂ g₀) with hQ
  -- The fibre value of the `½`-scaled difference section (the algebra is definitional).
  have hsmulsub : Tensor0SBundle.Tensor0SSpace.toModel
        ((((2⁻¹ : ℝ) •
          ((ricciModelTrace42 (I := I) g₀).op 0
              (DeTurck.permuteCcTensor (I := I) g₀ c[(1 : Fin 4), 2, 3] Q)
            - (ricciModelTrace42 (I := I) g₀).op 0
              (DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 4), 2, 3, 1] Q))).toSection x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![p 0, p 1] =
      2⁻¹ * (Tensor0SBundle.Tensor0SSpace.toModel
          (((ricciModelTrace42 (I := I) g₀).op 0
              (DeTurck.permuteCcTensor (I := I) g₀ c[(1 : Fin 4), 2, 3] Q)).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![p 0, p 1]
        - Tensor0SBundle.Tensor0SSpace.toModel
          (((ricciModelTrace42 (I := I) g₀).op 0
              (DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 4), 2, 3, 1] Q)).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![p 0, p 1]) := by
    have h1 : (((2⁻¹ : ℝ) •
          ((ricciModelTrace42 (I := I) g₀).op 0
              (DeTurck.permuteCcTensor (I := I) g₀ c[(1 : Fin 4), 2, 3] Q)
            - (ricciModelTrace42 (I := I) g₀).op 0
              (DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 4), 2, 3, 1] Q))).toSection x) =
        (2⁻¹ : ℝ) • (((ricciModelTrace42 (I := I) g₀).op 0
              (DeTurck.permuteCcTensor (I := I) g₀ c[(1 : Fin 4), 2, 3] Q)).toSection x
          - ((ricciModelTrace42 (I := I) g₀).op 0
              (DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 4), 2, 3, 1] Q)).toSection x) := by
      rw [Integral.L2.SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
        Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
    rw [h1]
    rfl
  rw [hsmulsub]
  -- Each arm: the `−2` cometric double trace of the slot-permuted operand.
  rw [show ((ricciModelTrace42 (I := I) g₀).op 0
        (DeTurck.permuteCcTensor (I := I) g₀ c[(1 : Fin 4), 2, 3] Q)) =
      ricciModelTrace42Op (I := I) g₀ 0
        (DeTurck.permuteCcTensor (I := I) g₀ c[(1 : Fin 4), 2, 3] Q) from rfl,
    show ((ricciModelTrace42 (I := I) g₀).op 0
        (DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 4), 2, 3, 1] Q)) =
      ricciModelTrace42Op (I := I) g₀ 0
        (DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 4), 2, 3, 1] Q) from rfl,
    ricciModelTrace42Op_zero_unitModel_apply (I := I) g₀
      (DeTurck.permuteCcTensor (I := I) g₀ c[(1 : Fin 4), 2, 3] Q) x (p 0) (p 1),
    ricciModelTrace42Op_zero_unitModel_apply (I := I) g₀
      (DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 4), 2, 3, 1] Q) x (p 0) (p 1)]
  -- Per index, the permuted unit model reads `Q`'s unit model on the two-pattern tuples.
  have hP1 : Tensor0SBundle.Tensor0SSpace.toModel
        ((DeTurck.permuteCcTensor (I := I) g₀ c[(1 : Fin 4), 2, 3] Q).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) =
      ContinuousMultilinearMap.domDomCongr c[(1 : Fin 4), 2, 3]
        (Tensor0SBundle.Tensor0SSpace.toModel (Q.toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))) :=
    DeTurck.permuteCcTensor_unitModel (I := I) g₀ c[(1 : Fin 4), 2, 3] Q x
  have hP2 : Tensor0SBundle.Tensor0SSpace.toModel
        ((DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 4), 2, 3, 1] Q).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) =
      ContinuousMultilinearMap.domDomCongr c[(0 : Fin 4), 2, 3, 1]
        (Tensor0SBundle.Tensor0SSpace.toModel (Q.toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))) :=
    DeTurck.permuteCcTensor_unitModel (I := I) g₀ c[(0 : Fin 4), 2, 3, 1] Q x
  have harm1C : ∀ k : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ c[(1 : Fin 4), 2, 3] Q).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          (Fin.cons (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) ![(p 0 : E), (p 1 : E)])) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (Q.toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          (Fin.cons (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            ![(p 0 : E), (p 1 : E), ((Module.finBasis ℝ E) k : E)]) := by
    intro k
    rw [hP1, ContinuousMultilinearMap.domDomCongr_apply]
    rw [consTuple_read_cycle123 (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)))
      ((Module.finBasis ℝ E) k) (p 0 : E) (p 1 : E)]
  have harm2C : ∀ k : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 4), 2, 3, 1] Q).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          (Fin.cons (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) ![(p 0 : E), (p 1 : E)])) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (Q.toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          (Fin.cons (p 0 : E)
            ![(cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)) : E),
              (p 1 : E), ((Module.finBasis ℝ E) k : E)]) := by
    intro k
    rw [hP2, ContinuousMultilinearMap.domDomCongr_apply]
    rw [consTuple_read_cycle0231 (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)))
      ((Module.finBasis ℝ E) k) (p 0 : E) (p 1 : E)]
  rw [Finset.sum_congr rfl (fun k _ => harm1C k), Finset.sum_congr rfl (fun k _ => harm2C k)]
  -- The antisymmetrised two-pattern trace identity closes the value match.
  have hleaf := cometricRaisedTrace_covGradLoweredSub_eq_ricciNeg2SectionDiffLinearEval
    (I := I) g₀ T₁ T₂ g₁ g₂ hr1 hr2 x (p 0) (p 1)
  rw [hQ]
  linarith [hleaf]

set_option linter.unusedSectionVars false in
/-- **Slot permutation distributes over a section difference.**  `permuteCcTensor g₀ σ` is a
fibrewise slot reindexing, hence additive: its unit model is the `domDomCongr σ` of the operand's
(`permuteCcTensor_unitModel`), and `domDomCongr` is linear.  Local re-statement at the
`SmoothCcTensor` level (no subtractivity lemma for `permuteCcTensor` is on disk). -/
private theorem permuteCcTensor_sub (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : Integral.L2.SmoothCcTensor g₀ 0 s) :
    DeTurck.permuteCcTensor (I := I) g₀ σ (A - B) =
      DeTurck.permuteCcTensor (I := I) g₀ σ A - DeTurck.permuteCcTensor (I := I) g₀ σ B := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply DifferentialGeometry.PDE.DeTurck.tensor0s_ext_unitZero (I := I) (M := M) (s := s)
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  have hL : Tensor0SBundle.Tensor0SSpace.toModel
        ((DeTurck.permuteCcTensor (I := I) g₀ σ (A - B)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel ((A - B).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ (A - B) x
  have hA : Tensor0SBundle.Tensor0SSpace.toModel
        ((DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel (A.toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ A x
  have hB : Tensor0SBundle.Tensor0SSpace.toModel
        ((DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel (B.toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ B x
  have hsubval : (A - B).toSection x = A.toSection x - B.toSection x := by
    rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  have hsubval' : ((DeTurck.permuteCcTensor (I := I) g₀ σ A
        - DeTurck.permuteCcTensor (I := I) g₀ σ B)).toSection x =
      (DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
        - (DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x := by
    rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  calc Tensor0SBundle.Tensor0SSpace.toModel
        ((DeTurck.permuteCcTensor (I := I) g₀ σ (A - B)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m
      = (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel ((A - B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m := by rw [hL]
    _ = (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SBundle.Tensor0SSpace.toModel (A.toSection x
              (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m
          - (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SBundle.Tensor0SSpace.toModel (B.toSection x
              (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m := by
        rw [hsubval]; rfl
    _ = Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m
          - Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m := by
        rw [hA, hB]
    _ = Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ σ A
            - DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m := by
        rw [hsubval']; rfl

/-- **The linearized-Ricci principal-part value identity for the antisymmetrised slot-permuted
cometric-trace pair.**  The linear-in-difference curvature section `linearSection g₀ g₁ g₂` is the
`½`-scaled antisymmetrised slot-permuted trace pair of the **once-`∇₀`-differentiated**
connection-difference Koszul **difference arm** `∇₀ koszulTripleDiff` minus the same trace pair of
the once-`∇₀`-differentiated **cross arm** `∇₀ crossCorrTripleDiff`.

**Decomposition.**  By the **proven** child-A `loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff`,
`koszulTripleDiff − crossCorrTripleDiff = 2·loweredConnDiffSection g₁ g₀ − 2·loweredConnDiffSection g₂ g₀`
(the `koszulTripleDiff` shape `R + perm₁ R − perm₂ R` is the clean realized combination, and
`crossCorrTripleDiff = 2·crossCorrectionSection g₁ − 2·crossCorrectionSection g₂` is the cross arm).
The two trace pairs re-collect over the section difference by the fibrewise-`ℝ`-linearity
`ricciModelTrace42_op_sub`, the slot-permutation additivity `permuteCcTensor_sub`, and the
covariant-gradient linearity `covGrad_sub_local`, reducing the goal to the irreducible value bridge
`linearSection_eq_ricciModelTrace42_loweredConnDiffSub` (the antisymmetrised trace pair of the
once-differentiated lowered connection-difference difference equals `linearSection`). -/
theorem linearSection_eq_ricciModelTrace42_koszulTriple_sub_crossCorrTriple
    (g₀ : SmoothRiemannianMetric I M) (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (hr1 : ∀ (x : M) (v w : TangentSpace I x),
      g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w)
    (hr2 : ∀ (x : M) (v w : TangentSpace I x),
      g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) :
    linearSection (I := I) g₀ g₁ g₂ =
      (2⁻¹ : ℝ) •
          ((ricciModelTrace42 (I := I) g₀).op 0
              (DeTurck.permuteCcTensor (I := I) g₀ c[(1 : Fin 4), 2, 3]
                (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
                  (koszulTripleDiff (I := I) g₀ T₁ T₂)))
            - (ricciModelTrace42 (I := I) g₀).op 0
              (DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 4), 2, 3, 1]
                (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
                  (koszulTripleDiff (I := I) g₀ T₁ T₂))))
        - (2⁻¹ : ℝ) •
          ((ricciModelTrace42 (I := I) g₀).op 0
              (DeTurck.permuteCcTensor (I := I) g₀ c[(1 : Fin 4), 2, 3]
                (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
                  (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)))
            - (ricciModelTrace42 (I := I) g₀).op 0
              (DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 4), 2, 3, 1]
                (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
                  (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)))) := by
  -- Re-collect the two trace pairs over the section difference (trace linearity, permutation
  -- additivity, and `∇₀`-linearity), reducing to the trace pair of `∇₀ (koszul − cross)`.
  rw [← smul_sub, sub_sub_sub_comm, ← ricciModelTrace42_op_sub, ← ricciModelTrace42_op_sub,
    ← permuteCcTensor_sub, ← permuteCcTensor_sub]
  rw [← covGrad_sub_local (I := I) g₀ 3
    (koszulTripleDiff (I := I) g₀ T₁ T₂) (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)]
  -- Child-A: `koszulTripleDiff − crossCorrTripleDiff = 2·loweredConnDiff g₁ − 2·loweredConnDiff g₂`.
  have hchildA :=
    (DeTurck.loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff
      (I := I) g₀ g₁ g₂ T₁ T₂ hr1 hr2).symm
  rw [koszulTripleDiff, crossCorrTripleDiff] at *
  rw [hchildA]
  -- The irreducible value bridge.
  exact linearSection_eq_ricciModelTrace42_loweredConnDiffSub (I := I) g₀ T₁ T₂ g₁ g₂ hr1 hr2

set_option linter.unusedSectionVars false in
/-- **The covariant gradient commutes with the slot permutation, the new gradient slot fixed at the
front.**  `∇₀ (permuteCcTensor σ R) = permuteCcTensor (decomposeFin.symm (0, σ)) (∇₀ R)`: the
extended permutation fixes the new leading (gradient) slot and shifts `σ` onto the trailing slots.
This is the section-level form of the directional-covariant-derivative slot-permutation naturality
`tensorCovDerivAt_unit_toModel_domDomCongr_of_section` (a constant slot reindexing is a parallel
fibre automorphism), read through the leading-slot covariant-gradient evaluation
`covGrad_toSection_apply_eval` and the unit-model relation `permuteCcTensor_unitModel`. -/
private theorem covGrad_permuteCcTensor (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (R : Integral.L2.SmoothCcTensor g₀ 0 s) :
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s
        (DeTurck.permuteCcTensor (I := I) g₀ σ R) =
      DeTurck.permuteCcTensor (I := I) g₀ (Equiv.Perm.decomposeFin.symm (0, σ))
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s R) := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply DifferentialGeometry.PDE.DeTurck.tensor0s_ext_unitZero (I := I) (M := M) (s := s + 1)
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  rw [Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 s
    (DeTurck.permuteCcTensor (I := I) g₀ σ R) x
    (Integral.Connection.unitZeroSec (I := I) (M := M) x) m]
  have hnat : Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
            Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ 0 s
              (DeTurck.permuteCcTensor (I := I) g₀ σ R) x (m 0))
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
              Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ 0 s R x (m 0))
            (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_unit_toModel_domDomCongr_of_section
      (I := I) (M := M) g₀ s σ R (DeTurck.permuteCcTensor (I := I) g₀ σ R)
      (fun y => DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ R y) x (m 0)
  rw [hnat, ContinuousMultilinearMap.domDomCongr_apply]
  have hR : Tensor0SBundle.Tensor0SSpace.toModel
        ((DeTurck.permuteCcTensor (I := I) g₀ (Equiv.Perm.decomposeFin.symm (0, σ))
            (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s R)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr (Equiv.Perm.decomposeFin.symm (0, σ))
        (Tensor0SBundle.Tensor0SSpace.toModel
          ((Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s R).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    DeTurck.permuteCcTensor_unitModel (I := I) g₀ (Equiv.Perm.decomposeFin.symm (0, σ))
      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 s R) x
  rw [hR, ContinuousMultilinearMap.domDomCongr_apply]
  rw [Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 s
    R x (Integral.Connection.unitZeroSec (I := I) (M := M) x)
    (fun k => m ((Equiv.Perm.decomposeFin.symm (0, σ)) k))]
  rw [Equiv.Perm.decomposeFin_symm_apply_zero]
  have htail : Matrix.vecTail (fun k : Fin (s + 1) =>
        m ((Equiv.Perm.decomposeFin.symm (0, σ)) k)) =
      fun j : Fin s => Matrix.vecTail m (σ j) := by
    funext j
    show m ((Equiv.Perm.decomposeFin.symm (0, σ)) (Fin.succ j)) = m (Fin.succ (σ j))
    rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
  rw [htail]

/-- **The `a`-shifted slot permutation**: fix the `a` accumulated leading gradient-passenger slots
and act by `σ` on the trailing four, built recursively by extending with the identity on each new
leading slot — exactly the extension produced by one covariant gradient
(`covGrad_permuteCcTensor`). -/
private def shiftPerm (σ : Equiv.Perm (Fin 4)) : (a : ℕ) → Equiv.Perm (Fin (4 + a))
  | 0 => σ
  | a + 1 => Equiv.Perm.decomposeFin.symm (0, shiftPerm σ a)

set_option linter.unusedSectionVars false in
/-- The rank-cast `castRankCc_db` is subtractive.  Local re-statement (`castRankCc_db_add` lives in
the curvature tower, not imported here). -/
private theorem castRankCc_db_sub_local (g₀ : SmoothRiemannianMetric I M) {a b : ℕ} (h : a = b)
    (W₁ W₂ : Integral.L2.SmoothCcTensor g₀ 0 a) :
    Integral.Connection.castRankCc_db g₀ 0 h (W₁ - W₂) =
      Integral.Connection.castRankCc_db g₀ 0 h W₁
        - Integral.Connection.castRankCc_db g₀ 0 h W₂ := by
  subst h; rfl

set_option linter.unusedSectionVars false in
/-- The rank-cast `castRankCc_db` is `ℝ`-homogeneous.  Local re-statement. -/
private theorem castRankCc_db_smul_local (g₀ : SmoothRiemannianMetric I M) {a b : ℕ} (h : a = b)
    (c : ℝ) (W : Integral.L2.SmoothCcTensor g₀ 0 a) :
    Integral.Connection.castRankCc_db g₀ 0 h (c • W) =
      c • Integral.Connection.castRankCc_db g₀ 0 h W := by
  subst h; rfl

set_option linter.unusedSectionVars false in
/-- The intrinsic squared fibre norm is `c²`-homogeneous, via the pointwise-inner bridge
`riemannianFiberNormSq_eq_tensorInnerPointwise` and the bilinearity of `tensorInnerPointwise`. -/
private theorem riemannianFiberNormSq_smul_local (g₀ : SmoothRiemannianMetric I M) (n : ℕ) (x : M)
    (c : ℝ) (T : Tensor0SBundle.TensorRSSpace 0 n I x) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 n x (c • T) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 n x T := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 n x (c • T),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 n x T,
    Tensor0SBundle.TensorRSSpace.toModel_smul,
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

/-- **The antisymmetrised slot-permuted cometric-trace pair as a parallel rank-reducing
contraction.**  At gradient-shift `a` the operator is
`op a R := ½·(ricciModelTrace42Op a (perm σ₁ᵃ R) − ricciModelTrace42Op a (perm σ₂ᵃ R))`, with
`σ₁ᵃ, σ₂ᵃ` the `a`-shifted readings `(x₀, x₂, x₃, x₁)` and `(x₂, x₀, x₃, x₁)` of the trailing four
slots (`shiftPerm`).  This is the genuine linearized-Ricci trace pattern (the contracted-Bianchi
antisymmetrisation), realised on top of the parallel cometric double trace:

* the exact parallel covariant Leibniz holds because each constituent commutes with `∇₀` — the
  double trace by the cometric parallelism (`ricciModelTrace42Op_covGrad`) and the slot permutation
  by the constant-reindexing naturality (`covGrad_permuteCcTensor`, which advances `shiftPerm` by
  one, fixing the new gradient slot);
* the single-value fibre envelope holds with the *same* uniform constant `κ₀` as the plain double
  trace: the slot permutations preserve the intrinsic fibre norm
  (`riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor` at order `0`), and the `½`-scaled
  difference is controlled by `2`-subadditivity (`riemannianFiberNormSq_sub_le`) and the
  `c²`-homogeneity (`riemannianFiberNormSq_smul_local`). -/
private noncomputable def ricciAntisymTrace42 (g₀ : SmoothRiemannianMetric I M) :
    Integral.Connection.ParallelRankReducingContraction (I := I) (M := M) g₀ 4 2 where
  op := fun a R =>
    (2⁻¹ : ℝ) •
      (ricciModelTrace42Op (I := I) g₀ a
          (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(1 : Fin 4), 2, 3] a) R)
        - ricciModelTrace42Op (I := I) g₀ a
          (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(0 : Fin 4), 2, 3, 1] a) R))
  covGrad_op := by
    intro a R
    rw [Analysis.Parabolic.TensorSpectral.covGrad_smul (I := I) (M := M) g₀ 0 (2 + a)]
    rw [covGrad_sub_local (I := I) g₀ (2 + a)
      (ricciModelTrace42Op (I := I) g₀ a
        (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(1 : Fin 4), 2, 3] a) R))
      (ricciModelTrace42Op (I := I) g₀ a
        (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(0 : Fin 4), 2, 3, 1] a) R))]
    rw [ricciModelTrace42Op_covGrad (I := I) g₀ a
        (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(1 : Fin 4), 2, 3] a) R),
      ricciModelTrace42Op_covGrad (I := I) g₀ a
        (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(0 : Fin 4), 2, 3, 1] a) R)]
    rw [covGrad_permuteCcTensor (I := I) g₀ (shiftPerm c[(1 : Fin 4), 2, 3] a) R,
      covGrad_permuteCcTensor (I := I) g₀ (shiftPerm c[(0 : Fin 4), 2, 3, 1] a) R]
    rw [← castRankCc_db_sub_local (I := I) g₀ (by omega : 2 + (a + 1) = (2 + a) + 1),
      ← castRankCc_db_smul_local (I := I) g₀ (by omega : 2 + (a + 1) = (2 + a) + 1)]
    rfl
  kappa := (exists_uniform_ricciModelTrace42Op_rfns_le (I := I) g₀).choose
  kappa_nonneg := (exists_uniform_ricciModelTrace42Op_rfns_le (I := I) g₀).choose_spec.1
  rfns_op_le := by
    intro a R x
    have hval : (((2⁻¹ : ℝ) •
          (ricciModelTrace42Op (I := I) g₀ a
              (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(1 : Fin 4), 2, 3] a) R)
            - ricciModelTrace42Op (I := I) g₀ a
              (DeTurck.permuteCcTensor (I := I) g₀
                (shiftPerm c[(0 : Fin 4), 2, 3, 1] a) R))).toSection x) =
        (2⁻¹ : ℝ) • ((ricciModelTrace42Op (I := I) g₀ a
            (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(1 : Fin 4), 2, 3] a) R)).toSection x
          - (ricciModelTrace42Op (I := I) g₀ a
            (DeTurck.permuteCcTensor (I := I) g₀
              (shiftPerm c[(0 : Fin 4), 2, 3, 1] a) R)).toSection x) := by
      rw [Integral.L2.SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
        Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
    rw [hval]
    rw [riemannianFiberNormSq_smul_local (I := I) g₀ (2 + a) x 2⁻¹ _]
    have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 0 (2 + a) x
      ((ricciModelTrace42Op (I := I) g₀ a
        (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(1 : Fin 4), 2, 3] a) R)).toSection x)
      ((ricciModelTrace42Op (I := I) g₀ a
        (DeTurck.permuteCcTensor (I := I) g₀
          (shiftPerm c[(0 : Fin 4), 2, 3, 1] a) R)).toSection x)
    have henv := (exists_uniform_ricciModelTrace42Op_rfns_le (I := I) g₀).choose_spec.2
    have h1 := henv a (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(1 : Fin 4), 2, 3] a) R) x
    have h2 := henv a (DeTurck.permuteCcTensor (I := I) g₀
      (shiftPerm c[(0 : Fin 4), 2, 3, 1] a) R) x
    have hp1 : Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + a) x
        ((DeTurck.permuteCcTensor (I := I) g₀
          (shiftPerm c[(1 : Fin 4), 2, 3] a) R).toSection x) =
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + a) x
          (R.toSection x) := by
      have h := DeTurck.riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) g₀
        (shiftPerm c[(1 : Fin 4), 2, 3] a) R 0 x
      rwa [PDE.RicciFlow.iteratedCovGrad_zero, PDE.RicciFlow.iteratedCovGrad_zero] at h
    have hp2 : Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + a) x
        ((DeTurck.permuteCcTensor (I := I) g₀
          (shiftPerm c[(0 : Fin 4), 2, 3, 1] a) R).toSection x) =
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + a) x
          (R.toSection x) := by
      have h := DeTurck.riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) g₀
        (shiftPerm c[(0 : Fin 4), 2, 3, 1] a) R 0 x
      rwa [PDE.RicciFlow.iteratedCovGrad_zero, PDE.RicciFlow.iteratedCovGrad_zero] at h
    have hκ0 := (exists_uniform_ricciModelTrace42Op_rfns_le (I := I) g₀).choose_spec.1
    nlinarith [h1, h2, hsub, hp1, hp2,
      Integral.Connection.riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + a) x
        (R.toSection x)]

/-- **The linearized-Ricci principal-part section identity: `linearSection` as a parallel
antisymmetrised slot-permuted cometric-trace pair of the *once-covariantly-differentiated*
connection-difference Koszul combination.**  There is a **parallel rank-reducing
`(0, 4) → (0, 2)` contraction** `Φ` (the `½`-scaled antisymmetrised pair of slot-permuted `−2`
cometric double traces `ricciAntisymTrace42` — parallel because `∇₀ g₀⁻¹ = 0` and a constant slot
reindexing is parallel, value-local because it reads only the fibre), **fibrewise `ℝ`-linear** (so
it distributes over the section difference), with the linear-in-difference curvature section
`linearSection g₀ g₁ g₂` equal to the trace of the **once-`∇₀`-differentiated**
connection-difference Koszul **difference arm** minus the trace of the once-`∇₀`-differentiated
**cross arm**:
```
linearSection g₀ g₁ g₂ = Φ.op 0 (∇₀ koszulTripleDiff) − Φ.op 0 (∇₀ crossCorrTripleDiff),
```
where `∇₀ · = covGrad g₀ 0 3 ·`.  Carrying the trace on the **once-differentiated** rank-`4`
`∇₀ koszulTripleDiff` supplies the missing derivative (`∇^{j+1} R = ∇^{j+2} w`) that the refuted
value-local `(0, 3) → (0, 2)` form was one short of.

**Decomposition.**  Assembled from the antisymmetrised permuted-trace instance
`ricciAntisymTrace42` (witness), its linearity (`ricciModelTrace42Op_sub` + `permuteCcTensor_sub`),
and the value identity `linearSection_eq_ricciModelTrace42_koszulTriple_sub_crossCorrTriple` (the
lift of the once-differentiated pointwise lowered-Koszul form to the section trace, over the proven
child-A `loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff`).

**Non-vacuity.**  `Φ` is a *genuine* parallel contraction (its `kappa` envelope rejects the
degenerate zero witness whenever `op a R ≠ 0`), and the right-hand side genuinely carries the
once-differentiated rank-`4` jet `∇₀ koszulTripleDiff`; `linearSection` genuinely vanishes only at
`g₁ = g₂` (`linearSection_self_toModel`). -/
theorem exists_parallelTrace_linearSection_eq_koszulTriple_sub_crossCorrTriple
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ Φ : Integral.Connection.ParallelRankReducingContraction (I := I) (M := M) g₀ 4 2,
      (∀ (a : ℕ) (A B : Integral.L2.SmoothCcTensor g₀ 0 (4 + a)),
          Φ.op a (A - B) = Φ.op a A - Φ.op a B) ∧
        ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
          (g₁ g₂ : SmoothRiemannianMetric I M),
          (∀ (x : M) (v w : TangentSpace I x),
            g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
          (∀ (x : M) (v w : TangentSpace I x),
            g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
          linearSection (I := I) g₀ g₁ g₂ =
            Φ.op 0 (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
                (koszulTripleDiff (I := I) g₀ T₁ T₂))
              - Φ.op 0 (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
                (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)) := by
  refine ⟨ricciAntisymTrace42 (I := I) g₀, fun a A B => ?_, fun T₁ T₂ g₁ g₂ hr1 hr2 => ?_⟩
  · -- Fibrewise `ℝ`-linearity: permutation additivity, trace additivity, and module algebra.
    show (2⁻¹ : ℝ) •
        (ricciModelTrace42Op (I := I) g₀ a
            (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(1 : Fin 4), 2, 3] a) (A - B))
          - ricciModelTrace42Op (I := I) g₀ a
            (DeTurck.permuteCcTensor (I := I) g₀
              (shiftPerm c[(0 : Fin 4), 2, 3, 1] a) (A - B))) = _
    rw [permuteCcTensor_sub (I := I) g₀ (shiftPerm c[(1 : Fin 4), 2, 3] a) A B,
      permuteCcTensor_sub (I := I) g₀ (shiftPerm c[(0 : Fin 4), 2, 3, 1] a) A B,
      ricciModelTrace42Op_sub (I := I) g₀ a, ricciModelTrace42Op_sub (I := I) g₀ a]
    rw [show ((2⁻¹ : ℝ) •
        ((ricciModelTrace42Op (I := I) g₀ a
              (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(1 : Fin 4), 2, 3] a) A)
            - ricciModelTrace42Op (I := I) g₀ a
              (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(1 : Fin 4), 2, 3] a) B))
          - (ricciModelTrace42Op (I := I) g₀ a
              (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(0 : Fin 4), 2, 3, 1] a) A)
            - ricciModelTrace42Op (I := I) g₀ a
              (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(0 : Fin 4), 2, 3, 1] a) B)))) =
      (2⁻¹ : ℝ) •
        ((ricciModelTrace42Op (I := I) g₀ a
              (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(1 : Fin 4), 2, 3] a) A)
            - ricciModelTrace42Op (I := I) g₀ a
              (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(0 : Fin 4), 2, 3, 1] a) A))
          - (ricciModelTrace42Op (I := I) g₀ a
              (DeTurck.permuteCcTensor (I := I) g₀ (shiftPerm c[(1 : Fin 4), 2, 3] a) B)
            - ricciModelTrace42Op (I := I) g₀ a
              (DeTurck.permuteCcTensor (I := I) g₀
                (shiftPerm c[(0 : Fin 4), 2, 3, 1] a) B))) from by
      rw [sub_sub_sub_comm]]
    rw [smul_sub]
    rfl
  · exact linearSection_eq_ricciModelTrace42_koszulTriple_sub_crossCorrTriple (I := I) g₀
      T₁ T₂ g₁ g₂ hr1 hr2

/-- **The bilinear-difference factorization of the cross-correction section difference.**  Each
cross-correction section is the parallel `g₀`-single contraction `cc(gₖ,Tₖ) = Φ(hₖ, Dₖ)` of the
realized perturbation `hₖ = realizeSymmCcTensor g₀ Tₖ` against the slot-cycled lowered connection
difference `Dₖ = permuteCcTensor g₀ c[0,1,2] (loweredConnDiffSection gₖ g₀)`
(`crossCorrParallelContraction_eq_crossCorrectionSection`).  The bilinear difference of two such
products telescopes onto a **clean arm** carrying the realized difference factor
`h₁ − h₂ = realizeSymmCcTensor g₀ (T₁ − T₂) = w` against the fixed `D₁`, plus a **δ-absorbed arm**
carrying the fixed `h₂` against the lowered-connection-difference cocycle `D₁ − D₂`:
```
cc(g₁,T₁) − cc(g₂,T₂) = Φ(w, D₁) + Φ(h₂, D₁ − D₂).
```
This is the structural decomposition the cross-correction-difference covariant-jet bound consumes (the
first arm by the diagonal product grid with the lowered-jet fold, the second by the δ-recursive
absorption).  Proved from the contraction's bilinearity (`crossCorrParallelContraction_sub_left`,
`_sub_right`) and the subtractivity of `realizeSymmCcTensor` (`realizeSymmCcTensor_sub`) and the slot
permutation (`permuteCcTensor_sub`). -/
private theorem crossCorrectionSectionDiff_eq_bilinearFactorization
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) :
    DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
        - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂ =
      Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))
          (DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
            (DeTurck.loweredConnDiffSection (I := I) g₁ g₀))
        + Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
          (realizeSymmCcTensor (I := I) g₀ T₂)
          (DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
              (DeTurck.loweredConnDiffSection (I := I) g₁ g₀)
            - DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
              (DeTurck.loweredConnDiffSection (I := I) g₂ g₀)) := by
  -- Rewrite each cross-correction section as the parallel contraction `Φ(hₖ, Dₖ)`.
  rw [← crossCorrParallelContraction_eq_crossCorrectionSection (I := I) g₀ g₁ T₁,
    ← crossCorrParallelContraction_eq_crossCorrectionSection (I := I) g₀ g₂ T₂]
  -- `h₁ − h₂ = realizeSymm(T₁ − T₂)`; reduce the goal to the abstract bilinear telescoping identity.
  rw [realizeSymmCcTensor_sub (I := I) g₀ T₁ T₂]
  set h₁ := realizeSymmCcTensor (I := I) g₀ T₁
  set h₂ := realizeSymmCcTensor (I := I) g₀ T₂
  set D₁ := DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
    (DeTurck.loweredConnDiffSection (I := I) g₁ g₀)
  set D₂ := DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
    (DeTurck.loweredConnDiffSection (I := I) g₂ g₀)
  -- Bilinear telescoping `Φ(h₁,D₁) − Φ(h₂,D₂) = Φ(h₁−h₂,D₁) + Φ(h₂,D₁−D₂)`.
  conv_rhs => rw [crossCorrParallelContraction_sub_left (I := I) g₀ (a := 0) (b := 0) h₁ h₂ D₁,
    crossCorrParallelContraction_sub_right (I := I) g₀ (a := 0) (b := 0) h₂ D₁ D₂]
  abel

set_option linter.unusedSectionVars false in
/-- **The squared metric `L²` norm of a `(0, s)`-tensor is the integral of its intrinsic squared
fibre norm** (`‖S‖² = ∫ rfns(S)(x) dμ`); the currency converter between the pointwise `rfns` brick
layer and the integrated `L²` two-arm layer (local copy of the standard bridge). -/
private lemma normSq_eq_integral_rfns (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Integral.L2.SmoothCcTensor g₀ 0 s) :
    ‖S‖ ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (S.toSection x)
      ∂(Integral.Measure.riemannianVolumeMeasure I M g₀) := by
  rw [Integral.L2.SmoothCcTensor.norm_def]
  exact Integral.Connection.tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
    (I := I) (M := M) g₀ s S

set_option linter.unusedSectionVars false in
/-- **Integrated trace-and-shift comparison.**  For a parallel rank-reducing `(0,4) → (0,2)`
contraction `Φ` and a `(0, 3)`-tensor `Y`, the metric `L²` norm of the order-`j` covariant gradient
of the traced once-differentiated section `Φ.op 0 (∇₀ Y)` is dominated by `√Φ.kappa` times the
`L²` norm of the order-`(j+1)` covariant gradient of `Y` — the pointwise value-local trace envelope
`Φ.rfns_iteratedCovGrad_le` composed with the front/back rank-shift
`iteratedCovGrad_covGrad_comm_heq_local`, integrated against the Riemannian volume. -/
private lemma trace_shift_l2Norm_le (g₀ : SmoothRiemannianMetric I M) (j : ℕ)
    (Φ : Integral.Connection.ParallelRankReducingContraction (I := I) (M := M) g₀ 4 2)
    (Y : Integral.L2.SmoothCcTensor g₀ 0 3) :
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
        (Φ.op 0 (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3 Y))‖ ≤
      Real.sqrt Φ.kappa *
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1) Y‖ := by
  classical
  set X := Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3 Y with hX
  -- The pointwise trace envelope + rank shift.
  have hpt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (Φ.op 0 X)).toSection x) ≤
      Φ.kappa * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + (j + 1)) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1) Y).toSection x) := by
    intro x
    have htrace : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0 + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (2 + 0) j (Φ.op 0 X)).toSection x) ≤
        Φ.kappa * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + 0 + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (4 + 0) j X).toSection x) :=
      Φ.rfns_iteratedCovGrad_le j 0 X x
    have hshift : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + 0 + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (4 + 0) j X).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + (j + 1)) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1) Y).toSection x) := by
      rw [hX]
      exact DeTurck.riemannianFiberNormSq_toSection_heq (I := I) (M := M) g₀
        (by omega : (4 : ℕ) + 0 + j = 3 + (j + 1))
        (DeTurck.iteratedCovGrad_covGrad_comm_heq_local (I := I) (M := M) g₀ 3 j Y) x
    rw [← hshift]
    exact htrace
  -- Integrate to the squared `L²` comparison.
  have hsq : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (Φ.op 0 X)‖ ^ 2 ≤
      Φ.kappa * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1) Y‖ ^ 2 := by
    rw [normSq_eq_integral_rfns, normSq_eq_integral_rfns]
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => ?_))
      ((Integral.Connection.integrable_riemannianFiberNormSq_toSection (I := I) (M := M)
        g₀ 0 (3 + (j + 1)) _).const_mul Φ.kappa) (Filter.Eventually.of_forall (fun x => hpt x))
    exact riemannianFiberNormSq_nonneg _ _ _ _ _
  -- Take square roots.
  have hk := Φ.kappa_nonneg
  calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (Φ.op 0 X)‖
      = Real.sqrt (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (Φ.op 0 X)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (Φ.kappa * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1) Y‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt Φ.kappa * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1) Y‖ := by
        rw [Real.sqrt_mul hk, Real.sqrt_sq (norm_nonneg _)]

/-- **(POSIT — the integrated two-arm `L²` bound of the cross-correction SECTION difference.)**
The genuinely-deep reusable bilinear-difference content beneath the cross-correction-difference
leaf, in the **integrated `L²` currency** (the pointwise diagonal-grid form is FALSE: the Neumann
`k ≥ 2` layer of the Koszul-realized connection difference `connDiff = g₁⁻¹·(∇⁰h)` injects CUBIC
jet monomials `(∇ᵃh)(∇ᵇh)(∇^{c+1}h)` into `∇^p D`, so no degree-2 pointwise product grid can
dominate at all `p` — the free-jet scaling certificate `lhs_scale 2 = 8 > rhs_scale 2 = 4`; only
the Gagliardo–Nirenberg engine absorbs the concentration, after integration): the metric `L²` norm
of the order-`p` covariant gradient of the rank-`3` cross-correction section difference is
dominated, at the honest window `i ≤ p + 1` (the lowered connection difference carries ONE
`T`-derivative), by the Hamilton-tame two-arm sum
```
‖∇^p (cc(g₁,T₁) − cc(g₂,T₂))‖
  ≤ Cd · ∑_{i ≤ p+1} ‖∇^i w‖
    + Cd · ‖(T₁ − T₂).toHs a‖ · ∑_{l ≤ p+1} (‖∇^l T₁‖ + ‖∇^l T₂‖),
```
`w := realizeSymmCcTensor g₀ (T₁ − T₂)`: the **difference arm** carries the full `L²`-jet scale of
the realized difference against ball-bounded constants, the **cross arm** carries the fixed-pair
`L²`-jet scale against the difference's supercritical `C⁰`/`toHs a` mass.

Each cross-correction section `cc(gₖ,Tₖ) = Φ(realizeSymm Tₖ, permute(loweredConnDiffSection gₖ g₀))`
is the parallel `g₀`-single contraction (`crossCorrParallelContraction_eq_crossCorrectionSection`);
the bilinear difference factorizes (`crossCorrectionSectionDiff_eq_bilinearFactorization`,
sorry-free) as `Φ(w, D₁) + Φ(h₂, D₁ − D₂)` — the **clean arm** (difference factor `w` against the
fixed `D₁`, whose jets fold into the `T₁`-jets by the proven `δ < 1/2`-uniform lowered-jet bound
`exists_riemannianFiberNormSq_iteratedCovGrad_loweredConnDiff_le_jetSum`) plus the **δ-absorbed
arm** (the fibre-small `h₂` against the cocycle `D₁ − D₂`).  The k = 1 bilinear layer is fed by the
proven pointwise grids (`ParallelContractionPointwiseGrid`, the quadratic trace-difference grids);
the k ≥ 2 Neumann cubic layer is bounded ONLY in this integrated currency, through the
Gagliardo–Nirenberg engine (`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le` /
`exists_integrated_diagonalProductGrid_twoArm_pair_le`) with the sharp-order embeddings
(`exists_realizedJetSum_le_toHs_sharpOrder` at order `a` for the cross arm,
`exists_iteratedCovGradJetSum_le_toHs_sharpOrder` at order `a + 2` for the ball arm).  Its body is
`sorry`: the genuine deep integrated bilinear-difference frontier of the redesign.

**Non-vacuity.**  At `T₁ = T₂` the section difference vanishes (both metrics coincide) and both
sides are `0`; a zero `Cd` is rejected whenever the difference is present.  Carries `w` up to
`∇^{p+1} w` and both fixed-pair endpoints; NO pointwise product grid at high order, NO order-`> 2`
pointwise jet on either side, NO spectral-nonlinearity, NO Weyl dependence. -/
private theorem crossCorrectionSectionDiff_iteratedCovGrad_twoArm_l2Norm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (p : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
            (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
              - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂)‖ ≤
          Cd * ∑ i ∈ Finset.range (p + 2),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                  (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖
            + Cd * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
                * ∑ l ∈ Finset.range (p + 2),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖) :=
  sorry

/-- **The integrated two-arm `L²` bound of the pre-trace cross-correction difference**
`crossCorrTripleDiff` (proven glue: the section identity `crossCorrTripleDiff =
2•(cc(g₁,T₁) − cc(g₂,T₂))` and `L²`-norm homogeneity over the integrated section-difference
posit).  Same two-arm Hamilton-tame shape at window `p + 1`, constant `2·Cd`.

**Non-vacuity.**  At `T₁ = T₂` both sides are `0`; carries `w` up to `∇^{p+1} w` and both
fixed-pair endpoints. -/
private theorem crossCorrTripleDiff_iteratedCovGrad_twoArm_l2Norm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (p : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
            (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)‖ ≤
          Cd * ∑ i ∈ Finset.range (p + 2),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                  (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖
            + Cd * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
                * ∑ l ∈ Finset.range (p + 2),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖) := by
  classical
  obtain ⟨Cd, hCd0, hCd⟩ :=
    crossCorrectionSectionDiff_iteratedCovGrad_twoArm_l2Norm_le (I := I) g₀ a ha B hB
      δ hδ0 hδ1 p
  refine ⟨2 * Cd, by positivity, ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2
  -- `crossCorrTripleDiff = 2 • (cc(g₁,T₁) − cc(g₂,T₂))`.
  have hsec : crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂ =
      (2 : ℝ) • (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
        - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂) := by
    rw [crossCorrTripleDiff, smul_sub]
  have hnorm : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
      (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)‖ =
    2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
      (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
        - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂)‖ := by
    rw [hsec, MetricRealization.iteratedCovGrad_smul, norm_smul, Real.norm_ofNat]
  have hbase := hCd T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2
  rw [hnorm]
  nlinarith [hbase]

/-- **The integrated two-arm `L²` bound of the traced once-differentiated cross-correction
difference** (proven glue: the integrated trace-and-shift comparison `trace_shift_l2Norm_le` over
the pre-trace integrated bound at order `j + 1`).  For any parallel rank-reducing `(0,4) → (0,2)`
contraction `Φ`, the metric `L²` norm of `∇^j (Φ.op 0 (∇₀ crossCorrTripleDiff))` carries the
two-arm Hamilton-tame bound at the window `j + 2`, with constant uniform over the supercritical
`H^{a+2}`-bounded `δ`-fibre-small (`δ < 1/2`) perturbation family. -/
theorem crossCorrectionDiff_iteratedCovGrad_twoArm_l2Norm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (j : ℕ)
    (Φ : Integral.Connection.ParallelRankReducingContraction (I := I) (M := M) g₀ 4 2) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
            (Φ.op 0 (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
              (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)))‖ ≤
          Cd * ∑ i ∈ Finset.range (j + 2 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                  (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖
            + Cd * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
                * ∑ l ∈ Finset.range (j + 2 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖) := by
  classical
  obtain ⟨Cd, hCd0, hCd⟩ :=
    crossCorrTripleDiff_iteratedCovGrad_twoArm_l2Norm_le (I := I) g₀ a ha B hB
      δ hδ0 hδ1 (j + 1)
  refine ⟨Real.sqrt Φ.kappa * Cd, by positivity, ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2
  have hbase := hCd T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2
  have htrace := trace_shift_l2Norm_le (I := I) g₀ j Φ
    (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)
  have hk : (0 : ℝ) ≤ Real.sqrt Φ.kappa := Real.sqrt_nonneg _
  have hwindow : (j + 1) + 2 = j + 2 + 1 := by omega
  rw [hwindow] at hbase
  calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (Φ.op 0 (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
            (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)))‖
      ≤ Real.sqrt Φ.kappa * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1)
          (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)‖ := htrace
    _ ≤ Real.sqrt Φ.kappa *
          (Cd * ∑ i ∈ Finset.range (j + 2 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                  (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖
            + Cd * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
                * ∑ l ∈ Finset.range (j + 2 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖)) :=
        mul_le_mul_of_nonneg_left hbase hk
    _ = Real.sqrt Φ.kappa * Cd * ∑ i ∈ Finset.range (j + 2 + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖
          + Real.sqrt Φ.kappa * Cd
              * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
              * ∑ l ∈ Finset.range (j + 2 + 1),
                  (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖
                    + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖) := by ring

/-- **The integrated two-arm `L²` bound of the linear difference section (proven by
composition).**  The metric `L²` norm of the order-`j` covariant gradient of the concrete
linear-in-difference curvature section `linearSection g₀ g₁ g₂` carries the two-arm Hamilton-tame
bound at the window `j + 2`:
```
‖∇^j linearSection‖
  ≤ Cd · ∑_{i ≤ j+2} ‖∇^i w‖
    + Cd · ‖(T₁ − T₂).toHs a‖ · ∑_{l ≤ j+2} (‖∇^l T₁‖ + ‖∇^l T₂‖),
```
`w := realizeSymmCcTensor g₀ (T₁ − T₂)`.

**Decomposition.**  Through the parallel rank-reducing contraction `Φ` the principal-part identity
`exists_parallelTrace_linearSection_eq_koszulTriple_sub_crossCorrTriple` exhibits
`linearSection = Φ.op 0 (∇₀ koszulTripleDiff) − Φ.op 0 (∇₀ crossCorrTripleDiff)`.  The **Koszul
arm** is clean: the integrated trace-and-shift comparison plus the pointwise `18·rfns(∇^{j+2}w)`
domination of the traced Koszul jet, integrated — the `i = j+2` term of the difference-factor arm.
The **cross-correction arm** is the integrated two-arm bound
`crossCorrectionDiff_iteratedCovGrad_twoArm_l2Norm_le`.  The triangle inequality re-collects the
two arms with the combined constant.

**Non-vacuity.**  The difference arm carries the high derivative `∇^{j+2} w` (a zero `Cd` falsifies
it whenever the linear part is genuinely present), the cross arm carries both fixed-pair endpoints;
at `g₁ = g₂` the linear section vanishes and the bound is `0 ≤ 0`.  Consumers transitively depend on
`sorryAx` only through the integrated bilinear-difference posit. -/
theorem ricciLinearSection_covGrad_twoArm_l2Norm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (j : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
            (linearSection (I := I) g₀ g₁ g₂)‖ ≤
          Cd * ∑ i ∈ Finset.range (j + 2 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                  (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖
            + Cd * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
                * ∑ l ∈ Finset.range (j + 2 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖) := by
  classical
  obtain ⟨Φ, hΦlin, hΦid⟩ :=
    exists_parallelTrace_linearSection_eq_koszulTriple_sub_crossCorrTriple (I := I) g₀
  obtain ⟨CdQ, hCdQ0, hCdQ⟩ :=
    crossCorrectionDiff_iteratedCovGrad_twoArm_l2Norm_le (I := I) g₀ a ha B hB
      δ hδ0 hδ1 j Φ
  refine ⟨Real.sqrt Φ.kappa * Real.sqrt 18 + CdQ, by positivity, ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2
  have hcrossarm := hCdQ T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2
  set R := Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)) with hR
  set Q := Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
    (koszulTripleDiff (I := I) g₀ T₁ T₂) with hQ
  have hid := hΦid T₁ T₂ g₁ g₂ hr1 hr2
  -- The triangle split on the principal-part identity.
  have hsplit : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
        (linearSection (I := I) g₀ g₁ g₂)‖ ≤
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (Φ.op 0 Q)‖
        + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
            (Φ.op 0 (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
              (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)))‖ := by
    rw [hid, ← hQ, PDE.RicciFlow.iteratedCovGrad_sub]
    exact norm_sub_le _ _
  -- The Koszul arm: integrated trace-and-shift, then the pointwise `18`-domination integrated.
  have htraceK := trace_shift_l2Norm_le (I := I) g₀ j Φ (koszulTripleDiff (I := I) g₀ T₁ T₂)
  have hkoszul_sq : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1)
        (koszulTripleDiff (I := I) g₀ T₁ T₂)‖ ^ 2 ≤
      18 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (j + 1 + 1)
        (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2 := by
    rw [normSq_eq_integral_rfns, normSq_eq_integral_rfns]
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => ?_))
      ((Integral.Connection.integrable_riemannianFiberNormSq_toSection (I := I) (M := M)
        g₀ 0 (2 + (j + 1 + 1)) _).const_mul 18) (Filter.Eventually.of_forall (fun x => ?_))
    · exact riemannianFiberNormSq_nonneg _ _ _ _ _
    -- The pointwise `18`-domination of the Koszul triple jet by the realized difference jet.
    set LR := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + (j + 1)) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1) R).toSection x) with hLR
    have hLRnn : 0 ≤ LR := riemannianFiberNormSq_nonneg _ _ _ _ _
    have hP1eq : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + (j + 1)) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1)
          (DeTurck.permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R)).toSection x) = LR := by
      rw [hLR]
      exact DeTurck.riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) g₀
        (Equiv.swap (0 : Fin 3) 1) R (j + 1) x
    have hP2eq : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + (j + 1)) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1)
          (DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R)).toSection x) = LR := by
      rw [hLR]
      exact DeTurck.riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) g₀
        c[(0 : Fin 3), 2, 1] R (j + 1) x
    have hkoszul : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + (j + 1)) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1)
              (koszulTripleDiff (I := I) g₀ T₁ T₂)).toSection x) ≤ 18 * LR := by
      rw [koszulTripleDiff, ← hR, PDE.RicciFlow.iteratedCovGrad_sub,
        PDE.RicciFlow.iteratedCovGrad_add,
        Integral.L2.SmoothCcTensor.toSection_sub, Integral.L2.SmoothCcTensor.toSection_add,
        ContMDiffSection.coe_sub, ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply]
      refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 0 (3 + (j + 1)) x _ _) ?_
      have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + (j + 1)) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1) R).toSection x)
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1)
          (DeTurck.permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R)).toSection x)
      rw [hP1eq] at hadd
      rw [hP2eq]
      nlinarith [hadd, hLRnn]
    have hLR_eq : LR = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1 + 1)) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (j + 1 + 1)
            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x) := by
      rw [hLR, hR]
      exact DifferentialGeometry.PDE.DeTurck.riemannianFiberNormSq_toSection_heq (I := I) (M := M) g₀
        (by omega : (3 : ℕ) + (j + 1) = 2 + (j + 1 + 1))
        (DifferentialGeometry.PDE.DeTurck.iteratedCovGrad_covGrad_comm_heq_local
          (I := I) (M := M) g₀ 2 (j + 1)
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))) x
    rw [hLR_eq] at hkoszul
    exact hkoszul
  have hkoszul_norm : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1)
        (koszulTripleDiff (I := I) g₀ T₁ T₂)‖ ≤
      Real.sqrt 18 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (j + 1 + 1)
        (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ := by
    calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1)
          (koszulTripleDiff (I := I) g₀ T₁ T₂)‖
        = Real.sqrt (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1)
            (koszulTripleDiff (I := I) g₀ T₁ T₂)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (18 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (j + 1 + 1)
            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2) := Real.sqrt_le_sqrt hkoszul_sq
      _ = Real.sqrt 18 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (j + 1 + 1)
            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ := by
          rw [Real.sqrt_mul (by norm_num) _, Real.sqrt_sq (norm_nonneg _)]
  -- The top realized-difference jet is one term of the difference-factor arm.
  have htop_le : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (j + 1 + 1)
        (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ≤
      ∑ i ∈ Finset.range (j + 2 + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ :=
    Finset.single_le_sum
      (f := fun i => ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
        (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖)
      (fun i _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  have hK_arm : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (Φ.op 0 Q)‖ ≤
      Real.sqrt Φ.kappa * Real.sqrt 18 *
        ∑ i ∈ Finset.range (j + 2 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
              (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ := by
    have hk : (0 : ℝ) ≤ Real.sqrt Φ.kappa := Real.sqrt_nonneg _
    have h18 : (0 : ℝ) ≤ Real.sqrt 18 := Real.sqrt_nonneg _
    calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (Φ.op 0 Q)‖
        ≤ Real.sqrt Φ.kappa * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1)
            (koszulTripleDiff (I := I) g₀ T₁ T₂)‖ := by
          rw [hQ]
          exact htraceK
      _ ≤ Real.sqrt Φ.kappa * (Real.sqrt 18 *
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (j + 1 + 1)
              (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖) :=
          mul_le_mul_of_nonneg_left hkoszul_norm hk
      _ ≤ Real.sqrt Φ.kappa * (Real.sqrt 18 *
            ∑ i ∈ Finset.range (j + 2 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                  (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htop_le h18) hk
      _ = Real.sqrt Φ.kappa * Real.sqrt 18 *
            ∑ i ∈ Finset.range (j + 2 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                  (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ := by ring
  -- Assemble.
  have hSW_nn : 0 ≤ ∑ i ∈ Finset.range (j + 2 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  have hST_nn : 0 ≤ ∑ l ∈ Finset.range (j + 2 + 1),
      (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖
        + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖) :=
    Finset.sum_nonneg fun l _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hD_nn : 0 ≤ ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a
      (T₁ - T₂)‖ := norm_nonneg _
  have hkk : (0 : ℝ) ≤ Real.sqrt Φ.kappa * Real.sqrt 18 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [hsplit, hK_arm, hcrossarm, mul_nonneg (mul_nonneg hkk hD_nn) hST_nn]

/-- **(POSIT — the integrated two-arm `L²` bound of the quadratic Cross section.)**  The metric
`L²` norm of the order-`j` covariant gradient of the concrete quadratic-in-difference curvature
Cross section `crossSection g₀ g₁ g₂` carries, at the natural Leibniz window `j + 2` (BOTH
quadratic factors are connection differences carrying one `T`-derivative each), the integrated
two-arm Hamilton-tame bound
```
‖∇^j crossSection‖
  ≤ Cd · ∑_{i ≤ j+2} ‖∇^i w‖
    + Cd · ‖(T₁ − T₂).toHs a‖ · ∑_{l ≤ j+2} (‖∇^l T₁‖ + ‖∇^l T₂‖),
```
`w := realizeSymmCcTensor g₀ (T₁ − T₂)`, uniform over the supercritical `H^{a+2}`-bounded
`δ`-fibre-small (`δ < 1/2`) perturbation family.

`crossSection`'s fibre value is the `−2` model-basis trace of the quadratic
`connDiffField ∘ connDiffField` summand difference (`ricciDiffQuad_modelTrace_eq_crossEndoTrace`);
the bilinear identity `D₁ ∘ D₁ − D₂ ∘ D₂ = (D₁ − D₂) ∘ D₁ + D₂ ∘ (D₁ − D₂)` carries one difference
factor against one fixed factor in each arm.  The **pointwise** diagonal-grid form of this bound is
FALSE at high order (the Neumann `k ≥ 2` layer of the Koszul-realized connection difference injects
cubic jet monomials; the free-jet scaling certificate); the k = 1 bilinear layer is fed by the
proven pointwise grids (`QuadraticTraceDifferencePointwiseGrid`), the k ≥ 2 layer only by the
integrated Gagliardo–Nirenberg absorption.  Its body is `sorry`: the genuine deep integrated
quadratic-Cross frontier of the redesign.

**Non-vacuity.**  At `g₁ = g₂` the Cross section vanishes (`crossSection_self_toModel`), so both
sides are `0`; a zero `Cd` is rejected whenever the Cross part is genuinely present.  NO pointwise
product grid at high order, NO `toHs` mass on the left, NO spectral-nonlinearity, NO Weyl
dependence. -/
theorem crossSection_iteratedCovGrad_twoArm_l2Norm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (j : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
            (crossSection (I := I) g₀ g₁ g₂)‖ ≤
          Cd * ∑ i ∈ Finset.range (j + 2 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                  (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖
            + Cd * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
                * ∑ l ∈ Finset.range (j + 2 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖) :=
  sorry

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
