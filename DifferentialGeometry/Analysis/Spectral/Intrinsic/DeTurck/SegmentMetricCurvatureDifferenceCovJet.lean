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
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.QuadraticTraceDifferencePointwiseGrid
import Batteries.Tactic.OpenPrivate

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

open private leadExtPerm iteratedCovGrad_appCcRS_of_parallel realizeSymm_rfns_le_of_gFibreOpBound
  exists_loweredConnDiff_rfns_fibre_sup iteratedCovGrad_permuteCcTensor_eq permuteCcTensor_sub_local
  appCcRS_sub_right_local rfns_permuteCcTensor_zero rfns_sub_le rfns_smul iteratedCovGrad_norm_sq_smul
  iteratedCovGrad_norm_sq_sub_le smoothCcTensor_norm_sq_sub_le
  koszulCombSection_iteratedCovGrad_norm_sq_le
  from DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CrossCorrectionParallelContraction

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

set_option linter.unusedSectionVars false in
/-- **The section-uniform pointwise full-window product grid of the parallel rank-reducing
contraction.**  The quantifier-hoisted form of the per-section grid: one constant `Cd` per
`(g₀, p)`, valid for EVERY rank-`2` first factor `S` and rank-`3` second factor `T` — the
family-uniformity the integrated two-arm consumers require.  Assembled from the operator-reduced
iterated Leibniz (`crossCorrParallelContraction_eq_appCcRS` + the parallel iterated Leibniz), the
`appCcRS` fibre envelope (`crossCorrEnvelopeConst_spec`), the slot-permutation `rfns` invariance,
and the `∀`-form bare-product diagonal grid (constant `mu·4^p`). -/
private theorem contraction_rfns_fullWindowGrid_uniform
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (S : Integral.L2.SmoothCcTensor g₀ 0 (2 + 0))
        (T : Integral.L2.SmoothCcTensor g₀ 0 (3 + 0)) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 0 + 0 + p) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p
                (Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
                  S T)).toSection x) ≤
          Cd * ∑ i ∈ Finset.range (p + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i T).toSection x)
                * ∑ l ∈ Finset.range (p + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l S).toSection x) := by
  classical
  obtain ⟨hCenv0, hCenvB⟩ := DeTurck.crossCorrEnvelopeConst_spec (I := I) g₀ p
  set Φb := Integral.Connection.bareTensorRfnsBilinearProduct (I := I) g₀ 3 2 with hΦb
  refine ⟨DeTurck.crossCorrEnvelopeConst (I := I) g₀ p * (Φb.mu * (4 : ℝ) ^ p),
    mul_nonneg hCenv0 (mul_nonneg Φb.mu_nonneg (by positivity)), fun S T x => ?_⟩
  rw [Integral.Connection.crossCorrParallelContraction_eq_appCcRS (I := I) g₀
    (a := 0) (b := 0) S T]
  rw [iteratedCovGrad_appCcRS_of_parallel (I := I) g₀ 0 ((3 + 0) + (2 + 0)) (3 + 0 + 0)
    (Integral.Connection.crossCorrCometricOp (I := I) g₀ 0 0)
    (Integral.Connection.crossCorrCometricOp_covGrad_eq_zero (I := I) g₀ 0 0)
    (Integral.Connection.crossCorrProdSection (I := I) g₀ (a := 0) (b := 0) S T) p]
  refine le_trans (hCenvB _ x) ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hCenv0
  rw [Integral.Connection.crossCorrProdSection_eq_permute_unitModelProdSection (I := I) g₀ S T,
    DeTurck.riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) (M := M) g₀
      (Integral.Connection.crossCorrPerm 0 0)
      (Analysis.Parabolic.TensorSpectral.unitModelProdSection (I := I) (M := M)
        (p := 3 + 0) (q := 2 + 0) g₀ T S) p x]
  have hgrid := Φb.rfns_iteratedCovGrad_prod_le_diagGrid p (a := 0) (b := 0) T S x
  have hcast : riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + 2) + p) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 2) p
        (Φb.prod (a := 0) (b := 0) T S)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + 0) + (2 + 0) + p) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((3 + 0) + (2 + 0)) p
          (Analysis.Parabolic.TensorSpectral.unitModelProdSection (I := I) (M := M)
            (p := 3 + 0) (q := 2 + 0) g₀ T S)).toSection x) := by
    rw [show (Φb.prod (a := 0) (b := 0) T S)
      = Integral.Connection.castRankCc_db g₀ 0 (by omega : (3 + 0) + (2 + 0) = (3 + 2) + 0 + 0)
        (Analysis.Parabolic.TensorSpectral.unitModelProdSection (I := I) (M := M)
          (p := 3 + 0) (q := 2 + 0) g₀ T S) from rfl]
    rw [Integral.Connection.rfns_iteratedCovGrad_castRankCc_db (I := I) (M := M) g₀ 0
      (by omega : (3 + 0) + (2 + 0) = (3 + 2) + 0 + 0)
      (Analysis.Parabolic.TensorSpectral.unitModelProdSection (I := I) (M := M)
        (p := 3 + 0) (q := 2 + 0) g₀ T S) p x]
  rw [← hcast]
  simp only [Nat.add_zero] at hgrid ⊢
  exact hgrid

set_option linter.unusedSectionVars false in
/-- **The integrated sharp `δ²` keystone-top bound at an arbitrary jet factor.**  The squared metric
`L²` norm of the keystone product-level top cell `crossCorrKeystoneTop g₀ p T₂ Z` is at most
`δ² · ‖Z‖²`, for any `(0, 3 + p)`-jet factor `Z` and any `δ`-fibre-small perturbation `T₂` — the
pointwise sharp keystone passenger bound (`crossCorrKeystoneTop_rfns_le_sq_passenger`), integrated
against the Riemannian volume. -/
private theorem keystoneTop_norm_sq_le (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hfib : gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ)
    (Z : Integral.L2.SmoothCcTensor g₀ 0 ((3 + 0) + p)) :
    ‖DeTurck.crossCorrKeystoneTop (I := I) g₀ p T₂ Z‖ ^ 2 ≤ δ ^ 2 * ‖Z‖ ^ 2 := by
  classical
  rw [normSq_eq_integral_rfns, normSq_eq_integral_rfns]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => ?_))
    ((Integral.Connection.integrable_riemannianFiberNormSq_toSection (I := I) (M := M)
      g₀ 0 ((3 + 0) + p) Z).const_mul (δ ^ 2)) (Filter.Eventually.of_forall (fun x => ?_))
  · exact riemannianFiberNormSq_nonneg _ _ _ _ _
  · exact DeTurck.crossCorrKeystoneTop_rfns_le_sq_passenger (I := I) g₀ p T₂ hfib Z x

set_option maxHeartbeats 12800000 in
set_option linter.unusedSectionVars false in
/-- **The section-uniform `t`-scaled Gagliardo–Nirenberg integrated peeled bound on the
parallel-contraction `Rest` arm, at an ARBITRARY second factor.**  For the parallel `g₀`-single
contraction of the realized perturbation `realizeSymm T₂` against an arbitrary rank-`3` section `Y`
with `C⁰` fibre sup `√rfns(Y) ≤ Λ_Y`, the squared metric `L²` mass of the rest cell — the
difference `∇^p (Φc(realizeSymm T₂, Y)) − crossCorrKeystoneTop g₀ p T₂ (∇^p Y)` — is dominated,
for every free scale `t ∈ (0, 1]`, by
```
t·δ²·‖∇^p Y‖² + Cpk·(1/t)^p·(∑_{q<p} ‖∇^q Y‖² + Λ_Y²·∑_{i ≤ p+1} ‖∇^i (realizeSymm T₂)‖²),
```
with `Cpk` uniform over `(t, T₂, Y)` (only `(g₀, p, δ, Λ_Y-level)`-dependent through the explicit
`Λ_Y²` factor).  The arbitrary-`Y` generalization of the single-metric rest peel
(`crossCorrectionSection_iteratedCovGrad_rest_peel_realizeSymm_le`): the second factor needs no
lowered-connection structure and no Sobolev ball — its only inputs are the `C⁰` sup and its
`L²`-jet scale, which the bound carries explicitly.  Same assembly: the operator-reduced iterated
Leibniz, the pointwise peeled binomial-Leibniz grid (constant `4^p`), the `appCcRS` fibre envelope,
the strictly-sub-diagonal symmetric two-arm engine, and the anti-diagonal `t`-scaled top-arm
engine with the internal rescale absorbing the envelope and dimension constants into the free
`t·δ²`. -/
private theorem contraction_rest_peel_uniform (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (δ : ℝ) (hδ0 : 0 ≤ δ) :
    ∃ Cpk : ℝ, 0 ≤ Cpk ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ (T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) (Y : Integral.L2.SmoothCcTensor g₀ 0 3)
        (ΛY : ℝ), 0 ≤ ΛY →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (Y.toSection x) ≤ ΛY ^ 2) →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p
              (Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
                (realizeSymmCcTensor (I := I) g₀ T₂) Y)
            - DeTurck.crossCorrKeystoneTop (I := I) g₀ p T₂
                (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0) p Y)‖ ^ 2 ≤
          t * δ ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p Y‖ ^ 2
            + Cpk * (1 / t) ^ p * (∑ q ∈ Finset.range p,
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q Y‖ ^ 2
              + ΛY ^ 2 * ∑ i ∈ Finset.range (p + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ T₂)‖ ^ 2) := by
  classical
  set μ := Integral.Measure.riemannianVolumeMeasure I M g₀ with hμ
  obtain ⟨hCenv0, hCenvB⟩ := DeTurck.crossCorrEnvelopeConst_spec (I := I) g₀ p
  obtain ⟨cGlow, hcGlow0, hGNlow⟩ :=
    Analysis.Sobolev.Tensor.exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le
      (I := I) (M := M) g₀ 3 2 (p - 1)
  obtain ⟨cAnti, hcAnti0, hAnti⟩ :=
    Analysis.Sobolev.Tensor.exists_integrated_iteratedCovGrad_antiDiagGrid_topArm_scaled_le
      (I := I) (M := M) g₀ 3 2 p
  set nE : ℝ := (Module.finrank ℝ E : ℝ) with hnE
  have hnE0 : 0 ≤ nE := by rw [hnE]; positivity
  set cE := DeTurck.crossCorrEnvelopeConst (I := I) g₀ p with hcE
  set Ar : ℝ := cE * 4 ^ p * nE ^ 2 + 1 with hAr
  have hAr1 : (1 : ℝ) ≤ Ar := by
    rw [hAr]
    have : (0 : ℝ) ≤ cE * 4 ^ p * nE ^ 2 := by positivity
    linarith
  have hAr0 : (0 : ℝ) < Ar := lt_of_lt_of_le zero_lt_one hAr1
  refine ⟨cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1) + cAnti * Ar ^ p),
    by positivity, ?_⟩
  intro t ht0 ht1 T₂ Y ΛY hΛY0 hfib hYsup
  set wS := realizeSymmCcTensor (I := I) g₀ T₂ with hwS
  set Xp := PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p
      (Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0) wS Y)
    with hXpd
  set Φb := Integral.Connection.bareTensorRfnsBilinearProduct (I := I) g₀ 3 2 with hΦbd
  set Φp := DeTurck.slotExtendPow (I := I) (M := M) g₀ ((3 + 0) + (2 + 0)) (3 + 0 + 0) p
      (Integral.Connection.crossCorrCometricOp (I := I) g₀ 0 0) with hΦpd
  set U := Analysis.Parabolic.TensorSpectral.unitModelProdSection (I := I) (M := M)
      (p := 3 + 0) (q := 2 + 0) g₀ Y wS with hUd
  set TopU := Integral.Connection.castRankCc_db g₀ 0
      (by omega : ((3 + 2) + (0 + p) + 0) = ((3 + 2) + 0 + 0) + p)
      (Φb.prod (a := 0 + p) (b := 0)
        (Integral.Connection.castRankCc_db g₀ 0 (by omega : ((3 + 0) + p) = 3 + (0 + p))
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0) p Y)) wS) with hTopUd
  set σcc := Integral.Connection.crossCorrPerm 0 0 with hσccd
  set Ztop := DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm σcc p) TopU with hZtopd
  set Ap := DeTurck.crossCorrKeystoneTop (I := I) g₀ p T₂
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0) p Y) with hApd
  -- The keystone top is the slot-extended operator on the permuted product-level top cell.
  have hApeq : Ap =
      Integral.Connection.appCcRS (I := I) (M := M) g₀ 0 (((3 + 0) + (2 + 0)) + p)
        ((3 + 0 + 0) + p) Φp Ztop := rfl
  -- (1) The operator-reduced iterated Leibniz: `∇^p Φc = appCcRS Φp (∇^p P)`.
  have hXeq : Xp =
      Integral.Connection.appCcRS (I := I) (M := M) g₀ 0 (((3 + 0) + (2 + 0)) + p)
        ((3 + 0 + 0) + p) Φp
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((3 + 0) + (2 + 0)) p
          (Integral.Connection.crossCorrProdSection (I := I) g₀ (a := 0) (b := 0) wS Y)) := by
    rw [hXpd, Integral.Connection.crossCorrParallelContraction_eq_appCcRS (I := I) g₀
      (a := 0) (b := 0) wS Y]
    exact iteratedCovGrad_appCcRS_of_parallel (I := I) g₀ 0 ((3 + 0) + (2 + 0)) (3 + 0 + 0)
      (Integral.Connection.crossCorrCometricOp (I := I) g₀ 0 0)
      (Integral.Connection.crossCorrCometricOp_covGrad_eq_zero (I := I) g₀ 0 0)
      (Integral.Connection.crossCorrProdSection (I := I) g₀ (a := 0) (b := 0) wS Y) p
  -- (2) The product section is the slot-permuted bare product.
  have hPU : Integral.Connection.crossCorrProdSection (I := I) g₀ (a := 0) (b := 0) wS Y =
      DeTurck.permuteCcTensor (I := I) g₀ σcc U :=
    Integral.Connection.crossCorrProdSection_eq_permute_unitModelProdSection (I := I)
      (a := 0) (b := 0) g₀ wS Y
  -- The bare-product realization of `U`.
  have hUb : U = Φb.prod (a := 0) (b := 0) Y wS := rfl
  -- (3) The iterated gradient commutes with the slot permutation.
  have hPp : PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((3 + 0) + (2 + 0)) p
        (Integral.Connection.crossCorrProdSection (I := I) g₀ (a := 0) (b := 0) wS Y) =
      DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm σcc p)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((3 + 0) + (2 + 0)) p U) := by
    rw [hPU]
    exact iteratedCovGrad_permuteCcTensor_eq (I := I) g₀ σcc U p
  -- (4) `Xp − Ap` as a single operator action on the permuted product-level difference.
  have hXAeq : Xp - Ap =
      Integral.Connection.appCcRS (I := I) (M := M) g₀ 0 (((3 + 0) + (2 + 0)) + p)
        ((3 + 0 + 0) + p) Φp
        (DeTurck.permuteCcTensor (I := I) g₀ (leadExtPerm σcc p)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((3 + 0) + (2 + 0)) p U - TopU)) := by
    rw [hApeq, permuteCcTensor_sub_local, appCcRS_sub_right_local, ← hPp, ← hXeq]
  -- (5) The pointwise peeled binomial-Leibniz grid of the bare product (constant `4^p`).
  have hpeel : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + 2) + p) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((3 + 0) + (2 + 0)) p
          (Φb.prod (a := 0) (b := 0) Y wS) - TopU).toSection x) ≤
    (4 : ℝ) ^ p * ∑ i ∈ Finset.range p,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
        ∑ l ∈ Finset.range (p + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x) := by
    intro x
    have hgrid := Φb.rfns_iteratedCovGrad_prod_topRest_le_peeledDiagGrid p (a := 0) (b := 0) Y wS x
    have hmu : Φb.mu = 1 := rfl
    rw [hmu, one_mul] at hgrid
    exact hgrid
  -- (6) The fibre-small `C⁰` sup of the realized factor.
  have hTsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (wS.toSection x) ≤
      (nE * δ) ^ 2 := by
    intro x
    rw [hwS, hnE]
    exact realizeSymm_rfns_le_of_gFibreOpBound (I := I) g₀ T₂ hfib x
  -- (7) The pointwise envelope bound on `rfns(Xp − Ap)` against the PEELED grid (window `i < p`).
  have hXApt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + 0 + 0) + p) x
      ((Xp - Ap).toSection x) ≤
    cE * (4 : ℝ) ^ p * ∑ i ∈ Finset.range p,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
        ∑ l ∈ Finset.range (p + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x) := by
    intro x
    rw [hXAeq]
    refine le_trans (hCenvB _ x) ?_
    rw [rfns_permuteCcTensor_zero, hUb]
    calc cE * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (((3 + 0) + (2 + 0)) + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((3 + 0) + (2 + 0)) p
              (Φb.prod (a := 0) (b := 0) Y wS)
            - TopU).toSection x)
        ≤ cE * ((4 : ℝ) ^ p * ∑ i ∈ Finset.range p,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
              ∑ l ∈ Finset.range (p + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) :=
          mul_le_mul_of_nonneg_left (hpeel x) hCenv0
      _ = cE * (4 : ℝ) ^ p * ∑ i ∈ Finset.range p,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
              ∑ l ∈ Finset.range (p + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x) := by
          ring
  -- (8) The two engine instances.
  obtain ⟨hint_low, hlow⟩ := hGNlow Y wS ΛY (nE * δ) hΛY0 (by positivity) hYsup hTsup
  set tt : ℝ := t / Ar with htt
  have htt0 : 0 < tt := by rw [htt]; positivity
  have htt1 : tt ≤ 1 := by
    rw [htt, div_le_one hAr0]
    linarith
  obtain ⟨hint_anti, hanti⟩ := hAnti Y wS ΛY (nE * δ) hΛY0 (by positivity) hYsup hTsup tt htt0 htt1
  -- (9) The named jet sums.
  set Lp := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p Y‖ ^ 2 with hLpd
  set Slow := ∑ q ∈ Finset.range p,
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q Y‖ ^ 2 with hSlowd
  set Sw := ∑ i ∈ Finset.range (p + 1 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i wS‖ ^ 2 with hSwd
  have hLp_nn : 0 ≤ Lp := by rw [hLpd]; positivity
  have hSlow_nn : 0 ≤ Slow := by rw [hSlowd]; positivity
  have hSw_nn : 0 ≤ Sw := by rw [hSwd]; positivity
  have hSwfold : ∀ N : ℕ, N ≤ p + 1 + 1 → (∑ l ∈ Finset.range N,
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS‖ ^ 2) ≤ Sw := by
    intro N hN
    rw [hSwd]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 hN) (fun l _ _ => by positivity)
  rcases Nat.eq_zero_or_pos p with hp0 | hppos
  · -- Degenerate order `p = 0`: the peeled grid is empty, so `‖Xp − Ap‖² ≤ 0`.
    subst hp0
    have hzero : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + 0 + 0) + 0) x
        ((Xp - Ap).toSection x) ≤ 0 := by
      intro x
      refine le_trans (hXApt x) (le_of_eq ?_)
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero]
    have hXA0 : ‖Xp - Ap‖ ^ 2 ≤ 0 := by
      rw [normSq_eq_integral_rfns]
      calc (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 0) x
              ((Xp - Ap).toSection x) ∂μ)
          ≤ ∫ x, (0 : ℝ) ∂μ := by
            refine MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun x => ?_))
              (MeasureTheory.integrable_zero _ _ _)
              (Filter.Eventually.of_forall (fun x => hzero x))
            exact riemannianFiberNormSq_nonneg _ _ _ _ _
        _ = 0 := by simp
    have hrhs_nn : 0 ≤ t * δ ^ 2 * Lp
        + cE * 4 ^ 0 * (cGlow * (nE ^ 2 * δ ^ 2 + 1) + cAnti * Ar ^ 0)
          * (1 / t) ^ 0 * (Slow + ΛY ^ 2 * Sw) := by
      have h1 : 0 ≤ t * δ ^ 2 * Lp := by positivity
      have h2 : 0 ≤ cE * (4 : ℝ) ^ 0 * (cGlow * (nE ^ 2 * δ ^ 2 + 1) + cAnti * Ar ^ 0)
          * (1 / t) ^ 0 * (Slow + ΛY ^ 2 * Sw) := by positivity
      linarith
    linarith [hXA0, hrhs_nn]
  · -- Genuine order `p ≥ 1`.
    have hp1 : (p - 1) + 1 = p := Nat.succ_pred_eq_of_pos hppos
    rw [hp1] at hlow hint_low
    -- The peeled grid splits pointwise as the sub-diagonal window grid plus the anti-diagonal.
    have hgrid_split : ∀ x : M, (∑ i ∈ Finset.range p,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
          ∑ l ∈ Finset.range (p + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) =
        (∑ i ∈ Finset.range p,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
            ∑ l ∈ Finset.range (p - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x))
        + ∑ i ∈ Finset.range p,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x) := by
      intro x
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hip : i < p := Finset.mem_range.mp hi
      rw [show p + 1 - i = (p - i) + 1 from by omega, Finset.sum_range_succ, mul_add]
    -- Integrate the pointwise envelope bound through the grid split.
    have hXAint : ‖Xp - Ap‖ ^ 2 ≤ cE * (4 : ℝ) ^ p *
        ((∫ x, (∑ i ∈ Finset.range p,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
              ∑ l ∈ Finset.range (p - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) ∂μ)
          + ∫ x, (∑ i ∈ Finset.range p,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x)) ∂μ) := by
      rw [normSq_eq_integral_rfns]
      calc (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
              ((Xp - Ap).toSection x) ∂μ)
          ≤ ∫ x, (cE * (4 : ℝ) ^ p * ((∑ i ∈ Finset.range p,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
                ∑ l ∈ Finset.range (p - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x))
            + ∑ i ∈ Finset.range p,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x))) ∂μ := by
            refine MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun x => ?_))
              ((hint_low.add hint_anti).const_mul _)
              (Filter.Eventually.of_forall (fun x => ?_))
            · exact riemannianFiberNormSq_nonneg _ _ _ _ _
            · refine le_trans (hXApt x) (le_of_eq ?_)
              rw [hgrid_split x]
        _ = cE * (4 : ℝ) ^ p * ((∫ x, (∑ i ∈ Finset.range p,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
                ∑ l ∈ Finset.range (p - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) ∂μ)
            + ∫ x, (∑ i ∈ Finset.range p,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x)) ∂μ) := by
            rw [MeasureTheory.integral_const_mul,
              MeasureTheory.integral_add hint_low hint_anti]
    -- The two w-arms fold into `Sw`.
    have hSw_low : (∑ l ∈ Finset.range p,
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS‖ ^ 2) ≤ Sw :=
      hSwfold p (by omega)
    have hSw_anti : (∑ l ∈ Finset.range (p + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS‖ ^ 2) ≤ Sw :=
      hSwfold (p + 1) (by omega)
    -- The low-window integral bound, folded.
    have hlow' : (∫ x, (∑ i ∈ Finset.range p,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
          ∑ l ∈ Finset.range (p - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) ∂μ) ≤
        cGlow * ((nE * δ) ^ 2 * Slow + ΛY ^ 2 * Sw) := by
      refine le_trans hlow ?_
      have h2 : ΛY ^ 2 * (∑ l ∈ Finset.range p,
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS‖ ^ 2) ≤ ΛY ^ 2 * Sw :=
        mul_le_mul_of_nonneg_left hSw_low (by positivity)
      nlinarith [hcGlow0, h2]
    -- The anti-diagonal integral bound, with the internal rescale `tt = t / Ar`.
    have hanti' : (∫ x, (∑ i ∈ Finset.range p,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x)) ∂μ) ≤
        tt * ((nE * δ) ^ 2 * Lp) + cAnti * (1 / tt) ^ p * (ΛY ^ 2 * Sw) := by
      refine le_trans hanti ?_
      have h2 : ΛY ^ 2 * (∑ l ∈ Finset.range (p + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS‖ ^ 2) ≤ ΛY ^ 2 * Sw :=
        mul_le_mul_of_nonneg_left hSw_anti (by positivity)
      have hc : 0 ≤ cAnti * (1 / tt) ^ p := by positivity
      nlinarith [hc, h2]
    -- The rescale algebra.
    have htopscale : cE * (4 : ℝ) ^ p * (tt * ((nE * δ) ^ 2 * Lp)) ≤ t * δ ^ 2 * Lp := by
      rw [htt]
      rw [show cE * (4 : ℝ) ^ p * (t / Ar * ((nE * δ) ^ 2 * Lp))
          = (cE * 4 ^ p * nE ^ 2) / Ar * (t * δ ^ 2 * Lp) from by ring]
      have hfrac : (cE * 4 ^ p * nE ^ 2) / Ar ≤ 1 := by
        rw [div_le_one hAr0, hAr]
        linarith
      have hmass : 0 ≤ t * δ ^ 2 * Lp := by positivity
      nlinarith [hfrac, hmass]
    have hinv_tt : (1 / tt) ^ p = Ar ^ p * (1 / t) ^ p := by
      rw [htt, one_div_div, show Ar / t = Ar * (1 / t) from by ring, mul_pow]
    have h1t1 : (1 : ℝ) ≤ (1 / t) ^ p := one_le_pow₀ (by rw [le_div_iff₀ ht0]; linarith)
    -- Assemble.
    have hfinal : cE * (4 : ℝ) ^ p *
        ((∫ x, (∑ i ∈ Finset.range p,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
              ∑ l ∈ Finset.range (p - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) ∂μ)
          + ∫ x, (∑ i ∈ Finset.range p,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x)) ∂μ) ≤
        t * δ ^ 2 * Lp
          + cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1) + cAnti * Ar ^ p)
            * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw) := by
      have hcE4 : (0 : ℝ) ≤ cE * 4 ^ p := by positivity
      have hsum_le := add_le_add hlow' hanti'
      have hstep : cE * (4 : ℝ) ^ p *
          ((∫ x, (∑ i ∈ Finset.range p,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
                ∑ l ∈ Finset.range (p - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l wS).toSection x)) ∂μ)
            + ∫ x, (∑ i ∈ Finset.range p,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i Y).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p - i)) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p - i) wS).toSection x)) ∂μ) ≤
          cE * 4 ^ p * (cGlow * ((nE * δ) ^ 2 * Slow + ΛY ^ 2 * Sw))
            + cE * 4 ^ p * (tt * ((nE * δ) ^ 2 * Lp))
            + cE * 4 ^ p * (cAnti * (1 / tt) ^ p * (ΛY ^ 2 * Sw)) := by
        nlinarith [hsum_le, hcE4]
      refine le_trans hstep ?_
      rw [hinv_tt]
      have hΛSw_nn : 0 ≤ ΛY ^ 2 * Sw := by positivity
      have hlow_piece : cE * (4 : ℝ) ^ p * (cGlow * ((nE * δ) ^ 2 * Slow + ΛY ^ 2 * Sw)) ≤
          cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1)) * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw) := by
        have hbase : cGlow * ((nE * δ) ^ 2 * Slow + ΛY ^ 2 * Sw) ≤
            cGlow * (nE ^ 2 * δ ^ 2 + 1) * (Slow + ΛY ^ 2 * Sw) := by
          nlinarith [hcGlow0, hSlow_nn, hΛSw_nn, sq_nonneg (nE * δ),
            mul_nonneg hcGlow0 (mul_nonneg (sq_nonneg (nE * δ)) hΛSw_nn),
            mul_nonneg hcGlow0 (mul_nonneg (sq_nonneg ΛY) hSlow_nn),
            mul_nonneg hcGlow0 hSlow_nn]
        calc cE * (4 : ℝ) ^ p * (cGlow * ((nE * δ) ^ 2 * Slow + ΛY ^ 2 * Sw))
            ≤ cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1) * (Slow + ΛY ^ 2 * Sw)) :=
              mul_le_mul_of_nonneg_left hbase hcE4
          _ = cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1)) * (1 : ℝ) * (Slow + ΛY ^ 2 * Sw) := by
              ring
          _ ≤ cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1)) * (1 / t) ^ p
                * (Slow + ΛY ^ 2 * Sw) := by
              have hmono : cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1)) * (1 : ℝ) ≤
                  cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1)) * (1 / t) ^ p := by
                have hc : (0 : ℝ) ≤ cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1)) := by
                  positivity
                nlinarith [h1t1, hc]
              exact mul_le_mul_of_nonneg_right hmono (by linarith [hSlow_nn, hΛSw_nn])
      have hanti_piece : cE * (4 : ℝ) ^ p * (cAnti * (Ar ^ p * (1 / t) ^ p) * (ΛY ^ 2 * Sw)) ≤
          cE * 4 ^ p * (cAnti * Ar ^ p) * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw) := by
        have hc : (0 : ℝ) ≤ cAnti * Ar ^ p * (1 / t) ^ p := by positivity
        have hbase : cAnti * (Ar ^ p * (1 / t) ^ p) * (ΛY ^ 2 * Sw) ≤
            cAnti * Ar ^ p * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw) := by
          nlinarith [hSlow_nn, hc]
        calc cE * (4 : ℝ) ^ p * (cAnti * (Ar ^ p * (1 / t) ^ p) * (ΛY ^ 2 * Sw))
            ≤ cE * 4 ^ p * (cAnti * Ar ^ p * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw)) :=
              mul_le_mul_of_nonneg_left hbase hcE4
          _ = cE * 4 ^ p * (cAnti * Ar ^ p) * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw) := by ring
      have hdistr : cE * (4 : ℝ) ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1))
            * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw)
          + cE * 4 ^ p * (cAnti * Ar ^ p) * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw)
          = cE * 4 ^ p * (cGlow * (nE ^ 2 * δ ^ 2 + 1) + cAnti * Ar ^ p)
            * (1 / t) ^ p * (Slow + ΛY ^ 2 * Sw) := by ring
      linarith [hlow_piece, hanti_piece, htopscale, hdistr.le, hdistr.ge]
    exact le_trans hXAint hfinal

set_option linter.unusedSectionVars false in
/-- **The squared metric `L²` norm of every iterated covariant jet is slot-permutation
invariant** — the pointwise fibre isometry
`riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor`, integrated. -/
private theorem norm_sq_iteratedCovGrad_permute (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (W : Integral.L2.SmoothCcTensor g₀ 0 s) (i : ℕ) :
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s i
        (DeTurck.permuteCcTensor (I := I) g₀ σ W)‖ ^ 2 =
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 s i W‖ ^ 2 := by
  rw [normSq_eq_integral_rfns, normSq_eq_integral_rfns]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact DeTurck.riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) (M := M)
    g₀ σ W i x

set_option linter.unusedSectionVars false in
/-- **The order-`i` realize-jet `L²` conversion** — the realization gains no derivatives: the
squared metric `L²` norm of the order-`i` covariant jet of the realized perturbation is bounded by
the `≤ i`-jet `L²` sum of the perturbation itself, with a constant uniform over the perturbation
(the pointwise `exists_riemannianFiberNormSq_iteratedCovGrad_realizeSymm_le_jetSum`, integrated). -/
private theorem realize_jet_norm_sq_fold (g₀ : SmoothRiemannianMetric I M) (i : ℕ) :
    ∃ Ci : ℝ, 0 ≤ Ci ∧
      ∀ T : Integral.L2.SmoothCcTensor g₀ 0 2,
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ T)‖ ^ 2 ≤
          Ci * ∑ l ∈ Finset.range (i + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T‖ ^ 2 := by
  classical
  set μ := Integral.Measure.riemannianVolumeMeasure I M g₀ with hμ
  obtain ⟨C, hC0, hC⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_realizeSymm_le_jetSum (I := I) g₀ i
  refine ⟨C, hC0, fun T => ?_⟩
  rw [normSq_eq_integral_rfns]
  have hintRl : ∀ l, MeasureTheory.Integrable (fun x =>
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) μ :=
    fun l => Integral.Connection.integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g₀ 0 (2 + l) _
  have hintRsum : MeasureTheory.Integrable (fun x => C * ∑ l ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) μ :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 1))
      (fun l _ => hintRl l)).const_mul C
  calc ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
              (realizeSymmCcTensor (I := I) g₀ T)).toSection x) ∂μ
      ≤ ∫ x, (C * ∑ l ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) ∂μ := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun x => ?_)) hintRsum
            (Filter.Eventually.of_forall (fun x => hC T x))
          exact riemannianFiberNormSq_nonneg _ _ _ _ _
    _ = C * ∑ l ∈ Finset.range (i + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T‖ ^ 2 := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finset_sum _ (fun l _ => hintRl l)]
        congr 1
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [normSq_eq_integral_rfns]

set_option linter.unusedSectionVars false in
/-- **The summed realize-jet `L²` conversion at window `N`.**  One constant per `(g₀, N)`, folding
the whole realized jet sum `∑_{i ≤ N} ‖∇^i (realizeSymm T)‖²` into the perturbation jet sum
`∑_{l ≤ N} ‖∇^l T‖²`. -/
private theorem realize_jet_norm_sq_sum_fold (g₀ : SmoothRiemannianMetric I M) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g₀ 0 2,
        (∑ i ∈ Finset.range (N + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
              (realizeSymmCcTensor (I := I) g₀ T)‖ ^ 2) ≤
          C * ∑ l ∈ Finset.range (N + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T‖ ^ 2 := by
  classical
  choose Ci hCi0 hCi using fun i => realize_jet_norm_sq_fold (I := I) (M := M) g₀ i
  refine ⟨∑ i ∈ Finset.range (N + 1), Ci i,
    Finset.sum_nonneg fun i _ => hCi0 i, fun T => ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  refine le_trans (hCi i T) (mul_le_mul_of_nonneg_left ?_ (hCi0 i))
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 (by have := Finset.mem_range.mp hi; omega))
    (fun l _ _ => by positivity)

set_option linter.unusedSectionVars false in
/-- **The section-uniform `t`-scaled top/rest split of the parallel contraction at an arbitrary
second factor.**  Combining the sharp integrated keystone-top bound (`δ²·‖∇^p Y‖²`) with the
`t`-scaled generic rest peel through the `2`-subadditivity `‖Top + Rest‖² ≤ 2‖Top‖² + 2‖Rest‖²`:
```
‖∇^p Φc(realizeSymm T₂, Y)‖²
  ≤ 2(1+t)·δ²·‖∇^p Y‖² + 2·Cpk·(1/t)^p·(∑_{q<p} ‖∇^q Y‖² + Λ_Y²·∑_{i ≤ p+1} ‖∇^i (realizeSymm T₂)‖²).
```
-/
private theorem contraction_topRest_split_uniform (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (δ : ℝ) (hδ0 : 0 ≤ δ) :
    ∃ Cpk : ℝ, 0 ≤ Cpk ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ (T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) (Y : Integral.L2.SmoothCcTensor g₀ 0 3)
        (ΛY : ℝ), 0 ≤ ΛY →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (Y.toSection x) ≤ ΛY ^ 2) →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p
              (Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
                (realizeSymmCcTensor (I := I) g₀ T₂) Y)‖ ^ 2 ≤
          2 * (1 + t) * δ ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p Y‖ ^ 2
            + 2 * Cpk * (1 / t) ^ p * (∑ q ∈ Finset.range p,
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q Y‖ ^ 2
              + ΛY ^ 2 * ∑ i ∈ Finset.range (p + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ T₂)‖ ^ 2) := by
  classical
  obtain ⟨Cpk, hCpk0, hCpk⟩ := contraction_rest_peel_uniform (I := I) (M := M) g₀ p δ hδ0
  refine ⟨Cpk, hCpk0, ?_⟩
  intro t ht0 ht1 T₂ Y ΛY hΛY0 hfib hYsup
  set Xp := PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p
      (Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
        (realizeSymmCcTensor (I := I) g₀ T₂) Y) with hXpd
  set Ap := DeTurck.crossCorrKeystoneTop (I := I) g₀ p T₂
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0) p Y) with hApd
  have htop : ‖Ap‖ ^ 2 ≤
      δ ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p Y‖ ^ 2 := by
    rw [hApd]
    exact keystoneTop_norm_sq_le (I := I) (M := M) g₀ p T₂ hfib
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0) p Y)
  have hrest := hCpk t ht0 ht1 T₂ Y ΛY hΛY0 hfib hYsup
  rw [← hXpd, ← hApd] at hrest
  -- `‖Xp‖² ≤ 2‖Ap‖² + 2‖Xp − Ap‖²`.
  have h2sub : ‖Xp‖ ^ 2 ≤ 2 * ‖Ap‖ ^ 2 + 2 * ‖Xp - Ap‖ ^ 2 := by
    have hXeq : Xp = Ap + (Xp - Ap) := (add_sub_cancel Ap Xp).symm
    have hns := norm_add_sq_real Ap (Xp - Ap)
    have hcs := abs_real_inner_le_norm Ap (Xp - Ap)
    have hcs' := le_abs_self (inner (𝕜 := ℝ) Ap (Xp - Ap))
    calc ‖Xp‖ ^ 2 = ‖Ap + (Xp - Ap)‖ ^ 2 := by rw [← hXeq]
      _ ≤ 2 * ‖Ap‖ ^ 2 + 2 * ‖Xp - Ap‖ ^ 2 := by
          nlinarith [hns, hcs, hcs', sq_nonneg (‖Ap‖ - ‖Xp - Ap‖), norm_nonneg Ap,
            norm_nonneg (Xp - Ap)]
  calc ‖Xp‖ ^ 2 ≤ 2 * ‖Ap‖ ^ 2 + 2 * ‖Xp - Ap‖ ^ 2 := h2sub
    _ ≤ 2 * (δ ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p Y‖ ^ 2)
        + 2 * (t * δ ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p Y‖ ^ 2
          + Cpk * (1 / t) ^ p * (∑ q ∈ Finset.range p,
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q Y‖ ^ 2
            + ΛY ^ 2 * ∑ i ∈ Finset.range (p + 1 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                  (realizeSymmCcTensor (I := I) g₀ T₂)‖ ^ 2)) := by
        have := mul_le_mul_of_nonneg_left htop (by norm_num : (0 : ℝ) ≤ 2)
        have := mul_le_mul_of_nonneg_left hrest (by norm_num : (0 : ℝ) ≤ 2)
        linarith
    _ = 2 * (1 + t) * δ ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p Y‖ ^ 2
        + 2 * Cpk * (1 / t) ^ p * (∑ q ∈ Finset.range p,
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q Y‖ ^ 2
          + ΛY ^ 2 * ∑ i ∈ Finset.range (p + 1 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ T₂)‖ ^ 2) := by ring

set_option linter.unusedSectionVars false in
/-- **The δ-separated integrated contraction grid at the LOW (`H^{a+2}`) ball** — the low-ball
sibling of `crossCorrectionSection_iteratedCovGrad_grid_le`: the `t`-scaled split at the
margin-chosen scale `t = (1 − 2δ)/(1 + 2δ)`, the scaled-Young absorption
`crossCorrMarginScale_absorb` relaxing the principal to `δ`, the `C⁰` sup of the lowered
connection difference funded by the order-`a` ball (`exists_loweredConnDiff_rfns_fibre_sup`,
mono-down from `a + 2`), and the realize-jet `L²` conversion folding the realized arm into the
`T₁`-jets. -/
private theorem cc_grid_le_low (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Cgrid : ℝ, 0 ≤ Cgrid ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁)‖ ^ 2 ≤
          δ * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (DeTurck.loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
          + Cgrid * (∑ q ∈ Finset.range p,
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                    (DeTurck.loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
              + ∑ l ∈ Finset.range (p + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2) := by
  classical
  obtain ⟨ΛD, hΛD0, hΛD⟩ := exists_loweredConnDiff_rfns_fibre_sup (I := I) g₀ hδ0 hδ1 B a ha
  obtain ⟨Cpk, hCpk0, hCpk⟩ := contraction_topRest_split_uniform (I := I) (M := M) g₀ p δ hδ0
  obtain ⟨Cr, hCr0, hCr⟩ := realize_jet_norm_sq_sum_fold (I := I) (M := M) g₀ (p + 1)
  obtain ⟨ht0', ht1'⟩ := DeTurck.crossCorrMarginScale_mem (δ := δ) hδ0 hδ1
  set t : ℝ := (1 - 2 * δ) / (1 + 2 * δ) with htdef
  refine ⟨2 * Cpk * (1 / t) ^ p * (1 + ΛD ^ 2 * Cr), by positivity, ?_⟩
  intro T₁ g₁ hr hfib hball
  have hball_a : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a T₁‖ ≤ B :=
    le_trans (toHs_norm_mono (I := I) (M := M) g₀ (by omega : a ≤ a + 2) T₁) hball
  set D := DeTurck.loweredConnDiffSection (I := I) g₁ g₀ with hDd
  set Y := DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2] D with hYd
  have hYsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (Y.toSection x) ≤
      ΛD ^ 2 := by
    intro x
    rw [hYd, rfns_permuteCcTensor_zero, hDd]
    exact hΛD T₁ g₁ hr hfib hball_a x
  -- The contraction realization of the cross-correction section.
  have hccid : DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁ =
      Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
        (realizeSymmCcTensor (I := I) g₀ T₁) Y :=
    (Integral.Connection.crossCorrParallelContraction_eq_crossCorrectionSection
      (I := I) g₀ g₁ T₁).symm
  have hsplit := hCpk t ht0' ht1' T₁ Y ΛD hΛD0 hfib hYsup
  -- The permutation `L²`-norm invariances `‖∇^q Y‖² = ‖∇^q D‖²`.
  have hYD : ∀ q : ℕ, ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q Y‖ ^ 2 =
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q D‖ ^ 2 := by
    intro q
    rw [hYd]
    exact norm_sq_iteratedCovGrad_permute (I := I) (M := M) g₀ c[(0 : Fin 3), 1, 2] D q
  rw [hccid]
  -- The margin absorption `2(1+t)δ² ≤ δ`.
  have habsorb : 2 * (1 + t) * δ ^ 2 ≤ δ := DeTurck.crossCorrMarginScale_absorb hδ0 hδ1
  -- Assemble.
  set Lp := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p D‖ ^ 2 with hLpd
  set Slow := ∑ q ∈ Finset.range p,
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q D‖ ^ 2 with hSlowd
  set ST := ∑ l ∈ Finset.range (p + 1 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 with hSTd
  have hLp_nn : 0 ≤ Lp := by rw [hLpd]; positivity
  have hSlow_nn : 0 ≤ Slow := by rw [hSlowd]; positivity
  have hST_nn : 0 ≤ ST := by rw [hSTd]; positivity
  have hSlowY : (∑ q ∈ Finset.range p,
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q Y‖ ^ 2) = Slow := by
    rw [hSlowd]
    exact Finset.sum_congr rfl fun q _ => hYD q
  have hSw_fold : (∑ i ∈ Finset.range (p + 1 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2) ≤ Cr * ST := by
    rw [hSTd]
    exact hCr T₁
  rw [hYD p, ← hLpd, hSlowY] at hsplit
  have h1t : (0 : ℝ) ≤ (1 / t) ^ p := by positivity
  have hprin : 2 * (1 + t) * δ ^ 2 * Lp ≤ δ * Lp :=
    mul_le_mul_of_nonneg_right habsorb hLp_nn
  have hrest_fold : 2 * Cpk * (1 / t) ^ p * (Slow + ΛD ^ 2 * ∑ i ∈ Finset.range (p + 1 + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2) ≤
      2 * Cpk * (1 / t) ^ p * (1 + ΛD ^ 2 * Cr) * (Slow + ST) := by
    have hin : Slow + ΛD ^ 2 * ∑ i ∈ Finset.range (p + 1 + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 ≤
        (1 + ΛD ^ 2 * Cr) * (Slow + ST) := by
      have h2 : ΛD ^ 2 * (∑ i ∈ Finset.range (p + 1 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2) ≤ ΛD ^ 2 * (Cr * ST) :=
        mul_le_mul_of_nonneg_left hSw_fold (by positivity)
      nlinarith [hSlow_nn, hST_nn, sq_nonneg ΛD, mul_nonneg (sq_nonneg ΛD)
        (mul_nonneg hCr0 hST_nn), mul_nonneg (mul_nonneg (sq_nonneg ΛD) hCr0) hSlow_nn]
    calc 2 * Cpk * (1 / t) ^ p * (Slow + ΛD ^ 2 * ∑ i ∈ Finset.range (p + 1 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2)
        ≤ 2 * Cpk * (1 / t) ^ p * ((1 + ΛD ^ 2 * Cr) * (Slow + ST)) :=
          mul_le_mul_of_nonneg_left hin (by positivity)
      _ = 2 * Cpk * (1 / t) ^ p * (1 + ΛD ^ 2 * Cr) * (Slow + ST) := by ring
  linarith [hsplit, hprin, hrest_fold]

set_option linter.unusedSectionVars false in
/-- **T1-LOW — the iterated-covariant-jet `L²` bound of the metrically-lowered connection
difference at the LOW (`H^{a+2}`) ball.**  The low-ball sibling of
`exists_riemannianFiberNormSq_iteratedCovGrad_loweredConnDiff_le_jetSum`: the same
differentiated-Koszul `δ < 1/2` strong-induction recursion (`4 − 8δ > 0`), but every brick funded
by the FIXED order-`(a+2)` Sobolev ball — the order-uniform Hamilton-tame fold the integrated
two-arm consumers (whose ball is `a + 2` at every gradient order) require. -/
private theorem loweredConnDiff_jet_norm_sq_fold_low (g₀ : SmoothRiemannianMetric I M) (p : ℕ)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (DeTurck.loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤
          C * ∑ l ∈ Finset.range (p + 1 + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 := by
  classical
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    obtain ⟨Ck, hCk0, hCk⟩ := koszulCombSection_iteratedCovGrad_norm_sq_le (I := I) g₀ p
    obtain ⟨Cg, hCg0, hCg⟩ := cc_grid_le_low (I := I) (M := M) g₀ p δ hδ0 hδ1 B a ha
    have hih : ∀ q ∈ Finset.range p, ∃ Cq : ℝ, 0 ≤ Cq ∧
        ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
          gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                (DeTurck.loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤
            Cq * ∑ l ∈ Finset.range (q + 1 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 :=
      fun q hq => ih q (Finset.mem_range.mp hq)
    choose! Cq hCq0 hCq using hih
    have hden : 0 < 4 - 8 * δ := by linarith
    refine ⟨(2 * Ck + 8 * Cg + 8 * Cg * ∑ q ∈ Finset.range p, Cq q) / (4 - 8 * δ), ?_, ?_⟩
    · have : 0 ≤ ∑ q ∈ Finset.range p, Cq q := Finset.sum_nonneg fun q hq => hCq0 q hq
      positivity
    intro T₁ g₁ hr hfib hball
    set S := ∑ l ∈ Finset.range (p + 1 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 with hSdef
    have hSnn : 0 ≤ S := Finset.sum_nonneg fun l _ => by positivity
    set L := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
      (DeTurck.loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 with hLdef
    have hLnn : 0 ≤ L := by rw [hLdef]; positivity
    set Kr := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
      (DeTurck.koszulCombSection (I := I) g₁ g₀ T₁)‖ ^ 2 with hKrdef
    set Cr := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
      (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁)‖ ^ 2 with hCrdef
    -- The section-level Koszul identity under `∇^p`: `4L ≤ 2Kr + 8Cr`.
    have hsub : (4 : ℝ) * L ≤ 2 * Kr + 8 * Cr := by
      have hid : PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
            ((2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₁ g₀) =
          PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (DeTurck.koszulCombSection (I := I) g₁ g₀ T₁) -
            PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              ((2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁) := by
        rw [← PDE.RicciFlow.iteratedCovGrad_sub]
        congr 1
        rw [DeTurck.koszulCombSection]
        abel
      have h4L : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
            ((2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 = 4 * L := by
        rw [iteratedCovGrad_norm_sq_smul, hLdef]; norm_num
      have h4Cr : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
            ((2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁)‖ ^ 2 = 4 * Cr := by
        rw [iteratedCovGrad_norm_sq_smul, hCrdef]; norm_num
      have hle := iteratedCovGrad_norm_sq_sub_le (I := I) g₀ 3 p
        (DeTurck.koszulCombSection (I := I) g₁ g₀ T₁)
        ((2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁)
      rw [PDE.RicciFlow.iteratedCovGrad_sub] at hle
      rw [hid] at h4L
      rw [← hKrdef, h4Cr] at hle
      linarith [hle, h4L]
    have hKr_le : Kr ≤ Ck * S := hCk T₁ g₁ hr
    have hCr_le : Cr ≤ δ * L + Cg * ((∑ q ∈ Finset.range p,
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
              (DeTurck.loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2) + S) :=
      hCg T₁ g₁ hr hfib hball
    have hlow_le : ∀ q ∈ Finset.range p,
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
            (DeTurck.loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤ Cq q * S := by
      intro q hq
      refine le_trans (hCq q hq T₁ g₁ hr hfib hball) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCq0 q hq)
      rw [hSdef]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2
          (by have := Finset.mem_range.mp hq; omega))
        fun l _ _ => by positivity
    have hsum_low : (∑ q ∈ Finset.range p,
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
              (DeTurck.loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2) ≤
        (∑ q ∈ Finset.range p, Cq q) * S := by
      rw [Finset.sum_mul]; exact Finset.sum_le_sum hlow_le
    have hsumCq_nn : 0 ≤ ∑ q ∈ Finset.range p, Cq q :=
      Finset.sum_nonneg fun q hq => hCq0 q hq
    have hkey : (4 - 8 * δ) * L ≤
        (2 * Ck + 8 * Cg + 8 * Cg * ∑ q ∈ Finset.range p, Cq q) * S := by
      nlinarith [hsub, hKr_le, hCr_le, hsum_low, hSnn, hLnn, hCg0, hCk0, hsumCq_nn,
        mul_le_mul_of_nonneg_left hsum_low hCg0]
    rw [hLdef] at hkey ⊢
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    nlinarith [hkey]

set_option linter.unusedSectionVars false in
/-- **The pointwise `18`-domination of the Koszul-triple jets by the realized-difference jets** —
the three slot readings of the once-differentiated realized difference factor, with the front/back
rank shift `∇^p (∇₀ w) ≍ ∇^{p+1} w`. -/
private theorem koszulTriple_rfns_le' (g₀ : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) (p : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
            (koszulTripleDiff (I := I) g₀ T₁ T₂)).toSection x) ≤
      18 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p + 1)) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p + 1)
            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x) := by
  classical
  set R := Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)) with hR
  set LR := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x) with hLR
  have hLRnn : 0 ≤ LR := riemannianFiberNormSq_nonneg _ _ _ _ _
  have hP1eq : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        (DeTurck.permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R)).toSection x) = LR := by
    rw [hLR]
    exact DeTurck.riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) g₀
      (Equiv.swap (0 : Fin 3) 1) R p x
  have hP2eq : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        (DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R)).toSection x) = LR := by
    rw [hLR]
    exact DeTurck.riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) g₀
      c[(0 : Fin 3), 2, 1] R p x
  have hkoszul : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
            (koszulTripleDiff (I := I) g₀ T₁ T₂)).toSection x) ≤ 18 * LR := by
    rw [koszulTripleDiff, ← hR, PDE.RicciFlow.iteratedCovGrad_sub,
      PDE.RicciFlow.iteratedCovGrad_add,
      Integral.L2.SmoothCcTensor.toSection_sub, Integral.L2.SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_sub, ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply]
    refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 0 (3 + p) x _ _) ?_
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + p) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x)
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        (DeTurck.permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R)).toSection x)
    rw [hP1eq] at hadd
    rw [hP2eq]
    nlinarith [hadd, hLRnn]
  have hLR_eq : LR = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p + 1)) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p + 1)
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x) := by
    rw [hLR, hR]
    exact DifferentialGeometry.PDE.DeTurck.riemannianFiberNormSq_toSection_heq
      (I := I) (M := M) g₀ (by omega : (3 : ℕ) + p = 2 + (p + 1))
      (DifferentialGeometry.PDE.DeTurck.iteratedCovGrad_covGrad_comm_heq_local
        (I := I) (M := M) g₀ 2 p
        (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))) x
  rw [hLR_eq] at hkoszul
  exact hkoszul

set_option linter.unusedSectionVars false in
/-- **The integrated `18`-domination of the Koszul-triple jets** — `koszulTriple_rfns_le'`
integrated against the Riemannian volume. -/
private theorem koszulTriple_norm_sq_le' (g₀ : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) (p : ℕ) :
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        (koszulTripleDiff (I := I) g₀ T₁ T₂)‖ ^ 2 ≤
      18 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p + 1)
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2 := by
  rw [normSq_eq_integral_rfns, normSq_eq_integral_rfns]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => ?_))
    ((Integral.Connection.integrable_riemannianFiberNormSq_toSection (I := I) (M := M)
      g₀ 0 (2 + (p + 1)) _).const_mul 18) (Filter.Eventually.of_forall (fun x =>
        koszulTriple_rfns_le' (I := I) (M := M) g₀ T₁ T₂ p x))
  exact riemannianFiberNormSq_nonneg _ _ _ _ _

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The supercritical pointwise bound of the realized difference and its first covariant
gradient by the order-`a` Sobolev mass of the difference.**  The `j ≤ 1` fibre values of
`w = realizeSymm (T₁ − T₂)` are bounded at every point by `Cemb·‖(T₁ − T₂).toHs a‖`
(`exists_realizedJetSum_le_toHs_sharpOrder`, the `2a > finrank + 4` realized `C²`-jet embedding). -/
private theorem realized_diff_rfns_le_toHs (g₀ : SmoothRiemannianMetric I M)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Cemb : ℝ, 0 ≤ Cemb ∧
      ∀ (S : Integral.L2.SmoothCcTensor g₀ 0 2) (j : ℕ), j < 3 → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (realizeSymmCcTensor (I := I) g₀ S)).toSection x) ≤
          (Cemb * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a S‖) ^ 2 := by
  classical
  obtain ⟨Cemb, hCemb0, hCemb⟩ :=
    exists_realizedJetSum_le_toHs_sharpOrder (I := I) g₀ a ha
  refine ⟨Cemb, hCemb0.le, fun S j hj x => ?_⟩
  have hjet := hCemb S x
  have hsqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (realizeSymmCcTensor (I := I) g₀ S)).toSection x)) ≤
      iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ S) x := by
    rw [iteratedCovGradJetSum]
    have hhead : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
            (realizeSymmCcTensor (I := I) g₀ S)).toSection x)) =
        (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + j) I bb) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
        ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
            (realizeSymmCcTensor (I := I) g₀ S)).toSection x‖) :=
      (norm_toSection_eq_sqrt_riemannianFiberNormSq_installed (I := I) (M := M) g₀ 0 (2 + j)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (realizeSymmCcTensor (I := I) g₀ S)) x).symm
    rw [hhead]
    refine Finset.single_le_sum (f := fun j' =>
        (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + j') I bb) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j')
        ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j'
            (realizeSymmCcTensor (I := I) g₀ S)).toSection x‖))
      (fun j' _ => ?_) (Finset.mem_range.mpr hj)
    letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + j') I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j')
    exact norm_nonneg _
  have hrfns_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x
    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
      (realizeSymmCcTensor (I := I) g₀ S)).toSection x)
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (realizeSymmCcTensor (I := I) g₀ S)).toSection x)
      = Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
            (realizeSymmCcTensor (I := I) g₀ S)).toSection x)) ^ 2 :=
        (Real.sq_sqrt hrfns_nn).symm
    _ ≤ (Cemb * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a S‖) ^ 2 := by
        have hle : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (realizeSymmCcTensor (I := I) g₀ S)).toSection x)) ≤
            Cemb * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a S‖ :=
          le_trans hsqrt hjet
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2

set_option linter.unusedSectionVars false in
/-- **The uniform `C⁰` fibre-sup Lipschitz bound of the lowered connection-difference COCYCLE.**
The order-`0` fibre value of `lowered(g₁, g₀) − lowered(g₂, g₀)` is bounded at every point by a
constant times the order-`a` Sobolev mass `‖(T₁ − T₂).toHs a‖` of the perturbation difference —
the pointwise Neumann absorption of the bilinear-factorized cocycle: the Koszul-triple arm and the
`Φ(w, D₁)` arm are difference-small through the supercritical realized embedding, and the
`Φ(h₂, D₁ − D₂)` arm is `δ²`-absorbed by the sharp passenger bound (`4 − 16δ² > 0` on
`δ < 1/2`). -/
private theorem loweredConnDiff_cocycle_rfns_sup (g₀ : SmoothRiemannianMetric I M)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ CΛsq : ℝ, 0 ≤ CΛsq ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          g₂.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₂ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
              ((DeTurck.loweredConnDiffSection (I := I) g₁ g₀
                - DeTurck.loweredConnDiffSection (I := I) g₂ g₀).toSection x) ≤
            CΛsq * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a
                (T₁ - T₂)‖ ^ 2 := by
  classical
  obtain ⟨ΛD, hΛD0, hΛD⟩ := exists_loweredConnDiff_rfns_fibre_sup (I := I) g₀ hδ0 hδ1 B a ha
  obtain ⟨Cd0, hCd00, hCd0⟩ := contraction_rfns_fullWindowGrid_uniform (I := I) (M := M) g₀ 0
  obtain ⟨Cemb, hCemb0, hCemb⟩ := realized_diff_rfns_le_toHs (I := I) (M := M) g₀ a ha
  have hden : (0 : ℝ) < 4 - 16 * δ ^ 2 := by nlinarith
  refine ⟨(36 * Cemb ^ 2 + 16 * Cd0 * ΛD ^ 2 * Cemb ^ 2) / (4 - 16 * δ ^ 2), by positivity, ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
  have hball1a : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a T₁‖ ≤ B :=
    le_trans (toHs_norm_mono (I := I) (M := M) g₀ (by omega : a ≤ a + 2) T₁) hball1
  set Dn := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
    with hDn
  have hDn_nn : 0 ≤ Dn := norm_nonneg _
  set L₁ := DeTurck.loweredConnDiffSection (I := I) g₁ g₀ with hL₁
  set L₂ := DeTurck.loweredConnDiffSection (I := I) g₂ g₀ with hL₂
  set w := realizeSymmCcTensor (I := I) g₀ (T₁ - T₂) with hw
  set D₁p := DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2] L₁ with hD₁p
  set D₂p := DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2] L₂ with hD₂p
  set X := riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x ((L₁ - L₂).toSection x) with hX
  have hX_nn : 0 ≤ X := riemannianFiberNormSq_nonneg _ _ _ _ _
  -- The section-level cocycle identity.
  have hid : (2 : ℝ) • L₁ - (2 : ℝ) • L₂ =
      koszulTripleDiff (I := I) g₀ T₁ T₂
        - ((2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
          - (2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂) := by
    rw [hL₁, hL₂]
    exact DifferentialGeometry.PDE.DeTurck.loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff
      (I := I) g₀ g₁ g₂ T₁ T₂ hr1 hr2
  -- The bilinear factorization of the cross-correction difference.
  have hfact := crossCorrectionSectionDiff_eq_bilinearFactorization (I := I) (M := M)
    g₀ g₁ g₂ T₁ T₂
  -- Pointwise values.
  set Φ₁ := Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
    w D₁p with hΦ₁
  set Φ₂ := Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
    (realizeSymmCcTensor (I := I) g₀ T₂) (D₁p - D₂p) with hΦ₂
  -- `4X = rfns(2•L₁ − 2•L₂)`.
  have h2smul : (2 : ℝ) • L₁ - (2 : ℝ) • L₂ = (2 : ℝ) • (L₁ - L₂) := by
    rw [smul_sub]
  have h4X : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      (((2 : ℝ) • L₁ - (2 : ℝ) • L₂).toSection x) = 4 * X := by
    rw [h2smul]
    rw [show ((((2 : ℝ) • (L₁ - L₂)).toSection x) : TensorRSSpace 0 3 I x) =
        (2 : ℝ) • ((L₁ - L₂).toSection x) from by
      rw [Integral.L2.SmoothCcTensor.toSection_smul]; rfl]
    rw [show riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((2 : ℝ) • ((L₁ - L₂).toSection x)) =
        (2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          ((L₁ - L₂).toSection x) from by
      exact rfns_smul (I := I) (M := M) g₀ 0 3 x 2 ((L₁ - L₂).toSection x)]
    rw [← hX]; norm_num
  -- The K-arm and the two contraction arms, pointwise.
  have hKpt : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      ((koszulTripleDiff (I := I) g₀ T₁ T₂).toSection x) ≤ 18 * (Cemb * Dn) ^ 2 := by
    have h0 := koszulTriple_rfns_le' (I := I) (M := M) g₀ T₁ T₂ 0 x
    rw [show (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 0
        (koszulTripleDiff (I := I) g₀ T₁ T₂)) = koszulTripleDiff (I := I) g₀ T₁ T₂
      from rfl] at h0
    refine le_trans h0 ?_
    have h1 := hCemb (T₁ - T₂) 1 (by omega) x
    rw [← hDn] at h1
    nlinarith [h1]
  have hΦ₁pt : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x ((Φ₁ :
      Integral.L2.SmoothCcTensor g₀ 0 (3 + 0 + 0)).toSection x) ≤
      Cd0 * (ΛD ^ 2 * (Cemb * Dn) ^ 2) := by
    have hgrid := hCd0 w D₁p x
    rw [← hΦ₁] at hgrid
    have hsimp : (∑ i ∈ Finset.range (0 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i D₁p).toSection x)
          * ∑ l ∈ Finset.range (0 + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l w).toSection x)) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (D₁p.toSection x)
          * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (w.toSection x) := by
      rw [Finset.sum_range_one, Finset.sum_range_one]
      rfl
    rw [hsimp] at hgrid
    refine le_trans hgrid ?_
    have hD₁sup : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (D₁p.toSection x) ≤
        ΛD ^ 2 := by
      rw [hD₁p, rfns_permuteCcTensor_zero, hL₁]
      exact hΛD T₁ g₁ hr1 hfib1 hball1a x
    have hwsup : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (w.toSection x) ≤
        (Cemb * Dn) ^ 2 := by
      have h0 := hCemb (T₁ - T₂) 0 (by omega) x
      rw [← hDn] at h0
      rw [hw]
      exact h0
    have hwnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x (w.toSection x)
    have hDnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 3 x (D₁p.toSection x)
    have := mul_le_mul hD₁sup hwsup hwnn (by positivity)
    nlinarith [hCd00, this]
  have hΦ₂pt : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x ((Φ₂ :
      Integral.L2.SmoothCcTensor g₀ 0 (3 + 0 + 0)).toSection x) ≤ δ ^ 2 * X := by
    have hsharp := DeTurck.crossCorrParallelContraction_rfns_le_sq_passenger (I := I) g₀ 0
      T₂ hfib2 (D₁p - D₂p) x
    rw [← hΦ₂] at hsharp
    refine le_trans hsharp ?_
    have hpermsub : D₁p - D₂p =
        DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2] (L₁ - L₂) := by
      rw [hD₁p, hD₂p, permuteCcTensor_sub_local]
    rw [hpermsub, rfns_permuteCcTensor_zero, ← hX]
  -- Assemble the pointwise Neumann absorption.
  have hccpt : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      ((DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
        - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂).toSection x) ≤
      2 * (Cd0 * (ΛD ^ 2 * (Cemb * Dn) ^ 2)) + 2 * (δ ^ 2 * X) := by
    rw [hfact]
    rw [Integral.L2.SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 3 x _ _) ?_
    have h1 := hΦ₁pt
    have h2 := hΦ₂pt
    linarith
  have hidpt : (((2 : ℝ) • L₁ - (2 : ℝ) • L₂).toSection x : TensorRSSpace 0 3 I x) =
      (koszulTripleDiff (I := I) g₀ T₁ T₂).toSection x
        - (((2 : ℝ) • (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
            - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂)).toSection x) := by
    rw [hid]
    rw [show ((2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
        - (2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂)
        = (2 : ℝ) • (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
          - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂) from (smul_sub _ _ _).symm]
    rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  have h2cc : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      ((((2 : ℝ) • (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
          - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂)).toSection x)) =
      4 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
          - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂).toSection x) := by
    rw [show ((((2 : ℝ) • (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
        - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂)).toSection x) :
          TensorRSSpace 0 3 I x) =
        (2 : ℝ) • ((DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
          - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂).toSection x) from by
      rw [Integral.L2.SmoothCcTensor.toSection_smul]; rfl]
    rw [rfns_smul (I := I) (M := M) g₀ 0 3 x 2 _]
    norm_num
  have hmain : 4 * X ≤ 2 * (18 * (Cemb * Dn) ^ 2)
      + 2 * (4 * (2 * (Cd0 * (ΛD ^ 2 * (Cemb * Dn) ^ 2)) + 2 * (δ ^ 2 * X))) := by
    have hsub' := rfns_sub_le (I := I) (M := M) g₀ 0 3 x
      ((koszulTripleDiff (I := I) g₀ T₁ T₂).toSection x)
      ((((2 : ℝ) • (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
          - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂)).toSection x))
    rw [h2cc] at hsub'
    rw [← hidpt] at hsub'
    rw [h4X] at hsub'
    have hcc4 : 4 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
          - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂).toSection x) ≤
        4 * (2 * (Cd0 * (ΛD ^ 2 * (Cemb * Dn) ^ 2)) + 2 * (δ ^ 2 * X)) := by
      linarith [hccpt]
    linarith [hsub', hKpt, hcc4]
  -- Divide by the Neumann margin `4 − 16δ²`.
  have hkey : (4 - 16 * δ ^ 2) * X ≤
      (36 * Cemb ^ 2 + 16 * Cd0 * ΛD ^ 2 * Cemb ^ 2) * Dn ^ 2 := by
    nlinarith [hmain, hDn_nn, hX_nn]
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith [hkey]

set_option maxHeartbeats 12800000 in
set_option linter.unusedSectionVars false in
/-- **The integrated two-arm `L²`-jet bound of the lowered connection-difference COCYCLE**
(squared two-arm currency).  By strong induction on the order: the cocycle identity
`2•(L₁ − L₂) = koszulTriple(w) − 2•Φ(w, D₁) − 2•Φ(h₂, D₁ − D₂)`, the `18`-dominated Koszul arm,
the engine-integrated `Φ(w, D₁)` arm (with the single-metric low-ball fold on the `D₁`-jets), and
the `t`-scaled top/rest split on the `δ`-absorbed arm at the margin scale
`t = (1 − 4δ²)/(1 + 4δ²)` (absorption `16(1 + t)δ² < 4` on all of `δ < 1/2`). -/
private theorem loweredConnDiff_cocycle_jet_norm_sq_fold (g₀ : SmoothRiemannianMetric I M)
    (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          g₂.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₂ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (DeTurck.loweredConnDiffSection (I := I) g₁ g₀
                - DeTurck.loweredConnDiffSection (I := I) g₂ g₀)‖ ^ 2 ≤
          C * ((∑ i ∈ Finset.range (p + 1 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                  (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2)
            + ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a
                (T₁ - T₂)‖ ^ 2
              * ∑ l ∈ Finset.range (p + 1 + 1),
                  (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2
                    + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖ ^ 2)) := by
  classical
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    set μ := Integral.Measure.riemannianVolumeMeasure I M g₀ with hμ
    obtain ⟨Cpk, hCpk0, hCpk⟩ := contraction_topRest_split_uniform (I := I) (M := M) g₀ p δ hδ0
    obtain ⟨CΛsq, hCΛsq0, hCΛsq⟩ :=
      loweredConnDiff_cocycle_rfns_sup (I := I) (M := M) g₀ δ hδ0 hδ1 B a ha
    obtain ⟨Cemb, hCemb0, hCemb⟩ := realized_diff_rfns_le_toHs (I := I) (M := M) g₀ a ha
    obtain ⟨ΛD, hΛD0, hΛD⟩ := exists_loweredConnDiff_rfns_fibre_sup (I := I) g₀ hδ0 hδ1 B a ha
    obtain ⟨CdU, hCdU0, hCdU⟩ := contraction_rfns_fullWindowGrid_uniform (I := I) (M := M) g₀ p
    obtain ⟨Csym, hCsym0, hsym⟩ :=
      Analysis.Sobolev.Tensor.exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le
        (I := I) (M := M) g₀ 3 2 p
    obtain ⟨Cr2, hCr20, hCr2⟩ := realize_jet_norm_sq_sum_fold (I := I) (M := M) g₀ (p + 1)
    choose CT1 hCT10 hCT1 using fun i =>
      loweredConnDiff_jet_norm_sq_fold_low (I := I) (M := M) g₀ i δ hδ0 hδ1 B a ha
    have hih : ∀ q ∈ Finset.range p, ∃ Cq : ℝ, 0 ≤ Cq ∧
        ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
          (g₁ g₂ : SmoothRiemannianMetric I M),
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
          (∀ (y : M) (v w : TangentSpace I y),
            g₂.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₂ y v w) →
          gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
          gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                (DeTurck.loweredConnDiffSection (I := I) g₁ g₀
                  - DeTurck.loweredConnDiffSection (I := I) g₂ g₀)‖ ^ 2 ≤
            Cq * ((∑ i ∈ Finset.range (q + 1 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2)
              + ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a
                  (T₁ - T₂)‖ ^ 2
                * ∑ l ∈ Finset.range (q + 1 + 1),
                    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖ ^ 2)) :=
      fun q hq => ih q (Finset.mem_range.mp hq)
    choose! Cq hCq0 hCq using hih
    set t : ℝ := (1 - 4 * δ ^ 2) / (1 + 4 * δ ^ 2) with htdef
    have hδsq : 4 * δ ^ 2 < 1 := by nlinarith
    have hdenpos : (0 : ℝ) < 1 + 4 * δ ^ 2 := by positivity
    have ht0 : 0 < t := by
      rw [htdef]
      exact div_pos (by linarith) hdenpos
    have ht1 : t ≤ 1 := by
      rw [htdef, div_le_one hdenpos]
      nlinarith
    have habsorb : 16 * (1 + t) * δ ^ 2 < 4 := by
      have h1t : 1 + t = 2 / (1 + 4 * δ ^ 2) := by
        rw [htdef]
        field_simp
        ring
      rw [h1t]
      rw [show 16 * (2 / (1 + 4 * δ ^ 2)) * δ ^ 2 = (32 * δ ^ 2) / (1 + 4 * δ ^ 2) from by
        ring]
      rw [div_lt_iff₀ hdenpos]
      nlinarith
    have hmargin : (0 : ℝ) < 4 - 16 * (1 + t) * δ ^ 2 := by linarith
    set CsumT1 : ℝ := ∑ i ∈ Finset.range (p + 1), CT1 i with hCsumT1
    have hCsumT1_nn : 0 ≤ CsumT1 := Finset.sum_nonneg fun i _ => hCT10 i
    set CsumQ : ℝ := ∑ q ∈ Finset.range p, Cq q with hCsumQ
    have hCsumQ_nn : 0 ≤ CsumQ := Finset.sum_nonneg fun q hq => hCq0 q hq
    set Cbig : ℝ := 72 + 16 * (CdU * Csym * (Cemb ^ 2 * CsumT1 + ΛD ^ 2))
        + 16 * Cpk * (1 / t) ^ p * (CsumQ + CΛsq * Cr2) with hCbig
    have hCbig_nn : 0 ≤ Cbig := by
      rw [hCbig]
      positivity
    refine ⟨Cbig / (4 - 16 * (1 + t) * δ ^ 2), by positivity, ?_⟩
    intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2
    set Dn := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
      with hDn
    have hDn_nn : 0 ≤ Dn := norm_nonneg _
    set w := realizeSymmCcTensor (I := I) g₀ (T₁ - T₂) with hw
    set SW2 := ∑ i ∈ Finset.range (p + 1 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w‖ ^ 2 with hSW2
    set ST2 := ∑ l ∈ Finset.range (p + 1 + 1),
      (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2
        + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖ ^ 2) with hST2
    have hSW2_nn : 0 ≤ SW2 := Finset.sum_nonneg fun i _ => by positivity
    have hST2_nn : 0 ≤ ST2 := Finset.sum_nonneg fun l _ => by positivity
    set RHS0 := SW2 + Dn ^ 2 * ST2 with hRHS0
    have hRHS0_nn : 0 ≤ RHS0 := by rw [hRHS0]; positivity
    set L₁ := DeTurck.loweredConnDiffSection (I := I) g₁ g₀ with hL₁
    set L₂ := DeTurck.loweredConnDiffSection (I := I) g₂ g₀ with hL₂
    set D₁p := DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2] L₁ with hD₁p
    set D₂p := DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2] L₂ with hD₂p
    set Φ₁ := Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
      w D₁p with hΦ₁
    set Φ₂ := Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
      (realizeSymmCcTensor (I := I) g₀ T₂) (D₁p - D₂p) with hΦ₂
    set Ldp := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p (L₁ - L₂)‖ ^ 2 with hLdp
    have hLdp_nn : 0 ≤ Ldp := by rw [hLdp]; positivity
    -- The section-level cocycle identity, bilinear-factorized.
    have hsec : (2 : ℝ) • (L₁ - L₂) =
        (koszulTripleDiff (I := I) g₀ T₁ T₂ - (2 : ℝ) • Φ₁) - (2 : ℝ) • Φ₂ := by
      have hid := DifferentialGeometry.PDE.DeTurck.loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff
        (I := I) g₀ g₁ g₂ T₁ T₂ hr1 hr2
      have hfact := crossCorrectionSectionDiff_eq_bilinearFactorization (I := I) (M := M)
        g₀ g₁ g₂ T₁ T₂
      have h2cc : (2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
          - (2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂
          = (2 : ℝ) • Φ₁ + (2 : ℝ) • Φ₂ := by
        rw [← smul_sub, hfact, smul_add]
      rw [smul_sub]
      rw [show ((2 : ℝ) • L₁ - (2 : ℝ) • L₂ :
          Integral.L2.SmoothCcTensor g₀ 0 3) = koszulTripleDiff (I := I) g₀ T₁ T₂
            - ((2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
              - (2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂) from hid]
      rw [h2cc]
      abel
    have h4L : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          ((2 : ℝ) • (L₁ - L₂))‖ ^ 2 = 4 * Ldp := by
      rw [iteratedCovGrad_norm_sq_smul, hLdp]; norm_num
    have hsplit : 4 * Ldp ≤
        4 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
            (koszulTripleDiff (I := I) g₀ T₁ T₂)‖ ^ 2
        + 16 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p Φ₁‖ ^ 2
        + 8 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p Φ₂‖ ^ 2 := by
      have hle1 := iteratedCovGrad_norm_sq_sub_le (I := I) g₀ 3 p
        (koszulTripleDiff (I := I) g₀ T₁ T₂ - (2 : ℝ) • Φ₁) ((2 : ℝ) • Φ₂)
      have hle2 := iteratedCovGrad_norm_sq_sub_le (I := I) g₀ 3 p
        (koszulTripleDiff (I := I) g₀ T₁ T₂) ((2 : ℝ) • Φ₁)
      have h4Φ₁ : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p ((2 : ℝ) • Φ₁)‖ ^ 2 =
          4 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p Φ₁‖ ^ 2 := by
        rw [iteratedCovGrad_norm_sq_smul]; norm_num
      have h4Φ₂ : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p ((2 : ℝ) • Φ₂)‖ ^ 2 =
          4 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p Φ₂‖ ^ 2 := by
        rw [iteratedCovGrad_norm_sq_smul]; norm_num
      have hLrw : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          ((2 : ℝ) • (L₁ - L₂))‖ ^ 2 =
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
            ((koszulTripleDiff (I := I) g₀ T₁ T₂ - (2 : ℝ) • Φ₁) - (2 : ℝ) • Φ₂)‖ ^ 2 := by
        rw [hsec]
      rw [h4L] at hLrw
      rw [h4Φ₁] at hle2
      rw [h4Φ₂] at hle1
      linarith [hle1, hle2, hLrw.ge, hLrw.le]
    -- ARM 1: the Koszul arm.
    have hK : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          (koszulTripleDiff (I := I) g₀ T₁ T₂)‖ ^ 2 ≤ 18 * SW2 := by
      refine le_trans (koszulTriple_norm_sq_le' (I := I) (M := M) g₀ T₁ T₂ p) ?_
      have htop : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p + 1) w‖ ^ 2 ≤ SW2 := by
        rw [hSW2]
        exact Finset.single_le_sum
          (f := fun i => ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w‖ ^ 2)
          (fun i _ => by positivity) (Finset.mem_range.mpr (by omega))
      rw [← hw]
      nlinarith [htop]
    -- ARM 2: the `Φ(w, D₁)` arm through the symmetric engine.
    have hball1a : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a T₁‖
        ≤ B :=
      le_trans (toHs_norm_mono (I := I) (M := M) g₀ (by omega : a ≤ a + 2) T₁) hball1
    have hD₁sup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        (D₁p.toSection x) ≤ ΛD ^ 2 := by
      intro x
      rw [hD₁p, rfns_permuteCcTensor_zero, hL₁]
      exact hΛD T₁ g₁ hr1 hfib1 hball1a x
    have hwsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        (w.toSection x) ≤ (Cemb * Dn) ^ 2 := by
      intro x
      have h0 := hCemb (T₁ - T₂) 0 (by omega) x
      rw [← hDn] at h0
      rw [hw]
      exact h0
    obtain ⟨hint_sym, hsym'⟩ := hsym D₁p w ΛD (Cemb * Dn) hΛD0 (by positivity) hD₁sup hwsup
    have hΦ₁sq : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p Φ₁‖ ^ 2 ≤
        CdU * (Csym * ((Cemb * Dn) ^ 2 * ∑ i ∈ Finset.range (p + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i D₁p‖ ^ 2
          + ΛD ^ 2 * ∑ l ∈ Finset.range (p + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l w‖ ^ 2)) := by
      rw [normSq_eq_integral_rfns]
      calc (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 0 + 0 + p) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p Φ₁).toSection x) ∂μ)
          ≤ ∫ x, (CdU * ∑ i ∈ Finset.range (p + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i D₁p).toSection x)
                * ∑ l ∈ Finset.range (p + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l w).toSection x)) ∂μ := by
            refine MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun x => ?_)) (hint_sym.const_mul CdU)
              (Filter.Eventually.of_forall (fun x => ?_))
            · exact riemannianFiberNormSq_nonneg _ _ _ _ _
            · exact hCdU w D₁p x
        _ = CdU * ∫ x, (∑ i ∈ Finset.range (p + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i D₁p).toSection x)
                * ∑ l ∈ Finset.range (p + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l w).toSection x)) ∂μ := by
            rw [MeasureTheory.integral_const_mul]
        _ ≤ CdU * (Csym * ((Cemb * Dn) ^ 2 * ∑ i ∈ Finset.range (p + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i D₁p‖ ^ 2
            + ΛD ^ 2 * ∑ l ∈ Finset.range (p + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l w‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hsym' hCdU0
    have hD₁fold : (∑ i ∈ Finset.range (p + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i D₁p‖ ^ 2) ≤ CsumT1 * ST2 := by
      rw [hCsumT1, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have hperm : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i D₁p‖ ^ 2 =
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i L₁‖ ^ 2 := by
        rw [hD₁p]
        exact norm_sq_iteratedCovGrad_permute (I := I) (M := M) g₀ c[(0 : Fin 3), 1, 2] L₁ i
      rw [hperm, hL₁]
      refine le_trans (hCT1 i T₁ g₁ hr1 hfib1 hball1) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCT10 i)
      rw [hST2]
      calc (∑ l ∈ Finset.range (i + 1 + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2)
          ≤ ∑ l ∈ Finset.range (p + 1 + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.2
                (by have := Finset.mem_range.mp hi; omega))
              (fun l _ _ => by positivity)
        _ ≤ ∑ l ∈ Finset.range (p + 1 + 1),
            (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2
              + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖ ^ 2) :=
            Finset.sum_le_sum fun l _ => le_add_of_nonneg_right (by positivity)
    have hwfold : (∑ l ∈ Finset.range (p + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l w‖ ^ 2) ≤ SW2 := by
      rw [hSW2]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (by omega)) (fun l _ _ => by positivity)
    have hΦ₁final : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p Φ₁‖ ^ 2 ≤
        CdU * Csym * (Cemb ^ 2 * CsumT1 + ΛD ^ 2) * RHS0 := by
      refine le_trans hΦ₁sq ?_
      have h1 : (Cemb * Dn) ^ 2 * (∑ i ∈ Finset.range (p + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i D₁p‖ ^ 2) ≤
          Cemb ^ 2 * CsumT1 * (Dn ^ 2 * ST2) := by
        have h := mul_le_mul_of_nonneg_left hD₁fold
          (by positivity : (0 : ℝ) ≤ (Cemb * Dn) ^ 2)
        nlinarith [h]
      have h2 : ΛD ^ 2 * (∑ l ∈ Finset.range (p + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l w‖ ^ 2) ≤ ΛD ^ 2 * SW2 :=
        mul_le_mul_of_nonneg_left hwfold (by positivity)
      have hDnST_nn : 0 ≤ Dn ^ 2 * ST2 := by positivity
      have hinner : (Cemb * Dn) ^ 2 * (∑ i ∈ Finset.range (p + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i D₁p‖ ^ 2)
          + ΛD ^ 2 * (∑ l ∈ Finset.range (p + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l w‖ ^ 2) ≤
          (Cemb ^ 2 * CsumT1 + ΛD ^ 2) * RHS0 := by
        rw [hRHS0]
        nlinarith [h1, h2, hSW2_nn, hDnST_nn,
          mul_nonneg (mul_nonneg (sq_nonneg Cemb) hCsumT1_nn) hSW2_nn,
          mul_nonneg (sq_nonneg ΛD) hDnST_nn]
      calc CdU * (Csym * ((Cemb * Dn) ^ 2 * ∑ i ∈ Finset.range (p + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i D₁p‖ ^ 2
            + ΛD ^ 2 * ∑ l ∈ Finset.range (p + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l w‖ ^ 2))
          ≤ CdU * (Csym * ((Cemb ^ 2 * CsumT1 + ΛD ^ 2) * RHS0)) := by
            refine mul_le_mul_of_nonneg_left ?_ hCdU0
            exact mul_le_mul_of_nonneg_left hinner hCsym0
        _ = CdU * Csym * (Cemb ^ 2 * CsumT1 + ΛD ^ 2) * RHS0 := by ring
    -- ARM 3: the `Φ(h₂, D₁ − D₂)` arm through the `t`-scaled top/rest split.
    set ΛY : ℝ := Real.sqrt CΛsq * Dn with hΛY
    have hΛY0 : 0 ≤ ΛY := by rw [hΛY]; positivity
    have hYd_sub : D₁p - D₂p =
        DeTurck.permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2] (L₁ - L₂) := by
      rw [hD₁p, hD₂p, permuteCcTensor_sub_local]
    have hYdsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((D₁p - D₂p).toSection x) ≤ ΛY ^ 2 := by
      intro x
      rw [hYd_sub, rfns_permuteCcTensor_zero]
      have h := hCΛsq T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
      rw [← hDn] at h
      rw [hL₁, hL₂]
      refine le_trans h (le_of_eq ?_)
      rw [hΛY, mul_pow, Real.sq_sqrt hCΛsq0]
    have hYdnorm : ∀ q : ℕ,
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q (D₁p - D₂p)‖ ^ 2 =
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q (L₁ - L₂)‖ ^ 2 := by
      intro q
      rw [hYd_sub]
      exact norm_sq_iteratedCovGrad_permute (I := I) (M := M) g₀
        c[(0 : Fin 3), 1, 2] (L₁ - L₂) q
    have hΦ₂split := hCpk t ht0 ht1 T₂ (D₁p - D₂p) ΛY hΛY0 hfib2 hYdsup
    rw [← hΦ₂] at hΦ₂split
    rw [hYdnorm p, ← hLdp] at hΦ₂split
    have hlowfold : (∑ q ∈ Finset.range p,
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q (D₁p - D₂p)‖ ^ 2) ≤
        CsumQ * RHS0 := by
      rw [hCsumQ, Finset.sum_mul]
      refine Finset.sum_le_sum fun q hq => ?_
      rw [hYdnorm q, hL₁, hL₂]
      refine le_trans (hCq q hq T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCq0 q hq)
      rw [hRHS0, hSW2, hST2, ← hw, ← hDn]
      have hqp : q + 1 + 1 ≤ p + 1 + 1 := by
        have := Finset.mem_range.mp hq; omega
      have hsw : (∑ i ∈ Finset.range (q + 1 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w‖ ^ 2) ≤
          ∑ i ∈ Finset.range (p + 1 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 hqp) (fun l _ _ => by positivity)
      have hst : (∑ l ∈ Finset.range (q + 1 + 1),
          (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2
            + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖ ^ 2)) ≤
          ∑ l ∈ Finset.range (p + 1 + 1),
          (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2
            + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖ ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 hqp) (fun l _ _ => by positivity)
      nlinarith [hsw, hst, hDn_nn, sq_nonneg Dn]
    have hSw₂fold : (∑ i ∈ Finset.range (p + 1 + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ T₂)‖ ^ 2) ≤ Cr2 * ST2 := by
      refine le_trans (hCr2 T₂) ?_
      refine mul_le_mul_of_nonneg_left ?_ hCr20
      rw [hST2]
      exact Finset.sum_le_sum fun l _ => le_add_of_nonneg_left (by positivity)
    have hΦ₂final : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p Φ₂‖ ^ 2 ≤
        2 * (1 + t) * δ ^ 2 * Ldp
          + 2 * Cpk * (1 / t) ^ p * (CsumQ + CΛsq * Cr2) * RHS0 := by
      refine le_trans hΦ₂split ?_
      have hΛYsq : ΛY ^ 2 = CΛsq * Dn ^ 2 := by
        rw [hΛY, mul_pow, Real.sq_sqrt hCΛsq0]
      have hpiece : ΛY ^ 2 * (∑ i ∈ Finset.range (p + 1 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (realizeSymmCcTensor (I := I) g₀ T₂)‖ ^ 2) ≤
          CΛsq * Cr2 * (Dn ^ 2 * ST2) := by
        rw [hΛYsq]
        have h := mul_le_mul_of_nonneg_left hSw₂fold
          (by positivity : (0 : ℝ) ≤ CΛsq * Dn ^ 2)
        nlinarith [h]
      have hin : (∑ q ∈ Finset.range p,
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q (D₁p - D₂p)‖ ^ 2)
          + ΛY ^ 2 * (∑ i ∈ Finset.range (p + 1 + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
              (realizeSymmCcTensor (I := I) g₀ T₂)‖ ^ 2) ≤
          (CsumQ + CΛsq * Cr2) * RHS0 := by
        have hDnST_nn : 0 ≤ Dn ^ 2 * ST2 := by positivity
        have hRHS_split : Dn ^ 2 * ST2 ≤ RHS0 := by
          rw [hRHS0]; linarith [hSW2_nn]
        have h2 : CΛsq * Cr2 * (Dn ^ 2 * ST2) ≤ CΛsq * Cr2 * RHS0 :=
          mul_le_mul_of_nonneg_left hRHS_split (by positivity)
        nlinarith [hlowfold, hpiece, h2]
      have hfin : 2 * Cpk * (1 / t) ^ p * ((∑ q ∈ Finset.range p,
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q (D₁p - D₂p)‖ ^ 2)
          + ΛY ^ 2 * ∑ i ∈ Finset.range (p + 1 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ T₂)‖ ^ 2) ≤
          2 * Cpk * (1 / t) ^ p * ((CsumQ + CΛsq * Cr2) * RHS0) :=
        mul_le_mul_of_nonneg_left hin (by positivity)
      have heq : 2 * Cpk * (1 / t) ^ p * ((CsumQ + CΛsq * Cr2) * RHS0) =
          2 * Cpk * (1 / t) ^ p * (CsumQ + CΛsq * Cr2) * RHS0 := by ring
      linarith [hfin, heq.le, heq.ge]
    -- Close the recursion.
    have hSW2_le : SW2 ≤ RHS0 := by
      rw [hRHS0]
      have : 0 ≤ Dn ^ 2 * ST2 := by positivity
      linarith
    have hkey : (4 - 16 * (1 + t) * δ ^ 2) * Ldp ≤ Cbig * RHS0 := by
      have hexp : Cbig * RHS0 = 72 * RHS0
          + 16 * (CdU * Csym * (Cemb ^ 2 * CsumT1 + ΛD ^ 2)) * RHS0
          + 16 * Cpk * (1 / t) ^ p * (CsumQ + CΛsq * Cr2) * RHS0 := by
        rw [hCbig]; ring
      have hK72 : 4 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          (koszulTripleDiff (I := I) g₀ T₁ T₂)‖ ^ 2 ≤ 72 * RHS0 := by
        nlinarith [hK, hSW2_le]
      have hΦ₁16 : 16 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p Φ₁‖ ^ 2 ≤
          16 * (CdU * Csym * (Cemb ^ 2 * CsumT1 + ΛD ^ 2)) * RHS0 := by
        nlinarith [hΦ₁final]
      have hΦ₂8 : 8 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p Φ₂‖ ^ 2 ≤
          16 * (1 + t) * δ ^ 2 * Ldp
            + 16 * Cpk * (1 / t) ^ p * (CsumQ + CΛsq * Cr2) * RHS0 := by
        nlinarith [hΦ₂final]
      linarith [hsplit, hK72, hΦ₁16, hΦ₂8, hexp.le, hexp.ge]
    rw [div_mul_eq_mul_div, le_div_iff₀ hmargin]
    calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p (L₁ - L₂)‖ ^ 2
          * (4 - 16 * (1 + t) * δ ^ 2)
        = (4 - 16 * (1 + t) * δ ^ 2) * Ldp := by rw [← hLdp]; ring
      _ ≤ Cbig * RHS0 := hkey
      _ = Cbig * ((∑ i ∈ Finset.range (p + 1 + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w‖ ^ 2)
          + Dn ^ 2 * ∑ l ∈ Finset.range (p + 1 + 1),
              (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2
                + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖ ^ 2)) := by
          rw [hRHS0, hSW2, hST2]

set_option linter.unusedSectionVars false in
/-- **Nonneg term-square sum is at most the squared sum.**  `∑ fᵢ² ≤ (∑ fᵢ)²` for nonnegative
terms (each `fᵢ² ≤ fᵢ·∑f`). -/
private lemma sum_sq_le_sq_sum (n : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i ∈ Finset.range n, f i ^ 2) ≤ (∑ i ∈ Finset.range n, f i) ^ 2 := by
  have hsum_nn : 0 ≤ ∑ i ∈ Finset.range n, f i := Finset.sum_nonneg fun i _ => hf i
  calc (∑ i ∈ Finset.range n, f i ^ 2)
      ≤ ∑ i ∈ Finset.range n, f i * (∑ l ∈ Finset.range n, f l) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [pow_two]
        refine mul_le_mul_of_nonneg_left ?_ (hf i)
        exact Finset.single_le_sum (fun l _ => hf l) hi
    _ = (∑ i ∈ Finset.range n, f i) ^ 2 := by
        rw [← Finset.sum_mul, pow_two]

set_option linter.unusedSectionVars false in
/-- **The two-arm unsquaring.**  From the squared two-arm bound `N² ≤ C·(SW2 + Dn²·ST2)` with
`SW2 ≤ SW²`, `ST2 ≤ ST²`, the unsquared two-arm bound `N ≤ √C·SW + √C·Dn·ST`. -/
private lemma norm_le_two_arm_of_sq_le {N C SW2 ST2 Dn SW ST : ℝ}
    (hN : 0 ≤ N) (hC : 0 ≤ C) (hDn : 0 ≤ Dn) (hSW : 0 ≤ SW) (hST : 0 ≤ ST)
    (h2 : N ^ 2 ≤ C * (SW2 + Dn ^ 2 * ST2)) (hSW2 : SW2 ≤ SW ^ 2) (hST2 : ST2 ≤ ST ^ 2) :
    N ≤ Real.sqrt C * SW + Real.sqrt C * Dn * ST := by
  have hsq : N ^ 2 ≤ (Real.sqrt C * SW + Real.sqrt C * Dn * ST) ^ 2 := by
    have hCsq : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC
    have hexp : (Real.sqrt C * SW + Real.sqrt C * Dn * ST) ^ 2
        = Real.sqrt C ^ 2 * SW ^ 2 + 2 * (Real.sqrt C ^ 2 * SW * (Dn * ST))
          + Real.sqrt C ^ 2 * (Dn ^ 2 * ST ^ 2) := by ring
    rw [hCsq] at hexp
    have h1 : C * SW2 ≤ C * SW ^ 2 := mul_le_mul_of_nonneg_left hSW2 hC
    have h2' : C * (Dn ^ 2 * ST2) ≤ C * (Dn ^ 2 * ST ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hST2 (sq_nonneg Dn)) hC
    have hcross : 0 ≤ 2 * (C * SW * (Dn * ST)) := by positivity
    have hexp' : (Real.sqrt C * SW + Real.sqrt C * Dn * ST) ^ 2
        = C * SW ^ 2 + 2 * (C * SW * (Dn * ST)) + C * (Dn ^ 2 * ST ^ 2) := hexp
    have h2'' : N ^ 2 ≤ C * SW2 + C * (Dn ^ 2 * ST2) := by
      calc N ^ 2 ≤ C * (SW2 + Dn ^ 2 * ST2) := h2
        _ = C * SW2 + C * (Dn ^ 2 * ST2) := by ring
    rw [hexp]
    linarith
  have hrhs_nn : 0 ≤ Real.sqrt C * SW + Real.sqrt C * Dn * ST := by positivity
  calc N = Real.sqrt (N ^ 2) := (Real.sqrt_sq hN).symm
    _ ≤ Real.sqrt ((Real.sqrt C * SW + Real.sqrt C * Dn * ST) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt C * SW + Real.sqrt C * Dn * ST := Real.sqrt_sq hrhs_nn


set_option linter.unusedVariables false in
/-- **The integrated two-arm `L²` bound of the cross-correction SECTION difference (PROVEN).**
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
`exists_iteratedCovGradJetSum_le_toHs_sharpOrder` for the ball arm).  Its body is **proven**: the
cocycle identity reduces it to the Koszul-triple arm (`koszulTriple_norm_sq_le'`, the integrated
`18`-domination) plus the cocycle two-arm recursion
(`loweredConnDiff_cocycle_jet_norm_sq_fold`), itself closed by the `δ < 1/2` ε-Young absorption
over the generic `t`-scaled top/rest split (`contraction_topRest_split_uniform`) with the
single-metric low-ball Hamilton-tame fold (`loweredConnDiff_jet_norm_sq_fold_low`).  Consumers
transitively depend on `sorryAx` ONLY through the sharp keystone passenger posit
`crossCorrKeystoneTop_rfns_le_sq_passenger` (the lone remaining frontier cell of the redesign).

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
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖) := by
  classical
  obtain ⟨Cco, hCco0, hCco⟩ :=
    loweredConnDiff_cocycle_jet_norm_sq_fold (I := I) (M := M) g₀ p δ hδ0 hδ1 B a ha
  refine ⟨Real.sqrt (9 + 2 * Cco), Real.sqrt_nonneg _, ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2
  set w := realizeSymmCcTensor (I := I) g₀ (T₁ - T₂) with hw
  set Dn := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
    with hDn
  have hDn_nn : 0 ≤ Dn := norm_nonneg _
  set SW2 := ∑ i ∈ Finset.range (p + 1 + 1),
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w‖ ^ 2 with hSW2
  set ST2 := ∑ l ∈ Finset.range (p + 1 + 1),
    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2
      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖ ^ 2) with hST2
  have hSW2_nn : 0 ≤ SW2 := Finset.sum_nonneg fun i _ => by positivity
  have hST2_nn : 0 ≤ ST2 := Finset.sum_nonneg fun l _ => by positivity
  set L₁ := DeTurck.loweredConnDiffSection (I := I) g₁ g₀ with hL₁
  set L₂ := DeTurck.loweredConnDiffSection (I := I) g₂ g₀ with hL₂
  -- The squared two-arm bound of the section difference.
  have hccsq : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
          - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂)‖ ^ 2 ≤
      (9 + 2 * Cco) * (SW2 + Dn ^ 2 * ST2) := by
    -- `2•ccdiff = KT − 2•(L₁ − L₂)`.
    have hid := DifferentialGeometry.PDE.DeTurck.loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff
      (I := I) g₀ g₁ g₂ T₁ T₂ hr1 hr2
    have hsec : (2 : ℝ) • (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
        - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂) =
        koszulTripleDiff (I := I) g₀ T₁ T₂ - (2 : ℝ) • (L₁ - L₂) := by
      have h1 : (2 : ℝ) • L₁ - (2 : ℝ) • L₂ = (2 : ℝ) • (L₁ - L₂) := (smul_sub _ _ _).symm
      have h2 : (2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
          - (2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂
          = (2 : ℝ) • (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
            - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂) := (smul_sub _ _ _).symm
      have hid' : (2 : ℝ) • (L₁ - L₂) =
          koszulTripleDiff (I := I) g₀ T₁ T₂
            - (2 : ℝ) • (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
              - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂) := by
        rw [← h1, ← h2]
        exact hid
      rw [hid']
      abel
    have h4N : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          ((2 : ℝ) • (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
            - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂))‖ ^ 2 =
        4 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
            - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂)‖ ^ 2 := by
      rw [iteratedCovGrad_norm_sq_smul]; norm_num
    have h4Ld : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          ((2 : ℝ) • (L₁ - L₂))‖ ^ 2 =
        4 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p (L₁ - L₂)‖ ^ 2 := by
      rw [iteratedCovGrad_norm_sq_smul]; norm_num
    have hle := iteratedCovGrad_norm_sq_sub_le (I := I) g₀ 3 p
      (koszulTripleDiff (I := I) g₀ T₁ T₂) ((2 : ℝ) • (L₁ - L₂))
    have hLrw : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        ((2 : ℝ) • (DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
          - DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂))‖ ^ 2 =
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          (koszulTripleDiff (I := I) g₀ T₁ T₂ - (2 : ℝ) • (L₁ - L₂))‖ ^ 2 := by
      rw [hsec]
    rw [h4N] at hLrw
    rw [h4Ld] at hle
    -- The Koszul arm and the cocycle arm.
    have hK : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          (koszulTripleDiff (I := I) g₀ T₁ T₂)‖ ^ 2 ≤ 18 * SW2 := by
      refine le_trans (koszulTriple_norm_sq_le' (I := I) (M := M) g₀ T₁ T₂ p) ?_
      have htop : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p + 1) w‖ ^ 2 ≤ SW2 := by
        rw [hSW2]
        exact Finset.single_le_sum
          (f := fun i => ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w‖ ^ 2)
          (fun i _ => by positivity) (Finset.mem_range.mpr (by omega))
      rw [← hw]
      nlinarith [htop]
    have hLd := hCco T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2
    rw [← hw, ← hDn, ← hSW2, ← hST2] at hLd
    rw [show DeTurck.loweredConnDiffSection (I := I) g₁ g₀
        - DeTurck.loweredConnDiffSection (I := I) g₂ g₀ = L₁ - L₂ from by
      rw [hL₁, hL₂]] at hLd
    have hRHS0_nn : 0 ≤ SW2 + Dn ^ 2 * ST2 := by positivity
    nlinarith [hle, hLrw.le, hLrw.ge, hK, hLd, hSW2_nn, hCco0, hRHS0_nn]
  -- Unsquare into the two unsquared arms.
  set SW := ∑ i ∈ Finset.range (p + 2),
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w‖ with hSW
  set ST := ∑ l ∈ Finset.range (p + 2),
    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖
      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖) with hST
  have hSW_nn : 0 ≤ SW := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hST_nn : 0 ≤ ST := Finset.sum_nonneg fun l _ =>
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hSW2le : SW2 ≤ SW ^ 2 := by
    rw [hSW2, hSW, show p + 1 + 1 = p + 2 from by omega]
    exact sum_sq_le_sq_sum (p + 2)
      (fun i => ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w‖)
      (fun i => norm_nonneg _)
  have hST2le : ST2 ≤ ST ^ 2 := by
    rw [hST2, hST, show p + 1 + 1 = p + 2 from by omega]
    calc (∑ l ∈ Finset.range (p + 2),
          (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2
            + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖ ^ 2))
        ≤ ∑ l ∈ Finset.range (p + 2),
          (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖
            + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖) ^ 2 := by
          refine Finset.sum_le_sum fun l _ => ?_
          nlinarith [norm_nonneg (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁),
            norm_nonneg (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂)]
      _ ≤ (∑ l ∈ Finset.range (p + 2),
          (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖
            + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖)) ^ 2 :=
          sum_sq_le_sq_sum (p + 2) _ (fun l =>
            add_nonneg (norm_nonneg _) (norm_nonneg _))
  exact norm_le_two_arm_of_sq_le (norm_nonneg _) (by positivity) hDn_nn hSW_nn hST_nn
    hccsq hSW2le hST2le

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

set_option maxHeartbeats 12800000 in
set_option linter.unusedVariables false in
/-- **The integrated two-arm `L²` bound of the quadratic Cross section (PROVEN).**  The metric
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
integrated Gagliardo–Nirenberg absorption.  Its body is **proven**: the structural bridge
`crossSection_eq_cometricDoubleDoubleTrace_loweredCocycleProduct` exposes the polarized carrier,
the section-uniform cocycle-telescope grid
(`cometricQuadraticTraceProduct_iteratedCovGrad_rfns_cocycleTelescope_fullWindowProductGrid_le`)
integrates through the symmetric Gagliardo–Nirenberg engine, and the two folds
(`loweredConnDiff_cocycle_jet_norm_sq_fold`, `loweredConnDiff_jet_norm_sq_fold_low`) land the two
Hamilton-tame arms.  Consumers transitively depend on `sorryAx` ONLY through the sharp keystone
passenger posit `crossCorrKeystoneTop_rfns_le_sq_passenger`.

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
                      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖) := by
  classical
  set μ := Integral.Measure.riemannianVolumeMeasure I M g₀ with hμ
  obtain ⟨Cq1, hCq10, hCq1⟩ :=
    Integral.Connection.cometricQuadraticTraceProduct_iteratedCovGrad_rfns_cocycleTelescope_fullWindowProductGrid_le
      (I := I) (M := M) g₀ crossTracePerm1 j
  obtain ⟨Cq2, hCq20, hCq2⟩ :=
    Integral.Connection.cometricQuadraticTraceProduct_iteratedCovGrad_rfns_cocycleTelescope_fullWindowProductGrid_le
      (I := I) (M := M) g₀ crossTracePerm2 j
  obtain ⟨Csym, hCsym0, hsym⟩ :=
    Analysis.Sobolev.Tensor.exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le
      (I := I) (M := M) g₀ 3 3 j
  obtain ⟨ΛD, hΛD0, hΛD⟩ := exists_loweredConnDiff_rfns_fibre_sup (I := I) g₀ hδ0 hδ1 B a ha
  obtain ⟨CΛsq, hCΛsq0, hCΛsq⟩ :=
    loweredConnDiff_cocycle_rfns_sup (I := I) (M := M) g₀ δ hδ0 hδ1 B a ha
  choose Cco hCco0 hCco using fun i =>
    loweredConnDiff_cocycle_jet_norm_sq_fold (I := I) (M := M) g₀ i δ hδ0 hδ1 B a ha
  choose CT1 hCT10 hCT1 using fun l =>
    loweredConnDiff_jet_norm_sq_fold_low (I := I) (M := M) g₀ l δ hδ0 hδ1 B a ha
  set CcoS : ℝ := ∑ i ∈ Finset.range (j + 1), Cco i with hCcoS
  have hCcoS_nn : 0 ≤ CcoS := Finset.sum_nonneg fun i _ => hCco0 i
  set CT1S : ℝ := ∑ l ∈ Finset.range (j + 1), CT1 l with hCT1S
  have hCT1S_nn : 0 ≤ CT1S := Finset.sum_nonneg fun l _ => hCT10 l
  set Ctot : ℝ := 16 * (Cq1 + Cq2) * Csym * (ΛD ^ 2 * CcoS + CΛsq * CT1S) with hCtot
  have hCtot_nn : 0 ≤ Ctot := by
    rw [hCtot]
    positivity
  refine ⟨Real.sqrt Ctot, Real.sqrt_nonneg _, ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2
  have hball1a : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a T₁‖ ≤ B :=
    le_trans (toHs_norm_mono (I := I) (M := M) g₀ (by omega : a ≤ a + 2) T₁) hball1
  have hball2a : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a T₂‖ ≤ B :=
    le_trans (toHs_norm_mono (I := I) (M := M) g₀ (by omega : a ≤ a + 2) T₂) hball2
  set Dn := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖
    with hDn
  have hDn_nn : 0 ≤ Dn := norm_nonneg _
  set w := realizeSymmCcTensor (I := I) g₀ (T₁ - T₂) with hw
  set L₁ := DeTurck.loweredConnDiffSection (I := I) g₁ g₀ with hL₁
  set L₂ := DeTurck.loweredConnDiffSection (I := I) g₂ g₀ with hL₂
  -- The window-`(j+2)` squared jet sums (the folds' currency).
  set SW2 := ∑ i ∈ Finset.range (j + 2 + 1),
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w‖ ^ 2 with hSW2
  set ST2 := ∑ l ∈ Finset.range (j + 2 + 1),
    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2
      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖ ^ 2) with hST2
  have hSW2_nn : 0 ≤ SW2 := Finset.sum_nonneg fun i _ => by positivity
  have hST2_nn : 0 ≤ ST2 := Finset.sum_nonneg fun l _ => by positivity
  set RHS0 := SW2 + Dn ^ 2 * ST2 with hRHS0
  have hRHS0_nn : 0 ≤ RHS0 := by rw [hRHS0]; positivity
  -- The two engine instances (one per fixed endpoint).
  have hLdiffsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      ((L₁ - L₂).toSection x) ≤ (Real.sqrt CΛsq * Dn) ^ 2 := by
    intro x
    have h := hCΛsq T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
    rw [← hDn] at h
    rw [hL₁, hL₂]
    refine le_trans h (le_of_eq ?_)
    rw [mul_pow, Real.sq_sqrt hCΛsq0]
  have hL₁sup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      (L₁.toSection x) ≤ ΛD ^ 2 := by
    intro x
    rw [hL₁]
    exact hΛD T₁ g₁ hr1 hfib1 hball1a x
  have hL₂sup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      (L₂.toSection x) ≤ ΛD ^ 2 := by
    intro x
    rw [hL₂]
    exact hΛD T₂ g₂ hr2 hfib2 hball2a x
  obtain ⟨hint1, heng1⟩ := hsym (L₁ - L₂) L₁ (Real.sqrt CΛsq * Dn) ΛD
    (by positivity) hΛD0 hLdiffsup hL₁sup
  obtain ⟨hint2, heng2⟩ := hsym (L₁ - L₂) L₂ (Real.sqrt CΛsq * Dn) ΛD
    (by positivity) hΛD0 hLdiffsup hL₂sup
  -- The jet-sum folds.
  have hLdifffold : (∑ i ∈ Finset.range (j + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i (L₁ - L₂)‖ ^ 2) ≤ CcoS * RHS0 := by
    rw [hCcoS, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [hL₁, hL₂]
    refine le_trans (hCco i T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCco0 i)
    rw [hRHS0, hSW2, hST2, ← hw, ← hDn]
    have hii : i + 1 + 1 ≤ j + 2 + 1 := by
      have := Finset.mem_range.mp hi; omega
    have hsw : (∑ i' ∈ Finset.range (i + 1 + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i' w‖ ^ 2) ≤
        ∑ i' ∈ Finset.range (j + 2 + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i' w‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 hii) (fun l _ _ => by positivity)
    have hst : (∑ l ∈ Finset.range (i + 1 + 1),
        (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2
          + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖ ^ 2)) ≤
        ∑ l ∈ Finset.range (j + 2 + 1),
        (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2
          + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖ ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 hii) (fun l _ _ => by positivity)
    nlinarith [hsw, hst, sq_nonneg Dn]
  have hL₁fold : (∑ l ∈ Finset.range (j + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l L₁‖ ^ 2) ≤ CT1S * ST2 := by
    rw [hCT1S, Finset.sum_mul]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [hL₁]
    refine le_trans (hCT1 l T₁ g₁ hr1 hfib1 hball1) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCT10 l)
    rw [hST2]
    calc (∑ l' ∈ Finset.range (l + 1 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l' T₁‖ ^ 2)
        ≤ ∑ l' ∈ Finset.range (j + 2 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l' T₁‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.2
              (by have := Finset.mem_range.mp hl; omega))
            (fun l' _ _ => by positivity)
      _ ≤ ∑ l' ∈ Finset.range (j + 2 + 1),
          (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l' T₁‖ ^ 2
            + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l' T₂‖ ^ 2) :=
          Finset.sum_le_sum fun l' _ => le_add_of_nonneg_right (by positivity)
  have hL₂fold : (∑ l ∈ Finset.range (j + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l L₂‖ ^ 2) ≤ CT1S * ST2 := by
    rw [hCT1S, Finset.sum_mul]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [hL₂]
    refine le_trans (hCT1 l T₂ g₂ hr2 hfib2 hball2) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCT10 l)
    rw [hST2]
    calc (∑ l' ∈ Finset.range (l + 1 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l' T₂‖ ^ 2)
        ≤ ∑ l' ∈ Finset.range (j + 2 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l' T₂‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.2
              (by have := Finset.mem_range.mp hl; omega))
            (fun l' _ _ => by positivity)
      _ ≤ ∑ l' ∈ Finset.range (j + 2 + 1),
          (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l' T₁‖ ^ 2
            + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l' T₂‖ ^ 2) :=
          Finset.sum_le_sum fun l' _ => le_add_of_nonneg_left (by positivity)
  -- The per-arm `L²` bound: each of the two engine readings lands in `Csym·(…)·RHS0`.
  have hArm : ∀ (Lk : Integral.L2.SmoothCcTensor g₀ 0 3),
      (∑ l ∈ Finset.range (j + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l Lk‖ ^ 2) ≤ CT1S * ST2 →
      Csym * (ΛD ^ 2 * ∑ i ∈ Finset.range (j + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i (L₁ - L₂)‖ ^ 2
        + (Real.sqrt CΛsq * Dn) ^ 2 * ∑ l ∈ Finset.range (j + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l Lk‖ ^ 2) ≤
      Csym * (ΛD ^ 2 * CcoS + CΛsq * CT1S) * RHS0 := by
    intro Lk hfold
    have h1 : ΛD ^ 2 * (∑ i ∈ Finset.range (j + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i (L₁ - L₂)‖ ^ 2) ≤
        ΛD ^ 2 * (CcoS * RHS0) :=
      mul_le_mul_of_nonneg_left hLdifffold (by positivity)
    have h2 : (Real.sqrt CΛsq * Dn) ^ 2 * (∑ l ∈ Finset.range (j + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l Lk‖ ^ 2) ≤
        CΛsq * CT1S * (Dn ^ 2 * ST2) := by
      rw [mul_pow, Real.sq_sqrt hCΛsq0]
      have h := mul_le_mul_of_nonneg_left hfold
        (by positivity : (0 : ℝ) ≤ CΛsq * Dn ^ 2)
      nlinarith [h]
    have h2' : CΛsq * CT1S * (Dn ^ 2 * ST2) ≤ CΛsq * CT1S * RHS0 := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hRHS0]
      linarith [hSW2_nn]
    have hinner : ΛD ^ 2 * (∑ i ∈ Finset.range (j + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i (L₁ - L₂)‖ ^ 2)
        + (Real.sqrt CΛsq * Dn) ^ 2 * (∑ l ∈ Finset.range (j + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l Lk‖ ^ 2) ≤
        (ΛD ^ 2 * CcoS + CΛsq * CT1S) * RHS0 := by
      nlinarith [h1, h2, h2', hRHS0_nn]
    calc Csym * (ΛD ^ 2 * ∑ i ∈ Finset.range (j + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i (L₁ - L₂)‖ ^ 2
          + (Real.sqrt CΛsq * Dn) ^ 2 * ∑ l ∈ Finset.range (j + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l Lk‖ ^ 2)
        ≤ Csym * ((ΛD ^ 2 * CcoS + CΛsq * CT1S) * RHS0) :=
          mul_le_mul_of_nonneg_left hinner hCsym0
      _ = Csym * (ΛD ^ 2 * CcoS + CΛsq * CT1S) * RHS0 := by ring
  -- The squared `L²` bound of each traced permuted polarized arm.
  have hTrace : ∀ (σ : Equiv.Perm (Fin 6)) (Cqσ : ℝ), 0 ≤ Cqσ →
      (∀ (A₁ A₂ : Integral.L2.SmoothCcTensor g₀ 0 3) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                (Integral.Connection.cometricDoubleTraceRecOp (I := I) g₀ 2 0
                  (Integral.Connection.cometricDoubleTraceRecOp (I := I) g₀ 4 0
                    (DeTurck.permuteCcTensor (I := I) g₀ σ
                      (Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0)
                          (A₁ - A₂) A₁
                        + Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0)
                          A₂ (A₁ - A₂)))))).toSection x) ≤
          Cqσ * ∑ i ∈ Finset.range (j + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i (A₁ - A₂)).toSection x)
                * ∑ l ∈ Finset.range (j + 1 - i),
                    (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l A₁).toSection x)
                      + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l A₂).toSection x))) →
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (cometricDoubleDoubleTrace (I := I) g₀
            (DeTurck.permuteCcTensor (I := I) g₀ σ
              (crossProductPolarized (I := I) g₀ g₁ g₂)))‖ ^ 2 ≤
        Cqσ * (2 * (Csym * (ΛD ^ 2 * CcoS + CΛsq * CT1S) * RHS0)) := by
    intro σ Cqσ hCqσ0 hgrid
    -- The RecOp spelling of the twice-applied double trace on the polarized carrier.
    have hspell : cometricDoubleDoubleTrace (I := I) g₀
        (DeTurck.permuteCcTensor (I := I) g₀ σ
          (crossProductPolarized (I := I) g₀ g₁ g₂)) =
        Integral.Connection.cometricDoubleTraceRecOp (I := I) g₀ 2 0
          (Integral.Connection.cometricDoubleTraceRecOp (I := I) g₀ 4 0
            (DeTurck.permuteCcTensor (I := I) g₀ σ
              (Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0)
                  (L₁ - L₂) L₁
                + Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0)
                  L₂ (L₁ - L₂)))) := rfl
    rw [hspell]
    -- Integrate the pointwise cocycle grid, splitting the pair sum into the two engine halves.
    rw [normSq_eq_integral_rfns]
    have hgridx := fun x => hgrid L₁ L₂ x
    have hsplitpt : ∀ x : M, (∑ i ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i (L₁ - L₂)).toSection x)
          * ∑ l ∈ Finset.range (j + 1 - i),
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l L₁).toSection x)
                + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l L₂).toSection x))) =
        (∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i (L₁ - L₂)).toSection x)
            * ∑ l ∈ Finset.range (j + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l L₁).toSection x))
        + ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i (L₁ - L₂)).toSection x)
            * ∑ l ∈ Finset.range (j + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l L₂).toSection x) := by
      intro x
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_add_distrib, mul_add]
    calc (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (Integral.Connection.cometricDoubleTraceRecOp (I := I) g₀ 2 0
                (Integral.Connection.cometricDoubleTraceRecOp (I := I) g₀ 4 0
                  (DeTurck.permuteCcTensor (I := I) g₀ σ
                    (Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0)
                        (L₁ - L₂) L₁
                      + Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0)
                        L₂ (L₁ - L₂)))))).toSection x) ∂μ)
        ≤ ∫ x, (Cqσ * ((∑ i ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i (L₁ - L₂)).toSection x)
              * ∑ l ∈ Finset.range (j + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l L₁).toSection x))
          + ∑ i ∈ Finset.range (j + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i (L₁ - L₂)).toSection x)
                * ∑ l ∈ Finset.range (j + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l L₂).toSection x))) ∂μ := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun x => ?_))
            ((hint1.add hint2).const_mul Cqσ)
            (Filter.Eventually.of_forall (fun x => ?_))
          · exact riemannianFiberNormSq_nonneg _ _ _ _ _
          · refine le_trans (hgridx x) (le_of_eq ?_)
            rw [hsplitpt x]
      _ = Cqσ * ((∫ x, (∑ i ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i (L₁ - L₂)).toSection x)
              * ∑ l ∈ Finset.range (j + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l L₁).toSection x)) ∂μ)
          + ∫ x, (∑ i ∈ Finset.range (j + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i (L₁ - L₂)).toSection x)
                * ∑ l ∈ Finset.range (j + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 l L₂).toSection x)) ∂μ) := by
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hint1 hint2]
      _ ≤ Cqσ * (2 * (Csym * (ΛD ^ 2 * CcoS + CΛsq * CT1S) * RHS0)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCqσ0
          have hb1 := le_trans heng1 (hArm L₁ hL₁fold)
          have hb2 := le_trans heng2 (hArm L₂ hL₂fold)
          linarith
  have hT1 := hTrace crossTracePerm1 Cq1 hCq10 hCq1
  have hT2 := hTrace crossTracePerm2 Cq2 hCq20 hCq2
  -- Assemble the `−2`-scaled antisymmetrised pair.
  have hcrossSq : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
        (crossSection (I := I) g₀ g₁ g₂)‖ ^ 2 ≤ Ctot * RHS0 := by
    have hidc := crossSection_eq_cometricDoubleDoubleTrace_loweredCocycleProduct
      (I := I) g₀ g₁ g₂
    set A₁ := cometricDoubleDoubleTrace (I := I) g₀
      (DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm1
        (crossProductPolarized (I := I) g₀ g₁ g₂)) with hA₁
    set A₂ := cometricDoubleDoubleTrace (I := I) g₀
      (DeTurck.permuteCcTensor (I := I) g₀ crossTracePerm2
        (crossProductPolarized (I := I) g₀ g₁ g₂)) with hA₂
    have h4 : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (crossSection (I := I) g₀ g₁ g₂)‖ ^ 2 =
        4 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (A₁ - A₂)‖ ^ 2 := by
      rw [show crossSection (I := I) g₀ g₁ g₂ = (-2 : ℝ) • (A₁ - A₂) from hidc]
      rw [iteratedCovGrad_norm_sq_smul]
      norm_num
    have hsub := iteratedCovGrad_norm_sq_sub_le (I := I) g₀ 2 j A₁ A₂
    rw [h4]
    have hctot : 4 * (2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j A₁‖ ^ 2
        + 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j A₂‖ ^ 2) ≤ Ctot * RHS0 := by
      have hb1 : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j A₁‖ ^ 2 ≤
          Cq1 * (2 * (Csym * (ΛD ^ 2 * CcoS + CΛsq * CT1S) * RHS0)) := hT1
      have hb2 : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j A₂‖ ^ 2 ≤
          Cq2 * (2 * (Csym * (ΛD ^ 2 * CcoS + CΛsq * CT1S) * RHS0)) := hT2
      have hCtoteq : Ctot * RHS0 = 16 * Cq1 * (Csym * (ΛD ^ 2 * CcoS + CΛsq * CT1S) * RHS0)
          + 16 * Cq2 * (Csym * (ΛD ^ 2 * CcoS + CΛsq * CT1S) * RHS0) := by
        rw [hCtot]; ring
      linarith [hb1, hb2, hCtoteq.le, hCtoteq.ge]
    have hLdsub : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (A₁ - A₂)‖ ^ 2 ≤
        2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j A₁‖ ^ 2
          + 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j A₂‖ ^ 2 := by
      rw [PDE.RicciFlow.iteratedCovGrad_sub] at hsub ⊢
      exact hsub
    linarith [hLdsub, hctot]
  -- Unsquare.
  set SW := ∑ i ∈ Finset.range (j + 2 + 1),
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w‖ with hSW
  set ST := ∑ l ∈ Finset.range (j + 2 + 1),
    (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖
      + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖) with hST
  have hSW_nn : 0 ≤ SW := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hST_nn : 0 ≤ ST := Finset.sum_nonneg fun l _ =>
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hSW2le : SW2 ≤ SW ^ 2 := by
    rw [hSW2, hSW]
    exact sum_sq_le_sq_sum (j + 2 + 1)
      (fun i => ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w‖)
      (fun i => norm_nonneg _)
  have hST2le : ST2 ≤ ST ^ 2 := by
    rw [hST2, hST]
    calc (∑ l ∈ Finset.range (j + 2 + 1),
          (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖ ^ 2
            + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖ ^ 2))
        ≤ ∑ l ∈ Finset.range (j + 2 + 1),
          (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖
            + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖) ^ 2 := by
          refine Finset.sum_le_sum fun l _ => ?_
          nlinarith [norm_nonneg (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁),
            norm_nonneg (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂)]
      _ ≤ (∑ l ∈ Finset.range (j + 2 + 1),
          (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁‖
            + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₂‖)) ^ 2 :=
          sum_sq_le_sq_sum (j + 2 + 1) _ (fun l =>
            add_nonneg (norm_nonneg _) (norm_nonneg _))
  exact norm_le_two_arm_of_sq_le (norm_nonneg _) hCtot_nn hDn_nn hSW_nn hST_nn
    hcrossSq hSW2le hST2le

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
