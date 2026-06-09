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

The genuine covariant-Faà-di-Bruno content beneath the difference-arm leaf is the **curvature-trace
covariant-Leibniz reduction**: the rank-`2` order-`j` covariant jet of `linearSection` is dominated by
the rank-`3` order-`≤ j + 1` covariant jets of the connection-level realized covariant gradient `R`
(the trace, the cocycle, and the metric-built `≤2`-jet coefficient folded into a family-uniform
constant `Cd`).  This is the connection-difference covariant-jet machinery of
`ConnectionDifferenceFieldJets.lean` (`koszulCombSection_iteratedCovGrad_rfns_le`,
`loweredConnDiffSection`) lifted through the curvature trace and the two-metric cocycle; that lift — the
curvature-trace covariant-Leibniz reduction of the difference-normal-form section to the connection
level — is genuinely absent on disk for the *difference* curvature (the connection-level file is
single-metric, rank-`3`).  Per the project's assume-and-recurse discipline, the reduction
`ricciLinearSection_covGrad_traceReduction_rfns_le` posits exactly this genuinely-missing covariant-FdB
content as the honest atomic boundary just below the leaf.

The reduction is **structurally distinct** from, and **strictly smaller** than, the consumer leaf: its
right-hand side is the **connection-level** `∇^{≤ j+1} R` jet sum (rank `3`, the `∇w`-level), not the
leaf's `∇^{≤ j+2} w` jet sum; the difference-arm leaf is then proved by composing this reduction with
the **sorry-free** rank-shift `rfns(∇^p R) = rfns(∇^{p+1} w)` (the front-commutation
`iteratedCovGrad_covGrad_comm_heq`, `R = covGrad g₀ 0 2 w`) and the window inclusion
`∑_{p ≤ j+1} rfns(∇^{p+1} w) ≤ ∑_{i ≤ j+2} rfns(∇^i w)`.  The reduction is **non-vacuous** (it carries
the connection-level high derivative `∇^{j+1} R`, so a zero constant falsifies it whenever the linear
part is genuinely present — `linearSection_self_toModel` shows it vanishes only when `g₁ = g₂`), and
carries no value-bounded `Φ.op 0 2 w` shape (the refuted structural split), NO pointwise-`C^{>2}`-jet
claim, NO spectral-nonlinearity, and NO Weyl dependence. -/

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
A `(0, 3)`-section, the input of the model-basis Ricci trace's difference arm. -/
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
`(0, 3)`-section, the input of the model-basis Ricci trace's cross arm. -/
private def crossCorrTripleDiff (g₀ : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ g₂ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 3 :=
  (2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₁ g₀ T₁
    - (2 : ℝ) • DeTurck.crossCorrectionSection (I := I) g₂ g₀ T₂

/-- **The model-fibre rank cast `Tensor0SModel m → Tensor0SModel n` along `h : m = n`.**  The
continuous-linear (isometric) reindex of the model multilinear fibre, via
`ContinuousMultilinearMap.domDomCongrₗᵢ (finCongr h)`.  Used to chain the two leading-slot interior
products of the model-basis double trace across the `Nat`-equalities `4 + a = (3 + a) + 1` and
`3 + a = (2 + a) + 1` (which hold by `omega` but not `rfl`, as `Nat.add` recurses on the right). -/
noncomputable def modelRankCast {m n : ℕ} (h : m = n) :
    Tensor0SBundle.Tensor0SModel m ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E :=
  (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
    (finCongr h)).toContinuousLinearEquiv.toContinuousLinearMap

/-- **The `−2` double-trace map against a vector tuple `(0, 4 + a) → (0, 2 + a)`.**  The model-level
continuous-linear map on the model fibre `Tensor0SModel` that contracts the leading two of the `4 + a`
model slots of a model `(0, 4 + a)`-tensor against a *given* tuple of vectors `vᵢ ∈ E` (feeding `vᵢ`
into the two leading slots via two iterated `model_interior_product` interior products) and sums over
`i`, scaled by `−2`:
```
modelTrace42MapVec a v D = (-2) • ∑ᵢ D(vᵢ, vᵢ, ·).
```
The two interior products `model_interior_product (2 + a) vᵢ ∘ model_interior_product (3 + a) vᵢ`
feed `vᵢ` into the first two model slots (chained across the slot-count rank casts `modelRankCast`);
the outer sum runs over the index set.  When `vᵢ := ♯ eᵢ` is the `g₀`-raised `E`-orthonormal coframe
`eᵢ := chartModelBasis E i` (the cometric `g₀⁻¹ = ∑ᵢ ♯eᵢ ⊗ ♯eᵢ`), this is the **intrinsic** `g₀⁻¹`
double trace of the two leading covariant slots — base-point-dependent only through the raised vectors,
which vary smoothly, with NO dependence on a chart-selected frame. -/
noncomputable def modelTrace42MapVec (a : ℕ) (v : Fin (Module.finrank ℝ E) → E) :
    Tensor0SBundle.Tensor0SModel (4 + a) ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel (2 + a) ℝ E :=
  (-2 : ℝ) • ∑ i : Fin (Module.finrank ℝ E),
    (Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) (2 + a) (v i)).comp
      ((modelRankCast (E := E) (by omega : (3 + a) = (2 + a) + 1)).comp
        ((Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) (3 + a) (v i)).comp
          (modelRankCast (E := E) (by omega : (4 + a) = (3 + a) + 1))))

/-- **The intrinsic `g₀`-raised model-basis vector field `♯ eᵢ : x ↦ ♯ eᵢ(x)`.**  The `g₀`-raised
(`inverseMetricSharpFib`, the smooth musical `♯`) of the `i`-th `E`-orthonormal coframe covector
`eᵢ := chartModelBasis E i` (lifted from the ambient functional `coframeOfBasis (chartModelBasis E) i :
E →L ℝ` into the cotangent fibre `Tensor0SSpace 1 I x`).  As `i` ranges over the `E`-orthonormal
coframe, `∑ᵢ ♯eᵢ(x) ⊗ ♯eᵢ(x)` is the cometric `g₀⁻¹(x)` (basis-independent); the raised vectors
`♯eᵢ(x) ∈ TangentSpace I x` depend smoothly on `x` (through `g₀⁻¹`), with NO chart-selected,
non-`∇₀`-parallel ambient basis appearing in the contraction. -/
noncomputable def cometricRaisedBasisVec (g₀ : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) : TangentSpace I x :=
  inverseMetricSharpFib (I := I) g₀ x
    ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        (Tensor0SBundle.coframeOfBasis (Integral.Measure.chartModelBasis E) i)))

/-- **The fibrewise `−2` intrinsic `g₀⁻¹` double-trace fibre operator.**  At a base point `x`, the
`−2`-scaled cometric double trace `modelTrace42MapVec a (♯e·(x))` (the leading-two-slot contraction
against the `g₀`-raised coframe) transported through the fibre/model continuous-linear equivalence
`tensor0SSpace_continuousLinearEquiv`: a continuous-linear map between tensor fibres
`Tensor0SSpace (4 + a) I x →L Tensor0SSpace (2 + a) I x`, i.e. a `(0, 4 + a) → (0, 2 + a)` fibre map.
It reads only the fibre value `D(x)` (value-local) and depends on the background metric `g₀` only
through the cometric `g₀⁻¹(x)` — NO chart-selected, non-`∇₀`-parallel ambient basis enters. -/
noncomputable def ricciModelTrace42Fib (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    Tensor0SBundle.Tensor0SSpace (4 + a) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a) I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (2 + a) x).symm.toContinuousLinearMap.comp
    ((modelTrace42MapVec (E := E) a
        (fun i => (cometricRaisedBasisVec (I := I) g₀ x i : E))).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (4 + a) x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in
/-- **The model image of the fibre operator is the intrinsic raised double trace.**  `toModel`
intertwines `ricciModelTrace42Fib` with the model-level `modelTrace42MapVec` against the `g₀`-raised
coframe:
`toModel (ricciModelTrace42Fib g₀ a x D) = modelTrace42MapVec a (♯e·(x)) (toModel D)`.  Definitional,
since `Tensor0SSpace.toModel = tensor0SSpace_continuousLinearEquiv` and the equivalence is `id`. -/
@[simp] theorem ricciModelTrace42Fib_toModel (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace (4 + a) I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (ricciModelTrace42Fib (I := I) g₀ a x D) =
      modelTrace42MapVec (E := E) a (fun i => (cometricRaisedBasisVec (I := I) g₀ x i : E))
        (Tensor0SBundle.Tensor0SSpace.toModel D) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **(POSIT — base-point smoothness of the intrinsic `g₀⁻¹` double-trace operator field.)**  The
fibre field `x ↦ ricciModelTrace42Fib g₀ a x` is a smooth section of the `(4 + a, 2 + a)`-tensor bundle.
The fibre map is the leading-two-slot contraction against the cometric `g₀⁻¹(x) = ∑ᵢ ♯eᵢ(x) ⊗ ♯eᵢ(x)`;
the `g₀`-raised coframe vectors `♯eᵢ(x)` depend smoothly on `x` (`inverseMetricSharpField_contMDiff`,
the smooth inverse-metric musical), and the model double-interior-product against a *smooth* vector
tuple is smooth (the `model_interior_bilinear` smooth-bilinear evaluation, the exact mechanism the
on-disk smooth vector-contraction field `contract_covariantField` uses, lifted to the bundle by
`contMDiff_clm_section_of_pointwise`).  Its body is `sorry`: the genuine smoothness of the intrinsic
`g₀⁻¹` double-trace operator field — the cometric-raised analogue of `contract_covariantField`'s
smooth-section skeleton, summed over the coframe.  (NO chart-selected, non-`∇₀`-parallel ambient basis
appears; the smoothness is genuinely intrinsic, through the smooth cometric.) -/
theorem ricciModelTrace42Fib_contMDiff (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel (4 + a) (2 + a) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel (4 + a) (2 + a) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace (4 + a) (2 + a) I z) x
        (ricciModelTrace42Fib (I := I) g₀ a x)) :=
  sorry

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

/-- **The section-level `−2` intrinsic `g₀⁻¹` Ricci-trace operator `(0, 4 + a) → (0, 2 + a)`.**  The
genuine building block of the intrinsic `g₀⁻¹` Ricci-trace parallel contraction: the operator at
gradient-shift `a` that contracts the leading two of the `4 + a` covariant slots of a smooth
`(0, 4 + a)`-tensor against the cometric `g₀⁻¹` (the `g₀⁻¹` double trace `∑ᵢ D(♯eᵢ, ♯eᵢ, ·)`, with
`♯eᵢ` the `g₀`-raised `E`-orthonormal coframe) and scales by `−2`, producing a smooth
compactly-supported `(0, 2 + a)`-tensor.  This is the rank-reducing metric-trace contraction the Ricci
difference arm needs (the `−2` `g₀⁻¹` curvature trace lowering rank `4 + a → 2 + a`); it depends on the
background metric `g₀` only through the cometric, with NO chart-selected ambient basis.

It is constructed concretely as the operator-field action `appCcRS` of the smooth `g₀⁻¹` double-trace
operator field `ricciModelTrace42Field g₀ a` (the cometric-raised model map `modelTrace42MapVec a
(♯e·(x))` transported through the bundle/model equivalence) on the input `(0, 4 + a)`-tensor — the same
smooth-section route as the algebraic trace `contractCcTensor` and the curvature operator-field action
`appCc`. -/
noncomputable def ricciModelTrace42Op (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    Integral.L2.SmoothCcTensor g₀ 0 (4 + a) → Integral.L2.SmoothCcTensor g₀ 0 (2 + a) :=
  fun T =>
    DifferentialGeometry.Integral.Connection.appCcRS (I := I) (M := M) g₀ 0 (4 + a) (2 + a)
      (ricciModelTrace42Field (I := I) g₀ a) T

set_option linter.unusedSectionVars false in
/-- **The fibre value of `ricciModelTrace42Op` is the fibrewise composition of the double-trace fibre
operator with the input section.**  Definitional via `appCcRS_toSection`. -/
@[simp] theorem ricciModelTrace42Op_toSection (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (T : Integral.L2.SmoothCcTensor g₀ 0 (4 + a)) (x : M) :
    (ricciModelTrace42Op (I := I) g₀ a T).toSection x =
      (show Tensor0SBundle.Tensor0SSpace (4 + a) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a) I x from
        ricciModelTrace42Fib (I := I) g₀ a x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (4 + a) I x from
          T.toSection x) := by
  rw [ricciModelTrace42Op,
    DifferentialGeometry.Integral.Connection.appCcRS_toSection (I := I) (M := M) g₀ 0 (4 + a) (2 + a)
      (ricciModelTrace42Field (I := I) g₀ a) T x, ricciModelTrace42Field_toSection]

set_option linter.unusedSectionVars false in
/-- **Fibrewise `ℝ`-additivity of the section-level model-basis Ricci-trace operator.**  The
`−2` model-basis double trace `ricciModelTrace42Op` distributes over a section difference: it is the
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

/-- **(POSIT — the exact parallel single-step covariant Leibniz of the intrinsic `g₀⁻¹` Ricci trace.)**
Because the background inverse metric `g₀^{ij}` is `∇₀`-parallel (`∇₀ g₀⁻¹ = 0`, the cometric skew core
`cometric_skew_core`: `g(∇_w ♯eᵢ, ♯eⱼ) + g(♯eᵢ, ∇_w ♯eⱼ) = 0` read on the raised coframe), the
covariant gradient passes through the `−2` intrinsic `g₀⁻¹` double trace with **no**
differentiated-operator cross term (the moving-coframe corrections cancel against the cometric
parallelism):
`∇₀(ricciModelTrace42Op a R) = (rank-cast) ricciModelTrace42Op (a+1) (∇₀ R)`, the new gradient slot
carried at the front, rank-cast from `2 + (a + 1)` to `(2 + a) + 1` by `castRankCc_db`.  This is now
genuinely TRUE (the contraction is against the `∇₀`-parallel cometric `g₀⁻¹`, NOT a fixed,
non-`∇₀`-parallel ambient basis).  Its body is `sorry`: the cometric-parallelism intertwining of `∇₀`
and the `g₀⁻¹` trace. -/
theorem ricciModelTrace42Op_covGrad (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (R : Integral.L2.SmoothCcTensor g₀ 0 (4 + a)) :
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 (2 + a)
        (ricciModelTrace42Op (I := I) g₀ a R) =
      Integral.Connection.castRankCc_db g₀ 0 (by omega : 2 + (a + 1) = (2 + a) + 1)
        (ricciModelTrace42Op (I := I) g₀ (a + 1)
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 (4 + a) R)) :=
  sorry

/-- **(POSIT — the base-point- and order-uniform single-value fibre envelope of the intrinsic `g₀⁻¹`
double trace.)**  The intrinsic `g₀⁻¹` double-trace contraction is value-local (it reads only the fibre
value `R(x)`, never a jet of `R`) and its leading-two-slot fibre operator-norm depends only on the
cometric `g₀⁻¹` (the passenger `a` slots are untouched), so there is a **single** nonnegative constant
`κ₀`, uniform over the gradient-shift `a`, the section `R`, and the base point `x`, with
```
rfns(ricciModelTrace42Op a R)(x) ≤ κ₀ · rfns(R)(x).
```
The honest envelope is `κ₀ = (2 · sup_x ∑ᵢ ‖♯eᵢ(x)‖²)²` (the squared uniform cometric trace, NOT the
chart-free `(2·dim)²` that would require a `g₀`-orthonormal coframe): each leading-slot interior product
against `♯eᵢ` has model-operator-norm `≤ ‖♯eᵢ(x)‖`, the two iterated products give `‖♯eᵢ(x)‖²`, the sum
over the `E`-orthonormal coframe gives the cometric trace `∑ᵢ ‖♯eᵢ(x)‖²` (uniformly bounded on the
compact `M` by `exists_uniform_cometricBilin_bound`), and the `−2`-scaling squares to the `(2·…)²`
factor — uniform over `a` because the operator norm of a leading-slot contraction is independent of the
passenger valence.  Its body is `sorry`: the order-uniform value-local fibre bound of the intrinsic
`g₀⁻¹` double trace. -/
theorem exists_uniform_ricciModelTrace42Op_rfns_le (g₀ : SmoothRiemannianMetric I M) :
    ∃ κ₀ : ℝ, 0 ≤ κ₀ ∧ ∀ (a : ℕ) (R : Integral.L2.SmoothCcTensor g₀ 0 (4 + a)) (x : M),
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((ricciModelTrace42Op (I := I) g₀ a R).toSection x) ≤
        κ₀ * Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + a) x
          (R.toSection x) :=
  sorry

/-- **The `(0, 4) → (0, 2)` intrinsic `g₀⁻¹` Ricci-trace parallel contraction.**  The parallel
rank-reducing single-section contraction realising the `−2` intrinsic `g₀⁻¹` Ricci trace `g₀^{ij}·` on
the once-`∇₀`-differentiated rank-`4` Koszul operand, a `ParallelRankReducingContraction g₀ 4 2`,
assembled from its four genuinely-deep fields: the section-level intrinsic `g₀⁻¹` double trace
`ricciModelTrace42Op` (contracting the leading two covariant slots against the cometric `g₀⁻¹`, NOT a
chart-selected ambient basis), its exact parallel single-step covariant Leibniz
`ricciModelTrace42Op_covGrad` (the cometric parallelism `∇₀ g₀⁻¹ = 0` via `cometric_skew_core`, carried
through `castRankCc_db`), the order-uniform envelope constant `κ₀` (the squared uniform cometric trace,
`exists_uniform_ricciModelTrace42Op_rfns_le`), and its single-value fibre envelope (value-locality of
the trace).

The contraction is **genuine** (non-degenerate): its envelope `kappa = κ₀ ≥ 0` is the value-local bound
genuinely using the section; the trace is tied to the linearized-Ricci principal part by the section
identity `linearSection_eq_ricciModelTrace42_koszulTriple_sub_crossCorrTriple` (a degenerate zero trace
would falsify it whenever the linear part is genuinely present, `linearSection_self_toModel`). -/
noncomputable def ricciModelTrace42 (g₀ : SmoothRiemannianMetric I M) :
    Integral.Connection.ParallelRankReducingContraction (I := I) (M := M) g₀ 4 2 where
  op := fun a => ricciModelTrace42Op (I := I) g₀ a
  covGrad_op := fun a R => ricciModelTrace42Op_covGrad (I := I) g₀ a R
  kappa := (exists_uniform_ricciModelTrace42Op_rfns_le (I := I) g₀).choose
  kappa_nonneg := (exists_uniform_ricciModelTrace42Op_rfns_le (I := I) g₀).choose_spec.1
  rfns_op_le := fun a R x =>
    (exists_uniform_ricciModelTrace42Op_rfns_le (I := I) g₀).choose_spec.2 a R x

set_option linter.unusedSectionVars false in
/-- **Fibrewise `ℝ`-linearity of the intrinsic `g₀⁻¹` Ricci trace.**  The `op` of the `(0, 4) → (0, 2)`
intrinsic `g₀⁻¹` Ricci-trace contraction `ricciModelTrace42` distributes over a section difference (it
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

/-- **(POSIT — the linearized-Ricci principal-part value identity, the irreducible trace bridge.)**  The
genuine value content of the linearized-Ricci principal part: the linear-in-difference curvature section
`linearSection g₀ g₁ g₂` is the `−2` intrinsic `g₀⁻¹` Ricci trace `ricciModelTrace42.op 0` of the
**once-`∇₀`-differentiated** `g₀`-lowered connection-difference *difference*
`∇₀ (2·loweredConnDiffSection g₁ g₀ − 2·loweredConnDiffSection g₂ g₀)`.  This is the section-level lift
of the once-differentiated pointwise lowered-Koszul form `connDiffDiff_g0_lowered_koszul_diffFactor`
(`ricciNeg2SectionDiffLinearEval = −2 g₀^{ij}` double trace of `∇₀` of the lowered connection-difference
difference), the genuine reconciliation tying the intrinsic `g₀⁻¹` trace `op` to the linearized-Ricci
principal part `linearSection` (`linearSection_toModel_apply = ricciNeg2SectionDiffLinearEval`,
`ricciModelTrace42Op` the `−2 g₀^{ij}` double trace).  Its body is `sorry`: the irreducible
linearized-Ricci principal-part covariant trace identity. -/
theorem linearSection_eq_ricciModelTrace42_loweredConnDiffSub
    (g₀ : SmoothRiemannianMetric I M) (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (hr1 : ∀ (x : M) (v w : TangentSpace I x),
      g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w)
    (hr2 : ∀ (x : M) (v w : TangentSpace I x),
      g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) :
    linearSection (I := I) g₀ g₁ g₂ =
      (ricciModelTrace42 (I := I) g₀).op 0
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
          ((2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₁ g₀
            - (2 : ℝ) • DeTurck.loweredConnDiffSection (I := I) g₂ g₀)) :=
  sorry

/-- **The linearized-Ricci principal-part value identity for the model-basis Ricci trace.**  The
linear-in-difference curvature section `linearSection g₀ g₁ g₂` is the trace of the
**once-`∇₀`-differentiated** connection-difference Koszul **difference arm** `∇₀ koszulTripleDiff` minus
the trace of the once-`∇₀`-differentiated **cross arm** `∇₀ crossCorrTripleDiff`.

**Decomposition.**  By the **proven** child-A `loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff`,
`koszulTripleDiff − crossCorrTripleDiff = 2·loweredConnDiffSection g₁ g₀ − 2·loweredConnDiffSection g₂ g₀`
(the `koszulTripleDiff` shape `R + perm₁ R − perm₂ R` is the clean realized combination, and
`crossCorrTripleDiff = 2·crossCorrectionSection g₁ − 2·crossCorrectionSection g₂` is the cross arm).  The
two traces re-collect over the section difference by the fibrewise-`ℝ`-linearity `ricciModelTrace42_op_sub`
and the covariant-gradient linearity `covGrad_sub_local`, reducing the goal to the irreducible value
bridge `linearSection_eq_ricciModelTrace42_loweredConnDiffSub` (the trace of the once-differentiated
lowered connection-difference difference equals `linearSection`). -/
theorem linearSection_eq_ricciModelTrace42_koszulTriple_sub_crossCorrTriple
    (g₀ : SmoothRiemannianMetric I M) (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (hr1 : ∀ (x : M) (v w : TangentSpace I x),
      g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w)
    (hr2 : ∀ (x : M) (v w : TangentSpace I x),
      g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) :
    linearSection (I := I) g₀ g₁ g₂ =
      (ricciModelTrace42 (I := I) g₀).op 0
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
            (koszulTripleDiff (I := I) g₀ T₁ T₂))
        - (ricciModelTrace42 (I := I) g₀).op 0
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
            (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)) := by
  -- Re-collect the two traces over the section difference (fibrewise-`ℝ`-linearity of the trace and
  -- linearity of `∇₀`), reducing to `op 0 (∇₀ (koszulTripleDiff − crossCorrTripleDiff))`.
  rw [← ricciModelTrace42_op_sub (I := I) g₀ 0
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
          (koszulTripleDiff (I := I) g₀ T₁ T₂))
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
          (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)),
    ← covGrad_sub_local (I := I) g₀ 3
      (koszulTripleDiff (I := I) g₀ T₁ T₂) (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)]
  -- Child-A: `koszulTripleDiff − crossCorrTripleDiff = 2·loweredConnDiff g₁ − 2·loweredConnDiff g₂`.
  have hchildA :=
    (DeTurck.loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff
      (I := I) g₀ g₁ g₂ T₁ T₂ hr1 hr2).symm
  rw [koszulTripleDiff, crossCorrTripleDiff] at *
  rw [hchildA]
  -- The irreducible value bridge.
  exact linearSection_eq_ricciModelTrace42_loweredConnDiffSub (I := I) g₀ T₁ T₂ g₁ g₂ hr1 hr2

/-- **The linearized-Ricci principal-part section identity: `linearSection` as a parallel model-basis
Ricci trace of the *once-covariantly-differentiated* connection-difference Koszul combination.**  There
is a **parallel rank-reducing `(0, 4) → (0, 2)` contraction** `Φ` (the `−2` model-basis Ricci trace
`g₀^{ij}·`, parallel because `∇₀ g₀⁻¹ = 0`, value-local because it reads only the fibre), **fibrewise
`ℝ`-linear** (so it distributes over the section difference), with the linear-in-difference curvature
section `linearSection g₀ g₁ g₂` equal to the trace of the **once-`∇₀`-differentiated**
connection-difference Koszul **difference arm** minus the trace of the once-`∇₀`-differentiated **cross
arm**:
```
linearSection g₀ g₁ g₂ = Φ.op 0 (∇₀ koszulTripleDiff) − Φ.op 0 (∇₀ crossCorrTripleDiff),
```
where `∇₀ · = covGrad g₀ 0 3 ·`.  Carrying the trace on the **once-differentiated** rank-`4`
`∇₀ koszulTripleDiff` supplies the missing derivative (`∇^{j+1} R = ∇^{j+2} w`) that the refuted
value-local `(0, 3) → (0, 2)` form was one short of.

**Decomposition.**  Assembled from the model-basis Ricci-trace instance `ricciModelTrace42` (witness),
its linearity `ricciModelTrace42_op_sub`, and the value identity
`linearSection_eq_ricciModelTrace42_koszulTriple_sub_crossCorrTriple` (the lift of the once-differentiated
pointwise lowered-Koszul form to the section trace, over the proven child-A
`loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff`).

**Non-vacuity.**  `Φ` is a *genuine* parallel contraction (its `kappa` envelope rejects the degenerate
zero witness whenever `op a R ≠ 0`), and the right-hand side genuinely carries the once-differentiated
rank-`4` jet `∇₀ koszulTripleDiff`; `linearSection` genuinely vanishes only at `g₁ = g₂`
(`linearSection_self_toModel`). -/
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
                (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)) :=
  ⟨ricciModelTrace42 (I := I) g₀,
    fun a A B => ricciModelTrace42_op_sub (I := I) g₀ a A B,
    fun T₁ T₂ g₁ g₂ hr1 hr2 =>
      linearSection_eq_ricciModelTrace42_koszulTriple_sub_crossCorrTriple (I := I) g₀ T₁ T₂ g₁ g₂
        hr1 hr2⟩

/-- **(POSIT — the connection-level top/rest split of the traced once-differentiated cross-correction
difference.)**  For any parallel rank-reducing `(0, 4) → (0, 2)` contraction `Φ` (the model-basis Ricci
trace), the order-`j` covariant gradient of the traced once-`∇₀`-differentiated cross-correction
difference `Φ.op 0 (∇₀ crossCorrTripleDiff)` (`∇₀ · = covGrad g₀ 0 3 ·`) splits, at each point `x`, into
a **connection-level difference part** `Top` and a **fixed-pair cross part** `Rest`:
```
∇^j (Φ.op 0 (∇₀ crossCorrTripleDiff))(x) = Top + Rest,
rfns(Top)(x)  ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x),
rfns(Rest)(x) ≤ (1/16) · (∑_{i ≤ j+2} (rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x))) · ‖(T₁ − T₂).toHs a‖²,
```
where `R := covGrad g₀ 0 2 (realizeSymmCcTensor g₀ (T₁ − T₂))` (rank `3`).

This is the genuine **connection-level** (rank-`3`, `∇w`-level) two-piece decomposition of the traced,
once-differentiated cross-correction difference.  It is the *difference* (two-metric) analogue of the
single-metric `crossCorrectionSection_iteratedCovGrad_topRest_split` (`ConnectionDifferenceFieldJets`),
but its difference part is carried by the **connection-level** `∑_{p ≤ j+1} rfns(∇^p R)` jet sum (rank
`3`), **not** that child's `w`-jet sum `∑_{i} rfns(∇^i w)`: after the value-local model-basis Ricci
trace `Φ.op` and the once-`∇₀` differentiation, the cross-correction-difference jet is controlled by the
connection-level `R = ∇₀ w` jets.  The `Top` part collects the connection-level difference-factor jets
(folded with the trace envelope and the metric-built `≤ 2`-jet coefficient into the family-uniform
`Cd`); the `Rest` part keeps the top coefficient jet on the **fixed pair** `T₁, T₂` against the
difference's order-`a` chart-Sobolev `C⁰` mass, with the per-recombination share `(1/16)` so that the
two-fold `riemannianFiberNormSq_add_le` recombination lands the consumer's `(1/8)` cross coefficient.

**Non-vacuity.**  The `Top` part carries the connection-level high derivative `∇^{j+1} R`, and the
`Rest` part carries **both** fixed-pair endpoints `T₁, T₂`.  At `T₁ = T₂` the cross-correction
difference vanishes (`ccTensorBilinSymm g₀ 0 = 0`), so `crossCorrTripleDiff = 0` and the split is
`0 = 0 + 0`.  NO value-bounded operator shape, NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity,
NO Weyl dependence.  Its body is `sorry`: the genuine deep connection-level post-trace
cross-correction-difference covariant-Leibniz split. -/
theorem crossCorrectionDiff_iteratedCovGrad_connLevel_split
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
        ∀ x : M,
          ∃ Top Rest : Tensor0SBundle.TensorRSSpace 0 (2 + j) I x,
            (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (Φ.op 0 (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
                    (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)))).toSection x = Top + Rest ∧
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x Top ≤
                Cd * ∑ p ∈ Finset.range (j + 1 + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x) ∧
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x Rest ≤
                (1 / 16 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                    (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                      + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
  sorry

/-- **(POSIT-DERIVED — the post-trace connection-level cross-correction-difference covariant-jet bound,
`(1/8)`-cross arm.)**  For any parallel rank-reducing `(0, 4) → (0, 2)` contraction `Φ` (the model-basis
Ricci trace), the intrinsic squared fibre norm of the order-`j` covariant gradient of the **traced
once-`∇₀`-differentiated** cross-correction difference `Φ.op 0 (∇₀ crossCorrTripleDiff)` is dominated by
the **connection-level** Hamilton/Moser two-arm sum: a difference arm carried by the order-`≤ j+1`
covariant jets of the once-differentiated realized difference factor
`R := covGrad g₀ 0 2 (realizeSymmCcTensor g₀ (T₁ − T₂))` (rank `3`), plus the fixed-pair cross piece
carrying the endpoint jets against the difference's order-`a` chart-Sobolev `C⁰` mass with the explicit
coefficient `(1/8)`, uniformly over the supercritical `H^{a+2}`-bounded fibre-small perturbation family:
```
rfns(∇^j (Φ.op 0 (∇₀ crossCorrTripleDiff)))(x)
  ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x)
    + (1/8) · (∑_{i ≤ j+2} (rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x))) · ‖(T₁ − T₂).toHs a‖².
```

This is the **connection-level** (rank-`3`, `∇w`-level) form of the cross-correction-difference bound:
it sits *strictly below* the consumer-level child `crossCorrectionSection_iteratedCovGrad_topRest_split`
(whose difference arm is the `w`-jet sum, carrying the extra `∇^0 w` term), because the model-basis
Ricci trace `Φ.op` is value-local and the cross-correction-difference jet, *after* the trace and the
once-`∇₀` differentiation, is controlled by the connection-level `R = ∇₀ w` jets, not the `w` jets.  The
`(1/8)` coefficient is the per-trace share so that the doubled cross arm of the `linearSection`
two-section split (the `2·rfns` subadditivity of `riemannianFiberNormSq_sub_le`) re-collects to the
target's `(1/4)` cross coefficient.

**Decomposition.**  This is the recombination of the genuinely-deep connection-level top/rest split
`crossCorrectionDiff_iteratedCovGrad_connLevel_split` (above): the split exhibits the order-`j` jet as
`Top + Rest`, and `riemannianFiberNormSq_add_le` (the `2·rfns` subadditivity) plus the split's two
fibre-norm bounds (`rfns(Top) ≤ Cd · ∑ rfns(∇^p R)`, `rfns(Rest) ≤ (1/16) · cross`) re-collect to
`(2·Cd) · ∑ rfns(∇^p R) + (1/8) · cross` (the doubled `(1/16)` cross share landing the `(1/8)`).

**Non-vacuity.**  Both arms carry genuine content: the difference arm carries the connection-level high
derivative `∇^{j+1} R`, and the cross arm carries **both** fixed-pair endpoints `T₁, T₂`.  At
`T₁ = T₂` the cross-correction difference vanishes (`ccTensorBilinSymm g₀ 0 = 0`), so
`crossCorrTripleDiff = 0` and the bound is `0 ≤ 0`.  NO value-bounded operator shape, NO
pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence. -/
theorem parallelTrace_crossCorrTripleDiff_iteratedCovGrad_connLevel_le
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
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (Φ.op 0 (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
                    (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)))).toSection x) ≤
            Cd * ∑ p ∈ Finset.range (j + 1 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                        (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x)
              + (1 / 8 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 := by
  classical
  obtain ⟨Cd, hCd0, hsplit⟩ :=
    crossCorrectionDiff_iteratedCovGrad_connLevel_split (I := I) g₀ a ha B hB δ hδ0 hδ1 j Φ
  refine ⟨2 * Cd, by positivity, ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
  obtain ⟨Top, Rest, hsum, hTop, hRest⟩ :=
    hsplit T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
  -- Recombine the split via the `2·rfns` subadditivity of `riemannianFiberNormSq_add_le`: the doubled
  -- `(1/16)` cross share of `Rest` lands the consumer's `(1/8)` cross coefficient, the doubled `Cd`
  -- diff bound of `Top` the consumer's `2·Cd` diff coefficient.
  rw [hsum]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + j) x Top Rest) ?_
  nlinarith [hTop, hRest, hCd0, riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x Top,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x Rest]

/-- **(POSIT — the connection-level curvature-trace covariant-jet two-arm reduction.)**  The genuine
deep curvature-trace covariant-Leibniz content beneath the difference-arm curvature leaf: the intrinsic
squared fibre norm of the order-`j` covariant gradient of the concrete linear-in-difference curvature
section `linearSection g₀ g₁ g₂` (a rank-`2` section) is dominated by the **Hamilton/Moser two-arm sum**
whose difference arm is the **connection-level** (rank-`3`) order-`≤ j+1` covariant jet sum of the
once-differentiated realized difference factor `R := covGrad g₀ 0 2 w`, `w := realizeSymmCcTensor g₀
(T₁ − T₂)`, plus the same fixed-pair cross piece carrying the endpoint jets against the difference's
order-`a` chart-Sobolev `C⁰` mass — with a nonnegative constant `Cd` **uniform** over the supercritical
`H^{a+2}`-bounded perturbation family:
```
rfns(∇^j linearSection)(x) ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x)
                           + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x)))·‖(T₁ − T₂).toHs a‖².
```

This is the curvature-trace covariant-Leibniz reduction of the difference-normal-form `(0,2)`-section
`linearSection` to the **connection level** (rank-`3`), the genuinely-missing covariant-Faà-di-Bruno
content for the *difference* curvature (the connection-difference covariant-jet machinery of
`ConnectionDifferenceFieldJets.lean` is single-metric, rank-`3`; this is its lift through the curvature
trace and the two-metric cocycle).  `linearSection`'s fibre value is the `−2` model-basis Ricci trace of
the antisymmetrised `∇₀`-of-connection-difference summand difference
(`ricciNeg2SectionDiffLinearEval`, `SegmentMetricCurvatureDifferenceOpDecomposition.lean`); its
`g₀`-lowered Koszul form (`connDiffDiff_g0_lowered_koszul_diffFactor`) is the clean realized
covariant-derivative combination `covDerivRealizeEval g₀ (T₁ − T₂)` — the three slot readings of
`R = ∇₀ w` (the difference arm) — **minus** the nonlinear fixed-pair cross correction
`2(h₁ ⌟ connDiff g₁ g₀ − h₂ ⌟ connDiff g₂ g₀)` (`h_k = ccTensorBilinSymm g₀ T_k`), which does **not**
cancel pointwise and rides on the **fixed pair** `T₁, T₂` (the cross arm).  The model-basis Ricci trace
is a parallel rank-reducing `(0,3) → (0,2)` contraction (`ParallelRankReducingContraction`), and the
order-`j` jet of the trace folds the metric-built `≤ 2`-jet trace coefficient into `Cd` over the window
`j + 1` (one extra `∇₀` from the `∇₀ D` linear summand shifts the rank-`3` window to `j + 1`).

**Non-vacuity.**  Both arms carry genuine content: the difference arm carries the connection-level high
derivative `∇^{j+1} R` (a zero `Cd` falsifies it whenever the linear part is genuinely present, since
`linearSection_self_toModel` shows it vanishes only when `g₁ = g₂`), and the cross arm carries **both**
fixed-pair endpoints `T₁, T₂`.  At `g₁ = g₂` (so `T₁ = T₂` realized) the linear section vanishes and the
bound is `0 ≤ 0`.  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet claim, NO
spectral-nonlinearity, NO Weyl dependence.  Its body is `sorry`: the genuine deep curvature-trace
covariant-Leibniz reduction to the connection level. -/
theorem ricciLinearSection_covGrad_traceReductionConn_rfns_le
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
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (linearSection (I := I) g₀ g₁ g₂)).toSection x) ≤
            Cd * ∑ p ∈ Finset.range (j + 1 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                        (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x)
              + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 := by
  classical
  -- The model-basis Ricci trace `Φ` (parallel, rank-reducing `(0,4) → (0,2)`, fibrewise-linear) and
  -- the principal-part identity `linearSection = Φ.op 0 (∇₀ koszulTripleDiff) − Φ.op 0 (∇₀ crossCorrTripleDiff)`.
  obtain ⟨Φ, hΦlin, hΦid⟩ :=
    exists_parallelTrace_linearSection_eq_koszulTriple_sub_crossCorrTriple (I := I) g₀
  -- The post-trace connection-level cross-correction-difference jet bound (`(1/8)`-cross arm).
  obtain ⟨CdQ, hCdQ0, hCdQ⟩ :=
    parallelTrace_crossCorrTripleDiff_iteratedCovGrad_connLevel_le (I := I) g₀ a ha B hB δ hδ0 hδ1 j Φ
  refine ⟨2 * Φ.kappa * 18 + 2 * CdQ, by have := Φ.kappa_nonneg; positivity, ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
  -- Abbreviate `R := covGrad g₀ 0 2 w`, the difference-arm jet sum `SR`, and the cross arm `ST·P`.
  set R := Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)) with hR
  set SR := ∑ p ∈ Finset.range (j + 1 + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x) with hSR
  have hSRnn : 0 ≤ SR :=
    Finset.sum_nonneg fun p _ => riemannianFiberNormSq_nonneg _ _ _ _ _
  set ST := ∑ i ∈ Finset.range (j + 2 + 1),
      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)) with hST
  have hSTnn : 0 ≤ ST :=
    Finset.sum_nonneg fun i _ =>
      add_nonneg (riemannianFiberNormSq_nonneg _ _ _ _ _) (riemannianFiberNormSq_nonneg _ _ _ _ _)
  set P := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 with hP
  have hPnn : 0 ≤ P := by rw [hP]; positivity
  -- The once-differentiated rank-`4` Koszul triple `Q := ∇₀ koszulTripleDiff` (the linearized-Ricci
  -- principal-part operand the model-basis Ricci trace `Φ` reads).
  set Q := Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
    (koszulTripleDiff (I := I) g₀ T₁ T₂) with hQ
  -- The principal-part identity, specialized to this realizing pair.
  have hid := hΦid T₁ T₂ g₁ g₂ hr1 hr2
  -- Split the squared fibre norm of `∇^j linearSection` over the trace difference identity.
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
            (linearSection (I := I) g₀ g₁ g₂)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (Φ.op 0 Q)).toSection x)
        + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
              (Φ.op 0 (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
                (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)))).toSection x) := by
    rw [hid, ← hQ, PDE.RicciFlow.iteratedCovGrad_sub, Integral.L2.SmoothCcTensor.toSection_sub,
      ContMDiffSection.coe_sub, Pi.sub_apply]
    exact riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 0 (2 + j) x _ _
  -- **Difference arm.**  The value-local trace grid bounds `∇^j (Φ.op 0 Q)` by `kappa · ∇^j Q`
  -- (`Φ.rfns_iteratedCovGrad_le` at shift `0`, lowering rank `4 → 2`).
  have htrace : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0 + j) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (2 + 0) j (Φ.op 0 Q)).toSection x) ≤
      Φ.kappa * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + 0 + j) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (4 + 0) j Q).toSection x) :=
    Φ.rfns_iteratedCovGrad_le j 0 Q x
  -- Rank-shift: `∇^j (∇₀ koszulTripleDiff) = ∇^{j+1} koszulTripleDiff` (front-commutation), so the
  -- difference arm carries the *second*-order jet `∇^{j+1} R`, not `∇^j R`.
  have hshift : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + 0 + j) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (4 + 0) j Q).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + (j + 1)) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1)
            (koszulTripleDiff (I := I) g₀ T₁ T₂)).toSection x) := by
    rw [hQ]
    exact DeTurck.riemannianFiberNormSq_toSection_heq (I := I) (M := M) g₀
      (by omega : (4 : ℕ) + 0 + j = 3 + (j + 1))
      (DeTurck.iteratedCovGrad_covGrad_comm_heq_local (I := I) (M := M) g₀ 3 j
        (koszulTripleDiff (I := I) g₀ T₁ T₂)) x
  -- The order-`(j+1)` jet of `koszulTripleDiff = R + perm₁ R − perm₂ R` is dominated by `18 · rfns(∇^{j+1} R)`,
  -- since the two slot permutations preserve the jet fibre norm (`permuteCcTensor`-invariance).
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
    rw [koszulTripleDiff, ← hR, PDE.RicciFlow.iteratedCovGrad_sub, PDE.RicciFlow.iteratedCovGrad_add,
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
  -- `rfns(∇^{j+1} R) = LR` is the `p = j+1` term of `SR`, hence `LR ≤ SR` (the dropped terms are nonneg).
  have hLR_le_SR : LR ≤ SR := by
    rw [hLR, hSR]
    refine Finset.single_le_sum (f := fun p => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x))
      (fun p _ => riemannianFiberNormSq_nonneg _ _ _ _ _) ?_
    exact Finset.mem_range.mpr (by omega)
  -- The difference arm: `rfns(∇^j (Φ.op 0 Q)) ≤ kappa · 18 · SR` (reaching `∇^{j+1} R = ∇^{j+2} w`).
  have hdiffarm : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (Φ.op 0 Q)).toSection x) ≤
      Φ.kappa * 18 * SR := by
    have htrace' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j (Φ.op 0 Q)).toSection x) ≤
        Φ.kappa * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + (j + 1)) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 (j + 1)
              (koszulTripleDiff (I := I) g₀ T₁ T₂)).toSection x) := by
      rw [← hshift]; exact htrace
    refine le_trans htrace' ?_
    have hk : (0 : ℝ) ≤ Φ.kappa := Φ.kappa_nonneg
    nlinarith [hkoszul, hLR_le_SR, hLRnn, hk, hSRnn]
  -- **Cross arm.**  The post-trace connection-level cross bound (`(1/8)`-cross arm).
  have hcrossarm := hCdQ T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
  rw [← hR, ← hSR, ← hST, ← hP] at hcrossarm
  -- Re-collect: `2·(diff) + 2·(cross) ≤ (2·kappa·18 + 2·CdQ)·SR + (1/4)·ST·P`.
  refine le_trans hsplit ?_
  nlinarith [hdiffarm, hcrossarm, hSRnn, hSTnn, hPnn, Φ.kappa_nonneg, hCdQ0, mul_nonneg hSTnn hPnn,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
          (Φ.op 0 (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 3
            (crossCorrTripleDiff (I := I) g₀ T₁ T₂ g₁ g₂)))).toSection x)]

/-- **(POSIT — the curvature-trace covariant-jet two-arm bound of the linear difference section.)**
The intrinsic squared fibre norm of the order-`j` covariant gradient of the concrete
linear-in-difference curvature section `linearSection g₀ g₁ g₂` is dominated by the **Hamilton/Moser
two-arm sum** — a difference-arm piece carrying the single high derivative on the difference factor
`w := realizeSymmCcTensor g₀ (T₁ − T₂)` up to `∇^{j+2}w`, plus a fixed-pair cross piece carrying the
endpoint jets against the difference's order-`a` chart-Sobolev `C⁰` mass — with a nonnegative constant
`Cd` **uniform** over the supercritical `H^{a+2}`-bounded perturbation family:
```
rfns(∇^j linearSection)(x) ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)(x)
                           + (∑_{i ≤ j+2} (rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x))) · ‖(T₁ − T₂).toHs a‖².
```

This is the **corrected** (two-arm) curvature-trace content of the linear difference section.  The
order-zero linear/quadratic split (`linearSection` / `crossSection`) does **not** coincide with the
analytic difference-arm/fixed-pair-cross split: `linearSection`'s `g₀`-lowered Koszul form
(`connDiff_diff_koszul_realize_diffFactor`) is the clean realized covariant-derivative combination
`covDerivRealizeEval g₀ (T₁ − T₂)` (the difference arm, carrying the single difference factor `w`)
**minus** a nonlinear quadratic correction `2(h₁ ⌟ connDiff g₁ g₀ − h₂ ⌟ connDiff g₂ g₀)`
(`h_k = ccTensorBilinSymm g₀ T_k`), which does **not** cancel pointwise and rides on the **fixed pair**
`T₁, T₂` — exactly a fixed-pair-high × diff-low cross term.  So the linear section genuinely carries
**both** arms.  The difference arm is the realized-jet domination of the clean combination
(`koszulCombSection_iteratedCovGrad_rfns_le`, the realization gains no derivatives) summed over the
curvature trace; the cross arm is the fibre-small-gated cross-correction jet bound
(`crossCorrectionSection_iteratedCovGrad_rfns_le`) of the two `crossCorrectionSection g_k g₀ T_k` terms,
the top coefficient jet kept on the fixed pair against the difference's `C⁰` mass via the supercritical
Sobolev embedding (`ha`).  The metric-built `≤2`-jet curvature-trace coefficient is folded into the
family-uniform `Cd` over the window `j + 2`.

**Non-vacuity.**  Both arms carry genuine content: the difference arm carries `∇^{j+2}w` (a zero `Cd`
falsifies it whenever the linear part is genuinely present, `linearSection_self_toModel`), and the cross
arm carries **both** fixed-pair endpoints.  NO value-bounded `Φ.op 0 2 w` shape, NO
pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence.

**Decomposition.**  The two-arm bound is proved by composing the genuinely-deep **connection-level**
curvature-trace reduction `ricciLinearSection_covGrad_traceReductionConn_rfns_le` (below — its difference
arm is the *connection-level* `∑_{p ≤ j+1} rfns(∇^p R)` jet sum at rank `3`, `R := covGrad g₀ 0 2 w` the
once-differentiated realized difference factor) with the **sorry-free** rank-shift
`rfns(∇^p R) = rfns(∇^{p+1} w)` (the front/back commutation `iteratedCovGrad_covGrad_comm_heq`, since
`R = covGrad g₀ 0 2 w`) and the window inclusion `∑_{p ≤ j+1} rfns(∇^{p+1} w) ≤ ∑_{i ≤ j+2} rfns(∇^i w)`
(`Finset.sum_range_succ'`, the dropped `∇^0 w` term being nonnegative).  The cross arm is carried in
target form by the connection-level reduction unchanged.  This is precisely the composition the curvature
difference-arm leaf is documented to use; the only remaining genuine content is the connection-level
reduction itself. -/
theorem ricciLinearSection_covGrad_traceReduction_rfns_le
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
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (linearSection (I := I) g₀ g₁ g₂)).toSection x) ≤
            Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)
              + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 := by
  classical
  obtain ⟨Cd, hCd0, hCd⟩ :=
    ricciLinearSection_covGrad_traceReductionConn_rfns_le (I := I) g₀ a ha B hB δ hδ0 hδ1 j
  refine ⟨Cd, hCd0, ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
  -- The connection-level reduction, with `R := covGrad g₀ 0 2 (realizeSymm (T₁ − T₂))`.
  have hconn := hCd T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
  set w := realizeSymmCcTensor (I := I) g₀ (T₁ - T₂) with hw
  set R := Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2 w with hR
  -- Rank-shift: the order-`p` jet of `R = ∇₀ w` is the order-`(p+1)` jet of `w` (front/back commutation).
  have hRshift : ∀ p : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p + 1)) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p + 1) w).toSection x) := by
    intro p
    rw [hR]
    exact DifferentialGeometry.PDE.DeTurck.riemannianFiberNormSq_toSection_heq (I := I) (M := M) g₀
      (by omega : (3 : ℕ) + p = 2 + (p + 1))
      (DifferentialGeometry.PDE.DeTurck.iteratedCovGrad_covGrad_comm_heq_local
        (I := I) (M := M) g₀ 2 p w) x
  -- The connection-level difference-arm sum, rewritten termwise into the `w`-jet sum.
  have hsumR : (∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x)) =
      ∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p + 1)) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p + 1) w).toSection x) :=
    Finset.sum_congr rfl fun p _ => hRshift p
  -- Window inclusion `∑_{p ≤ j+1} rfns(∇^{p+1} w) ≤ ∑_{i ≤ j+2} rfns(∇^i w)` (drop the nonneg `∇^0 w`).
  have hwindow : (∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p + 1)) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p + 1) w).toSection x)) ≤
      ∑ i ∈ Finset.range (j + 2 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w).toSection x) := by
    rw [Finset.sum_range_succ' (n := j + 1 + 1)
      (f := fun i => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w).toSection x))]
    exact le_add_of_nonneg_right (riemannianFiberNormSq_nonneg _ _ _ _ _)
  -- The connection-level difference arm dominates the target `w`-jet difference arm.
  have hCdnn_term : (0 : ℝ) ≤ Cd := hCd0
  have harm : Cd * ∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x) ≤
      Cd * ∑ i ∈ Finset.range (j + 2 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w).toSection x) := by
    rw [hsumR]
    exact mul_le_mul_of_nonneg_left hwindow hCdnn_term
  -- Compose: connection-level reduction, then arm domination; the cross arm is unchanged.
  refine le_trans hconn ?_
  linarith [harm]

/-- **(POSIT — the connection-level top/rest split of the quadratic Cross section.)**  The genuine deep
**connection-level** (rank-`3`, `∇w`-level) two-piece decomposition of the quadratic-in-difference
curvature Cross section `crossSection g₀ g₁ g₂`: its order-`j` covariant gradient splits, at each point
`x`, into a connection-level difference part `Top` and a fixed-pair cross part `Rest`,
```
∇^j (crossSection)(x) = Top + Rest,
rfns(Top)(x)  ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x),
rfns(Rest)(x) ≤ (1/8) · (∑_{i ≤ j+2} (rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x))) · ‖(T₁ − T₂).toHs a‖²,
```
where `R := covGrad g₀ 0 2 (realizeSymmCcTensor g₀ (T₁ − T₂))` (rank `3`).

`crossSection`'s fibre value is the `−2` model-basis trace of the quadratic
`connDiffField ∧ connDiffField` summand difference (`ricciDiffQuad_modelTrace_eq_crossEndoTrace`); the
quadratic difference `D₁ ∘ D₁ − D₂ ∘ D₂ = (D₁ − D₂) ∘ D₁ + D₂ ∘ (D₁ − D₂)` (`D_k = connDiffField g_k
g₀`) puts the single high derivative on the difference factor `D₁ − D₂ = connDiffField g₁ g₂` (the
cocycle), whose `g₀`-lowered Koszul form is `R = ∇₀ w`.  The `Top` part collects the connection-level
difference-factor jets through the rank-reducing `(0, 3) → (0, 2)` curvature trace and the parallel
two-section bilinear product grid `RfnsBilinearProduct` (where the high derivative may land on either
factor, folded with the *fixed* factor sup and the metric-built `≤ 2`-jet trace coefficient into the
family-uniform `Cd`); the `Rest` part keeps the top coefficient jet on the **fixed pair** `T₁, T₂`
against the difference's order-`a` chart-Sobolev `C⁰` mass (the supercritical embedding `ha`), with the
per-recombination share `(1/8)` so that the `2·rfns` `riemannianFiberNormSq_add_le` recombination lands
the consumer's `(1/4)` cross coefficient.

**Non-vacuity.**  The `Top` part carries the connection-level high derivative `∇^{j+1} R`, and the
`Rest` part carries **both** fixed-pair endpoints `T₁, T₂`.  At `g₁ = g₂` the Cross section vanishes
(`crossSection_self_toModel`), so the split is `0 = 0 + 0`.  NO value-bounded operator shape, NO
pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl dependence.  Its body is `sorry`: the
genuine deep connection-level quadratic-Cross covariant-Leibniz split. -/
theorem crossSection_iteratedCovGrad_connLevel_split
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
        ∀ x : M,
          ∃ Top Rest : Tensor0SBundle.TensorRSSpace 0 (2 + j) I x,
            (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (crossSection (I := I) g₀ g₁ g₂)).toSection x = Top + Rest ∧
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x Top ≤
                Cd * ∑ p ∈ Finset.range (j + 1 + 1),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                            (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x) ∧
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x Rest ≤
                (1 / 8 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                    (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                      + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                  * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
  sorry

/-! ### The curvature-trace covariant-jet reduction of the *quadratic* Cross section

The quadratic-half analogue of the linear difference-arm reduction above.  The Cross section
`crossSection g₀ g₁ g₂`'s fibre value is the `−2` model-basis trace of the quadratic
`connDiffField ∧ connDiffField` summand difference (`ricciNeg2SectionDiffCrossEval`,
`ricciDiffQuad_modelTrace_eq_crossEndoTrace`).  Differenced along the segment, the quadratic product of
two endomorphism fields `D_k = connDiffField g_k g₀` splits by the bilinear identity
`D₁ ∘ D₁ − D₂ ∘ D₂ = (D₁ − D₂) ∘ D₁ + D₂ ∘ (D₁ − D₂)`, and the connection-difference cocycle
`D₁ − D₂ = connDiffField g₁ g₂` carries the single difference factor, whose metrically-lowered Koszul
form is the realized covariant derivative `R := covGrad g₀ 0 2 w`, `w := realizeSymmCcTensor g₀
(T₁ − T₂)` (the connection-level once-differentiated realized difference factor — exactly as for the
linear half).  The rank-reducing curvature trace (`(0, 3) → (0, 2)`) then folds the metric-built
`≤ 2`-jet trace coefficient and the *fixed* factor `D₁`, resp. `D₂`, sup into a family-uniform constant
`Cd` over the connection-level window `j + 1`. -/

/-- **(POSIT — the connection-level curvature-trace covariant-jet two-arm reduction of the quadratic
Cross section.)**  The genuine deep curvature-trace covariant-Leibniz content beneath the quadratic Cross
leaf: the intrinsic squared fibre norm of the order-`j` covariant gradient of the concrete
quadratic-in-difference curvature Cross section `crossSection g₀ g₁ g₂` (a rank-`2` section) is dominated
by the **Hamilton/Moser two-arm sum** whose difference arm is the **connection-level** (rank-`3`)
order-`≤ j+1` covariant jet sum of the once-differentiated realized difference factor `R := covGrad g₀
0 2 w`, `w := realizeSymmCcTensor g₀ (T₁ − T₂)`, plus the same fixed-pair cross piece carrying the
endpoint jets against the difference's order-`a` chart-Sobolev `C⁰` mass — with a nonnegative constant
`Cd` **uniform** over the supercritical `H^{a+2}`-bounded perturbation family:
```
rfns(∇^j crossSection)(x) ≤ Cd · ∑_{p ≤ j+1} rfns(∇^p R)(x)
                          + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x)))·‖(T₁ − T₂).toHs a‖².
```

This is the curvature-trace covariant-Leibniz reduction of the quadratic Cross `(0, 2)`-section to the
**connection level** (rank-`3`), structurally distinct from and strictly smaller than the consumer leaf:
its difference-arm right-hand side is the **connection-level** `∑_{p ≤ j+1} rfns(∇^p R)` jet sum (rank
`3`, the `∇w`-level), not the leaf's `∇^{≤ j+2} w` jet sum.  `crossSection`'s fibre value is the `−2`
model-basis trace of the quadratic `connDiffField ∧ connDiffField` summand difference (the genuine
second-order remainder, vanishing to second order in the difference, `crossSection_self_toModel`).  The
quadratic difference `D₁ ∘ D₁ − D₂ ∘ D₂ = (D₁ − D₂) ∘ D₁ + D₂ ∘ (D₁ − D₂)` puts the single high
derivative on the difference factor `D₁ − D₂ = connDiffField g₁ g₂` (the cocycle), whose `g₀`-lowered
Koszul form is `R = ∇₀ w` (the difference arm), while the *fixed* factor `D₁` / `D₂` and the metric-built
`≤ 2`-jet trace coefficient fold into the family-uniform `Cd` (the bilinear two-section covariant-Leibniz
grid `RfnsBilinearProduct` keeps the top coefficient jet of the fixed factor on the fixed pair `T₁, T₂`
against the difference's `C⁰` mass, which the supercritical Sobolev embedding `ha` bounds).

**Non-vacuity.**  Both arms carry genuine content: the difference arm carries the connection-level high
derivative `∇^{j+1} R` (a zero `Cd` falsifies it whenever the Cross part is genuinely present, since
`crossSection_self_toModel` shows it vanishes only when `g₁ = g₂`), and the cross arm carries **both**
fixed-pair endpoints `T₁, T₂`.  At `g₁ = g₂` (so `T₁ = T₂` realized) the Cross section vanishes and the
bound is `0 ≤ 0`.  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet claim, NO
spectral-nonlinearity, NO Weyl dependence.  Its body is `sorry`: the genuine deep curvature-trace
covariant-Leibniz reduction of the quadratic Cross to the connection level. -/
theorem ricciCrossSection_covGrad_traceReductionConn_rfns_le
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
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (crossSection (I := I) g₀ g₁ g₂)).toSection x) ≤
            Cd * ∑ p ∈ Finset.range (j + 1 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
                        (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))).toSection x)
              + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 := by
  classical
  -- The connection-level Cross split (`(1/8)`-cross arm).
  obtain ⟨Cd, hCd0, hsplit⟩ :=
    crossSection_iteratedCovGrad_connLevel_split (I := I) g₀ a ha B hB δ hδ0 hδ1 j
  refine ⟨2 * Cd, by positivity, ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
  obtain ⟨Top, Rest, hsum, hTop, hRest⟩ :=
    hsplit T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
  -- Recombine the split via the `2·rfns` subadditivity `riemannianFiberNormSq_add_le`: the doubled
  -- `(1/8)` cross share lands the consumer's `(1/4)` cross coefficient, the doubled `Cd` diff bound the
  -- consumer's `2·Cd` diff coefficient.
  rw [hsum]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + j) x Top Rest) ?_
  nlinarith [hTop, hRest, hCd0, riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x Top,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x Rest]

/-- **(POSIT-DERIVED — the curvature-trace covariant-jet two-arm bound of the quadratic Cross section.)**
The intrinsic squared fibre norm of the order-`j` covariant gradient of the concrete
quadratic-in-difference curvature Cross section `crossSection g₀ g₁ g₂` is dominated by the
**Hamilton/Moser two-arm sum** — a difference-arm piece carrying the single high derivative on the
difference factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)` up to `∇^{j+2}w`, plus a fixed-pair cross piece
carrying the endpoint jets against the difference's order-`a` chart-Sobolev `C⁰` mass — with a
nonnegative constant `Cd` **uniform** over the supercritical `H^{a+2}`-bounded perturbation family:
```
rfns(∇^j crossSection)(x) ≤ Cd · ∑_{i ≤ j+2} rfns(∇^i w)(x)
                          + (1/4)·(∑_{i ≤ j+2}(rfns(∇^i T₁)(x) + rfns(∇^i T₂)(x)))·‖(T₁ − T₂).toHs a‖².
```

This is the **corrected** (two-arm) curvature-trace content of the quadratic Cross section.  The Cross
section is the genuine quadratic remainder (`crossSection_self_toModel`); its differenced operator-trace
fibre value (`D₁ ∘ D₁ − D₂ ∘ D₂`, `D_k = connDiffField g_k g₀`) carries **both** a diff-high × fixed-low
arm and a fixed-high × diff-low arm (the connection-difference bilinear product of two independently
varying endomorphism fields), arising from the parallel two-section bilinear product `RfnsBilinearProduct`
grid where the high derivative may land on either factor.  The difference arm carries the single high
derivative on the difference factor `w`; the cross arm keeps the top coefficient jet on the fixed pair.

**Non-vacuity.**  Both arms carry genuine content: the difference arm carries `∇^{j+2}w` (a zero `Cd`
falsifies it whenever the Cross part is genuinely present, `crossSection_self_toModel`), and the cross arm
carries **both** fixed-pair endpoints.  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet
claim, NO spectral-nonlinearity, NO Weyl dependence.

**Decomposition.**  The two-arm bound is proved by composing the genuinely-deep **connection-level**
curvature-trace reduction `ricciCrossSection_covGrad_traceReductionConn_rfns_le` (whose difference arm is
the *connection-level* `∑_{p ≤ j+1} rfns(∇^p R)` jet sum at rank `3`, `R := covGrad g₀ 0 2 w` the
once-differentiated realized difference factor) with the **sorry-free** rank-shift
`rfns(∇^p R) = rfns(∇^{p+1} w)` (the front/back commutation `iteratedCovGrad_covGrad_comm_heq_local`,
since `R = covGrad g₀ 0 2 w`) and the window inclusion `∑_{p ≤ j+1} rfns(∇^{p+1} w) ≤ ∑_{i ≤ j+2}
rfns(∇^i w)` (`Finset.sum_range_succ'`, the dropped `∇^0 w` term being nonnegative).  The cross arm is
carried in target form by the connection-level reduction unchanged.  This is exactly the composition the
linear difference-arm half (`ricciLinearSection_covGrad_traceReduction_rfns_le`) uses; the only remaining
genuine content is the connection-level quadratic-Cross reduction itself. -/
theorem ricciCrossSection_covGrad_traceReduction_rfns_le
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
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                  (crossSection (I := I) g₀ g₁ g₂)).toSection x) ≤
            Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))).toSection x)
              + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂).toSection x)))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 := by
  classical
  obtain ⟨Cd, hCd0, hCd⟩ :=
    ricciCrossSection_covGrad_traceReductionConn_rfns_le (I := I) g₀ a ha B hB δ hδ0 hδ1 j
  refine ⟨Cd, hCd0, ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
  -- The connection-level reduction, with `R := covGrad g₀ 0 2 (realizeSymm (T₁ − T₂))`.
  have hconn := hCd T₁ T₂ g₁ g₂ hr1 hr2 hfib1 hfib2 hball1 hball2 x
  set w := realizeSymmCcTensor (I := I) g₀ (T₁ - T₂) with hw
  set R := Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2 w with hR
  -- Rank-shift: the order-`p` jet of `R = ∇₀ w` is the order-`(p+1)` jet of `w` (front/back commutation).
  have hRshift : ∀ p : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p + 1)) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p + 1) w).toSection x) := by
    intro p
    rw [hR]
    exact DifferentialGeometry.PDE.DeTurck.riemannianFiberNormSq_toSection_heq (I := I) (M := M) g₀
      (by omega : (3 : ℕ) + p = 2 + (p + 1))
      (DifferentialGeometry.PDE.DeTurck.iteratedCovGrad_covGrad_comm_heq_local
        (I := I) (M := M) g₀ 2 p w) x
  -- The connection-level difference-arm sum, rewritten termwise into the `w`-jet sum.
  have hsumR : (∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x)) =
      ∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p + 1)) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p + 1) w).toSection x) :=
    Finset.sum_congr rfl fun p _ => hRshift p
  -- Window inclusion `∑_{p ≤ j+1} rfns(∇^{p+1} w) ≤ ∑_{i ≤ j+2} rfns(∇^i w)` (drop the nonneg `∇^0 w`).
  have hwindow : (∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (p + 1)) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 (p + 1) w).toSection x)) ≤
      ∑ i ∈ Finset.range (j + 2 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w).toSection x) := by
    rw [Finset.sum_range_succ' (n := j + 1 + 1)
      (f := fun i => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w).toSection x))]
    exact le_add_of_nonneg_right (riemannianFiberNormSq_nonneg _ _ _ _ _)
  -- The connection-level difference arm dominates the target `w`-jet difference arm.
  have harm : Cd * ∑ p ∈ Finset.range (j + 1 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p R).toSection x) ≤
      Cd * ∑ i ∈ Finset.range (j + 2 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i w).toSection x) := by
    rw [hsumR]
    exact mul_le_mul_of_nonneg_left hwindow hCd0
  -- Compose: connection-level reduction, then arm domination; the cross arm is unchanged.
  refine le_trans hconn ?_
  linarith [harm]

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
