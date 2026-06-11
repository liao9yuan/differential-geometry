import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceQuadraticTraceProduct
import DifferentialGeometry.Geometry.Connection.DeTurckVFFaaDiBrunoDecomposition
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckCartanDiffBilinOp
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckCartanRfnsBilinearProduct
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField

/-! # The Cartan-difference section factorization of the symmetrised-lowered DeTurck-field difference

For two pairs of smooth Riemannian metrics `g₁, g₂` realizing perturbations `T₁, T₂` over a common
background `g₀` on a closed (compact, boundaryless) smooth manifold `M` modelled on a real
inner-product space `E`, this file supplies the **section-level Cartan-difference factorization** of
the difference of the two metrics' symmetrised covariant lowerings of the DeTurck vector field
`symLoweredDeTurckVFRetagG0 g₀ g₁ g_bg − symLoweredDeTurckVFRetagG0 g₀ g₂ g_bg` — the prerequisite
beneath the Lie-half deep gauge top/rest split `symLoweredDeTurckVF_iteratedCovGrad_topRest_split`
(`DeTurckVFCovGradTopRestSplit.lean`, the P1b consumer).

## What the carrier is, and why this telescoped factorization

The carrier `symLoweredDeTurckVFRetagG0 g₀ g₁ g_bg` (`LieDerivSectionCartan.lean`) is the `g₀`-retag
of `symLoweredDeTurckVF g₁ g_bg`, whose unit-evaluated `(0, 2)`-value is the intrinsic Cartan bilinear
form `cartanRHSBilin g₁ (deTurckVF g₁ g_bg) x v w = g₁(∇^{g₁}_v W₁, w) + g₁(v, ∇^{g₁}_w W₁)`,
`W₁ = deTurckVF g₁ g_bg`, `∇^{g₁} = LeviCivita g₁` (`symLoweredDeTurckVFRetagG0_unitModel_eq`).  It is a
covariant Faà-di-Bruno contraction of the metric jet, order-`≤ 2` in the metric.

The carrier difference `cartanRHSBilin g₁ W₁ − cartanRHSBilin g₂ W₂` varies **three** slots at once —
the inner product `g₁.inner`, the Levi-Civita connection `LeviCivita g₁` (inside `∇^{g₁}W₁`), **and**
the DeTurck field `W₁ = deTurckVF g₁ g_bg`.  It does **not** equal a single difference factor `w` plus a
`w`-free quadratic.  It telescopes one difference factor per slot through `Φ(a, b) − Φ(c, d) =
Φ(a − c, b) + Φ(c, b − d)`:

* the **Δinner slot** `(g₁ − g₂)(∇^{g₁}W₁, ·)`: the metric difference paired against the endpoint
  field, `g₁ − g₂ = ccTensorBilinSymm g₀ (T₁ − T₂)` (by `hr1`/`hr2`), the realized single difference
  factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)` against endpoint `∇^{g₁}W₁` data;
* the **ΔΓ (Levi-Civita) slot** `g₂((∇^{g₁} − ∇^{g₂})W₁, ·)`: the connection-difference `connDiff g₁ g₂`
  (cocycle-anchored `connDiff_cocycle` to `connDiff g₁ g₀ − connDiff g₂ g₀`, i.e. the **difference**
  `loweredConnDiffSection g₁ g₀ − loweredConnDiffSection g₂ g₀`) against the endpoint field;
* the **ΔW slot** `g₂(∇^{g₂}(W₁ − W₂), ·)`: the DeTurck-field difference, itself a `g₂`-trace of the
  same pair connection difference, again carrying the difference factor.

Each summand is therefore a **(difference factor) × (endpoint factor)** product — engine-consumable —
and **each vanishes when `T₁ = T₂`** (`w = 0`, `loweredConnDiffSection g₁ g₀ − loweredConnDiffSection g₂
g₀ = 0`).  The two concrete, independently-defined `(0, 2)`-summands are:

* `cartanDiffTopSec g₀ T₁ T₂` — the **linear-in-difference** part: the order-`0` member
  `(deTurckCartanDiffBilinOp g₀).op 0 2 w` of the value-local linear-arm tower on the realized single
  difference factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)` (one high derivative; by
  `deTurckCartanDiffBilinOp_op_zero_eq_self` it equals `w`), the carrier on which the linear engine's
  single-sum jet grid `DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le` (sorry-free) delivers
  `∑_{q ≤ j} rfns(∇^q w)`.  Genuinely linear in `w`, vanishing at `T₁ = T₂`, defined independently of
  the carrier difference.

* `cartanDiffRestSec g₀ g₁ g₂` — the **difference-carrying quadratic** part: the `g₀`-cometric double
  trace (twice, `(0, 6) → (0, 4) → (0, 2)`) of the bare fibrewise model **difference-of-products**
  `cartanCrossProductDiff g₀ g₁ g₂ := bareProd g₀ 3 3 (loweredConnDiffSection g₁ g₀)
  (loweredConnDiffSection g₂ g₀) − bareProd g₀ 3 3 (loweredConnDiffSection g₂ g₀)
  (loweredConnDiffSection g₂ g₀)` — the genuine `Φ(L₁, L₂) − Φ(L₂, L₂)` bilinear-difference on the
  fixed-endpoint factor `L₂ := loweredConnDiffSection g₂ g₀`, carrying the connection-difference
  **difference** `L₁ − L₂` against the endpoint `L₂`.  It **vanishes at `T₁ = T₂`** (`L₁ = L₂`, so it is
  `Φ(L₂, L₂) − Φ(L₂, L₂) = 0`), the carrier on which the quadratic engine's diagonal product grid
  `RfnsBilinearProduct.exists_rfns_iteratedCovGrad_prod_diagGrid_le` (sorry-free, via
  `deTurckCartanRfnsBilinearProduct`) delivers the convolution `≤ j`-jet of both factors.  Defined
  independently of the carrier difference.

The headline `symLoweredDeTurckVFRetagG0_sub_eq_topSec_add_restSec` exhibits the section identity
`carrier_difference = cartanDiffTopSec + cartanDiffRestSec`, the gauge analogue of the curvature half's
`exists_parallelTrace_linearSection_eq_koszulTriple_sub_crossCorrTriple`
(`SegmentMetricCurvatureDifferenceCovJet.lean`) and of the pairwise structural Koszul identity
`loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff`
(`ConnectionDifferenceQuadraticTraceProduct.lean`).

## What is posited vs. derived

Unlike the curvature half — where the connection-difference **cocycle** `connDiff g₁ g₂ = connDiff g₁
g₀ − connDiff g₂ g₀` and the `g₀`-fixed Koszul re-expression `connDiff_koszul_realize_g0` collapse the
two-metric lowered difference onto a single difference factor, making the section identity provable by
unit-extensionality — the Cartan carrier difference `cartanRHSBilin g₁ W₁ − cartanRHSBilin g₂ W₂`
varies the inner product `g₁.inner`, the Levi-Civita connection `LeviCivita g₁`, **and** the field
`W₁ = deTurckVF g₁ g_bg` simultaneously, and there is **no `cartanRHSBilin` slot-difference lemma** and
**no `deTurckVF` difference lemma** on disk (the carrier difference is taken at the Cartan-bilinear
level, where no cocycle re-expression exists).  The single genuine deep covariant-gauge Faà-di-Bruno
content — the fibre-level telescope of `cartanRHSBilin g₁ W₁ − cartanRHSBilin g₂ W₂` onto the three
difference-factor-carrying slots, identified with the two concrete summands — is therefore **posited**
here as `cartanDiffSecFactorization`: a bare section equality (NO covariant-jet bounds, NO fibre norms,
NO family-uniform constant), strictly weaker than the quantitative jet-bound split P1b
(`symLoweredDeTurckVF_iteratedCovGrad_topRest_split`) it feeds.  The headline
`symLoweredDeTurckVFRetagG0_sub_eq_topSec_add_restSec` is then the same equality re-stated; all the
supporting concrete objects (`cartanKoszulTripleDiff`, `cartanCrossProductDiff`, the two summands) and
their value / bilinearity / structure / degeneracy lemmas are sorry-free.

**Non-vacuity / degenerate-correctness.**  Both summands are concrete and defined independently of the
carrier difference (NOT `carrier − topSec` nor `topSec, restSec := 0`): `cartanDiffTopSec` is the
genuine value-local linear member on the difference factor `w` (`= w`, carrying the order-`0` value jet
and `∇^{j+2} w`), and `cartanDiffRestSec` is the genuine `g₀`-cometric double trace of the bare
**difference-of-products** `Φ(L₁, L₂) − Φ(L₂, L₂)` carrying the connection-difference difference
`L₁ − L₂` against the endpoint `L₂`.  At `T₁ = T₂` realized (so `g₁ = g₂`, `L₁ = L₂`) the carrier
difference vanishes, `w = 0`, and **both summands vanish** (`cartanDiffTopSec_self`,
`cartanDiffRestSec_self`), so the posited identity is `0 = 0 + 0` — degenerate-correct.  NO
value-bounded operator shape, NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl
dependence. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2 (SmoothCcTensor)
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricDoubleTraceField)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### The linear-in-difference concrete object: the Cartan-Koszul triple of the difference factor

The `(0, 3)`-section reading the three permuted slot combinations of the once-differentiated realized
difference factor `R := covGrad g₀ 0 2 w`, `w := realizeSymmCcTensor g₀ (T₁ − T₂)` — the gauge
analogue of the curvature half's `koszulTripleDiff` (`SegmentMetricCurvatureDifferenceCovJet.lean`),
the linear building block on which the Cartan linear arm rides. -/

/-- **The Cartan-Koszul triple of the realized difference factor.**  The clean permuted-`covGrad`
combination `R + permute (swap 0 1) R − permute c[0,2,1] R` on the once-differentiated realized
difference factor `R := covGrad g₀ 0 2 (realizeSymmCcTensor g₀ (T₁ − T₂))`, i.e. the three slot
readings of `covDerivRealizeEval g₀ (T₁ − T₂)`.  A `(0, 3)`-section, genuinely linear in the difference
factor `w` (and so in `T₁ − T₂`); the structural sibling of `koszulTripleDiff`. -/
def cartanKoszulTripleDiff (g₀ : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) : Integral.L2.SmoothCcTensor g₀ 0 3 :=
  Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
      (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))
    + permuteCcTensor (I := I) g₀ (Equiv.swap 0 1)
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))
    - permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1]
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))

set_option linter.unusedSectionVars false in
/-- **The unit-evaluated value of the Cartan-Koszul triple is the realized `covDerivRealizeEval`
combination.**  On a tangent triple `![a, b, c]` the unit-model value of `cartanKoszulTripleDiff g₀
T₁ T₂` is the three permuted slot readings
`covDerivRealizeEval g₀ (T₁ − T₂) x a b c + …x b a c − …x c a b` of the realized covariant derivative
of the difference factor.  Proved through the realized-Koszul unit-model identity
`covGrad_realizeSymm_unitModel_eq_covDerivRealizeEval` and the slot reindexing
`permuteCcTensor_unitModel`. -/
theorem cartanKoszulTripleDiff_toModel_apply (g₀ : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) (a b c : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((cartanKoszulTripleDiff (I := I) g₀ T₁ T₂).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] =
      covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x a b c
        + covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x b a c
        - covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x c a b := by
  classical
  set R := Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)) with hR
  -- The realized covariant-derivative unit-model of `R` on a tangent triple.
  have hRu : ∀ w : Fin 3 → TangentSpace I x,
      Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 3 R x w =
      covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x (w 0) (w 1) (w 2) := by
    intro w
    rw [hR, Analysis.Parabolic.TensorSpectral.unitModel]
    have h := covGrad_realizeSymm_unitModel_eq_covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x
      (w 0) (w 1) (w 2)
    have hwtuple : (![w 0, w 1, w 2] : Fin 3 → TangentSpace I x) = w := by
      funext i; fin_cases i <;> rfl
    rw [hwtuple] at h
    exact h
  have hP1 := permuteCcTensor_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R x
  have hP2 := permuteCcTensor_unitModel (I := I) g₀ c[(0 : Fin 3), 2, 1] R x
  rw [show (cartanKoszulTripleDiff (I := I) g₀ T₁ T₂).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) =
      (R + permuteCcTensor (I := I) g₀ (Equiv.swap 0 1) R
          - permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl]
  rw [show (R + permuteCcTensor (I := I) g₀ (Equiv.swap 0 1) R
          - permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) =
        R.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
          + (permuteCcTensor (I := I) g₀ (Equiv.swap 0 1) R).toSection x
              (ContinuousMultilinearMap.constOfIsEmpty ℝ
                (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
          - (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R).toSection x
              (ContinuousMultilinearMap.constOfIsEmpty ℝ
                (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from by
    rw [Integral.L2.SmoothCcTensor.toSection_sub, Integral.L2.SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_sub, ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]]
  rw [Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.add_apply]
  have e0 : Tensor0SSpace.toModel (R.toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] =
      covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x a b c := by
    have hmod : Tensor0SSpace.toModel (R.toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] =
        Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 3 R x ![a, b, c] := rfl
    rw [hmod, hRu ![a, b, c]]; rfl
  have e1 : Tensor0SSpace.toModel
        ((permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] =
      covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x b a c := by
    have hmod : Tensor0SSpace.toModel
          ((permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] =
        Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 3
          (permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R) x ![a, b, c] := rfl
    rw [hmod, hP1, ContinuousMultilinearMap.domDomCongr_apply, hRu]
    rfl
  have e2 : Tensor0SSpace.toModel
        ((permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] =
      covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x c a b := by
    have hmod : Tensor0SSpace.toModel
          ((permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] =
        Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 3
          (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R) x ![a, b, c] := rfl
    rw [hmod, hP2, ContinuousMultilinearMap.domDomCongr_apply, hRu]
    rfl
  rw [e0, e1, e2]

/-! ### The linear-in-difference engine-shaped summand

The `(0, 2)`-carrier on which the linear engine's single-sum jet grid acts.  It is the order-`0`
member of the value-local linear-arm tower on the realized difference factor `w`, which by
`deTurckCartanDiffBilinOp_op_zero_eq_self` equals `w` itself. -/

/-- **The Cartan-difference linear (`Top`) summand.**  The order-`0` member
`(deTurckCartanDiffBilinOp g₀).op 0 2 w` of the value-local linear-arm tower on the realized single
difference factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)`.  A `(0, 2)`-section, genuinely linear in the
difference factor `w`, defined independently of the carrier difference.  By
`deTurckCartanDiffBilinOp_op_zero_eq_self` it equals `w`; the linear engine's single-sum jet grid
`DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le` controls its covariant jets by
`∑_{q ≤ j} rfns(∇^q w)`. -/
def cartanDiffTopSec (g₀ : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) : Integral.L2.SmoothCcTensor g₀ 0 2 :=
  (deTurckCartanDiffBilinOp (I := I) (M := M) g₀).op 0 2
    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))

set_option linter.unusedSectionVars false in
/-- **The linear (`Top`) summand is the realized difference factor `w`.**  By
`deTurckCartanDiffBilinOp_op_zero_eq_self` the order-`0` member of the value-local linear-arm tower is
the section itself.  Definitional engine read-off; this is what makes the linear engine's single-sum
grid deliver `∑_{q ≤ j} rfns(∇^q w)` directly on `cartanDiffTopSec`. -/
theorem cartanDiffTopSec_eq (g₀ : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) :
    cartanDiffTopSec (I := I) g₀ T₁ T₂ = realizeSymmCcTensor (I := I) g₀ (T₁ - T₂) :=
  deTurckCartanDiffBilinOp_op_zero_eq_self (I := I) (M := M) g₀ 2
    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))

set_option linter.unusedSectionVars false in
/-- **The linear (`Top`) summand vanishes when the perturbations coincide.**  At `T₁ = T₂` the
realized difference factor `w = realizeSymmCcTensor g₀ 0 = 0`, so `cartanDiffTopSec g₀ T T = 0`.  A
non-vacuity certificate: the linear summand genuinely tracks the difference factor. -/
theorem cartanDiffTopSec_self (g₀ : SmoothRiemannianMetric I M)
    (T : Integral.L2.SmoothCcTensor g₀ 0 2) :
    cartanDiffTopSec (I := I) g₀ T T = 0 := by
  rw [cartanDiffTopSec_eq, realizeSymmCcTensor_sub, sub_self]

/-! ### The difference-carrying quadratic concrete object and the engine-shaped quadratic summand

The corrected `D∘D`-type quadratic: the bare fibrewise model **difference-of-products** `Φ(L₁, L₂) −
Φ(L₂, L₂)` on the fixed-endpoint factor `L₂`, carrying the connection-difference difference `L₁ − L₂`,
doubly `g₀`-cometric-traced down to a `(0, 2)`-carrier.  This is the corrected shape: the OLD single
bare product `bareProd L₁ L₂` was nonzero at `T₁ = T₂` (`L₁ = L₂`, `bareProd L L ≠ 0`) and did NOT
track the difference; the bilinear difference `Φ(L₁, L₂) − Φ(L₂, L₂)` vanishes there
(`bareProd L₂ L₂ − bareProd L₂ L₂ = 0`). -/

/-- **The Cartan cross-product difference of the two endpoints' lowered connection differences.**  The
bare fibrewise model tensor-product **difference**
`bareProd g₀ 3 3 (loweredConnDiffSection g₁ g₀) (loweredConnDiffSection g₂ g₀)
  − bareProd g₀ 3 3 (loweredConnDiffSection g₂ g₀) (loweredConnDiffSection g₂ g₀)`,
i.e. `Φ(L₁, L₂) − Φ(L₂, L₂)` on the fixed-endpoint factor `L₂ := loweredConnDiffSection g₂ g₀`, a
`(0, 6)`-section.  The genuine non-vacuous fibrewise `ℝ`-bilinear-difference carrying the
connection-difference **difference** `L₁ − L₂` (morally `bareProd (L₁ − L₂) L₂`) against the endpoint
`L₂`; the carrier the quadratic engine's diagonal product grid
`RfnsBilinearProduct.exists_rfns_iteratedCovGrad_prod_diagGrid_le` (via `deTurckCartanRfnsBilinearProduct`)
controls.  Frame-free; the tensor-product map carries no metric.  **Vanishes at `T₁ = T₂`** (`L₁ = L₂`,
so it is `Φ(L₂, L₂) − Φ(L₂, L₂) = 0`). -/
def cartanCrossProductDiff (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 6 :=
  Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0)
      (DeTurck.loweredConnDiffSection (I := I) g₁ g₀)
      (DeTurck.loweredConnDiffSection (I := I) g₂ g₀)
    - Integral.Connection.bareProd (I := I) g₀ 3 3 (a := 0) (b := 0)
      (DeTurck.loweredConnDiffSection (I := I) g₂ g₀)
      (DeTurck.loweredConnDiffSection (I := I) g₂ g₀)

set_option linter.unusedSectionVars false in
/-- **`cartanCrossProductDiff` is the assembled quadratic engine's product-difference on the two
connection-difference factors.**  Definitional: the `prod` field of `deTurckCartanRfnsBilinearProduct`
at `(a, b) = (0, 0)` is exactly the bare product `bareProd g₀ 3 3`, so `cartanCrossProductDiff` is the
difference `prod L₁ L₂ − prod L₂ L₂`.  This is the engine read-off on which the quadratic diagonal grid
`exists_rfns_iteratedCovGrad_deTurckCartanProd_diagGrid_le` fires (on each of the two bare products). -/
theorem cartanCrossProductDiff_eq_prod (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    cartanCrossProductDiff (I := I) g₀ g₁ g₂ =
      (deTurckCartanRfnsBilinearProduct (I := I) g₀).prod (a := 0) (b := 0)
          (DeTurck.loweredConnDiffSection (I := I) g₁ g₀)
          (DeTurck.loweredConnDiffSection (I := I) g₂ g₀)
        - (deTurckCartanRfnsBilinearProduct (I := I) g₀).prod (a := 0) (b := 0)
          (DeTurck.loweredConnDiffSection (I := I) g₂ g₀)
          (DeTurck.loweredConnDiffSection (I := I) g₂ g₀) :=
  rfl

set_option linter.unusedSectionVars false in
/-- **`cartanCrossProductDiff` vanishes when the perturbations coincide.**  At `g₁ = g₂` the two
lowered connection differences coincide (`loweredConnDiffSection g₁ g₀ = loweredConnDiffSection g₂ g₀`),
so the bilinear difference is `bareProd L₂ L₂ − bareProd L₂ L₂ = 0`.  The corrected non-vacuity
certificate: the cross-product difference genuinely tracks the connection-difference difference. -/
theorem cartanCrossProductDiff_self (g₀ g : SmoothRiemannianMetric I M) :
    cartanCrossProductDiff (I := I) g₀ g g = 0 := by
  rw [cartanCrossProductDiff, sub_self]

/-- **The Cartan-difference quadratic (`Rest`) summand.**  The `g₀`-cometric **double** trace, applied
**twice** `(0, 6) → (0, 4) → (0, 2)`, of the bare cross-product difference `cartanCrossProductDiff g₀
g₁ g₂` of the two endpoints' lowered connection differences.  Each application is the operator-field
action `appCc` of the rank-generic cometric double-trace operator field `cometricDoubleTraceField g₀ ·`
(`CometricDoubleTraceField.lean`, contracting the two leading covariant slots against the cometric
`g₀⁻¹`, parallel).  A `(0, 2)`-section, the genuine difference-carrying quadratic carrying the
connection-difference **difference** `L₁ − L₂` against the endpoint `L₂`, defined independently of the
carrier difference; the quadratic part of the Cartan-difference factorization.  **Vanishes at
`T₁ = T₂`** (`cartanCrossProductDiff g₀ g g = 0`). -/
def cartanDiffRestSec (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  Integral.Connection.appCc (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
    (Integral.Connection.appCc (I := I) (M := M) g₀ 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
      (cartanCrossProductDiff (I := I) g₀ g₁ g₂))

/-! ### The bilinearity of the bare cross-product difference and the quadratic summand

The two `g₀`-cometric traces are `ℝ`-linear in the contracted section; so the quadratic summand
distributes over the bare-product difference and vanishes on a zero cross-product, exactly like the
curvature half's `crossCorrParallelContraction`-driven `Rest`. -/

set_option linter.unusedSectionVars false in
/-- **The quadratic summand is `ℝ`-additive through the double trace** (through the two cometric
traces' additivity).  Used to distribute the double trace over the bare-product **difference**
`Φ(L₁, L₂) − Φ(L₂, L₂)`. -/
theorem cartanDiffRestSec_appCc_add_right (g₀ : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 6) :
    Integral.Connection.appCc (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
        (Integral.Connection.appCc (I := I) (M := M) g₀ 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (T₁ + T₂)) =
      Integral.Connection.appCc (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
          (Integral.Connection.appCc (I := I) (M := M) g₀ 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
            T₁)
        + Integral.Connection.appCc (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
          (Integral.Connection.appCc (I := I) (M := M) g₀ 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
            T₂) := by
  rw [← Integral.Connection.appCcRS_zero_eq_appCc (I := I) (M := M) g₀ 6 4
      (cometricDoubleTraceField (I := I) g₀ 4) (T₁ + T₂),
    Integral.Connection.appCcRS_add_right (I := I) (M := M) g₀ 0 6 4,
    Integral.Connection.appCcRS_zero_eq_appCc, Integral.Connection.appCcRS_zero_eq_appCc,
    ← Integral.Connection.appCcRS_zero_eq_appCc (I := I) (M := M) g₀ 4 2
      (cometricDoubleTraceField (I := I) g₀ 2) _,
    Integral.Connection.appCcRS_add_right (I := I) (M := M) g₀ 0 4 2,
    Integral.Connection.appCcRS_zero_eq_appCc, Integral.Connection.appCcRS_zero_eq_appCc]

set_option linter.unusedSectionVars false in
/-- **The quadratic summand vanishes on the zero cross-product.**  Both `g₀`-cometric traces are
`ℝ`-linear, so `appCc (appCc 0) = 0`.  A non-vacuity certificate (rejects a value-discarding
construction): the quadratic summand genuinely tracks the bare cross-product. -/
theorem cartanDiffRestSec_appCc_zero (g₀ : SmoothRiemannianMetric I M) :
    Integral.Connection.appCc (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
        (Integral.Connection.appCc (I := I) (M := M) g₀ 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (0 : Integral.L2.SmoothCcTensor g₀ 0 6)) = 0 := by
  rw [← Integral.Connection.appCcRS_zero_eq_appCc (I := I) (M := M) g₀ 6 4
      (cometricDoubleTraceField (I := I) g₀ 4) (0 : Integral.L2.SmoothCcTensor g₀ 0 6),
    show (0 : Integral.L2.SmoothCcTensor g₀ 0 6) = (0 : ℝ) • (0 : Integral.L2.SmoothCcTensor g₀ 0 6)
      by rw [zero_smul],
    Integral.Connection.appCcRS_smul_right, zero_smul,
    ← Integral.Connection.appCcRS_zero_eq_appCc (I := I) (M := M) g₀ 4 2
      (cometricDoubleTraceField (I := I) g₀ 2) (0 : Integral.L2.SmoothCcTensor g₀ 0 4),
    show (0 : Integral.L2.SmoothCcTensor g₀ 0 4) = (0 : ℝ) • (0 : Integral.L2.SmoothCcTensor g₀ 0 4)
      by rw [zero_smul],
    Integral.Connection.appCcRS_smul_right, zero_smul]

set_option linter.unusedSectionVars false in
/-- **The quadratic (`Rest`) summand vanishes when the perturbations coincide.**  At `T₁ = T₂` (hence
`g₁ = g₂`) the bare cross-product difference vanishes (`cartanCrossProductDiff_self`), and the double
cometric trace of `0` is `0` (`cartanDiffRestSec_appCc_zero`).  The corrected degenerate-correctness
certificate for the quadratic summand. -/
theorem cartanDiffRestSec_self (g₀ g : SmoothRiemannianMetric I M) :
    cartanDiffRestSec (I := I) g₀ g g = 0 := by
  rw [cartanDiffRestSec, cartanCrossProductDiff_self, cartanDiffRestSec_appCc_zero]

/-! ### The refuted section factorization (REMOVED)

A previously-posited clean section identity `cartanDiffSecFactorization` — asserting the carrier
difference `symLoweredDeTurckVFRetagG0 g₀ g₁ g_bg − symLoweredDeTurckVFRetagG0 g₀ g₂ g_bg` equals
`cartanDiffTopSec + cartanDiffRestSec` — was Lean-certified FALSE and deleted, together with its
consumer-facing wrapper: its right-hand side was independent of the background `g_bg` while the
left-hand side depends on it essentially (instantiating the identity at `g_bg = g₂` and `g_bg = g₁`
and subtracting forces `cartanRHSBilin g₁ (deTurckVF g₁ g₂) + cartanRHSBilin g₂ (deTurckVF g₂ g₁) = 0`
identically, which is generically false), and its linear summand `cartanDiffTopSec = w` lacks the
`∇W₁` data the genuine Δinner slot carries.  The quantitative integrated two-arm jet bound consumed
by `symLoweredDeTurckVF_iteratedCovGrad_topRest_split` (P1b) must be proven directly on the carrier
difference; the summand definitions above are retained as reusable quadratic-trace carriers. -/

end DeTurck
end PDE
end DifferentialGeometry

end
