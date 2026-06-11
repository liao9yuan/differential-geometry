import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CrossCorrectionContractionCalculus
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.QuadraticProductRfnsGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckCartanRfnsBilinearProduct
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotExtendCovariantParallelism
import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceFieldJets
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricJetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging

/-! # The contraction-native cross-correction peeled `topRest` bound

The cross-correction `cc = crossCorrParallelContraction g₀ (realizeSymm T₁) (permute (loweredConnDiff
g₁ g₀))` is the `∇₀`-parallel `g₀`-single cometric contraction `h ⌟ D` of the realized symmetric
perturbation `h = realizeSymm T₁` (rank `2`) against the slot-cycled `g₀`-lowered connection difference
`D = loweredConnDiff g₁ g₀` (rank `3`).  Its order-`p` covariant jet splits, at the section level, into
the `i = 0` binomial **top** cell `Top_p = crossCorrParallelContraction g₀ (a := 0) (b := p) (realizeSymm
T₁) (∇^p (permute c[0,1,2] loweredConnDiff))` (all `p` derivatives on the connection-difference factor,
none on `h`) and the **rest** `∇^p cc − Top_p` (the `i ≥ 1` cells).

This file delivers the genuine deep frontier content of the `Rest` arm — the **contraction-native**
peeled two-arm bound

```
‖∇^p cc − Top_p‖² ≤ Cpk · (∑_{q < p} ‖∇^q loweredConnDiff‖² + ∑_{i ≤ p+1} ‖∇^i (realizeSymm T₁)‖²).
```

The route is contraction-native, not bare-product: the order-`p` jet of `cc` is read through the
operator-reduced two-section parallel covariant Leibniz of the contraction
(`crossCorrParallelContraction_covGrad`, iterated through the `p`-fold passenger extension of the fixed
`∇₀`-parallel cometric trace field), so the `Rest` is `appCcRS (slotExtendPow p (crossCorrCometricOp g₀
0 0))` acting on the **bare-product binomial remainder** `∇^p (crossCorrProdSection) − TopCell_p`.  The
`appCcRS` cometric envelope (`exists_uniform_riemannianFiberNormSq_appCcRS_le`) absorbs the cometric
into a fixed constant, and the bare-product **peel** (`exists_rfns_iteratedCovGrad_prod_topRest_diagGrid_
le`) keeps the lowered-connection-difference order **strictly below `p`** (`i < p`), so the difference
arm of the integrated Gagliardo–Nirenberg interpolation is capped at `p − 1` and never re-introduces the
top `∇^p D` term (the over-estimate of the symmetric-window engine).  The two factors' supercritical
`C⁰` fibre sups — `realizeSymm T₁`'s order-`0` jet (`exists_realizeSymm_iteratedCovGradJet2_sup_le`) and
`loweredConnDiff`'s fibre-small Koszul sup — feed the two-arm conversion.

The two genuinely-irreducible deep inputs are posited as precise children: the rectangular-window
integrated Gagliardo–Nirenberg two-arm engine (the difference-factor window strictly below the
fixed-factor window, the asymmetric companion of the symmetric engine) and the uniform `C⁰` fibre sup of
the lowered connection difference for the fibre-small perturbation family.  Everything else — the
operator-reduced covariant Leibniz, the slot reconciliation of the top cell, the bare-product peel, the
`appCcRS` cometric envelope, the realized factor's `C⁰` sup — is built here sorry-free. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-! ## The `p`-fold passenger slot extension and the iterated parallel operator-field Leibniz

These reproduce, as first-class upstream API (R1), the passenger-extension tower that the iterated
covariant gradient of a `∇₀`-parallel operator-field action produces.  They compose only the upstream
public operator-field calculus (`slotExtend`, `covGrad_appCcRS_eq`, `appCcRS_zero_left`,
`covGrad_slotExtend_eq_zero_of_covGrad_eq_zero`). -/

/-- **The `p`-fold passenger-slot extension of an operator field.**  `slotExtendPow p Φ` extends the
`(r, s)`-operator field `Φ` to the `(r + p, s + p)`-operator field obtained by inserting `p` leading
spectator slots one at a time.  It is the operator tower that the iterated parallel covariant Leibniz of
`appCcRS Φ` produces (each covariant gradient inserts one leading gradient direction as a spectator,
left uncontracted, `slotExtendFib_apply_eval`). -/
noncomputable def slotExtendPow (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∀ p : ℕ, Integral.L2.SmoothCcTensor g₀ r s → Integral.L2.SmoothCcTensor g₀ (r + p) (s + p)
  | 0 => fun Φ => Φ
  | (p + 1) => fun Φ => slotExtend (I := I) (M := M) g₀ (r + p) (s + p) (slotExtendPow g₀ r s p Φ)

set_option linter.unusedSectionVars false in
/-- The `p`-fold passenger-slot extension of a `∇₀`-parallel operator field is `∇₀`-parallel:
`slotExtend` preserves parallelism (`covGrad_slotExtend_eq_zero_of_covGrad_eq_zero`). -/
theorem covGrad_slotExtendPow_eq_zero (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : Integral.L2.SmoothCcTensor g₀ r s)
    (hΦ : Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ r s Φ = 0) (p : ℕ) :
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ (r + p) (s + p)
        (slotExtendPow (I := I) (M := M) g₀ r s p Φ) = 0 := by
  induction p with
  | zero => exact hΦ
  | succ p ih =>
    exact DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.covGrad_slotExtend_eq_zero_of_covGrad_eq_zero
      (I := I) (M := M) g₀ (r + p) (s + p) (slotExtendPow (I := I) (M := M) g₀ r s p Φ) ih

set_option linter.unusedSectionVars false in
/-- **The iterated parallel operator-field covariant Leibniz.**  For a `∇₀`-parallel operator field `Φ`
(`covGrad Φ = 0`), the order-`p` covariant gradient of the operator action `appCcRS Φ W` is the action
of the `p`-fold passenger extension on the order-`p` gradient of the contracted section:
```
∇^p (appCcRS Φ W) = appCcRS (slotExtendPow p Φ) (∇^p W).
```
Each covariant gradient splits by `covGrad_appCcRS_eq` into the differentiated-coefficient action (which
vanishes since `Φ` and its slot extensions are parallel) plus the slot-extended action on the gradient. -/
theorem iteratedCovGrad_appCcRS_of_parallel (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : Integral.L2.SmoothCcTensor g₀ b c)
    (hΦ : Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ b c Φ = 0)
    (W : Integral.L2.SmoothCcTensor g₀ a b) (p : ℕ) :
    PDE.RicciFlow.iteratedCovGrad (I := I) g₀ a c p (appCcRS (I := I) (M := M) g₀ a b c Φ W) =
      appCcRS (I := I) (M := M) g₀ a (b + p) (c + p)
        (slotExtendPow (I := I) (M := M) g₀ b c p Φ)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ a b p W) := by
  induction p with
  | zero =>
    rw [PDE.RicciFlow.iteratedCovGrad_zero, PDE.RicciFlow.iteratedCovGrad_zero]
    rfl
  | succ p ih =>
    rw [PDE.RicciFlow.iteratedCovGrad_succ, ih]
    rw [covGrad_appCcRS_eq (I := I) (M := M) g₀ a (b + p) (c + p)
      (slotExtendPow (I := I) (M := M) g₀ b c p Φ)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ a b p W)]
    rw [covGrad_slotExtendPow_eq_zero (I := I) (M := M) g₀ b c Φ hΦ p]
    rw [appCcRS_zero_left (I := I) (M := M) g₀ a (b + p) (c + p + 1)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ a b p W), zero_add]
    rw [PDE.RicciFlow.iteratedCovGrad_succ]
    rfl

/-! ## The realized factor's order-`0` `C⁰` fibre sup (sorry-free) -/

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The uniform order-`0` `C⁰` fibre sup of the realized symmetric perturbation.**  For the
supercritically `H^{2a}`-bounded (`2a > finrank + 4`) perturbation family, the order-`0` intrinsic
squared fibre norm of `realizeSymmCcTensor g₀ T₁` is uniformly bounded by a single constant over the
manifold:
```
∀ x, rfns(realizeSymm T₁)(x) ≤ Λ²,    Λ ≥ 0.
```
This is the order-`0` term of the supercritical `C²`-jet sup `exists_realizeSymm_iteratedCovGradJet2_
sup_le` (`iteratedCovGradJetSum g₀ (realizeSymm T₁) x ≤ C` dominates its `j = 0` summand
`‖(realizeSymm T₁).toSection x‖ = √rfns(realizeSymm T₁)(x)`); squaring gives the `C⁰` fibre sup. Proved
sorry-free over the realized-jet embedding. -/
theorem exists_realizeSymmCcTensor_rfns_fibre_sup_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) (B : ℝ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2),
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * a)
            (realizeSymmCcTensor (I := I) g₀ T₁)‖ ≤ B →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x) ≤ Λ ^ 2 := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_realizeSymm_iteratedCovGradJet2_sup_le (I := I) g₀ a ha B
  -- `rfns(realizeSymm)(x) ≤ (iteratedCovGradJetSum)² ≤ C²`: the `j = 0` term is `√rfns`, the engine sup is `C`.
  refine ⟨C, hC0, fun T₁ hball x => ?_⟩
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + 0) I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 0)
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + 1) I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + 2) I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 2)
  have hjet : iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x ≤ C :=
    hC T₁ hball x
  have hjet_nn : 0 ≤ iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x :=
    iteratedCovGradJetSum_nonneg (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x
  -- The order-`0` realize-jet `rfns` is `≤ C²` directly: bound `rfns` by the jet-sum-squared.
  have hrfns_le : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x) ≤
      iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x ^ 2 := by
    -- `rfns(realizeSymm)(x) = (√rfns)²` and `√rfns ≤ jetSum` (its `j = 0` summand), nonneg jetSum.
    have hsqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x)) ≤
        iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x := by
      -- The `j = 0` summand of the jet sum is `√rfns`; the other two summands are nonnegative.
      rw [iteratedCovGradJetSum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      have hhead : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x)) =
          ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 0
              (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x‖ :=
        (norm_toSection_eq_sqrt_riemannianFiberNormSq_installed (I := I) (M := M) g₀ 0 (2 + 0)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 0 (realizeSymmCcTensor (I := I) g₀ T₁)) x).symm
      rw [hhead]
      have h1nn : (0 : ℝ) ≤ ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 1
          (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x‖ := norm_nonneg _
      have h2nn : (0 : ℝ) ≤ ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 2
          (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x‖ := norm_nonneg _
      exact le_add_of_le_of_nonneg (le_add_of_nonneg_right h1nn) h2nn
    have hrfns_eq : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x) =
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x)) ^ 2 :=
      (Real.sq_sqrt (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x _)).symm
    rw [hrfns_eq]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
  exact le_trans hrfns_le (pow_le_pow_left₀ hjet_nn hjet 2)

set_option linter.unusedSectionVars false in
/-- **(POSITED CHILD — the metric-realization map's `H^{2k}`-Sobolev boundedness.)**  The realized
symmetric perturbation `realizeSymm T₁` is bounded in `H^{2a}` by the perturbation `T₁`'s `H^{p+3+a}`
norm, uniformly:
```
‖(realizeSymm T₁).toHs (2a)‖ ≤ C · ‖T₁.toHs (p + 3 + a)‖.
```
This is the `H^{2k}`-Sobolev analogue of the slot-swap fibre-jet isometry `flipCcTensor_iteratedCovGrad_
norm_eq` for the realization map `realizeSymm T = ½ T + ½ flip T` (the realization map is `ℝ`-linear and
slot-swap-bounded; the convex combination is `H^{2k}`-bounded by the triangle inequality and the slot-swap
`Hˢ`-isometry), as `2a ≤ p + 3 + a`.  It is the realization-map `Hˢ`-boundedness statement named in
`SegmentMetricJetBound`'s docstring as "supplied by the metric-realization Sobolev layer".

**Non-vacuity.**  A genuine `Hˢ`-bound (a `C = 0` witness forces `realizeSymm T₁ = 0` in `H^{2a}`, false
for a nonzero symmetric `T₁`).  At `T₁ = 0`, `realizeSymm 0 = 0` and the bound is `0 ≤ 0`.  Its body is
`sorry`: the realization-map `H^{2k}`-Sobolev boundedness. -/
theorem exists_realizeSymm_toHs_le (g₀ : SmoothRiemannianMetric I M) (p a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2),
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * a)
            (realizeSymmCcTensor (I := I) g₀ T₁)‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ :=
  sorry

/-! ## The two irreducible deep inputs (posited children) -/

set_option linter.unusedSectionVars false in
/-- **(POSITED CHILD — the uniform `C⁰` fibre sup of the lowered connection difference, fibre-small
Neumann-absorbed Koszul form.)**  For the fibre-small (`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`,
`δ < 1/2`) supercritically `H^{2 + a}`-bounded (`2a > finrank + 4`) perturbation family, the order-`0`
intrinsic squared fibre norm of the `g₀`-lowered connection difference `D = loweredConnDiffSection g₁ g₀`
is uniformly bounded by a single constant `Λ²` over the manifold:
```
∀ x, rfns(loweredConnDiffSection g₁ g₀)(x) ≤ Λ²,    Λ ≥ 0.
```

The fibre-pointwise Koszul triangle bound `connDiff_g0_fibre_abs_bound` controls
`|2·g₀(D · b a, c)|` by the `≤ 1`-jet evaluations `covDerivRealizeEval g₀ T₁` of `h = ccTensorBilinSymm
g₀ T₁` plus the self-referential perturbation·connection-difference correction `2·|h(D · b a, c)|`;
the realized `≤ 1`-jet is dominated by the supercritical `C¹` embedding (`2a > finrank + 4` through the
realized-jet sharp-order embedding of `T₁`), and the self-referential correction is divided out by the
`(1 − 2δ) > 0` Neumann absorption (the fibre-smallness `gFibreOpBound … δ`), giving the uniform `C⁰`
fibre sup with no residual `D`-jet.  This bound is **non-circular** with the downstream
`loweredConnDiffSection` covariant-jet `L²` bound (which folds the *high* jets into the `T₁` jets) — it
reads only the order-`0` fibre value through the order-`≤ 1` realized jet and the Neumann absorption,
both of which precede the high-order contraction development.

**Non-vacuity.**  The bound is a genuine fibre sup of `D` (a `Λ = 0` witness forces `D ≡ 0` at every
point, false whenever `g₁ ≠ g₀`).  At `T₁ = 0`, `ccTensorBilinSymm g₀ 0 = 0`, so `g₁ = g₀`, `D = 0`,
and `Λ = 0` works.  Its body is `sorry`: the genuine supercritical-`C¹` / Neumann-absorption fibre sup
of the lowered connection difference. -/
theorem exists_loweredConnDiffSection_rfns_fibre_sup_le
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ ≤ B →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((loweredConnDiffSection (I := I) g₁ g₀).toSection x) ≤ Λ ^ 2 :=
  sorry

set_option linter.unusedSectionVars false in
/-- **(POSITED CHILD — the rectangular-window integrated Gagliardo–Nirenberg two-arm bound.)**

The asymmetric companion of `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le` in which
the **difference-factor window** `kW` is strictly below the **fixed-factor window** `kT` (`kW < kT`).
For a section `U` dominated *pointwise* by the **peeled** diagonal product grid of the difference factor
`W` (running `i ≤ kW`, strictly below the top order) against the fixed factor `T` (running `l ≤ kT − i`),
```
rfns(∇^j U)(x) ≤ Cmid · ∑_{i ≤ kW} rfns(∇^i W)(x) · ∑_{l ≤ kT − i} rfns(∇^l T)(x),
```
with `C⁰` fibre sups `√rfns(W) ≤ Λ_W`, `√rfns(T) ≤ Λ_T`, the `L²`-norm-squared of `∇^j U` is bounded by
the two-arm sum with the **difference arm capped at `kW`** (never re-introducing the top `∇^{kT}` jet of
`W`) and the **cross arm at `kT`**:
```
‖∇^j U‖² ≤ Cd · (Λ_T² · ∑_{i ≤ kW} ‖∇^i W‖² + Λ_W² · ∑_{l ≤ kT} ‖∇^l T‖²).
```

This is the **rectangular-window** engine the contraction-native cross-correction `Rest` arm requires:
the bare-product peel delivers the grid with the difference factor strictly below the top order
(`i < p`, i.e. `kW = p − 1`), and the symmetric single-window engine's `∑_{i ≤ k}` output (which forces
`k = kT` to cover the fixed factor and thus re-introduces `∇^p W` on the difference arm) over-estimates.
The asymmetric window keeps the difference arm strictly below the top.  It is the rectangular companion
of the symmetric engine (`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le`); the deep
content is the same `Lᵖ` Gagliardo–Nirenberg interpolation, applied per cell with the two distinct
windows.

**Non-vacuity.**  `Cd` is uniform over `(U, W, T, Cmid, Λ_W, Λ_T)` (quantified before them); the
difference arm carries `W`'s jet scale up to `kW`, the cross arm `T`'s up to `kT`; at `Cmid = 0` (or
`W = 0`, `T = 0`) the grid vanishes and the bound is `0 ≤ 0`.  The difference window is genuinely
**strict** (`kW < kT`): the output difference arm stops at `kW`, never reaching `kT`.  Its body is
`sorry`: the rectangular-window `Lᵖ` Gagliardo–Nirenberg interpolation. -/
theorem exists_integrated_diagonalProductGrid_twoArm_rectangular_le
    (g : SmoothRiemannianMetric I M) (sU s₁ s₂ kW kT : ℕ) (hk : kW < kT) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (U : Integral.L2.SmoothCcTensor g 0 sU) (W : Integral.L2.SmoothCcTensor g 0 s₁)
        (T : Integral.L2.SmoothCcTensor g 0 s₂) (Cmid ΛW ΛT : ℝ),
        0 ≤ Cmid → 0 ≤ ΛW → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s₁ x (W.toSection x) ≤ ΛW ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x) ≤ ΛT ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 sU x (U.toSection x) ≤
            Cmid * ∑ i ∈ Finset.range (kW + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i W).toSection x)
                * ∑ l ∈ Finset.range (kT + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + l) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T).toSection x)) →
        ‖U‖ ^ 2 ≤
            Cd * (ΛT ^ 2 * ∑ i ∈ Finset.range (kW + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i W‖ ^ 2
              + ΛW ^ 2 * ∑ l ∈ Finset.range (kT + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2) :=
  sorry

/-! ## The contraction-native peeled `topRest` bound (the public deliverable) -/

set_option linter.unusedSectionVars false in
/-- **The order-`p` covariant jet of the cross-correction contraction is the slot-extended cometric
action on the order-`p` jet of the frame-free product section.**  Writing the contraction as
`appCcRS (crossCorrCometricOp g₀ 0 0) (crossCorrProdSection g₀ S T)` (`crossCorrParallelContraction_eq_
appCcRS`) of the `∇₀`-parallel cometric trace field (`crossCorrCometricOp_covGrad_eq_zero`), the iterated
parallel operator-field Leibniz carries `∇^p` through as the `p`-fold passenger extension:
```
∇^p (crossCorrParallelContraction g₀ S T)
  = appCcRS (slotExtendPow p (crossCorrCometricOp g₀ 0 0)) (∇^p (crossCorrProdSection g₀ S T)).
```
The cometric pair traces the two ORIGINAL product slots throughout; the `p` gradient directions ride as
leading spectators. -/
theorem crossCorrParallelContraction_iteratedCovGrad_eq_appCcRS_slotExtendPow
    (g₀ : SmoothRiemannianMetric I M)
    (S : Integral.L2.SmoothCcTensor g₀ 0 (2 + 0)) (T : Integral.L2.SmoothCcTensor g₀ 0 (3 + 0))
    (p : ℕ) :
    PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p
        (crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0) S T) =
      appCcRS (I := I) (M := M) g₀ 0 (((3 + 0) + (2 + 0)) + p) ((3 + 0 + 0) + p)
        (slotExtendPow (I := I) (M := M) g₀ ((3 + 0) + (2 + 0)) (3 + 0 + 0) p
          (crossCorrCometricOp (I := I) g₀ 0 0))
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 ((3 + 0) + (2 + 0)) p
          (crossCorrProdSection (I := I) g₀ (a := 0) (b := 0) S T)) := by
  rw [crossCorrParallelContraction_eq_appCcRS (I := I) g₀ (a := 0) (b := 0) S T]
  exact iteratedCovGrad_appCcRS_of_parallel (I := I) g₀ 0 ((3 + 0) + (2 + 0)) (3 + 0 + 0)
    (crossCorrCometricOp (I := I) g₀ 0 0)
    (crossCorrCometricOp_covGrad_eq_zero (I := I) g₀ 0 0)
    (crossCorrProdSection (I := I) g₀ (a := 0) (b := 0) S T) p

set_option linter.unusedSectionVars false in
/-- **(POSITED CHILD — the contraction-native per-cell cometric-annihilation `rfns` peel of the
cross-correction `Rest`, the operator-reconciliation + binomial-telescope frontier.)**

The pointwise intrinsic squared fibre norm of the order-`p` covariant `Rest` cell of the
cross-correction contraction — the difference `∇^p (crossCorrParallelContraction g₀ (realizeSymm T₁)
(permute c[0,1,2] lowered)) − Top_p`, with `Top_p = crossCorrParallelContraction g₀ (a := 0) (b := p)
(realizeSymm T₁) (∇^p (permute c[0,1,2] lowered))` the `i = 0` binomial cell (all `p` derivatives on the
connection-difference factor) — is dominated by the **peeled** diagonal-convolution grid in the two
factors, the connection-difference order running **strictly below `p`** (`i < p`):
```
rfns(∇^p cc − Top_p)(x)
  ≤ C p · ∑_{i < p} rfns(∇^i loweredConnDiffSection)(x) · ∑_{l ≤ p − i} rfns(∇^l (realizeSymm T₁))(x).
```

This is the genuine contraction-native deep content (the dispatch's pieces 1+2 in one consumer-minimal
grid).  The order-`p` jet of the contraction is `appCcRS (slotExtendPow p (crossCorrCometricOp g₀ 0 0))`
acting on `∇^p (crossCorrProdSection g₀ (realizeSymm T₁) (permute lowered))`
(`crossCorrParallelContraction_iteratedCovGrad_eq_appCcRS_slotExtendPow`, sorry-free above); the `Top_p`
cell reconciles with the slot-extended cometric action on the bare-product `i = 0` binomial cell
(`crossCorrCometricOp_eq_appCcRS`, slot permutation `crossCorrPerm 0 0` + `p` passengers vs
`crossCorrPerm 0 p`), so the `Rest` is the cometric envelope of the bare-product **binomial remainder**
`∇^p (crossCorrProdSection) − TopCell_p`.  The `appCcRS` cometric envelope
(`exists_uniform_riemannianFiberNormSq_appCcRS_le`) absorbs the trace into a fixed constant; the
bare-product **peel** (`exists_rfns_iteratedCovGrad_prod_topRest_diagGrid_le` on
`bareTensorRfnsBilinearProduct`) keeps the connection-difference order **strictly below `p`** — the
cometric trace annihilation that prevents the bare-product over-estimate of re-introducing `∇^p D` at the
internal cells.  The genuine remaining content is the operator-slot reconciliation
(`slotExtendPow p (crossCorrCometricOp 0 0)` vs `crossCorrCometricOp 0 p`) and the bare-product
binomial telescope under the two permutation conventions.

**Non-vacuity.**  Carries genuine content on the strictly-lower connection-difference jets `∑_{i<p}` and
the realized jets (a zero coefficient falsifies it whenever an `i ≥ 1` cell is genuinely present).  At
`p = 0` the grid is the empty sum, matching `Rest_0 = 0`.  At `T₁ = 0`, `ccTensorBilinSymm g₀ 0 = 0`, so
`cc = 0`, `Top_0 = 0`, and the bound is `0 ≤ 0`.  Its body is `sorry`: the operator-reconciliation +
bare-product binomial telescope under the cometric trace annihilation. -/
theorem crossCorrParallelContraction_iteratedCovGrad_rest_rfns_peel_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) :
    ∃ C : ℕ → ℝ, (∀ p, 0 ≤ C p) ∧ ∀ (x : M) (p : ℕ),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 0 + 0 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p
              (crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
                (realizeSymmCcTensor (I := I) g₀ T₁)
                (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
                  (loweredConnDiffSection (I := I) g₁ g₀)))
            - crossCorrParallelContraction (I := I) g₀ (a := 0) (b := p)
                (realizeSymmCcTensor (I := I) g₀ T₁)
                (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                  (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
                    (loweredConnDiffSection (I := I) g₁ g₀)))).toSection x) ≤
        C p * ∑ i ∈ Finset.range p,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i
                (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) *
            ∑ l ∈ Finset.range (p + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
                  (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x) :=
  sorry

set_option linter.unusedSectionVars false in
/-- **The contraction-native cross-correction peeled `topRest` bound (the public deliverable for the
`Rest` arm).**

The squared metric `L²` mass of the order-`p` covariant `Rest` cell of the cross-correction contraction
— the difference `∇^p (crossCorrParallelContraction g₀ (realizeSymm T₁) (permute c[0,1,2] lowered)) −
Top_p`, with `Top_p = crossCorrParallelContraction g₀ (a := 0) (b := p) (realizeSymm T₁) (∇^p (permute
c[0,1,2] lowered))` the `i = 0` binomial cell — is dominated, uniformly over the fibre-small (`gFibreOp
Bound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`) supercritically `H^{p+3+a}`-bounded (`2a > finrank +
4`) perturbation family, by the **contraction-native** two-arm grid: the connection-difference jets kept
**strictly below `p`** plus the `≤ (p+1)`-jet of the realized perturbation:
```
‖∇^p cc − Top_p‖² ≤ Cpk · (∑_{q < p} ‖∇^q loweredConnDiffSection‖² + ∑_{i ≤ p+1} ‖∇^i (realizeSymm T₁)‖²).
```

This is the form `crossCorrectionSection_iteratedCovGrad_rest_peel_realizeSymm_le` consumes (after the
sorry-free section identity `crossCorrParallelContraction_eq_crossCorrectionSection` rewrites the
contraction to `crossCorrectionSection`).  It is assembled sorry-free from the contraction-native peeled
`rfns` grid (`crossCorrParallelContraction_iteratedCovGrad_rest_rfns_peel_le`, the operator-reconciliation
+ cometric-trace-annihilation child) integrated by the **rectangular-window** Gagliardo–Nirenberg engine
(`exists_integrated_diagonalProductGrid_twoArm_rectangular_le`, difference-factor window `p − 1` strictly
below the fixed-factor window `p`) with the two factors' `C⁰` fibre sups — the lowered connection
difference's (`exists_loweredConnDiffSection_rfns_fibre_sup_le`) and the realized perturbation's
(`exists_realizeSymmCcTensor_rfns_fibre_sup_le`, sorry-free, fed by the realization-map `H^{2a}`
boundedness `exists_realizeSymm_toHs_le`).

**Non-vacuity.**  Carries genuine content on both the strictly-lower connection-difference jets `∑_{q<p}`
and the realized jets.  At `T₁ = 0`, `ccTensorBilinSymm g₀ 0 = 0`, so `cc = 0` and `Top_p = 0`, and the
bound is `0 ≤ 0`. -/
theorem crossCorrParallelContraction_iteratedCovGrad_rest_peel_realizeSymm_le
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Cpk : ℝ, 0 ≤ Cpk ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p
                (crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
                  (realizeSymmCcTensor (I := I) g₀ T₁)
                  (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
                    (loweredConnDiffSection (I := I) g₁ g₀)))
              - crossCorrParallelContraction (I := I) g₀ (a := 0) (b := p)
                  (realizeSymmCcTensor (I := I) g₀ T₁)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                    (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
                      (loweredConnDiffSection (I := I) g₁ g₀)))‖ ^ 2 ≤
          Cpk * (∑ q ∈ Finset.range p,
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                    (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
              + ∑ i ∈ Finset.range (p + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2) := by
  classical
  -- The realization-map `H^{2a}` size bound `B' := Crz·B` and the realized factor's `C⁰` fibre sup `ΛT`.
  obtain ⟨Crz, hCrz0, hCrz⟩ := exists_realizeSymm_toHs_le (I := I) g₀ p a
  obtain ⟨ΛT, hΛT0, hΛT⟩ := exists_realizeSymmCcTensor_rfns_fibre_sup_le (I := I) g₀ a ha (Crz * B)
  -- The lowered connection difference's `C⁰` fibre sup `ΛW`.
  obtain ⟨ΛW, hΛW0, hΛW⟩ := exists_loweredConnDiffSection_rfns_fibre_sup_le (I := I) g₀ p δ hδ0 hδ1 B a ha
  -- The rectangular-window two-arm GN engine constant (difference window `p−1` strictly below `p`).
  rcases Nat.eq_zero_or_pos p with hp0 | hppos
  · -- `p = 0`: `Rest_0 = 0`, the bound is `0 ≤ nonneg`.
    subst hp0
    refine ⟨0, le_refl 0, fun T₁ g₁ hr hfib hball => ?_⟩
    have hzero : (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) 0
            (crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
              (realizeSymmCcTensor (I := I) g₀ T₁)
              (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
                (loweredConnDiffSection (I := I) g₁ g₀)))
          - crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
              (realizeSymmCcTensor (I := I) g₀ T₁)
              (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 0
                (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
                  (loweredConnDiffSection (I := I) g₁ g₀)))) = 0 := by
      rw [PDE.RicciFlow.iteratedCovGrad_zero, PDE.RicciFlow.iteratedCovGrad_zero, sub_self]
    rw [hzero]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    positivity
  -- `p ≥ 1`: set the rectangular window `kW := p - 1 < p =: kT`; `U` is the rank-`(3+p)` `Rest`.
  obtain ⟨Cd, hCd0, hCd⟩ :=
    exists_integrated_diagonalProductGrid_twoArm_rectangular_le (I := I) g₀ (3 + 0 + 0 + p) 3 2
      (p - 1) p (by omega : p - 1 < p)
  refine ⟨Cd * (ΛT ^ 2 + ΛW ^ 2), by positivity, fun T₁ g₁ hr hfib hball => ?_⟩
  obtain ⟨Cgrid, hCgrid0, hCgrid⟩ :=
    crossCorrParallelContraction_iteratedCovGrad_rest_rfns_peel_le (I := I) g₀ g₁ T₁
  -- The realized factor's `H^{2a}` size bound from `T₁`'s `H^{p+3+a}` bound.
  have hballRz : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * a)
      (realizeSymmCcTensor (I := I) g₀ T₁)‖ ≤ Crz * B :=
    le_trans (hCrz T₁) (mul_le_mul_of_nonneg_left hball hCrz0)
  -- The two `C⁰` fibre sups, instantiated.
  have hΛTx : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
      ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x) ≤ ΛT ^ 2 := hΛT T₁ hballRz
  have hΛWx : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      ((loweredConnDiffSection (I := I) g₁ g₀).toSection x) ≤ ΛW ^ 2 := hΛW T₁ g₁ hr hfib hball
  -- The rank-`(3+p)` `Rest` section, fed to the rectangular engine as `U`.
  set Rest : Integral.L2.SmoothCcTensor g₀ 0 (3 + 0 + 0 + p) :=
    PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p
        (crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
          (realizeSymmCcTensor (I := I) g₀ T₁)
          (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
            (loweredConnDiffSection (I := I) g₁ g₀)))
      - crossCorrParallelContraction (I := I) g₀ (a := 0) (b := p)
          (realizeSymmCcTensor (I := I) g₀ T₁)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
            (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
              (loweredConnDiffSection (I := I) g₁ g₀))) with hRest_def
  -- The grid hypothesis the engine consumes: `rfns(Rest)(x) ≤ Cgrid·grid(p−1, p)`.
  have hgrid : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 0 + 0 + p) x
        (Rest.toSection x) ≤
      Cgrid p * ∑ i ∈ Finset.range ((p - 1) + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i
              (loweredConnDiffSection (I := I) g₁ g₀)).toSection x)
          * ∑ l ∈ Finset.range (p + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
                  (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x) := by
    intro x
    have hpe : (p - 1) + 1 = p := by omega
    rw [hpe, hRest_def]
    exact hCgrid x p
  -- Apply the rectangular engine; its output is the two-arm bound at windows `(p−1, p)`.
  have hmain := hCd Rest (loweredConnDiffSection (I := I) g₁ g₀) (realizeSymmCcTensor (I := I) g₀ T₁)
    (Cgrid p) ΛW ΛT (hCgrid0 p) hΛW0 hΛT0 hΛWx hΛTx hgrid
  -- The engine output windows `∑_{i≤p−1}‖∇^i lowered‖²` and `∑_{l≤p}‖∇^l realizeSymm‖²`.
  have hpe : (p - 1) + 1 = p := by omega
  rw [hpe] at hmain
  rw [hRest_def] at hmain
  -- Bound the target RHS by the engine output: lowered arm = `∑_{q<p}`, realize arm `∑_{l≤p} ≤ ∑_{i≤p+1}`.
  refine le_trans hmain ?_
  set LS := ∑ q ∈ Finset.range p,
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
    with hLS_def
  set RZ := ∑ l ∈ Finset.range (p + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2
    with hRZ_def
  set RS2 := ∑ i ∈ Finset.range (p + 1 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2
    with hRS2_def
  -- The engine's lowered arm `∑_{i≤p−1}` is `LS = ∑_{q<p}` (after `hpe`); the realize arm `RZ = ∑_{l≤p} ≤ RS2`.
  have hRz_le : RZ ≤ RS2 := by
    rw [hRZ_def, hRS2_def]
    have hsub : Finset.range (p + 1) ⊆ Finset.range (p + 1 + 1) := by
      intro i hi
      rw [Finset.mem_range] at hi ⊢
      omega
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro i _ _; positivity
  have hRzpnn : (0 : ℝ) ≤ RZ := by rw [hRZ_def]; exact Finset.sum_nonneg fun l _ => by positivity
  have hLSnn : 0 ≤ LS := by rw [hLS_def]; exact Finset.sum_nonneg fun q _ => by positivity
  have hRS2nn : 0 ≤ RS2 := le_trans hRzpnn hRz_le
  -- Combine: `Cd·(ΛT²·LS + ΛW²·RZ) ≤ Cd·(ΛT²+ΛW²)·(LS+RS2)`.
  have hΛT2nn : (0 : ℝ) ≤ ΛT ^ 2 := sq_nonneg ΛT
  have hΛW2nn : (0 : ℝ) ≤ ΛW ^ 2 := sq_nonneg ΛW
  have hinner : ΛT ^ 2 * LS + ΛW ^ 2 * RZ ≤ (ΛT ^ 2 + ΛW ^ 2) * (LS + RS2) := by
    have h1 : ΛT ^ 2 * LS ≤ ΛT ^ 2 * (LS + RS2) :=
      mul_le_mul_of_nonneg_left (by linarith) hΛT2nn
    have h2 : ΛW ^ 2 * RZ ≤ ΛW ^ 2 * (LS + RS2) :=
      mul_le_mul_of_nonneg_left (by linarith) hΛW2nn
    nlinarith [h1, h2, hΛT2nn, hΛW2nn, hLSnn, hRS2nn]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hinner hCd0

end Connection
end Integral
end DifferentialGeometry

end
