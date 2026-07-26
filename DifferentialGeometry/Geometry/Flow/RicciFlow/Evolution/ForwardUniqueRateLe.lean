import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueIBP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRmBounds
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The Kotschwar rate estimate `E' ≤ K·E − κ·D` (Route-K brick K4)

`Evolution/ForwardUniqueEnergy.lean` differentiates the forward-uniqueness energy exactly:
`HasDerivAt (forwardUniqueEnergy g₁ g₂) (forwardUniqueRate g₁ g₂ Adot Sdot t) t`.  This file
turns that exact rate into the Grönwall-facing **estimate** of
`ShortTime/FORWARD_UNIQUE_PRO_RULING.md` §6,

`forwardUniqueRate ≤ K · forwardUniqueEnergy − κ · forwardUniqueDissipation`,

where the dissipation is `D = ∫ |∇¹S₀₄|²_{g₁} dμ_{g₁}`.

## Main definitions

* `forwardUniqueDissipation g₁ Sfield t` — `D = ∫_M |∇^{g₁}S₀₄|²_{g₁} dμ_{g₁(t)}`.
* `rateRest g₁ g₂ Adot t x` — the rate integrand minus the principal pairing `2⟨Ṡ, S₀₄⟩`.

## Main results

* `l2Inner_eq_integral` — the **currency bridge**: the model `L²` pairing that
  `Evolution/ForwardUniqueIBP.lean` speaks is the integral of the fibre pairing `inner0S`
  that the energy is built from.  `intInner_lap_eq_neg` / `intInner_div_eq_neg` are the two
  integration-by-parts identities restated through it.
* `ricciDiffSq_le` — sub-lemma 1, the Ricci-difference trace bound.
* `sPart_le` — the analytic core: `∫2⟨Ṡ, S₀₄⟩ ≤ (ε − 2)·D + (ε⁻¹C_U + C_rem + 1)·E`.
* `rateRest_le` / `intRateRest_le` — the `h`-, `A`- and volume parts.
* `forwardUniqueRate_le` — the capstone `E′ ≤ K·E − D`.

## Hypothesis discipline

Every background/slab bound is a **named hypothesis argument**; nothing is hidden in an
instance or in an implicit uniformity.  The named slots and their producers are

* `hSdec` — the divergence-form decomposition of the `S₀₄` speed, in exactly the shape
  `rmLowComp_deriv` (`Evolution/ForwardUniqueRmDot.lean`) supplies it;
* `hAdot` — the K1C-b pointwise bound `|∂ₜA₀₃|² ≤ C(|h|² + |A|² + |∇¹S|²)`;
* `hU`, `hrem` — the flux and remainder bounds, in the shape `rmFluxNormSq_le` /
  `rmRemNormSq_le` (`Evolution/ForwardUniqueRmBounds.lean`) produce them;
* `hreact`, `hvol` — the slab bounds on the moving-metric reaction and on the
  moving-volume factor `½ tr_{g₁}(∂ₜg₁)`;
* the integrability side conditions, one per integrand actually split off.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]

section Young

/-! ## The `ε`-Young kit on covariant tensor fibres

`Tensor0SMetricIneq.lean` supplies Cauchy–Schwarz (`abs_inner0S_le`) and the balanced
polarization `two_inner0S_le`.  The absorption steps of the rate estimate need the
*unbalanced* form with a free parameter, so that the `|∇¹S₀₄|²` produced by a cross term can
be made a small multiple of the dissipation. -/

variable {s : Nat}

/-- **`ε`-Young on a tensor fibre.**  `2⟨A, B⟩ ≤ ε|A|² + ε⁻¹|B|²` for every `ε > 0`. -/
theorem two_inner0S_le_eps (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) {ε : Real} (hε : 0 < ε) :
    2 * inner0S (I := I) g x s A B ≤
      ε * normSq0S (I := I) g x s A + ε⁻¹ * normSq0S (I := I) g x s B := by
  set p := Real.sqrt (normSq0S (I := I) g x s A) with hp
  set q := Real.sqrt (normSq0S (I := I) g x s B) with hq
  have hpnn : 0 ≤ p := Real.sqrt_nonneg _
  have hqnn : 0 ≤ q := Real.sqrt_nonneg _
  have hp2 : p ^ 2 = normSq0S (I := I) g x s A :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) g x s A)
  have hq2 : q ^ 2 = normSq0S (I := I) g x s B :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) g x s B)
  have hcs : inner0S (I := I) g x s A B ≤ p * q :=
    le_trans (le_abs_self _) (abs_inner0S_le (I := I) g x s A B)
  have hkey : 0 ≤ ε⁻¹ * (ε * p - q) ^ 2 := by positivity
  have hexp : ε * p ^ 2 + ε⁻¹ * q ^ 2 - 2 * (p * q) = ε⁻¹ * (ε * p - q) ^ 2 := by
    field_simp
    ring
  rw [← hp2, ← hq2]
  linarith [hcs, hkey, hexp]

/-- **`ε`-Young with a sign flip.**  `-(2⟨A, B⟩) ≤ ε|A|² + ε⁻¹|B|²` for every `ε > 0`. -/
theorem neg_two_inner0S_le_eps (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) {ε : Real} (hε : 0 < ε) :
    -(2 * inner0S (I := I) g x s A B) ≤
      ε * normSq0S (I := I) g x s A + ε⁻¹ * normSq0S (I := I) g x s B := by
  set p := Real.sqrt (normSq0S (I := I) g x s A) with hp
  set q := Real.sqrt (normSq0S (I := I) g x s B) with hq
  have hpnn : 0 ≤ p := Real.sqrt_nonneg _
  have hqnn : 0 ≤ q := Real.sqrt_nonneg _
  have hp2 : p ^ 2 = normSq0S (I := I) g x s A :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) g x s A)
  have hq2 : q ^ 2 = normSq0S (I := I) g x s B :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) g x s B)
  have hcs : -inner0S (I := I) g x s A B ≤ p * q :=
    le_trans (neg_le_abs _) (abs_inner0S_le (I := I) g x s A B)
  have hkey : 0 ≤ ε⁻¹ * (ε * p - q) ^ 2 := by positivity
  have hexp : ε * p ^ 2 + ε⁻¹ * q ^ 2 - 2 * (p * q) = ε⁻¹ * (ε * p - q) ^ 2 := by
    field_simp
    ring
  rw [← hp2, ← hq2]
  linarith [hcs, hkey, hexp]

/-- Scaling of the fibre squared norm: `|c · A|² = c²|A|²`. -/
theorem normSq0S_smul (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (c : Real) (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (c • A) = c ^ 2 * normSq0S (I := I) g x s A := by
  rw [normSq0S_eq_inner, inner0S_smul_left, inner0S_smul_right, ← normSq0S_eq_inner]
  ring

end Young

section Density

/-! ## Pointwise algebra of the energy density -/

/-- The energy density is nonnegative. -/
theorem density_nonneg (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    0 ≤ forwardUniqueDensity (I := I) g₁ g₂ t x := by
  have h₁ : (0 : Real) ≤ metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [metricDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 2 _
  have h₂ : (0 : Real) ≤ connDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [connDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 3 _
  have h₃ : (0 : Real) ≤ rmDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [rmDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 4 _
  rw [forwardUniqueDensity]
  linarith

/-- Each carrier's squared norm is dominated by the energy density. -/
theorem metricDiffSq_le_dens (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ forwardUniqueDensity (I := I) g₁ g₂ t x := by
  have h₂ : (0 : Real) ≤ connDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [connDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 3 _
  have h₃ : (0 : Real) ≤ rmDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [rmDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 4 _
  rw [forwardUniqueDensity]
  linarith

theorem connDiffSq_le_dens (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    connDiffSq (I := I) (g₁ t) (g₂ t) x ≤ forwardUniqueDensity (I := I) g₁ g₂ t x := by
  have h₁ : (0 : Real) ≤ metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [metricDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 2 _
  have h₃ : (0 : Real) ≤ rmDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [rmDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 4 _
  rw [forwardUniqueDensity]
  linarith

theorem rmDiffSq_le_dens (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    rmDiffSq (I := I) (g₁ t) (g₂ t) x ≤ forwardUniqueDensity (I := I) g₁ g₂ t x := by
  have h₁ : (0 : Real) ≤ metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [metricDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 2 _
  have h₂ : (0 : Real) ≤ connDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [connDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 3 _
  rw [forwardUniqueDensity]
  linarith

end Density

section Dissipation

variable [CompactSpace M]

/-- **The Kotschwar dissipation** `D(t) = ∫_M |∇^{g₁}S₀₄|²_{g₁} dμ_{g₁(t)}`.

The gradient is the lane's own one-step Levi-Civita derivative `metricNabla0S`, and the
measure is the same moving Riemannian volume that carries `forwardUniqueEnergy`.  The
carrier `Sfield` is supplied as a smooth field: `rmDiffLowAt` is a pointwise family, and it
is the consumer's job (via `hcar`) to certify that `Sfield` realises it at time `t`. -/
def forwardUniqueDissipation (g₁ : Real → SmoothRiemannianMetric I M)
    (Sfield : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (t : Real) : Real :=
  ∫ x, normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) Sfield x)
    ∂(riemannianMeasureFamily (I := I) (M := M) g₁ t)

/-- The dissipation is nonnegative. -/
theorem dissipation_nonneg (g₁ : Real → SmoothRiemannianMetric I M)
    (Sfield : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (t : Real) :
    0 ≤ forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t :=
  integral_nonneg fun x => normSq0S_nonneg (I := I) (g₁ t) x 5 _

end Dissipation

section Pairing

/-! ## The lane-currency `L²` pairing

`Evolution/ForwardUniqueIBP.lean` proves integration by parts in the *model* currency
`tensorL2Inner g 0 s (ccLift0S g T).toFun …`, while the energy of
`Evolution/ForwardUniqueEnergy.lean` is an integral of the *fibre* pairing `inner0S`.  This
section identifies the two, so that the rate estimate can consume the IBP theorems directly
against the energy density.

The diagonal identification expands both sides in one `g`-orthonormal frame — the model side
through `tensorInnerPointwise_0s_eq_diag_sum_orthoFrame`, the fibre side through
`normSq0S_identity_eq_sum_sq` — and the off-diagonal case follows by polarisation.  (The
diagonal step re-derives the *private* `rfns_eq_normSq0S_unit` of
`HCGCompactness/MetricCovDerivBridge.lean:181`, itself already duplicated at
`HCGCompactness/UnifCurvatureJetBound.lean:477`; promoting that lemma is a dedup item for the
`RiemannianFiberNormSq` layer, not for this brick.) -/

variable {s : Nat}

/-- **The `r = 0` index-lowering is unit evaluation.** -/
private theorem lowerZero_unit (g : SmoothRiemannianMetric I M) (s : Nat) (x : M)
    (W : TensorRSSpace 0 s I x) (w : Fin (0 + s) → TangentSpace I x) :
    lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel W) w =
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W)
        (unitZeroSec (I := I) (M := M) x) (fun j : Fin s => w (Fin.natAdd 0 j)) := by
  rw [lowerAllUpperIndices_apply, separableFormAt_zero]
  rw [show (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => E) (1 : Real)) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) from rfl]
  rw [← toModel_tensorRS_apply (I := I) (M := M) 0 s x W (unitZeroSec (I := I) (M := M) x)]
  rfl

/-- Diagonal fibre/model identification of the `(0, s)` pointwise pairing. -/
private theorem innerPtDiag (g : SmoothRiemannianMetric I M) (s : Nat) (x : M)
    (W : TensorRSSpace 0 s I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) =
      normSq0S (I := I) g x s
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W)
          (unitZeroSec (I := I) (M := M) x)) := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  rw [show tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) =
      tensorInnerPointwise_0s (I := I) (M := M) (0 + s) g x
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel W))
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel W)) from rfl]
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (0 + s)
    basis hON _ _]
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) g x s basis
    (metricInverseInBasis_of_orthonormal (I := I) g basis hON) _]
  symm
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (finCongr (Nat.zero_add s).symm) (Equiv.refl _)) _ _ ?_
  intro slots
  rw [Tensor0SBundle.component0S_apply]
  rw [lowerZero_unit (I := I) g s x W]
  rw [sq]
  congr 1 <;>
    (congr 1; funext a;
     simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq];
     congr 1;
     apply Fin.ext;
     simp)

/-- **Fibre/model identification of the `(0, s)` pointwise pairing.**  The model Gram-matrix
pairing of two `(0, s)`-tensors, read through the unit-scalar `(0, s) ≃ (r = 0, s)`
identification, is the metric fibre pairing `inner0S` of their unit values. -/
theorem innerPt_eq_inner0S (g : SmoothRiemannianMetric I M) (s : Nat) (x : M)
    (W₁ W₂ : TensorRSSpace 0 s I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel W₁) (TensorRSSpace.toModel W₂) =
      inner0S (I := I) g x s
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W₁)
          (unitZeroSec (I := I) (M := M) x))
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W₂)
          (unitZeroSec (I := I) (M := M) x)) := by
  have hunit :
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W₁ + W₂)
          (unitZeroSec (I := I) (M := M) x) =
        (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W₁)
            (unitZeroSec (I := I) (M := M) x) +
          (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W₂)
            (unitZeroSec (I := I) (M := M) x) := rfl
  have h := innerPtDiag (I := I) g s x (W₁ + W₂)
  rw [TensorRSSpace.toModel_add, hunit, normSq0S_add,
    tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
    tensorInnerPointwise_add_right,
    innerPtDiag (I := I) g s x W₁, innerPtDiag (I := I) g s x W₂,
    tensorInnerPointwise_symm (I := I) (M := M) g 0 s x
      (TensorRSSpace.toModel W₂) (TensorRSSpace.toModel W₁)] at h
  linarith

/-- **The lane `L²` pairing is the integral of the fibre pairing.**  This is the bridge that
lets the rate estimate consume `l2Inner_nabla_eq_neg_div` /
`l2Inner_nabla_self_eq_neg_lap` (`Evolution/ForwardUniqueIBP.lean`) against the
`inner0S`-integrals that make up `forwardUniqueRate`. -/
theorem l2Inner_eq_integral (g : SmoothRiemannianMetric I M)
    (T T' : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    tensorL2Inner (I := I) (M := M) g 0 s
        (ccLift0S (I := I) g T).toFun (ccLift0S (I := I) g T').toFun =
      ∫ x, inner0S (I := I) g x s (T x) (T' x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [tensorL2Inner]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change tensorInnerPointwise (I := I) (M := M) g 0 s x
      ((ccLift0S (I := I) g T).toFun x) ((ccLift0S (I := I) g T').toFun x) =
    inner0S (I := I) g x s (T x) (T' x)
  rw [show (ccLift0S (I := I) g T).toFun x =
      TensorRSSpace.toModel ((ccLift0S (I := I) g T).toSection x) from rfl,
    show (ccLift0S (I := I) g T').toFun x =
      TensorRSSpace.toModel ((ccLift0S (I := I) g T').toSection x) from rfl,
    innerPt_eq_inner0S (I := I) g s x, ccLift0S_unit, ccLift0S_unit]

end Pairing

section RicciDiff

/-! ## Sub-lemma 1 — the Ricci-difference trace bound

Both Ricci tensors are traces of curvature: `Ric_i` is the pure contraction of the `(1,3)`
Riemann tensor of `∇^i`, and a pure contraction is recovered from *any* lowering by tracing
back with the *same* metric.  Taking `g₁` as that metric for both flows exhibits
`Ric₁ − Ric₂` as a `g₁`-trace of the Kotschwar carrier `S₀₄`; the trace representative `V`
and its norm bound are the named inputs here, so that a slot permutation or a residual
`h₀₂`-algebraic lowering defect can be absorbed on the producer side without changing this
estimate. -/

/-- **The Ricci-difference trace bound.**  If the Ricci difference is the `g₁`-trace of a
`(0,4)` representative `V` whose fibre norm is controlled by the curvature-difference density
(plus a background multiple of the metric-difference density), then

`|Ric₁ − Ric₂|²_{g₁} ≤ n⁴ · (|S₀₄|²_{g₁} + B · |h₀₂|²_{g₁})`,  `n = finrank ℝ E`.

The dimension factor is `traceNormSq_le` at `s = 2`; no other content is added. -/
theorem ricciDiffSq_le (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (V : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x) {B : Real}
    (htr : metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x =
      metricTraceFirstTwo0STensor (I := I) g₁ V)
    (hV : normSq0S (I := I) g₁ x 4 V ≤
      rmDiffSq (I := I) g₁ g₂ x + B * metricDiffSq (I := I) g₁ g₂ x) :
    normSq0S (I := I) g₁ x 2
        (metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x) ≤
      (Module.finrank Real E : Real) ^ 4 *
        (rmDiffSq (I := I) g₁ g₂ x + B * metricDiffSq (I := I) g₁ g₂ x) := by
  rw [htr]
  refine (traceNormSq_le (I := I) (s := 2) g₁ x V).trans ?_
  exact mul_le_mul_of_nonneg_left hV (by positivity)

end RicciDiff

section RateSplit

variable [CompactSpace M]

/-- **The non-principal part of the rate integrand.**  Everything in the integrand of
`forwardUniqueRate` except the curvature-difference pairing `2⟨Ṡ, S₀₄⟩`: the three
moving-metric reactions, the metric- and connection-difference pairings, and the
moving-volume term.  Only `2⟨Ṡ, S₀₄⟩` needs integration by parts, so isolating it keeps the
integral splitting to a single step. -/
def rateRest (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x) (t : Real) (x : M) : Real :=
  (movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
      (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
    2 * inner0S (I := I) (g₁ t) x 2 (metricDiffDot (I := I) g₁ g₂ t x)
      (metricDiffAt (I := I) (g₁ t) (g₂ t) x)) +
  (movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
      (connDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
    2 * inner0S (I := I) (g₁ t) x 3 (Adot t x)
      (connDiffLowAt (I := I) (g₁ t) (g₂ t) x)) +
  movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
      (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
  (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x *
    forwardUniqueDensity (I := I) g₁ g₂ t x

/-- The rate integrand splits as `rateRest + 2⟨Ṡ, S₀₄⟩`. -/
theorem rateIntegrand_eq (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : Real → (x : M) → Tensor0SSpace 4 I x) (t : Real) (x : M) :
    forwardUniqueDensityDot (I := I) g₁ g₂ Adot Sdot t x +
        (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x *
          forwardUniqueDensity (I := I) g₁ g₂ t x =
      rateRest (I := I) g₁ g₂ Adot t x +
        2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) := by
  rw [forwardUniqueDensityDot, rateRest]
  ring

/-- `forwardUniqueRate` as the integral of `rateRest` plus the integral of the
curvature-difference pairing, under the two integrability side conditions. -/
theorem rate_eq_add (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : Real → (x : M) → Tensor0SSpace 4 I x) (t : Real)
    (hrest : Integrable (fun x => rateRest (I := I) g₁ g₂ Adot t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hpair : Integrable
      (fun x => 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t)) :
    forwardUniqueRate (I := I) (M := M) g₁ g₂ Adot Sdot t =
      (∫ x, rateRest (I := I) g₁ g₂ Adot t x
        ∂(riemannianMeasureFamily (I := I) (M := M) g₁ t)) +
      ∫ x, 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g₁ t) := by
  rw [forwardUniqueRate, ← integral_add hrest hpair]
  refine integral_congr_ae ?_
  filter_upwards with x
  exact rateIntegrand_eq (I := I) g₁ g₂ Adot Sdot t x

end RateSplit

section IBPCurrency

variable [CompactSpace M] {s : Nat}

/-- **The Dirichlet identity in lane currency.**  `∫⟨Δ_g T, T⟩ = −∫|∇^g T|²` on a closed
manifold; `l2Inner_nabla_self_eq_neg_lap` transported through `l2Inner_eq_integral`. -/
theorem intInner_lap_eq_neg (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    (∫ x, inner0S (I := I) g x s (roughLap0SField (I := I) g T x) (T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      -∫ x, normSq0S (I := I) g x (s + 1) (metricNabla0S (I := I) g T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h := l2Inner_nabla_self_eq_neg_lap (I := I) g T
  rw [l2Inner_eq_integral (I := I) g (metricNabla0S (I := I) g T)
      (metricNabla0S (I := I) g T),
    l2Inner_eq_integral (I := I) g T (roughLap0SField (I := I) g T)] at h
  rw [show (∫ x, inner0S (I := I) g x s (roughLap0SField (I := I) g T x) (T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, inner0S (I := I) g x s (T x) (roughLap0SField (I := I) g T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) from
    integral_congr_ae (Filter.Eventually.of_forall fun x =>
      inner0S_comm (I := I) g x s _ _)]
  rw [show (∫ x, normSq0S (I := I) g x (s + 1) (metricNabla0S (I := I) g T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, inner0S (I := I) g x (s + 1) (metricNabla0S (I := I) g T x)
        (metricNabla0S (I := I) g T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) from rfl]
  linarith [h]

/-- **Integration by parts in lane currency.**  `∫⟨div_g V, T⟩ = −∫⟨∇^g T, V⟩` on a closed
manifold; `l2Inner_nabla_eq_neg_div` transported through `l2Inner_eq_integral`. -/
theorem intInner_div_eq_neg (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (V : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    (∫ x, inner0S (I := I) g x s (covDiv0SField (I := I) g V x) (T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      -∫ x, inner0S (I := I) g x (s + 1) (metricNabla0S (I := I) g T x) (V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h := l2Inner_nabla_eq_neg_div (I := I) g T V
  rw [l2Inner_eq_integral (I := I) g (metricNabla0S (I := I) g T) V,
    l2Inner_eq_integral (I := I) g T (covDiv0SField (I := I) g V)] at h
  rw [show (∫ x, inner0S (I := I) g x s (covDiv0SField (I := I) g V x) (T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, inner0S (I := I) g x s (T x) (covDiv0SField (I := I) g V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) from
    integral_congr_ae (Filter.Eventually.of_forall fun x =>
      inner0S_comm (I := I) g x s _ _)]
  linarith [h]

end IBPCurrency

section SPart

variable [CompactSpace M]

/-- **The `S₀₄`-part of the rate (the analytic core).**

With the curvature-difference speed decomposed in divergence form as
`Ṡ = Δ_{g₁}S₀₄ + div_{g₁}U₀₅ + rem` — exactly the shape `rmLowComp_deriv`
(`Evolution/ForwardUniqueRmDot.lean`) produces — the principal term integrates by parts to
`−2·D`, the flux cross term absorbs into `ε·D` by Young at the cost of `ε⁻¹·C_U·E`, and the
remainder is a plain zeroth-order Young step.  Altogether

`∫ 2⟨Ṡ, S₀₄⟩ ≤ (ε − 2)·D + (ε⁻¹·C_U + C_rem + 1)·E`.

The flux bound `hU` is the `rmFluxNormSq_le` shape (`|U₀₅|² ≤ C·|A₀₃|²·|Rm₂|²`, hence a
multiple of the density on a slab); `hrem` is the `rmRemNormSq_le` + `rmDotRem` shape.  The
integrability side conditions are named, one per integrand actually split off. -/
theorem sPart_le
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Sdot : Real → (x : M) → Tensor0SSpace 4 I x)
    (Sfield : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (rem : (x : M) → Tensor0SSpace 4 I x)
    {t ε C_U C_rem : Real} (hε : 0 < ε)
    (hcar : ∀ x, Sfield x = rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)
    (hSdec : ∀ x, Sdot t x =
      roughLap0SField (I := I) (g₁ t) Sfield x +
        covDiv0SField (I := I) (g₁ t) U x + rem x)
    (hU : ∀ x, normSq0S (I := I) (g₁ t) x 5 (U x) ≤
      C_U * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hrem : ∀ x, normSq0S (I := I) (g₁ t) x 4 (rem x) ≤
      C_rem * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hilap : Integrable (fun x => inner0S (I := I) (g₁ t) x 4
        (roughLap0SField (I := I) (g₁ t) Sfield x) (Sfield x))
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t)))
    (hidiv : Integrable (fun x => inner0S (I := I) (g₁ t) x 4
        (covDiv0SField (I := I) (g₁ t) U x) (Sfield x))
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t)))
    (hirem : Integrable (fun x => inner0S (I := I) (g₁ t) x 4 (rem x) (Sfield x))
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t)))
    (hinab : Integrable (fun x => inner0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) Sfield x) (U x))
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t)))
    (hidis : Integrable (fun x => normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) Sfield x))
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t)))
    (hidens : Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t))) :
    (∫ x, 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) (g₁ t))) ≤
      (ε - 2) * forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t +
        (ε⁻¹ * C_U + C_rem + 1) * forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t := by
  classical
  rw [forwardUniqueDissipation, forwardUniqueEnergy, riemannianMeasureFamily_def]
  set μ := riemannianVolumeMeasure (I := I) (M := M) (g₁ t) with hμ
  -- Step 1: the integrand splits along the divergence-form decomposition
  have hsplitPt : ∀ x, 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) =
      2 * inner0S (I := I) (g₁ t) x 4
          (roughLap0SField (I := I) (g₁ t) Sfield x) (Sfield x) +
        (2 * inner0S (I := I) (g₁ t) x 4 (covDiv0SField (I := I) (g₁ t) U x) (Sfield x) +
          2 * inner0S (I := I) (g₁ t) x 4 (rem x) (Sfield x)) := by
    intro x
    rw [← hcar x, hSdec x, inner0S_add_left, inner0S_add_left]
    ring
  have hsplit :
      (∫ x, 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ∂μ) =
        (∫ x, 2 * inner0S (I := I) (g₁ t) x 4
            (roughLap0SField (I := I) (g₁ t) Sfield x) (Sfield x) ∂μ) +
          ((∫ x, 2 * inner0S (I := I) (g₁ t) x 4
              (covDiv0SField (I := I) (g₁ t) U x) (Sfield x) ∂μ) +
            ∫ x, 2 * inner0S (I := I) (g₁ t) x 4 (rem x) (Sfield x) ∂μ) := by
    have hIBC : Integrable (fun x =>
        2 * inner0S (I := I) (g₁ t) x 4
            (covDiv0SField (I := I) (g₁ t) U x) (Sfield x) +
          2 * inner0S (I := I) (g₁ t) x 4 (rem x) (Sfield x)) μ :=
      (hidiv.const_mul 2).add (hirem.const_mul 2)
    have h1 :
        (∫ x, 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
            (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ∂μ) =
          ∫ x, (2 * inner0S (I := I) (g₁ t) x 4
              (roughLap0SField (I := I) (g₁ t) Sfield x) (Sfield x) +
            (2 * inner0S (I := I) (g₁ t) x 4
                (covDiv0SField (I := I) (g₁ t) U x) (Sfield x) +
              2 * inner0S (I := I) (g₁ t) x 4 (rem x) (Sfield x))) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hsplitPt)
    rw [h1, integral_add (hilap.const_mul 2) hIBC,
      integral_add (hidiv.const_mul 2) (hirem.const_mul 2)]
  -- Step 2: the principal term is exactly `-2 D`
  have hprin :
      (∫ x, 2 * inner0S (I := I) (g₁ t) x 4
          (roughLap0SField (I := I) (g₁ t) Sfield x) (Sfield x) ∂μ) =
        -2 * ∫ x, normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) Sfield x) ∂μ := by
    rw [integral_const_mul, intInner_lap_eq_neg (I := I) (g₁ t) Sfield]
    ring
  -- Step 3: the flux cross term absorbs by Young
  have hflux :
      (∫ x, 2 * inner0S (I := I) (g₁ t) x 4
          (covDiv0SField (I := I) (g₁ t) U x) (Sfield x) ∂μ) ≤
        ε * (∫ x, normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) Sfield x) ∂μ) +
          ε⁻¹ * C_U * ∫ x, forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ := by
    have hrewrite :
        (∫ x, 2 * inner0S (I := I) (g₁ t) x 4
            (covDiv0SField (I := I) (g₁ t) U x) (Sfield x) ∂μ) =
          ∫ x, -(2 * inner0S (I := I) (g₁ t) x 5
              (metricNabla0S (I := I) (g₁ t) Sfield x) (U x)) ∂μ := by
      rw [integral_const_mul, intInner_div_eq_neg (I := I) (g₁ t) Sfield U,
        show (∫ x, -(2 * inner0S (I := I) (g₁ t) x 5
              (metricNabla0S (I := I) (g₁ t) Sfield x) (U x)) ∂μ) =
            -∫ x, 2 * inner0S (I := I) (g₁ t) x 5
              (metricNabla0S (I := I) (g₁ t) Sfield x) (U x) ∂μ from
          integral_neg _]
      rw [integral_const_mul]
      ring
    have hptwise : ∀ x, -(2 * inner0S (I := I) (g₁ t) x 5
          (metricNabla0S (I := I) (g₁ t) Sfield x) (U x)) ≤
        ε * normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) Sfield x) +
          ε⁻¹ * C_U * forwardUniqueDensity (I := I) g₁ g₂ t x := by
      intro x
      refine le_trans (neg_two_inner0S_le_eps (I := I) (g₁ t) x 5 _ _ hε) ?_
      have hmul : ε⁻¹ * normSq0S (I := I) (g₁ t) x 5 (U x) ≤
          ε⁻¹ * (C_U * forwardUniqueDensity (I := I) g₁ g₂ t x) :=
        mul_le_mul_of_nonneg_left (hU x) (by positivity)
      have hassoc : ε⁻¹ * (C_U * forwardUniqueDensity (I := I) g₁ g₂ t x) =
          ε⁻¹ * C_U * forwardUniqueDensity (I := I) g₁ g₂ t x := by ring
      linarith [hmul, hassoc]
    have hIrhs : Integrable (fun x =>
        ε * normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) Sfield x) +
          ε⁻¹ * C_U * forwardUniqueDensity (I := I) g₁ g₂ t x) μ :=
      (hidis.const_mul ε).add (hidens.const_mul (ε⁻¹ * C_U))
    have hIlhs : Integrable (fun x =>
        -(2 * inner0S (I := I) (g₁ t) x 5
          (metricNabla0S (I := I) (g₁ t) Sfield x) (U x))) μ :=
      (hinab.const_mul 2).neg
    have hval :
        (∫ x, (ε * normSq0S (I := I) (g₁ t) x 5
              (metricNabla0S (I := I) (g₁ t) Sfield x) +
            ε⁻¹ * C_U * forwardUniqueDensity (I := I) g₁ g₂ t x) ∂μ) =
          ε * (∫ x, normSq0S (I := I) (g₁ t) x 5
              (metricNabla0S (I := I) (g₁ t) Sfield x) ∂μ) +
            ε⁻¹ * C_U * ∫ x, forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ := by
      rw [integral_add (hidis.const_mul ε) (hidens.const_mul (ε⁻¹ * C_U)),
        integral_const_mul, integral_const_mul]
    rw [hrewrite]
    exact le_trans (integral_mono hIlhs hIrhs hptwise) (le_of_eq hval)
  -- Step 4: the zeroth-order remainder
  have hremInt :
      (∫ x, 2 * inner0S (I := I) (g₁ t) x 4 (rem x) (Sfield x) ∂μ) ≤
        (C_rem + 1) * ∫ x, forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ := by
    have hptwise : ∀ x, 2 * inner0S (I := I) (g₁ t) x 4 (rem x) (Sfield x) ≤
        (C_rem + 1) * forwardUniqueDensity (I := I) g₁ g₂ t x := by
      intro x
      refine le_trans (two_inner0S_le (I := I) (g₁ t) x 4 (rem x) (Sfield x)) ?_
      have hSsq : normSq0S (I := I) (g₁ t) x 4 (Sfield x) =
          rmDiffSq (I := I) (g₁ t) (g₂ t) x := by
        rw [hcar x, rmDiffSq_def]
      have hSle := rmDiffSq_le_dens (I := I) g₁ g₂ t x
      have hr := hrem x
      have hexp : (C_rem + 1) * forwardUniqueDensity (I := I) g₁ g₂ t x =
          C_rem * forwardUniqueDensity (I := I) g₁ g₂ t x +
            forwardUniqueDensity (I := I) g₁ g₂ t x := by ring
      rw [hSsq]
      linarith
    exact le_trans (integral_mono (hirem.const_mul 2)
      (hidens.const_mul (C_rem + 1)) hptwise)
      (le_of_eq (integral_const_mul (C_rem + 1) _))
  -- Assembly
  set D := ∫ x, normSq0S (I := I) (g₁ t) x 5
    (metricNabla0S (I := I) (g₁ t) Sfield x) ∂μ with hDdef
  set En := ∫ x, forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ with hEndef
  rw [hsplit, hprin]
  have hring : (ε - 2) * D + (ε⁻¹ * C_U + C_rem + 1) * En =
      -2 * D + ((ε * D + ε⁻¹ * C_U * En) + (C_rem + 1) * En) := by ring
  linarith [hflux, hremInt, hring]

end SPart

section RestPart

variable [CompactSpace M]

/-- **Pointwise bound on the non-principal part of the rate integrand.**

The metric-difference pairing is closed by sub-lemma 1 (`hRic`, produced by `ricciDiffSq_le`),
the connection-difference pairing by the K1C-b bound `hAdot` — whose `|∇¹S₀₄|²` share is made
a *small* multiple `δ·C_A` of the dissipation density by the free Young parameter `δ` — the
three moving-metric reactions by the slab bound `hreact`, and the moving-volume factor by the
slab bound `hvol`.  Note `hAdot` is stated in the form implied by (and weaker than) the
ruling's `|∂ₜA₀₃|² ≤ C(|h₀₂|² + |A₀₃|² + |∇¹S₀₄|²)`, since `|h₀₂|² + |A₀₃|²` is at most the
energy density. -/
theorem rateRest_le (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sfield : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    {t δ C_A C_R C_Ric C_V : Real} (hδ : 0 < δ)
    (hreact : ∀ x,
      movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
          (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
          (connDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
      C_R * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hRic : ∀ x, normSq0S (I := I) (g₁ t) x 2
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) ≤
      C_Ric * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hAdot : ∀ x, normSq0S (I := I) (g₁ t) x 3 (Adot t x) ≤
      C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
        normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) Sfield x)))
    (hvol : ∀ x, (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V)
    (x : M) :
    rateRest (I := I) g₁ g₂ Adot t x ≤
      (C_R + 4 * C_Ric + 1 + δ * C_A + δ⁻¹ + C_V) *
          forwardUniqueDensity (I := I) g₁ g₂ t x +
        δ * C_A * normSq0S (I := I) (g₁ t) x 5
          (metricNabla0S (I := I) (g₁ t) Sfield x) := by
  have hdens := density_nonneg (I := I) g₁ g₂ t x
  -- the metric-difference pairing
  have hhdot : normSq0S (I := I) (g₁ t) x 2 (metricDiffDot (I := I) g₁ g₂ t x) =
      4 * normSq0S (I := I) (g₁ t) x 2
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) := by
    rw [metricDiffDot, normSq0S_smul]
    ring
  have hh : 2 * inner0S (I := I) (g₁ t) x 2 (metricDiffDot (I := I) g₁ g₂ t x)
        (metricDiffAt (I := I) (g₁ t) (g₂ t) x) ≤
      (4 * C_Ric + 1) * forwardUniqueDensity (I := I) g₁ g₂ t x := by
    refine le_trans (two_inner0S_le (I := I) (g₁ t) x 2 _ _) ?_
    have hm : normSq0S (I := I) (g₁ t) x 2 (metricDiffAt (I := I) (g₁ t) (g₂ t) x) =
        metricDiffSq (I := I) (g₁ t) (g₂ t) x := (metricDiffSq_def (I := I) _ _ x).symm
    have hmle := metricDiffSq_le_dens (I := I) g₁ g₂ t x
    have hR := hRic x
    have hexp : (4 * C_Ric + 1) * forwardUniqueDensity (I := I) g₁ g₂ t x =
        4 * (C_Ric * forwardUniqueDensity (I := I) g₁ g₂ t x) +
          forwardUniqueDensity (I := I) g₁ g₂ t x := by ring
    rw [hhdot, hm]
    linarith
  -- the connection-difference pairing
  have hA : 2 * inner0S (I := I) (g₁ t) x 3 (Adot t x)
        (connDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
      (δ * C_A + δ⁻¹) * forwardUniqueDensity (I := I) g₁ g₂ t x +
        δ * C_A * normSq0S (I := I) (g₁ t) x 5
          (metricNabla0S (I := I) (g₁ t) Sfield x) := by
    refine le_trans (two_inner0S_le_eps (I := I) (g₁ t) x 3 _ _ hδ) ?_
    have hc : normSq0S (I := I) (g₁ t) x 3 (connDiffLowAt (I := I) (g₁ t) (g₂ t) x) =
        connDiffSq (I := I) (g₁ t) (g₂ t) x := (connDiffSq_def (I := I) _ _ x).symm
    have hcle := connDiffSq_le_dens (I := I) g₁ g₂ t x
    have hAd : δ * normSq0S (I := I) (g₁ t) x 3 (Adot t x) ≤
        δ * (C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
          normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) Sfield x))) :=
      mul_le_mul_of_nonneg_left (hAdot x) hδ.le
    have hexp : δ * (C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
          normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) Sfield x))) =
        δ * C_A * forwardUniqueDensity (I := I) g₁ g₂ t x +
          δ * C_A * normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) Sfield x) := by ring
    have hcmul : δ⁻¹ * connDiffSq (I := I) (g₁ t) (g₂ t) x ≤
        δ⁻¹ * forwardUniqueDensity (I := I) g₁ g₂ t x :=
      mul_le_mul_of_nonneg_left hcle (by positivity)
    have hexp2 : (δ * C_A + δ⁻¹) * forwardUniqueDensity (I := I) g₁ g₂ t x =
        δ * C_A * forwardUniqueDensity (I := I) g₁ g₂ t x +
          δ⁻¹ * forwardUniqueDensity (I := I) g₁ g₂ t x := by ring
    rw [hc]
    linarith
  -- the moving-volume factor
  have hv : (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x *
        forwardUniqueDensity (I := I) g₁ g₂ t x ≤
      C_V * forwardUniqueDensity (I := I) g₁ g₂ t x :=
    mul_le_mul_of_nonneg_right (hvol x) hdens
  have hr := hreact x
  have hfinal : (C_R + 4 * C_Ric + 1 + δ * C_A + δ⁻¹ + C_V) *
        forwardUniqueDensity (I := I) g₁ g₂ t x =
      C_R * forwardUniqueDensity (I := I) g₁ g₂ t x +
        ((4 * C_Ric + 1) * forwardUniqueDensity (I := I) g₁ g₂ t x +
          ((δ * C_A + δ⁻¹) * forwardUniqueDensity (I := I) g₁ g₂ t x +
            C_V * forwardUniqueDensity (I := I) g₁ g₂ t x)) := by ring
  rw [rateRest]
  linarith

/-- The integrated form of `rateRest_le`. -/
theorem intRateRest_le (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sfield : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    {t δ C_A C_R C_Ric C_V : Real} (hδ : 0 < δ)
    (hreact : ∀ x,
      movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
          (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
          (connDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
      C_R * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hRic : ∀ x, normSq0S (I := I) (g₁ t) x 2
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) ≤
      C_Ric * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hAdot : ∀ x, normSq0S (I := I) (g₁ t) x 3 (Adot t x) ≤
      C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
        normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) Sfield x)))
    (hvol : ∀ x, (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V)
    (hirest : Integrable (fun x => rateRest (I := I) g₁ g₂ Adot t x)
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t)))
    (hidis : Integrable (fun x => normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) Sfield x))
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t)))
    (hidens : Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t))) :
    (∫ x, rateRest (I := I) g₁ g₂ Adot t x
        ∂(riemannianVolumeMeasure (I := I) (M := M) (g₁ t))) ≤
      (C_R + 4 * C_Ric + 1 + δ * C_A + δ⁻¹ + C_V) *
          forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t +
        δ * C_A * forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t := by
  rw [forwardUniqueEnergy, forwardUniqueDissipation, riemannianMeasureFamily_def]
  set μ := riemannianVolumeMeasure (I := I) (M := M) (g₁ t) with hμ
  have hI : Integrable (fun x =>
      (C_R + 4 * C_Ric + 1 + δ * C_A + δ⁻¹ + C_V) *
          forwardUniqueDensity (I := I) g₁ g₂ t x +
        δ * C_A * normSq0S (I := I) (g₁ t) x 5
          (metricNabla0S (I := I) (g₁ t) Sfield x)) μ :=
    (hidens.const_mul _).add (hidis.const_mul _)
  refine le_trans (integral_mono hirest hI
    (rateRest_le (I := I) g₁ g₂ Adot Sfield hδ hreact hRic hAdot hvol)) ?_
  rw [integral_add (hidens.const_mul _) (hidis.const_mul _),
    integral_const_mul, integral_const_mul]

end RestPart

section Capstone

variable [CompactSpace M]

/-- **The Kotschwar rate estimate** (Route-K brick K4).

Under the named slab-hypothesis package below the exact first variation of the
forward-uniqueness energy obeys

`forwardUniqueRate ≤ K · forwardUniqueEnergy − forwardUniqueDissipation`,

with `K = C_R + 4C_Ric + 2 + δC_A + δ⁻¹ + C_V + ε⁻¹C_U + C_rem` explicit in the slab
constants.  This is `E′ ≤ K·E − κ·D ≤ K·E` of `ShortTime/FORWARD_UNIQUE_PRO_RULING.md` §6
with `κ = 1`; the normalisation `κ = 1` is exactly what the Young smallness condition
`habs : δ·C_A + ε ≤ 1` buys.

The named hypotheses and their producers:

* `hcar` — `Sfield` realises the carrier `S₀₄` at time `t`;
* `hSdec` — the divergence-form decomposition of `Ṡ`, in the shape `rmLowComp_deriv`
  (`Evolution/ForwardUniqueRmDot.lean`) supplies;
* `hAdot` — the K1C-b bound on `|∂ₜA₀₃|²`;
* `hU`, `hrem` — the K2.4 / K2.5 flux and remainder bounds
  (`rmFluxNormSq_le`, `rmRemNormSq_le`), read against the energy density on the slab;
* `hRic` — the Ricci-difference bound, produced by `ricciDiffSq_le`;
* `hreact` — the slab bound on the three moving-metric reactions (a `|Ric₁|` bound);
* `hvol` — the slab bound on the moving-volume factor `½ tr_{g₁}(∂ₜg₁)`;
* `hirest … hidens` — the integrability side conditions, one per integrand split off. -/
theorem forwardUniqueRate_le
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : Real → (x : M) → Tensor0SSpace 4 I x)
    (Sfield : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (rem : (x : M) → Tensor0SSpace 4 I x)
    {t ε δ C_A C_R C_Ric C_V C_U C_rem : Real}
    (hε : 0 < ε) (hδ : 0 < δ) (habs : δ * C_A + ε ≤ 1)
    (hcar : ∀ x, Sfield x = rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)
    (hSdec : ∀ x, Sdot t x =
      roughLap0SField (I := I) (g₁ t) Sfield x +
        covDiv0SField (I := I) (g₁ t) U x + rem x)
    (hU : ∀ x, normSq0S (I := I) (g₁ t) x 5 (U x) ≤
      C_U * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hrem : ∀ x, normSq0S (I := I) (g₁ t) x 4 (rem x) ≤
      C_rem * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hreact : ∀ x,
      movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
          (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
          (connDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
      C_R * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hRic : ∀ x, normSq0S (I := I) (g₁ t) x 2
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) ≤
      C_Ric * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hAdot : ∀ x, normSq0S (I := I) (g₁ t) x 3 (Adot t x) ≤
      C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
        normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) Sfield x)))
    (hvol : ∀ x, (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V)
    (hirest : Integrable (fun x => rateRest (I := I) g₁ g₂ Adot t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hipair : Integrable
      (fun x => 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hilap : Integrable (fun x => inner0S (I := I) (g₁ t) x 4
        (roughLap0SField (I := I) (g₁ t) Sfield x) (Sfield x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidiv : Integrable (fun x => inner0S (I := I) (g₁ t) x 4
        (covDiv0SField (I := I) (g₁ t) U x) (Sfield x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hirem : Integrable (fun x => inner0S (I := I) (g₁ t) x 4 (rem x) (Sfield x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hinab : Integrable (fun x => inner0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) Sfield x) (U x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidis : Integrable (fun x => normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) Sfield x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidens : Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t)) :
    forwardUniqueRate (I := I) (M := M) g₁ g₂ Adot Sdot t ≤
      (C_R + 4 * C_Ric + 2 + δ * C_A + δ⁻¹ + C_V + ε⁻¹ * C_U + C_rem) *
          forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t -
        forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t := by
  rw [riemannianMeasureFamily_def] at hirest hipair hilap hidiv hirem hinab hidis hidens
  rw [rate_eq_add (I := I) g₁ g₂ Adot Sdot t
    (by rw [riemannianMeasureFamily_def]; exact hirest)
    (by rw [riemannianMeasureFamily_def]; exact hipair),
    riemannianMeasureFamily_def]
  have h1 := intRateRest_le (I := I) g₁ g₂ Adot Sfield hδ hreact hRic hAdot hvol
    hirest hidis hidens
  have h2 := sPart_le (I := I) g₁ g₂ Sdot Sfield U rem hε hcar hSdec hU hrem
    hilap hidiv hirem hinab hidis hidens
  have hD := dissipation_nonneg (I := I) (M := M) g₁ Sfield t
  have hkey : (δ * C_A + ε - 1) * forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t ≤ 0 := by
    have h := mul_le_mul_of_nonneg_right (show δ * C_A + ε - 1 ≤ 0 by linarith) hD
    simpa using h
  have hring : (C_R + 4 * C_Ric + 2 + δ * C_A + δ⁻¹ + C_V + ε⁻¹ * C_U + C_rem) *
        forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t -
      forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t =
    ((C_R + 4 * C_Ric + 1 + δ * C_A + δ⁻¹ + C_V) *
          forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t +
        δ * C_A * forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t) +
      ((ε - 2) * forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t +
        (ε⁻¹ * C_U + C_rem + 1) * forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t) -
      (δ * C_A + ε - 1) * forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t := by
    ring
  linarith [h1, h2, hkey, hring]

end Capstone

end DifferentialGeometry.PDE.RicciFlow

end
