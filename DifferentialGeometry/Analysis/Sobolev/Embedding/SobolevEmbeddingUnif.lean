import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingSharpC0JetSum
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradParallelNaturality
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

/-!
# Class-uniform fibre-Morrey constant (item-6 brick E4)

The sharp fibre-Morrey embedding
`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`
(`SobolevEmbeddingSharpC0JetSum.lean`) produces, for each metric `g`, an
existential constant `C(g)`.  Two metrics of the same comparability class
therefore receive *unrelated* constants, so that endpoint cannot floor a
class-uniform existence time.  This file supplies the constant-exposed sibling:
a closed formula `morreyUnifConst` and the theorem that every metric that is
`Λ`-comparable to a fixed background `gBase` satisfies the fibre-Morrey bound
with that single constant.

## The route

The chart atlas and the partition of unity used by the per-metric endpoint are
metric-free (`chartAtlasPOU`, subordinate to the chart sources), so the covering
data are literally the same object for every metric on `(I, M)`.  Only two
factors move with the metric:

* the **fibre/Gram factor**, controlled by comparability alone
  (`fibreNormSq_cross_le` below, constant `Λ ^ s`, one `Λ` per covariant slot);
* the **covariant-jet conversion**, i.e. the change of Levi-Civita connection
  between `g₀` and `gBase`, which is governed by the metric jets.

The first factor is discharged here outright.  The second enters as the abstract
input `hjet` with an explicit constant `Kjet`, exactly as the spectral brick S1
(`UnifBochnerGap.lean`) takes its curvature-jet envelope `Fc` abstractly:
`MetricCovDerivOrderBoundOn` lives downstream of `Analysis/`, so an `Analysis/`
leaf must consume the jet input in constant-exposed form.  See
`SobolevEmbeddingUnif.md` for the discharge ledger.

## Main statements

* `SmoothCcTensor.recast` — the metric-free transport of a smooth
  compactly-supported tensor section between metrics.
* `fibreNormSq_cross_le` — pointwise fibre-norm comparison under comparability.
* `morreyUnifConst` — the closed constant `√(Λ^s) · Cb · (n/2+2) · Kjet`.
* `fibreMorrey_unif` — the class-uniform fibre-Morrey bound.
* `baseMorreyConst` / `fibreMorrey_unif_base` — the same bound with the
  background constant realized once at the fixed metric `gBase`.

The spectral face (`H²(g₀) → C⁰`) is NOT duplicated here: `fibreMorrey_unif_base`
is exactly the `hmorrey` input of `hs2_fiber_sq_unif`
(`Analysis/Spectral/Tensor/Estimates/H2PointwiseUnif.lean`, brick E5), which
composes it with the Gårding constant `covsumHsC`.
-/

set_option autoImplicit false

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Topology Metric Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Metric-free recast of a smooth compactly-supported tensor section.**

Neither field of `SmoothCcTensor` mentions the metric: `g` is carried only to
make the type metric-indexed, so that metric-dependent norms can be attached.
Hence one and the same section is a `SmoothCcTensor g r s` for every `g`, and
cross-metric statements can be phrased on the common smooth core.

Hoist candidate: `Analysis/Integration/L2/SmoothSections/Defs.lean`. -/
def SmoothCcTensor.recast {g g' : SmoothRiemannianMetric I M} {r s : ℕ}
    (T : SmoothCcTensor g r s) : SmoothCcTensor g' r s where
  toSection := T.toSection
  hasCompactSupport := T.hasCompactSupport

@[simp] lemma SmoothCcTensor.recast_toSection
    {g g' : SmoothRiemannianMetric I M} {r s : ℕ} (T : SmoothCcTensor g r s) :
    (T.recast (g' := g')).toSection = T.toSection := rfl

end L2
end Integral
end DifferentialGeometry

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### The fibre/Gram factor -/

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
/-- **`r = 0` index-lowering is unit-evaluation.**  Replica of the (private)
upstream `lowerAllUpperIndices_zero_apply_unitModel`: lowering the model
coercion of a `(0, s)`-tensor section against no upper slots is exactly
evaluating the section on the unit `(0, 0)`-tensor. -/
private lemma lowerAllUpper_zero_unit
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : SmoothCcTensor g 0 s) (w : Fin (0 + s) → TangentSpace I x) :
    lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
        (unitZeroSec (I := I) (M := M) x) (fun j : Fin s => w (Fin.natAdd 0 j)) := by
  rw [lowerAllUpperIndices_apply, separableFormAt_zero]
  rw [show (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) from rfl]
  rw [← toModel_tensorRS_apply (I := I) (M := M) 0 s x (W.toSection x)
    (unitZeroSec (I := I) (M := M) x)]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
/-- **Fibre-inner bridge (`(0, s)`).**  The `g`-Riemannian squared fibre norm of
a smooth `(0, s)`-tensor section — the currency of the fibre-Morrey embedding —
equals the intrinsic `normSq0S` of its unit-value, the currency of the
metric-comparison layer `normSq0S_le_of_metric_equiv`.  Both are expanded in one
`g`-orthonormal frame. -/
private lemma rfns0_eq_normSq0S
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (W : SmoothCcTensor g 0 s) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x (W.toSection x) =
      normSq0S (I := I) g x s
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
          (unitZeroSec (I := I) (M := M) x)) := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 s x
    (W.toSection x)]
  rw [show tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (W.toSection x)) (TensorRSSpace.toModel (W.toSection x)) =
      covariantTensorInnerPointwise (I := I) (M := M) (0 + s) g x
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (W.toSection x)))
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (W.toSection x))) from rfl]
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (0 + s)
    basis hON _ _]
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis
    (metricInverseInBasis_of_orthonormal (I := I) g basis hON) _]
  symm
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (finCongr (Nat.zero_add s).symm) (Equiv.refl _)) _ _ ?_
  intro slots
  rw [component0S_apply]
  rw [lowerAllUpper_zero_unit (I := I) g s x W]
  rw [sq]
  congr 1 <;>
    (congr 1; funext a;
     simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq];
     congr 1;
     apply Fin.ext;
     simp)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
/-- **Cross-metric fibre-norm comparison (the Gram factor of brick E4).**

If `g₀` is `Λ`-comparable to `gBase` then the `g₀`-fibre squared norm of a
covariant `(0, s)`-tensor section is at most `Λ ^ s` times its `gBase`-fibre
squared norm — one factor of `Λ` per covariant slot.  This is the *only*
`g₀`-dependence of the fibre-Morrey chain that comes from the metric itself
rather than from its jets, and it is bounded by comparability alone. -/
theorem fibreNormSq_cross_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hequiv : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (s : ℕ) (x : M) (T : SmoothCcTensor g₀ 0 s) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (T.toSection x) ≤
      Λ ^ s * riemannianFiberNormSq (I := I) (M := M) gBase 0 s x
        ((T.recast (g' := gBase)).toSection x) := by
  rw [rfns0_eq_normSq0S (I := I) g₀ s x T,
    rfns0_eq_normSq0S (I := I) gBase s x (T.recast (g' := gBase))]
  have h := (normSq0S_le_of_metric_equiv (I := I) gBase g₀ x s hΛ (hequiv x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T.toSection x)
      (unitZeroSec (I := I) (M := M) x))).2
  rwa [zpow_natCast] at h

/-! ### The class-uniform constant -/

/-- **The class-uniform fibre-Morrey constant.**

`morreyUnifConst Λ Cb Kjet n s = √(Λ^s) · Cb · (n/2+2) · Kjet`, where

* `√(Λ^s)` is the fibre/Gram factor of `fibreNormSq_cross_le`;
* `Cb` is the fibre-Morrey constant of the fixed background metric;
* `n/2+2` is the (metric-free) number of jet orders in the supercritical window,
  entering through one Cauchy–Schwarz over that window;
* `Kjet` is the cross-metric covariant-jet transfer constant.

Every factor is an explicit function of the background data, the comparability
constant and the dimension: no choice is made at a variable metric. -/
def morreyUnifConst (Λ Cb Kjet : ℝ) (n s : ℕ) : ℝ :=
  Real.sqrt (Λ ^ s) * (Cb * ((n / 2 + 2 : ℕ) : ℝ) * Kjet)

lemma morreyUnifConst_nonneg {Λ Cb Kjet : ℝ} (hΛ : 0 ≤ Λ) (hCb : 0 ≤ Cb)
    (hKjet : 0 ≤ Kjet) (n s : ℕ) : 0 ≤ morreyUnifConst Λ Cb Kjet n s := by
  unfold morreyUnifConst
  have hp : (0 : ℝ) ≤ Λ ^ s := pow_nonneg hΛ s
  positivity

lemma morreyUnifConst_sq {Λ Cb Kjet : ℝ} (hΛ : 0 ≤ Λ) (n s : ℕ) :
    morreyUnifConst Λ Cb Kjet n s ^ 2 =
      Λ ^ s * (Cb ^ 2 * (((n / 2 + 2 : ℕ) : ℝ) ^ 2 * Kjet ^ 2)) := by
  unfold morreyUnifConst
  rw [mul_pow, Real.sq_sqrt (pow_nonneg hΛ s)]
  ring

/-- **The uniform fibre-Morrey / Sobolev-embedding bound (brick E4).**

Fix a background metric `gBase` with fibre-Morrey constant `Cb` in the
supercritical window `j < n/2 + 2`, and let `Kjet` bound the transfer of
`gBase`-covariant jets by `g₀`-covariant jets over the same window.  Then *every*
metric `g₀` that is `Λ`-comparable to `gBase` satisfies the fibre-Morrey bound
with the single closed constant `morreyUnifConst Λ Cb Kjet (finrank ℝ E) s`.

This is the constant-exposed sibling of
`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`, whose
`∃ C` conclusion is not class-uniform. -/
theorem fibreMorrey_unif
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hequiv : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (s : ℕ) {Cb Kjet : ℝ}
    (hbase : ∀ (W : SmoothCcTensor gBase 0 s) (y : M),
      riemannianFiberNormSq (I := I) (M := M) gBase 0 s y (W.toSection y) ≤
        Cb ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) gBase 0 s j W‖ ^ 2)
    (hjet : ∀ (S : SmoothCcTensor g₀ 0 s),
      ∀ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
        ‖iteratedCovGrad (I := I) gBase 0 s j (S.recast (g' := gBase))‖ ≤
          Kjet * ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 s i S‖)
    (T : SmoothCcTensor g₀ 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (T.toSection x) ≤
      morreyUnifConst Λ Cb Kjet (Module.finrank ℝ E) s ^ 2 *
        ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 s j T‖ ^ 2 := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ
  set w : ℕ := Module.finrank ℝ E / 2 + 2 with hw_def
  set Q : ℝ := ∑ i ∈ Finset.range w, ‖iteratedCovGrad (I := I) g₀ 0 s i T‖ ^ 2
    with hQ_def
  set S : ℝ := ∑ i ∈ Finset.range w, ‖iteratedCovGrad (I := I) g₀ 0 s i T‖
    with hS_def
  have hQ_nn : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => norm_nonneg _
  -- Cauchy-Schwarz over the (metric-free) supercritical window
  have hCS : S ^ 2 ≤ (w : ℝ) * Q := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range w)
      (f := fun i => ‖iteratedCovGrad (I := I) g₀ 0 s i T‖)
    simpa [hS_def, hQ_def] using h
  -- the jet transfer, squared and summed over the window
  have hjet_sq : ∀ j ∈ Finset.range w,
      ‖iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))‖ ^ 2 ≤
        Kjet ^ 2 * S ^ 2 := by
    intro j hj
    have h := hjet T j hj
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    calc ‖iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))‖ ^ 2
        ≤ (Kjet * S) ^ 2 := h2
      _ = Kjet ^ 2 * S ^ 2 := by ring
  have hjet_sum : (∑ j ∈ Finset.range w,
      ‖iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))‖ ^ 2) ≤
      (w : ℝ) ^ 2 * Kjet ^ 2 * Q := by
    have hstep := Finset.sum_le_sum hjet_sq
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hstep
    have hmul : (w : ℝ) * (Kjet ^ 2 * S ^ 2) ≤
        (w : ℝ) * (Kjet ^ 2 * ((w : ℝ) * Q)) := by
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg w)
      exact mul_le_mul_of_nonneg_left hCS (sq_nonneg Kjet)
    calc (∑ j ∈ Finset.range w,
        ‖iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))‖ ^ 2)
        ≤ (w : ℝ) * (Kjet ^ 2 * S ^ 2) := hstep
      _ ≤ (w : ℝ) * (Kjet ^ 2 * ((w : ℝ) * Q)) := hmul
      _ = (w : ℝ) ^ 2 * Kjet ^ 2 * Q := by ring
  -- background Morrey bound, then the fibre/Gram comparison
  have hCb_sq_nn : (0 : ℝ) ≤ Cb ^ 2 := sq_nonneg Cb
  have hbase' :
      riemannianFiberNormSq (I := I) (M := M) gBase 0 s x
          ((T.recast (g' := gBase)).toSection x) ≤
        Cb ^ 2 * ((w : ℝ) ^ 2 * Kjet ^ 2 * Q) :=
    le_trans (hbase (T.recast (g' := gBase)) x)
      (mul_le_mul_of_nonneg_left hjet_sum hCb_sq_nn)
  have hfib := fibreNormSq_cross_le (I := I) gBase g₀ hΛ hequiv s x T
  have hpow_nn : (0 : ℝ) ≤ Λ ^ s := pow_nonneg hΛ0 s
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (T.toSection x)
      ≤ Λ ^ s * riemannianFiberNormSq (I := I) (M := M) gBase 0 s x
          ((T.recast (g' := gBase)).toSection x) := hfib
    _ ≤ Λ ^ s * (Cb ^ 2 * ((w : ℝ) ^ 2 * Kjet ^ 2 * Q)) :=
        mul_le_mul_of_nonneg_left hbase' hpow_nn
    _ = morreyUnifConst Λ Cb Kjet (Module.finrank ℝ E) s ^ 2 * Q := by
        rw [morreyUnifConst_sq hΛ0, ← hw_def]
        ring

/-! ### Realizing the background constant at the fixed metric -/

/-- **The background fibre-Morrey constant.**  The existential constant of
`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`, chosen
once and for all at the *fixed* background metric.  It is pure `gBase`-data: no
choice is made at a variable metric of the class. -/
def baseMorreyConst (gBase : SmoothRiemannianMetric I M) (r s : ℕ) : ℝ :=
  (exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
    (I := I) (M := M) gBase r s).choose

lemma baseMorreyConst_nonneg (gBase : SmoothRiemannianMetric I M) (r s : ℕ) :
    0 ≤ baseMorreyConst (I := I) (M := M) gBase r s :=
  (exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
    (I := I) (M := M) gBase r s).choose_spec.1

lemma fibreNormSq_le_baseMorreyConst
    (gBase : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor gBase r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) gBase r s x (W.toSection x) ≤
      baseMorreyConst (I := I) (M := M) gBase r s ^ 2 *
        ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) gBase r s j W‖ ^ 2 :=
  (exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
    (I := I) (M := M) gBase r s).choose_spec.2 W x

/-- **Brick E4, background-realized form.**  Same as `fibreMorrey_unif`, with the
background constant supplied by the fixed-metric endpoint.  The resulting
constant

`morreyUnifConst Λ (baseMorreyConst gBase 0 s) Kjet (finrank ℝ E) s`

depends only on `gBase`, the comparability constant `Λ`, the jet-transfer
constant `Kjet` and the dimension — never on the individual `g₀`. -/
theorem fibreMorrey_unif_base
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hequiv : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (s : ℕ) {Kjet : ℝ}
    (hjet : ∀ (S : SmoothCcTensor g₀ 0 s),
      ∀ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
        ‖iteratedCovGrad (I := I) gBase 0 s j (S.recast (g' := gBase))‖ ≤
          Kjet * ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 s i S‖)
    (T : SmoothCcTensor g₀ 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (T.toSection x) ≤
      morreyUnifConst Λ (baseMorreyConst (I := I) (M := M) gBase 0 s) Kjet
          (Module.finrank ℝ E) s ^ 2 *
        ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 s j T‖ ^ 2 :=
  fibreMorrey_unif (I := I) gBase g₀ hΛ hequiv s
    (fibreNormSq_le_baseMorreyConst (I := I) gBase 0 s) hjet T x

end DifferentialGeometry.PDE.RicciFlow

end
