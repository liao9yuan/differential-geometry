import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.AppCcRSJetMul

/-!
# All-order Moser jet windows for the low-base operator families

`topKer_jet` (`DeTurck/LowRegC2JetTower.lean`) needs, for **every** order `i`,
an affine covariant `L2` jet window

`lowJetSq g i F ≤ K i * (1 + lowJetSq g i T)`

for each operator family occurring in the three summands of `topKernel_eq`.
The tree stocks these only at the fixed order two, as `private` helpers inside
`DeTurckRemainderLowBaseAction.lean` (`full_slot_h2_low`, `connLow_h2_low`,
`curvMono_h2`), and those fixed-order members linearize the quadratic product
step with an `H2` ball (`lowJetSq g 2 P ≤ 1`), which the ball-free route of
planner ruling No. 104 forbids.

This module supplies the order-generic members on the Moser route.  The single
organizing device is the predicate `IsMoserWin g T A S X`, which records
*both* halves that the Moser pairing consumes: a pointwise fibre bound `S` for
`X` and an affine jet envelope `A` for `X` against the state `T`.  Carrying the
pointwise bound alongside the jet bound is exactly what keeps the estimate
affine: `appRS_hn_sup` multiplies each arm's `L∞` bound by the *other* arm's
`L2` jet, so a product of two windows is again a window, with no ball and no
order gate.

Closure lemmas: `moserWin_appRS` (operator-field action), `moserWin_slot`
(`slotExtend`), `moserWin_rsperm` (covariant slot permutation),
`moserWin_sub`, `moserWin_const` (background objects).

Family windows, in dependency order:

* `moserWin_sharp` — `sharpFlatEndoCc g g₁`, the metric-inverse core.  All
  orders, from the free-`a` radius-free engine
  `sharpFlatEndoCc_lowOrder_jetL2_radiusFree`.
* `moserWin_fullSlot` — `slotInsertEndoCc g s (fullRaisedEndoField g g₁)`,
  the general-`i` replacement for `full_slot_h2_low`.
* `moserWin_connLow` — `connLowOp g g₁`, the general-`i` replacement for
  `connLow_h2_low`.
* `moserWin_dagTop` — **family `dagTopOp`**.
* `moserWin_curvMono` — the general-`i` replacement for `curvMono_h2`.
* `moserWin_daTrans` — **family `daTrans`**.
* `moserWin_ricciTop` — the assembled `ricciTop` summand of `topKernel_eq`.
* `moserWin_phiDev` — the metric-deviation summand of `topKernel_eq`.
* `moserWin_pureTr`, `moserWin_lieCovP`, `moserWin_monoMov`,
  `moserWin_lieRef2` — the moving-metric branch: the curvature-refold monomials
  of `lieRefold2` take their pair coefficient at the *path* metric, so
  `lieCovPair g gm` is not a constant and gets its own window through
  `pairTrace_eq`'s two `pureTrace` factors.
* `pathPert_rad` — the discharge of `IsPathPert` along the radial path
  `s ↦ realizedFam g T 0 s`, uniformly for `s ∈ [0, 1]`.

Every window has honest derivative offset `w = 0`: order `n` on the left costs
order `n` of `T` on the right, well inside `topKer_jet`'s `range (i + 2)`
budget.  The only smallness input is the fibre certificate
`gFibreOpBound g (ccTensorBilinSymm g P) δ` with `δ ≤ δ₀ < 1`; no Sobolev ball
and no `finrank` gate appears anywhere in this file.

Every family window quantifies the state `T` **inside** its existential, so a
single constant sequence serves all states.  This is what `topKer_jet` needs:
its `Kk` is chosen before `T`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped BigOperators Manifold ContDiff
namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open LowBaseInternal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section Window

/-- **Moser window.**  `IsMoserWin g T A S X` says that the tensor `X` carries
the two data the Moser pairing consumes against the state `T`: the pointwise
fibre bound `S` and, at every jet order `n`, the affine covariant `L2` jet
envelope `A n * (1 + lowJetSq g n T)`.

The pointwise half is what keeps products affine, so the predicate is closed
under the operator-field action with no Sobolev ball and no order gate. -/
def IsMoserWin (g : SmoothRiemannianMetric I M) {r c : ℕ}
    (T : SmoothCcTensor g 0 2) (A : ℕ → ℝ) (S : ℝ)
    (X : SmoothCcTensor g r c) : Prop :=
  0 ≤ S ∧
  (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r c x
    (X.toSection x) ≤ S ^ 2) ∧
  (∀ n : ℕ, lowJetSq (I := I) (M := M) g n X ≤
    A n * (1 + lowJetSq (I := I) (M := M) g n T))

omit [BoundarylessManifold I M] in
/-- The squared covariant jet is nonnegative. -/
theorem jetNn (g : SmoothRiemannianMetric I M) {r c m : ℕ}
    (X : SmoothCcTensor g r c) :
    0 ≤ lowJetSq (I := I) (M := M) g m X :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [BoundarylessManifold I M] in
/-- `2`-subadditivity of the squared covariant jet on a difference. -/
theorem jetSub (g : SmoothRiemannianMetric I M) {r c : ℕ} (m : ℕ)
    (X Y : SmoothCcTensor g r c) :
    lowJetSq (I := I) (M := M) g m (X - Y) ≤
      2 * (lowJetSq (I := I) (M := M) g m X +
        lowJetSq (I := I) (M := M) g m Y) := by
  unfold lowJetSq
  calc
    ∑ q ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r c q (X - Y)‖ ^ 2 ≤
        ∑ q ∈ Finset.range (m + 1),
          2 * (‖iteratedCovGrad (I := I) g r c q X‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r c q Y‖ ^ 2) := by
      refine Finset.sum_le_sum fun q _ => ?_
      rw [iteratedCovGrad_sub]
      have htri := norm_sub_le
        (iteratedCovGrad (I := I) g r c q X)
        (iteratedCovGrad (I := I) g r c q Y)
      have hstep :
          ‖iteratedCovGrad (I := I) g r c q X -
              iteratedCovGrad (I := I) g r c q Y‖ ^ 2 ≤
            (‖iteratedCovGrad (I := I) g r c q X‖ +
              ‖iteratedCovGrad (I := I) g r c q Y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
      nlinarith [hstep, sq_nonneg
        (‖iteratedCovGrad (I := I) g r c q X‖ -
          ‖iteratedCovGrad (I := I) g r c q Y‖)]
    _ = 2 * ((∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r c q X‖ ^ 2) +
        ∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r c q Y‖ ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

omit [BoundarylessManifold I M] in
/-- The negation leaves the squared covariant jet unchanged. -/
theorem jetNeg (g : SmoothRiemannianMetric I M) {r c : ℕ} (m : ℕ)
    (Y : SmoothCcTensor g r c) :
    lowJetSq (I := I) (M := M) g m (-Y) =
      lowJetSq (I := I) (M := M) g m Y := by
  unfold lowJetSq
  exact Finset.sum_congr rfl fun q _ => by
    rw [show (-Y) = (-1 : ℝ) • Y from by module,
      iteratedCovGrad_smul, norm_smul]
    norm_num

omit [BoundarylessManifold I M] in
/-- `2`-subadditivity of the squared covariant jet on a sum, for the operator-window lane. -/
theorem opJetAdd (g : SmoothRiemannianMetric I M) {r c : ℕ} (m : ℕ)
    (X Y : SmoothCcTensor g r c) :
    lowJetSq (I := I) (M := M) g m (X + Y) ≤
      2 * (lowJetSq (I := I) (M := M) g m X +
        lowJetSq (I := I) (M := M) g m Y) := by
  have h := jetSub (I := I) (M := M) g m X (-Y)
  rwa [sub_neg_eq_add, jetNeg (I := I) (M := M) g m Y] at h

omit [BoundarylessManifold I M] in
/-- Every jet envelope in a window is nonnegative. -/
theorem moserWin_nnA {g : SmoothRiemannianMetric I M} {r c : ℕ}
    {T : SmoothCcTensor g 0 2} {A : ℕ → ℝ} {S : ℝ}
    {X : SmoothCcTensor g r c} (h : IsMoserWin (I := I) (M := M) g T A S X)
    (n : ℕ) : 0 ≤ A n := by
  have hpos : (0 : ℝ) < 1 + lowJetSq (I := I) (M := M) g n T := by
    have := jetNn (I := I) (M := M) (m := n) g T
    linarith
  have hle := h.2.2 n
  have hX := jetNn (I := I) (M := M) (m := n) g X
  nlinarith [hle, hX, hpos]

omit [BoundarylessManifold I M] in
/-- Enlarging both constants preserves a window. -/
theorem moserWin_mono {g : SmoothRiemannianMetric I M} {r c : ℕ}
    {T : SmoothCcTensor g 0 2} {A A' : ℕ → ℝ} {S S' : ℝ}
    {X : SmoothCcTensor g r c} (h : IsMoserWin (I := I) (M := M) g T A S X)
    (hA : ∀ n, A n ≤ A' n) (hS : S ≤ S') :
    IsMoserWin (I := I) (M := M) g T A' S' X := by
  refine ⟨le_trans h.1 hS, fun x => ?_, fun n => ?_⟩
  · exact (h.2.1 x).trans (by nlinarith [h.1, hS])
  · refine (h.2.2 n).trans (mul_le_mul_of_nonneg_right (hA n) ?_)
    have := jetNn (I := I) (M := M) (m := n) g T
    linarith

omit [BoundarylessManifold I M] in
/-- A background object with no metric dependence is a window — for **every**
state `T`, with the same constants.  The uniformity in `T` is what lets the
downstream family windows produce a single constant sequence ahead of the
state, as `topKer_jet` requires. -/
theorem moserWin_const (g : SmoothRiemannianMetric I M) {r c : ℕ}
    (X : SmoothCcTensor g r c) :
    ∃ (A : ℕ → ℝ) (S : ℝ), ∀ T : SmoothCcTensor g 0 2,
      IsMoserWin (I := I) (M := M) g T A S X := by
  classical
  obtain ⟨K, hK0, hK⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g r c X
  refine ⟨fun n => lowJetSq (I := I) (M := M) g n X, Real.sqrt K, fun T => ?_⟩
  refine ⟨Real.sqrt_nonneg _, fun x => ?_, fun n => ?_⟩
  · rw [Real.sq_sqrt hK0]
    exact hK x
  · have hT := jetNn (I := I) (M := M) (m := n) g T
    nlinarith [jetNn (I := I) (M := M) (m := n) g X]

omit [BoundarylessManifold I M] in
/-- The squared covariant jet is monotone in the order. -/
theorem jetMono (g : SmoothRiemannianMetric I M) {r c m n : ℕ} (hmn : m ≤ n)
    (X : SmoothCcTensor g r c) :
    lowJetSq (I := I) (M := M) g m X ≤ lowJetSq (I := I) (M := M) g n X := by
  unfold lowJetSq
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.add_le_add_right hmn 1))
    (fun _ _ _ => sq_nonneg _)

omit [BoundarylessManifold I M] in
/-- A sum of windows is a window. -/
theorem moserWin_add {g : SmoothRiemannianMetric I M} {r c : ℕ}
    {T : SmoothCcTensor g 0 2} {A B : ℕ → ℝ} {S U : ℝ}
    {X Y : SmoothCcTensor g r c}
    (hX : IsMoserWin (I := I) (M := M) g T A S X)
    (hY : IsMoserWin (I := I) (M := M) g T B U Y) :
    IsMoserWin (I := I) (M := M) g T (fun n => 2 * (A n + B n))
      (Real.sqrt (2 * S ^ 2 + 2 * U ^ 2)) (X + Y) := by
  refine ⟨Real.sqrt_nonneg _, fun x => ?_, fun n => ?_⟩
  · rw [Real.sq_sqrt (by positivity)]
    rw [SmoothCcTensor.toSection_add]
    exact le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g r c x
      (X.toSection x) (Y.toSection x))
      (by nlinarith [hX.2.1 x, hY.2.1 x])
  · have hT : (0 : ℝ) ≤ 1 + lowJetSq (I := I) (M := M) g n T := by
      have := jetNn (I := I) (M := M) (m := n) g T
      linarith
    exact le_trans (opJetAdd (I := I) (M := M) g n X Y)
      (by nlinarith [hX.2.2 n, hY.2.2 n])

omit [BoundarylessManifold I M] in
/-- A difference of windows is a window. -/
theorem moserWin_sub {g : SmoothRiemannianMetric I M} {r c : ℕ}
    {T : SmoothCcTensor g 0 2} {A B : ℕ → ℝ} {S U : ℝ}
    {X Y : SmoothCcTensor g r c}
    (hX : IsMoserWin (I := I) (M := M) g T A S X)
    (hY : IsMoserWin (I := I) (M := M) g T B U Y) :
    IsMoserWin (I := I) (M := M) g T (fun n => 2 * (A n + B n))
      (Real.sqrt (2 * S ^ 2 + 2 * U ^ 2)) (X - Y) := by
  refine ⟨Real.sqrt_nonneg _, fun x => ?_, fun n => ?_⟩
  · rw [Real.sq_sqrt (by positivity)]
    rw [SmoothCcTensor.toSection_sub]
    exact le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g r c x
      (X.toSection x) (Y.toSection x))
      (by nlinarith [hX.2.1 x, hY.2.1 x])
  · have hT : (0 : ℝ) ≤ 1 + lowJetSq (I := I) (M := M) g n T := by
      have := jetNn (I := I) (M := M) (m := n) g T
      linarith
    exact le_trans (jetSub (I := I) (M := M) g n X Y)
      (by nlinarith [hX.2.2 n, hY.2.2 n])

omit [BoundarylessManifold I M] in
/-- The squared covariant jet is homogeneous of degree two in the operator-window lane. -/
theorem opJetSmul (g : SmoothRiemannianMetric I M) {r c : ℕ} (m : ℕ) (a : ℝ)
    (X : SmoothCcTensor g r c) :
    lowJetSq (I := I) (M := M) g m (a • X) =
      a ^ 2 * lowJetSq (I := I) (M := M) g m X := by
  unfold lowJetSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [iteratedCovGrad_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- A scalar multiple of a window is a window. -/
theorem moserWin_smul {g : SmoothRiemannianMetric I M} {r c : ℕ}
    {T : SmoothCcTensor g 0 2} {A : ℕ → ℝ} {S : ℝ} {X : SmoothCcTensor g r c}
    (a : ℝ) (h : IsMoserWin (I := I) (M := M) g T A S X) :
    IsMoserWin (I := I) (M := M) g T (fun n => a ^ 2 * A n) (|a| * S) (a • X) := by
  refine ⟨mul_nonneg (abs_nonneg _) h.1, fun x => ?_, fun n => ?_⟩
  · rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      riemannianFiberNormSq_smul, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_left (h.2.1 x) (sq_nonneg a)
  · rw [opJetSmul]
    have hT : (0 : ℝ) ≤ 1 + lowJetSq (I := I) (M := M) g n T := by
      have := jetNn (I := I) (M := M) (m := n) g T
      linarith
    calc
      a ^ 2 * lowJetSq (I := I) (M := M) g n X ≤
          a ^ 2 * (A n * (1 + lowJetSq (I := I) (M := M) g n T)) :=
        mul_le_mul_of_nonneg_left (h.2.2 n) (sq_nonneg a)
      _ = a ^ 2 * A n * (1 + lowJetSq (I := I) (M := M) g n T) := by ring

end Window

section Transfer

omit [BoundarylessManifold I M] in
/-- Integrating a pointwise fibre-norm domination gives the `L2` domination. -/
private theorem l2OfPt (g : SmoothRiemannianMetric I M) {a b a' b' : ℕ}
    (X : SmoothCcTensor g a b) (Y : SmoothCcTensor g a' b') {K : ℝ}
    (h : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g a b x (X.toSection x) ≤
      K * riemannianFiberNormSq (I := I) (M := M) g a' b' x (Y.toSection x)) :
    ‖X‖ ^ 2 ≤ K * ‖Y‖ ^ 2 := by
  have hF : MeasureTheory.Integrable
      (fun x => K * riemannianFiberNormSq (I := I) (M := M) g a' b' x
        (Y.toSection x)) (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g a' b' Y).const_mul K
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g a b X _ hF h
  have hint : (∫ x, riemannianFiberNormSq (I := I) (M := M) g a' b' x
      (Y.toSection x) ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ‖Y‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  rwa [MeasureTheory.integral_const_mul, hint] at hsq

omit [BoundarylessManifold I M] in
/-- A per-order pointwise fibre-norm domination transfers to every jet
window. -/
private theorem jetOfPt (g : SmoothRiemannianMetric I M) {a b a' b' : ℕ}
    (X : SmoothCcTensor g a b) (Y : SmoothCcTensor g a' b') {K : ℝ}
    (h : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g a (b + i) x
        ((iteratedCovGrad (I := I) g a b i X).toSection x) ≤
      K * riemannianFiberNormSq (I := I) (M := M) g a' (b' + i) x
        ((iteratedCovGrad (I := I) g a' b' i Y).toSection x))
    (n : ℕ) :
    lowJetSq (I := I) (M := M) g n X ≤
      K * lowJetSq (I := I) (M := M) g n Y := by
  unfold lowJetSq
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    l2OfPt (I := I) (M := M) g (iteratedCovGrad (I := I) g a b i X)
      (iteratedCovGrad (I := I) g a' b' i Y) (h i)

/-- **The Moser product step.**  A window times a window is a window: each
arm's pointwise bound multiplies the other arm's jet envelope, so the result is
still affine in the state's jets.  No order gate and no Sobolev ball. -/
theorem moserWin_appRS (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (T : SmoothCcTensor g 0 2) (A B : ℕ → ℝ) (S U : ℝ)
        (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        IsMoserWin (I := I) (M := M) g T A S Φ →
        IsMoserWin (I := I) (M := M) g T B U W →
        IsMoserWin (I := I) (M := M) g T
          (fun n => C n * (U ^ 2 * A n + S ^ 2 * B n)) (S * U)
          (appCcRS (I := I) (M := M) g p r c Φ W) := by
  obtain ⟨C, hC0, hC⟩ := appRS_hn_sup (I := I) (M := M) g p r c
  refine ⟨C, hC0, ?_⟩
  intro T A B S U Φ W hΦ hW
  refine ⟨mul_nonneg hΦ.1 hW.1, fun x => ?_, fun n => ?_⟩
  · rw [appCcRS_toSection (I := I) (M := M) g p r c Φ W x]
    have h := riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g p r c x
      (show TensorRSSpace r c I x from Φ.toSection x)
      (show TensorRSSpace p r I x from W.toSection x)
    have hΦx := hΦ.2.1 x
    have hWx := hW.2.1 x
    have hΦ0 := riemannianFiberNormSq_nonneg (I := I) (M := M) g r c x
      (Φ.toSection x)
    have hW0 := riemannianFiberNormSq_nonneg (I := I) (M := M) g p r x
      (W.toSection x)
    have hmul : riemannianFiberNormSq (I := I) (M := M) g r c x (Φ.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g p r x (W.toSection x) ≤
        (S * U) ^ 2 := by nlinarith [sq_nonneg S, sq_nonneg U]
    simpa using h.trans hmul
  · have hjet := hC n Φ W S U hΦ.1 hW.1 hΦ.2.1 hW.2.1
    have hjet' : lowJetSq (I := I) (M := M) g n
        (appCcRS (I := I) (M := M) g p r c Φ W) ≤
        C n * (U ^ 2 * lowJetSq (I := I) (M := M) g n Φ +
          S ^ 2 * lowJetSq (I := I) (M := M) g n W) := by
      simpa only [lowJetSq] using hjet
    have hT : (0 : ℝ) ≤ 1 + lowJetSq (I := I) (M := M) g n T := by
      have := jetNn (I := I) (M := M) (m := n) g T
      linarith
    refine hjet'.trans ?_
    have h1 := hΦ.2.2 n
    have h2 := hW.2.2 n
    have hstep : U ^ 2 * lowJetSq (I := I) (M := M) g n Φ +
        S ^ 2 * lowJetSq (I := I) (M := M) g n W ≤
        (U ^ 2 * A n + S ^ 2 * B n) *
          (1 + lowJetSq (I := I) (M := M) g n T) := by
      calc
        U ^ 2 * lowJetSq (I := I) (M := M) g n Φ +
            S ^ 2 * lowJetSq (I := I) (M := M) g n W ≤
            U ^ 2 * (A n * (1 + lowJetSq (I := I) (M := M) g n T)) +
              S ^ 2 * (B n * (1 + lowJetSq (I := I) (M := M) g n T)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (sq_nonneg U))
            (mul_le_mul_of_nonneg_left h2 (sq_nonneg S))
        _ = (U ^ 2 * A n + S ^ 2 * B n) *
            (1 + lowJetSq (I := I) (M := M) g n T) := by ring
    calc
      C n * (U ^ 2 * lowJetSq (I := I) (M := M) g n Φ +
          S ^ 2 * lowJetSq (I := I) (M := M) g n W) ≤
          C n * ((U ^ 2 * A n + S ^ 2 * B n) *
            (1 + lowJetSq (I := I) (M := M) g n T)) :=
        mul_le_mul_of_nonneg_left hstep (hC0 n)
      _ = C n * (U ^ 2 * A n + S ^ 2 * B n) *
          (1 + lowJetSq (I := I) (M := M) g n T) := by ring

/-- Slot extension of a window is a window, at cost one dimension factor. -/
theorem moserWin_slot {g : SmoothRiemannianMetric I M} {r c : ℕ}
    {T : SmoothCcTensor g 0 2} {A : ℕ → ℝ} {S : ℝ} {Φ : SmoothCcTensor g r c}
    (h : IsMoserWin (I := I) (M := M) g T A S Φ) :
    IsMoserWin (I := I) (M := M) g T
      (fun n => (Module.finrank ℝ E : ℝ) * A n)
      (Real.sqrt (Module.finrank ℝ E : ℝ) * S)
      (slotExtend (I := I) (M := M) g r c Φ) := by
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) h.1, fun x => ?_, fun n => ?_⟩
  · have hpt := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g r c Φ 0 x
    simp only [iteratedCovGrad_zero, Nat.add_zero] at hpt
    have hsq : (Real.sqrt (Module.finrank ℝ E : ℝ) * S) ^ 2 =
        (Module.finrank ℝ E : ℝ) * S ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hfr]
    rw [hsq]
    exact hpt.trans (mul_le_mul_of_nonneg_left (h.2.1 x) hfr)
  · have hstep := jetOfPt (I := I) (M := M) g
      (slotExtend (I := I) (M := M) g r c Φ) Φ
      (fun i x => rfns_iteratedCovGrad_slotExtend_le
        (I := I) (M := M) g r c Φ i x) n
    have hT : (0 : ℝ) ≤ 1 + lowJetSq (I := I) (M := M) g n T := by
      have := jetNn (I := I) (M := M) (m := n) g T
      linarith
    nlinarith [hstep, h.2.2 n, hfr, hT]

omit [BoundarylessManifold I M] in
/-- **Window transfer along a per-order domination.**  If `X` is dominated
pointwise at order zero and in every `L2` jet by `Y`, then `Y`'s window
transfers to `X`. -/
theorem moserWin_dom {g : SmoothRiemannianMetric I M} {a b a' b' : ℕ}
    {T : SmoothCcTensor g 0 2} {A : ℕ → ℝ} {S Cs : ℝ} {Cj : ℕ → ℝ}
    {X : SmoothCcTensor g a b} {Y : SmoothCcTensor g a' b'}
    (hCs : 0 ≤ Cs) (hCj : ∀ i, 0 ≤ Cj i)
    (hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g a b x
      (X.toSection x) ≤
      Cs * riemannianFiberNormSq (I := I) (M := M) g a' b' x (Y.toSection x))
    (hjet : ∀ i : ℕ, ‖iteratedCovGrad (I := I) g a b i X‖ ^ 2 ≤
      Cj i * lowJetSq (I := I) (M := M) g i Y)
    (hY : IsMoserWin (I := I) (M := M) g T A S Y) :
    IsMoserWin (I := I) (M := M) g T
      (fun n => (∑ i ∈ Finset.range (n + 1), Cj i) * A n)
      (Real.sqrt Cs * S) X := by
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) hY.1, fun x => ?_, fun n => ?_⟩
  · rw [mul_pow, Real.sq_sqrt hCs]
    exact (hsup x).trans (mul_le_mul_of_nonneg_left (hY.2.1 x) hCs)
  · have hT : (0 : ℝ) ≤ 1 + lowJetSq (I := I) (M := M) g n T := by
      have := jetNn (I := I) (M := M) (m := n) g T
      linarith
    have hstep : lowJetSq (I := I) (M := M) g n X ≤
        (∑ i ∈ Finset.range (n + 1), Cj i) *
          lowJetSq (I := I) (M := M) g n Y := by
      unfold lowJetSq
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      refine (hjet i).trans ?_
      exact mul_le_mul_of_nonneg_left
        (jetMono (I := I) (M := M) g
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) Y) (hCj i)
    refine hstep.trans ?_
    have hsum : (0 : ℝ) ≤ ∑ i ∈ Finset.range (n + 1), Cj i :=
      Finset.sum_nonneg fun i _ => hCj i
    calc
      (∑ i ∈ Finset.range (n + 1), Cj i) *
          lowJetSq (I := I) (M := M) g n Y ≤
          (∑ i ∈ Finset.range (n + 1), Cj i) *
            (A n * (1 + lowJetSq (I := I) (M := M) g n T)) :=
        mul_le_mul_of_nonneg_left (hY.2.2 n) hsum
      _ = (∑ i ∈ Finset.range (n + 1), Cj i) * A n *
          (1 + lowJetSq (I := I) (M := M) g n T) := by ring

/-- Reindexing the contravariant slots preserves a window unchanged. -/
theorem moserWin_reindex {g : SmoothRiemannianMetric I M} {r c : ℕ}
    {T : SmoothCcTensor g 0 2} {A : ℕ → ℝ} {S : ℝ} {R : SmoothCcTensor g r c}
    (ρ : Equiv.Perm (Fin r)) (h : IsMoserWin (I := I) (M := M) g T A S R) :
    IsMoserWin (I := I) (M := M) g T A S
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen
        (I := I) (M := M) g r c R ρ) := by
  have heq := rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g r c R ρ
  refine ⟨h.1, fun x => ?_, fun n => ?_⟩
  · have hx := heq 0 x
    simp only [iteratedCovGrad_zero, Nat.add_zero] at hx
    rw [hx]
    exact h.2.1 x
  · have hstep := jetOfPt (I := I) (M := M) g
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen
        (I := I) (M := M) g r c R ρ) R
      (fun i x => le_of_eq (by rw [heq i x, one_mul])) n
    rw [one_mul] at hstep
    exact hstep.trans (h.2.2 n)

/-- Permuting the covariant slots preserves a window unchanged. -/
theorem moserWin_rsperm {g : SmoothRiemannianMetric I M} {r c : ℕ}
    {T : SmoothCcTensor g 0 2} {A : ℕ → ℝ} {S : ℝ} {Φ : SmoothCcTensor g r c}
    (σ : Equiv.Perm (Fin c)) (h : IsMoserWin (I := I) (M := M) g T A S Φ) :
    IsMoserWin (I := I) (M := M) g T A S
      (rsDomDomCongrSection (I := I) (M := M) g r c σ Φ) := by
  have heq : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g r (c + i) x
        ((iteratedCovGrad (I := I) g r c i
          (rsDomDomCongrSection (I := I) (M := M) g r c σ Φ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (c + i) x
        ((iteratedCovGrad (I := I) g r c i Φ).toSection x) := by
    intro i x
    exact rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr
      (I := I) (M := M) g r c σ Φ
      (rsDomDomCongrSection (I := I) (M := M) g r c σ Φ)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x
  refine ⟨h.1, fun x => ?_, fun n => ?_⟩
  · have := heq 0 x
    simp only [iteratedCovGrad_zero, Nat.add_zero] at this
    rw [this]
    exact h.2.1 x
  · have hstep := jetOfPt (I := I) (M := M) g
      (rsDomDomCongrSection (I := I) (M := M) g r c σ Φ) Φ
      (fun i x => le_of_eq (by rw [heq i x, one_mul])) n
    rw [one_mul] at hstep
    exact hstep.trans (h.2.2 n)

end Transfer

section Core

/-- **Path-perturbation data over the state `T`, at fibre size `δ₀`.**

The moving metric `g₁` is `g` plus the symmetric perturbation `P`, whose fibre
operator norm is at most `δ₀`, together with the matching pointwise fibre
certificate for `P` and the jet domination of `P` by `T`.

For the radial path `g₁ = realizedFam g T 0 hδ hδZ s` with
`P = convexPerturbation g T 0 s` this holds for every `s ∈ [0, 1]` with the
*same* `δ₀`, which is where the uniformity in the path parameter comes from:
none of the constants produced below depends on `s`. -/
def IsPathPert (g g₁ : SmoothRiemannianMetric I M)
    (P T : SmoothCcTensor g 0 2) (δ₀ : ℝ) : Prop :=
  (∃ δ : ℝ, 0 ≤ δ ∧ δ ≤ δ₀ ∧
    gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g P) δ) ∧
  (∀ (x : M) (u v : TangentSpace I x),
    g₁.inner x u v = g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) ∧
  (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x (P.toSection x) ≤
    ((Module.finrank ℝ E : ℝ) * δ₀) ^ 2) ∧
  (∀ n : ℕ, lowJetSq (I := I) (M := M) g n P ≤
    lowJetSq (I := I) (M := M) g n T)

omit [BoundarylessManifold I M] in
/-- The state is its own window, with its own fibre certificate as pointwise
bound.  This is the arm that the Moser pairing pays the `L∞` smallness on, and
it is the only place where `δ ≤ 1/3` enters. -/
theorem moserWin_self {g : SmoothRiemannianMetric I M}
    {T : SmoothCcTensor g 0 2} {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀)
    (hTsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (T.toSection x) ≤ ((Module.finrank ℝ E : ℝ) * δ₀) ^ 2) :
    IsMoserWin (I := I) (M := M) g T (fun _ => 1)
      ((Module.finrank ℝ E : ℝ) * δ₀) T := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) hδ₀0, hTsup, fun n => ?_⟩
  rw [one_mul]
  have := jetNn (I := I) (M := M) (m := n) g T
  linarith

/-- The slot symmetrization is dominated, pointwise and at every jet order, by
the state itself: `symmS` is a half-sum of `T` and a covariant slot
permutation of `T`, and the permutation is a fibre isometry. -/
private theorem rfnsSymmS (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
        ((iteratedCovGrad (I := I) g 0 2 j
          (symmS (I := I) (M := M) g T)).toSection x) ≤
      1 * riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
        ((iteratedCovGrad (I := I) g 0 2 j T).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g 0 2 j
        (symmS (I := I) (M := M) g T)).toSection x =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g 0 2 j T).toSection x +
        (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g 0 2 j
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T)).toSection x := by
    rw [iteratedCovGrad_symmS_eq (I := I) (M := M) g T j,
      SmoothCcTensor.toSection_add]
    rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j T).toSection +
        ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T)).toSection) x =
        ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j T).toSection x +
          ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j
            (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T)).toSection x from rfl]
    rw [SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_smul]
    rfl
  rw [hsec, one_mul]
  refine le_trans (riemannianFiberNormSq_add_le
    (I := I) (M := M) g 0 (2 + j) x _ _) ?_
  rw [riemannianFiberNormSq_smul (I := I) (M := M) g 0 (2 + j) x,
    riemannianFiberNormSq_smul (I := I) (M := M) g 0 (2 + j) x,
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1) T j x]
  nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (2 + j) x
    ((iteratedCovGrad (I := I) g 0 2 j T).toSection x)]

/-- **Window for the slot symmetrization of the state.**

`symmS g T` is the argument the curvature-refold monomials of `lieRefold2`
actually see.  Its window is the state's own, with the same constants: the
symmetrization is a fibre-norm contraction at every jet order. -/
theorem moserWin_symmS (g : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀0 : 0 ≤ δ₀) :
    ∃ (A : ℕ → ℝ) (S : ℝ),
      ∀ T : SmoothCcTensor g 0 2,
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (T.toSection x) ≤ ((Module.finrank ℝ E : ℝ) * δ₀) ^ 2) →
        IsMoserWin (I := I) (M := M) g T A S
          (symmS (I := I) (M := M) g T) := by
  refine ⟨fun _ => 1, (Module.finrank ℝ E : ℝ) * δ₀, ?_⟩
  intro T hTsup
  refine ⟨mul_nonneg (Nat.cast_nonneg _) hδ₀0, fun x => ?_, fun n => ?_⟩
  · refine le_trans ?_ (hTsup x)
    simpa only [iteratedCovGrad_zero, Nat.add_zero, one_mul] using
      rfnsSymmS (I := I) (M := M) g T 0 x
  · rw [one_mul]
    have hj := jetOfPt (I := I) (M := M) g (symmS (I := I) (M := M) g T) T
      (fun i x => rfnsSymmS (I := I) (M := M) g T i x) n
    rw [one_mul] at hj
    have := jetNn (I := I) (M := M) (m := n) g T
    linarith

/-- Slot-zero insertion of the full raised endomorphism is the sharp-flat
endomorphism field. -/
private theorem sharpSlot0 (g g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g g₁ =
      slotInsertEndoCc (I := I) (M := M) g 0
        (fullRaisedEndoField (I := I) (M := M) g g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g 0
          (fullRaisedEndoField (I := I) (M := M) g g₁)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (gInvRaisedEndo (I := I) g g₁ x) om from rfl]
  rw [cotangentToDual_slotInsertEndoFib' (I := I) (M := M) x
    (gInvRaisedEndo (I := I) g g₁ x) om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g g₁).toSection x) om =
      g0FlatCLM (I := I) g x (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [cotangentToDual_g0FlatCLM]
  rw [show cotangentToDual (I := I) om
      (gInvRaisedEndo (I := I) g g₁ x w) =
      g₁.inner x (inverseMetricSharpFib (I := I) g₁ x om)
        (gInvRaisedEndo (I := I) g g₁ x w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) g₁ x om
      (gInvRaisedEndo (I := I) g g₁ x w)).symm]
  rw [show gInvRaisedEndo (I := I) g g₁ x w =
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g x w) from by
    rw [gInvRaisedEndo_apply]]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om)
    (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g x w))]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x
    (g0FlatCLM (I := I) g x w) (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  rw [g.symm x w (inverseMetricSharpFib (I := I) g₁ x om)]

/-- **All-order window for the metric-inverse core.**

The general-order replacement for the fixed-order-two private `sharp_h2_low`.
Both are read off the same radius-free engine
`sharpFlatEndoCc_lowOrder_jetL2_radiusFree`; the point is that its order cap
`a` is a free parameter, so raising `a` with the requested order gives every
order at no cost.  Derivative offset `w = 0`. -/
theorem moserWin_sharp (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ (A : ℕ → ℝ) (S : ℝ),
      ∀ (T : SmoothCcTensor g 0 2) (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2),
        IsPathPert (I := I) (M := M) g g₁ P T δ₀ →
        IsMoserWin (I := I) (M := M) g T A S
          (sharpFlatEndoCc (I := I) g g₁) := by
  classical
  have hkey : ∀ n : ℕ, ∃ Λ K : ℝ, 0 ≤ Λ ∧ 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2) (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2),
        IsPathPert (I := I) (M := M) g g₁ P T δ₀ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 1 1 x
            ((sharpFlatEndoCc (I := I) g g₁).toSection x) ≤ Λ ^ 2) ∧
          lowJetSq (I := I) (M := M) g n (sharpFlatEndoCc (I := I) g g₁) ≤
            K * (1 + lowJetSq (I := I) (M := M) g n P) := by
    intro n
    obtain ⟨Λ, Flow, hΛ, hFlow0, hFlow⟩ :=
      sharpFlatEndoCc_lowOrder_jetL2_radiusFree (I := I) (M := M) g
        (2 * Module.finrank ℝ E + 10 + n) (by omega) hδ₀
        (Λ₀ := (Module.finrank ℝ E : ℝ) * δ₀)
        (mul_nonneg (Nat.cast_nonneg _) hδ₀0)
    refine ⟨Λ, Flow n, hΛ, hFlow0 n, ?_⟩
    rintro T g₁ P ⟨⟨δ, hδ0, hδ_le, hδ⟩, htie, hPsup, hPT⟩
    obtain ⟨h1, h2⟩ := hFlow g₁ P htie hδ_le hδ0 hδ hPsup
    exact ⟨h1, by simpa only [lowJetSq] using h2 n (by omega)⟩
  choose Λf Kf hΛf hKf hmain using hkey
  refine ⟨Kf, Λf 0, ?_⟩
  intro T g₁ P hpert
  refine ⟨hΛf 0, fun x => (hmain 0 T g₁ P hpert).1 x, fun n => ?_⟩
  refine (hmain n T g₁ P hpert).2.trans ?_
  exact mul_le_mul_of_nonneg_left (by linarith [hpert.2.2.2 n]) (hKf n)

/-- Raising the insertion slot preserves a window, at cost `s` dimension
factors. -/
theorem moserWin_endoIns {g : SmoothRiemannianMetric I M}
    {T : SmoothCcTensor g 0 2} {A : ℕ → ℝ} {S : ℝ} (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (h : IsMoserWin (I := I) (M := M) g T A S
      (slotInsertEndoCc (I := I) (M := M) g 0 Λ)) :
    IsMoserWin (I := I) (M := M) g T
      (fun n => (Module.finrank ℝ E : ℝ) ^ s * A n)
      (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ s) * S)
      (slotInsertEndoCc (I := I) (M := M) g s Λ) := by
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ s := by positivity
  have hpt := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g s Λ
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) h.1, fun x => ?_, fun n => ?_⟩
  · have hx := hpt 0 x
    simp only [iteratedCovGrad_zero, Nat.add_zero] at hx
    have hsq : (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ s) * S) ^ 2 =
        (Module.finrank ℝ E : ℝ) ^ s * S ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hfr]
    rw [hsq]
    exact hx.trans (mul_le_mul_of_nonneg_left (h.2.1 x) hfr)
  · have hstep := jetOfPt (I := I) (M := M) g
      (slotInsertEndoCc (I := I) (M := M) g s Λ)
      (slotInsertEndoCc (I := I) (M := M) g 0 Λ)
      (fun i x => hpt i x) n
    calc
      lowJetSq (I := I) (M := M) g n
          (slotInsertEndoCc (I := I) (M := M) g s Λ) ≤
          (Module.finrank ℝ E : ℝ) ^ s *
            lowJetSq (I := I) (M := M) g n
              (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := hstep
      _ ≤ (Module.finrank ℝ E : ℝ) ^ s *
          (A n * (1 + lowJetSq (I := I) (M := M) g n T)) :=
        mul_le_mul_of_nonneg_left (h.2.2 n) hfr
      _ = (Module.finrank ℝ E : ℝ) ^ s * A n *
          (1 + lowJetSq (I := I) (M := M) g n T) := by ring

/-- **All-order window for the inserted full raised endomorphism.**

The general-order replacement for the fixed-order-two private
`full_slot_h2_low`.  Derivative offset `w = 0`. -/
theorem moserWin_fullSlot (g : SmoothRiemannianMetric I M)
    (s : ℕ) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ (A : ℕ → ℝ) (S : ℝ),
      ∀ (T : SmoothCcTensor g 0 2) (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2),
        IsPathPert (I := I) (M := M) g g₁ P T δ₀ →
        IsMoserWin (I := I) (M := M) g T A S
          (slotInsertEndoCc (I := I) (M := M) g s
            (fullRaisedEndoField (I := I) (M := M) g g₁)) := by
  obtain ⟨A, S, hwin⟩ :=
    moserWin_sharp (I := I) (M := M) g hδ₀0 hδ₀
  refine ⟨fun n => (Module.finrank ℝ E : ℝ) ^ s * A n,
    Real.sqrt ((Module.finrank ℝ E : ℝ) ^ s) * S, ?_⟩
  intro T g₁ P hpert
  refine moserWin_endoIns (I := I) (M := M) s _ ?_
  rw [← sharpSlot0 (I := I) (M := M) g g₁]
  exact hwin T g₁ P hpert

/-- The full raised endomorphism at the background metric is the identity. -/
private lemma raisedSelf (g : SmoothRiemannianMetric I M) (x : M) :
    gInvRaisedEndo (I := I) g g x =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM,
    ContinuousLinearMap.id_apply]

/-- The full raised endomorphism splits off its background identity part. -/
private lemma raisedDecomp (g g₁ : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g g₁ =
      gInvDiffRaisedEndoField (I := I) g g₁ +
        fullRaisedEndoField (I := I) (M := M) g g := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g g₁ +
        fullRaisedEndoField (I := I) (M := M) g g) x) =
      gInvDiffRaisedEndoField (I := I) g g₁ x +
        fullRaisedEndoField (I := I) (M := M) g g x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g g₁ x) =
      gInvDiffRaisedEndo (I := I) g g₁ x from rfl]
  rw [fullRaisedEndoField_apply, raisedSelf, ContinuousLinearMap.id_apply]
  rw [gInvRaisedEndo_eq_diff_add_id]

/-- Slot insertion is additive in the endomorphism field. -/
private lemma insAdd (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g s (A + B) =
      slotInsertEndoCc (I := I) (M := M) g s A +
        slotInsertEndoCc (I := I) (M := M) g s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotInsertEndoCc (I := I) (M := M) g s A +
        slotInsertEndoCc (I := I) (M := M) g s B).toSection x) =
      (slotInsertEndoCc (I := I) (M := M) g s A).toSection x +
        (slotInsertEndoCc (I := I) (M := M) g s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

/-- **All-order window for the inserted inverse-metric-difference
endomorphism, at an arbitrary slot.**

This is the common core of the cometric inverse-difference multiplier
`gInvDiffSlotCoeff` (slot `1`) and of the moving double trace `pureTrace`
(slot `s + 1`).  Derivative offset `w = 0`. -/
theorem moserWin_gInvSlot (g : SmoothRiemannianMetric I M)
    (k : ℕ) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ (A : ℕ → ℝ) (S : ℝ),
      ∀ (T : SmoothCcTensor g 0 2) (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2),
        IsPathPert (I := I) (M := M) g g₁ P T δ₀ →
        IsMoserWin (I := I) (M := M) g T A S
          (slotInsertEndoCc (I := I) (M := M) g k
            (gInvDiffRaisedEndoField (I := I) g g₁)) := by
  obtain ⟨A, S, hwin⟩ := moserWin_sharp (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨AI, SI, hI⟩ := moserWin_const (I := I) (M := M) g
    (slotInsertEndoCc (I := I) (M := M) g 0
      (fullRaisedEndoField (I := I) (M := M) g g))
  refine ⟨fun n => (Module.finrank ℝ E : ℝ) ^ k * (2 * (A n + AI n)),
    Real.sqrt ((Module.finrank ℝ E : ℝ) ^ k) *
      Real.sqrt (2 * S ^ 2 + 2 * SI ^ 2), ?_⟩
  intro T g₁ P hpert
  have hdiff : slotInsertEndoCc (I := I) (M := M) g 0
      (gInvDiffRaisedEndoField (I := I) g g₁) =
      sharpFlatEndoCc (I := I) g g₁ -
        slotInsertEndoCc (I := I) (M := M) g 0
          (fullRaisedEndoField (I := I) (M := M) g g) := by
    rw [sharpSlot0 (I := I) (M := M) g g₁,
      raisedDecomp (I := I) (M := M) g g₁,
      insAdd (I := I) (M := M) g 0]
    abel
  refine moserWin_endoIns (I := I) (M := M) k _ ?_
  rw [hdiff]
  exact moserWin_sub (I := I) (M := M) (hwin T g₁ P hpert) (hI T)

/-- **All-order window for the cometric inverse-difference multiplier.**

`gInvDiffSlotCoeff g gm` is the factor through which the metric deviation
`deTurckPhiMetTotal g g_bg gm - deTurckPhiMetTotal g g_bg g` is controlled, by
the per-order producers
`traceHessianCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2` and
`ricciArmPrincipalCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2`.
Only the fixed-order-two, ball-based `inv_coeff_h2` was stocked; this is the
ball-free general-order member.  Derivative offset `w = 0`. -/
theorem moserWin_gInvDiff (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ (A : ℕ → ℝ) (S : ℝ),
      ∀ (T : SmoothCcTensor g 0 2) (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2),
        IsPathPert (I := I) (M := M) g g₁ P T δ₀ →
        IsMoserWin (I := I) (M := M) g T A S
          (gInvDiffSlotCoeff (I := I) g g₁) := by
  obtain ⟨A, S, hwin⟩ := moserWin_gInvSlot (I := I) (M := M) g 1 hδ₀0 hδ₀
  refine ⟨A, S, fun T g₁ P hpert => ?_⟩
  rw [gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) (M := M) g g₁]
  exact hwin T g₁ P hpert

end Core

section Families

/-- **All-order window for the lowered connection-difference coefficient.**

The general-order replacement for the fixed-order-two private
`connLow_h2_low`.  The two background factors (the low permutation coefficient
and the Koszul coefficient) enter only as constants; the whole metric
dependence is the inserted full raised endomorphism.  Derivative offset
`w = 0`. -/
theorem moserWin_connLow (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ (A : ℕ → ℝ) (S : ℝ),
      ∀ (T : SmoothCcTensor g 0 2) (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2),
        IsPathPert (I := I) (M := M) g g₁ P T δ₀ →
        IsMoserWin (I := I) (M := M) g T A S
          (connLowOp (I := I) (M := M) g g₁) := by
  obtain ⟨Q, Kop, hcl⟩ : ∃ Q Kop : SmoothCcTensor g 3 3,
      ∀ g₁ : SmoothRiemannianMetric I M,
        connLowOp (I := I) (M := M) g g₁ =
          appCcRS (I := I) (M := M) g 3 3 3 Q
            (appCcRS (I := I) (M := M) g 3 3 3
              (slotInsertEndoCc (I := I) (M := M) g 2
                (fullRaisedEndoField (I := I) (M := M) g g₁)) Kop) :=
    ⟨_, _, fun _ => rfl⟩
  obtain ⟨AQ, SQ, hQ⟩ := moserWin_const (I := I) (M := M) g Q
  obtain ⟨AK, SK, hK⟩ := moserWin_const (I := I) (M := M) g Kop
  obtain ⟨AF, SF, hF⟩ :=
    moserWin_fullSlot (I := I) (M := M) g 2 hδ₀0 hδ₀
  obtain ⟨C, hC0, happ⟩ := moserWin_appRS (I := I) (M := M) g 3 3 3
  refine ⟨fun n => C n * ((SF * SK) ^ 2 * AQ n +
      SQ ^ 2 * (C n * (SK ^ 2 * AF n + SF ^ 2 * AK n))),
    SQ * (SF * SK), ?_⟩
  intro T g₁ P hpert
  rw [hcl g₁]
  exact happ T AQ (fun n => C n * (SK ^ 2 * AF n + SF ^ 2 * AK n))
    SQ (SF * SK) _ _ (hQ T)
    (happ T AF AK SF SK _ _ (hF T g₁ P hpert) (hK T))

/-- **All-order window for the family `dagTopOp`.**

`dagTopOp g gm` is the top derivative coefficient of the Ricci connection arm
in the `ricciTop` summand of `topKernel_eq`.  This is the general-order
statement that the fixed-order-two `ricciTop_h2` proof only had as an inline
`have`.  Derivative offset `w = 0`, uniform in the path parameter. -/
theorem moserWin_dagTop (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ (A : ℕ → ℝ) (S : ℝ),
      ∀ (T : SmoothCcTensor g 0 2) (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2),
        IsPathPert (I := I) (M := M) g g₁ P T δ₀ →
        IsMoserWin (I := I) (M := M) g T A S
          (dagTopOp (I := I) (M := M) g g₁) := by
  obtain ⟨AC, SC, hCw⟩ := moserWin_connLow (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨AP, SP, hP⟩ := moserWin_const (I := I) (M := M) g
    (permCoeff (I := I) (M := M) g daPermA)
  obtain ⟨C, hC0, happ⟩ := moserWin_appRS (I := I) (M := M) g 4 4 4
  refine ⟨fun n => C n *
      ((Real.sqrt (Module.finrank ℝ E : ℝ) * SC) ^ 2 * AP n +
        SP ^ 2 * ((Module.finrank ℝ E : ℝ) * AC n)),
    SP * (Real.sqrt (Module.finrank ℝ E : ℝ) * SC), ?_⟩
  intro T g₁ P hpert
  rw [dagTopOp]
  exact happ T AP (fun n => (Module.finrank ℝ E : ℝ) * AC n) SP
    (Real.sqrt (Module.finrank ℝ E : ℝ) * SC) _ _ (hP T)
    (moserWin_slot (I := I) (M := M) (hCw T g₁ P hpert))

/-- **All-order window for the moving-inverse weight.**

`daWeight g gm T` is the state `T` acted on by the inserted full raised
endomorphism of the moving metric.  The Moser pairing is what keeps this
affine: the fixed-order-two route needed `lowJetSq g 2 P ≤ 1` here and got a
quadratic bound, whereas the `L∞` slot of `appRS_hn_sup` turns the same product
into an affine window.  Derivative offset `w = 0`. -/
theorem moserWin_daWeight (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ (A : ℕ → ℝ) (S : ℝ),
      ∀ (T : SmoothCcTensor g 0 2),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (T.toSection x) ≤ ((Module.finrank ℝ E : ℝ) * δ₀) ^ 2) →
        ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2),
        IsPathPert (I := I) (M := M) g g₁ P T δ₀ →
        IsMoserWin (I := I) (M := M) g T A S
          (daWeight (I := I) (M := M) g g₁ T) := by
  obtain ⟨AF, SF, hF⟩ :=
    moserWin_fullSlot (I := I) (M := M) g 1 hδ₀0 hδ₀
  obtain ⟨C, hC0, happ⟩ := moserWin_appRS (I := I) (M := M) g 0 2 2
  refine ⟨fun n => C n * (((Module.finrank ℝ E : ℝ) * δ₀) ^ 2 * AF n +
      SF ^ 2 * 1), SF * ((Module.finrank ℝ E : ℝ) * δ₀), ?_⟩
  intro T hTsup g₁ P hpert
  have hself := moserWin_self (I := I) (M := M) hδ₀0 hTsup
  rw [daWeight, ← appCcRS_zero_eq_appCc]
  exact happ T AF (fun _ => 1) SF ((Module.finrank ℝ E : ℝ) * δ₀) _ _
    (hF T g₁ P hpert) hself

/-- **All-order window for one curvature-refold monomial.**

The general-order replacement for the fixed-order-two private `curvMono_h2`.
The transparent two-trace product form `curvMono_eq` reduces it to the
background pair coefficient times a four-fold slot extension of the weight, and
both factors are already windows. -/
theorem moserWin_curvMono (g : SmoothRiemannianMetric I M)
    {A : ℕ → ℝ} {S : ℝ} :
    ∃ (A' : ℕ → ℝ) (S' : ℝ),
      ∀ (T Y : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 4)),
        IsMoserWin (I := I) (M := M) g T A S Y →
        IsMoserWin (I := I) (M := M) g T A' S'
          (curvatureRefoldMonomialCoeffField (I := I) (M := M) g g
            (ccTensorUnitValueSection (I := I) (M := M) g Y)
            (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g Y) σ) := by
  obtain ⟨AL, SL, hL⟩ := moserWin_const (I := I) (M := M) g
    (lieCovPair (I := I) (M := M) g g)
  obtain ⟨C, hC0, happ⟩ := moserWin_appRS (I := I) (M := M) g 4 6 2
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  set sfr : ℝ := Real.sqrt fr with hsfr_def
  refine ⟨fun n => C n *
      ((sfr * (sfr * (sfr * (sfr * S)))) ^ 2 * AL n +
        SL ^ 2 * (fr * (fr * (fr * (fr * A n))))),
    SL * (sfr * (sfr * (sfr * (sfr * S)))), ?_⟩
  intro T Y σ hY
  have hiter : slotExtendIter (I := I) (M := M) g 0 2 4 Y =
      slotExtend (I := I) (M := M) g 3 5
        (slotExtend (I := I) (M := M) g 2 4
          (slotExtend (I := I) (M := M) g 1 3
            (slotExtend (I := I) (M := M) g 0 2 Y))) := rfl
  have hslots : IsMoserWin (I := I) (M := M) g T
      (fun n => fr * (fr * (fr * (fr * A n))))
      (sfr * (sfr * (sfr * (sfr * S))))
      (slotExtendIter (I := I) (M := M) g 0 2 4 Y) := by
    rw [hiter]
    exact moserWin_slot (I := I) (M := M)
      (moserWin_slot (I := I) (M := M)
        (moserWin_slot (I := I) (M := M)
          (moserWin_slot (I := I) (M := M) hY)))
  rw [curvMono_eq (I := I) (M := M) g g Y σ]
  exact happ T AL (fun n => fr * (fr * (fr * (fr * A n)))) SL
    (sfr * (sfr * (sfr * (sfr * S)))) _ _ (hL T)
    (moserWin_rsperm (I := I) (M := M) (monoPerm σ) hslots)

/-- **All-order window for the family `daTrans`.**

`daTrans g gm T` is the two-monomial Palatini transfer coefficient of the
`ricciTop` summand of `topKernel_eq`.  The general-order replacement for the
fixed-order-two chain `full_slot_h2_low` → `curvMono_h2` → `ricciTop_h2`'s
inline `hTrans`.  Derivative offset `w = 0`, uniform in the path parameter. -/
theorem moserWin_daTrans (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ (A : ℕ → ℝ) (S : ℝ),
      ∀ (T : SmoothCcTensor g 0 2),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (T.toSection x) ≤ ((Module.finrank ℝ E : ℝ) * δ₀) ^ 2) →
        ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2),
        IsPathPert (I := I) (M := M) g g₁ P T δ₀ →
        IsMoserWin (I := I) (M := M) g T A S
          (daTrans (I := I) (M := M) g g₁ T) := by
  obtain ⟨AW, SW, hW⟩ :=
    moserWin_daWeight (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨A', S', hmono⟩ :=
    moserWin_curvMono (I := I) (M := M) g (A := AW) (S := SW)
  refine ⟨fun n => 2 * (A' n + A' n),
    Real.sqrt (2 * S' ^ 2 + 2 * S' ^ 2), ?_⟩
  intro T hTsup g₁ P hpert
  rw [daTrans, daTransMono, daTransMono]
  exact moserWin_sub (I := I) (M := M)
    (hmono T _ daPermA (hW T hTsup g₁ P hpert))
    (hmono T _ daPermB (hW T hTsup g₁ P hpert))

/-- **All-order window for the `ricciTop` summand of `topKernel_eq`.**

The general-order replacement for `ricciTop_h2`, ball-free: where the
fixed-order statement needed `lowJetSq g 2 P ≤ 1` and `lowJetSq g 2 T ≤ R ^ 2`,
this one needs only the fibre certificates.  Derivative offset `w = 0`, so
`lowJetSq g i (ricciTop g gm T) ≤ K i * (1 + lowJetSq g i T)` sits strictly
inside `topKer_jet`'s `Finset.range (i + 2)` budget. -/
theorem moserWin_ricciTop (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ (A : ℕ → ℝ) (S : ℝ),
      ∀ (T : SmoothCcTensor g 0 2),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (T.toSection x) ≤ ((Module.finrank ℝ E : ℝ) * δ₀) ^ 2) →
        ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2),
        IsPathPert (I := I) (M := M) g g₁ P T δ₀ →
        IsMoserWin (I := I) (M := M) g T A S
          (ricciTop (I := I) (M := M) g g₁ T) := by
  obtain ⟨AT, ST, hT⟩ :=
    moserWin_daTrans (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨AD, SD, hD⟩ := moserWin_dagTop (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨C, hC0, happ⟩ := moserWin_appRS (I := I) (M := M) g 4 4 2
  refine ⟨fun n => C n * (SD ^ 2 * AT n + ST ^ 2 * AD n), ST * SD, ?_⟩
  intro T hTsup g₁ P hpert
  rw [ricciTop]
  exact happ T AT AD ST SD _ _ (hT T hTsup g₁ P hpert) (hD T g₁ P hpert)

/-- Reindexing distributes over a difference of coefficients. -/
private lemma reindexSub (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : SmoothCcTensor g r s) (ρ : Equiv.Perm (Fin r)) :
    reindexCoeffGen (I := I) (M := M) g r s (X - Y) ρ =
      reindexCoeffGen (I := I) (M := M) g r s X ρ -
        reindexCoeffGen (I := I) (M := M) g r s Y ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((reindexCoeffGen (I := I) (M := M) g r s X ρ -
        reindexCoeffGen (I := I) (M := M) g r s Y ρ).toSection x) =
      (reindexCoeffGen (I := I) (M := M) g r s X ρ).toSection x -
        (reindexCoeffGen (I := I) (M := M) g r s Y ρ).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [reindexCoeffGen_toSection, reindexCoeffGen_toSection,
    reindexCoeffGen_toSection]
  rw [show (X - Y).toSection x = X.toSection x - Y.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [reindexCoeffFibGen, reindexCoeffFibGen, reindexCoeffFibGen]
  exact ContinuousLinearMap.sub_comp _ _ _

/-- **All-order window for the family `deTurckPhiMetTotal ∘ realizedFam`.**

The metric-deviation summand of `topKernel_eq`.  The two per-order producers
`traceHessianCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2` and
`ricciArmPrincipalCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2` were
already order-generic; what was missing was the ball-free general-order window
for their common factor `gInvDiffSlotCoeff`, which `moserWin_gInvDiff` now
supplies.  The general-order replacement for `phi_dev_h2`, which needed an
`H2` ball on the state.  Derivative offset `w = 0`, uniform in the path
parameter. -/
theorem moserWin_phiDev (g g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ (A : ℕ → ℝ) (S : ℝ),
      ∀ (T : SmoothCcTensor g 0 2) (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2),
        IsPathPert (I := I) (M := M) g g₁ P T δ₀ →
        IsMoserWin (I := I) (M := M) g T A S
          (deTurckPhiMetTotal (I := I) (M := M) g g_bg g₁ -
            deTurckPhiMetTotal (I := I) (M := M) g g_bg g) := by
  obtain ⟨AG, SG, hG⟩ := moserWin_gInvDiff (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨CTp, hCTp0, hCTp⟩ :=
    traceHessianCoeff_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns
      (I := I) (M := M) g
  obtain ⟨CTj, hCTj0, hCTj⟩ :=
    traceHessianCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2
      (I := I) (M := M) g
  obtain ⟨CRp, hCRp0, hCRp⟩ :=
    ricciArmPrincipalCoeff_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns
      (I := I) (M := M) g
  obtain ⟨CRj, hCRj0, hCRj⟩ :=
    ricciArmPrincipalCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2
      (I := I) (M := M) g
  set ρA : Equiv.Perm (Fin 4) :=
    traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA with hρA
  set ρAT : Equiv.Perm (Fin 4) :=
    traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT with hρAT
  set ATH : ℕ → ℝ :=
    fun n => (∑ i ∈ Finset.range (n + 1), CTj i) * AG n with hATH
  set STH : ℝ := Real.sqrt (CTp 0) * SG with hSTH
  set AR : ℕ → ℝ :=
    fun n => (∑ i ∈ Finset.range (n + 1), CRj i) * AG n with hAR
  set SR : ℝ := Real.sqrt (CRp 0) * SG with hSR
  refine ⟨fun n => 2 * (2 * (ATH n + ATH n) + 2 * (AR n + AR n)),
    Real.sqrt (2 * Real.sqrt (2 * STH ^ 2 + 2 * STH ^ 2) ^ 2 +
      2 * Real.sqrt (2 * SR ^ 2 + 2 * SR ^ 2) ^ 2), ?_⟩
  intro T g₁ P hpert
  have hg := hG T g₁ P hpert
  have hTH : IsMoserWin (I := I) (M := M) g T ATH STH
      (traceHessianCoeff (I := I) (M := M) g g₁ -
        traceHessianCoeff (I := I) (M := M) g g) := by
    refine moserWin_dom (I := I) (M := M) (hCTp0 0) hCTj0 (fun x => ?_)
      (fun i => ?_) hg
    · simpa only [iteratedCovGrad_zero, Nat.add_zero, Nat.zero_add,
        Finset.sum_range_one]
        using hCTp g₁ 0 x
    · simpa only [lowJetSq] using hCTj g₁ i
  have hRA : IsMoserWin (I := I) (M := M) g T AR SR
      (ricciArmPrincipalCoeff (I := I) (M := M) g g₁ -
        ricciArmPrincipalCoeff (I := I) (M := M) g g) := by
    refine moserWin_dom (I := I) (M := M) (hCRp0 0) hCRj0 (fun x => ?_)
      (fun i => ?_) hg
    · simpa only [iteratedCovGrad_zero, Nat.add_zero, Nat.zero_add,
        Finset.sum_range_one]
        using hCRp g₁ 0 x
    · simpa only [lowJetSq] using hCRj g₁ i
  have hdev : deTurckPhiMetTotal (I := I) (M := M) g g_bg g₁ -
      deTurckPhiMetTotal (I := I) (M := M) g g_bg g =
      (reindexCoeffGen (I := I) (M := M) g 4 2
          (traceHessianCoeff (I := I) (M := M) g g₁ -
            traceHessianCoeff (I := I) (M := M) g g) ρA +
        reindexCoeffGen (I := I) (M := M) g 4 2
          (traceHessianCoeff (I := I) (M := M) g g₁ -
            traceHessianCoeff (I := I) (M := M) g g) ρAT) -
      ((ricciArmPrincipalCoeff (I := I) (M := M) g g₁ -
          ricciArmPrincipalCoeff (I := I) (M := M) g g) +
        (ricciArmPrincipalCoeff (I := I) (M := M) g g₁ -
          ricciArmPrincipalCoeff (I := I) (M := M) g g)) := by
    rw [phiMet_reindex (I := I) (M := M) g g_bg g₁,
      phiMet_reindex (I := I) (M := M) g g_bg g,
      reindexSub (I := I) (M := M) g 4 2 _ _ ρA,
      reindexSub (I := I) (M := M) g 4 2 _ _ ρAT]
    abel
  rw [hdev]
  exact moserWin_sub (I := I) (M := M)
    (moserWin_add (I := I) (M := M)
      (moserWin_reindex (I := I) (M := M) ρA hTH)
      (moserWin_reindex (I := I) (M := M) ρAT hTH))
    (moserWin_add (I := I) (M := M) hRA hRA)

end Families

section LieRefold

/-- **All-order window for the moving cometric double trace.**

`pureTrace g gm k` is the genuine `gm⁻¹` double trace retagged to the frozen
metric.  `pureTrace_split` writes it as the fixed parallel trace plus the
inverse-metric-difference correction, and both pieces are windows. -/
theorem moserWin_pureTr (g : SmoothRiemannianMetric I M) (k : ℕ)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ (A : ℕ → ℝ) (S : ℝ),
      ∀ (T : SmoothCcTensor g 0 2) (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2),
        IsPathPert (I := I) (M := M) g g₁ P T δ₀ →
        IsMoserWin (I := I) (M := M) g T A S
          (pureTrace (I := I) (M := M) g g₁ k) := by
  obtain ⟨AD, SD, hD⟩ := moserWin_const (I := I) (M := M) g
    (cometricDoubleTraceField (I := I) g k)
  obtain ⟨AG, SG, hG⟩ := moserWin_gInvSlot (I := I) (M := M) g (k + 1) hδ₀0 hδ₀
  obtain ⟨C, hC0, happ⟩ := moserWin_appRS (I := I) (M := M) g (k + 2) (k + 2) k
  refine ⟨fun n => 2 * (C n * (SG ^ 2 * AD n + SD ^ 2 * AG n) + AD n),
    Real.sqrt (2 * (SD * SG) ^ 2 + 2 * SD ^ 2), ?_⟩
  intro T g₁ P hpert
  rw [pureTrace_split (I := I) (M := M) g g₁ k]
  exact moserWin_add (I := I) (M := M)
    (happ T AD AG SD SG _ _ (hD T) (hG T g₁ P hpert)) (hD T)

/-- **All-order window for the moving double-trace pair coefficient.**

`lieCovPair g gm` is the one factor of the curvature-refold monomials that is
*not* constant along the radial path: its second metric argument is the moving
`gm`.  `pairTrace_eq` factors it into two `pureTrace`s. -/
theorem moserWin_lieCovP (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ (A : ℕ → ℝ) (S : ℝ),
      ∀ (T : SmoothCcTensor g 0 2) (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2),
        IsPathPert (I := I) (M := M) g g₁ P T δ₀ →
        IsMoserWin (I := I) (M := M) g T A S
          (lieCovPair (I := I) (M := M) g g₁) := by
  obtain ⟨A2, S2, h2⟩ := moserWin_pureTr (I := I) (M := M) g 2 hδ₀0 hδ₀
  obtain ⟨A4, S4, h4⟩ := moserWin_pureTr (I := I) (M := M) g 4 hδ₀0 hδ₀
  obtain ⟨C, hC0, happ⟩ := moserWin_appRS (I := I) (M := M) g 6 4 2
  refine ⟨fun n => C n * (S4 ^ 2 * A2 n + S2 ^ 2 * A4 n), S2 * S4, ?_⟩
  intro T g₁ P hpert
  rw [pairTrace_eq (I := I) (M := M) g g₁]
  exact happ T A2 A4 S2 S4 _ _ (h2 T g₁ P hpert) (h4 T g₁ P hpert)

/-- **All-order window for a curvature-refold monomial over the moving
metric.**

The moving sibling of `moserWin_curvMono`: the pair coefficient is taken at the
path metric `g₁` rather than the background, so its constant factor comes from
`moserWin_lieCovP` instead of `moserWin_const`.  These are the monomials of
`lieRefold2`. -/
theorem moserWin_monoMov (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) {A : ℕ → ℝ} {S : ℝ} :
    ∃ (A' : ℕ → ℝ) (S' : ℝ),
      ∀ (T : SmoothCcTensor g 0 2) (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2),
        IsPathPert (I := I) (M := M) g g₁ P T δ₀ →
        ∀ (Y : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 4)),
        IsMoserWin (I := I) (M := M) g T A S Y →
        IsMoserWin (I := I) (M := M) g T A' S'
          (curvatureRefoldMonomialCoeffField (I := I) (M := M) g g₁
            (ccTensorUnitValueSection (I := I) (M := M) g Y)
            (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g Y) σ) := by
  obtain ⟨AL, SL, hL⟩ := moserWin_lieCovP (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨C, hC0, happ⟩ := moserWin_appRS (I := I) (M := M) g 4 6 2
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  set sfr : ℝ := Real.sqrt fr with hsfr_def
  refine ⟨fun n => C n *
      ((sfr * (sfr * (sfr * (sfr * S)))) ^ 2 * AL n +
        SL ^ 2 * (fr * (fr * (fr * (fr * A n))))),
    SL * (sfr * (sfr * (sfr * (sfr * S)))), ?_⟩
  intro T g₁ P hpert Y σ hY
  have hiter : slotExtendIter (I := I) (M := M) g 0 2 4 Y =
      slotExtend (I := I) (M := M) g 3 5
        (slotExtend (I := I) (M := M) g 2 4
          (slotExtend (I := I) (M := M) g 1 3
            (slotExtend (I := I) (M := M) g 0 2 Y))) := rfl
  have hslots : IsMoserWin (I := I) (M := M) g T
      (fun n => fr * (fr * (fr * (fr * A n))))
      (sfr * (sfr * (sfr * (sfr * S))))
      (slotExtendIter (I := I) (M := M) g 0 2 4 Y) := by
    rw [hiter]
    exact moserWin_slot (I := I) (M := M)
      (moserWin_slot (I := I) (M := M)
        (moserWin_slot (I := I) (M := M)
          (moserWin_slot (I := I) (M := M) hY)))
  rw [curvMono_eq (I := I) (M := M) g g₁ Y σ]
  exact happ T AL (fun n => fr * (fr * (fr * (fr * A n)))) SL
    (sfr * (sfr * (sfr * (sfr * S)))) _ _ (hL T g₁ P hpert)
    (moserWin_rsperm (I := I) (M := M) (monoPerm σ) hslots)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
/-- The convex perturbation from the zero endpoint is the radial scaling. -/
private lemma cvxRad (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (s : ℝ) :
    convexPerturbation (I := I) g T (0 : SmoothCcTensor g 0 2) s = s • T := by
  simp [convexPerturbation]

/-- **The radial path is path-perturbation data, uniformly on `[0, 1]`.**

At every parameter `s ∈ [0, 1]` the realized family `realizedFam g T 0 s` is
`g` plus `s • T`, whose fibre operator norm is at most the *same* `δ` as `T`'s,
and whose jets are dominated by `T`'s.  This is the discharge that makes every
constant produced by the family windows independent of `s`. -/
theorem pathPert_rad (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {δ₀ δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ δ₀)
    (hδ_lt : δ < 1)
    (hδg : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (hTsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (T.toSection x) ≤ ((Module.finrank ℝ E : ℝ) * δ₀) ^ 2)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    IsPathPert (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδg hδZ s)
      (convexPerturbation (I := I) g T 0 s) T δ₀ := by
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (convexPerturbation (I := I) g T 0 s)) δ := by
    intro y v w
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g T 0 hδg hδZ s y v w
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith only [hs1] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs0]
      ring
    rwa [heq] at hraw
  refine ⟨⟨δ, hδ0, hδ_le, hP⟩,
    fun y v w => realizedFam_inner_of_mem (I := I) g T 0 hδg hδZ hsmem y v w,
    fun x => ?_, fun n => ?_⟩
  · rw [cvxRad, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
      Pi.smul_apply, riemannianFiberNormSq_smul]
    nlinarith [hTsup x, riemannianFiberNormSq_nonneg
      (I := I) (M := M) g 0 2 x (T.toSection x)]
  · rw [cvxRad, opJetSmul]
    nlinarith [jetNn (I := I) (M := M) (m := n) g T]

/-- **All-order window for the `lieRefold2` summand of `topKernel_eq`.**

The remaining summand, and the only one whose curvature monomials are taken
over the *moving* metric.  `deTurckLieCovDerivRefoldC2Family_eq_symmS_weight`
writes it as `s` times a three-term signed combination of monomials in
`symmS g T`; each is a window by `moserWin_monoMov`, and both scalars are
bounded by one, so the constants do not see `s`.  Derivative offset `w = 0`. -/
theorem moserWin_lieRef2 (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ (A : ℕ → ℝ) (S : ℝ),
      ∀ (T : SmoothCcTensor g 0 2),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (T.toSection x) ≤ ((Module.finrank ℝ E : ℝ) * δ₀) ^ 2) →
        ∀ {δ : ℝ}, 0 ≤ δ → δ ≤ δ₀ → δ < 1 →
        ∀ (hδg : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ)
          (hδZ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
          {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
        IsMoserWin (I := I) (M := M) g T A S
          (lieRefold2 (I := I) (M := M) g T hδg hδZ s) := by
  obtain ⟨AY, SY, hY⟩ := moserWin_symmS (I := I) (M := M) g hδ₀0
  obtain ⟨AM, SM, hM⟩ :=
    moserWin_monoMov (I := I) (M := M) g hδ₀0 hδ₀ (A := AY) (S := SY)
  refine ⟨fun n => 2 * (2 * (AM n + AM n) + AM n),
    Real.sqrt (2 * Real.sqrt (2 * SM ^ 2 + 2 * SM ^ 2) ^ 2 + 2 * SM ^ 2), ?_⟩
  intro T hTsup δ hδ0 hδ_le hδ_lt hδg hδZ s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hpert :=
    pathPert_rad (I := I) (M := M) g T hδ0 hδ_le hδ_lt hδg hδZ hTsup hs
  have hmono : ∀ σ : Equiv.Perm (Fin 4),
      IsMoserWin (I := I) (M := M) g T AM SM
        (curvatureRefoldMonomialCoeffField (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδg hδZ s)
          (ccTensorUnitValueSection (I := I) (M := M) g
            (symmS (I := I) (M := M) g T))
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g
            (symmS (I := I) (M := M) g T)) σ) :=
    fun σ => hM T _ _ hpert (symmS (I := I) (M := M) g T) σ (hY T hTsup)
  have hAM : ∀ n, 0 ≤ AM n :=
    fun n => moserWin_nnA (I := I) (M := M) (hmono daPermA) n
  have hSM : 0 ≤ SM := (hmono daPermA).1
  have hscal : ∀ i : Fin 3,
      IsMoserWin (I := I) (M := M) g T AM SM
        (lieRefoldEps i •
          curvatureRefoldMonomialCoeffField (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδg hδZ s)
            (ccTensorUnitValueSection (I := I) (M := M) g
              (symmS (I := I) (M := M) g T))
            (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g
              (symmS (I := I) (M := M) g T)) (lieRefoldQ i)) := by
    intro i
    have heps : |lieRefoldEps i| ≤ (1 : ℝ) := by
      fin_cases i <;> simp [lieRefoldEps]
    have heps2 : lieRefoldEps i ^ 2 ≤ 1 := by
      nlinarith [abs_nonneg (lieRefoldEps i), sq_abs (lieRefoldEps i), heps]
    refine moserWin_mono (I := I) (M := M)
      (moserWin_smul (I := I) (M := M) (lieRefoldEps i)
        (hmono (lieRefoldQ i))) (fun n => ?_) ?_
    · nlinarith [hAM n]
    · nlinarith [hSM, abs_nonneg (lieRefoldEps i)]
  rw [lieRefold2, deTurckLieCovDerivRefoldC2Family_eq_symmS_weight,
    Fin.sum_univ_three]
  have hsum := moserWin_add (I := I) (M := M)
    (moserWin_add (I := I) (M := M) (hscal 0) (hscal 1)) (hscal 2)
  refine moserWin_mono (I := I) (M := M)
    (moserWin_smul (I := I) (M := M) s hsum) (fun n => ?_) ?_
  · have hs2 : s ^ 2 ≤ 1 := by nlinarith
    nlinarith [hAM n]
  · have habs : |s| = s := abs_of_nonneg hs0
    rw [habs]
    nlinarith [Real.sqrt_nonneg
      (2 * Real.sqrt (2 * SM ^ 2 + 2 * SM ^ 2) ^ 2 + 2 * SM ^ 2)]

end LieRefold

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
