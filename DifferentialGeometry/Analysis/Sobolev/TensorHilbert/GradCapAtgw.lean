import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.AtgwArmFold
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingSharpC0JetSum
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalArmEnergyCrossTerm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence

/-!
# The `Λ₁`-capped (`∇P`-capped) antidiagonal-grid currency

The radius-free currency of `AtgwArmFold.lean` measures every arm against the
state's own fibre jets `gridBase g₀ P x j = |∇ʲP|²(x)`, and its integration step
`atgwToJet` spends the order-zero cap `‖P‖_∞ = Λ₀`.  That is exactly right for
arms that are **linear** in the connection difference: one derivative of the
state per arm, offsets add to `+2`, budget `range (i+2)`.

It is NOT enough for the two summands of `selfLow_split` that are **quadratic**
in `∇P` (the `A·A` arm inside `ricciGoodLow`, and `lc0VB`).  There both arms
carry a derivative, the offsets add to `+3`, and the resulting `range (i+3)`
budget is genuinely false: concentrating a bump keeps `‖T‖` and `‖∇T‖` bounded
in `L²` while `‖ |∇T|² ‖_{L²}` blows up.  Gagliardo--Nirenberg closes the gap
only through the split `‖∇P‖_∞ · ‖∇^{i+1}P‖_{L²}`, i.e. through a cap on the
FIRST covariant gradient.

This module supplies that cap and the currency that consumes it.

* `gradCapOfJets` / `gradCapOfBall` — **the `Λ₁` producer**: on a fixed
  `H^{a+2}` ball with `1 ≤ a` in dimension three (`H³ ⊂ C¹`), the first
  covariant gradient is bounded pointwise by a constant of the background and
  the radius.  The gate is `1 ≤ a`; the supercritical pointwise-jet producers
  of the tame layer, which need `2·finrank + 10 ≤ a`, are NOT used.
* `gradBase_eq` — the shifted grid base: `gridBase g₀ (∇P) x j` is
  `gridBase g₀ P x (1 + j)`, i.e. `|∇^{j+1}P|²(x)`.  Running the whole grid on
  `∇P` instead of `P` is what buys the missing order.
* `atgwCapToJet` — **the capped integration step**: a pointwise grid window in
  the SHIFTED base at offset `w` integrates into the `range (n + w + 1)` budget
  measured in `P`'s own jets.  At `w = 1` — which is where a two-arm fold of two
  once-differentiated arms lands in the shifted base — this is `range (n + 2)`,
  exactly the budget of the low-window towers.

The analytic content is entirely in the valence-generic engines
`grid_prod_int_le` / `atgGridIntRs` / `atgwToJetRs`: the capped currency is
those engines instantiated at the base valence `(0, 3)` of `∇P`, with `Λ₁` in
the role that `Λ₀` plays at `(0, 2)`.
-/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### Composing iterated gradients -/

/-- **Norm form of the iterated-gradient composition.**  `‖∇ᵐ(∇ˡΨ)‖ = ‖∇^{l+m}Ψ‖`.

The pointwise fibre-norm form is `rfns_iteratedCovGrad_comp`; this is its `L²`
consequence, needed whenever a bound stated in the jets of `∇P` is to be read
back as a bound in the jets of `P`. -/
theorem icgNormComp (g₀ : SmoothRiemannianMetric I M) (r s l m : ℕ)
    (Ψ : SmoothCcTensor g₀ r s) :
    ‖iteratedCovGrad (I := I) g₀ r (s + l) m (iteratedCovGrad (I := I) g₀ r s l Ψ)‖ =
      ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖ := by
  have hnn1 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ r (s + l) m
      (iteratedCovGrad (I := I) g₀ r s l Ψ)‖ := norm_nonneg _
  have hnn2 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖ := norm_nonneg _
  have hsq : ‖iteratedCovGrad (I := I) g₀ r (s + l) m
        (iteratedCovGrad (I := I) g₀ r s l Ψ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖ ^ 2 := by
    simp only [SmoothCcTensor.norm_def]
    rw [tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g₀ r ((s + l) + m),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g₀ r (s + (l + m))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ r s l m Ψ x
  nlinarith [hsq, hnn1, hnn2,
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ r (s + l) m (iteratedCovGrad (I := I) g₀ r s l Ψ)‖ -
      ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖)]

/-- **The shifted grid base.**  The generic-valence `gridBase` applied to the
first covariant gradient of the state is the state's own jet family shifted by
one: `gridBase g₀ (∇P) x j = |∇^{j+1}P|²(x)`. -/
theorem gradBase_eq (g₀ : SmoothRiemannianMetric I M) {rb sb : ℕ}
    (P : SmoothCcTensor g₀ rb sb) (x : M) (j : ℕ) :
    gridBase (I := I) (M := M) g₀ (iteratedCovGrad (I := I) g₀ rb sb 1 P) x j =
      gridBase (I := I) (M := M) g₀ P x (1 + j) :=
  rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ rb sb 1 j P x

/-! ### The `Λ₁` producer -/

/-- **The `∇P` cap from a jet ball (`Λ₁`, jet form).**

In dimension three, with `1 ≤ a`, a bound `R₀` on all covariant jets of `T`
through order `a + 2` gives a POINTWISE bound on the first covariant gradient:
`|∇T|(x) ≤ Λ₁` for every `x`, with `Λ₁` a constant of the background metric and
`R₀` only.

This is the fibre Sobolev embedding `H^{1+2} ⊂ C¹` in disguise: the sharp
fibre-norm estimate `exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`
at valence `(0, 3)` needs the jets of `∇T` through order `finrank/2 + 1`, i.e.
the jets of `T` through order `finrank/2 + 2 = 3` when `finrank = 3`, and
`a + 2 ≥ 3` is exactly `1 ≤ a`.  No supercritical (`2·finrank + 10 ≤ a`) gate is
inherited. -/
theorem gradCapOfJets (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 1 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Λ₁ : ℝ, 0 ≤ Λ₁ ∧
      ∀ (T : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R₀) →
        ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) ≤ Λ₁ ^ 2 := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g₀ 0 (2 + 1)
  have hw : Module.finrank ℝ E / 2 + 2 = 3 := by omega
  refine ⟨Real.sqrt (C ^ 2 * 3 * R₀ ^ 2), Real.sqrt_nonneg _, ?_⟩
  intro T hjet x
  have hsq : Real.sqrt (C ^ 2 * 3 * R₀ ^ 2) ^ 2 = C ^ 2 * 3 * R₀ ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [hsq]
  refine le_trans (hC (iteratedCovGrad (I := I) g₀ 0 2 1 T) x) ?_
  rw [hw]
  have hterm : ∀ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + 1) j
          (iteratedCovGrad (I := I) g₀ 0 2 1 T)‖ ^ 2 ≤ R₀ ^ 2 := by
    intro j hj
    have hjr : j < 3 := Finset.mem_range.mp hj
    rw [icgNormComp (I := I) (M := M) g₀ 0 2 1 j T]
    have hle : ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) T‖ ≤ R₀ :=
      hjet (1 + j) (by omega)
    nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 (1 + j) T), hle, hR₀]
  have hsum : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + 1) j
        (iteratedCovGrad (I := I) g₀ 0 2 1 T)‖ ^ 2) ≤ 3 * R₀ ^ 2 := by
    calc (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + 1) j
            (iteratedCovGrad (I := I) g₀ 0 2 1 T)‖ ^ 2)
        ≤ ∑ _j ∈ Finset.range 3, R₀ ^ 2 := Finset.sum_le_sum hterm
      _ = 3 * R₀ ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  calc C ^ 2 * ∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + 1) j
          (iteratedCovGrad (I := I) g₀ 0 2 1 T)‖ ^ 2
      ≤ C ^ 2 * (3 * R₀ ^ 2) := mul_le_mul_of_nonneg_left hsum (sq_nonneg C)
    _ = C ^ 2 * 3 * R₀ ^ 2 := by ring

/-- **The `∇P` cap from the `H^{a+2}` Sobolev ball (`Λ₁`, ball form).**

This is the form the C0 jet tower threads: `selfLow_jet` carries
`‖smoothCcToTensorHs g ((a:ℝ)+2) T‖ ≤ R₀` with `1 ≤ a`, and this turns it into
the pointwise cap on `∇T` that the capped currency consumes.  The Sobolev-ball
to jet-ball passage is `exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general`;
the gate stays `1 ≤ a`. -/
theorem gradCapOfBall (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 1 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Λ₁ : ℝ, 0 ≤ Λ₁ ∧
      ∀ (T : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) ≤ Λ₁ ^ 2 := by
  classical
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  obtain ⟨Λ₁, hΛ₁_nn, hΛ₁⟩ :=
    gradCapOfJets (I := I) (M := M) hDim g₀ a ha (R₀ := C2 * R₀) (mul_nonneg hC2_nn hR₀)
  refine ⟨Λ₁, hΛ₁_nn, ?_⟩
  intro T hball
  refine hΛ₁ T (fun j hj => ?_)
  have hsum := hC2 T
  have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T
  rw [hcast] at hsum
  have hsumB : ∑ l ∈ Finset.range (a + 2 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T‖ ≤ C2 * R₀ :=
    le_trans hsum (mul_le_mul_of_nonneg_left hball hC2_nn)
  exact le_trans
    (Finset.single_le_sum
      (f := fun l => ‖iteratedCovGrad (I := I) g₀ 0 2 l T‖)
      (fun l _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))) hsumB

/-! ### The base shift

Pure combinatorics of `antidiagonalTupleGrid`, stated here rather than in
`Analysis/Sobolev/AntidiagonalTupleProductGrid.lean` only to keep the rebuild
scope of this brick contained; the canonical home is that module (recorded in
`GradCapAtgw.md`).

An arm carrying one derivative of the state has its order-`i` fibre jet bounded
by `atgw bP (i + 2)`: grids in the state's own jets of weight `≤ i + 1`.  What
the capped currency needs is the SAME bound read in the shifted base
`b'P j = |∇^{j+1}P|²` at level `i + 1`, i.e. grids in the jets of `∇P` of weight
`≤ i`.  That is legitimate because every factor of weight `w ≥ 1` in the old
base becomes a factor of weight `w - 1` in the new one, and the factors of
weight `0` and `1` are absorbed by the two caps `‖P‖_∞` and `‖∇P‖_∞`. -/

/-- The constant of the base shift at level `k`: a finite sum of powers of the
cap against the antidiagonal-tuple counts. -/
def shiftConst (Λ : ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (k + 1), Λ ^ m * Combinatorics.antidiagonalTupleGridCount m

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
/-- The shift constant is nonnegative. -/
lemma shiftConst_nn {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (k : ℕ) : 0 ≤ shiftConst Λ k :=
  Finset.sum_nonneg (fun m _ => mul_nonneg (pow_nonneg hΛ0 m)
    (Combinatorics.antidiagonalTupleGridCount_nonneg m))

/-- **One antidiagonal product term, re-read in the shifted base.**

A product `∏ b (e q)` over a tuple of total weight `m ≥ 1` splits into the
factors of weight `≥ 2` — which are honest factors of the shifted base at total
weight `< m` — and the factors of weight `0` or `1`, each bounded by the cap
`Λ`. -/
private lemma prodShift {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (h0 : b 0 ≤ Λ) (h1 : b 1 ≤ Λ) {n m : ℕ} (hn : n ≤ m) (hm : 1 ≤ m)
    (e : Fin n → ℕ) (he : ∑ q, e q = m) :
    (∏ q : Fin n, b (e q)) ≤
      Λ ^ m * Combinatorics.antidiagonalTupleGridWindow (fun j => b (j + 1)) m := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  set b' : ℕ → ℝ := fun j => b (j + 1) with hb'def
  have hb'nn : ∀ j, 0 ≤ b' j := fun j => hb _
  set W : ℝ := Combinatorics.antidiagonalTupleGridWindow b' m with hWdef
  have hW1 : (1 : ℝ) ≤ W :=
    Combinatorics.one_le_antidiagonalTupleGridWindow b' hb'nn (by omega)
  have hWnn : (0 : ℝ) ≤ W := le_trans zero_le_one hW1
  set S : Finset (Fin n) := Finset.univ.filter (fun q => 2 ≤ e q) with hSdef
  set Sc : Finset (Fin n) := Finset.univ.filter (fun q => ¬ (2 ≤ e q)) with hScdef
  -- the total weight carried by the big factors, after the shift
  set mT : ℕ := ∑ q ∈ S, (e q - 1) with hmTdef
  have hSe : ∀ q ∈ S, 2 ≤ e q := by
    intro q hq; rw [hSdef, Finset.mem_filter] at hq; exact hq.2
  have hSsum : ∑ q ∈ S, e q ≤ m := by
    rw [← he]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun q _ _ => Nat.zero_le _)
  have hmT_add : mT + S.card = ∑ q ∈ S, e q := by
    rw [hmTdef, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun q hq => by have := hSe q hq; omega)
  have hcardS : S.card ≤ mT := by
    rw [hmTdef, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun q hq => by have := hSe q hq; omega)
  have hmT_lt : mT < m := by
    rcases Nat.eq_zero_or_pos S.card with hc | hc
    · have hS0 : S = ∅ := Finset.card_eq_zero.mp hc
      have hz : mT = 0 := by rw [hmTdef, hS0, Finset.sum_empty]
      omega
    · omega
  -- reindex the big factors along `Fin S.card`
  obtain ⟨f, hsum_f, hprod_f⟩ : ∃ f : Fin S.card → ℕ,
      (∑ i, f i = mT) ∧ (∏ i, b' (f i)) = ∏ q ∈ S, b (e q) := by
    refine ⟨fun i => e ((S.equivFin.symm i : {x // x ∈ S}) : Fin n) - 1, ?_, ?_⟩
    · have h1 : (∑ i : Fin S.card,
            (e ((S.equivFin.symm i : {x // x ∈ S}) : Fin n) - 1)) =
          ∑ q : {x // x ∈ S}, (e (q : Fin n) - 1) :=
        Fintype.sum_equiv S.equivFin.symm _ _ (fun i => rfl)
      rw [h1, hmTdef]
      exact Finset.sum_coe_sort S (fun q => e q - 1)
    · have h1 : (∏ i : Fin S.card,
            b' (e ((S.equivFin.symm i : {x // x ∈ S}) : Fin n) - 1)) =
          ∏ q : {x // x ∈ S}, b' (e (q : Fin n) - 1) :=
        Fintype.prod_equiv S.equivFin.symm _ _ (fun i => rfl)
      rw [h1, Finset.prod_coe_sort S (fun q => b' (e q - 1))]
      refine Finset.prod_congr rfl (fun q hq => ?_)
      have h2 := hSe q hq
      simp only [hb'def]
      congr 1
      omega
  have hmem : f ∈ Finset.Nat.antidiagonalTuple S.card mT :=
    Finset.Nat.mem_antidiagonalTuple.mpr hsum_f
  have hbig : (∏ q ∈ S, b (e q)) ≤ W := by
    rw [← hprod_f, hWdef]
    refine le_trans
      (Combinatorics.prodTerm_le_antidiagonalTupleGrid b' hb'nn mT S.card (by omega) f hmem) ?_
    exact Combinatorics.antidiagonalTupleGrid_le_window b' hb'nn hmT_lt
  -- the small factors are eaten by the cap
  have hsmall : (∏ q ∈ Sc, b (e q)) ≤ Λ ^ Sc.card := by
    calc (∏ q ∈ Sc, b (e q))
        ≤ ∏ _q ∈ Sc, Λ := by
          refine Finset.prod_le_prod (fun q _ => hb _) (fun q hq => ?_)
          rw [hScdef, Finset.mem_filter] at hq
          have hq2 : e q = 0 ∨ e q = 1 := by omega
          rcases hq2 with h | h <;> rw [h]
          · exact h0
          · exact h1
      _ = Λ ^ Sc.card := by rw [Finset.prod_const]
  have hSc_le : Sc.card ≤ m := le_trans (le_trans (Finset.card_filter_le _ _)
    (le_of_eq (Finset.card_univ.trans (Fintype.card_fin n)))) hn
  have hpow : Λ ^ Sc.card ≤ Λ ^ m := pow_le_pow_right₀ hΛ1 hSc_le
  -- assemble
  have hsplit : (∏ q : Fin n, b (e q)) = (∏ q ∈ S, b (e q)) * ∏ q ∈ Sc, b (e q) := by
    rw [hSdef, hScdef]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun q => 2 ≤ e q)
      (fun q => b (e q))).symm
  rw [hsplit]
  calc (∏ q ∈ S, b (e q)) * ∏ q ∈ Sc, b (e q)
      ≤ W * Λ ^ m := by
        refine mul_le_mul hbig (le_trans hsmall hpow) (Finset.prod_nonneg (fun q _ => hb _)) hWnn
    _ = Λ ^ m * W := by ring

/-- **The base shift at one grid level** (`1 ≤ m`; at `m = 0` the shifted window
of level `0` is empty and the statement is false — that case is handled inside
`atgwShift`, where the window is taken at the outer level `k ≥ 1`). -/
private lemma gridShift {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (h0 : b 0 ≤ Λ) (h1 : b 1 ≤ Λ) {m : ℕ} (hm1 : 1 ≤ m) :
    Combinatorics.antidiagonalTupleGrid b m ≤
      Λ ^ m * Combinatorics.antidiagonalTupleGridCount m *
        Combinatorics.antidiagonalTupleGridWindow (fun j => b (j + 1)) m := by
  classical
  have hb'nn : ∀ j, 0 ≤ (fun j => b (j + 1)) j := fun j => hb _
  set W : ℝ := Combinatorics.antidiagonalTupleGridWindow (fun j => b (j + 1)) m with hWdef
  rw [Combinatorics.antidiagonalTupleGrid, Combinatorics.antidiagonalTupleGridCount]
  have hterm : ∀ n' ∈ Finset.range (m + 1),
      (∑ e ∈ Finset.Nat.antidiagonalTuple n' m, ∏ q : Fin n', b (e q)) ≤
        ((Finset.Nat.antidiagonalTuple n' m).card : ℝ) * (Λ ^ m * W) := by
    intro n' hn'
    have hn'le : n' ≤ m := by have := Finset.mem_range.mp hn'; omega
    calc (∑ e ∈ Finset.Nat.antidiagonalTuple n' m, ∏ q : Fin n', b (e q))
        ≤ ∑ _e ∈ Finset.Nat.antidiagonalTuple n' m, Λ ^ m * W := by
          refine Finset.sum_le_sum (fun e he => ?_)
          exact prodShift hb hΛ1 h0 h1 hn'le hm1 e
            (Finset.Nat.mem_antidiagonalTuple.mp he)
      _ = ((Finset.Nat.antidiagonalTuple n' m).card : ℝ) * (Λ ^ m * W) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  calc (∑ n' ∈ Finset.range (m + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n' m, ∏ q : Fin n', b (e q))
      ≤ ∑ n' ∈ Finset.range (m + 1),
          ((Finset.Nat.antidiagonalTuple n' m).card : ℝ) * (Λ ^ m * W) :=
        Finset.sum_le_sum hterm
    _ = Λ ^ m * (∑ n' ∈ Finset.range (m + 1),
          ((Finset.Nat.antidiagonalTuple n' m).card : ℝ)) * W := by
        rw [← Finset.sum_mul]; ring

/-- **The base shift on a whole window.**

A grid window of level `k + 1` in the state's own jets is dominated by the grid
window of level `k` in the jets of `∇P`, at the price of the two caps.  This is
the bridge that lets an arm's EXISTING radius-free window (stated in the state's
base at offset `+1`, i.e. level `i + 2`) enter the capped currency at offset `0`
in the shifted base, i.e. level `i + 1`. -/
theorem atgwShift {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (h0 : b 0 ≤ Λ) (h1 : b 1 ≤ Λ) {k : ℕ} (hk : 1 ≤ k) :
    Combinatorics.antidiagonalTupleGridWindow b (k + 1) ≤
      shiftConst Λ k * Combinatorics.antidiagonalTupleGridWindow (fun j => b (j + 1)) k := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  have hb'nn : ∀ j, 0 ≤ (fun j => b (j + 1)) j := fun j => hb _
  set Wk : ℝ := Combinatorics.antidiagonalTupleGridWindow (fun j => b (j + 1)) k with hWkdef
  have hWk_nn : (0 : ℝ) ≤ Wk :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg _ hb'nn k
  have hWk_one : (1 : ℝ) ≤ Wk :=
    Combinatorics.one_le_antidiagonalTupleGridWindow _ hb'nn (by omega)
  rw [Combinatorics.antidiagonalTupleGridWindow, shiftConst, Finset.sum_mul]
  refine Finset.sum_le_sum (fun m hm => ?_)
  have hmk : m ≤ k := by have := Finset.mem_range.mp hm; omega
  have hcoef_nn : (0 : ℝ) ≤ Λ ^ m * Combinatorics.antidiagonalTupleGridCount m :=
    mul_nonneg (pow_nonneg hΛ0 m) (Combinatorics.antidiagonalTupleGridCount_nonneg m)
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · subst hm0
    rw [Combinatorics.antidiagonalTupleGrid_zero, pow_zero, one_mul]
    have hcount : Combinatorics.antidiagonalTupleGridCount 0 = 1 := by
      rw [Combinatorics.antidiagonalTupleGridCount, Finset.sum_range_one,
        Finset.Nat.antidiagonalTuple_zero_zero]
      norm_num
    rw [hcount, one_mul]
    exact hWk_one
  · refine le_trans (gridShift hb hΛ1 h0 h1 hm1) ?_
    exact mul_le_mul_of_nonneg_left
      (Combinatorics.antidiagonalTupleGridWindow_mono _ hb'nn hmk) hcoef_nn

/-! ### The capped integration step -/

/-- **The `Λ₁`-capped grid-window integration step.**

A pointwise `antidiagonalTupleGridWindow` bound at offset `w` measured in the
SHIFTED base — the fibre jets of `∇P` rather than of `P` — integrates to the
affine `L²` jet bound with the `range (n + w + 1)` budget in `P`'s own jets.
The order-zero cap it spends is `Λ₁ = ‖∇P‖_∞`, not `‖P‖_∞`, which is precisely
the Gagliardo--Nirenberg endpoint swap that buys the missing order.

At `w = 1` this reads `range (n + 2)`: a two-arm fold of two arms each carrying
one derivative of the state sits at offset `0 + 0 + 1 = 1` in the shifted base
(each such arm's jets are grids in `∇P` of weight `≤ i'`), so the quadratic
summands land on the same `range (i + 2)` budget as the linear ones. -/
theorem atgwCapToJet (g₀ : SmoothRiemannianMetric I M) {Λ₁ : ℝ} (hΛ₁0 : 0 ≤ Λ₁) :
    ∃ Kint : ℕ → ℝ, (∀ k, 0 ≤ Kint k) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2) →
        ∀ (r c n w : ℕ) (X : SmoothCcTensor g₀ r c) (K : ℝ), 0 ≤ K →
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r (c + n) x
              ((iteratedCovGrad (I := I) g₀ r c n X).toSection x) ≤
            K * Combinatorics.antidiagonalTupleGridWindow
              (gridBase (I := I) (M := M) g₀
                (iteratedCovGrad (I := I) g₀ 0 2 1 P) x) (n + w)) →
          ‖iteratedCovGrad (I := I) g₀ r c n X‖ ^ 2 ≤
            K * (∑ k ∈ Finset.range (n + w), Kint k) *
              (1 + ∑ j ∈ Finset.range (n + w + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Kint, hKint_nn, hint⟩ := atgwToJetRs (I := I) (M := M) g₀ 0 (2 + 1) hΛ₁0
  refine ⟨Kint, hKint_nn, ?_⟩
  intro P hsup r c n w X K hK hX
  have hbase := hint (iteratedCovGrad (I := I) g₀ 0 2 1 P) hsup r c n w X K hK hX
  refine hbase.trans ?_
  have hKK_nn : 0 ≤ K * ∑ k ∈ Finset.range (n + w), Kint k :=
    mul_nonneg hK (Finset.sum_nonneg (fun k _ => hKint_nn k))
  refine mul_le_mul_of_nonneg_left ?_ hKK_nn
  have hstep : (∑ j ∈ Finset.range (n + w),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + 1) j
          (iteratedCovGrad (I := I) g₀ 0 2 1 P)‖ ^ 2) ≤
      ∑ j ∈ Finset.range (n + w + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
    have hre : (∑ j ∈ Finset.range (n + w),
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + 1) j
            (iteratedCovGrad (I := I) g₀ 0 2 1 P)‖ ^ 2) =
        ∑ j ∈ Finset.Ico 1 (n + w + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by rw [show n + w + 1 - 1 = n + w from by omega]) (fun j _ => ?_)
      rw [icgNormComp (I := I) (M := M) g₀ 0 2 1 j P]
    rw [hre]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun j hj => Finset.mem_range.mpr (by
        rw [Finset.mem_Ico] at hj; omega))
      (fun j _ _ => sq_nonneg _)
  linarith only [hstep]

/-! ### The capped two-arm workhorse -/

/-- The shifted base as a function equality, in the form the arm windows need. -/
theorem gradBase_fun (g₀ : SmoothRiemannianMetric I M) {rb sb : ℕ}
    (P : SmoothCcTensor g₀ rb sb) (x : M) :
    (fun j => gridBase (I := I) (M := M) g₀ P x (j + 1)) =
      gridBase (I := I) (M := M) g₀ (iteratedCovGrad (I := I) g₀ rb sb 1 P) x := by
  funext j
  rw [gradBase_eq (I := I) (M := M) g₀ P x j, Nat.add_comm 1 j]

/-- **Re-basing an arm's radius-free window into the `∇P`-capped base.**

Every radius-free per-order producer of the `DeTurck`/`LieCorr0` layer delivers
its arm as `KX i · atgw bP (i + u + 2)` — for an arm carrying exactly one
derivative of the state, `u = 0`.  Against the two caps this is
`KX i · shiftConst Λ (i+u+1) · atgw b'P (i + u + 1)` in the base of `∇P`: **the
level drops by one**, which is exactly the order the quadratic summands were
missing.  No arm has to be re-derived. -/
theorem armShift (g₀ : SmoothRiemannianMetric I M) {rb sb : ℕ}
    (P : SmoothCcTensor g₀ rb sb) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ Λ)
    (hP1 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 1 ≤ Λ)
    {r c : ℕ} (X : SmoothCcTensor g₀ r c) {KX : ℕ → ℝ} (hKX : ∀ i, 0 ≤ KX i) (u : ℕ)
    (hX : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
          ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) ≤
        KX i * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P x) (i + u + 2))
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
        ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) ≤
      KX i * shiftConst Λ (i + u + 1) * Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ (iteratedCovGrad (I := I) g₀ rb sb 1 P) x)
        (i + u + 1) := by
  refine le_trans (hX i x) ?_
  have hb := gridBase_nn (I := I) (M := M) g₀ P x
  have hshift := atgwShift (b := gridBase (I := I) (M := M) g₀ P x) hb hΛ1
    (hP0 x) (hP1 x) (k := i + u + 1) (by omega)
  rw [← gradBase_fun (I := I) (M := M) g₀ P x, mul_assoc]
  exact mul_le_mul_of_nonneg_left hshift (hKX i)

/-- **The `Λ`-capped POINTWISE two-arm fold.**

Both arms carry one derivative of the state (`bP`-offset `+2`); against the two
caps their `appCcRS` product has its order-`n` fibre jet inside the SHIFTED-base
window at level `n + 1`.  This is the pointwise half of `atgwCapFold`, exposed
separately because a nested product (`lc0VB = cometric ⋆ (mcd ⋆ ipLow)`) has to
feed the inner fold's output into the outer one before integrating. -/
theorem atgwCapArm (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ Λ)
    (hP1 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 1 ≤ Λ)
    {p a b : ℕ} (Φ : SmoothCcTensor g₀ a b) (W : SmoothCcTensor g₀ p a)
    {KΦ KW : ℕ → ℝ} (hKΦ : ∀ i, 0 ≤ KΦ i) (hKW : ∀ l, 0 ≤ KW l)
    (hΦ : ∀ (i' : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ a (b + i') x
          ((iteratedCovGrad (I := I) g₀ a b i' Φ).toSection x) ≤
        KΦ i' * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P x) (i' + 2))
    (hW : ∀ (l : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
          ((iteratedCovGrad (I := I) g₀ p a l W).toSection x) ≤
        KW l * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P x) (l + 2))
    (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ p (b + n) x
        ((iteratedCovGrad (I := I) g₀ p b n
          (appCcRS (I := I) (M := M) g₀ p a b Φ W)).toSection x) ≤
      foldConst (E := E) 0 0 (fun i => KΦ i * shiftConst Λ (i + 1))
          (fun l => KW l * shiftConst Λ (l + 1)) n *
        Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ (iteratedCovGrad (I := I) g₀ 0 2 1 P) x)
          (n + 1) := by
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  have hKΦ' : ∀ i, 0 ≤ KΦ i * shiftConst Λ (i + 1) :=
    fun i => mul_nonneg (hKΦ i) (shiftConst_nn hΛ0 _)
  have hKW' : ∀ l, 0 ≤ KW l * shiftConst Λ (l + 1) :=
    fun l => mul_nonneg (hKW l) (shiftConst_nn hΛ0 _)
  have hΦ' := armShift (I := I) (M := M) g₀ P hΛ1 hP0 hP1 Φ hKΦ 0
    (fun i y => by simpa using hΦ i y)
  have hW' := armShift (I := I) (M := M) g₀ P hΛ1 hP0 hP1 W hKW 0
    (fun l y => by simpa using hW l y)
  simpa using atgwFold (I := I) (M := M) g₀ (u := 0) (v := 0) Φ W
    (iteratedCovGrad (I := I) g₀ 0 2 1 P) hKΦ' hKW'
    (fun i' y => by simpa using hΦ' i' y) (fun l y => by simpa using hW' l y) n x

/-- **The `Λ`-capped two-arm fold-and-integrate: the workhorse of the quadratic
C0 summands.**

If both arms of an `appCcRS` product carry ONE derivative of the state — the
shape that makes the summand quadratic in `∇P`, and the reason the radius-free
currency lands at `range (i+3)` — then against the two pointwise caps
`|P| ≤ Λ`, `|∇P| ≤ Λ` the product's order-`n` `L²` jet is controlled by the
`range (n + 2)` budget.  That is the same budget the LINEAR summands enjoy, so
`selfLow_jet`'s window is honest on both halves of `selfLow_split`.

The three steps are `armShift` (re-base each arm, dropping a level), `atgwFold`
at offsets `(0, 0)` in the shifted base, and `atgwCapToJet` at `w = 1`. -/
theorem atgwCapFold (g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ Kint : ℕ → ℝ, (∀ k, 0 ≤ Kint k) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ Λ) →
        (∀ x : M, gridBase (I := I) (M := M) g₀ P x 1 ≤ Λ) →
        ∀ {p a b : ℕ} (Φ : SmoothCcTensor g₀ a b) (W : SmoothCcTensor g₀ p a)
          {KΦ KW : ℕ → ℝ}, (∀ i, 0 ≤ KΦ i) → (∀ l, 0 ≤ KW l) →
          (∀ (i' : ℕ) (x : M),
            riemannianFiberNormSq (I := I) (M := M) g₀ a (b + i') x
                ((iteratedCovGrad (I := I) g₀ a b i' Φ).toSection x) ≤
              KΦ i' * Combinatorics.antidiagonalTupleGridWindow
                (gridBase (I := I) (M := M) g₀ P x) (i' + 2)) →
          (∀ (l : ℕ) (x : M),
            riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
                ((iteratedCovGrad (I := I) g₀ p a l W).toSection x) ≤
              KW l * Combinatorics.antidiagonalTupleGridWindow
                (gridBase (I := I) (M := M) g₀ P x) (l + 2)) →
          ∀ n : ℕ,
            ‖iteratedCovGrad (I := I) g₀ p b n
                (appCcRS (I := I) (M := M) g₀ p a b Φ W)‖ ^ 2 ≤
              foldConst (E := E) 0 0 (fun i => KΦ i * shiftConst Λ (i + 1))
                  (fun l => KW l * shiftConst Λ (l + 1)) n *
                (∑ k ∈ Finset.range (n + 1), Kint k) *
                (1 + ∑ j ∈ Finset.range (n + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨Kint, hKint_nn, hint⟩ :=
    atgwCapToJet (I := I) (M := M) g₀ (Λ₁ := Real.sqrt Λ) (Real.sqrt_nonneg Λ)
  refine ⟨Kint, hKint_nn, ?_⟩
  intro P hP0 hP1 p a b Φ W KΦ KW hKΦ hKW hΦ hW n
  have hsqrt : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hΛ0
  have hcap : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Real.sqrt Λ ^ 2 := by
    intro x; rw [hsqrt]; exact hP1 x
  have hKΦ' : ∀ i, 0 ≤ KΦ i * shiftConst Λ (i + 1) :=
    fun i => mul_nonneg (hKΦ i) (shiftConst_nn hΛ0 _)
  have hKW' : ∀ l, 0 ≤ KW l * shiftConst Λ (l + 1) :=
    fun l => mul_nonneg (hKW l) (shiftConst_nn hΛ0 _)
  exact hint P hcap p b n 1 (appCcRS (I := I) (M := M) g₀ p a b Φ W) _
    (foldConst_nn (u := 0) (v := 0) hKΦ' hKW' n)
    (fun x => atgwCapArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 Φ W hKΦ hKW hΦ hW n x)

end DifferentialGeometry.Integral.Connection

end
