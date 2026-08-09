import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.GradCapAtgw
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVFEndoInsertProducers
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureRefoldMonomialFibreNormBound

/-!
# The tame currency: grid products whose constant is affine in the `∇P` cap

The capped currency of `GradCapAtgw.lean` runs the whole antidiagonal grid in
the shifted (`∇P`) base, so every tuple entry is charged to `Λ₁ = ‖∇P‖_∞` and
the resulting constants are polynomials in `Λ₁` whose degree grows with the jet
order.  For the quadratic C0 summands that is fatal: the target constant must be
**affine** in `Λ₁²` (one power of `‖T‖²_{H³}`), not a growing power.

This module supplies the currency in which that is possible.  The mechanism is
the classical Moser/Gagliardo–Nirenberg tame split: measure a single `∇P` factor
in `L^∞` (one power of `Λ₁`) and interpolate every remaining factor at the
*fixed* `δ`-anchor `‖P‖_∞ ≤ 1`, where the interpolation constant no longer sees
the state.

* `gridIntUnit` — the **state-free** per-antidiagonal grid-product integral.  It
  is `grid_prod_int_le` with the order-zero cap normalized to `Λ₀ ≤ 1`: the
  workhorse constant `(max Λ₀ (max C 1))^{7i}` then collapses to `(max C 1)^{7i}`,
  which depends on the background metric and the order alone.  Unlike
  `atgGridIntRs` the top jet is kept as a bare `‖∇ⁱP‖²` with no additive `1`,
  which is what lets a rescaling be undone without creating a `Λ₁⁴` term.
* `gridIntTwo` — the two-factor specialization, the shape every Leibniz product
  node actually produces.
* `gridIntGrad` — **the quadratic tame product**.  For `c₁ + c₂ = i + 2` with
  `c₁, c₂ ≥ 1`,
  `∫ |∇^{c₁}P|²·|∇^{c₂}P|² ≤ K i · (1 + Λ₁²) · ‖∇^{i+1}P‖²`,
  with `K` state-free.  This is the first estimate in the tree in which a
  product of two once-differentiated arms lands inside the `range (i+2)` budget
  at a constant that is affine — not a growing power — in the `∇P` cap.  The
  proof rescales `∇P` by `max Λ₁ 1` to normalize its sup to `1`, applies
  `gridIntUnit` in the shifted base at total order `i`, and undoes the rescaling;
  the two orders `i ≤ 1`, where the shifted grid has no room, are closed by
  `intCapMul` instead.
* `gradCapLin` — the `∇P` cap with its `H³` dependence kept **explicit**:
  `|∇T|²(x) ≤ c · ∑_{j<3} ‖∇^{1+j}T‖²`, `c` a constant of the background alone.
  `gradCapOfJets` hides that dependence inside an existential over a fixed
  radius, which is exactly why the capped currency could not exhibit its own
  degree; this is the form in which `Λ₁²` may be replaced by `c‖T‖²_{H³}`.
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

/-! ### Continuity and integrability of fibre-norm products -/

set_option linter.unusedSectionVars false in
private theorem contRfns (g₀ : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g₀ r s) :
    Continuous (fun x : M => riemannianFiberNormSq (I := I) (M := M) g₀ r s x
      (S.toSection x)) := by
  have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M) S
  refine hc.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ r s x
      (S.toSection x),
    ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M) S x]

/-- **The `L^∞`-capped factor comes out of a fibre-norm product integral.**

If the fibre norm of `A` is bounded by `Λ` everywhere, then the integral of
`|A|²·|B|²` is at most `Λ²‖B‖²_{L²}`.  This is the degenerate (`no interpolation
needed`) end of the tame split, used at the two orders where the shifted grid is
too short to carry a two-factor tuple. -/
private theorem intCapMul (g₀ : SmoothRiemannianMetric I M) {r s t : ℕ}
    (A : SmoothCcTensor g₀ r s) (B : SmoothCcTensor g₀ r t) {Λ : ℝ}
    (hA : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x
      (A.toSection x) ≤ Λ ^ 2) :
    (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (A.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ r t x (B.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ Λ ^ 2 * ‖B‖ ^ 2 := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hBint : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ r t x (B.toSection x)) μ := by
    rw [hμ]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ r t B
  have hprod : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ r s x (A.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ r t x (B.toSection x)) μ :=
    ((contRfns (I := I) (M := M) g₀ A).mul
      (contRfns (I := I) (M := M) g₀ B)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmono : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (A.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ r t x (B.toSection x) ∂μ) ≤
      ∫ x, Λ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ r t x (B.toSection x) ∂μ := by
    refine MeasureTheory.integral_mono hprod (hBint.const_mul _) (fun x => ?_)
    exact mul_le_mul_of_nonneg_right (hA x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ r t x _)
  refine hmono.trans ?_
  rw [MeasureTheory.integral_const_mul]
  have hnorm : ‖B‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r t x (B.toSection x) ∂μ := by
    rw [SmoothCcTensor.norm_def, hμ]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r t B
  rw [hnorm]

/-- **Scaling of the `L²` norm of a smooth compactly supported tensor.**

`SmoothCcTensor` carries a seminorm but no `NormedSpace` instance, so the
scaling law is proved through the fibre-norm integral. -/
private theorem normSqSmul (g₀ : SmoothRiemannianMetric I M) {r s : ℕ} (c : ℝ)
    (S : SmoothCcTensor g₀ r s) :
    ‖(c • S : SmoothCcTensor g₀ r s)‖ ^ 2 = c ^ 2 * ‖S‖ ^ 2 := by
  classical
  have h1 : ‖(c • S : SmoothCcTensor g₀ r s)‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((c • S).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r s _
  have h2 : ‖S‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (S.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r s S
  rw [h1, h2, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  dsimp only
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    riemannianFiberNormSq_smul (I := I) (M := M) g₀ r s x c _]

/-! ### The state-free grid-product integral -/

/-- **The per-antidiagonal grid-product integral at a unit order-zero cap.**

For a tensor whose fibre norm is bounded by `Λ₀ ≤ 1` and any tuple of orders
summing to `i`, the integral of the product of the corresponding fibre-norm
squares is at most `K i · ‖∇ⁱP‖²_{L²}` with `K` depending on the background
metric and the order only — **not** on the state.

This is `grid_prod_int_le` with the cap normalized: its workhorse constant is
`(max Λ₀ (max C 1))^{7i}`, and `Λ₀ ≤ 1 ≤ max C 1` collapses the outer maximum.
The top jet is kept bare (no additive `1`), which is what makes the constant
survive a rescaling of the base tensor. -/
theorem gridIntUnit (g₀ : SmoothRiemannianMetric I M) (rb sb : ℕ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ rb sb) {Λ₀ : ℝ}, 0 ≤ Λ₀ → Λ₀ ≤ 1 →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ rb sb x
          (P.toSection x) ≤ Λ₀ ^ 2) →
        ∀ (i : ℕ), 1 ≤ i → ∀ (n : ℕ), n ≤ i → ∀ (e : Fin n → ℕ), (∑ m, e m) = i →
          (∫ x, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ rb (sb + e m) x
                  ((iteratedCovGrad (I := I) g₀ rb sb (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            K i * ‖iteratedCovGrad (I := I) g₀ rb sb i P‖ ^ 2 := by
  classical
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ rb sb k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ rb sb k h).choose_spec.1
    · exact le_refl 0
  refine ⟨fun i => (i : ℝ) * (max (Cgn i) 1) ^ (7 * i), ?_, ?_⟩
  · intro i
    refine mul_nonneg (Nat.cast_nonneg i) (pow_nonneg ?_ _)
    exact le_trans zero_le_one (le_max_right _ _)
  · intro P Λ₀ hΛ₀0 hΛ₀1 hsup i hi1 n hn e he
    have hC_nn : 0 ≤ Cgn i := hCgn_nn i
    have hGN := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
      (I := I) (M := M) g₀ rb sb i hi1).choose_spec.2 P Λ₀ hΛ₀0 hsup
    have hCeq : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ rb sb i hi1).choose = Cgn i := by
      simp only [hCgn, dif_pos hi1]
    rw [hCeq] at hGN
    have hmain := grid_prod_int_le (I := I) (M := M) g₀ P
      (R := ‖iteratedCovGrad (I := I) g₀ rb sb i P‖) (norm_nonneg _) i hi1 hΛ₀0 hsup
      (le_refl _) hC_nn hGN n hn e he
    refine hmain.2.trans ?_
    have hmax : max Λ₀ (max (Cgn i) 1) = max (Cgn i) 1 :=
      max_eq_right (le_trans hΛ₀1 (le_max_right _ _))
    rw [hmax]

/-- **Two-factor specialization of `gridIntUnit`.**

The shape every Leibniz product node produces: two covariant gradients whose
orders sum to `i`, integrated against each other. -/
theorem gridIntTwo (g₀ : SmoothRiemannianMetric I M) (rb sb : ℕ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ rb sb) {Λ₀ : ℝ}, 0 ≤ Λ₀ → Λ₀ ≤ 1 →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ rb sb x
          (P.toSection x) ≤ Λ₀ ^ 2) →
        ∀ (i d₁ d₂ : ℕ), 2 ≤ i → d₁ + d₂ = i →
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ rb (sb + d₁) x
                  ((iteratedCovGrad (I := I) g₀ rb sb d₁ P).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ rb (sb + d₂) x
                  ((iteratedCovGrad (I := I) g₀ rb sb d₂ P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            K i * ‖iteratedCovGrad (I := I) g₀ rb sb i P‖ ^ 2 := by
  classical
  obtain ⟨K, hK_nn, hK⟩ := gridIntUnit (I := I) (M := M) g₀ rb sb
  refine ⟨K, hK_nn, ?_⟩
  intro P Λ₀ hΛ₀0 hΛ₀1 hsup i d₁ d₂ hi2 hd
  have hi1 : 1 ≤ i := by omega
  have h := hK P hΛ₀0 hΛ₀1 hsup i hi1 2 hi2 ![d₁, d₂] (by
    rw [Fin.sum_univ_two]; exact hd)
  refine le_trans (le_of_eq ?_) h
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  dsimp only
  rw [Fin.prod_univ_two]
  rfl

/-! ### The quadratic tame product -/

/-- **The quadratic tame product: a constant affine in the `∇P` cap.**

For orders `c₁, c₂ ≥ 1` with `c₁ + c₂ = k + 1`,
```
∫ |∇^{c₁}P|² · |∇^{c₂}P|²  ≤  K k · (1 + Λ₁²) · ‖∇ᵏP‖²_{L²},
```
where `Λ₁` is any pointwise bound for `|∇P|` and `K` is a constant of the
background metric and the order alone.  A per-order arm window at order `i` feeds
this at `k = i + 1`, i.e. inside the `range (i + 2)` budget.

This is the estimate the capped-grid currency cannot produce.  There, a product
of two once-differentiated arms is read in the shifted base, every tuple entry is
charged to `Λ₁`, and the constant becomes a polynomial in `Λ₁` whose degree grows
with the order.  Here exactly **one** power of `Λ₁²` appears.

The proof normalizes: with `Λ := max Λ₁ 1`, the rescaled gradient `Λ⁻¹ • ∇P` has
unit sup, so `gridIntUnit` applies in the shifted base at total order
`(c₁ - 1) + (c₂ - 1) = k - 1` with a state-free constant; undoing the rescaling
multiplies by `Λ⁴` on the left and `Λ⁻²` on the right, leaving a single `Λ²`,
and `Λ² ≤ 1 + Λ₁²`.  The two short orders `k ≤ 2` force `min (c₁, c₂) = 1`, where
the capped factor may simply be pulled out (`intCapMul`). -/
theorem gridIntGrad (g₀ : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ k, 0 ≤ K k) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2) {Λ₁ : ℝ}, 0 ≤ Λ₁ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2) →
        ∀ (k c₁ c₂ : ℕ), 1 ≤ c₁ → 1 ≤ c₂ → c₁ + c₂ = k + 1 →
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + c₁) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 c₁ P).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + c₂) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 c₂ P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            K k * (1 + Λ₁ ^ 2) * ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2 := by
  classical
  obtain ⟨K2, hK2_nn, h2⟩ := gridIntTwo (I := I) (M := M) g₀ 0 (2 + 1)
  refine ⟨fun k => max (K2 (k - 1)) 1, fun k => le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro P Λ₁ hΛ₁0 hcap k c₁ c₂ hc₁ hc₂ hsum
  obtain ⟨m, rfl⟩ : ∃ m, k = 1 + m := ⟨k - 1, by omega⟩
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  set Rtop : ℝ := ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + m) P‖ with hRtop
  have hRtop_nn : (0 : ℝ) ≤ Rtop ^ 2 := sq_nonneg _
  have hKidx : (1 + m) - 1 = m := by omega
  have hK2m_nn : 0 ≤ K2 m := hK2_nn m
  have hΛsq_nn : (0 : ℝ) ≤ Λ₁ ^ 2 := sq_nonneg _
  simp only [hKidx]
  have hKmax : K2 m ≤ max (K2 m) 1 := le_max_left _ _
  have hone_le : (1 : ℝ) ≤ max (K2 m) 1 := le_max_right _ _
  by_cases hm2 : 2 ≤ m
  · -- the shifted grid has room: rescale `∇P` to unit sup
    set Λ : ℝ := max Λ₁ 1 with hΛdef
    have hΛ1 : (1 : ℝ) ≤ Λ := le_max_right _ _
    have hΛ_pos : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hΛ1
    have hΛ_ne : Λ ≠ 0 := ne_of_gt hΛ_pos
    set u : SmoothCcTensor g₀ 0 (2 + 1) := iteratedCovGrad (I := I) g₀ 0 2 1 P with hu
    set v : SmoothCcTensor g₀ 0 (2 + 1) := (Λ⁻¹ : ℝ) • u with hv
    -- the rescaled gradient has unit sup
    have hvsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
        (v.toSection x) ≤ (1 : ℝ) ^ 2 := by
      intro x
      have hsm : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x (v.toSection x) =
          (Λ⁻¹) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
            (u.toSection x) := by
        rw [hv, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
          riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (2 + 1) x (Λ⁻¹) _]
      rw [hsm]
      have hcapx : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x (u.toSection x) ≤
          Λ ^ 2 := by
        refine le_trans (hcap x) ?_
        have hle : Λ₁ ≤ Λ := le_max_left _ _
        nlinarith [hΛ₁0, hle, hΛ1]
      have hinv_nn : (0 : ℝ) ≤ (Λ⁻¹) ^ 2 := sq_nonneg _
      have hmul : (Λ⁻¹) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          (u.toSection x) ≤ (Λ⁻¹) ^ 2 * Λ ^ 2 :=
        mul_le_mul_of_nonneg_left hcapx hinv_nn
      refine hmul.trans (le_of_eq ?_)
      field_simp
    -- the rescaled jets, in the form that undoes the rescaling by `ring`
    have hjet : ∀ (d : ℕ) (x : M),
        Λ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 1) + d) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 1) d v).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + d)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (1 + d) P).toSection x) := by
      intro d x
      rw [hv, iteratedCovGrad_smul_real (I := I) (M := M) g₀ 0 (2 + 1) d (Λ⁻¹) u,
        SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
        riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 ((2 + 1) + d) x (Λ⁻¹) _, hu,
        rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 1 d P x]
      field_simp
    -- the top jet of the rescaled gradient
    have htop : Λ ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 (2 + 1) m v‖ ^ 2 = Rtop ^ 2 := by
      rw [hv, iteratedCovGrad_smul_real (I := I) (M := M) g₀ 0 (2 + 1) m (Λ⁻¹) u,
        normSqSmul (I := I) (M := M) g₀ (Λ⁻¹) _, hu,
        icgNormComp (I := I) (M := M) g₀ 0 2 1 m P, ← hRtop]
      field_simp
    -- the two orders, shifted
    obtain ⟨d₁, rfl⟩ : ∃ d, c₁ = 1 + d := ⟨c₁ - 1, by omega⟩
    obtain ⟨d₂, rfl⟩ : ∃ d, c₂ = 1 + d := ⟨c₂ - 1, by omega⟩
    have hdsum : d₁ + d₂ = m := by omega
    have hgrid := h2 v (Λ₀ := 1) zero_le_one (le_refl 1) hvsup m d₁ d₂ hm2 hdsum
    -- undo the rescaling
    have hlhs : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + d₁)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (1 + d₁) P).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + d₂)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (1 + d₂) P).toSection x) ∂μ) =
        Λ ^ 4 * ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 1) + d₁) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + 1) d₁ v).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 1) + d₂) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + 1) d₂ v).toSection x) ∂μ := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      dsimp only
      rw [← hjet d₁ x, ← hjet d₂ x]
      ring
    rw [hlhs]
    have hΛ4_nn : (0 : ℝ) ≤ Λ ^ 4 := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hgrid hΛ4_nn) ?_
    have hcollapse : Λ ^ 4 * (K2 m * ‖iteratedCovGrad (I := I) g₀ 0 (2 + 1) m v‖ ^ 2) =
        K2 m * (Λ ^ 2 * (Λ ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 (2 + 1) m v‖ ^ 2)) := by
      ring
    rw [hcollapse, htop]
    have hΛsq : Λ ^ 2 ≤ 1 + Λ₁ ^ 2 := by
      rcases le_total Λ₁ 1 with h | h
      · have hL : Λ = 1 := max_eq_right h
        rw [hL]; nlinarith [hΛsq_nn]
      · have hL : Λ = Λ₁ := max_eq_left h
        rw [hL]; nlinarith
    have hstep : K2 m * (Λ ^ 2 * Rtop ^ 2) ≤ K2 m * ((1 + Λ₁ ^ 2) * Rtop ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΛsq hRtop_nn) hK2m_nn
    refine hstep.trans ?_
    have hpos : (0 : ℝ) ≤ (1 + Λ₁ ^ 2) * Rtop ^ 2 :=
      mul_nonneg (by linarith [hΛsq_nn]) hRtop_nn
    nlinarith [mul_le_mul_of_nonneg_right hKmax hpos]
  · -- `m ≤ 1`: one of the two orders is `1`, and the cap comes out directly
    have hcase : c₁ = 1 ∧ c₂ = 1 + m ∨ c₂ = 1 ∧ c₁ = 1 + m := by omega
    have hpos : (0 : ℝ) ≤ (1 + Λ₁ ^ 2) * Rtop ^ 2 :=
      mul_nonneg (by linarith [hΛsq_nn]) hRtop_nn
    have hfin : Λ₁ ^ 2 * Rtop ^ 2 ≤ max (K2 m) 1 * (1 + Λ₁ ^ 2) * Rtop ^ 2 := by
      calc Λ₁ ^ 2 * Rtop ^ 2 ≤ (1 + Λ₁ ^ 2) * Rtop ^ 2 :=
            mul_le_mul_of_nonneg_right (by linarith) hRtop_nn
        _ ≤ max (K2 m) 1 * ((1 + Λ₁ ^ 2) * Rtop ^ 2) := le_mul_of_one_le_left hpos hone_le
        _ = max (K2 m) 1 * (1 + Λ₁ ^ 2) * Rtop ^ 2 := by ring
    rcases hcase with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · subst h1; subst h2'
      exact le_trans (intCapMul (I := I) (M := M) g₀
        (iteratedCovGrad (I := I) g₀ 0 2 1 P)
        (iteratedCovGrad (I := I) g₀ 0 2 (1 + m) P) hcap) hfin
    · subst h1; subst h2'
      have hcomm : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + m)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (1 + m) P).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
              ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ∂μ) =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
                ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + m)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (1 + m) P).toSection x) ∂μ := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        ring
      rw [hcomm]
      exact le_trans (intCapMul (I := I) (M := M) g₀
        (iteratedCovGrad (I := I) g₀ 0 2 1 P)
        (iteratedCovGrad (I := I) g₀ 0 2 (1 + m) P) hcap) hfin

/-- **The tame split when the Leibniz term carries a bare `∇P` factor.**

If one factor of a product node is an undifferentiated `∇P`, it is measured in
`L^∞` — one power of `Λ₁²` — and the remaining tuple, of total order `k`, is
integrated at the state's own δ-anchor with a state-free constant:
```
∫ |∇P|² · ∏_m |∇^{e_m}P|²  ≤  Λ₁² · K k · ‖∇ᵏP‖²_{L²}   (∑ e_m = k).
```

Together with `gridIntGrad` this covers every Leibniz term of a quadratic C0 arm
except those in which **all** factors carry at least two derivatives and there
are at least three of them (which first occurs at jet order `4`); see
`TameGridProd.md`. -/
theorem gridIntPull (g₀ : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ k, 0 ≤ K k) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2) {Λ₀ Λ₁ : ℝ}, 0 ≤ Λ₀ → Λ₀ ≤ 1 →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2) →
        ∀ (k : ℕ), 1 ≤ k → ∀ (n : ℕ), n ≤ k → ∀ (e : Fin n → ℕ), (∑ m, e m) = k →
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) *
                ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            Λ₁ ^ 2 * (K k * ‖iteratedCovGrad (I := I) g₀ 0 2 k P‖ ^ 2) := by
  classical
  obtain ⟨K, hK_nn, hK⟩ := gridIntUnit (I := I) (M := M) g₀ 0 2
  refine ⟨K, hK_nn, ?_⟩
  intro P Λ₀ Λ₁ hΛ₀0 hΛ₀1 hsup hcap k hk1 n hn e he
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  have hGcont : Continuous (fun x : M => ∏ m : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) :=
    continuous_finset_prod _ (fun m _ => contRfns (I := I) (M := M) g₀ _)
  have hGint : MeasureTheory.Integrable (fun x : M => ∏ m : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    hGcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPint : MeasureTheory.Integrable (fun x : M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) *
        ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    ((contRfns (I := I) (M := M) g₀ _).mul hGcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmono := MeasureTheory.integral_mono hPint (hGint.const_mul (Λ₁ ^ 2)) (fun x => by
    exact mul_le_mul_of_nonneg_right (hcap x)
      (Finset.prod_nonneg (fun m _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e m) x _)))
  rw [MeasureTheory.integral_const_mul] at hmono
  refine hmono.trans ?_
  exact mul_le_mul_of_nonneg_left (hK P hΛ₀0 hΛ₀1 hsup k hk1 n hn e he) (sq_nonneg Λ₁)

/-! ### The `∇P` cap with its `H³` dependence explicit -/

/-- **The `∇P` cap, stated linearly in the state's own jets.**

In dimension three the first covariant gradient of a `(0,2)` state is bounded
pointwise by the state's covariant `L²` jets through order three:
```
|∇T|²(x)  ≤  c · ∑_{j < 3} ‖∇^{1+j}T‖²_{L²} ,
```
with `c` a constant of the background metric alone.

`gradCapOfJets` is the same fibre embedding with the jet sum replaced by a fixed
radius `R₀` *before* the constant is chosen, so the `H³` dependence disappears
inside an existential; that is precisely why the capped currency cannot exhibit
its own degree in `‖T‖_{H³}`.  Here the dependence is kept explicit, which is
what turns the `Λ₁²` of `gridIntGrad` into `c‖T‖²_{H³}` and produces the
`K₀ + K₂‖T‖²_{H³}` shape. -/
theorem gradCapLin (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (T : SmoothCcTensor g₀ 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
            ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) ≤
          c * ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) T‖ ^ 2 := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g₀ 0 (2 + 1)
  have hw : Module.finrank ℝ E / 2 + 2 = 3 := by omega
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro T x
  refine le_trans (hC (iteratedCovGrad (I := I) g₀ 0 2 1 T) x) ?_
  rw [hw]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (sq_nonneg C)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [icgNormComp (I := I) (M := M) g₀ 0 2 1 j T]

end DifferentialGeometry.Integral.Connection

end

