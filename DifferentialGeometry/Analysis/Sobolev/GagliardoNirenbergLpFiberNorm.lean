import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.CovGradBundleEquivFiberNormFrameSum
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradCrossBridge

/-! # The Lᵖ-fibre-norm Gagliardo–Nirenberg interpolation for iterated covariant gradients

This file isolates the **Lᵖ-form** of the closed-manifold tensor Gagliardo–Nirenberg interpolation
(Hamilton, *Three-manifolds with positive Ricci curvature* §12.5; Aubin): for a smooth
compactly-supported `(0, s)`-tensor `u` with `C⁰`-sup fibre bound `Λ₀`, a top order `k ≥ 1`, and an
intermediate order `0 < j < k`, the `L^{2k/j}` fibre norm of the `j`-th iterated covariant gradient
is controlled by the interpolated product of the `L^∞` sup and the top-order covariant `L²`-jet:
```
‖∇^j u‖_{L^{2k/j}}^2 ≤ C · Λ₀^{2(1 − j/k)} · ‖∇^k u‖_{L²}^{2 j/k} .
```
Equivalently, in the squared-fibre-norm integral form used by the diagonal-product-grid consumer,
```
(∫ rfns(∇^j u)^{k/j} dμ)^{j/k} ≤ C · Λ₀^{2(1 − j/k)} · ‖∇^k u‖_{L²}^{2 j/k} ,
```
the left member being `‖∇^j u‖²_{L^{2k/j}}` (the `L^{2k/j}` norm of the *pointwise fibre norm*
`|∇^j u|`, raised to the second power and written through the squared fibre norm
`rfns(∇^j u) = |∇^j u|²`).

The companion `L²`-form already on disk
(`exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le`, `Analysis/Sobolev/MoserTameProduct.lean`)
is the *degenerate* `p = 2` case `j = k - 1` collapsed to the `L²` left member, and does **not**
imply this `L^{2k/j}` form: the diagonal-product-grid two-arm estimate
(`Analysis/Spectral/Tensor/CovGrad/GagliardoNirenbergProductTwoArm.lean`) integrates each pointwise
product `rfns(∇^i S)·rfns(∇^l T)` via Hölder at the conjugate pair `(k/i, k/l)`, which requires the
*genuine `L^{2k/i}` interpolation* of each factor — exactly the left member here, with a free
`L^p` exponent that the `L²`-form's fixed `L²` left member cannot supply.  This file is therefore
the precise Lᵖ-interpolation kernel the product grid consumes.

The deep analytic content is now isolated in a **single** posited single-tensor input — the
sub-unit-exponent `Lᵖ` log-convexity `lpFiberJet_secondOrder_subunit_logConvex_bound` (the genuine
`Lᵖ` Lyapunov / log-convexity frontier in the regime `k ≤ i + 1`, where covariant IBP is no longer
available).  Everything else is proven outright: the **second-order covariant `L^p` interpolation
step** `secondOrderInterp_lpFiberJet_fin` (`‖∇w‖_{L^{2k/(i+1)}}² ≤ K'·‖w‖_{L^{2k/i}}·‖∇²w‖_{L^{2k/(i+2)}}`)
and its order-`0` `L^∞`-lower-factor form `secondOrderInterp_lpFiberJet_sup` are glue over the genuine
covariant integration-by-parts engine `weightedCovIBP_lpFiberJet_fin` (proven — the regularised weighted
IBP against `(|∇w|²+ε)^{(p-2)/2}` in the `ε → 0` limit) plus three-function Hölder, in the standard
regime, and the log-convexity in the sub-unit regime.  Mathlib carries only the first-order Sobolev
*embedding* `eLpNorm_le_eLpNorm_fderiv`, not this iterated-jet interpolation, and no `L^p` Lyapunov
interpolation.
On top of those two steps the **single-step log-convexity** `lpFiberJet_logConvex_iteratedCovGrad`
(`c_{i+1}² ≤ K·c_i·c_{i+2}` for the mixed-`L^p` fibre jets `c_i := ‖|∇^i u|‖_{L^{2k/i}}`,
`c_0 := Λ₀·√(vol M)`, `c_k := ‖∇^k u‖_{L²}`) is proven outright — by reading the ladder as the honest
jet for `i ≥ 1` (`i = k` via the `L²` bridge), the `iteratedCovGrad_succ` identification
`covGrad(∇^i u) = ∇^{i+1}u`, the `L^∞`-endpoint comparison, and the constant absorption.  The
headline is then assembled by the discrete Hardy–Littlewood–Pólya power law `lp_hlp_real` (proven
here as elementary real arithmetic on the abstract jets) and a single `rpow` extraction — mirroring
the `L²`-companion's `l2Interp_pow_iteratedCovGrad` architecture but carrying the genuinely stronger
`L^{2k/j}` left member.  Consumers transitively depend on the `sorryAx` of the single posited
sub-unit `Lᵖ` log-convexity `lpFiberJet_secondOrder_subunit_logConvex_bound`. -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Tensor

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section SecondOrderInterpInfra

set_option linter.unusedSectionVars false in
/-- Continuity of `x ↦ rfns(S)(x)` for a smooth compactly-supported tensor section, read
through the fibre-norm bridge `riemannianFiberNormSq = tensorInnerPointwise (·,·)` and the
continuity of the diagonal pointwise inner product on smooth sections. -/
private theorem continuous_rfns_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Integral.L2.SmoothCcTensor g r s) :
    Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) := by
  have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M) S
  refine hc.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (S.toSection x),
    ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M) S x]

set_option linter.unusedSectionVars false in
/-- `MemLp` of `x ↦ rfns(S)(x) ^ a` for any nonnegative exponent `a`, on a closed manifold: a
continuous compactly-supported function on a compact space lies in every `Lᵖ`. -/
private theorem memLp_rfns_rpow
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Integral.L2.SmoothCcTensor g r s) (a : ℝ) (ha : 0 ≤ a) (p : ℝ≥0∞) :
    MeasureTheory.MemLp
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) ^ a) p
      (Integral.Measure.riemannianVolumeMeasure I M g) := by
  haveI : MeasureTheory.IsFiniteMeasure (Integral.Measure.riemannianVolumeMeasure I M g) :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hcont : Continuous
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) ^ a) :=
    (continuous_rfns_section (I := I) (M := M) g r s S).rpow_const (fun _ => Or.inr ha)
  exact hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

set_option linter.unusedSectionVars false in
/-- **Three-function Hölder for nonnegative continuous functions** on the (finite) Riemannian
volume of a closed manifold, in integral form: for `α⁻¹ + β⁻¹ + γ⁻¹ = 1` with all positive,
```
∫ f₁·f₂·f₃ ≤ (∫ f₁^α)^{1/α} · (∫ f₂^β)^{1/β} · (∫ f₃^γ)^{1/γ},
```
obtained by two applications of the two-function Hölder
`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`.  The first split is `f₁·(f₂·f₃)` at the
conjugate pair `(α, α')` with `α' := (β⁻¹ + γ⁻¹)⁻¹`; the inner split is `f₂^{α'}·f₃^{α'}` at the
conjugate pair `(β/α', γ/α')`. -/
private theorem real_holder_three_nonneg
    (g : SmoothRiemannianMetric I M) (f₁ f₂ f₃ : M → ℝ)
    (hf₁c : Continuous f₁) (hf₂c : Continuous f₂) (hf₃c : Continuous f₃)
    (hf₁0 : ∀ x, 0 ≤ f₁ x) (hf₂0 : ∀ x, 0 ≤ f₂ x) (hf₃0 : ∀ x, 0 ≤ f₃ x)
    {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hABC : α⁻¹ + β⁻¹ + γ⁻¹ = 1) :
    ∫ x, f₁ x * f₂ x * f₃ x ∂(Integral.Measure.riemannianVolumeMeasure I M g) ≤
      (∫ x, f₁ x ^ α ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ (1 / α) *
        ((∫ x, f₂ x ^ β ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ (1 / β) *
          (∫ x, f₃ x ^ γ ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ (1 / γ)) := by
  classical
  set μ : MeasureTheory.Measure M := Integral.Measure.riemannianVolumeMeasure I M g with hμ
  haveI : MeasureTheory.IsFiniteMeasure μ :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  -- The intermediate conjugate exponent `α' = (β⁻¹+γ⁻¹)⁻¹`, conjugate to `α`.
  set α' : ℝ := (β⁻¹ + γ⁻¹)⁻¹ with hα'def
  have hβγpos : 0 < β⁻¹ + γ⁻¹ := by positivity
  have hα'pos : 0 < α' := by rw [hα'def]; positivity
  have hα'inv : α'⁻¹ = β⁻¹ + γ⁻¹ := by rw [hα'def, inv_inv]
  have hγinv_pos : (0 : ℝ) < γ⁻¹ := by positivity
  have hβinv_pos : (0 : ℝ) < β⁻¹ := by positivity
  -- `α` and `α'` are Hölder conjugate: `α⁻¹ + α'⁻¹ = 1`.
  have hconj1 : α.HolderConjugate α' := by
    refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
    · -- `1 < α`: from `α⁻¹ = 1 - (β⁻¹+γ⁻¹) < 1` and `0 < α`.
      have hαinv_lt : α⁻¹ < 1 := by
        have hαeq : α⁻¹ = 1 - (β⁻¹ + γ⁻¹) := by linarith [hABC]
        rw [hαeq]; linarith [hβγpos]
      have hαinv_pos : (0 : ℝ) < α⁻¹ := by positivity
      rw [← inv_inv α]
      exact one_lt_inv_iff₀.mpr ⟨hαinv_pos, hαinv_lt⟩
    · rw [hα'inv]; linarith [hABC]
  -- The product `f₂·f₃` is nonnegative and continuous (hence in every Lᵖ).
  have hf23_0 : ∀ x, 0 ≤ f₂ x * f₃ x := fun x => mul_nonneg (hf₂0 x) (hf₃0 x)
  have hf1_mem : MeasureTheory.MemLp f₁ (ENNReal.ofReal α) μ :=
    hf₁c.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf23_mem : MeasureTheory.MemLp (fun x => f₂ x * f₃ x) (ENNReal.ofReal α') μ :=
    (hf₂c.mul hf₃c).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- First Hölder split: `∫ f₁·(f₂f₃) ≤ (∫f₁^α)^{1/α}·(∫(f₂f₃)^{α'})^{1/α'}`.
  have hstep1 := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hconj1
    (f := f₁) (g := fun x => f₂ x * f₃ x)
    (MeasureTheory.ae_of_all _ hf₁0) (MeasureTheory.ae_of_all _ hf23_0) hf1_mem hf23_mem
  -- The inner conjugate pair `(β/α', γ/α')`.
  have hβα' : 0 < β / α' := by positivity
  have hγα' : 0 < γ / α' := by positivity
  have hf2α'_mem : MeasureTheory.MemLp (fun x => f₂ x ^ α') (ENNReal.ofReal (β / α')) μ :=
    ((hf₂c.rpow_const (fun _ => Or.inr hα'pos.le)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hf3α'_mem : MeasureTheory.MemLp (fun x => f₃ x ^ α') (ENNReal.ofReal (γ / α')) μ :=
    ((hf₃c.rpow_const (fun _ => Or.inr hα'pos.le)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hα'ne : α' ≠ 0 := ne_of_gt hα'pos
  have hconj2 : (β / α').HolderConjugate (γ / α') := by
    refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
    · -- `1 < β/α'`: equivalently `α' < β`, from `β⁻¹ < β⁻¹+γ⁻¹ = α'⁻¹`.
      rw [one_lt_div hα'pos]
      have hlt : β⁻¹ < α'⁻¹ := by rw [hα'inv]; linarith [hγinv_pos]
      exact (inv_lt_inv₀ hβ hα'pos).mp hlt
    · -- `(β/α')⁻¹ + (γ/α')⁻¹ = α'/β + α'/γ = α'·(β⁻¹+γ⁻¹) = α'·α'⁻¹ = 1`.
      have hsplit : α' / β + α' / γ = α' * (β⁻¹ + γ⁻¹) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_add]
      rw [inv_div, inv_div, hsplit, ← hα'inv, mul_inv_cancel₀ hα'ne]
  -- Second Hölder split on `f₂^{α'}·f₃^{α'}` at `(β/α', γ/α')`.
  have hstep2 := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hconj2
    (f := fun x => f₂ x ^ α') (g := fun x => f₃ x ^ α')
    (MeasureTheory.ae_of_all _ (fun x => Real.rpow_nonneg (hf₂0 x) _))
    (MeasureTheory.ae_of_all _ (fun x => Real.rpow_nonneg (hf₃0 x) _)) hf2α'_mem hf3α'_mem
  -- Identify `(f₂f₃)^{α'} = f₂^{α'}·f₃^{α'}` (nonneg bases) so the two splits chain.
  have hprod_rpow : ∀ x, (f₂ x * f₃ x) ^ α' = f₂ x ^ α' * f₃ x ^ α' :=
    fun x => Real.mul_rpow (hf₂0 x) (hf₃0 x)
  -- `(f₂^{α'})^{β/α'} = f₂^β`, `(f₃^{α'})^{γ/α'} = f₃^γ`.
  have hmulcancel : ∀ t : ℝ, α' * (t / α') = t := by
    intro t; rw [mul_comm, div_mul_cancel₀ t hα'ne]
  have hpow2 : ∀ x, (f₂ x ^ α') ^ (β / α') = f₂ x ^ β := by
    intro x
    rw [← Real.rpow_mul (hf₂0 x), hmulcancel]
  have hpow3 : ∀ x, (f₃ x ^ α') ^ (γ / α') = f₃ x ^ γ := by
    intro x
    rw [← Real.rpow_mul (hf₃0 x), hmulcancel]
  -- Rewrite the integrals in `hstep2`.
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpow2),
      MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpow3)] at hstep2
  -- The intermediate factor: `(∫ (f₂f₃)^{α'})^{1/α'} ≤ (∫f₂^β)^{1/β}·(∫f₃^γ)^{1/γ}`.
  set Iβ : ℝ := ∫ x, f₂ x ^ β ∂μ with hIβ
  set Iγ : ℝ := ∫ x, f₃ x ^ γ ∂μ with hIγ
  have hIβ_nn : 0 ≤ Iβ := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hf₂0 x) _)
  have hIγ_nn : 0 ≤ Iγ := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hf₃0 x) _)
  have hI23 : (∫ x, (f₂ x * f₃ x) ^ α' ∂μ) = ∫ x, f₂ x ^ α' * f₃ x ^ α' ∂μ :=
    MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hprod_rpow)
  have hmid : (∫ x, (f₂ x * f₃ x) ^ α' ∂μ) ^ (1 / α') ≤ Iβ ^ (1 / β) * Iγ ^ (1 / γ) := by
    rw [hI23]
    have hbase_nn : 0 ≤ ∫ x, f₂ x ^ α' * f₃ x ^ α' ∂μ :=
      MeasureTheory.integral_nonneg (fun x =>
        mul_nonneg (Real.rpow_nonneg (hf₂0 x) _) (Real.rpow_nonneg (hf₃0 x) _))
    have hα'inv_pos : 0 < 1 / α' := by positivity
    calc (∫ x, f₂ x ^ α' * f₃ x ^ α' ∂μ) ^ (1 / α')
        ≤ (Iβ ^ (1 / (β / α')) * Iγ ^ (1 / (γ / α'))) ^ (1 / α') :=
          Real.rpow_le_rpow hbase_nn hstep2 (le_of_lt hα'inv_pos)
      _ = Iβ ^ (1 / β) * Iγ ^ (1 / γ) := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            ← Real.rpow_mul hIβ_nn, ← Real.rpow_mul hIγ_nn]
          have he2 : (1 / (β / α')) * (1 / α') = 1 / β := by
            rw [one_div_div]
            field_simp
          have he3 : (1 / (γ / α')) * (1 / α') = 1 / γ := by
            rw [one_div_div]
            field_simp
          rw [he2, he3]
  -- Chain the two splits.
  calc ∫ x, f₁ x * f₂ x * f₃ x ∂μ
      = ∫ x, f₁ x * (f₂ x * f₃ x) ∂μ := by
        refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ (fun x => ?_))
        ring
    _ ≤ (∫ x, f₁ x ^ α ∂μ) ^ (1 / α) * (∫ x, (f₂ x * f₃ x) ^ α' ∂μ) ^ (1 / α') := hstep1
    _ ≤ (∫ x, f₁ x ^ α ∂μ) ^ (1 / α) * (Iβ ^ (1 / β) * Iγ ^ (1 / γ)) := by
        apply mul_le_mul_of_nonneg_left hmid
        exact Real.rpow_nonneg (MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hf₁0 x) _)) _

end SecondOrderInterpInfra

section LpDiscreteLogConvex

/-- One-step "slope-defect" iterated (bounded form): if `Δ i ≤ Δ (i+1) + d` for all
`i < N`, then `Δ i ≤ Δ i' + (i'-i) * d` whenever `i ≤ i' ≤ N`.  Elementary real arithmetic. -/
private lemma lp_slope_spread (Δ : ℕ → ℝ) (d : ℝ) (N : ℕ)
    (hstep : ∀ i, i < N → Δ i ≤ Δ (i + 1) + d) :
    ∀ i i' : ℕ, i ≤ i' → i' ≤ N → Δ i ≤ Δ i' + (i' - i : ℕ) * d := by
  intro i i' hii' hiN
  induction i' with
  | zero => interval_cases i; simp
  | succ n ih =>
      rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · have hin : i ≤ n := Nat.lt_succ_iff.mp hlt
        have h1 := ih hin (by omega)
        have h2 := hstep n (by omega)
        have hbody : Δ i ≤ Δ (n + 1) + d + (n - i : ℕ) * d := by
          calc Δ i ≤ Δ n + (n - i : ℕ) * d := h1
            _ ≤ (Δ (n + 1) + d) + (n - i : ℕ) * d := by linarith
        have hcast : ((n + 1 - i : ℕ) : ℝ) = (n - i : ℕ) + 1 := by
          have hn : n + 1 - i = (n - i) + 1 := by omega
          rw [hn]; push_cast; ring
        rw [hcast]; nlinarith [hbody]
      · have hie : i = n + 1 := le_antisymm hii' hge
        subst hie; simp

/-- The discrete chord bound from a convexity defect, in additive form. If
`Δ i ≤ Δ (i+1) + d` for all `i + 1 < k` and `0 ≤ d`, then for `0 < j < k`
```
k * ∑_{i<j} Δ i ≤ j * ∑_{i<k} Δ i + k^3 * d.
```
Writing `Δ i = L (i+1) - L i` makes `∑_{i<n} Δ i = L n - L 0`, so this is exactly the
log-convex chord bound for `L`.  Elementary real arithmetic. -/
private lemma lp_chord_bound (Δ : ℕ → ℝ) (d : ℝ) (hd : 0 ≤ d) (j k : ℕ)
    (hstep : ∀ i, i + 1 < k → Δ i ≤ Δ (i + 1) + d) (hj : 0 < j) (hjk : j < k) :
    (k : ℝ) * (∑ i ∈ Finset.range j, Δ i)
      ≤ (j : ℝ) * (∑ i ∈ Finset.range k, Δ i) + (k ^ 3 : ℕ) * d := by
  have hsplit : (∑ i ∈ Finset.range k, Δ i)
      = (∑ i ∈ Finset.range j, Δ i) + ∑ i ∈ Finset.Ico j k, Δ i := by
    rw [← Finset.sum_range_add_sum_Ico Δ (le_of_lt hjk)]
  rw [hsplit, mul_add]
  set Sj : ℝ := ∑ i ∈ Finset.range j, Δ i with hSj
  set Sjk : ℝ := ∑ i ∈ Finset.Ico j k, Δ i with hSjk
  have hcard1 : (Finset.Ico j k).card = k - j := by rw [Nat.card_Ico]
  have hcard2 : (Finset.range j).card = j := by rw [Finset.card_range]
  have hLHS : ((k : ℝ) - j) * Sj = ∑ _i' ∈ Finset.Ico j k, Sj := by
    rw [Finset.sum_const, hcard1, nsmul_eq_mul]
    have hc : ((k - j : ℕ) : ℝ) = (k : ℝ) - j := by rw [Nat.cast_sub (le_of_lt hjk)]
    rw [hc]
  have hRHS : (j : ℝ) * Sjk = ∑ _i ∈ Finset.range j, Sjk := by
    rw [Finset.sum_const, hcard2, nsmul_eq_mul]
  have key : ((k : ℝ) - j) * Sj - (j : ℝ) * Sjk ≤ (k ^ 3 : ℕ) * d := by
    rw [hLHS, hRHS]
    have e1 : (∑ _i' ∈ Finset.Ico j k, Sj)
        = ∑ p ∈ (Finset.range j) ×ˢ (Finset.Ico j k), Δ p.1 := by
      rw [hSj, Finset.sum_product' (f := fun (a : ℕ) (_ : ℕ) => Δ a)]
      exact (Finset.sum_comm).symm
    have e2 : (∑ _i ∈ Finset.range j, Sjk)
        = ∑ p ∈ (Finset.range j) ×ˢ (Finset.Ico j k), Δ p.2 := by
      rw [hSjk, Finset.sum_product' (f := fun (_ : ℕ) (b : ℕ) => Δ b)]
    rw [e1, e2, ← Finset.sum_sub_distrib]
    have hbound : ∀ p ∈ (Finset.range j) ×ˢ (Finset.Ico j k),
        Δ p.1 - Δ p.2 ≤ (k : ℝ) * d := by
      intro p hp
      rw [Finset.mem_product] at hp
      obtain ⟨hp1, hp2⟩ := hp
      have hi : p.1 < j := Finset.mem_range.mp hp1
      have hi' : j ≤ p.2 := (Finset.mem_Ico.mp hp2).1
      have hi'k : p.2 < k := (Finset.mem_Ico.mp hp2).2
      have hle : p.1 ≤ p.2 := le_trans (le_of_lt hi) hi'
      have hstep' : ∀ i, i < k - 1 → Δ i ≤ Δ (i + 1) + d := fun i hik => hstep i (by omega)
      have hsp := lp_slope_spread Δ d (k - 1) hstep' p.1 p.2 hle (by omega)
      have hdiff : ((p.2 - p.1 : ℕ) : ℝ) ≤ (k : ℝ) := by
        have hpp : p.2 - p.1 ≤ k := by omega
        exact_mod_cast hpp
      have hstep2 : Δ p.1 - Δ p.2 ≤ (p.2 - p.1 : ℕ) * d := by linarith [hsp]
      calc Δ p.1 - Δ p.2 ≤ (p.2 - p.1 : ℕ) * d := hstep2
        _ ≤ (k : ℝ) * d := mul_le_mul_of_nonneg_right hdiff hd
    calc ∑ p ∈ (Finset.range j) ×ˢ (Finset.Ico j k), (Δ p.1 - Δ p.2)
        ≤ ∑ _p ∈ (Finset.range j) ×ˢ (Finset.Ico j k), (k : ℝ) * d :=
          Finset.sum_le_sum hbound
      _ = ((Finset.range j) ×ˢ (Finset.Ico j k)).card * ((k : ℝ) * d) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((j * (k - j) : ℕ) : ℝ) * ((k : ℝ) * d) := by
          rw [Finset.card_product, hcard1, hcard2]
      _ ≤ (k ^ 3 : ℕ) * d := by
          have hjk_le : j * (k - j) ≤ k * k := by
            calc j * (k - j) ≤ k * (k - j) := by apply Nat.mul_le_mul_right; omega
              _ ≤ k * k := by apply Nat.mul_le_mul_left; omega
          have hcastjk : ((j * (k - j) : ℕ) : ℝ) ≤ (k : ℝ) * (k : ℝ) := by exact_mod_cast hjk_le
          have hcast3 : ((k ^ 3 : ℕ) : ℝ) = (k : ℝ) * (k : ℝ) * (k : ℝ) := by push_cast; ring
          have hkd : 0 ≤ (k : ℝ) * d := mul_nonneg (by positivity) hd
          have hknn : (0 : ℝ) ≤ (k : ℝ) := by positivity
          rw [hcast3]
          nlinarith [hcastjk, hkd, hknn, hd, mul_le_mul_of_nonneg_right hcastjk hkd]
  nlinarith [key]

/-- Positivity propagates downward from any positive term: with all `a ≥ 0`, the
log-convexity `a (i+1)^2 ≤ M * a i * a (i+2)` forces `a (i+1) > 0 → a i > 0`, hence a
single positive `a j` makes every earlier term positive. -/
private lemma lp_pos_propagate (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (M : ℝ)
    (hlc : ∀ i, (a (i + 1)) ^ 2 ≤ M * a i * a (i + 2)) (j : ℕ) (hpos : 0 < a j) :
    ∀ i, i ≤ j → 0 < a i := by
  have hL : ∀ i, 0 < a (i + 1) → 0 < a i := by
    intro i hi
    by_contra h
    rw [not_lt] at h
    have hai : a i = 0 := le_antisymm h (ha i)
    have hh := hlc i
    rw [hai] at hh
    simp only [mul_zero, zero_mul] at hh
    nlinarith [hh, hi, sq_nonneg (a (i + 1))]
  have key0 : ∀ s, s ≤ j → 0 < a (j - s) := by
    intro s
    induction s with
    | zero => intro _; simpa using hpos
    | succ m ihm =>
        intro hs
        have hjm : 0 < a (j - m) := ihm (by omega)
        have hidx : j - m = (j - (m + 1)) + 1 := by omega
        rw [hidx] at hjm
        exact hL (j - (m + 1)) hjm
  intro i hi
  have heq : i = j - (j - i) := by omega
  rw [heq]
  exact key0 (j - i) (by omega)

/-- Positivity also propagates upward: a single positive `a j` (`0 < j`) makes every
later term positive. -/
private lemma lp_pos_propagate_up (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (M : ℝ)
    (hlc : ∀ i, (a (i + 1)) ^ 2 ≤ M * a i * a (i + 2)) (j : ℕ) (hj : 0 < j)
    (hpos : 0 < a j) :
    ∀ i, j ≤ i → 0 < a i := by
  have hR : ∀ i, 0 < a (i + 1) → 0 < a (i + 2) := by
    intro i hi
    by_contra h
    rw [not_lt] at h
    have hai : a (i + 2) = 0 := le_antisymm h (ha (i + 2))
    have hh := hlc i
    rw [hai] at hh
    simp only [mul_zero] at hh
    nlinarith [hh, hi, sq_nonneg (a (i + 1))]
  intro i hji
  obtain ⟨t, rfl⟩ : ∃ t, i = j + t := ⟨i - j, by omega⟩
  clear hji
  induction t with
  | zero => simpa using hpos
  | succ n ih =>
      have hjn : 0 < a (j + n) := ih
      have hidx : j + n = (j + n - 1) + 1 := by omega
      rw [hidx] at hjn
      have hRr := hR (j + n - 1) hjn
      have hidx2 : j + n - 1 + 2 = j + (n + 1) := by omega
      rw [hidx2] at hRr
      exact hRr

/-- **Discrete log-convexity power law (Hardy–Littlewood–Pólya, real form).** A
nonnegative sequence `a` satisfying `a (i+1)^2 ≤ M * a i * a (i+2)` with `1 ≤ M` obeys,
for `0 < j < k`,
```
(a j)^k ≤ M^(k^3) * (a 0)^(k-j) * (a k)^j.
```
The proof reduces (via the square bound) to the all-positive case, in which
`i ↦ Real.log (a i)` has a discrete second difference bounded below by `-Real.log M`; the
chord bound then yields the linear inequality on logs, which exponentiates to the claimed
power law.  Elementary real arithmetic; no `sorry`. -/
private theorem lp_hlp_real (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (M : ℝ) (hM : 1 ≤ M)
    (hlc : ∀ i, (a (i + 1)) ^ 2 ≤ M * a i * a (i + 2)) (j k : ℕ) (hj : 0 < j) (hjk : j < k) :
    (a j) ^ k ≤ M ^ (k ^ 3) * (a 0) ^ (k - j) * (a k) ^ j := by
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM
  rcases eq_or_lt_of_le (ha j) with hzero | hpos
  · rw [← hzero, zero_pow (by omega)]
    have h0 : 0 ≤ a 0 := ha 0
    have hk : 0 ≤ a k := ha k
    have hMnn : 0 ≤ M := le_of_lt hM0
    positivity
  · have hposj : 0 < a j := hpos
    have hpL : ∀ i, i ≤ j → 0 < a i := lp_pos_propagate a ha M hlc j hposj
    have hpU : ∀ i, j ≤ i → 0 < a i := lp_pos_propagate_up a ha M hlc j hj hposj
    have hpall : ∀ i, i ≤ k → 0 < a i := by
      intro i hik
      rcases Nat.lt_or_ge i j with h | h
      · exact hpL i (le_of_lt h)
      · exact hpU i h
    set L : ℕ → ℝ := fun i => Real.log (a i) with hLdef
    set Δ : ℕ → ℝ := fun i => L (i + 1) - L i with hΔdef
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
    have hstep : ∀ i, i + 1 < k → Δ i ≤ Δ (i + 1) + Real.log M := by
      intro i hik
      have hi0 : 0 < a i := hpall i (by omega)
      have hi1 : 0 < a (i + 1) := hpall (i + 1) (by omega)
      have hi2 : 0 < a (i + 2) := hpall (i + 2) (by omega)
      have hlci := hlc i
      have hlog : Real.log ((a (i + 1)) ^ 2) ≤ Real.log (M * a i * a (i + 2)) :=
        Real.log_le_log (by positivity) hlci
      rw [Real.log_pow] at hlog
      rw [Real.log_mul (by positivity) (ne_of_gt hi2),
          Real.log_mul (ne_of_gt hM0) (ne_of_gt hi0)] at hlog
      simp only [hΔdef, hLdef]
      push_cast at hlog
      nlinarith [hlog]
    have hchord := lp_chord_bound Δ (Real.log M) hlogM j k hstep hj hjk
    have htel : ∀ n, (∑ i ∈ Finset.range n, Δ i) = L n - L 0 := by
      intro n; simp only [hΔdef]; exact Finset.sum_range_sub L n
    rw [htel j, htel k] at hchord
    have hlin : (k : ℝ) * L j ≤
        ((k - j : ℕ) : ℝ) * L 0 + (j : ℝ) * L k + (k ^ 3 : ℕ) * Real.log M := by
      have hcastsub : ((k - j : ℕ) : ℝ) = (k : ℝ) - (j : ℝ) := by rw [Nat.cast_sub (le_of_lt hjk)]
      rw [hcastsub]; nlinarith [hchord]
    have hLHSpos : 0 < (a j) ^ k := by positivity
    have h0 : 0 < a 0 := hpall 0 (by omega)
    have hk : 0 < a k := hpall k (le_refl k)
    have hRHSpos : 0 < M ^ (k ^ 3) * (a 0) ^ (k - j) * (a k) ^ j := by positivity
    rw [← Real.log_le_log_iff hLHSpos hRHSpos]
    rw [Real.log_pow]
    rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
        Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity))]
    rw [Real.log_pow, Real.log_pow, Real.log_pow]
    simp only [hLdef] at hlin ⊢
    push_cast at hlin ⊢
    nlinarith [hlin]

end LpDiscreteLogConvex

/-- The mixed-`L^p` fibre-jet ladder of a smooth compactly-supported `(0, s)`-tensor `u` at top
order `k`: the value at order `i` is the `L^{2k/i}` norm of the pointwise fibre norm `|∇^i u|`,
written through its squared fibre norm as `c_i := (∫ rfns(∇^i u)^{k/i} dμ)^{i/(2k)}` for `0 < i`,
with the two posited endpoints folded in (`c_0 := Λ₀ · √(vol M)` the `L^∞`-endpoint comparison,
`c_k := ‖∇^k u‖_{L²}`).  It is the discrete sequence whose Gagliardo–Nirenberg log-convexity drives
the interpolation; it is `noncomputable` only through the volume measure. -/
private noncomputable def lpFiberJetLadder
    (g : SmoothRiemannianMetric I M) (s k : ℕ) (u : Integral.L2.SmoothCcTensor g 0 s)
    (Λ₀ : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then
    Λ₀ * Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal
  else if i = k then
    Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun
  else
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u).toSection x)) ^ ((k : ℝ) / i)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * k))

section SecondOrderInterpCore

/-! ### The finite-factor weighted covariant `Lᵖ` integration-by-parts

The genuine covariant integration-by-parts engine of the second-order interpolation, isolated to a
single smooth compactly-supported tensor `w`.  Writing `∇ = covGrad`, `a := rfns(w)`,
`b := rfns(∇w)`, `c := rfns(∇²w)` and the exponent `p := k/(i+1)` (with `1 < p`, i.e. `i + 1 < k` in
the finite regime), moving one covariant derivative off the right factor `∇w` of
`∫ |∇w|^{2p} = ∫ |∇w|^{2p-2}·⟨∇w,∇w⟩` through the divergence theorem yields
```
∫ b^p ≤ (2(p-1) + √(finrank)) · ∫ a^{1/2} · b^{p-1} · c^{1/2}.
```
Because the weight `b^{p-1}` is not smooth where `b = 0` (for `1 < p < 2`), this is reached through
the smooth *regularised* weight `(b + ε)^{p-1}` and an `ε → 0` dominated limit; accordingly the
headline `weightedCovIBP_lpFiberJet_fin` is assembled as honest limit-glue over the two posited
analytic children `weightedCovIBP_lpFiberJet_fin_regIneq` (the regularised inequality at each `ε`)
and `weightedCovIBP_lpFiberJet_fin_regLimit` (the `ε → 0` dominated-convergence limits).  Consumers
transitively depend on the `sorryAx` of those two children.  **General analytic infrastructure**
(regularised weighted-`Lᵖ` covariant IBP) to be promoted to a dedicated `Analysis/Sobolev` file. -/


/-- **Diagonal frame-trace sub-sum bound for the second covariant derivative.** With
`B_i := smoothOrthoFrame g x i` the `g_x`-orthonormal smooth frame at `x`, the sum over the
diagonal directions `(B_i, B_i)` of the fibre norms of the second covariant derivatives is
dominated by the full fibre norm of the second iterated covariant gradient:
```
∑ᵢ rfns(∇²_{Bᵢ, Bᵢ} w)(x) ≤ rfns(∇²w)(x).
```
The full fibre norm `rfns(∇²w)` is the slot-`0` double Parseval frame-sum
`∑_{a,b,J} (component(∇²w)(a :: b :: J))²` in the `g_x`-orthonormal frame `e a := B_a x`
(`riemannianFiberNormSq_eq_sum_componentS_sq` with two `Fin.consEquiv` re-indexings); each
diagonal term `rfns(∇²_{Bᵢ, Bᵢ}w)` is the `(a = b = i)` slice `∑_J (component(∇²w)(i :: i :: J))²`,
the per-component identity reading the two leftmost slots of `∇²w` at `(Bᵢ x, Bᵢ x)`
(`tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal`); the diagonal sub-sum of the
non-negative double sum is bounded by the whole. -/
private theorem secondCovDeriv_frame_diag_fiberNormSq_sum_le
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (w : Integral.L2.SmoothCcTensor g 0 m) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E),
        riemannianFiberNormSq (I := I) (M := M) g 0 m x
          (Integral.Connection.tensorSecondCovDeriv (I := I) g 0 m
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (fun y : M => w.toSection y) x) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
        ((covGrad (I := I) (M := M) g 0 (m + 1)
            (covGrad (I := I) (M := M) g 0 m w)).toSection x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  -- The `g_x`-orthonormal moving frame, read at the centre `x`.
  set e : Fin n → TangentSpace I x :=
    fun a => Integral.Connection.smoothOrthoFrame (I := I) g x a x with he_def
  have hnTan : n = Module.finrank ℝ (TangentSpace I x) := hn_def
  have horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := by
    intro a b
    rw [he_def]
    exact Integral.Connection.smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  -- The second iterated covariant gradient as a `(0, m+1+1)`-tensor at `x`.
  set T2 : Tensor0SBundle.TensorRSSpace 0 (m + 1 + 1) I x :=
    (covGrad (I := I) (M := M) g 0 (m + 1)
      (covGrad (I := I) (M := M) g 0 m w)).toSection x with hT2_def
  -- The frame Parseval representations at ranks `m` and `m + 1 + 1` in the moving frame `e`.
  have hreprS : ∀ S : Tensor0SBundle.TensorRSSpace 0 m I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 m x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin m → Fin n,
          Integral.Connection.fiberNormSqSummand (I := I) (M := M) g x 0 m S n e K J :=
    fun S => Integral.Connection.rfns_eq_sum_fiberNormSqSummand_of_orthoFrame
      (I := I) (M := M) g m x S e hnTan horth
  have hreprT2 : ∀ S : Tensor0SBundle.TensorRSSpace 0 (m + 1 + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (m + 1 + 1) → Fin n,
          Integral.Connection.fiberNormSqSummand (I := I) (M := M) g x 0 (m + 1 + 1) S n e K J :=
    fun S => Integral.Connection.rfns_eq_sum_fiberNormSqSummand_of_orthoFrame
      (I := I) (M := M) g (m + 1 + 1) x S e hnTan horth
  -- The per-component identity: each diagonal second-derivative component reads off `T2`
  -- at the two leftmost slots `(e i, e i)` via the two-slot evaluation bridge.
  have hcomp : ∀ (i : Fin n) (J : Fin m → Fin n),
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 m
          (Integral.Connection.tensorSecondCovDeriv (I := I) g 0 m
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (fun y : M => w.toSection y) x) n e K₀ J =
        Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
          (Fin.cons i (Fin.cons i J)) := by
    intro i J
    -- The empty coframe covector at `K₀` is the unit `(0, 0)`-tensor.
    have hco : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K₀ k))) : Tensor0SBundle.Tensor0SSpace 0 I x) =
        unitZeroSec (I := I) (M := M) x := by
      rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K₀ k))) : Tensor0SBundle.Tensor0SSpace 0 I x) =
          Integral.Connection.coframeS (I := I) (M := M) g x 0 e K₀ from rfl]
      exact Integral.Connection.coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K₀
    -- Tuple identity: `fun k => e ((i :: i :: J) k) = e i :: e i :: (fun k => e (J k))`.
    have htuple : (fun k : Fin (m + 1 + 1) =>
          e ((Fin.cons i (Fin.cons i J) : Fin (m + 1 + 1) → Fin n) k)) =
        Fin.cons (e i) (Fin.cons (e i) (fun k : Fin m => e (J k))) := by
      funext k
      refine Fin.cases ?_ ?_ k
      · simp
      · intro j
        refine Fin.cases ?_ ?_ j
        · simp
        · intro l; simp
    -- Unfold both components and match through the two-slot bridge.
    rw [Integral.Connection.fiberNormSqComponent, Integral.Connection.fiberNormSqComponent,
      hco, htuple]
    rw [he_def]
    exact (Integral.Connection.tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal
      (I := I) (M := M) g m w
      (X := Integral.Connection.smoothOrthoFrame (I := I) g x i)
      (Y := Integral.Connection.smoothOrthoFrame (I := I) g x i)
      (Integral.Connection.smoothOrthoFrame_smooth (I := I) g x i)
      (Integral.Connection.smoothOrthoFrame_smooth (I := I) g x i) x
      (fun k : Fin m => e (J k))).symm
  -- Each diagonal fibre norm is the `(a = b = i)` slice of the `T2` component double sum.
  have hdiag_term : ∀ i : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 m x
          (Integral.Connection.tensorSecondCovDeriv (I := I) g 0 m
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (fun y : M => w.toSection y) x) =
        ∑ J : Fin m → Fin n,
          (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
            (Fin.cons i (Fin.cons i J))) ^ 2 := by
    intro i
    rw [Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq
      (I := I) (M := M) g x m e hreprS _ K₀]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [hcomp i J]
  -- The full fibre norm of `T2` is the slot-`0` double Parseval frame sum over `(a, b, J)`.
  have hfull : riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x T2 =
      ∑ a : Fin n, ∑ b : Fin n, ∑ J : Fin m → Fin n,
        (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
          (Fin.cons a (Fin.cons b J))) ^ 2 := by
    rw [Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq
      (I := I) (M := M) g x (m + 1 + 1) e hreprT2 T2 K₀]
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1 + 1) => Fin n))
          (fun pr : Fin n × (Fin (m + 1) → Fin n) =>
            (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
              (Fin.cons pr.1 pr.2)) ^ 2)
          (fun J'' : Fin (m + 1 + 1) → Fin n =>
            (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
              J'') ^ 2)
          (fun pr => by simp [Fin.consEquiv])]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Fin n))
          (fun pr : Fin n × (Fin m → Fin n) =>
            (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
              (Fin.cons a (Fin.cons pr.1 pr.2))) ^ 2)
          (fun J' : Fin (m + 1) → Fin n =>
            (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
              (Fin.cons a J')) ^ 2)
          (fun pr => by simp [Fin.consEquiv])]
    rw [Fintype.sum_prod_type]
  -- Sum the diagonal terms and bound by the full double sum (drop the off-diagonal `b ≠ i`).
  rw [hfull]
  have hdiag_sum : ∑ i : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 m x
          (Integral.Connection.tensorSecondCovDeriv (I := I) g 0 m
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (Integral.Connection.smoothOrthoFrame (I := I) g x i)
            (fun y : M => w.toSection y) x) =
      ∑ i : Fin n, ∑ J : Fin m → Fin n,
        (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
          (Fin.cons i (Fin.cons i J))) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => hdiag_term i)
  rw [hdiag_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  -- The diagonal `b = i` term is one non-negative summand of the inner `∑_b` sum.
  refine Finset.single_le_sum (f := fun b : Fin n =>
      ∑ J : Fin m → Fin n,
        (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 (m + 1 + 1) T2 n e K₀
          (Fin.cons i (Fin.cons b J))) ^ 2)
    (fun b _ => Finset.sum_nonneg (fun J _ => sq_nonneg _)) (Finset.mem_univ i)

/-- **(POSIT — child A: the `√n` rough-Laplacian trace bound.)**

The pointwise Cauchy–Schwarz bound for the rough-Laplacian inner product against `w`, with the
sharp `√(finrank)` trace constant (NOT the naive `finrank·|∇²w|`): reading `Δ_raw w (x) = ∑ᵢ ∇²_{Bᵢ,Bᵢ}
w (x)` as a diagonal frame trace, the discrete Cauchy–Schwarz on the `n = finrank`-term sum gives the
`√n`, and the diagonal sub-sum `∑ᵢ |∇²_{Bᵢ,Bᵢ}w|²(x) ≤ |∇²w|²(x) = rfns(∇²w)(x)` bounds the remaining
factor:
```
|⟨Δ_raw w, w⟩(x)| ≤ √(finrank) · (rfns(w)(x))^{1/2} · (rfns(∇²w)(x))^{1/2}.
```
Assembled from the frame trace `rawTensorConnLap_eq_frame_trace_secondCovDeriv`, the per-direction
pointwise Cauchy–Schwarz `tensorInnerPointwise_sq_le_mul`, the discrete `n`-term Cauchy–Schwarz
`Finset.sum_mul_sq_le_sq_mul_sq`, and the diagonal frame-trace sub-sum bound
`secondCovDeriv_frame_diag_fiberNormSq_sum_le`.  **General analytic infrastructure**
(rough-Laplacian diagonal trace bound) to be promoted to `Analysis/Elliptic/ConnectionLaplacian`. -/
private theorem rawConnLap_innerWith_sqrt_finrank_bound
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (w : Integral.L2.SmoothCcTensor g 0 m) (x : M) :
    |Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        ((rawTensorConnLapSmooth (I := I) g 0 m w).toFun x) (w.toFun x)| ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) *
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) *
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
          ((covGrad (I := I) (M := M) g 0 (m + 1)
            (covGrad (I := I) (M := M) g 0 m w)).toSection x)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  -- Abbreviations for the two squared fibre norms appearing on the right.
  set aw : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) with haw_def
  set cw : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
      ((covGrad (I := I) (M := M) g 0 (m + 1)
        (covGrad (I := I) (M := M) g 0 m w)).toSection x) with hcw_def
  have haw_nn : 0 ≤ aw := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m x _
  have hcw_nn : 0 ≤ cw := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) x _
  -- The per-direction diagonal second covariant derivatives.
  set D : Fin n → Tensor0SBundle.TensorRSSpace 0 m I x :=
    fun i => Integral.Connection.tensorSecondCovDeriv (I := I) g 0 m
      (Integral.Connection.smoothOrthoFrame (I := I) g x i)
      (Integral.Connection.smoothOrthoFrame (I := I) g x i)
      (fun y : M => w.toSection y) x with hD_def
  -- The rough Laplacian is the frame trace of the second covariant derivative.
  have htrace : (rawTensorConnLapSmooth (I := I) g 0 m w).toFun x =
      Tensor0SBundle.TensorRSSpace.toModel (∑ i : Fin n, D i) := by
    have h1 : (rawTensorConnLapSmooth (I := I) g 0 m w).toFun x =
        Tensor0SBundle.TensorRSSpace.toModel
          ((rawTensorConnLapSmooth (I := I) g 0 m w).toSection x) := rfl
    rw [h1, Integral.Connection.rawTensorConnLapSmooth_toSection_apply (I := I) (M := M) g 0 m w x,
      Integral.Connection.rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 m
        (fun y : M => w.toSection y) x]
  -- Distribute the pairing over the frame sum (linearity of `toModel` and the left slot).
  have hsum_aux : ∀ (s' : Finset (Fin n)),
      Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
          (Tensor0SBundle.TensorRSSpace.toModel (∑ i ∈ s', D i)) (w.toFun x) =
        ∑ i ∈ s', Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
          (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x) := by
    intro s'
    induction s' using Finset.induction with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty, Tensor0SBundle.TensorRSSpace.toModel_zero]
        exact Integral.L2.tensorInnerPointwise_zero_left (I := I) (M := M) g 0 m x (w.toFun x)
    | insert i₀ s'' hi₀ ih =>
        rw [Finset.sum_insert hi₀, Finset.sum_insert hi₀, Tensor0SBundle.TensorRSSpace.toModel_add,
          Integral.L2.tensorInnerPointwise_add_left, ih]
  -- Read the pairing as the frame sum of per-direction pairings.
  have hsum : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        ((rawTensorConnLapSmooth (I := I) g 0 m w).toFun x) (w.toFun x) =
      ∑ i : Fin n, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x) := by
    rw [htrace]
    exact hsum_aux Finset.univ
  -- Per-direction pointwise Cauchy–Schwarz: `|⟨D i, w⟩| ≤ √(rfns(D i)) · √(aw)`.
  set r : Fin n → ℝ := fun i => riemannianFiberNormSq (I := I) (M := M) g 0 m x (D i) with hr_def
  have hr_nn : ∀ i, 0 ≤ r i := fun i =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m x (D i)
  have hCSi : ∀ i, |Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x)| ≤
      Real.sqrt (r i) * Real.sqrt aw := by
    intro i
    have hsq := Integral.L2.tensorInnerPointwise_sq_le_mul (I := I) (M := M) g 0 m x
      (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x)
    have hDi_self : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Tensor0SBundle.TensorRSSpace.toModel (D i))
        (Tensor0SBundle.TensorRSSpace.toModel (D i)) = r i := by
      rw [show r i = riemannianFiberNormSq (I := I) (M := M) g 0 m x (D i) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 m x (D i)]
    have hw_self : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (w.toFun x) (w.toFun x) = aw := by
      rw [show aw = riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 m x (w.toSection x)]
      rfl
    rw [hDi_self, hw_self] at hsq
    have habs : |Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x)| ≤ Real.sqrt (r i * aw) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_mul (hr_nn i)] at habs
    exact habs
  -- Bound the pairing by `∑ᵢ √(r i) · √(aw)`, then discrete Cauchy–Schwarz.
  rw [hsum]
  have hstep1 : |∑ i : Fin n, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x)| ≤
      ∑ i : Fin n, Real.sqrt (r i) * Real.sqrt aw := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum (fun i _ => hCSi i)
  -- Discrete `n`-term Cauchy–Schwarz: `(∑ᵢ √(r i))² ≤ n · ∑ᵢ r i`.
  have hdiscrete : (∑ i : Fin n, Real.sqrt (r i)) ^ 2 ≤ (n : ℝ) * ∑ i : Fin n, r i := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun _ => (1 : ℝ)) (fun i => Real.sqrt (r i))
    have hone : ∑ _i : Fin n, (1 : ℝ) ^ 2 = (n : ℝ) := by
      simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
    have hsqrt_sq : ∑ i : Fin n, Real.sqrt (r i) ^ 2 = ∑ i : Fin n, r i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Real.sq_sqrt (hr_nn i)]
    have hlhs : (∑ i : Fin n, (1 : ℝ) * Real.sqrt (r i)) = ∑ i : Fin n, Real.sqrt (r i) := by
      refine Finset.sum_congr rfl (fun i _ => ?_); rw [one_mul]
    rw [hlhs, hone, hsqrt_sq] at hcs
    exact hcs
  -- The diagonal frame-trace sub-sum bound: `∑ᵢ r i ≤ cw`.
  have hdiag : ∑ i : Fin n, r i ≤ cw :=
    secondCovDeriv_frame_diag_fiberNormSq_sum_le (I := I) (M := M) g m w x
  -- Assemble: `∑ᵢ √(r i) ≤ √(n · ∑ᵢ r i) ≤ √n · √(cw)`.
  have hsum_sqrt_nn : 0 ≤ ∑ i : Fin n, Real.sqrt (r i) :=
    Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsum_r_nn : 0 ≤ ∑ i : Fin n, r i := Finset.sum_nonneg (fun i _ => hr_nn i)
  have hsqrt_bound : ∑ i : Fin n, Real.sqrt (r i) ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt cw := by
    have h1 : ∑ i : Fin n, Real.sqrt (r i) ≤ Real.sqrt ((n : ℝ) * ∑ i : Fin n, r i) := by
      rw [← Real.sqrt_sq hsum_sqrt_nn]
      exact Real.sqrt_le_sqrt hdiscrete
    have h2 : Real.sqrt ((n : ℝ) * ∑ i : Fin n, r i) ≤ Real.sqrt ((n : ℝ) * cw) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hdiag hn_nn)
    have h3 : Real.sqrt ((n : ℝ) * cw) = Real.sqrt (n : ℝ) * Real.sqrt cw :=
      Real.sqrt_mul hn_nn cw
    calc ∑ i : Fin n, Real.sqrt (r i)
        ≤ Real.sqrt ((n : ℝ) * ∑ i : Fin n, r i) := h1
      _ ≤ Real.sqrt ((n : ℝ) * cw) := h2
      _ = Real.sqrt (n : ℝ) * Real.sqrt cw := h3
      _ = Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt cw := by rw [hn_def]
  calc |∑ i : Fin n, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
          (Tensor0SBundle.TensorRSSpace.toModel (D i)) (w.toFun x)|
      ≤ ∑ i : Fin n, Real.sqrt (r i) * Real.sqrt aw := hstep1
    _ = (∑ i : Fin n, Real.sqrt (r i)) * Real.sqrt aw := by rw [← Finset.sum_mul]
    _ ≤ (Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt cw) * Real.sqrt aw := by
        exact mul_le_mul_of_nonneg_right hsqrt_bound (Real.sqrt_nonneg _)
    _ = Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt aw * Real.sqrt cw := by ring

/-- **Frame-sum fibre norm of the covector-prepend section.** For a smooth scalar `ζ`, a smooth
compactly-supported `(0, t)`-tensor `S`, a point `x`, and the `g_x`-orthonormal moving frame
`B_a := smoothOrthoFrame g x a`, the fibre norm of the covector-prepend section
`prependCovGradSlot g 0 t ζ S` at `x` is the frame `g`-norm² of the differential `dζ` times the
fibre norm of `S`:
```
rfns(prependCovGradSlot g 0 t ζ S)(x) = (∑_a (dζ(B_a x))²) · rfns(S)(x).
```
The section value is `covGradBundleEquiv((dζ)·smulRight S(x))`
(`prependCovGradSlot_toSection_apply`); the slot-`0` frame-sum
`riemannianFiberNormSq_covGradBundleEquiv_eq_sum_frame` reads it as `∑_a rfns(dζ(B_a x) • S(x))`,
and each scalar-multiplied fibre norm factors as `(dζ(B_a x))² · rfns(S(x))`. -/
private theorem prependCovGradSlot_fiberNormSq_frame_sum
    (g : SmoothRiemannianMetric I M) (t : ℕ) (ζ : C^∞⟮I, M; ℝ⟯)
    (S : Integral.L2.SmoothCcTensor g 0 t) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (t + 1) x
        ((prependCovGradSlot (I := I) (M := M) g 0 t ζ S).toSection x) =
      (∑ a : Fin (Module.finrank ℝ E),
          (extDerivFun (I := I) (ζ : M → ℝ) x
            (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) *
        riemannianFiberNormSq (I := I) (M := M) g 0 t x (S.toSection x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set e : Fin n → TangentSpace I x :=
    fun a => Integral.Connection.smoothOrthoFrame (I := I) g x a x with he_def
  have hnTan : n = Module.finrank ℝ (TangentSpace I x) := hn_def
  have horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := by
    intro a b
    rw [he_def]
    exact Integral.Connection.smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  have hreprS : ∀ U : Tensor0SBundle.TensorRSSpace 0 t I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 t x U =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
          Integral.Connection.fiberNormSqSummand (I := I) (M := M) g x 0 t U n e K J :=
    fun U => Integral.Connection.rfns_eq_sum_fiberNormSqSummand_of_orthoFrame
      (I := I) (M := M) g t x U e hnTan horth
  have hreprSucc : ∀ U : Tensor0SBundle.TensorRSSpace 0 (t + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (t + 1) x U =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (t + 1) → Fin n,
          Integral.Connection.fiberNormSqSummand (I := I) (M := M) g x 0 (t + 1) U n e K J :=
    fun U => Integral.Connection.rfns_eq_sum_fiberNormSqSummand_of_orthoFrame
      (I := I) (M := M) g (t + 1) x U e hnTan horth
  -- The section value is the covariant-gradient bundle image of `v ↦ dζ(v) • S(x)`.
  rw [prependCovGradSlot_toSection_apply (I := I) (M := M) g 0 t ζ S x]
  rw [Integral.Connection.riemannianFiberNormSq_covGradBundleEquiv_eq_sum_frame
    (I := I) (M := M) g t x
    ((extDerivFun (I := I) (ζ : M → ℝ) x).smulRight (S.toSection x)) e K₀ hreprS hreprSucc]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  -- Each per-direction slice is `dζ(e a) • S(x)`, whose fibre norm is `(dζ(e a))² · rfns(S(x))`.
  rw [ContinuousLinearMap.smulRight_apply]
  -- `rfns(c • T) = c² · rfns(T)` via the inner-product bridge.
  rw [show ((extDerivFun (I := I) (ζ : M → ℝ) x (e a)) • S.toSection x :
        Tensor0SBundle.TensorRSSpace 0 t I x) =
      (extDerivFun (I := I) (ζ : M → ℝ) x (e a)) • S.toSection x from rfl]
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 t x
    ((extDerivFun (I := I) (ζ : M → ℝ) x (e a)) • S.toSection x),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 t x (S.toSection x)]
  rw [Tensor0SBundle.TensorRSSpace.toModel_smul,
    Integral.L2.tensorInnerPointwise_smul_left, Integral.L2.tensorInnerPointwise_smul_right]
  rw [he_def]
  ring

/-- **Directional metric compatibility of the squared fibre norm, in covariant-gradient form.**
For a smooth compactly-supported `(0, p)`-tensor `Q`, a point `x`, and a tangent vector `v`, the
manifold derivative of `y ↦ rfns(Q)(y)` in the direction `v` is twice the pointwise inner product
of the directional covariant derivative `∇_v Q` against `Q(x)`:
```
mfderiv(rfns Q) x v = 2 · ⟨∇_v Q, Q⟩(x).
```
This is the diagonal `W = S = Q` case of the metric-compatibility identity
`tensorInnerPointwise_hasMFDerivAt_metricCompatible` (the two Leibniz halves coincide by symmetry
of the covariant inner product), pushed back from the `loweredCovDerivAt`/`lifted` `(0, 0 + p)`
form to the un-lowered `(0, p)` covariant-derivative form through the rank-`0` lowering intertwiner
`loweredCovDerivAt_eq_lower_tensorCovDerivAt_gen` and `toModel_liftedTensorSection`. -/
private theorem mfderiv_riemannianFiberNormSq_eq_two_mul_covDeriv_inner
    (g : SmoothRiemannianMetric I M) (p : ℕ)
    (Q : Integral.L2.SmoothCcTensor g 0 p) (x : M) (v : TangentSpace I x) :
    extDerivFun (I := I)
        (fun y : M => riemannianFiberNormSq (I := I) (M := M) g 0 p y (Q.toSection y)) x v =
      2 * Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p x
        (Tensor0SBundle.TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 p Q x v))
        (Q.toFun x) := by
  classical
  -- `extDerivFun = mfderiv` (definitionally), and `rfns(Q)` is the inner-product scalar.
  have hfun : (fun y : M => riemannianFiberNormSq (I := I) (M := M) g 0 p y (Q.toSection y)) =
      fun y : M => Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p y
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y))
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y)) := by
    funext y
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 p y (Q.toSection y)]
  rw [hfun]
  rw [show extDerivFun (I := I)
        (fun y : M => Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p y
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y))
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y))) x v =
      mfderiv I 𝓘(ℝ, ℝ)
        (fun y : M => Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p y
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y))
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection y))) x v from rfl]
  -- The metric-compatibility identity (general `(r, s) = (0, p)`, two equal halves).
  rw [Integral.Connection.tensorInnerPointwise_hasMFDerivAt_metricCompatible
    (I := I) (M := M) g 0 p Q.toSection Q.toSection x v]
  -- Identify each `(0, 0 + p)` lowered/lifted half with the un-lowered `(0, p)` covariant pairing.
  have hbridge : Integral.L2.tensorInnerPointwise_0s (I := I) (M := M) (0 + p) g x
        (Tensor0SBundle.Tensor0SSpace.toModel
          (Integral.Connection.loweredCovDerivAt (I := I) (M := M) g 0 p Q.toSection x v))
        (Tensor0SBundle.Tensor0SSpace.toModel
          (Integral.Connection.liftedTensorSection (I := I) (M := M) g 0 p Q.toSection x)) =
      Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p x
        (Tensor0SBundle.TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 p Q x v))
        (Q.toFun x) := by
    rw [show Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p x
          (Tensor0SBundle.TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 p Q x v))
          (Q.toFun x) =
        Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p x
          (Tensor0SBundle.TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 p Q x v))
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x)) from rfl]
    unfold Integral.L2.tensorInnerPointwise
    rw [show Integral.L2.lowerAllUpperIndices (I := I) (M := M) g 0 p x
          (Tensor0SBundle.TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 p Q x v)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (Integral.Connection.loweredCovDerivAt (I := I) (M := M) g 0 p Q.toSection x v) from
      (Integral.Connection.loweredCovDerivAt_eq_lower_tensorCovDerivAt_gen
        (I := I) (M := M) g p Q.toSection x v).symm]
    rw [show Integral.L2.lowerAllUpperIndices (I := I) (M := M) g 0 p x
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (Integral.Connection.liftedTensorSection (I := I) (M := M) g 0 p Q.toSection x) from
      (Integral.Connection.toModel_liftedTensorSection
        (I := I) (M := M) g 0 p Q.toSection x).symm]
  rw [hbridge]
  -- The second metric-compatibility half is the same pairing by symmetry of `⟨·,·⟩_{0s}`.
  rw [Integral.L2.tensorInnerPointwise_0s_symm (I := I) (M := M) g x (0 + p)
      (Tensor0SBundle.Tensor0SSpace.toModel
        (Integral.Connection.liftedTensorSection (I := I) (M := M) g 0 p Q.toSection x))
      (Tensor0SBundle.Tensor0SSpace.toModel
        (Integral.Connection.loweredCovDerivAt (I := I) (M := M) g 0 p Q.toSection x v))]
  rw [hbridge]
  ring

/-- **The Kato frame-sum bound for the squared-fibre-norm differential.** For a smooth
compactly-supported `(0, p)`-tensor `Q`, a point `x`, and the `g_x`-orthonormal moving frame
`B_a := smoothOrthoFrame g x a`, the frame `g`-norm² of the differential of `rfns(Q)` is bounded
by four times the product of the fibre norm of `Q` and the fibre norm of its covariant gradient:
```
∑_a (mfderiv(rfns Q) x (B_a x))² ≤ 4 · rfns(Q)(x) · rfns(∇Q)(x).
```
Each `mfderiv(rfns Q) x (B_a x) = 2⟨∇_{B_a} Q, Q⟩(x)`
(`mfderiv_riemannianFiberNormSq_eq_two_mul_covDeriv_inner`); the per-direction Cauchy–Schwarz
`tensorInnerPointwise_sq_le_mul` bounds its square by `4 · rfns(∇_{B_a} Q) · rfns(Q)`; and the
slot-`0` frame-sum `riemannianFiberNormSq_covGradBundleEquiv_eq_sum_frame` (applied to
`∇Q = covGrad g 0 p Q`, whose section value is the bundle image of `v ↦ ∇_v Q`) reassembles
`∑_a rfns(∇_{B_a} Q) = rfns(∇Q)`. -/
private theorem kato_mfderiv_riemannianFiberNormSq_frame_sum_le
    (g : SmoothRiemannianMetric I M) (p : ℕ)
    (Q : Integral.L2.SmoothCcTensor g 0 p) (x : M) :
    ∑ a : Fin (Module.finrank ℝ E),
        (extDerivFun (I := I)
          (fun y : M => riemannianFiberNormSq (I := I) (M := M) g 0 p y (Q.toSection y)) x
          (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2 ≤
      4 * riemannianFiberNormSq (I := I) (M := M) g 0 p x (Q.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 0 (p + 1) x
          ((covGrad (I := I) (M := M) g 0 p Q).toSection x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set e : Fin n → TangentSpace I x :=
    fun a => Integral.Connection.smoothOrthoFrame (I := I) g x a x with he_def
  have hnTan : n = Module.finrank ℝ (TangentSpace I x) := hn_def
  have horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := by
    intro a b
    rw [he_def]
    exact Integral.Connection.smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  set rQ : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 p x (Q.toSection x) with hrQ_def
  have hrQ_nn : 0 ≤ rQ := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 p x (Q.toSection x)
  -- The per-direction covariant derivatives and their fibre norms.
  set V : Fin n → Tensor0SBundle.TensorRSSpace 0 p I x :=
    fun a => tensorCovDerivAt (I := I) (M := M) g 0 p Q x (e a) with hV_def
  set s : Fin n → ℝ := fun a => riemannianFiberNormSq (I := I) (M := M) g 0 p x (V a) with hs_def
  have hs_nn : ∀ a, 0 ≤ s a := fun a =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 p x (V a)
  -- Each directional differential squared is `≤ 4 · s a · rQ`.
  have hterm : ∀ a : Fin n,
      (extDerivFun (I := I)
        (fun y : M => riemannianFiberNormSq (I := I) (M := M) g 0 p y (Q.toSection y)) x (e a)) ^ 2 ≤
        4 * s a * rQ := by
    intro a
    rw [mfderiv_riemannianFiberNormSq_eq_two_mul_covDeriv_inner (I := I) (M := M) g p Q x (e a)]
    have hsq := Integral.L2.tensorInnerPointwise_sq_le_mul (I := I) (M := M) g 0 p x
      (Tensor0SBundle.TensorRSSpace.toModel (V a)) (Q.toFun x)
    have hVself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p x
        (Tensor0SBundle.TensorRSSpace.toModel (V a))
        (Tensor0SBundle.TensorRSSpace.toModel (V a)) = s a := by
      rw [show s a = riemannianFiberNormSq (I := I) (M := M) g 0 p x (V a) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 p x (V a)]
    have hQself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 p x
        (Q.toFun x) (Q.toFun x) = rQ := by
      rw [show rQ = riemannianFiberNormSq (I := I) (M := M) g 0 p x (Q.toSection x) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 p x (Q.toSection x)]
      rfl
    rw [hVself, hQself] at hsq
    have hVa_eq : Tensor0SBundle.TensorRSSpace.toModel (V a) =
        Tensor0SBundle.TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 p Q x (e a)) := by
      rw [hV_def]
    rw [hVa_eq] at hsq ⊢
    nlinarith [hsq]
  -- The frame sum of the per-direction fibre norms reconstructs `rfns(∇Q)`.
  have hframe : ∑ a : Fin n, s a =
      riemannianFiberNormSq (I := I) (M := M) g 0 (p + 1) x
        ((covGrad (I := I) (M := M) g 0 p Q).toSection x) := by
    rw [covGrad_toSection_apply (I := I) (M := M) g 0 p Q x]
    have hreprS : ∀ U : Tensor0SBundle.TensorRSSpace 0 p I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 p x U =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin p → Fin n,
            Integral.Connection.fiberNormSqSummand (I := I) (M := M) g x 0 p U n e K J :=
      fun U => Integral.Connection.rfns_eq_sum_fiberNormSqSummand_of_orthoFrame
        (I := I) (M := M) g p x U e hnTan horth
    have hreprSucc : ∀ U : Tensor0SBundle.TensorRSSpace 0 (p + 1) I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 (p + 1) x U =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin (p + 1) → Fin n,
            Integral.Connection.fiberNormSqSummand (I := I) (M := M) g x 0 (p + 1) U n e K J :=
      fun U => Integral.Connection.rfns_eq_sum_fiberNormSqSummand_of_orthoFrame
        (I := I) (M := M) g (p + 1) x U e hnTan horth
    rw [Integral.Connection.riemannianFiberNormSq_covGradBundleEquiv_eq_sum_frame
      (I := I) (M := M) g p x
      (TensorRSNabla.tensorRSCovariantDerivative I M 0 p (LeviCivita (I := I) g)
        Q.toSection x) e K₀ hreprS hreprSucc]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hs_def, hV_def]
    rfl
  -- Assemble.
  calc ∑ a : Fin n,
        (extDerivFun (I := I)
          (fun y : M => riemannianFiberNormSq (I := I) (M := M) g 0 p y (Q.toSection y)) x
          (e a)) ^ 2
      ≤ ∑ a : Fin n, 4 * s a * rQ := Finset.sum_le_sum (fun a _ => hterm a)
    _ = 4 * (∑ a : Fin n, s a) * rQ := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = 4 * rQ * riemannianFiberNormSq (I := I) (M := M) g 0 (p + 1) x
          ((covGrad (I := I) (M := M) g 0 p Q).toSection x) := by rw [hframe]; ring

set_option maxHeartbeats 1600000 in
/-- **(POSIT — child B: the `2(k-1)` weight cross-term bound.)**

The pointwise bound on the Leibniz cross term `⟨∇w, dζ ⊗ w⟩(x) = tensorCovDerivCrossLeft g 0 m ζ w w x`
for the weight `ζ = (rfns(∇w))^{k-1}`.  Expanding `dζ = (k-1)(rfns(∇w))^{k-2}·d(rfns(∇w))` and
`d(rfns(∇w)) = 2⟨∇²w, ∇w⟩` (metric compatibility), then Cauchy–Schwarz on the inverse-Gram double sum
gives
```
|tensorCovDerivCrossLeft g 0 m ζ w w x|
  ≤ 2·(k-1) · A · (rfns(∇w)(x))^{k-1} · (rfns(∇²w)(x))^{1/2},
```
using `rfns(w)(x) ≤ A²`.  Assembled from the cross-left metric-isometry bridge
`tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad`, the pointwise Cauchy–Schwarz
`tensorInnerPointwise_sq_le_mul`, the frame-sum prepend fibre norm
`prependCovGradSlot_fiberNormSq_frame_sum`, the metric-compatible chain rule for the weight
differential, and the Kato frame-sum bound `kato_mfderiv_rfns_frame_sum_le`.  **General analytic
infrastructure** (Leibniz weight cross-term bound) to be promoted alongside child A. -/
private theorem covDerivCrossLeft_weight_bound
    (g : SmoothRiemannianMetric I M) (k m : ℕ) (_hk : 1 ≤ k)
    (w : Integral.L2.SmoothCcTensor g 0 m) (A : ℝ) (_hA : 0 ≤ A)
    (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) ≤ A ^ 2)
    (ζ : C^∞⟮I, M; ℝ⟯)
    (hζ : (ζ : M → ℝ) = fun y => (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) y
        ((covGrad (I := I) (M := M) g 0 m w).toSection y)) ^ (k - 1))
    (x : M) :
    |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x| ≤
      2 * ((k : ℝ) - 1) * A *
        (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
          ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) - 1) *
        (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
          ((covGrad (I := I) (M := M) g 0 (m + 1)
            (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ (1 / 2 : ℝ) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  -- The gradient `Q = ∇w`, its squared fibre norm `b = rfns(∇w)(x)`, and `c = rfns(∇²w)(x)`.
  set Q : Integral.L2.SmoothCcTensor g 0 (m + 1) := covGrad (I := I) (M := M) g 0 m w with hQ_def
  set bfun : M → ℝ := fun y =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) y (Q.toSection y) with hbfun_def
  set b : ℝ := bfun x with hb_def
  set c : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
      ((covGrad (I := I) (M := M) g 0 (m + 1) Q).toSection x) with hc_def
  have hb_nn : 0 ≤ b := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) x (Q.toSection x)
  have hc_nn : 0 ≤ c := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) x _
  have hAsq : riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) ≤ A ^ 2 := _hsup x
  -- Step 1 — the cross term as the genuine `(0, m+1)`-tensor pairing `⟨∇w, P⟩`.
  set P : Integral.L2.SmoothCcTensor g 0 (m + 1) :=
    prependCovGradSlot (I := I) (M := M) g 0 m ζ w with hP_def
  have hcross_eq : tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x =
      Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
        (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x)) :=
    tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad (I := I) (M := M) g 0 m ζ w w x
  -- Step 2 — pointwise Cauchy–Schwarz: `|⟨∇w, P⟩| ≤ √b · √(rfns P)`.
  set rP : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x (P.toSection x) with hrP_def
  have hrP_nn : 0 ≤ rP := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) x _
  have hCS2 : |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x| ≤
      Real.sqrt b * Real.sqrt rP := by
    rw [hcross_eq]
    have hsq := Integral.L2.tensorInnerPointwise_sq_le_mul (I := I) (M := M) g 0 (m + 1) x
      (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
      (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x))
    have hQself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x)) = b := by
      rw [show b = riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x (Q.toSection x) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x (Q.toSection x)]
    have hPself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x
        (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x))
        (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x)) = rP := by
      rw [show rP = riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x (P.toSection x) from rfl,
        riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x (P.toSection x)]
    rw [hQself, hPself] at hsq
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hb_nn]
    exact Real.sqrt_le_sqrt hsq
  -- Step 3 — the prepend fibre norm `rfns(P) = (∑_a (dζ(B_a x))²) · rfns(w)`.
  have hrP_eq : rP = (∑ a : Fin n,
        (extDerivFun (I := I) (ζ : M → ℝ) x
          (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) *
        riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) :=
    prependCovGradSlot_fiberNormSq_frame_sum (I := I) (M := M) g m ζ w x
  -- Step 4 — the chain rule: `dζ(v) = (k-1) · b^{k-2} · mfderiv(bfun) x v`.
  have hbfun_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) bfun x := by
    have hb_eq_scalar : bfun = Integral.Connection.tensorInnerScalar (I := I) (M := M) g 0 (m + 1)
        Q.toSection Q.toSection := by
      funext y
      simp only [hbfun_def, Integral.Connection.tensorInnerScalar_apply]
      rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) y
        (Q.toSection y)]
    rw [hb_eq_scalar]
    exact (Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g 0 (m + 1)
      Q.toSection Q.toSection).mdifferentiableAt (by norm_num)
  have hchain : ∀ v : TangentSpace I x,
      extDerivFun (I := I) (ζ : M → ℝ) x v =
        ((k : ℝ) - 1) * b ^ (k - 2) * extDerivFun (I := I) bfun x v := by
    intro v
    have hinner : HasMFDerivAt I 𝓘(ℝ, ℝ) bfun x (mfderiv I 𝓘(ℝ, ℝ) bfun x) :=
      hbfun_mdiff.hasMFDerivAt
    have houter : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t ^ (k - 1)) (bfun x)
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (((k - 1 : ℕ) : ℝ) * (bfun x) ^ (k - 1 - 1)))) :=
      ((hasDerivAt_pow (k - 1) (bfun x)).hasFDerivAt).hasMFDerivAt
    have hcomp : HasMFDerivAt I 𝓘(ℝ, ℝ) ((fun t : ℝ => t ^ (k - 1)) ∘ bfun) x
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
            (((k - 1 : ℕ) : ℝ) * (bfun x) ^ (k - 1 - 1))).comp
          (mfderiv I 𝓘(ℝ, ℝ) bfun x)) :=
      HasMFDerivAt.comp x houter hinner
    have hζeq : (ζ : M → ℝ) = (fun t : ℝ => t ^ (k - 1)) ∘ bfun := by
      rw [hζ]; rfl
    have hext : extDerivFun (I := I) (ζ : M → ℝ) x v = mfderiv I 𝓘(ℝ, ℝ) (ζ : M → ℝ) x v := rfl
    have hCLM : (mfderiv I 𝓘(ℝ, ℝ) ((fun t : ℝ => t ^ (k - 1)) ∘ bfun) x) v =
        (((k - 1 : ℕ) : ℝ) * (bfun x) ^ (k - 1 - 1)) * extDerivFun (I := I) bfun x v := by
      rw [hcomp.mfderiv]
      change extDerivFun (I := I) bfun x v * (((k - 1 : ℕ) : ℝ) * (bfun x) ^ (k - 1 - 1)) =
        (((k - 1 : ℕ) : ℝ) * (bfun x) ^ (k - 1 - 1)) * extDerivFun (I := I) bfun x v
      ring
    have hmfζ : extDerivFun (I := I) (ζ : M → ℝ) x v =
        (((k - 1 : ℕ) : ℝ) * (bfun x) ^ (k - 1 - 1)) * extDerivFun (I := I) bfun x v := by
      rw [hext, hζeq]
      exact hCLM
    rw [hmfζ]
    have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub _hk, Nat.cast_one]
    have hexp : k - 1 - 1 = k - 2 := by omega
    rw [show (bfun x) = b from rfl, hkcast, hexp]
  -- Step 5 — Kato bound on `∑_a (db(B_a x))² ≤ 4 · b · c`.
  have hkato : ∑ a : Fin n,
      (extDerivFun (I := I) bfun x (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2 ≤
        4 * b * c :=
    kato_mfderiv_riemannianFiberNormSq_frame_sum_le (I := I) (M := M) g (m + 1) Q x
  -- Step 6 — bound `∑_a (dζ(B_a x))² ≤ (k-1)² b^{2(k-2)} · 4 b c`.
  have hdζsum : (∑ a : Fin n,
      (extDerivFun (I := I) (ζ : M → ℝ) x
        (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) ≤
        ((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 * (4 * b * c) := by
    have hrw : (∑ a : Fin n,
        (extDerivFun (I := I) (ζ : M → ℝ) x
          (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) =
        ((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 *
          ∑ a : Fin n,
            (extDerivFun (I := I) bfun x
              (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hchain (Integral.Connection.smoothOrthoFrame (I := I) g x a x)]
      ring
    rw [hrw]
    have hcoeff_nn : (0 : ℝ) ≤ ((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hkato hcoeff_nn
  -- Step 7 — assemble the bound on `rfns(P)`, then on `|crossLeft|`.
  have hrP_bound : rP ≤ ((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 * (4 * b * c) * A ^ 2 := by
    rw [hrP_eq]
    have hrfnsw_le : riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) ≤ A ^ 2 := hAsq
    have hrfnsw_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m x (w.toSection x)
    have hsum_nn : (0 : ℝ) ≤ ∑ a : Fin n,
        (extDerivFun (I := I) (ζ : M → ℝ) x
          (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2 :=
      Finset.sum_nonneg (fun a _ => sq_nonneg _)
    have hbound_nn : (0 : ℝ) ≤ ((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 * (4 * b * c) := by
      have : (0 : ℝ) ≤ 4 * b * c := by positivity
      positivity
    calc (∑ a : Fin n,
            (extDerivFun (I := I) (ζ : M → ℝ) x
              (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)
        ≤ (((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 * (4 * b * c)) *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) :=
          mul_le_mul_of_nonneg_right hdζsum hrfnsw_nn
      _ ≤ (((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 * (4 * b * c)) * A ^ 2 :=
          mul_le_mul_of_nonneg_left hrfnsw_le hbound_nn
      _ = ((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 * (4 * b * c) * A ^ 2 := by ring
  -- The final numeric assembly through `√b · √(rfns P)`.
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast _hk
    linarith
  -- Bridge the natural power `b^{k-1}` to the real power `b^{(k:ℝ)-1}`.
  have hbnat_rpow : b ^ (k - 1) = b ^ ((k : ℝ) - 1) := by
    rw [← Real.rpow_natCast b (k - 1)]
    congr 1
    rw [Nat.cast_sub _hk, Nat.cast_one]
  -- The goal right-hand side is already in `b`, `c` form (the `set`s fold the fibre norms).
  change |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x| ≤
      2 * ((k : ℝ) - 1) * A * b ^ ((k : ℝ) - 1) * c ^ (1 / 2 : ℝ)
  have hRHS_nn : (0 : ℝ) ≤ 2 * ((k : ℝ) - 1) * A * b ^ ((k : ℝ) - 1) * c ^ (1 / 2 : ℝ) := by
    have hbrpow : (0 : ℝ) ≤ b ^ ((k : ℝ) - 1) := Real.rpow_nonneg hb_nn _
    have hcrpow : (0 : ℝ) ≤ c ^ (1 / 2 : ℝ) := Real.rpow_nonneg hc_nn _
    positivity
  -- Reduce to the squared inequality `b · rP ≤ (RHS)²`.
  refine le_trans hCS2 ?_
  rw [← Real.sqrt_mul hb_nn rP,
    show 2 * ((k : ℝ) - 1) * A * b ^ ((k : ℝ) - 1) * c ^ (1 / 2 : ℝ) =
      Real.sqrt ((2 * ((k : ℝ) - 1) * A * b ^ ((k : ℝ) - 1) * c ^ (1 / 2 : ℝ)) ^ 2) from
    (Real.sqrt_sq hRHS_nn).symm]
  refine Real.sqrt_le_sqrt ?_
  -- Rewrite the squared target through the natural-power identity `(b^{k-1})² = b^{k-1}·b^{k-1}`.
  have hcrpow_sq : (c ^ (1 / 2 : ℝ)) ^ 2 = c := by
    rw [← Real.rpow_natCast (c ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hc_nn]
    norm_num
  have htarget_eq : (2 * ((k : ℝ) - 1) * A * b ^ ((k : ℝ) - 1) * c ^ (1 / 2 : ℝ)) ^ 2 =
      ((k : ℝ) - 1) ^ 2 * (4 * A ^ 2) * (b ^ (k - 1) * b ^ (k - 1)) * c := by
    rw [hbnat_rpow]
    rw [mul_pow, mul_pow, mul_pow, mul_pow, hcrpow_sq]
    ring
  rw [htarget_eq]
  -- The `(k-1)²`-weighted natural-power core (handles `k = 1` via the vanishing `(k-1)²` factor).
  have hb_core : ((k : ℝ) - 1) ^ 2 * (b * (b ^ (k - 2)) ^ 2 * b) =
      ((k : ℝ) - 1) ^ 2 * (b ^ (k - 1) * b ^ (k - 1)) := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · -- `k = 1`: the `(k - 1) = 0` real factor makes both members vanish.
      have hk1' : k = 1 := by omega
      subst hk1'
      norm_num
    · -- `k ≥ 2`: `b^{k-1} = b^{k-2}·b`, so both sides are products of `b` and `b^{k-2}`.
      have hbk1 : b ^ (k - 1) = b ^ (k - 2) * b := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hbk1, sq]
      ring
  calc b * rP
      ≤ b * (((k : ℝ) - 1) ^ 2 * (b ^ (k - 2)) ^ 2 * (4 * b * c) * A ^ 2) :=
        mul_le_mul_of_nonneg_left hrP_bound hb_nn
    _ = (4 * A ^ 2) * c * (((k : ℝ) - 1) ^ 2 * (b * (b ^ (k - 2)) ^ 2 * b)) := by ring
    _ = (4 * A ^ 2) * c * (((k : ℝ) - 1) ^ 2 * (b ^ (k - 1) * b ^ (k - 1))) := by rw [hb_core]
    _ = ((k : ℝ) - 1) ^ 2 * (4 * A ^ 2) * (b ^ (k - 1) * b ^ (k - 1)) * c := by ring

set_option maxHeartbeats 2000000 in
/-- **The finite-factor weighted covariant IBP at a fixed regularising level `ε > 0`.**

The weighted covariant integration-by-parts inequality *at a fixed regularising level* `ε > 0`,
against the smooth regularised weight `(b + ε)^{p-1}` (`b := rfns(∇w)`, `p := k/(i+1) > 1` in the
finite regime `i + 1 < k`).  Because `b + ε ≥ ε > 0` everywhere the weight is a genuine smooth
function on the closed manifold, so the covariant Green identity
`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen` applies to `v = (b+ε)^{p-1} • w`; the
metric Leibniz split, the regularised cross-term bound
(`|crossLeft| ≤ 2(p-1)·(rfns w)^{1/2}·(b+ε)^{p-1}·(rfns ∇²w)^{1/2}` via the chain rule
`d((b+ε)^{p-1}) = (p-1)(b+ε)^{p-2}·db`, the Kato bound, and `b·(b+ε)^{p-2} ≤ (b+ε)^{p-1}`), and the
rough-Laplacian `√(finrank)` trace bound `rawConnLap_innerWith_sqrt_finrank_bound` assemble to
```
∫ b·(b+ε)^{p-1} ≤ (2(p-1) + √(finrank)) · ∫ (rfns w)^{1/2}·(b+ε)^{p-1}·(rfns ∇²w)^{1/2}.
```
Proven outright by mirroring the `L^∞`-factor route `weightedCovIBP_lpFiberJet_sup` with the smooth
`ε`-weight in place of the natural-power weight; **general analytic infrastructure** (regularised
weighted-`Lᵖ` covariant IBP) to be promoted alongside the `ε → 0` limit. -/
private theorem weightedCovIBP_lpFiberJet_fin_regIneq
    (g : SmoothRiemannianMetric I M) (k m i : ℕ) (_hk : 1 ≤ k) (_hi : 1 ≤ i) (_hik : i + 1 < k)
    (w : Integral.L2.SmoothCcTensor g 0 m) (ε : ℝ) (_hε : 0 < ε) :
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
            ((covGrad (I := I) (M := M) g 0 m w).toSection x)) *
          ((riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
            ((covGrad (I := I) (M := M) g 0 m w).toSection x)) + ε) ^ ((k : ℝ) / (i + 1) - 1)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ≤
      (2 * ((k : ℝ) / (i + 1) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) *
        ∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) ^ (1 / 2 : ℝ) *
            ((riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) + ε) ^ ((k : ℝ) / (i + 1) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (m + 1)
                (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ (1 / 2 : ℝ)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g) := by
  classical
  haveI : MeasureTheory.IsFiniteMeasure (Integral.Measure.riemannianVolumeMeasure I M g) :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set μ : MeasureTheory.Measure M := Integral.Measure.riemannianVolumeMeasure I M g with hμ
  set n : ℕ := Module.finrank ℝ E with hn_def
  -- The IBP exponent `p = k/(i+1) > 1` and the weight exponent `pm1 = p − 1 > 0`.
  set p : ℝ := (k : ℝ) / (i + 1) with hp_def
  set pm1 : ℝ := p - 1 with hpm1_def
  have hi1R : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hp1 : 1 < p := by
    rw [hp_def, lt_div_iff₀ hi1R, one_mul]; exact_mod_cast _hik
  have hpm1_pos : 0 < pm1 := by rw [hpm1_def]; linarith
  have hpm1_nn : 0 ≤ pm1 := le_of_lt hpm1_pos
  -- The gradient tensors and the rough Laplacian.
  set gw : Integral.L2.SmoothCcTensor g 0 (m + 1) := covGrad (I := I) (M := M) g 0 m w with hgw
  set ggw : Integral.L2.SmoothCcTensor g 0 (m + 1 + 1) :=
    covGrad (I := I) (M := M) g 0 (m + 1) gw with hggw
  set Lw : Integral.L2.SmoothCcTensor g 0 m :=
    rawTensorConnLapSmooth (I := I) g 0 m w with hLw
  -- The pointwise fibre norms `a = rfns(w)`, `b = rfns(∇w)`, `c = rfns(∇²w)`.
  set a : M → ℝ := fun y => riemannianFiberNormSq (I := I) (M := M) g 0 m y (w.toSection y) with ha
  set b : M → ℝ := fun y => riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) y (gw.toSection y)
    with hb
  set c : M → ℝ := fun y =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) y (ggw.toSection y) with hc
  have ha_nonneg : ∀ y, 0 ≤ a y := fun y =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m y (w.toSection y)
  have hb_nonneg : ∀ y, 0 ≤ b y := fun y =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) y (gw.toSection y)
  have hc_nonneg : ∀ y, 0 ≤ c y := fun y =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) y (ggw.toSection y)
  -- `b` agrees pointwise with the smooth scalar `tensorInnerScalar g 0 (m+1) (∇w) (∇w)`.
  have hb_eq_scalar : b = Integral.Connection.tensorInnerScalar (I := I) (M := M) g 0 (m + 1)
      gw.toSection gw.toSection := by
    funext y
    simp only [hb, Integral.Connection.tensorInnerScalar_apply]
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) y
      (gw.toSection y)]
  have hb_smooth : ContMDiff I 𝓘(ℝ) ∞ b := by
    rw [hb_eq_scalar]
    exact Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g 0 (m + 1)
      gw.toSection gw.toSection
  -- The shifted base `bε = b + ε ≥ ε > 0` (smooth, nowhere zero).
  set bε : M → ℝ := fun y => b y + ε with hbε
  have hbε_smooth : ContMDiff I 𝓘(ℝ) ∞ bε := hb_smooth.add contMDiff_const
  have hbε_pos : ∀ y, 0 < bε y := fun y => by rw [hbε]; linarith [hb_nonneg y]
  have hbε_ne : ∀ y, bε y ≠ 0 := fun y => ne_of_gt (hbε_pos y)
  have hbε_nonneg : ∀ y, 0 ≤ bε y := fun y => le_of_lt (hbε_pos y)
  -- The smooth weight `ζ = (b + ε)^{p−1}` (positive base, so smooth everywhere).
  have hζ_smooth : ContMDiff I 𝓘(ℝ) ∞ (fun y => bε y ^ pm1) := by
    intro y
    exact (Real.contDiffAt_rpow_const_of_ne (p := pm1) (hbε_ne y)).comp_contMDiffAt
      hbε_smooth.contMDiffAt
  set ζ : C^∞⟮I, M; ℝ⟯ := ⟨fun y => bε y ^ pm1, hζ_smooth⟩ with hζ
  have hζ_apply : (ζ : M → ℝ) = fun y => bε y ^ pm1 := rfl
  have hζ_nonneg : ∀ y, 0 ≤ (ζ : M → ℝ) y := by
    intro y; rw [hζ_apply]; exact Real.rpow_nonneg (hbε_nonneg y) _
  -- The weight tensor `v = ζ • w`.
  set v : Integral.L2.SmoothCcTensor g 0 m :=
    scalarSmul (I := I) (M := M) g 0 m ζ w with hv
  -- The diagonal pointwise gradient inner product is `b`.
  have hdiag : ∀ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w w x = b x := by
    intro x
    rw [tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad (I := I) (M := M) g 0 m w w x,
      ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x
        ((covGrad (I := I) (M := M) g 0 m w).toSection x)]
  -- The metric Leibniz split (right slot): `⟨∇w, ∇(ζw)⟩ = ζ·⟨∇w,∇w⟩ + ⟨∇w, dζ⊗w⟩`.
  have hsplit : ∀ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v x =
      (ζ : M → ℝ) x * b x + tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x := by
    intro x
    rw [tensorCovDerivPointwiseInner_def, tensorCovDerivCrossLeft_def, ← hdiag,
      tensorCovDerivPointwiseInner_def, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hv, tensorCovDerivAt_scalarSmul (I := I) (M := M) g 0 m ζ w x
      ((Integral.Measure.chartModelBasis E) j)]
    have hwx : Tensor0SBundle.TensorRSSpace.toModel (w.toSection x) = w.toFun x := rfl
    simp only [Tensor0SBundle.TensorRSSpace.toModel_add, Tensor0SBundle.TensorRSSpace.toModel_smul,
      hwx, Integral.L2.tensorInnerPointwise_add_right, Integral.L2.tensorInnerPointwise_smul_right]
    ring
  -- The right-hand scalar pull-out: `⟨Δw, ζw⟩ = ζ·⟨Δw, w⟩` pointwise.
  have hpull : ∀ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Lw.toFun x) (v.toFun x) =
      (ζ : M → ℝ) x * Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Lw.toFun x) (w.toFun x) := by
    intro x
    rw [hv, scalarSmul_toFun_apply, Integral.L2.tensorInnerPointwise_smul_right]
  -- The Green identity composed with the Dirichlet bridge.
  have hcentral : ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v x ∂μ =
      - ∫ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
          (Lw.toFun x) (v.toFun x) ∂μ := by
    have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen
      (I := I) (M := M) g m w v
    have hdir := tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
      (I := I) (M := M) g 0 m w v
    rw [hdir] at hgreen
    rw [hgreen, Integral.L2.tensorL2Inner, hLw]
  -- Continuity of the integrands.
  have hb_cont : Continuous b := hb_smooth.continuous
  have ha_cont : Continuous a := continuous_rfns_section (I := I) (M := M) g 0 m w
  have hc_cont : Continuous c := continuous_rfns_section (I := I) (M := M) g 0 (m + 1 + 1) ggw
  have hbε_cont : Continuous bε := hbε_smooth.continuous
  have hζ_cont : Continuous (ζ : M → ℝ) := by
    rw [hζ_apply]; exact hbε_cont.rpow_const (fun y => Or.inl (hbε_ne y))
  have htcdpi_cont : Continuous (tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v) :=
    tensorCovDerivPointwiseInner_continuous (I := I) (M := M) g 0 m w v
  have hζb_cont : Continuous (fun x => (ζ : M → ℝ) x * b x) := hζ_cont.mul hb_cont
  have hcrossL_cont : Continuous (tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w) := by
    have heq : tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w =
        fun x => tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v x -
          (ζ : M → ℝ) x * b x := by
      funext x; rw [hsplit x]; ring
    rw [heq]; exact htcdpi_cont.sub hζb_cont
  -- The diagonal inner product `dw = ⟨Δw, w⟩` is the smooth scalar `tensorInnerScalar g 0 m Δw w`.
  set dw : M → ℝ := fun x => Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
    (Lw.toFun x) (w.toFun x) with hdw
  have hdw_eq : dw = Integral.Connection.tensorInnerScalar (I := I) (M := M) g 0 m
      Lw.toSection w.toSection := by
    funext x
    simp only [hdw, Integral.Connection.tensorInnerScalar_apply]
    rfl
  have hdw_cont : Continuous dw := by
    rw [hdw_eq]
    exact (Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g 0 m
      Lw.toSection w.toSection).continuous
  have hζdw_cont : Continuous (fun x => (ζ : M → ℝ) x * dw x) := hζ_cont.mul hdw_cont
  -- Integrability on the closed manifold.
  have hint : ∀ f : M → ℝ, Continuous f → MeasureTheory.Integrable f μ := by
    intro f hf
    exact (hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (p := 1)).integrable
      (le_refl 1)
  -- The target right-hand integrand `F = a^{1/2}·ζ·c^{1/2}`.
  set F : M → ℝ := fun x => (a x) ^ (1 / 2 : ℝ) * (ζ : M → ℝ) x * (c x) ^ (1 / 2 : ℝ) with hF
  have hF_nonneg : ∀ x, 0 ≤ F x := fun x => by
    rw [hF]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (ha_nonneg x) _) (hζ_nonneg x))
      (Real.rpow_nonneg (hc_nonneg x) _)
  have hF_cont : Continuous F := by
    rw [hF]
    exact ((ha_cont.rpow_const (fun x => Or.inr (by norm_num))).mul hζ_cont).mul
      (hc_cont.rpow_const (fun x => Or.inr (by norm_num)))
  -- The goal left member is `∫ b·(b+ε)^{p−1} = ∫ ζ·b`.
  have hLHS_eq : (∫ x, b x * (b x + ε) ^ pm1 ∂μ) = ∫ x, (ζ : M → ℝ) x * b x ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hζ_apply, hbε]; ring
  -- The master equation: `∫ ζ·b + ∫ crossLeft = − ∫ ζ·dw`.
  have hLHS_split : (∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v x ∂μ) =
      (∫ x, (ζ : M → ℝ) x * b x ∂μ) +
        ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ := by
    rw [← MeasureTheory.integral_add (hint _ hζb_cont) (hint _ hcrossL_cont)]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit)
  have hRHS_pull : (∫ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Lw.toFun x) (v.toFun x) ∂μ) = ∫ x, (ζ : M → ℝ) x * dw x ∂μ :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpull)
  have hmaster : (∫ x, (ζ : M → ℝ) x * b x ∂μ) +
      (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ) =
      - ∫ x, (ζ : M → ℝ) x * dw x ∂μ := by
    rw [← hLHS_split, ← hRHS_pull]; exact hcentral
  -- **The regularised cross-term bound** `|crossLeft| ≤ 2(p−1)·√a·ζ·√c` (pointwise).
  -- Built from the prepend fibre-norm frame sum, the real-power chain rule
  -- `dζ = (p−1)·(b+ε)^{p−2}·db`, the Kato bound, and `b·(b+ε)^{p−2} ≤ (b+ε)^{p−1}`.
  have hcrossB : ∀ x, |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x| ≤
      2 * pm1 * F x := by
    intro x
    -- The gradient `Q = ∇w`, fibre norms `bv = rfns(∇w)(x)`, `cv = rfns(∇²w)(x)`, `av = rfns(w)(x)`.
    set Q : Integral.L2.SmoothCcTensor g 0 (m + 1) := covGrad (I := I) (M := M) g 0 m w with hQ_def
    set bfun : M → ℝ := fun y =>
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) y (Q.toSection y) with hbfun_def
    set bv : ℝ := bfun x with hbv_def
    set cv : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
        ((covGrad (I := I) (M := M) g 0 (m + 1) Q).toSection x) with hcv_def
    set av : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) with hav_def
    have hbv_nn : 0 ≤ bv := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) x (Q.toSection x)
    have hcv_nn : 0 ≤ cv := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) x _
    have hav_nn : 0 ≤ av := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m x (w.toSection x)
    have hbεx_pos : 0 < bv + ε := by linarith
    -- The displayed `F x` (defeq through the `ζ`/`a`/`c` unfoldings).
    have hFx : F x = av ^ (1 / 2 : ℝ) * (bv + ε) ^ pm1 * cv ^ (1 / 2 : ℝ) := rfl
    -- Step 1 — the cross term as `⟨∇w, P⟩`, then pointwise Cauchy–Schwarz.
    set P : Integral.L2.SmoothCcTensor g 0 (m + 1) :=
      prependCovGradSlot (I := I) (M := M) g 0 m ζ w with hP_def
    have hcross_eq : tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x =
        Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x)) :=
      tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad (I := I) (M := M) g 0 m ζ w w x
    set rP : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x (P.toSection x) with hrP_def
    have hrP_nn : 0 ≤ rP := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) x _
    have hCS2 : |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x| ≤
        Real.sqrt bv * Real.sqrt rP := by
      rw [hcross_eq]
      have hsq := Integral.L2.tensorInnerPointwise_sq_le_mul (I := I) (M := M) g 0 (m + 1) x
        (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
        (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x))
      have hQself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (Q.toSection x)) = bv := by
        rw [show bv = riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x (Q.toSection x) from rfl,
          riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x (Q.toSection x)]
      have hPself : Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x
          (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (P.toSection x)) = rP := by
        rw [show rP = riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x (P.toSection x) from rfl,
          riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x (P.toSection x)]
      rw [hQself, hPself] at hsq
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hbv_nn]
      exact Real.sqrt_le_sqrt hsq
    -- Step 2 — `rfns(P) = (∑_a (dζ(B_a x))²)·rfns(w)`.
    have hrP_eq : rP = (∑ a : Fin n,
          (extDerivFun (I := I) (ζ : M → ℝ) x
            (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) * av :=
      prependCovGradSlot_fiberNormSq_frame_sum (I := I) (M := M) g m ζ w x
    -- Step 3 — the real-power chain rule `dζ(v) = (p−1)·(bfun x + ε)^{p−2}·d(bfun)(v)`.
    have hbfun_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) bfun x := by
      have hb_eq_scalar : bfun = Integral.Connection.tensorInnerScalar (I := I) (M := M) g 0 (m + 1)
          Q.toSection Q.toSection := by
        funext y
        simp only [hbfun_def, Integral.Connection.tensorInnerScalar_apply]
        rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) y
          (Q.toSection y)]
      rw [hb_eq_scalar]
      exact (Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g 0 (m + 1)
        Q.toSection Q.toSection).mdifferentiableAt (by norm_num)
    -- The real outer map `h t = (t + ε)^{p−1}`, with `h (bfun x) = (bv + ε)^{p−1}`.
    have hbεbfun_ne : bfun x + ε ≠ 0 := ne_of_gt hbεx_pos
    have hchain : ∀ v : TangentSpace I x,
        extDerivFun (I := I) (ζ : M → ℝ) x v =
          (pm1 * (bv + ε) ^ (pm1 - 1)) * extDerivFun (I := I) bfun x v := by
      intro v
      -- `t ↦ (t+ε)^{p−1}` via the real chain rule `HasDerivAt.rpow_const`.
      have hshift : HasDerivAt (fun t : ℝ => t + ε) 1 (bfun x) :=
        (hasDerivAt_id' (bfun x)).add_const ε
      have houterReal : HasDerivAt (fun t : ℝ => (t + ε) ^ pm1)
          (1 * pm1 * (bfun x + ε) ^ (pm1 - 1)) (bfun x) :=
        hshift.rpow_const (Or.inl hbεbfun_ne)
      have houter : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t + ε) ^ pm1) (bfun x)
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
            (1 * pm1 * (bfun x + ε) ^ (pm1 - 1))) :=
        houterReal.hasFDerivAt.hasMFDerivAt
      have hcomp : HasMFDerivAt I 𝓘(ℝ, ℝ) ((fun t : ℝ => (t + ε) ^ pm1) ∘ bfun) x
          ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
              (1 * pm1 * (bfun x + ε) ^ (pm1 - 1))).comp (mfderiv I 𝓘(ℝ, ℝ) bfun x)) :=
        HasMFDerivAt.comp x houter hbfun_mdiff.hasMFDerivAt
      have hζeq : (ζ : M → ℝ) = (fun t : ℝ => (t + ε) ^ pm1) ∘ bfun := rfl
      have hext : extDerivFun (I := I) (ζ : M → ℝ) x v = mfderiv I 𝓘(ℝ, ℝ) (ζ : M → ℝ) x v := rfl
      have hCLM : (mfderiv I 𝓘(ℝ, ℝ) ((fun t : ℝ => (t + ε) ^ pm1) ∘ bfun) x) v =
          (1 * pm1 * (bfun x + ε) ^ (pm1 - 1)) * extDerivFun (I := I) bfun x v := by
        rw [hcomp.mfderiv]
        change extDerivFun (I := I) bfun x v * (1 * pm1 * (bfun x + ε) ^ (pm1 - 1)) =
          (1 * pm1 * (bfun x + ε) ^ (pm1 - 1)) * extDerivFun (I := I) bfun x v
        ring
      rw [hext, hζeq, hCLM, one_mul, hbv_def]
    -- Step 4 — Kato bound `∑_a (d(bfun)(B_a x))² ≤ 4·bv·cv`.
    have hkato : ∑ a : Fin n,
        (extDerivFun (I := I) bfun x (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2 ≤
          4 * bv * cv :=
      kato_mfderiv_riemannianFiberNormSq_frame_sum_le (I := I) (M := M) g (m + 1) Q x
    -- Step 5 — `∑_a (dζ(B_a x))² ≤ (p−1)²·((bv+ε)^{p−2})²·4·bv·cv`, then `rfns(P) ≤ … · av`.
    have hdζsum : (∑ a : Fin n,
        (extDerivFun (I := I) (ζ : M → ℝ) x
          (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) ≤
          pm1 ^ 2 * ((bv + ε) ^ (pm1 - 1)) ^ 2 * (4 * bv * cv) := by
      have hrw : (∑ a : Fin n,
          (extDerivFun (I := I) (ζ : M → ℝ) x
            (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) =
          (pm1 * (bv + ε) ^ (pm1 - 1)) ^ 2 *
            ∑ a : Fin n,
              (extDerivFun (I := I) bfun x
                (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [hchain (Integral.Connection.smoothOrthoFrame (I := I) g x a x), mul_pow]
      rw [hrw, mul_pow]
      exact mul_le_mul_of_nonneg_left hkato (by positivity)
    have hrP_bound : rP ≤ pm1 ^ 2 * ((bv + ε) ^ (pm1 - 1)) ^ 2 * (4 * bv * cv) * av := by
      rw [hrP_eq]
      calc (∑ a : Fin n,
              (extDerivFun (I := I) (ζ : M → ℝ) x
                (Integral.Connection.smoothOrthoFrame (I := I) g x a x)) ^ 2) * av
          ≤ (pm1 ^ 2 * ((bv + ε) ^ (pm1 - 1)) ^ 2 * (4 * bv * cv)) * av :=
            mul_le_mul_of_nonneg_right hdζsum hav_nn
        _ = pm1 ^ 2 * ((bv + ε) ^ (pm1 - 1)) ^ 2 * (4 * bv * cv) * av := by ring
    -- Step 6 — the numeric assembly through `√bv · √rP ≤ 2(p−1)·F x`.
    have hRHS_nn : (0 : ℝ) ≤ 2 * pm1 * F x := by
      have := hF_nonneg x; positivity
    refine le_trans hCS2 ?_
    rw [← Real.sqrt_mul hbv_nn rP,
      show 2 * pm1 * F x = Real.sqrt ((2 * pm1 * F x) ^ 2) from (Real.sqrt_sq hRHS_nn).symm]
    refine Real.sqrt_le_sqrt ?_
    have htarget_eq : (2 * pm1 * F x) ^ 2 =
        pm1 ^ 2 * (4 * av * cv) * ((bv + ε) ^ pm1) ^ 2 := by
      have hsa : (av ^ (1 / 2 : ℝ)) ^ 2 = av := by
        rw [← Real.rpow_natCast (av ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hav_nn]; norm_num
      have hsc : (cv ^ (1 / 2 : ℝ)) ^ 2 = cv := by
        rw [← Real.rpow_natCast (cv ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hcv_nn]; norm_num
      rw [hFx]
      have hexpand : (2 * pm1 * (av ^ (1 / 2 : ℝ) * (bv + ε) ^ pm1 * cv ^ (1 / 2 : ℝ))) ^ 2 =
          (2 * pm1) ^ 2 * (av ^ (1 / 2 : ℝ)) ^ 2 * ((bv + ε) ^ pm1) ^ 2 *
            (cv ^ (1 / 2 : ℝ)) ^ 2 := by ring
      rw [hexpand, hsa, hsc]; ring
    rw [htarget_eq]
    have hp2_nn : (0 : ℝ) ≤ (bv + ε) ^ (pm1 - 1) := Real.rpow_nonneg hbεx_pos.le _
    have hfac1 : bv * (bv + ε) ^ (pm1 - 1) ≤ (bv + ε) ^ pm1 := by
      have habsorb : (bv + ε) ^ pm1 = (bv + ε) * (bv + ε) ^ (pm1 - 1) := by
        rw [mul_comm, ← Real.rpow_add_one (ne_of_gt hbεx_pos) (pm1 - 1)]
        congr 1; ring
      rw [habsorb]
      exact mul_le_mul_of_nonneg_right (by linarith) hp2_nn
    have hfac0_nn : (0 : ℝ) ≤ bv * (bv + ε) ^ (pm1 - 1) := mul_nonneg hbv_nn hp2_nn
    calc bv * rP
        ≤ bv * (pm1 ^ 2 * ((bv + ε) ^ (pm1 - 1)) ^ 2 * (4 * bv * cv) * av) :=
          mul_le_mul_of_nonneg_left hrP_bound hbv_nn
      _ = pm1 ^ 2 * (4 * av * cv) * (bv * (bv + ε) ^ (pm1 - 1)) ^ 2 := by ring
      _ ≤ pm1 ^ 2 * (4 * av * cv) * ((bv + ε) ^ pm1) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ hfac0_nn hfac1 2
  -- **The `√n` rough-Laplacian term** `ζ·|dw| ≤ √n·√a·ζ·√c = √n·F`.
  have hA_bound : ∀ x, (ζ : M → ℝ) x * |dw x| ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) * F x := by
    intro x
    have hcA : |dw x| ≤ Real.sqrt (Module.finrank ℝ E : ℝ) *
        Real.sqrt (a x) * Real.sqrt (c x) :=
      rawConnLap_innerWith_sqrt_finrank_bound (I := I) (M := M) g m w x
    have hζF : (ζ : M → ℝ) x * (Real.sqrt (Module.finrank ℝ E : ℝ) *
        Real.sqrt (a x) * Real.sqrt (c x)) = Real.sqrt (Module.finrank ℝ E : ℝ) * F x := by
      rw [hF, Real.sqrt_eq_rpow (a x), Real.sqrt_eq_rpow (c x)]; ring
    calc (ζ : M → ℝ) x * |dw x|
        ≤ (ζ : M → ℝ) x * (Real.sqrt (Module.finrank ℝ E : ℝ) *
            Real.sqrt (a x) * Real.sqrt (c x)) :=
          mul_le_mul_of_nonneg_left hcA (hζ_nonneg x)
      _ = Real.sqrt (Module.finrank ℝ E : ℝ) * F x := hζF
  -- Integrate the two carrier bounds.
  have hintF : MeasureTheory.Integrable F μ := hint _ hF_cont
  have hcrossL_int_bound_neg :
      -(∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ) ≤
        2 * pm1 * ∫ x, F x ∂μ := by
    calc -(∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ)
        ≤ |∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ| := neg_le_abs _
      _ ≤ ∫ x, |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x| ∂μ :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ x, 2 * pm1 * F x ∂μ :=
          MeasureTheory.integral_mono (hint _ hcrossL_cont.abs)
            ((hintF.const_mul _)) hcrossB
      _ = 2 * pm1 * ∫ x, F x ∂μ := MeasureTheory.integral_const_mul _ _
  have hLap_int_bound :
      -(∫ x, (ζ : M → ℝ) x * dw x ∂μ) ≤
        Real.sqrt (Module.finrank ℝ E : ℝ) * ∫ x, F x ∂μ := by
    calc -(∫ x, (ζ : M → ℝ) x * dw x ∂μ)
        ≤ |∫ x, (ζ : M → ℝ) x * dw x ∂μ| := neg_le_abs _
      _ ≤ ∫ x, |(ζ : M → ℝ) x * dw x| ∂μ := MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ x, Real.sqrt (Module.finrank ℝ E : ℝ) * F x ∂μ := by
          refine MeasureTheory.integral_mono (hint _ hζdw_cont.abs) ((hintF.const_mul _))
            (fun x => ?_)
          rw [abs_mul, abs_of_nonneg (hζ_nonneg x)]
          exact hA_bound x
      _ = Real.sqrt (Module.finrank ℝ E : ℝ) * ∫ x, F x ∂μ :=
          MeasureTheory.integral_const_mul _ _
  -- Assemble: the master equation gives `∫ ζ·b = − ∫ ζ·dw − ∫ crossLeft`, bound each.
  have hζb_eq : (∫ x, (ζ : M → ℝ) x * b x ∂μ) =
      -(∫ x, (ζ : M → ℝ) x * dw x ∂μ) -
        (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ) := by
    have := hmaster; linarith [this]
  -- The two-sided assembled bound `∫ ζ·b ≤ (2(p−1)+√n)·∫ F`.
  have hassembled : (∫ x, (ζ : M → ℝ) x * b x ∂μ) ≤
      (2 * pm1 + Real.sqrt (Module.finrank ℝ E : ℝ)) * ∫ x, F x ∂μ := by
    rw [hζb_eq]
    calc -(∫ x, (ζ : M → ℝ) x * dw x ∂μ) -
            (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ)
        ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * (∫ x, F x ∂μ) +
            2 * pm1 * (∫ x, F x ∂μ) := by
          have h1 := hLap_int_bound
          have h2 := hcrossL_int_bound_neg
          linarith [h1, h2]
      _ = (2 * pm1 + Real.sqrt (Module.finrank ℝ E : ℝ)) * (∫ x, F x ∂μ) := by ring
  -- The goal is defeq to `∫ b·(b+ε)^{p−1} ≤ (2(p−1)+√n)·∫ F`; `hassembled` after `hLHS_eq`.
  change (∫ x, b x * (b x + ε) ^ pm1 ∂μ) ≤
      (2 * pm1 + Real.sqrt (Module.finrank ℝ E : ℝ)) * ∫ x, F x ∂μ
  rw [hLHS_eq]
  exact hassembled

set_option maxHeartbeats 1200000 in
/-- **The `ε → 0` controlled limit of the finite-factor weighted IBP.**

The two dominated-convergence limits, along the regularising sequence `εₙ = 1/(n+1) → 0⁺`, that
pass the regularised inequality (child A) to the unregularised conclusion.  On the closed manifold
the integrands are continuous and uniformly dominated for `n` large (`(b + εₙ)^{p-1} ≤ (b + 1)^{p-1}`
since `p - 1 > 0` and `εₙ ≤ 1`, and `(b + εₙ)^{p-1} → b^{p-1}` pointwise, including `b = 0` via
`p - 1 > 0`), so
```
∫ b·(b + εₙ)^{p-1} → ∫ b^p  and
∫ (rfns w)^{1/2}·(b + εₙ)^{p-1}·(rfns ∇²w)^{1/2} → ∫ (rfns w)^{1/2}·b^{p-1}·(rfns ∇²w)^{1/2}.
```
Proven outright by Mathlib's dominated convergence `tendsto_integral_of_dominated_convergence`
twice, with the continuous compactly-supported dominating function `(rfns w)^{1/2}·(b+1)^{p-1}·…`
and the pointwise `rpow` limit `Filter.Tendsto.rpow_const`; **general analytic infrastructure**
(regularised `Lᵖ` covariant integrand `ε → 0` limit) promoted alongside child A. -/
private theorem weightedCovIBP_lpFiberJet_fin_regLimit
    (g : SmoothRiemannianMetric I M) (k m i : ℕ) (_hk : 1 ≤ k) (_hi : 1 ≤ i) (_hik : i + 1 < k)
    (w : Integral.L2.SmoothCcTensor g 0 m) :
    Filter.Tendsto
        (fun n : ℕ => ∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) *
            ((riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) + 1 / ((n : ℝ) + 1))
              ^ ((k : ℝ) / (i + 1) - 1)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g))
        Filter.atTop
        (𝓝 (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / (i + 1))
          ∂(Integral.Measure.riemannianVolumeMeasure I M g))) ∧
      Filter.Tendsto
        (fun n : ℕ => ∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x))
              ^ (1 / 2 : ℝ) *
            ((riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) + 1 / ((n : ℝ) + 1))
              ^ ((k : ℝ) / (i + 1) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (m + 1)
                (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ (1 / 2 : ℝ)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g))
        Filter.atTop
        (𝓝 (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) ^ (1 / 2 : ℝ) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / (i + 1) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (m + 1)
                (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ (1 / 2 : ℝ)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g))) := by
  classical
  haveI : MeasureTheory.IsFiniteMeasure (Integral.Measure.riemannianVolumeMeasure I M g) :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set μ : MeasureTheory.Measure M := Integral.Measure.riemannianVolumeMeasure I M g with hμ
  set p : ℝ := (k : ℝ) / (i + 1) with hp_def
  have hi1R : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hp1 : 1 < p := by
    rw [hp_def, lt_div_iff₀ hi1R, one_mul]; exact_mod_cast _hik
  have hp0 : 0 < p := lt_trans one_pos hp1
  have hpm1_pos : (0 : ℝ) < p - 1 := by linarith
  have hpm1_nn : (0 : ℝ) ≤ p - 1 := le_of_lt hpm1_pos
  -- The pointwise fibre norms (continuous, nonnegative).
  set a : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) with ha
  set b : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
    ((covGrad (I := I) (M := M) g 0 m w).toSection x) with hb
  set c : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
    ((covGrad (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w)).toSection x)
    with hc
  have ha0 : ∀ x, 0 ≤ a x := fun x => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m x _
  have hb0 : ∀ x, 0 ≤ b x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) x _
  have hc0 : ∀ x, 0 ≤ c x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) x _
  have hac : Continuous a := continuous_rfns_section (I := I) (M := M) g 0 m w
  have hbc : Continuous b :=
    continuous_rfns_section (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w)
  have hcc : Continuous c :=
    continuous_rfns_section (I := I) (M := M) g 0 (m + 1 + 1)
      (covGrad (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w))
  -- The regularising sequence `εₙ = 1/(n+1) ∈ (0, 1]`.
  have hε_pos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hε_le_one : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    intro n
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hε_tendsto : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- The pointwise rpow limit `(b x + εₙ)^{p−1} → (b x)^{p−1}`.
  have hrpow_lim : ∀ x : M, Filter.Tendsto
      (fun n : ℕ => (b x + 1 / ((n : ℝ) + 1)) ^ (p - 1)) Filter.atTop (𝓝 ((b x) ^ (p - 1))) := by
    intro x
    have hbase : Filter.Tendsto (fun n : ℕ => b x + 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 (b x)) := by
      have := hε_tendsto
      simpa using (tendsto_const_nhds.add this)
    exact hbase.rpow_const (Or.inr hpm1_nn)
  -- The uniform domination `(b x + εₙ)^{p−1} ≤ (b x + 1)^{p−1}`.
  have hbεn_base_nn : ∀ (n : ℕ) (x : M), 0 ≤ b x + 1 / ((n : ℝ) + 1) := fun n x => by
    have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    linarith [hb0 x]
  have hdom_rpow : ∀ (n : ℕ) (x : M),
      (b x + 1 / ((n : ℝ) + 1)) ^ (p - 1) ≤ (b x + 1) ^ (p - 1) := by
    intro n x
    apply Real.rpow_le_rpow (hbεn_base_nn n x) _ hpm1_nn
    linarith [hε_le_one n]
  have hbε1_nn : ∀ x : M, 0 ≤ (b x + 1) ^ (p - 1) := fun x =>
    Real.rpow_nonneg (by linarith [hb0 x]) _
  have hbεn_nn : ∀ (n : ℕ) (x : M), 0 ≤ (b x + 1 / ((n : ℝ) + 1)) ^ (p - 1) := fun n x =>
    Real.rpow_nonneg (hbεn_base_nn n x) _
  -- Integrability on the closed manifold (continuous, compact support).
  have hint : ∀ f : M → ℝ, Continuous f → MeasureTheory.Integrable f μ := by
    intro f hf
    exact (hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (p := 1)).integrable
      (le_refl 1)
  have hbε1_cont : Continuous (fun x => (b x + 1) ^ (p - 1)) :=
    (hbc.add continuous_const).rpow_const (fun x => Or.inr hpm1_nn)
  have ha12_cont : Continuous (fun x => (a x) ^ (1 / 2 : ℝ)) :=
    hac.rpow_const (fun x => Or.inr (by norm_num))
  have hc12_cont : Continuous (fun x => (c x) ^ (1 / 2 : ℝ)) :=
    hcc.rpow_const (fun x => Or.inr (by norm_num))
  have ha12_nn : ∀ x, 0 ≤ (a x) ^ (1 / 2 : ℝ) := fun x => Real.rpow_nonneg (ha0 x) _
  have hc12_nn : ∀ x, 0 ≤ (c x) ^ (1 / 2 : ℝ) := fun x => Real.rpow_nonneg (hc0 x) _
  -- The pointwise identity `b·b^{p−1} = b^p`, integrated.
  have hbp : (∫ x, b x * (b x) ^ (p - 1) ∂μ) = ∫ x, (b x) ^ p ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    have hadd := Real.rpow_one_add' (hb0 x) (show (1 : ℝ) + (p - 1) ≠ 0 by linarith)
    rw [show (1 : ℝ) + (p - 1) = p from by ring] at hadd
    exact hadd.symm
  refine ⟨?_, ?_⟩
  · -- **LHS limit:** `∫ b·(b+εₙ)^{p−1} → ∫ b·b^{p−1} = ∫ b^p`.
    have hconv : Filter.Tendsto
        (fun n : ℕ => ∫ x, b x * (b x + 1 / ((n : ℝ) + 1)) ^ (p - 1) ∂μ) Filter.atTop
        (𝓝 (∫ x, b x * (b x) ^ (p - 1) ∂μ)) :=
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (bound := fun x => b x * (b x + 1) ^ (p - 1))
        (fun n => (hbc.mul ((hbc.add continuous_const).rpow_const
          (fun x => Or.inr hpm1_nn))).aestronglyMeasurable)
        (hint _ (hbc.mul hbε1_cont))
        (fun n => Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hb0 x) (hbεn_nn n x))]
          exact mul_le_mul_of_nonneg_left (hdom_rpow n x) (hb0 x)))
        (Filter.Eventually.of_forall (fun x => tendsto_const_nhds.mul (hrpow_lim x)))
    rw [hbp] at hconv
    exact hconv
  · -- **RHS limit:** `∫ a^{1/2}·(b+εₙ)^{p−1}·c^{1/2} → ∫ a^{1/2}·b^{p−1}·c^{1/2}`.
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (bound := fun x => (a x) ^ (1 / 2 : ℝ) * (b x + 1) ^ (p - 1) * (c x) ^ (1 / 2 : ℝ))
      (fun n => ((ha12_cont.mul ((hbc.add continuous_const).rpow_const
        (fun x => Or.inr hpm1_nn))).mul hc12_cont).aestronglyMeasurable)
      (hint _ ((ha12_cont.mul hbε1_cont).mul hc12_cont))
      (fun n => Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (mul_nonneg (ha12_nn x) (hbεn_nn n x)) (hc12_nn x))]
        apply mul_le_mul_of_nonneg_right _ (hc12_nn x)
        exact mul_le_mul_of_nonneg_left (hdom_rpow n x) (ha12_nn x)))
      (Filter.Eventually.of_forall (fun x =>
        (tendsto_const_nhds.mul (hrpow_lim x)).mul tendsto_const_nhds))

/-- **The finite-factor weighted covariant `Lᵖ` integration-by-parts inequality.**  With
`∇ = covGrad`, `a := rfns(w)`, `b := rfns(∇w)`, `c := rfns(∇²w)` and `p := k/(i+1) > 1` (finite
regime `i + 1 < k`),
```
∫ b^p ≤ (2(p-1) + √(finrank)) · ∫ a^{1/2}·b^{p-1}·c^{1/2}.
```
This is honest limit-glue: the regularised inequality `weightedCovIBP_lpFiberJet_fin_regIneq` at the
sequence `εₙ = 1/(n+1) > 0` is passed through the `ε → 0` dominated-convergence limits
`weightedCovIBP_lpFiberJet_fin_regLimit` by `le_of_tendsto_of_tendsto'`.  Both children are now
proven outright, so this finite-factor weighted IBP is `sorry`-free. -/
private theorem weightedCovIBP_lpFiberJet_fin
    (g : SmoothRiemannianMetric I M) (k m i : ℕ) (_hk : 1 ≤ k) (_hi : 1 ≤ i) (_hik : i + 1 < k)
    (w : Integral.L2.SmoothCcTensor g 0 m) :
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
            ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / (i + 1))
        ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ≤
      (2 * ((k : ℝ) / (i + 1) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) *
        ∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) ^ (1 / 2 : ℝ) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / (i + 1) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (m + 1)
                (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ (1 / 2 : ℝ)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g) := by
  -- The corrected Hamilton IBP constant at this order, `D' = 2(p-1)+√n` with `p = k/(i+1)`.
  set D' : ℝ := 2 * ((k : ℝ) / (i + 1) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ) with hD'
  obtain ⟨hLlim, hRlim⟩ :=
    weightedCovIBP_lpFiberJet_fin_regLimit (I := I) (M := M) g k m i _hk _hi _hik w
  -- The regularised inequality `child A` at each `εₙ = 1/(n+1) > 0`.
  have hreg : ∀ n : ℕ, (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) *
            ((riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) + 1 / ((n : ℝ) + 1))
              ^ ((k : ℝ) / (i + 1) - 1)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ≤
        D' * ∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) ^ (1 / 2 : ℝ) *
            ((riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) + 1 / ((n : ℝ) + 1))
              ^ ((k : ℝ) / (i + 1) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (m + 1)
                (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ (1 / 2 : ℝ)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g) := by
    intro n
    have hεpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact weightedCovIBP_lpFiberJet_fin_regIneq (I := I) (M := M) g k m i _hk _hi _hik w
      (1 / ((n : ℝ) + 1)) hεpos
  -- Pass the inequality through the `n → ∞` limit: LHS → `∫ b^p`, RHS → `D'·∫ a^{1/2}b^{p-1}c^{1/2}`.
  exact le_of_tendsto_of_tendsto' hLlim (hRlim.const_mul D') hreg

/-- **(POSIT — the weighted covariant `Lᵖ` integration-by-parts inequality, `L^∞`-factor form.)**

The order-`0` instance of the covariant IBP engine, where the lowest factor `|w|` is replaced by a
uniform `L^∞` bound `A ≥ 0` on the fibre norm of `w` (`rfns(w) ≤ A²` pointwise).  With `∇ = covGrad`,
`b := rfns(∇w)`, `c := rfns(∇²w)`, at the top exponent `p := k ≥ 1`,
```
∫ b^k ≤ (2(k-1) + √(finrank)) · A · ∫ b^{k-1} · c^{1/2},
```
i.e. `∫ |∇w|^{2k} ≤ (2(k-1)+√n)·A·∫ |∇w|^{2k-2}·|∇²w|`, the corrected Hamilton constant (the `√n` is the
irreducible trace factor from the diagonal frame trace of `∇²w`).  It is assembled from the covariant
Green identity (`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen`) on the weight `v = ζ·w`
with `ζ = b^{k-1}`, the Dirichlet bridge, the metric Leibniz split of `∫⟨∇w, ∇(ζw)⟩` into `∫ b^k` plus
the cross term `tensorCovDerivCrossLeft`, and the two pointwise carriers
`covDerivCrossLeft_weight_bound` (the `2(k-1)` term) and `rawConnLap_innerWith_sqrt_finrank_bound`
(the `√n` term); consumers transitively depend on the `sorryAx` of those two carriers.  **General
analytic infrastructure** (weighted-`Lᵖ` covariant IBP, `L^∞`-factor) to be promoted alongside the
finite form. -/
private theorem weightedCovIBP_lpFiberJet_sup
    (g : SmoothRiemannianMetric I M) (k m : ℕ) (_hk : 1 ≤ k)
    (w : Integral.L2.SmoothCcTensor g 0 m) (A : ℝ) (_hA : 0 ≤ A)
    (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) ≤ A ^ 2) :
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
            ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / 1)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ≤
      (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) * A *
        ∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
              ((covGrad (I := I) (M := M) g 0 (m + 1)
                (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ (1 / 2 : ℝ)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g) := by
  classical
  haveI : MeasureTheory.IsFiniteMeasure (Integral.Measure.riemannianVolumeMeasure I M g) :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set μ : MeasureTheory.Measure M := Integral.Measure.riemannianVolumeMeasure I M g with hμ
  -- The gradient tensors and the rough Laplacian.
  set gw : Integral.L2.SmoothCcTensor g 0 (m + 1) := covGrad (I := I) (M := M) g 0 m w with hgw
  set ggw : Integral.L2.SmoothCcTensor g 0 (m + 1 + 1) :=
    covGrad (I := I) (M := M) g 0 (m + 1) gw with hggw
  set Lw : Integral.L2.SmoothCcTensor g 0 m :=
    rawTensorConnLapSmooth (I := I) g 0 m w with hLw
  -- The pointwise fibre norms `b = rfns(∇w)`, `c = rfns(∇²w)`.
  set b : M → ℝ := fun y => riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) y (gw.toSection y)
    with hb
  set c : M → ℝ := fun y =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) y (ggw.toSection y) with hc
  have hb_nonneg : ∀ y, 0 ≤ b y := fun y =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) y (gw.toSection y)
  have hc_nonneg : ∀ y, 0 ≤ c y := fun y =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) y (ggw.toSection y)
  -- `b` agrees pointwise with the smooth scalar `tensorInnerScalar g 0 (m+1) (∇w) (∇w)`.
  have hb_eq_scalar : b = Integral.Connection.tensorInnerScalar (I := I) (M := M) g 0 (m + 1)
      gw.toSection gw.toSection := by
    funext y
    simp only [hb, Integral.Connection.tensorInnerScalar_apply]
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) y
      (gw.toSection y)]
  have hb_smooth : ContMDiff I 𝓘(ℝ) ∞ b := by
    rw [hb_eq_scalar]
    exact Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g 0 (m + 1)
      gw.toSection gw.toSection
  -- The smooth weight `ζ = b^{k-1}` (natural power; smooth everywhere).
  set ζ : C^∞⟮I, M; ℝ⟯ := ⟨fun y => b y ^ (k - 1), hb_smooth.pow (k - 1)⟩ with hζ
  have hζ_apply : (ζ : M → ℝ) = fun y => b y ^ (k - 1) := rfl
  have hζ_nonneg : ∀ y, 0 ≤ (ζ : M → ℝ) y := by
    intro y; rw [hζ_apply]; exact pow_nonneg (hb_nonneg y) _
  -- `ζ y = (b y)^{(k:ℝ)-1}` as a real power.
  have hζ_rpow : ∀ y, (ζ : M → ℝ) y = (b y) ^ ((k : ℝ) - 1) := by
    intro y
    simp only [hζ_apply]
    rw [← Real.rpow_natCast (b y) (k - 1)]
    congr 1
    rw [Nat.cast_sub _hk, Nat.cast_one]
  -- The weight tensor `v = ζ • w`.
  set v : Integral.L2.SmoothCcTensor g 0 m :=
    scalarSmul (I := I) (M := M) g 0 m ζ w with hv
  -- The diagonal pointwise gradient inner product is `b`.
  have hdiag : ∀ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w w x = b x := by
    intro x
    rw [tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad (I := I) (M := M) g 0 m w w x,
      ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (m + 1) x
        ((covGrad (I := I) (M := M) g 0 m w).toSection x)]
  -- The metric Leibniz split (right slot): `⟨∇w, ∇(ζw)⟩ = ζ·⟨∇w,∇w⟩ + ⟨∇w, dζ⊗w⟩`.
  have hsplit : ∀ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v x =
      (ζ : M → ℝ) x * b x + tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x := by
    intro x
    rw [tensorCovDerivPointwiseInner_def, tensorCovDerivCrossLeft_def, ← hdiag,
      tensorCovDerivPointwiseInner_def, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hv, tensorCovDerivAt_scalarSmul (I := I) (M := M) g 0 m ζ w x
      ((Integral.Measure.chartModelBasis E) j)]
    have hwx : Tensor0SBundle.TensorRSSpace.toModel (w.toSection x) = w.toFun x := rfl
    simp only [Tensor0SBundle.TensorRSSpace.toModel_add, Tensor0SBundle.TensorRSSpace.toModel_smul,
      hwx, Integral.L2.tensorInnerPointwise_add_right, Integral.L2.tensorInnerPointwise_smul_right]
    ring
  -- The right-hand scalar pull-out: `⟨Δw, ζw⟩ = ζ·⟨Δw, w⟩` pointwise.
  have hpull : ∀ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Lw.toFun x) (v.toFun x) =
      (ζ : M → ℝ) x * Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Lw.toFun x) (w.toFun x) := by
    intro x
    rw [hv, scalarSmul_toFun_apply, Integral.L2.tensorInnerPointwise_smul_right]
  -- The Green identity composed with the Dirichlet bridge.
  have hcentral : ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v x ∂μ =
      - ∫ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
          (Lw.toFun x) (v.toFun x) ∂μ := by
    have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen
      (I := I) (M := M) g m w v
    have hdir := tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
      (I := I) (M := M) g 0 m w v
    rw [hdir] at hgreen
    rw [hgreen, Integral.L2.tensorL2Inner, hLw]
  -- Continuity of the integrands (everything is continuous on the compact manifold `M`).
  have hb_cont : Continuous b := hb_smooth.continuous
  have hc_cont : Continuous c := continuous_rfns_section (I := I) (M := M) g 0 (m + 1 + 1) ggw
  have hζ_cont : Continuous (ζ : M → ℝ) := by
    simp only [hζ_apply]; exact hb_cont.pow (k - 1)
  have htcdpi_cont : Continuous (tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v) :=
    tensorCovDerivPointwiseInner_continuous (I := I) (M := M) g 0 m w v
  have hζb_cont : Continuous (fun x => (ζ : M → ℝ) x * b x) := hζ_cont.mul hb_cont
  -- The cross term is continuous (as `tCDPI w v − ζ·b`).
  have hcrossL_cont : Continuous (tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w) := by
    have heq : tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w =
        fun x => tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v x -
          (ζ : M → ℝ) x * b x := by
      funext x; rw [hsplit x]; ring
    rw [heq]; exact htcdpi_cont.sub hζb_cont
  -- The diagonal inner product `dw = ⟨Δw, w⟩` is the smooth scalar `tensorInnerScalar g 0 m Δw w`.
  set dw : M → ℝ := fun x => Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
    (Lw.toFun x) (w.toFun x) with hdw
  have hdw_eq : dw = Integral.Connection.tensorInnerScalar (I := I) (M := M) g 0 m
      Lw.toSection w.toSection := by
    funext x
    simp only [hdw, Integral.Connection.tensorInnerScalar_apply]
    rfl
  have hdw_cont : Continuous dw := by
    rw [hdw_eq]
    exact (Integral.Connection.tensorInnerScalar_contMDiff (I := I) (M := M) g 0 m
      Lw.toSection w.toSection).continuous
  have hζdw_cont : Continuous (fun x => (ζ : M → ℝ) x * dw x) := hζ_cont.mul hdw_cont
  -- Integrability on the closed manifold.
  have hint : ∀ f : M → ℝ, Continuous f → MeasureTheory.Integrable f μ := by
    intro f hf
    exact (hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (p := 1)).integrable
      (le_refl 1)
  -- The target right-hand integrand `F = b^{k-1} · c^{1/2} = ζ · √c`.
  set F : M → ℝ := fun x => (b x) ^ ((k : ℝ) - 1) * (c x) ^ (1 / 2 : ℝ) with hF
  have hF_nonneg : ∀ x, 0 ≤ F x := fun x =>
    mul_nonneg (Real.rpow_nonneg (hb_nonneg x) _) (Real.rpow_nonneg (hc_nonneg x) _)
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast _hk
    linarith
  have hF_cont : Continuous F :=
    (hb_cont.rpow_const (fun x => Or.inr hk1)).mul
      (hc_cont.rpow_const (fun x => Or.inr (by norm_num)))
  have hζsqrtc : ∀ x, (ζ : M → ℝ) x * Real.sqrt (c x) = F x := by
    intro x
    rw [hF, hζ_rpow x, Real.sqrt_eq_rpow]
  -- The goal left member is `∫ ζ·b`.
  have hLHS_eq : (∫ x, (b x) ^ ((k : ℝ) / 1) ∂μ) = ∫ x, (ζ : M → ℝ) x * b x ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hζ_apply, div_one]
    rw [Real.rpow_natCast (b x) k]
    have hkpow : (b x) ^ (k - 1) * b x = (b x) ^ k := by
      rw [← pow_succ]; congr 1; omega
    rw [hkpow]
  -- The master equation: `∫ ζ·b + ∫ crossLeft = − ∫ ζ·dw`.
  have hLHS_split : (∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 m w v x ∂μ) =
      (∫ x, (ζ : M → ℝ) x * b x ∂μ) +
        ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ := by
    rw [← MeasureTheory.integral_add (hint _ hζb_cont) (hint _ hcrossL_cont)]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit)
  have hRHS_pull : (∫ x, Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 m x
        (Lw.toFun x) (v.toFun x) ∂μ) = ∫ x, (ζ : M → ℝ) x * dw x ∂μ :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpull)
  have hmaster : (∫ x, (ζ : M → ℝ) x * b x ∂μ) +
      (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ) =
      - ∫ x, (ζ : M → ℝ) x * dw x ∂μ := by
    rw [← hLHS_split, ← hRHS_pull]; exact hcentral
  -- The two pointwise carrier bounds, integrated.
  have hA_nonneg : (0 : ℝ) ≤ A := _hA
  -- Bound the cross-term integral (child B).
  have hcrossB : ∀ x, |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x| ≤
      2 * ((k : ℝ) - 1) * A * F x := by
    intro x
    have hb' := covDerivCrossLeft_weight_bound (I := I) (M := M) g k m _hk w A _hA _hsup ζ
      (by simp only [hζ_apply, hb, hgw]) x
    calc |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x|
        ≤ 2 * ((k : ℝ) - 1) * A *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x (gw.toSection x))
              ^ ((k : ℝ) - 1) *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x (ggw.toSection x))
              ^ (1 / 2 : ℝ) := hb'
      _ = 2 * ((k : ℝ) - 1) * A * F x := by simp only [hF]; ring
  -- Bound the Laplacian integral (child A) after the `√a ≤ A` reduction.
  have hsqrt_a_le : ∀ x, Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 m x
      (w.toSection x)) ≤ A := by
    intro x
    rw [← Real.sqrt_sq _hA]
    exact Real.sqrt_le_sqrt (_hsup x)
  have hA_bound : ∀ x, (ζ : M → ℝ) x * |dw x| ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) * A * F x := by
    intro x
    have hcA : |dw x| ≤ Real.sqrt (Module.finrank ℝ E : ℝ) *
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) *
        Real.sqrt (c x) :=
      rawConnLap_innerWith_sqrt_finrank_bound (I := I) (M := M) g m w x
    have hsqc_nonneg : (0 : ℝ) ≤ Real.sqrt (c x) := Real.sqrt_nonneg _
    have hkey : |dw x| ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * A * Real.sqrt (c x) := by
      calc |dw x| ≤ Real.sqrt (Module.finrank ℝ E : ℝ) *
              Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) *
              Real.sqrt (c x) := hcA
        _ ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * A * Real.sqrt (c x) := by
            apply mul_le_mul_of_nonneg_right _ hsqc_nonneg
            apply mul_le_mul_of_nonneg_left (hsqrt_a_le x) (Real.sqrt_nonneg _)
    calc (ζ : M → ℝ) x * |dw x|
        ≤ (ζ : M → ℝ) x * (Real.sqrt (Module.finrank ℝ E : ℝ) * A * Real.sqrt (c x)) :=
          mul_le_mul_of_nonneg_left hkey (hζ_nonneg x)
      _ = Real.sqrt (Module.finrank ℝ E : ℝ) * A * ((ζ : M → ℝ) x * Real.sqrt (c x)) := by ring
      _ = Real.sqrt (Module.finrank ℝ E : ℝ) * A * F x := by rw [hζsqrtc x]
  -- Integrate the two carrier bounds.
  have hintF : MeasureTheory.Integrable F μ := hint _ hF_cont
  have hcrossL_int_bound :
      (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ) ≤
        2 * ((k : ℝ) - 1) * A * ∫ x, F x ∂μ := by
    calc (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ)
        ≤ ∫ x, 2 * ((k : ℝ) - 1) * A * F x ∂μ := by
          refine MeasureTheory.integral_mono (hint _ hcrossL_cont)
            ((hintF.const_mul _)) (fun x => ?_)
          exact le_trans (le_abs_self _) (hcrossB x)
      _ = 2 * ((k : ℝ) - 1) * A * ∫ x, F x ∂μ := MeasureTheory.integral_const_mul _ _
  have hcrossL_int_bound_neg :
      -(∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ) ≤
        2 * ((k : ℝ) - 1) * A * ∫ x, F x ∂μ := by
    calc -(∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ)
        ≤ |∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ| := neg_le_abs _
      _ ≤ ∫ x, |tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x| ∂μ :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ x, 2 * ((k : ℝ) - 1) * A * F x ∂μ :=
          MeasureTheory.integral_mono (hint _ hcrossL_cont.abs)
            ((hintF.const_mul _)) hcrossB
      _ = 2 * ((k : ℝ) - 1) * A * ∫ x, F x ∂μ := MeasureTheory.integral_const_mul _ _
  have hLap_int_bound :
      -(∫ x, (ζ : M → ℝ) x * dw x ∂μ) ≤
        Real.sqrt (Module.finrank ℝ E : ℝ) * A * ∫ x, F x ∂μ := by
    calc -(∫ x, (ζ : M → ℝ) x * dw x ∂μ)
        ≤ |∫ x, (ζ : M → ℝ) x * dw x ∂μ| := neg_le_abs _
      _ ≤ ∫ x, |(ζ : M → ℝ) x * dw x| ∂μ := MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ x, Real.sqrt (Module.finrank ℝ E : ℝ) * A * F x ∂μ := by
          refine MeasureTheory.integral_mono (hint _ hζdw_cont.abs) ((hintF.const_mul _))
            (fun x => ?_)
          rw [abs_mul, abs_of_nonneg (hζ_nonneg x)]
          exact hA_bound x
      _ = Real.sqrt (Module.finrank ℝ E : ℝ) * A * ∫ x, F x ∂μ :=
          MeasureTheory.integral_const_mul _ _
  -- Assemble: rewrite the goal LHS as `∫ ζ·b`, substitute the master equation, and bound.
  rw [show (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x (gw.toSection x))
          ^ ((k : ℝ) / 1) ∂μ) = ∫ x, (b x) ^ ((k : ℝ) / 1) ∂μ from rfl, hLHS_eq]
  have hζb_eq : (∫ x, (ζ : M → ℝ) x * b x ∂μ) =
      -(∫ x, (ζ : M → ℝ) x * dw x ∂μ) -
        (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ) := by
    have := hmaster; linarith [this]
  rw [hζb_eq]
  have hRHS_eq : (∫ x, (b x) ^ ((k : ℝ) - 1) *
        (c x) ^ (1 / 2 : ℝ) ∂μ) = ∫ x, F x ∂μ := rfl
  calc -(∫ x, (ζ : M → ℝ) x * dw x ∂μ) -
          (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g 0 m ζ w w x ∂μ)
      ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * A * (∫ x, F x ∂μ) +
          2 * ((k : ℝ) - 1) * A * (∫ x, F x ∂μ) := by
        have h1 := hLap_int_bound
        have h2 := hcrossL_int_bound_neg
        linarith [h1, h2]
    _ = (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) * A * (∫ x, F x ∂μ) := by ring
    _ = (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) * A *
          ∫ x, (b x) ^ ((k : ℝ) - 1) * (c x) ^ (1 / 2 : ℝ) ∂μ := by rw [hRHS_eq]

/-- **(POSIT — the sub-unit second-order `Lᵖ` log-convexity bound, with a nonnegative constant.)**

The genuine analytic kernel of the sub-unit interpolation step: the Gagliardo–Nirenberg
second-order interpolation in the *sub-unit* range `k ≤ i + 1` (where the target exponent
`q₁ = 2k/(i+1) ≤ 2` and the standard covariant integration-by-parts is no longer available), here
with a single nonnegative multiplier `K_sub ≥ 0` uniform in `(m, w, i)`:
```
‖∇w‖_{L^{2k/(i+1)}}² ≤ K_sub · ‖w‖_{L^{2k/i}} · ‖∇²w‖_{L^{2k/(i+2)}}
```
(written through the squared fibre norms with the ladder exponents).  In this regime the inequality
follows from the convexity of `p ↦ log‖f‖_{L^{1/p}}` (Lyapunov / log-convexity of `Lᵖ` norms) rather
than from IBP — the pointwise bound `|∇w|² ≤ |w|·|∇²w|` is *false* on a curved manifold, so it must
be the integral/convexity inequality; it is tight, attaining equality on a single Fourier mode of the
flat torus.  Its body is `sorry`: the genuine sub-unit-exponent `Lᵖ` interpolation (the
log-convexity frontier), which the project does not carry; consumers transitively depend on its
`sorryAx`.  **General analytic infrastructure** (`Lᵖ` log-convexity / sub-unit interpolation) to be
promoted to a dedicated `Analysis/Sobolev` or `Analysis/Integration` file. -/
private theorem lpFiberJet_secondOrder_subunit_logConvex_bound
    (g : SmoothRiemannianMetric I M) (k : ℕ) (_hk : 1 ≤ k) :
    ∃ K_sub : ℝ, 0 ≤ K_sub ∧
      ∀ (m : ℕ) (w : Integral.L2.SmoothCcTensor g 0 m) (i : ℕ), 1 ≤ i → k ≤ i + 1 →
        ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / (i + 1))
            ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ (((i : ℝ) + 1) / (2 * k))) ^ 2 ≤
          K_sub *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) ^ ((k : ℝ) / i)
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * k))) *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
                  ((covGrad (I := I) (M := M) g 0 (m + 1)
                    (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ ((k : ℝ) / (i + 2))
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ (((i : ℝ) + 2) / (2 * k))) := by
  sorry

/-- **The sub-unit second-order covariant `Lᵖ` interpolation step.**  The continuation of the
finite second-order interpolation into the sub-unit range `k ≤ i + 1`, with a multiplier `K'' ≥ 1`
uniform in `(m, w, i)`.  This is the constant-normalisation glue over the genuine analytic kernel
`lpFiberJet_secondOrder_subunit_logConvex_bound`: its nonnegative multiplier `K_sub` is upgraded to
`max K_sub 1 ≥ 1`, the inequality surviving the upgrade by nonnegativity of the two right factors.
Consumers transitively depend on the `sorryAx` of that kernel. -/
private theorem secondOrderInterp_lpFiberJet_fin_lowExp
    (g : SmoothRiemannianMetric I M) (k : ℕ) (_hk : 1 ≤ k) :
    ∃ K'' : ℝ, 1 ≤ K'' ∧
      ∀ (m : ℕ) (w : Integral.L2.SmoothCcTensor g 0 m) (i : ℕ), 1 ≤ i → k ≤ i + 1 →
        ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / (i + 1))
            ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ (((i : ℝ) + 1) / (2 * k))) ^ 2 ≤
          K'' *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) ^ ((k : ℝ) / i)
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * k))) *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
                  ((covGrad (I := I) (M := M) g 0 (m + 1)
                    (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ ((k : ℝ) / (i + 2))
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ (((i : ℝ) + 2) / (2 * k))) := by
  obtain ⟨K_sub, hK_sub0, hbound⟩ :=
    lpFiberJet_secondOrder_subunit_logConvex_bound (I := I) (M := M) g k _hk
  refine ⟨max K_sub 1, le_max_right _ _, fun m w i hi1 hik => ?_⟩
  -- Nonnegativity of the two right `rpow` factors `Ia^{i/(2k)}`, `Ic^{(i+2)/(2k)}`.
  have hIa_nn : (0 : ℝ) ≤ (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x))
        ^ ((k : ℝ) / i) ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * k)) :=
    Real.rpow_nonneg (MeasureTheory.integral_nonneg
      (fun x => Real.rpow_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m x _) _)) _
  have hIc_nn : (0 : ℝ) ≤ (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
        ((covGrad (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w)).toSection x))
        ^ ((k : ℝ) / (i + 2)) ∂(Integral.Measure.riemannianVolumeMeasure I M g))
        ^ (((i : ℝ) + 2) / (2 * k)) :=
    Real.rpow_nonneg (MeasureTheory.integral_nonneg
      (fun x => Real.rpow_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) x _)
        _)) _
  calc ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / (i + 1))
            ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ (((i : ℝ) + 1) / (2 * k))) ^ 2
      ≤ K_sub *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) ^ ((k : ℝ) / i)
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * k))) *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
                  ((covGrad (I := I) (M := M) g 0 (m + 1)
                    (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ ((k : ℝ) / (i + 2))
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ (((i : ℝ) + 2) / (2 * k))) :=
        hbound m w i hi1 hik
    _ ≤ max K_sub 1 *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) ^ ((k : ℝ) / i)
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * k))) *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
                  ((covGrad (I := I) (M := M) g 0 (m + 1)
                    (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ ((k : ℝ) / (i + 2))
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ (((i : ℝ) + 2) / (2 * k))) := by
        apply mul_le_mul_of_nonneg_right _ hIc_nn
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hIa_nn

end SecondOrderInterpCore

set_option maxHeartbeats 1600000 in
/-- **(POSIT — the generic single-tensor second-order covariant `L^p` interpolation step, finite
lower factor.)**

The genuine analytic engine, isolated to a *single* smooth compactly-supported tensor `w` and a
*single* interpolation step (one covariant integration by parts against the regularised weight
`(|∇w|²+ε)^{(p₁-2)/2}` plus a three-function Hölder at the conjugate triple, in the `ε → 0` limit).
For a top order `k ≥ 1` there is one multiplier `K' ≥ 1` (depending only on `g`, the manifold and
`k`, *uniform in the tensor valence `m`, the tensor `w` and the order index `i`*) with, for every
`(0, m)`-tensor `w` and every `i ≥ 1`,
```
‖∇w‖_{L^{2k/(i+1)}}² ≤ K' · ‖w‖_{L^{2k/i}} · ‖∇²w‖_{L^{2k/(i+2)}},
```
the mixed-`L^p` fibre norms written through their squared fibre norms with the ladder exponents
`(k/i, k/(i+1), k/(i+2))` and weights `((i)/(2k), (i+1)/(2k), (i+2)/(2k))`, where `∇ = covGrad`.
The three exponents satisfy the Gagliardo–Nirenberg balance `2·(i+1)/(2k) = i/(2k)·1 + (i+2)/(2k)·1`
identically in `i`, so the displayed inequality is the genuine second-order interpolation; for
`i + 2 ≤ 2k` it is the standard regime (all `L^p` exponents `≥ 1`), and for `i + 2 > 2k` it is the
sub-unit-exponent continuation (the convexity of `p ↦ log‖f‖_{L^{1/p}}` keeps it true with the same
uniform multiplier — it is tight, attaining equality on a single Fourier mode of the flat torus).

**Non-vacuity.**  `K'` is quantified before `(m, w, i)`; the conclusion reads the genuine covariant
derivatives `∇w`, `∇²w` of `w` (not a free family), and a tensor with a nonvanishing first jet rejects
the `K' = 0` reading by positivity of the left member.  Its body is `sorry`: the genuine covariant IBP
plus Hölder interpolation; consumers transitively depend on its `sorryAx`. -/
private theorem secondOrderInterp_lpFiberJet_fin
    (g : SmoothRiemannianMetric I M) (k : ℕ) (_hk : 1 ≤ k) :
    ∃ K' : ℝ, 1 ≤ K' ∧
      ∀ (m : ℕ) (w : Integral.L2.SmoothCcTensor g 0 m) (i : ℕ), 1 ≤ i →
        ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / (i + 1))
            ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ (((i : ℝ) + 1) / (2 * k))) ^ 2 ≤
          K' *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) ^ ((k : ℝ) / i)
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * k))) *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
                  ((covGrad (I := I) (M := M) g 0 (m + 1)
                    (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ ((k : ℝ) / (i + 2))
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ (((i : ℝ) + 2) / (2 * k))) := by
  classical
  obtain ⟨K'', hK''1, hlowExp⟩ := secondOrderInterp_lpFiberJet_fin_lowExp (I := I) (M := M) g k _hk
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one _hk)
  -- The uniform multiplier dominates the standard-regime IBP constant `2(k-1)+√n` (an `i`-uniform
  -- upper bound for the order-`i` constant `2(k/(i+1)-1)+√n`), `1`, and the sub-unit engine `K''`.
  refine ⟨max (max (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) 1) K'', ?_, ?_⟩
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  intro m w i hi1
  set μ : MeasureTheory.Measure M := Integral.Measure.riemannianVolumeMeasure I M g with hμ
  haveI : MeasureTheory.IsFiniteMeasure μ :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set K' : ℝ := max (max (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) 1) K''
    with hK'def
  -- Abbreviations for the three squared fibre norms (nonnegative continuous functions).
  set a : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)
    with ha_def
  set b : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
    ((covGrad (I := I) (M := M) g 0 m w).toSection x) with hb_def
  set c : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
    ((covGrad (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w)).toSection x)
    with hc_def
  have ha0 : ∀ x, 0 ≤ a x := fun x => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m x _
  have hb0 : ∀ x, 0 ≤ b x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) x _
  have hc0 : ∀ x, 0 ≤ c x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) x _
  have hac : Continuous a := continuous_rfns_section (I := I) (M := M) g 0 m w
  have hbc : Continuous b :=
    continuous_rfns_section (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w)
  have hcc : Continuous c :=
    continuous_rfns_section (I := I) (M := M) g 0 (m + 1 + 1)
      (covGrad (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w))
  rcases lt_or_ge (i + 1) k with hreg | hreg
  · -- **Standard regime `i + 1 < k`**: covariant IBP + three-function Hölder.
    have hiR : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi1
    have hi1R : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hi2R : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    -- The IBP exponent `p = k/(i+1) > 1`.
    set p : ℝ := (k : ℝ) / (i + 1) with hp_def
    have hp1 : 1 < p := by
      rw [hp_def, lt_div_iff₀ hi1R, one_mul]; exact_mod_cast hreg
    have hp0 : 0 < p := lt_trans one_pos hp1
    have hp1m : 0 < p - 1 := by linarith
    -- The three Hölder exponents `α = 2k/i`, `β = k/(k-i-1)`, `γ = 2k/(i+2)`.
    set α : ℝ := 2 * (k : ℝ) / i with hα_def
    set β : ℝ := (k : ℝ) / ((k : ℝ) - ((i : ℝ) + 1)) with hβ_def
    set γ : ℝ := 2 * (k : ℝ) / (i + 2) with hγ_def
    have hkmi : 0 < (k : ℝ) - ((i : ℝ) + 1) := by
      have : ((i : ℝ) + 1) < (k : ℝ) := by exact_mod_cast hreg
      linarith
    have hα0 : 0 < α := by rw [hα_def]; positivity
    have hβ0 : 0 < β := by rw [hβ_def]; positivity
    have hγ0 : 0 < γ := by rw [hγ_def]; positivity
    -- Hölder balance `α⁻¹ + β⁻¹ + γ⁻¹ = 1`.
    have hbalance : α⁻¹ + β⁻¹ + γ⁻¹ = 1 := by
      rw [hα_def, hβ_def, hγ_def]
      rw [inv_div, inv_div, inv_div]
      field_simp
      ring
    -- The continuous nonnegative Hölder factors `f₁ = a^{1/2}`, `f₂ = b^{p-1}`, `f₃ = c^{1/2}`.
    set f₁ : M → ℝ := fun x => a x ^ (1 / 2 : ℝ) with hf₁_def
    set f₂ : M → ℝ := fun x => b x ^ (p - 1) with hf₂_def
    set f₃ : M → ℝ := fun x => c x ^ (1 / 2 : ℝ) with hf₃_def
    have hf₁c : Continuous f₁ := hac.rpow_const (fun _ => Or.inr (by norm_num))
    have hf₂c : Continuous f₂ := hbc.rpow_const (fun _ => Or.inr (le_of_lt hp1m))
    have hf₃c : Continuous f₃ := hcc.rpow_const (fun _ => Or.inr (by norm_num))
    have hf₁0 : ∀ x, 0 ≤ f₁ x := fun x => Real.rpow_nonneg (ha0 x) _
    have hf₂0 : ∀ x, 0 ≤ f₂ x := fun x => Real.rpow_nonneg (hb0 x) _
    have hf₃0 : ∀ x, 0 ≤ f₃ x := fun x => Real.rpow_nonneg (hc0 x) _
    -- The three-function Hölder bound.
    have hHolder := real_holder_three_nonneg (I := I) (M := M) g f₁ f₂ f₃
      hf₁c hf₂c hf₃c hf₁0 hf₂0 hf₃0 hα0 hβ0 hγ0 hbalance
    -- Identify the three Hölder integrals with `Aw`, `Ib^{1-1/p}`, `C`.
    -- `(f₁ x)^α = a x^{(1/2)·α} = a x^{k/i}`.
    have hαexp : (1 / 2 : ℝ) * α = (k : ℝ) / i := by
      rw [hα_def]; field_simp
    have he1 : ∀ x, f₁ x ^ α = a x ^ ((k : ℝ) / i) := by
      intro x; rw [hf₁_def, ← Real.rpow_mul (ha0 x), hαexp]
    -- `(f₃ x)^γ = c x^{(1/2)·γ} = c x^{k/(i+2)}`.
    have hγexp : (1 / 2 : ℝ) * γ = (k : ℝ) / (i + 2) := by
      rw [hγ_def]; field_simp
    have he3 : ∀ x, f₃ x ^ γ = c x ^ ((k : ℝ) / (i + 2)) := by
      intro x; rw [hf₃_def, ← Real.rpow_mul (hc0 x), hγexp]
    -- `(f₂ x)^β = b x^{(p-1)·β} = b x^p`.
    have hβexp : (p - 1) * β = p := by
      have hpm1 : p - 1 = ((k : ℝ) - ((i : ℝ) + 1)) / ((i : ℝ) + 1) := by
        rw [hp_def, div_sub_one (ne_of_gt hi1R)]
      rw [hpm1, hβ_def, hp_def, div_mul_div_comm, mul_comm ((k : ℝ) - ((i : ℝ) + 1)) (k : ℝ),
        mul_div_mul_right _ _ (ne_of_gt hkmi)]
    have he2 : ∀ x, f₂ x ^ β = b x ^ p := by
      intro x; rw [hf₂_def, ← Real.rpow_mul (hb0 x), hβexp]
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he1),
        MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he2),
        MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he3)] at hHolder
    -- The pointwise integrand of the IBP RHS is `f₁·f₂·f₃`.
    have hprod_pt : ∀ x, a x ^ (1 / 2 : ℝ) * b x ^ (p - 1) * c x ^ (1 / 2 : ℝ)
        = f₁ x * f₂ x * f₃ x := fun x => by rw [hf₁_def, hf₂_def, hf₃_def]
    -- The covariant IBP inequality (child).
    have hIBP := weightedCovIBP_lpFiberJet_fin (I := I) (M := M) g k m i _hk hi1 hreg w
    -- Rewrite the IBP RHS integrand into `f₁·f₂·f₃` and fold the abbreviations `a, b, c`.
    rw [show (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x)) ^ (1 / 2 : ℝ) *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
                ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / (i + 1) - 1) *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (m + 1)
                  (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ (1 / 2 : ℝ) ∂μ)
            = ∫ x, f₁ x * f₂ x * f₃ x ∂μ from by
        refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ (fun x => ?_))
        rw [hf₁_def, hf₂_def, hf₃_def, ha_def, hb_def, hc_def, hp_def]] at hIBP
    -- Abbreviate the three target integrals.
    set Ia : ℝ := ∫ x, a x ^ ((k : ℝ) / i) ∂μ with hIa_def
    set Ib : ℝ := ∫ x, b x ^ p ∂μ with hIb_def
    set Ic : ℝ := ∫ x, c x ^ ((k : ℝ) / (i + 2)) ∂μ with hIc_def
    have hIa_nn : 0 ≤ Ia := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (ha0 x) _)
    have hIb_nn : 0 ≤ Ib := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hb0 x) _)
    have hIc_nn : 0 ≤ Ic := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hc0 x) _)
    set Aw : ℝ := Ia ^ ((i : ℝ) / (2 * k)) with hAw_def
    set C : ℝ := Ic ^ (((i : ℝ) + 2) / (2 * k)) with hC_def
    have hAw_nn : 0 ≤ Aw := Real.rpow_nonneg hIa_nn _
    have hC_nn : 0 ≤ C := Real.rpow_nonneg hIc_nn _
    -- The Hölder factor exponents: `1/α = i/(2k)`, `1/β = (k-i-1)/k = 1 - 1/p`, `1/γ = (i+2)/(2k)`.
    have hinvα : (1 : ℝ) / α = (i : ℝ) / (2 * k) := by rw [hα_def]; rw [one_div_div]
    have hinvγ : (1 : ℝ) / γ = ((i : ℝ) + 2) / (2 * k) := by rw [hγ_def]; rw [one_div_div]
    -- `hHolder` now reads `∫ f₁f₂f₃ ≤ Ia^{1/α}·(Ib^{1/β}·Ic^{1/γ})`.
    -- The corrected Hamilton IBP constant at this order, `D = 2(p-1)+√n` (with `p = k/(i+1)`).
    set D : ℝ := 2 * (p - 1) + Real.sqrt (Module.finrank ℝ E : ℝ) with hD_def
    have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt (Module.finrank ℝ E : ℝ) := Real.sqrt_nonneg _
    -- Combine with IBP: `Ib ≤ D·Ia^{1/α}·Ib^{1/β}·Ic^{1/γ}`.
    have hIb_bound : Ib ≤ D * (Aw * (Ib ^ (1 / β) * C)) := by
      have hcoef_nn : 0 ≤ D := by rw [hD_def]; nlinarith [hp1m, hsqrt_nn]
      have hstep : Ib ≤ D * (∫ x, f₁ x * f₂ x * f₃ x ∂μ) := hIBP
      refine le_trans hstep ?_
      apply mul_le_mul_of_nonneg_left _ hcoef_nn
      rw [hinvα, hinvγ] at hHolder
      rw [hAw_def, hC_def]
      exact hHolder
    -- Key exponent identities: `1/p = (i+1)/k`, `1/β = (k-(i+1))/k`, and `1/p + 1/β = 1`.
    have hinvp : (1 : ℝ) / p = ((i : ℝ) + 1) / k := by
      rw [hp_def, one_div_div]
    have hinvβ : (1 : ℝ) / β = ((k : ℝ) - ((i : ℝ) + 1)) / k := by
      rw [hβ_def, one_div_div]
    have hsum_pβ : (1 : ℝ) / p + 1 / β = 1 := by
      rw [hinvp, hinvβ, ← add_div]
      rw [show ((i : ℝ) + 1) + ((k : ℝ) - ((i : ℝ) + 1)) = (k : ℝ) from by ring,
        div_self (ne_of_gt hkR)]
    -- The leaf LHS squared equals `Ib^{1/p}` (since `2·(i+1)/(2k) = (i+1)/k = 1/p`).
    have hLHS_sq : (Ib ^ (((i : ℝ) + 1) / (2 * k))) ^ 2 = Ib ^ ((1 : ℝ) / p) := by
      have hexp : ((i : ℝ) + 1) / (2 * k) * ((2 : ℕ) : ℝ) = (1 : ℝ) / p := by
        rw [hinvp]; push_cast; ring
      rw [← Real.rpow_natCast (Ib ^ (((i : ℝ) + 1) / (2 * k))) 2, ← Real.rpow_mul hIb_nn, hexp]
    -- `D = 2(p-1)+√n ≤ 2(k-1)+√n ≤ K'` since `p ≤ k` (as `i + 1 ≥ 2`).
    have hcoef_le : D ≤ K' := by
      have hp_le_k : p ≤ (k : ℝ) := by
        rw [hp_def, div_le_iff₀ hi1R]
        nlinarith [hkR, hiR]
      have hDk : D ≤ 2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ) := by
        rw [hD_def]; linarith
      exact le_trans hDk (le_trans (le_max_left _ _) (le_max_left _ _))
    -- Conclude by dividing the IBP+Hölder bound by `Ib^{1/β}`.
    rw [hLHS_sq]
    rcases eq_or_lt_of_le hIb_nn with hIb0 | hIbpos
    · -- `Ib = 0`: LHS = `0^{1/p} = 0 ≤ RHS`.
      rw [← hIb0, Real.zero_rpow (by rw [hinvp]; positivity)]
      positivity
    · -- `Ib > 0`: cancel the positive factor `Ib^{1/β}`.
      have hIbβ_pos : 0 < Ib ^ (1 / β) := Real.rpow_pos_of_pos hIbpos _
      -- `Ib = Ib^{1/p}·Ib^{1/β}`.
      have hIb_split : Ib = Ib ^ ((1 : ℝ) / p) * Ib ^ (1 / β) := by
        rw [← Real.rpow_add hIbpos, hsum_pβ, Real.rpow_one]
      -- From `hIb_bound`: `Ib^{1/p}·Ib^{1/β} ≤ D·Aw·C·Ib^{1/β}`.
      have hkey : Ib ^ ((1 : ℝ) / p) * Ib ^ (1 / β) ≤ (D * (Aw * C)) * Ib ^ (1 / β) := by
        rw [← hIb_split]
        calc Ib ≤ D * (Aw * (Ib ^ (1 / β) * C)) := hIb_bound
          _ = (D * (Aw * C)) * Ib ^ (1 / β) := by ring
      have hcancel : Ib ^ ((1 : ℝ) / p) ≤ D * (Aw * C) :=
        le_of_mul_le_mul_right hkey hIbβ_pos
      calc Ib ^ ((1 : ℝ) / p) ≤ D * (Aw * C) := hcancel
        _ ≤ K' * (Aw * C) := by
            apply mul_le_mul_of_nonneg_right hcoef_le (mul_nonneg hAw_nn hC_nn)
        _ = K' * Aw * C := by ring
  · -- **Sub-unit regime `k ≤ i + 1`**: the log-convexity engine, constant `K'' ≤ K'`.
    have hstep := hlowExp m w i hi1 hreg
    have hK''_le : K'' ≤ K' := le_max_right _ _
    -- Nonnegativity of the two right factors.
    have hAw_nn : 0 ≤ (∫ x, a x ^ ((k : ℝ) / i) ∂μ) ^ ((i : ℝ) / (2 * k)) :=
      Real.rpow_nonneg (MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (ha0 x) _)) _
    have hC_nn : 0 ≤ (∫ x, c x ^ ((k : ℝ) / (i + 2)) ∂μ) ^ (((i : ℝ) + 2) / (2 * k)) :=
      Real.rpow_nonneg (MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hc0 x) _)) _
    calc ((∫ x, b x ^ ((k : ℝ) / (i + 1)) ∂μ) ^ (((i : ℝ) + 1) / (2 * k))) ^ 2
        ≤ K'' * (∫ x, a x ^ ((k : ℝ) / i) ∂μ) ^ ((i : ℝ) / (2 * k)) *
            (∫ x, c x ^ ((k : ℝ) / (i + 2)) ∂μ) ^ (((i : ℝ) + 2) / (2 * k)) := hstep
      _ ≤ K' * (∫ x, a x ^ ((k : ℝ) / i) ∂μ) ^ ((i : ℝ) / (2 * k)) *
            (∫ x, c x ^ ((k : ℝ) / (i + 2)) ∂μ) ^ (((i : ℝ) + 2) / (2 * k)) := by
          apply mul_le_mul_of_nonneg_right _ hC_nn
          exact mul_le_mul_of_nonneg_right hK''_le hAw_nn

set_option maxHeartbeats 1600000 in
/-- **(POSIT — the generic single-tensor second-order covariant `L^p` interpolation step,
`L^∞` lower factor, the order-zero endpoint.)**

The order-`0` instance of the second-order interpolation, where the lowest factor is the `L^∞` fibre
sup of `w` (here supplied as any uniform bound `A` on the fibre norm).  For a top order `k ≥ 1` there
is one multiplier `K' ≥ 1` (depending only on `g`, the manifold and `k`, uniform in `m`, `w`, `A`)
with, for every `(0, m)`-tensor `w` and every `A ≥ 0` bounding the fibre norm-squared of `w`,
```
‖∇w‖_{L^{2k}}² ≤ K' · A · ‖∇²w‖_{L^{k}},
```
written through the squared fibre norms with the order-`0` ladder exponents `k/1`, `k/2` and weights
`1/(2k)`, `2/(2k)` (`∇ = covGrad`).  This is the second-order Gagliardo–Nirenberg interpolation at the
`L^∞`–`L^{2k}`–`L^k` endpoint triple `2/(2k) = 0·1 + (2/(2k))·1`, the `i = 0` continuation of the
finite step.

**Non-vacuity.**  `K'` is quantified before `(m, w, A)`; the hypothesis `∀ x, |w(x)|² ≤ A²` genuinely
constrains `w` by `A` (it rejects no nontrivial `w` and forces `A > 0` whenever `w ≠ 0`), and the
conclusion reads the genuine covariant derivatives of `w`.  Its body is `sorry`: the genuine covariant
IBP with an `L^∞` factor; consumers transitively depend on its `sorryAx`. -/
private theorem secondOrderInterp_lpFiberJet_sup
    (g : SmoothRiemannianMetric I M) (k : ℕ) (_hk : 1 ≤ k) :
    ∃ K' : ℝ, 1 ≤ K' ∧
      ∀ (m : ℕ) (w : Integral.L2.SmoothCcTensor g 0 m) (A : ℝ), 0 ≤ A →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 m x (w.toSection x) ≤ A ^ 2) →
        ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
              ((covGrad (I := I) (M := M) g 0 m w).toSection x)) ^ ((k : ℝ) / 1)
            ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((1 : ℝ) / (2 * k))) ^ 2 ≤
          K' * A *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
                  ((covGrad (I := I) (M := M) g 0 (m + 1)
                    (covGrad (I := I) (M := M) g 0 m w)).toSection x)) ^ ((k : ℝ) / 2)
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((2 : ℝ) / (2 * k))) := by
  classical
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one _hk)
  refine ⟨max (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) 1, le_max_right _ _, ?_⟩
  intro m w A hA hsup
  set μ : MeasureTheory.Measure M := Integral.Measure.riemannianVolumeMeasure I M g with hμ
  haveI : MeasureTheory.IsFiniteMeasure μ :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set K' : ℝ := max (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) 1 with hK'def
  set b : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x
    ((covGrad (I := I) (M := M) g 0 m w).toSection x) with hb_def
  set c : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1 + 1) x
    ((covGrad (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w)).toSection x)
    with hc_def
  have hb0 : ∀ x, 0 ≤ b x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1) x _
  have hc0 : ∀ x, 0 ≤ c x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (m + 1 + 1) x _
  have hbc : Continuous b :=
    continuous_rfns_section (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w)
  have hcc : Continuous c :=
    continuous_rfns_section (I := I) (M := M) g 0 (m + 1 + 1)
      (covGrad (I := I) (M := M) g 0 (m + 1) (covGrad (I := I) (M := M) g 0 m w))
  set Ib : ℝ := ∫ x, b x ^ ((k : ℝ) / 1) ∂μ with hIb_def
  set Ic : ℝ := ∫ x, c x ^ ((k : ℝ) / 2) ∂μ with hIc_def
  have hIb_nn : 0 ≤ Ib := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hb0 x) _)
  have hIc_nn : 0 ≤ Ic := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hc0 x) _)
  set C : ℝ := Ic ^ ((2 : ℝ) / (2 * k)) with hC_def
  have hC_nn : 0 ≤ C := Real.rpow_nonneg hIc_nn _
  -- The covariant IBP inequality with the `L^∞` factor (child).
  have hIBP := weightedCovIBP_lpFiberJet_sup (I := I) (M := M) g k m _hk w A hA hsup
  -- The leaf LHS squared equals `Ib^{1/k}`.
  have hk1 : (k : ℝ) / 1 = (k : ℝ) := by norm_num
  have hLHS_sq : (Ib ^ ((1 : ℝ) / (2 * k))) ^ 2 = Ib ^ ((1 : ℝ) / k) := by
    have hexp : (1 : ℝ) / (2 * k) * ((2 : ℕ) : ℝ) = (1 : ℝ) / k := by push_cast; ring
    rw [← Real.rpow_natCast (Ib ^ ((1 : ℝ) / (2 * k))) 2, ← Real.rpow_mul hIb_nn, hexp]
  -- `C = Ic^{1/k}`.
  have hC_eq : C = Ic ^ ((1 : ℝ) / k) := by
    rw [hC_def]; congr 1; rw [eq_div_iff (by positivity)]; field_simp
  rw [hLHS_sq]
  -- Bound the IBP RHS integral `∫ b^{k-1}·c^{1/2}` and chain to `Ib^{1/k} ≤ (2k-1)·A·C`.
  set J : ℝ := ∫ x, b x ^ ((k : ℝ) - 1) * c x ^ (1 / 2 : ℝ) ∂μ with hJ_def
  have hJ_nn : 0 ≤ J := MeasureTheory.integral_nonneg (fun x =>
    mul_nonneg (Real.rpow_nonneg (hb0 x) _) (Real.rpow_nonneg (hc0 x) _))
  -- The corrected Hamilton IBP constant `D = 2(k-1)+√n` (the `i = 0`, `p = k` order).
  set D : ℝ := 2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ) with hD_def
  have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt (Module.finrank ℝ E : ℝ) := Real.sqrt_nonneg _
  have hkm1_nn : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast _hk
    linarith
  have hD_nn : 0 ≤ D := by rw [hD_def]; nlinarith [hkm1_nn, hsqrt_nn]
  -- `hIBP : Ib ≤ D·A·J`.
  have hIBP' : Ib ≤ D * A * J := by
    rw [hIb_def, hJ_def, hD_def]; exact hIBP
  -- Two-function Hölder on `J` (for `k ≥ 2`); for `k = 1` the factor `b^{k-1} = 1` is handled
  -- directly.  In both cases we obtain `J ≤ Ib^{(k-1)/k}·C`.
  have hJ_bound : J ≤ Ib ^ (((k : ℝ) - 1) / k) * C := by
    rcases eq_or_lt_of_le _hk with hk_eq | hk_gt
    · -- `k = 1`: `b^{k-1} = b^0 = 1`, so `J = ∫ c^{1/2} = Ic^{...}`, and `(k-1)/k = 0`.
      have hk1' : (k : ℝ) = 1 := by exact_mod_cast hk_eq.symm
      have hb0pow : ∀ x, b x ^ ((k : ℝ) - 1) = 1 := by
        intro x; rw [hk1']; norm_num
      rw [hJ_def]
      simp_rw [hb0pow, one_mul]
      rw [hk1']
      simp only [sub_self, zero_div, Real.rpow_zero, one_mul]
      -- `∫ c^{1/2} ≤ Ic^{1/1} = ∫ c^{1/2}`; here `C = Ic^{2/(2·1)} = Ic^1 = ∫ c^{1/2}`.
      have hCeq1 : C = ∫ x, c x ^ (1 / 2 : ℝ) ∂μ := by
        rw [hC_def, hIc_def, hk1']
        norm_num
      rw [hCeq1]
    · -- `k ≥ 2`: two-function Hölder at the conjugate pair `(k/(k-1), k)`.
      have hk2R : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_gt
      have hkm1 : 0 < (k : ℝ) - 1 := by linarith
      set β : ℝ := (k : ℝ) / ((k : ℝ) - 1) with hβ_def
      have hβ0 : 0 < β := by rw [hβ_def]; positivity
      have hconj : β.HolderConjugate (k : ℝ) := by
        refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
        · rw [hβ_def, one_lt_div hkm1]; linarith
        · rw [hβ_def, inv_div, inv_eq_one_div, div_add_div _ _ (ne_of_gt hkR) (ne_of_gt hkR),
            div_eq_one_iff_eq (by positivity)]
          ring
      -- The two Hölder factors `b^{k-1}` and `c^{1/2}` (continuous, nonneg, in the relevant Lᵖ).
      have hf2c : Continuous (fun x => b x ^ ((k : ℝ) - 1)) :=
        hbc.rpow_const (fun _ => Or.inr (le_of_lt hkm1))
      have hf3c : Continuous (fun x => c x ^ (1 / 2 : ℝ)) :=
        hcc.rpow_const (fun _ => Or.inr (by norm_num))
      have hf2mem : MeasureTheory.MemLp (fun x => b x ^ ((k : ℝ) - 1)) (ENNReal.ofReal β) μ :=
        hf2c.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hf3mem : MeasureTheory.MemLp (fun x => c x ^ (1 / 2 : ℝ)) (ENNReal.ofReal (k : ℝ)) μ :=
        hf3c.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hH := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hconj
        (f := fun x => b x ^ ((k : ℝ) - 1)) (g := fun x => c x ^ (1 / 2 : ℝ))
        (MeasureTheory.ae_of_all _ (fun x => Real.rpow_nonneg (hb0 x) _))
        (MeasureTheory.ae_of_all _ (fun x => Real.rpow_nonneg (hc0 x) _)) hf2mem hf3mem
      -- `(b^{k-1})^β = b^{k/1}`, `(c^{1/2})^k = c^{k/2}`.
      have hβcancel : ((k : ℝ) - 1) * β = (k : ℝ) := by
        rw [hβ_def, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self (ne_of_gt hkm1), mul_one]
      have hpow2 : ∀ x, (b x ^ ((k : ℝ) - 1)) ^ β = b x ^ ((k : ℝ) / 1) := by
        intro x; rw [← Real.rpow_mul (hb0 x), hβcancel, hk1]
      have hpow3 : ∀ x, (c x ^ (1 / 2 : ℝ)) ^ (k : ℝ) = c x ^ ((k : ℝ) / 2) := by
        intro x; rw [← Real.rpow_mul (hc0 x)]; congr 1; ring
      rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpow2),
          MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpow3)] at hH
      -- `hH : ∫b^{k-1}c^{1/2} ≤ (∫b^{k/1})^{1/β}·(∫c^{k/2})^{1/k}`; identify each factor.
      have hinvβ : (1 : ℝ) / β = ((k : ℝ) - 1) / k := by rw [hβ_def, one_div_div]
      have hinvk : (1 : ℝ) / (k : ℝ) = (2 : ℝ) / (2 * k) := by
        rw [eq_div_iff (by positivity)]; field_simp
      rw [hinvβ, hinvk] at hH
      -- Fold `∫b^{k/1} = Ib`, `∫c^{k/2} = Ic`, `Ic^{2/(2k)} = C`, `∫b^{k-1}c^{1/2} = J`.
      rw [show (∫ x, b x ^ ((k : ℝ) / 1) ∂μ) = Ib from hIb_def.symm,
          show (∫ x, c x ^ ((k : ℝ) / 2) ∂μ) = Ic from hIc_def.symm,
          ← hC_def] at hH
      rw [hJ_def]
      exact hH
  -- Conclude: `Ib ≤ D·A·Ib^{(k-1)/k}·C`, then cancel `Ib^{(k-1)/k}`.
  have hcoef_le : D ≤ K' := by rw [hD_def]; exact le_max_left _ _
  have hAC_nn : 0 ≤ A * C := mul_nonneg hA hC_nn
  -- `1/k + (k-1)/k = 1`.
  have hsum_k : (1 : ℝ) / k + ((k : ℝ) - 1) / k = 1 := by
    rw [← add_div, show (1 : ℝ) + ((k : ℝ) - 1) = (k : ℝ) from by ring, div_self (ne_of_gt hkR)]
  rcases eq_or_lt_of_le hIb_nn with hIb0 | hIbpos
  · -- `Ib = 0`: LHS = `0^{1/k} = 0 ≤ RHS`.
    rw [← hIb0, Real.zero_rpow (by positivity)]
    positivity
  · -- `Ib > 0`: cancel `Ib^{(k-1)/k}`.
    have hIbβ_pos : 0 < Ib ^ (((k : ℝ) - 1) / k) := Real.rpow_pos_of_pos hIbpos _
    have hIb_split : Ib = Ib ^ ((1 : ℝ) / k) * Ib ^ (((k : ℝ) - 1) / k) := by
      rw [← Real.rpow_add hIbpos, hsum_k, Real.rpow_one]
    have hchain : Ib ^ ((1 : ℝ) / k) * Ib ^ (((k : ℝ) - 1) / k)
        ≤ (D * (A * C)) * Ib ^ (((k : ℝ) - 1) / k) := by
      rw [← hIb_split]
      calc Ib ≤ D * A * J := hIBP'
        _ ≤ D * A * (Ib ^ (((k : ℝ) - 1) / k) * C) := by
            apply mul_le_mul_of_nonneg_left hJ_bound
            exact mul_nonneg hD_nn hA
        _ = (D * (A * C)) * Ib ^ (((k : ℝ) - 1) / k) := by ring
    have hcancel : Ib ^ ((1 : ℝ) / k) ≤ D * (A * C) :=
      le_of_mul_le_mul_right hchain hIbβ_pos
    calc Ib ^ ((1 : ℝ) / k) ≤ D * (A * C) := hcancel
      _ ≤ K' * (A * C) := mul_le_mul_of_nonneg_right hcoef_le hAC_nn
      _ = K' * A * C := by ring

/-- **The single-step Gagliardo–Nirenberg log-convexity of the mixed-`L^p` fibre jets.**

Fix an anchor `g`, a valence `s`, and a top order `k ≥ 1`.  There is a single multiplier `K ≥ 1`
(depending only on `g`, the manifold and `(s, k)`) such that for every smooth compactly-supported
`(0, s)`-tensor `u` whose `C⁰`-sup fibre norm-squared is `≤ Λ₀²` (with `Λ₀ ≥ 0`) and every order `i`,
the mixed-`L^p` fibre-jet ladder `c := lpFiberJetLadder g s k u Λ₀` (whose value at order `i` is the
`L^{2k/i}` norm of the pointwise fibre norm `|∇^i u|`, with the `L^∞`-endpoint `c_0 = Λ₀·√(vol M)` and
the `L²`-endpoint `c_k = ‖∇^k u‖_{L²}`) is **log-convex up to the multiplier `K`**:
```
c_{i+1}² ≤ K · c_i · c_{i+2}.
```

**The `Λ₀` hypotheses are load-bearing (the bare statement is false).**  The conclusion is quantified
over `Λ₀` with the `L^∞`-endpoint `c_0 = Λ₀·√(vol M)`.  Without `0 ≤ Λ₀` and the fibre bound
`|u|² ≤ Λ₀²`, the order-`0` instance `c_1² ≤ K·c_0·c_2 = K·Λ₀√(vol M)·c_2` fails at `Λ₀ = 0` for any
`u` with a nonvanishing first jet (`c_1 > 0`, right member `0`); the two hypotheses (mirrored from the
consumer `exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le`, which has them in scope and now
passes them at the call site) make `c_0` a genuine upper bound for the `L^∞` reading of `u` and the
node true.

This is the genuine **`L^p` interpolation engine** of the closed-manifold tensor Gagliardo–Nirenberg
inequality (Hamilton 12.5, Aubin), the single covariant analytic input from which the full
`j`-versus-`k` interpolation follows by the elementary discrete Hardy–Littlewood–Pólya power law
`lp_hlp_real`.  Because `iteratedCovGrad` is the *straight* covariant iterate (`∇^{i+2}u =
covGrad (covGrad (∇^i u))` by `iteratedCovGrad_succ = rfl`), there is **no curvature commutator** to
absorb: setting `v := ∇^i u` the step is the pure second-order interpolation `‖∇v‖_{q₁}² ≤
K·‖v‖_{q₀}·‖∇²v‖_{q₂}` at `q_m = 2k/(i+m)`.

The proof is glue over two posited deep analytic inputs — the second-order covariant `L^p`
interpolation step on a single tensor, finite (`secondOrderInterp_lpFiberJet_fin`) and `L^∞`-lower-
factor (`secondOrderInterp_lpFiberJet_sup`) — composed with: the honest-jet reading of the ladder
(`c_i = ‖∇^i u‖_{L^{2k/i}}` for `i ≥ 1`, the `L²`-endpoint via `tensorL2Norm_sq_toFun_eq_integral_
riemannianFiberNormSq`), the `iteratedCovGrad_succ` identification `covGrad(∇^i u) = ∇^{i+1}u`, the
`L^∞`-endpoint comparison `c_0 = Λ₀√(vol M)` against the sup bound, and the volume/finite/sup constant
absorption.  Mathlib carries only the *first-order Sobolev embedding* `eLpNorm_le_eLpNorm_fderiv`, not
this iterated-jet `L^p` interpolation; consumers therefore transitively depend on the `sorryAx` of the
two posited steps.

**Non-vacuity.**  `K` is quantified before `(u, Λ₀, i)`; the conclusion is the consecutive-jet square
bound on the *intrinsically defined* ladder `lpFiberJetLadder` (its order-`i` value genuinely reads
the `i`-th covariant jet of `u`), not a free sequence, so no degenerate witness is asserted (a tensor
with a nonvanishing intermediate jet rejects the `K = 0` reading by positivity of `c_i`). -/
private theorem lpFiberJet_logConvex_iteratedCovGrad
    (g : SmoothRiemannianMetric I M) (s k : ℕ) (hk : 1 ≤ k) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (u : Integral.L2.SmoothCcTensor g 0 s) (Λ₀ : ℝ), 0 ≤ Λ₀ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s x (u.toSection x) ≤ Λ₀ ^ 2) →
        ∀ i : ℕ,
          (lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ (i + 1)) ^ 2 ≤
            K * lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ i *
              lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ (i + 2) := by
  classical
  obtain ⟨Kf, hKf1, hfin⟩ := secondOrderInterp_lpFiberJet_fin (I := I) (M := M) g k hk
  obtain ⟨Ks, hKs1, hsupc⟩ := secondOrderInterp_lpFiberJet_sup (I := I) (M := M) g k hk
  have hk0 : (k : ℕ) ≠ 0 := by omega
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  have hkRpos : (0 : ℝ) < (k : ℝ) := by positivity
  set V : ℝ := Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal with hV
  have hVnn : 0 ≤ V := Real.sqrt_nonneg _
  -- The uniform multiplier: dominates the finite engine, the sup engine reweighted by `1/V`, and `1`.
  refine ⟨max (max Kf 1) (Ks * (1 / V) + Ks), ?_, ?_⟩
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  intro u Λ₀ hΛ₀ hsup
  set K : ℝ := max (max Kf 1) (Ks * (1 / V) + Ks) with hKdef
  have hKf_le : Kf ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKsV_le : Ks * (1 / V) + Ks ≤ K := le_max_right _ _
  -- The honest mixed-`L^p` fibre jet at order `i` (the interior/`L²`-endpoint reading of the ladder).
  set J : ℕ → ℝ := fun i =>
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u).toSection x)) ^ ((k : ℝ) / i)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * k)) with hJdef
  have hJnn : ∀ i, 0 ≤ J i := by
    intro i; rw [hJdef]
    exact Real.rpow_nonneg (integral_nonneg (fun x =>
      Real.rpow_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + i) x _) _)) _
  -- Reading: for `i ≥ 1`, the ladder value equals the honest jet (`i = k` via the `L²` bridge).
  have hread : ∀ i, 1 ≤ i → lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ i = J i := by
    intro i hi1
    rcases eq_or_ne i k with hik | hik
    · -- `i = k`: the `L²`-endpoint branch equals the honest jet via the fibre-norm bridge.
      subst hik
      rw [hJdef]
      simp only [lpFiberJetLadder, if_neg (show i ≠ 0 by omega), if_true]
      set t : ℝ := Integral.L2.tensorL2Norm (I := I) g 0 (s + i)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u).toFun with ht
      have htnn : 0 ≤ t := Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + i) _
      have hbridge : (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u).toSection x)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g)) = t ^ 2 := by
        rw [ht, tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g (s + i)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u)]
      have hii : (i : ℝ) / i = 1 := by
        rw [div_self]; exact_mod_cast (show i ≠ 0 by omega)
      symm
      calc (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u).toSection x)) ^ ((i : ℝ) / i)
              ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * i))
          = (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u).toSection x)
              ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((1 : ℝ) / 2) := by
              rw [hii]
              simp only [Real.rpow_one]
              rw [show (i : ℝ) / (2 * i) = 1 / 2 by field_simp]
        _ = (t ^ 2) ^ ((1 : ℝ) / 2) := by rw [hbridge]
        _ = t := by
              rw [← Real.rpow_natCast t 2, ← Real.rpow_mul htnn]
              norm_num
    · -- `i ≠ k`, `i ≥ 1`: the interior branch is literally the honest jet.
      rw [hJdef]
      simp only [lpFiberJetLadder, if_neg (show i ≠ 0 by omega), if_neg hik]
  -- Either the volume vanishes (the empty/degenerate manifold: every jet is `0`) or `V > 0`.
  rcases eq_or_lt_of_le hVnn with hV0 | hVpos
  · -- `V = 0`: the measure is null, so every honest jet and the `c_0` endpoint vanish.
    have hmuzero : (Integral.Measure.riemannianVolumeMeasure I M g) = 0 := by
      have hfin : (Integral.Measure.riemannianVolumeMeasure I M g) Set.univ ≠ ⊤ := by
        haveI := Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
          (I := I) (M := M) g
        exact (MeasureTheory.measure_ne_top _ _)
      have htoReal0 : ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal = 0 := by
        have hsqrt0 : Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal
            = 0 := by rw [← hV]; exact hV0.symm
        have hle := Real.sqrt_eq_zero'.mp hsqrt0
        exact le_antisymm hle ENNReal.toReal_nonneg
      have huniv0 : (Integral.Measure.riemannianVolumeMeasure I M g) Set.univ = 0 := by
        rwa [ENNReal.toReal_eq_zero_iff, or_iff_left hfin] at htoReal0
      exact MeasureTheory.Measure.measure_univ_eq_zero.mp huniv0
    have hJ0 : ∀ i, 1 ≤ i → J i = 0 := by
      intro i hi
      simp only [hJdef, hmuzero, MeasureTheory.integral_zero_measure]
      apply Real.zero_rpow
      have hiR : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
      positivity
    intro i
    have h1 : lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ (i + 1) = 0 := by
      rw [hread (i + 1) (by omega), hJ0 (i + 1) (by omega)]
    have h3 : lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ (i + 2) = 0 := by
      rw [hread (i + 2) (by omega), hJ0 (i + 2) (by omega)]
    rw [h1, h3]; ring_nf
    positivity
  · -- `V > 0`: the interior steps use the finite engine, the order-`0` step the `L^∞` engine.
    have hVne : V ≠ 0 := ne_of_gt hVpos
    intro i
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · -- Order-zero step `c₁² ≤ K · c₀ · c₂` via the `L^∞` engine.
      subst hi0
      rw [hread 1 (by omega), hread 2 (by omega)]
      have hc0eq : lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ 0 = Λ₀ * V := by
        rw [show lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ 0
              = Λ₀ * Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal
            from by unfold lpFiberJetLadder; rw [if_pos rfl], ← hV]
      rw [hc0eq]
      -- The sup engine on `u` with the fibre bound `Λ₀`.
      have hstep := hsupc s u Λ₀ hΛ₀ hsup
      -- Reconcile the literal `1`, `2` casts of the sup engine to `↑1`, `↑2` of `J`.
      have e1 : (1 : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
      have e2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
      rw [show ((k : ℝ) / 1) = ((k : ℝ) / ((1 : ℕ) : ℝ)) by norm_num,
          show ((1 : ℝ) / (2 * k)) = (((1 : ℕ) : ℝ) / (2 * k)) by norm_num,
          show ((k : ℝ) / 2) = ((k : ℝ) / ((2 : ℕ) : ℝ)) by norm_num,
          show ((2 : ℝ) / (2 * k)) = (((2 : ℕ) : ℝ) / (2 * k)) by norm_num] at hstep
      -- The sup engine's terms are now defeq to `J 1` and `J 2`; reconcile the constant.
      have hstep' : (J 1) ^ 2 ≤ Ks * Λ₀ * J 2 := hstep
      refine le_trans hstep' ?_
      have hJ2nn : 0 ≤ J 2 := hJnn 2
      have hreconc : Ks * Λ₀ ≤ K * (Λ₀ * V) := by
        have hKsKV : Ks ≤ K * V := by
          have hKsdivV : Ks / V ≤ K := by
            have hKsle : Ks ≤ Ks * (1 / V) + Ks := by
              have : 0 ≤ Ks * (1 / V) := by positivity
              linarith
            have : Ks * (1 / V) ≤ K := le_trans (by linarith) hKsV_le
            rw [div_eq_mul_one_div]; exact le_trans this (le_refl _)
          calc Ks = (Ks / V) * V := by field_simp
            _ ≤ K * V := mul_le_mul_of_nonneg_right hKsdivV hVnn
        nlinarith [hKsKV, hΛ₀, mul_nonneg (le_trans zero_le_one hKs1) hΛ₀]
      exact mul_le_mul_of_nonneg_right hreconc hJ2nn
    · -- Interior step `c_{i+1}² ≤ K · c_i · c_{i+2}` via the finite engine, `i ≥ 1`.
      rw [hread (i + 1) (by omega), hread i hipos, hread (i + 2) (by omega)]
      have hstep := hfin (s + i) (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u) i hipos
      -- Reconcile the `↑i + 1`, `↑i + 2` casts of the finite engine to `↑(i+1)`, `↑(i+2)` of `J`.
      have e1 : ((i : ℝ) + 1) = ((i + 1 : ℕ) : ℝ) := by push_cast; ring
      have e2 : ((i : ℝ) + 2) = ((i + 2 : ℕ) : ℝ) := by push_cast; ring
      rw [e1, e2] at hstep
      -- The finite engine's terms are now defeq to `J (i+1)`, `J i`, `J (i+2)` (the tensors agree by
      -- `iteratedCovGrad_succ = rfl`); chain through `Kf ≤ K`.
      refine le_trans hstep ?_
      have hJinn : 0 ≤ J i := hJnn i
      have hJi2nn : 0 ≤ J (i + 2) := hJnn (i + 2)
      have hbase : Kf * J i * J (i + 2) ≤ K * J i * J (i + 2) := by
        apply mul_le_mul_of_nonneg_right _ hJi2nn
        apply mul_le_mul_of_nonneg_right hKf_le hJinn
      exact le_trans (le_of_eq (by rfl)) hbase

/-- **(POSIT — the Lᵖ-fibre-norm Gagliardo–Nirenberg interpolation for iterated covariant
gradients; Hamilton 12.5.)**

Fix an anchor `g`, a valence `s`, and a top order `k ≥ 1`.  There is a single constant `C ≥ 0`
such that for every smooth compactly-supported `(0, s)`-tensor `u` whose `C⁰`-sup fibre norm is
`≤ Λ₀` and every intermediate order `0 < j < k`, the `L^{2k/j}` fibre norm of the `j`-th iterated
covariant gradient — written through its squared fibre norm `rfns(∇^j u) = |∇^j u|²` as
`(∫ rfns(∇^j u)^{k/j} dμ)^{j/k} = ‖∇^j u‖²_{L^{2k/j}}` — is controlled by the **interpolated**
product of the `L^∞` sup `Λ₀` and the top-order covariant `L²`-jet:
```
(∫ rfns(∇^j u)^{k/j} dμ)^{j/k} ≤ C · Λ₀^{2(1 − j/k)} · ‖∇^k u‖_{L²}^{2 j/k} .
```

This is the genuine **`Lᵖ` Gagliardo–Nirenberg interpolation** with the *free exponent* `p = 2k/j`:
the intermediate covariant gradient is estimated by interpolation between the `L^∞` bound (order
`0`) and the top-order `L²` bound (order `k`), the interpolation weights being `1 − j/k` (on the
sup) and `j/k` (on the top jet), now in the **`L^{2k/j}`** norm rather than the degenerate `L²` of
the companion `exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le`.  It is the precise kernel that
the diagonal covariant-jet product grid
(`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le`) consumes through Hölder at the
conjugate pair `(k/i, k/l)`: each Hölder factor is exactly an `L^{2k/i}` norm of one tensor's `i`-th
fibre jet, which this statement bounds.

**Non-vacuity.**  The constant `C` is uniform over `(u, Λ₀, j)` (quantified before all of them);
the bound `0 < j < k` confines the interpolation exponent `j/k ∈ (0, 1)` (so `p = 2k/j ∈ (2, ∞)`),
and the `k = 1` case is vacuous (no `j` with `0 < j < 1`), so no degenerate witness is asserted; a
`C = 0` witness is rejected by any `u` with a nonvanishing intermediate jet.

The proof is the genuine `k`-th-root (`rpow (1/k)`) extraction from the discrete log-convexity power
law on the mixed-`L^p` fibre-jet ladder `c := lpFiberJetLadder g s k u Λ₀`.  Feeding the posited
single-step log-convexity `lpFiberJet_logConvex_iteratedCovGrad` (`c_{i+1}² ≤ K·c_i·c_{i+2}`) to the
discrete Hardy–Littlewood–Pólya power law `lp_hlp_real` gives `c_j^k ≤ K^{k³}·c_0^{k-j}·c_k^j`;
identifying the ladder's interior value `c_j² = (∫ rfns(∇^j u)^{k/j})^{j/k}` (its `L^{2k/j}` fibre
norm squared), the `L^∞`-endpoint `c_0 = Λ₀·√(vol M)`, and the `L²`-endpoint `c_k = ‖∇^k u‖_{L²}`,
then taking `rpow (1/k)` of the squared bound and absorbing the volume factor
`(√(vol M))^{2(1−j/k)} ≤ max 1 (vol M)` into the constant `C := K^{2k²}·max 1 √(vol M)^2`, yields the
displayed interpolation.  It therefore depends transitively only on the `sorry` of
`lpFiberJet_logConvex_iteratedCovGrad` (the deep closed-manifold covariant `L^p` interpolation
engine), which `#print axioms` records as `sorryAx`; the displayed real-power statement is proven
outright on top of that single posited analytic input.  No packaging: the conclusion is a real-valued
`L^p` interpolation inequality on a single tensor's covariant jets, structurally distinct from any
consumer's Nemytskii conclusion. -/
theorem exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le
    (g : SmoothRiemannianMetric I M) (s k : ℕ) (_hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Integral.L2.SmoothCcTensor g 0 s) (Λ₀ : ℝ), 0 ≤ Λ₀ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s x (u.toSection x) ≤ Λ₀ ^ 2) →
        ∀ j : ℕ, 0 < j → j < k →
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toSection x)) ^ ((k : ℝ) / j)
              ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((j : ℝ) / k) ≤
            C * Λ₀ ^ (2 * (1 - (j : ℝ) / k)) *
              (Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun) ^ (2 * (j : ℝ) / k) := by
  classical
  obtain ⟨K, hK1, hlc⟩ := lpFiberJet_logConvex_iteratedCovGrad (I := I) (M := M) g s k _hk
  set V : ℝ := Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal with hV
  have hVnn : 0 ≤ V := Real.sqrt_nonneg _
  have hmax1 : (1 : ℝ) ≤ max 1 V := le_max_left _ _
  have hmaxV : V ≤ max 1 V := le_max_right _ _
  have hmax_nn : 0 ≤ max 1 V := le_trans zero_le_one hmax1
  -- The single uniform constant.
  set C : ℝ := K ^ (2 * k ^ 2) * (max 1 V) ^ 2 with hC
  have hKnn : 0 ≤ K := le_trans zero_le_one hK1
  have hC_nn : 0 ≤ C := by rw [hC]; positivity
  refine ⟨C, hC_nn, ?_⟩
  intro u Λ₀ hΛ₀ hsup j hj0 hjk
  have hk0 : (k : ℕ) ≠ 0 := by omega
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  have hkRpos : (0 : ℝ) < (k : ℝ) := by positivity
  -- The mixed-L^p fibre-jet ladder.
  set c : ℕ → ℝ := fun i => lpFiberJetLadder (I := I) (M := M) g s k u Λ₀ i with hc_def
  -- Nonnegativity of every ladder value.
  have hc_nn : ∀ i, 0 ≤ c i := by
    intro i
    rw [hc_def]
    simp only [lpFiberJetLadder]
    split_ifs with hi0 hik
    · exact mul_nonneg hΛ₀ hVnn
    · exact Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + k) _
    · exact Real.rpow_nonneg (integral_nonneg (fun x =>
        Real.rpow_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + i) x _) _)) _
  -- Log-convexity for this ladder (from the posited child).
  have hc_lc : ∀ i, (c (i + 1)) ^ 2 ≤ K * c i * c (i + 2) := by
    intro i; rw [hc_def]; exact hlc u Λ₀ hΛ₀ hsup i
  -- The HLP power law on the ladder.
  have hpow : (c j) ^ k ≤ K ^ (k ^ 3) * (c 0) ^ (k - j) * (c k) ^ j :=
    lp_hlp_real c hc_nn K hK1 hc_lc j k hj0 hjk
  -- Endpoint identifications: c 0 = Λ₀·V, c k = ‖∇^k u‖_{L²}, c j² = the LHS integral power.
  have hc0_eq : c 0 = Λ₀ * V := by
    simp only [hc_def, lpFiberJetLadder, if_pos rfl]
    rw [hV]
  have hck_eq : c k = Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun := by
    simp only [hc_def, lpFiberJetLadder, if_neg (show k ≠ 0 by omega), if_true]
  have hcj_sq : (c j) ^ 2 =
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toSection x)) ^ ((k : ℝ) / j)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((j : ℝ) / k) := by
    simp only [hc_def, lpFiberJetLadder, if_neg (show j ≠ 0 by omega), if_neg (show j ≠ k by omega)]
    set Iint : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toSection x)) ^ ((k : ℝ) / j)
        ∂(Integral.Measure.riemannianVolumeMeasure I M g) with hIint
    have hIint_nn : 0 ≤ Iint := integral_nonneg (fun x =>
      Real.rpow_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + j) x _) _)
    have hexp : (j : ℝ) / (2 * k) * ((2 : ℕ) : ℝ) = (j : ℝ) / k := by
      push_cast
      rw [mul_comm, ← mul_div_assoc, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [← Real.rpow_natCast (Iint ^ ((j : ℝ) / (2 * k))) 2,
        ← Real.rpow_mul hIint_nn, hexp]
  -- Nonnegativity of the endpoints.
  have hc0_nn : 0 ≤ c 0 := hc_nn 0
  have hck_nn : 0 ≤ c k := hc_nn k
  have hcj_nn : 0 ≤ c j := hc_nn j
  -- Square the HLP bound, then take rpow (1/k) of the squared form.
  have hpow_sq : ((c j) ^ 2) ^ k ≤
      (K ^ (k ^ 3)) ^ 2 * ((c 0) ^ 2) ^ (k - j) * ((c k) ^ 2) ^ j := by
    have hrw : ((c j) ^ 2) ^ k = ((c j) ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hrw]
    have hbase_nn : 0 ≤ K ^ (k ^ 3) * (c 0) ^ (k - j) * (c k) ^ j := by positivity
    calc ((c j) ^ k) ^ 2 ≤ (K ^ (k ^ 3) * (c 0) ^ (k - j) * (c k) ^ j) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hpow 2
      _ = (K ^ (k ^ 3)) ^ 2 * ((c 0) ^ 2) ^ (k - j) * ((c k) ^ 2) ^ j := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
          ring_nf
  -- Take rpow (1/k) of both sides of the squared bound.
  have hcj2_nn : 0 ≤ (c j) ^ 2 := by positivity
  have hmono : (((c j) ^ 2) ^ k) ^ ((k : ℝ)⁻¹) ≤
      ((K ^ (k ^ 3)) ^ 2 * ((c 0) ^ 2) ^ (k - j) * ((c k) ^ 2) ^ j) ^ ((k : ℝ)⁻¹) :=
    Real.rpow_le_rpow (by positivity) hpow_sq (by positivity)
  rw [Real.pow_rpow_inv_natCast hcj2_nn hk0] at hmono
  -- Compute the rpow (1/k) of the RHS via rpow algebra.
  have hcast_sub : ((k - j : ℕ) : ℝ) = (k : ℝ) - (j : ℝ) := by rw [Nat.cast_sub (le_of_lt hjk)]
  have hrhs : ((K ^ (k ^ 3)) ^ 2 * ((c 0) ^ 2) ^ (k - j) * ((c k) ^ 2) ^ j) ^ ((k : ℝ)⁻¹) =
      (K ^ (2 * k ^ 2)) * ((c 0) ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) * ((c k) ^ 2) ^ ((j : ℝ) / k) := by
    have hKpow_nn : 0 ≤ (K ^ (k ^ 3)) ^ 2 := by positivity
    have hc02_nn : 0 ≤ ((c 0) ^ 2) ^ (k - j) := by positivity
    have hck2_nn : 0 ≤ ((c k) ^ 2) ^ j := by positivity
    rw [Real.mul_rpow (by positivity) hck2_nn, Real.mul_rpow hKpow_nn hc02_nn]
    congr 1
    · congr 1
      · -- `((K^{k³})²)^{1/k} = K^{2k²}`
        have hexpK : ((k ^ 3 * 2 : ℕ) : ℝ) * (k : ℝ)⁻¹ = ((2 * k ^ 2 : ℕ) : ℝ) := by
          push_cast
          field_simp
        rw [← pow_mul, ← Real.rpow_natCast K (k ^ 3 * 2), ← Real.rpow_mul hKnn, hexpK,
          Real.rpow_natCast K (2 * k ^ 2)]
      · -- `(((c 0)²)^{k-j})^{1/k} = ((c 0)²)^{1 - j/k}`
        have hexp0 : ((k - j : ℕ) : ℝ) * (k : ℝ)⁻¹ = (1 : ℝ) - (j : ℝ) / k := by
          rw [hcast_sub]
          field_simp
        rw [← Real.rpow_natCast ((c 0) ^ 2) (k - j), ← Real.rpow_mul (by positivity), hexp0]
    · -- `(((c k)²)^j)^{1/k} = ((c k)²)^{j/k}`
      rw [← Real.rpow_natCast ((c k) ^ 2) j, ← Real.rpow_mul (by positivity), div_eq_mul_inv]
  rw [hrhs] at hmono
  -- Now substitute the endpoint identifications and the LHS, then fold the volume factor.
  rw [hcj_sq] at hmono
  rw [hc0_eq, hck_eq] at hmono
  -- `hmono` now reads: LHS ≤ K^{2k²}·((Λ₀·V)²)^{1-j/k}·(‖∇^k u‖_{L²}²)^{j/k}.
  -- Massage the endpoint powers to the displayed form.
  set ak : ℝ := Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
    (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun with hak_def
  have hak_nn : 0 ≤ ak := Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + k) _
  -- `(ak²)^{j/k} = ak^{2j/k}`.
  have hak_pow : (ak ^ 2) ^ ((j : ℝ) / k) = ak ^ (2 * (j : ℝ) / k) := by
    rw [← Real.rpow_natCast ak 2, ← Real.rpow_mul hak_nn]
    congr 1
    push_cast; ring
  -- `((Λ₀·V)²)^{1-j/k} = Λ₀^{2(1-j/k)}·(V²)^{1-j/k}` and `(V²)^{1-j/k} ≤ (max 1 V)²`.
  have hweight_nn : 0 ≤ (1 : ℝ) - (j : ℝ) / k := by
    have : (j : ℝ) / k ≤ 1 := by
      rw [div_le_one hkRpos]; exact_mod_cast le_of_lt hjk
    linarith
  have hweight_le1 : (1 : ℝ) - (j : ℝ) / k ≤ 1 := by
    have : 0 ≤ (j : ℝ) / k := by positivity
    linarith
  have hLV_pow : ((Λ₀ * V) ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) =
      Λ₀ ^ (2 * ((1 : ℝ) - (j : ℝ) / k)) * (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) := by
    rw [mul_pow, Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast Λ₀ 2, ← Real.rpow_mul hΛ₀]
    norm_num
  -- `(V²)^{1-j/k} ≤ (max 1 V)²`.
  have hV2_le : (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) ≤ (max 1 V) ^ 2 := by
    have hV2_nn : 0 ≤ V ^ 2 := by positivity
    have h2max : (1 : ℝ) ≤ (max 1 V) ^ 2 := by
      have := pow_le_pow_left₀ (zero_le_one) hmax1 2
      rwa [one_pow] at this
    rcases le_total (V ^ 2) 1 with hle | hge
    · -- base ≤ 1: rpow to a nonnegative weight stays ≤ 1 ≤ (max 1 V)².
      have h1 : (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) ≤ 1 :=
        Real.rpow_le_one hV2_nn hle hweight_nn
      linarith
    · -- base ≥ 1: monotone in the exponent (≤ 1), so ≤ (V²)^1 = V² ≤ (max 1 V)².
      have h1 : (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) ≤ (V ^ 2) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hge hweight_le1
      rw [Real.rpow_one] at h1
      have hV2_le_max : V ^ 2 ≤ (max 1 V) ^ 2 := pow_le_pow_left₀ hVnn hmaxV 2
      linarith
  -- Assemble: chain `hmono` through the endpoint massaging and the volume fold.
  calc (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toSection x)) ^ ((k : ℝ) / j)
          ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((j : ℝ) / k)
      ≤ K ^ (2 * k ^ 2) * ((Λ₀ * V) ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k) * (ak ^ 2) ^ ((j : ℝ) / k) :=
        hmono
    _ = K ^ (2 * k ^ 2) *
          (Λ₀ ^ (2 * ((1 : ℝ) - (j : ℝ) / k)) * (V ^ 2) ^ ((1 : ℝ) - (j : ℝ) / k)) *
          ak ^ (2 * (j : ℝ) / k) := by rw [hLV_pow, hak_pow]
    _ ≤ K ^ (2 * k ^ 2) *
          (Λ₀ ^ (2 * ((1 : ℝ) - (j : ℝ) / k)) * (max 1 V) ^ 2) *
          ak ^ (2 * (j : ℝ) / k) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left hV2_le (by positivity)
    _ = (K ^ (2 * k ^ 2) * (max 1 V) ^ 2) * Λ₀ ^ (2 * (1 - (j : ℝ) / k)) *
          ak ^ (2 * (j : ℝ) / k) := by ring
    _ = C * Λ₀ ^ (2 * (1 - (j : ℝ) / k)) * ak ^ (2 * (j : ℝ) / k) := by rw [hC]

end DifferentialGeometry.Analysis.Sobolev.Tensor

end
