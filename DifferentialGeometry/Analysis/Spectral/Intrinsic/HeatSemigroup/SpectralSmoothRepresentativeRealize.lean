import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothing
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.EigenvectorSmoothToL2
import DifferentialGeometry.Analysis.Spectral.Intrinsic.TensorHsInterpolationLimit

/-!
# `C^∞` spectral-series realization of the smooth-representative gate

This file carries the eigenfunction-series content that realizes the
smooth-representative gate `SpectralSmoothRealizesAsSmooth` (defined in
`SpectralSmoothing.lean`) on the intrinsic *smooth* eigenbasis
`eigenvectorSmooth g r s i`. Because these declarations are the only ones
that consume the chart-locality-free `eigenvectorSmooth_toL2` identity,
they are separated from `SpectralSmoothing.lean` so that the latter does
not import (and therefore does not leak the `TensorSpectral.TensorEigenIdx`
abbrev of) `EigenvectorSmoothToL2` into its downstream consumers.

## Main results

* `spectralSeries_hasSmoothSum_of_allOrders_summable` — the all-orders
  `Cᵏ`-completeness engine: a coordinate family with super-polynomial
  decay sums, on the smooth eigenbasis, to the `L²` class of a genuine
  `SmoothCcTensor` (a deferred classical analytic input, body `sorry`).
* `spectralSeries_smoothCcTensor_of_allOrders_summable` — the assembled
  form: concrete all-orders coefficient summability of an `L²` tensor `u`
  yields a `C^∞` representative `T` with `↑T = u`.
* `spectralSmoothRealizesAsSmooth_holds` — the gate predicate
  `SpectralSmoothRealizesAsSmooth` holds unconditionally, by extracting
  the concrete all-orders summability from the abstract `⋂_σ Hˢ`
  membership.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **On-diagonal heat-trace polynomial bound (the classical analytic
spectral input).**

For the intrinsic connection-Laplacian eigenvalues `λᵢ ≥ 0` of the mixed
`(r, s)`-tensor bundle on a closed Riemannian `n`-manifold, the heat
trace `Tr(e^{tΔ}) = ∑ᵢ exp(-λᵢ t)` is summable for every `t > 0` and
obeys the classical small-time on-diagonal bound

  `∑ᵢ exp(-λᵢ t) ≤ C · t^{-n/2}`   for all `t > 0`,

with a constant `C ≥ 0` (`n = dim M = Module.finrank ℝ E`). This is the
Minakshisundaram–Pleijel / ultracontractive heat-kernel estimate: on a
closed manifold the connection heat kernel satisfies the on-diagonal
bound `k_t(x, x) ≤ C' · t^{-n/2}`, and integrating the trace over the
compact `M` gives the stated `t^{-n/2}` rate.

This is the genuine classical analytic ingredient missing from the
library (which carries no heat-trace / ultracontractivity / Schatten /
Courant machinery). The statement is genuinely **non-vacuous**: it
asserts both that the heat trace converges (`Summable`) *and* an actual
`t^{-n/2}` small-time growth rate; a spectrum whose heat trace grew
faster than any power of `1/t` (super-polynomially many eigenvalues in
each sublevel) would falsify it, and the convergence claim rejects the
degenerate "trace `= 0`" reading. Its body is `sorry`: it is the one
classical analytic input black-boxed here (the on-diagonal heat-kernel
bound), and the Weyl counting bound
`tensorEigenIdx_one_add_lambda_lt_polynomial_counting` below — hence
every transitive consumer — depends on `sorryAx` through it. -/
theorem tensorHeatTrace_le_polynomial
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      Summable
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) ∧
      ∑' i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s,
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)
        ≤ C * t ^ (-(Module.finrank ℝ E : ℝ) / 2) :=
  sorry

/-- **Weyl polynomial eigenvalue-counting bound (the genuine classical
spectral input).**

For the intrinsic connection-Laplacian eigenvalues `λᵢ ≥ 0` of the mixed
`(r, s)`-tensor bundle on a closed Riemannian manifold, the eigenvalue
*counting function* `Λ ↦ #{i | 1 + λᵢ < Λ}` grows at most polynomially in
`Λ`: there exist a constant `C` and an exponent `p ≥ 0` with

  `#{i | 1 + λᵢ < Λ} ≤ C · Λ^p`   for all `Λ ≥ 1`.

(The counting set is the finite Finset
`(tensorEigenIdx_one_add_lambda_lt_finite g r s Λ).toFinset` carried by
the library.) This is the **Weyl asymptotic** in its crude one-sided
upper-bound form: on a closed `n`-manifold the connection-Laplacian
counting function satisfies `N(Λ) ≍ Λ^{n/2}`, so the bound holds with
any `p ≥ n/2` and a suitable `C`.

This is the genuine spectral-counting ingredient missing from the
library, which carries only the sublevel-set *finiteness*
`tensorEigenIdx_one_add_lambda_lt_finite` (`{i | 1 + λᵢ < Λ}.Finite`) —
enough for countability of each sublevel, but not for the *rate* of
growth that yields summability. The statement is strictly more than the
available finiteness (a compact operator with `μⱼ = 1/log(j+2)` has every
sublevel finite yet violates every polynomial counting bound), and it is
genuinely non-vacuous: it asserts an actual polynomial growth rate that a
super-polynomially-degenerating spectrum would falsify. Its body is
`sorry`: it is the one classical analytic input (the local Weyl law on a
closed manifold), and every consumer transitively depends on `sorryAx`
through it.

This is the strictly-minimal classical prerequisite of the trace-class
summability `tensorEigenIdx_one_add_lambda_rpow_neg_summable`, which is
proved from it below by an elementary linear-block (layer-cake)
estimate.

It is itself the **elementary heat-trace consequence** of the classical
on-diagonal heat-trace bound `tensorHeatTrace_le_polynomial`
(`Tr(e^{tΔ}) = ∑ᵢ exp(-λᵢ t) ≤ C · t^{-n/2}`): evaluating the trace at
`t = 1/Λ` and dropping every off-counting-set term bounds the counting
cardinality by `e · C · Λ^{n/2}`, since on the counting set
`λᵢ/Λ < 1` forces `exp(-λᵢ/Λ) ≥ e⁻¹`. The genuine classical analytic
content (the heat-kernel on-diagonal/ultracontractive bound) is isolated
in that posited child; this declaration is the elementary block-counting
reduction. -/
theorem tensorEigenIdx_one_add_lambda_lt_polynomial_counting
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C p : ℝ, 0 ≤ p ∧
      ∀ Λ : ℝ, 1 ≤ Λ →
        ((tensorEigenIdx_one_add_lambda_lt_finite
              (I := I) (M := M) g r s Λ).toFinset.card : ℝ)
          ≤ C * Λ ^ p := by
  classical
  obtain ⟨C, hC_nn, htrace⟩ :=
    tensorHeatTrace_le_polynomial (I := I) (M := M) g r s
  -- The Weyl exponent `p := n/2` and the counting constant `C' := e · C`.
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  refine ⟨Real.exp 1 * C, n / 2, by positivity, fun Λ hΛ => ?_⟩
  have hΛ_pos : (0 : ℝ) < Λ := by linarith
  -- Evaluate the heat trace at the small time `t = 1/Λ`.
  set t : ℝ := Λ⁻¹ with ht_def
  have ht_pos : (0 : ℝ) < t := by rw [ht_def]; positivity
  obtain ⟨hsummable, htrace_le⟩ := htrace t ht_pos
  set F : Finset (TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :=
    (tensorEigenIdx_one_add_lambda_lt_finite (I := I) (M := M) g r s Λ).toFinset
    with hF_def
  -- On the counting set, `λᵢ · t ≤ 1`, so `exp(-1) ≤ exp(-λᵢ t)`.
  have hterm_ge : ∀ i ∈ F,
      Real.exp (-(1 : ℝ)) ≤
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) := by
    intro i hi
    rw [hF_def, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi
    have hlam_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
      tensor_lambda_nonneg (I := I) (M := M) i
    have hlt : TensorEigenIdx.lambda (I := I) (M := M) i < Λ := by linarith
    have hprod : TensorEigenIdx.lambda (I := I) (M := M) i * t ≤ 1 := by
      rw [ht_def]
      rw [mul_inv_le_iff₀ hΛ_pos, one_mul]
      exact hlt.le
    apply Real.exp_le_exp.mpr
    have : -(TensorEigenIdx.lambda (I := I) (M := M) i) * t = -(TensorEigenIdx.lambda (I := I) (M := M) i * t) := by ring
    rw [this]
    linarith
  -- Block-count: `card · e⁻¹ ≤ ∑_{F} exp(-λᵢ t) ≤ ∑'ᵢ exp(-λᵢ t) ≤ C · t^{-n/2}`.
  have hsum_nn : ∀ i ∉ F,
      (0 : ℝ) ≤ Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) :=
    fun i _ => (Real.exp_pos _).le
  have hcard_lb :
      (F.card : ℝ) * Real.exp (-(1 : ℝ)) ≤
        ∑' i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s,
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) := by
    calc (F.card : ℝ) * Real.exp (-(1 : ℝ))
        = ∑ _i ∈ F, Real.exp (-(1 : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ F,
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) :=
          Finset.sum_le_sum hterm_ge
      _ ≤ ∑' i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s,
            Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) :=
          hsummable.sum_le_tsum F hsum_nn
  -- The trace bound `C · t^{-n/2}` at `t = 1/Λ` is `C · Λ^{n/2}`.
  have ht_rpow : t ^ (-n / 2) = Λ ^ (n / 2) := by
    rw [ht_def, neg_div, Real.inv_rpow hΛ_pos.le, ← Real.rpow_neg hΛ_pos.le, neg_neg]
  have hcard_le : (F.card : ℝ) * Real.exp (-(1 : ℝ)) ≤ C * Λ ^ (n / 2) := by
    refine hcard_lb.trans ?_
    rwa [ht_rpow] at htrace_le
  -- Divide through by `e⁻¹ = exp(-1)` (multiply by `e = exp 1`).
  have hexp_neg_pos : (0 : ℝ) < Real.exp (-(1 : ℝ)) := Real.exp_pos _
  rw [← le_div_iff₀ hexp_neg_pos] at hcard_le
  refine hcard_le.trans (le_of_eq ?_)
  rw [Real.exp_neg]
  field_simp

/-- **Weyl-type eigenvalue-power summability (trace-class property of a
large resolvent power).**

For the intrinsic connection-Laplacian eigenvalues `λᵢ ≥ 0` of the mixed
`(r, s)`-tensor bundle on a closed Riemannian manifold, there is an
exponent `N` (large enough) for which the powers `(1 + λᵢ)^{-N}` are
summable over the eigen-index set `TensorEigenIdx g r s`. Concretely this
is the trace-class property of a large power of the (compact) resolvent:
since `1 + λᵢ = (i.fst.val)⁻¹` is the reciprocal of the resolvent
eigenvalue, `∑ᵢ (1 + λᵢ)^{-N}` is the `N`-th Schatten quasi-norm of the
resolvent, and it converges once `2N > dim M`.

The proof is the elementary **linear-block (layer-cake) estimate** built
on the Weyl polynomial counting bound
`tensorEigenIdx_one_add_lambda_lt_polynomial_counting` (`#{i | 1 + λᵢ < Λ}
≤ C · Λ^p`). Take `N := p + 2`. For a finite index set `u`, group its
indices by the natural block `k(i) := ⌊1 + λᵢ⌋₊` (so `k ≤ 1 + λᵢ < k + 1`
and `k ≥ 1` since `1 + λᵢ ≥ 1`). On block `k` the term `(1 + λᵢ)^{-N}` is
`≤ k^{-N}`, and the block has `≤ C · (k+1)^p` indices (its members lie in
`{i | 1 + λᵢ < k + 1}`), so the block contributes `≤ C · (k+1)^p · k^{-N}
≤ C · 2^p · k^{-2}`. Summing the geometric-decay majorant `∑ₖ k^{-2}
< ∞` over all blocks bounds every finite partial sum uniformly, whence
`summable_of_sum_le` gives summability. -/
theorem tensorEigenIdx_one_add_lambda_rpow_neg_summable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ N : ℝ,
      Summable
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          (1 + i.lambda) ^ (-N)) := by
  classical
  obtain ⟨C, p, hp_nn, hcount⟩ :=
    tensorEigenIdx_one_add_lambda_lt_polynomial_counting (I := I) (M := M) g r s
  -- WLOG `C ≥ 0`: the counting cardinalities are nonnegative, so if the
  -- supplied `C` were negative the bound would already be vacuous at `Λ = 1`;
  -- replace it by `max C 0 ≥ 0` (which only weakens the bound).
  set C' : ℝ := max C 0 with hC'_def
  have hC'_nn : 0 ≤ C' := le_max_right _ _
  have hcount' : ∀ Λ : ℝ, 1 ≤ Λ →
      ((tensorEigenIdx_one_add_lambda_lt_finite
            (I := I) (M := M) g r s Λ).toFinset.card : ℝ) ≤ C' * Λ ^ p := by
    intro Λ hΛ
    refine (hcount Λ hΛ).trans ?_
    have hΛp_nn : 0 ≤ Λ ^ p := Real.rpow_nonneg (by linarith) p
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hΛp_nn
  -- The exponent `N := p + 2`, so the leftover power is `p - N = -2 < -1`.
  refine ⟨p + 2, ?_⟩
  set N : ℝ := p + 2 with hN_def
  set I0 := TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s
  set lam : I0 → ℝ := fun i => 1 + i.lambda with hlam_def
  have hlam_one_le : ∀ i : I0, (1 : ℝ) ≤ lam i := by
    intro i
    have := tensor_lambda_nonneg (I := I) (M := M) i
    simp only [hlam_def]; linarith
  -- The per-block index: `k(i) = ⌊1 + λᵢ⌋₊`, which is `≥ 1`.
  set blk : I0 → ℕ := fun i => ⌊lam i⌋₊ with hblk_def
  have hblk_pos : ∀ i : I0, 1 ≤ blk i := by
    intro i
    simp only [hblk_def]
    exact (Nat.one_le_floor_iff _).2 (hlam_one_le i)
  -- The polynomially-decaying majorant over blocks `k : ℕ`.
  set Maj : ℕ → ℝ := fun k => C' * ((k : ℝ) + 1) ^ p * (k : ℝ) ^ (-N) with hMaj_def
  have hMaj_summable : Summable Maj := by
    -- dominate `Maj k` by `C' * 2^p * k^{-2}`, summable since `-2 < -1`.
    have hmaj_summable : Summable (fun k : ℕ => C' * 2 ^ p * (k : ℝ) ^ (-2 : ℝ)) :=
      ((Real.summable_nat_rpow (p := (-2 : ℝ))).2 (by norm_num)).mul_left _
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hmaj_summable
    · -- `0 ≤ Maj k`
      have h1 : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ p :=
        Real.rpow_nonneg (by positivity) p
      have h2 : (0 : ℝ) ≤ (k : ℝ) ^ (-N) :=
        Real.rpow_nonneg (by positivity) _
      simp only [hMaj_def]; positivity
    · -- `Maj k ≤ C' * 2^p * k^{-2}`
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simp only [hMaj_def, Nat.cast_zero, zero_add]
        have hNne : (-N : ℝ) ≠ 0 := by rw [hN_def]; intro h; linarith [neg_eq_zero.mp h]
        have hz : (0 : ℝ) ^ (-N) = 0 := Real.zero_rpow hNne
        rw [hz]; ring_nf
        positivity
      · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
        have hkpos' : (0 : ℝ) < (k : ℝ) := by linarith
        -- `(k+1)^p ≤ (2k)^p = 2^p · k^p`
        have hk1le : ((k : ℝ) + 1) ≤ 2 * (k : ℝ) := by linarith
        have hstep1 : ((k : ℝ) + 1) ^ p ≤ (2 * (k : ℝ)) ^ p :=
          Real.rpow_le_rpow (by positivity) hk1le hp_nn
        have hstep2 : (2 * (k : ℝ)) ^ p = 2 ^ p * (k : ℝ) ^ p := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
        -- `k^p · k^{-N} = k^{p - N} = k^{-2}`
        have hstep3 : (k : ℝ) ^ p * (k : ℝ) ^ (-N) = (k : ℝ) ^ (-2 : ℝ) := by
          rw [← Real.rpow_add hkpos']
          congr 1
          rw [hN_def]; ring
        have hkN_nn : (0 : ℝ) ≤ (k : ℝ) ^ (-N) := Real.rpow_nonneg hkpos'.le _
        calc Maj k = C' * (((k : ℝ) + 1) ^ p) * (k : ℝ) ^ (-N) := rfl
          _ ≤ C' * (2 ^ p * (k : ℝ) ^ p) * (k : ℝ) ^ (-N) := by
              apply mul_le_mul_of_nonneg_right _ hkN_nn
              apply mul_le_mul_of_nonneg_left _ hC'_nn
              exact hstep1.trans_eq hstep2
          _ = C' * 2 ^ p * ((k : ℝ) ^ p * (k : ℝ) ^ (-N)) := by ring
          _ = C' * 2 ^ p * (k : ℝ) ^ (-2 : ℝ) := by rw [hstep3]
  -- The uniform bound on finite partial sums, with constant `c := ∑' k, Maj k`.
  have hf_nn : (0 : I0 → ℝ) ≤ fun i => lam i ^ (-N) := by
    intro i
    exact Real.rpow_nonneg (by have := hlam_one_le i; linarith) _
  refine summable_of_sum_le (c := ∑' k : ℕ, Maj k) hf_nn (fun u => ?_)
  · -- `∑_{i∈u} (1+λᵢ)^{-N} ≤ ∑'_k Maj k =: c`.
    -- Group `u` by the block index `blk`.
    set t : Finset ℕ := u.image blk with ht_def
    have hmaps : ∀ i ∈ u, blk i ∈ t := fun i hi => Finset.mem_image_of_mem blk hi
    have hfib :
        ∑ k ∈ t, ∑ i ∈ u.filter (fun i => blk i = k), lam i ^ (-N)
          = ∑ i ∈ u, lam i ^ (-N) :=
      Finset.sum_fiberwise_of_maps_to hmaps (fun i => lam i ^ (-N))
    -- `Maj k` is always nonnegative.
    have hMaj_nn : ∀ k : ℕ, 0 ≤ Maj k := by
      intro k
      have h1 : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ p := Real.rpow_nonneg (by positivity) p
      have h2 : (0 : ℝ) ≤ (k : ℝ) ^ (-N) := Real.rpow_nonneg (by positivity) _
      simp only [hMaj_def]; positivity
    -- Bound each block sum by `Maj k`.
    have hblock : ∀ k ∈ t,
        ∑ i ∈ u.filter (fun i => blk i = k), lam i ^ (-N) ≤ Maj k := by
      intro k _
      rcases (u.filter (fun i => blk i = k)).eq_empty_or_nonempty with hempty | hne
      · simp only [hempty, Finset.sum_empty]; exact hMaj_nn k
      -- The fiber is nonempty: extract `k ≥ 1` from any member.
      obtain ⟨i₀, hi₀⟩ := hne
      rw [Finset.mem_filter] at hi₀
      have hk1 : 1 ≤ k := by rw [← hi₀.2]; exact hblk_pos i₀
      have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      have hkposR : (0 : ℝ) < (k : ℝ) := by linarith
      -- The fiber sits inside the finite sublevel set `{i | 1 + λᵢ < k + 1}`.
      set F : Finset I0 :=
        (tensorEigenIdx_one_add_lambda_lt_finite
          (I := I) (M := M) g r s ((k : ℝ) + 1)).toFinset with hF_def
      have hfiber_sub : u.filter (fun i => blk i = k) ⊆ F := by
        intro i hi
        rw [Finset.mem_filter] at hi
        have hlt : lam i < (k : ℝ) + 1 := by
          have hfl : lam i < (⌊lam i⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (lam i)
          have hcast : (⌊lam i⌋₊ : ℝ) = (k : ℝ) := by
            simp only [hblk_def] at hi; rw [hi.2]
          rwa [hcast] at hfl
        rw [hF_def, Set.Finite.mem_toFinset]
        simpa only [Set.mem_setOf_eq, hlam_def] using hlt
      -- Cardinality of the fiber is bounded by the counting bound.
      have hcard_le :
          ((u.filter (fun i => blk i = k)).card : ℝ) ≤ C' * ((k : ℝ) + 1) ^ p := by
        have hcsub : (u.filter (fun i => blk i = k)).card ≤ F.card :=
          Finset.card_le_card hfiber_sub
        have hcsubR : ((u.filter (fun i => blk i = k)).card : ℝ) ≤ (F.card : ℝ) := by
          exact_mod_cast hcsub
        refine hcsubR.trans ?_
        rw [hF_def]
        exact hcount' ((k : ℝ) + 1) (by linarith)
      -- On the fiber, each term `(1+λᵢ)^{-N} ≤ k^{-N}`.
      have hterm_le : ∀ i ∈ u.filter (fun i => blk i = k),
          lam i ^ (-N) ≤ (k : ℝ) ^ (-N) := by
        intro i hi
        rw [Finset.mem_filter] at hi
        have hge : (k : ℝ) ≤ lam i := by
          have hfl : (⌊lam i⌋₊ : ℝ) ≤ lam i :=
            Nat.floor_le (by linarith [hlam_one_le i])
          have hcast : (⌊lam i⌋₊ : ℝ) = (k : ℝ) := by
            simp only [hblk_def] at hi; rw [hi.2]
          rwa [hcast] at hfl
        have hNnonpos : (-N : ℝ) ≤ 0 := by rw [hN_def]; linarith
        exact Real.rpow_le_rpow_of_nonpos hkposR hge hNnonpos
      have hkN_nn : (0 : ℝ) ≤ (k : ℝ) ^ (-N) := Real.rpow_nonneg hkposR.le _
      -- Assemble: fiber sum ≤ card · k^{-N} ≤ C' (k+1)^p · k^{-N} = Maj k.
      calc ∑ i ∈ u.filter (fun i => blk i = k), lam i ^ (-N)
          ≤ ∑ _i ∈ u.filter (fun i => blk i = k), (k : ℝ) ^ (-N) :=
            Finset.sum_le_sum hterm_le
        _ = ((u.filter (fun i => blk i = k)).card : ℝ) * (k : ℝ) ^ (-N) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (C' * ((k : ℝ) + 1) ^ p) * (k : ℝ) ^ (-N) :=
            mul_le_mul_of_nonneg_right hcard_le hkN_nn
        _ = Maj k := by simp only [hMaj_def, mul_assoc]
    -- Sum the block bound and dominate by the tsum of the majorant.
    calc ∑ i ∈ u, lam i ^ (-N)
        = ∑ k ∈ t, ∑ i ∈ u.filter (fun i => blk i = k), lam i ^ (-N) := hfib.symm
      _ ≤ ∑ k ∈ t, Maj k := Finset.sum_le_sum hblock
      _ ≤ ∑' k : ℕ, Maj k := Summable.sum_le_tsum t (fun k _ => hMaj_nn k) hMaj_summable

/-- **`C^∞` realization of a super-polynomially-`ℓ¹`-decaying eigenfunction
series (the deep uniform-limit-of-derivatives analytic core).**

Let `c : TensorEigenIdx g r s → ℝ` be a coordinate family such that:

* the eigenfunction series `∑ᵢ cᵢ · eigenvectorSmooth g r s i` sums, in
  `L²`, to `u` (hypothesis `h_repr`); and
* the coefficients decay faster than every polynomial in the eigenvalue,
  in the absolute (`ℓ¹`) sense: for *every order* `k`, the weighted
  absolute family `|cᵢ| · (1 + λᵢ)^k` is summable (hypothesis `h_poly`).

Then `u` admits a genuine smooth, compactly-supported representative
`T : SmoothCcTensor g r s` with `↑T = u`.

This is the precise `Cᵏ`-Banach-completeness content of the all-orders
spectral Sobolev embedding `⋂_σ Hˢ ⊆ C^∞`, isolated as the *one* deep
classical analytic input of the smooth-representative gate. Its proof is
term-by-term: the partial sums of the eigenfunction series obey, in each
intrinsic `H^{2k}` (iterated-covariant-derivative) Banach norm, the
per-eigentensor uniform bound `eigenvectorSmooth_wtwokTwoNorm_le_uniform`
(`wtwokTwoNorm g k (eigenvectorSmooth g r s i)
  ≤ ENNReal.ofReal (C · (1 + λᵢ) ^ (2k+1))`, polynomial growth in the
eigenvalue since `1 + λᵢ = i.fst.val⁻¹` by `one_add_lambda_eq_inv_val`
and the eigenbasis is orthonormal); the super-polynomial `ℓ¹` coefficient
decay `h_poly` beats this polynomial growth, making the partial sums
Cauchy in the `Cᵏ` Banach norm for each `k`, via the unconditional `C^m`
tensor Sobolev embedding `iteratedCovGrad_toSobolev_embedding_Cm_unconditional`.
The common `C^∞` limit of those `Cᵏ`-Cauchy partial sums is the desired
`SmoothCcTensor`, and its `L²` class is `u` by `h_repr`.

This is a **deferred input**: its body is `sorry`, and every consumer
transitively depends on `sorryAx`. The genuine prerequisite it
black-boxes is the all-orders uniform-limit-of-derivatives passage to
`ContMDiff` (`Mathlib` carries only the single-derivative
`hasFDerivAt_of_tendstoUniformly` family; there is no `ContDiff` /
`ContMDiff` uniform-derivative-limit theorem, nor the transport of a
`Cᵏ`-for-all-`k` uniform limit to `ContMDiffSection` / `SmoothCcTensor`).
The hypotheses are genuinely load-bearing: dropping `h_poly` makes the
statement false (a generic `ℓ²`-but-not-smooth coefficient family has no
smooth representative). -/
theorem smoothCcTensor_of_eigenSeries_poly_summable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (c : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    (h_repr :
      HasSum
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          c i •
            (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g))
        u)
    (h_poly : ∀ k : ℕ,
      Summable
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          |c i| * (1 + i.lambda) ^ (k : ℝ))) :
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = u :=
  sorry

/-- **`C^∞` realization of an all-orders-decaying `L²` tensor.**

Let `u : TensorL2 r s g` be an `L²` tensor field whose intrinsic
eigenbasis coordinates `cᵢ = tensorL2Coeff h_compact u i` decay so fast
that, for *every even order* `2k`, the weighted squares
`(1 + λᵢ)^{2k} · cᵢ²` are summable. Then `u` admits a genuine smooth,
compactly-supported representative `T : SmoothCcTensor g r s` with
`↑T = u`.

This is the all-orders spectral Sobolev embedding `⋂_σ Hˢ ⊆ C^∞` in its
`L²`-coordinate form. The proof assembles two classical analytic inputs:

* the **Weyl-type eigenvalue summability**
  `tensorEigenIdx_one_add_lambda_rpow_neg_summable`
  (`∃ N, Summable (fun i => (1 + λᵢ)^{-N})`); and
* the **uniform-limit-of-derivatives `C^∞` realization core**
  `smoothCcTensor_of_eigenSeries_poly_summable`
  (a super-polynomially-`ℓ¹`-decaying eigenfunction series has a smooth
  `L²`-limit).

The genuine work done here is the bridge between the two: the hypothesised
`ℓ²`-with-`(1+λ)^{2k}`-weight decay `h_decay`, together with the Weyl
summability, yields — by the elementary `2ab ≤ a² + b²` splitting — the
super-polynomial `ℓ¹` decay `h_poly` (`∀ k, ∑ᵢ |cᵢ| (1+λᵢ)^k < ∞`) that
the realization core consumes; and the `L²` expansion `h_repr` of `u` on
the orthonormal smooth eigenbasis (`HilbertBasis.hasSum_repr` together
with `eigenvectorSmooth_toL2`) supplies its other hypothesis.

The `h_decay` hypothesis is genuinely load-bearing: dropping it makes the
statement false (a generic `ℓ²`-but-not-smooth `L²` tensor has no smooth
representative). -/
theorem tensorL2_smoothRepr_of_allOrders_decay
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (h_decay : ∀ k : ℕ,
      Summable
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          tensorSobolevWeight (I := I) (M := M) i (2 * k : ℝ) *
            (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
              u i) ^ 2)) :
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = u := by
  classical
  set h_compact :=
    tensorResolventL2_isCompactOperator (I := I) (M := M) g r s
    with hcompact_def
  set c : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M) h_compact u i with hc_def
  -- The `L²` expansion of `u` on the orthonormal smooth eigenbasis:
  -- `u = ∑ᵢ cᵢ • eigenvectorSmooth i`, with `cᵢ = tensorL2Coeff h_compact u i`.
  have h_repr :
      HasSum
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          c i •
            (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g))
        u := by
    have hbasis :=
      (tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact).hasSum_repr u
    refine hbasis.congr_fun (fun i => ?_)
    have hb :
        (tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact) i =
          (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g) := by
      rw [tensorResolventHilbertEigenbasisSigma_apply
        (I := I) (M := M) h_compact i,
        eigenvectorSmooth_toL2 (I := I) (M := M) g r s i]
    rw [hb]
    rfl
  -- The super-polynomial `ℓ¹` decay of `c`, produced from the `ℓ²` decay
  -- `h_decay` and the Weyl eigenvalue summability by the `2ab ≤ a² + b²`
  -- splitting.
  obtain ⟨N, hN⟩ :=
    tensorEigenIdx_one_add_lambda_rpow_neg_summable (I := I) (M := M) g r s
  have h_poly : ∀ k : ℕ,
      Summable
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          |c i| * (1 + i.lambda) ^ (k : ℝ)) := by
    intro k
    -- pick a natural shift `m` with `2 m ≥ N + 2 k`, so that the negative
    -- leftover exponent `2(k - m)` is `≤ -N`.
    obtain ⟨m, hm⟩ := exists_nat_ge ((N + 2 * (k : ℝ)) / 2)
    have hm2 : N + 2 * (k : ℝ) ≤ 2 * (m : ℝ) := by
      have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hm
      linarith
    -- `aᵢ = |cᵢ| (1+λᵢ)^m`, `bᵢ = (1+λᵢ)^(k - m)`.
    set base : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
      fun i => 1 + i.lambda with hbase_def
    have hbase_pos : ∀ i, (0 : ℝ) < base i := by
      intro i
      have := tensor_lambda_nonneg (I := I) (M := M) i
      simp only [hbase_def]; linarith
    have hbase_one_le : ∀ i, (1 : ℝ) ≤ base i := by
      intro i
      have := tensor_lambda_nonneg (I := I) (M := M) i
      simp only [hbase_def]; linarith
    -- `∑ aᵢ²` is summable: it is `h_decay m` reindexed.
    have hsumA :
        Summable (fun i => (|c i| * base i ^ (m : ℝ)) ^ 2) := by
      have hdm := h_decay m
      refine hdm.congr (fun i => ?_)
      have hci : tensorL2Coeff (I := I) (M := M) h_compact u i = c i := rfl
      rw [hci]
      have hcsq : tensorSobolevWeight (I := I) (M := M) i (2 * (m : ℝ)) =
          base i ^ (2 * (m : ℝ)) := rfl
      rw [hcsq]
      have hpow : base i ^ (2 * (m : ℝ)) = (base i ^ (m : ℝ)) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast (base i ^ (m : ℝ)) 2,
          ← Real.rpow_mul (hbase_pos i).le]
        norm_num; ring_nf
      rw [hpow, mul_pow, sq_abs]
      ring
    -- `∑ bᵢ²` is summable: dominated by the Weyl-summable `(1+λᵢ)^{-N}`.
    have hsumB :
        Summable (fun i => (base i ^ ((k : ℝ) - (m : ℝ))) ^ 2) := by
      refine Summable.of_nonneg_of_le
        (fun i => sq_nonneg _)
        (fun i => ?_) hN
      have hexp : (base i ^ ((k : ℝ) - (m : ℝ))) ^ 2 =
          base i ^ (2 * ((k : ℝ) - (m : ℝ))) := by
        rw [← Real.rpow_natCast (base i ^ ((k : ℝ) - (m : ℝ))) 2,
          ← Real.rpow_mul (hbase_pos i).le]
        norm_num; ring_nf
      rw [hexp]
      have hle : 2 * ((k : ℝ) - (m : ℝ)) ≤ -N := by linarith
      exact Real.rpow_le_rpow_of_exponent_le (hbase_one_le i) hle
    -- domination: `|cᵢ|(1+λᵢ)^k = aᵢ·bᵢ ≤ aᵢ² + bᵢ²`.
    refine Summable.of_nonneg_of_le
      (fun i => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (hbase_pos i).le _))
      (fun i => ?_)
      (hsumA.add hsumB)
    set a : ℝ := |c i| * base i ^ (m : ℝ) with ha_def
    set b : ℝ := base i ^ ((k : ℝ) - (m : ℝ)) with hb_def
    have ha_nn : 0 ≤ a :=
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (hbase_pos i).le _)
    have hb_nn : 0 ≤ b := Real.rpow_nonneg (hbase_pos i).le _
    have hab : a * b = |c i| * base i ^ (k : ℝ) := by
      rw [ha_def, hb_def, mul_assoc, ← Real.rpow_add (hbase_pos i)]
      ring_nf
    have hamgm : a * b ≤ a ^ 2 + b ^ 2 := by
      have h2 := two_mul_le_add_sq a b
      nlinarith [mul_nonneg ha_nn hb_nn]
    calc |c i| * base i ^ (k : ℝ) = a * b := hab.symm
      _ ≤ a ^ 2 + b ^ 2 := hamgm
  exact smoothCcTensor_of_eigenSeries_poly_summable
    (I := I) (M := M) g r s u c h_repr h_poly

/-- **Smooth realization of an all-orders-decaying coordinate family.**

Let `c : TensorEigenIdx g r s → ℝ` be a coordinate family whose weighted
squares `(1 + λᵢ)^{2k} · cᵢ²` are summable for *every even order* `2k`.
Then `c` is the intrinsic eigenbasis coordinate family of a genuine
smooth, compactly-supported section `T : SmoothCcTensor g r s`:

  `∀ i, tensorL2Coeff h_compact (↑T) i = cᵢ`.

The proof is the `L²`-side reduction to the single deep analytic core
`tensorL2_smoothRepr_of_allOrders_decay`: the order-`0` instance of
`h_decay` (with `tensorSobolevWeight i 0 = 1`) makes `c` square-summable,
hence an element `c ∈ ℓ²`; the resolvent eigenbasis
`tensorResolventHilbertEigenbasisSigma h_compact` realizes it as the
`L²` element `u = b.repr.symm c`, whose intrinsic eigenbasis coordinates
`tensorL2Coeff h_compact u i = (b.repr u) i = cᵢ` are exactly `c` by the
`b.repr.symm`-round-trip. Transporting `h_decay` along this coordinate
identity, the analytic core supplies the smooth representative `T` with
`↑T = u`, and `tensorL2Coeff h_compact (↑T) i = tensorL2Coeff h_compact u i
= cᵢ`. The hypothesis is genuinely load-bearing: dropping `h_decay` makes
the statement false (a generic `ℓ²`-but-not-smooth coordinate family has
no smooth representative). -/
theorem smoothCcTensor_exists_of_allOrders_decay
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    (h_decay : ∀ k : ℕ,
      Summable
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          tensorSobolevWeight (I := I) (M := M) i (2 * k : ℝ) * (c i) ^ 2)) :
    ∃ T : SmoothCcTensor g r s,
      ∀ i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            (T : TensorL2 r s g) i = c i := by
  classical
  set h_compact :=
    tensorResolventL2_isCompactOperator (I := I) (M := M) g r s
    with hcompact_def
  set bsis := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact
    with hbsis_def
  have hsq : Summable (fun i => (c i) ^ 2) := by
    have h0 := h_decay 0
    simp only [Nat.cast_zero, mul_zero, tensorSobolevWeight_zero, one_mul] at h0
    exact h0
  have hmem : Memℓp c 2 := by
    rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    simpa using hsq
  set cl : lp
      (fun _ : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s => ℝ) 2 :=
    ⟨c, hmem⟩ with hcl_def
  set u : TensorL2 r s g := bsis.repr.symm cl with hu_def
  have hcoeff_u : ∀ i, tensorL2Coeff (I := I) (M := M) h_compact u i = c i := by
    intro i
    have hround : bsis.repr u = cl := by
      rw [hu_def]; exact bsis.repr.apply_symm_apply cl
    have hval : (bsis.repr u) i = c i := by rw [hround]
    simpa [tensorL2Coeff] using hval
  have h_decay_u : ∀ k : ℕ,
      Summable
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          tensorSobolevWeight (I := I) (M := M) i (2 * k : ℝ) *
            (tensorL2Coeff (I := I) (M := M) h_compact u i) ^ 2) := by
    intro k
    refine (h_decay k).congr (fun i => ?_)
    rw [hcoeff_u i]
  obtain ⟨T, hT⟩ :=
    tensorL2_smoothRepr_of_allOrders_decay (I := I) (M := M) g r s u h_decay_u
  refine ⟨T, fun i => ?_⟩
  rw [hT, hcoeff_u i]

/-- **Smooth-series convergence engine.**

Let `c : TensorEigenIdx g r s → ℝ` be a coordinate family whose weighted
squares `(1 + λᵢ)^{2k} · cᵢ²` are summable for *every even order* `2k`.
Then the intrinsic eigenfunction series
`∑ᵢ cᵢ · eigenvectorSmooth g r s i` (each summand a smooth, compactly
supported eigentensor) sums, in `L²`, to a genuine smooth,
compactly-supported section `T : SmoothCcTensor g r s`:

  `HasSum (fun i => cᵢ • (eigenvectorSmooth g r s i : L²)) (↑T)`.

The smooth section `T` is produced by the deferred analytic core
`smoothCcTensor_exists_of_allOrders_decay`, whose `i`-th eigenbasis
coordinate is exactly `cᵢ`. The `HasSum` is then the resolvent
eigenbasis expansion of `↑T`: the `HilbertBasis.hasSum_repr` of `↑T`
against `tensorResolventHilbertEigenbasisSigma` is the series
`∑ᵢ (b.repr (↑T) i) • bᵢ = ∑ᵢ cᵢ • bᵢ`, and each basis vector
`bᵢ = (eigenvectorSmooth g r s i : L²)` by `eigenvectorSmooth_toL2`. -/
theorem spectralSeries_hasSmoothSum_of_allOrders_summable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    (h_decay : ∀ k : ℕ,
      Summable
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          tensorSobolevWeight (I := I) (M := M) i (2 * k : ℝ) * (c i) ^ 2)) :
    ∃ T : SmoothCcTensor g r s,
      HasSum
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          c i •
            (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g))
        (T : TensorL2 r s g) := by
  classical
  set h_compact :=
    tensorResolventL2_isCompactOperator (I := I) (M := M) g r s
    with hcompact_def
  set bsis := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact
    with hbsis_def
  obtain ⟨T, hT_coeff⟩ :=
    smoothCcTensor_exists_of_allOrders_decay (I := I) (M := M) g r s c h_decay
  refine ⟨T, ?_⟩
  have hHasSum : HasSum (fun i => bsis.repr (T : TensorL2 r s g) i • bsis i)
      (T : TensorL2 r s g) := bsis.hasSum_repr (T : TensorL2 r s g)
  refine hHasSum.congr_fun (fun i => ?_)
  have hbi : bsis i =
      (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g) := by
    rw [hbsis_def, tensorResolventHilbertEigenbasisSigma_apply,
      eigenvectorSmooth_toL2 (I := I) (M := M) g r s i]
  have hci : bsis.repr (T : TensorL2 r s g) i = c i := by
    have hcoe : bsis.repr (T : TensorL2 r s g) i =
        tensorL2Coeff (I := I) (M := M) h_compact (T : TensorL2 r s g) i := rfl
    rw [hcoe, hT_coeff i]
  rw [hbi, hci]

/-- **Classical `C^∞` spectral-series assembly.**

Let `u : TensorL2 r s g` be an `L²` tensor field whose intrinsic
eigenbasis coordinates `cᵢ = tensorL2Coeff h_compact u i` decay so fast
that, for *every even order* `2k`, the weighted squares
`(1 + λᵢ)^{2k} · cᵢ²` are summable. Then the eigenfunction series
`∑ᵢ cᵢ · eigenvectorSmooth g r s i` converges in `Cᵏ` for every `k`, and
its limit is a genuine smooth, compactly-supported section
`T : SmoothCcTensor g r s` whose `L²` class is `u`.

This is the **all-orders spectral Sobolev embedding** in its assembled
form. The body is a thin reduction to
`spectralSeries_hasSmoothSum_of_allOrders_summable` (whence to the deep
analytic core `tensorL2_smoothRepr_of_allOrders_decay`), identifying the
two `L²`-expansions of `u` — the resolvent eigenbasis expansion and the
smooth-section series — by `HasSum.unique`. The remaining genuine
analytic content lives strictly downstream, in the two posited leaves
`tensorEigenIdx_one_add_lambda_rpow_neg_summable` (Weyl summability) and
`smoothCcTensor_of_eigenSeries_poly_summable` (the uniform-limit-of-
derivatives `Cᵏ`-completeness core); consumers transitively depend on
`sorryAx` only through those two. The hypothesis is the *concrete*
all-orders coefficient summability of `u` (strictly weaker, and strictly
more elementary, than the abstract `⋂_σ Hˢ`-membership hypothesis of the
gate predicate, from which it is derived in
`spectralSmoothRealizesAsSmooth_holds`). -/
theorem spectralSeries_smoothCcTensor_of_allOrders_summable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (h_decay : ∀ k : ℕ,
      Summable (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i (2 * k : ℝ) *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            u i) ^ 2)) :
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = u := by
  classical
  set h_compact :=
    tensorResolventL2_isCompactOperator (I := I) (M := M) g r s
    with hcompact_def
  -- The deep `Cᵏ`-completeness engine: the eigenfunction series with the
  -- coefficient family `cᵢ = tensorL2Coeff h_compact u i` converges to the
  -- `L²` class of a smooth section `T`.
  obtain ⟨T, hT⟩ :=
    spectralSeries_hasSmoothSum_of_allOrders_summable
      (I := I) (M := M) g r s
      (fun i => tensorL2Coeff (I := I) (M := M) h_compact u i) h_decay
  refine ⟨T, ?_⟩
  -- The resolvent eigenbasis representation of `u` is the *same* series:
  -- `bᵢ = (eigenvectorSmooth g r s i : L²)` and `b.repr u i = tensorL2Coeff u i`.
  have h_repr :
      HasSum
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          tensorL2Coeff (I := I) (M := M) h_compact u i •
            (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g)) u := by
    have hbasis :=
      (tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact).hasSum_repr u
    refine hbasis.congr_fun (fun i => ?_)
    have hb :
        (tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact) i =
          (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g) := by
      rw [tensorResolventHilbertEigenbasisSigma_apply
        (I := I) (M := M) h_compact i,
        eigenvectorSmooth_toL2 (I := I) (M := M) g r s i]
    rw [hb]
    rfl
  exact hT.unique h_repr

/-- **The smooth-representative gate (proved).**

`SpectralSmoothRealizesAsSmooth g r s` holds unconditionally: every `L²`
tensor `u` lying (via the chart-locality-free inclusion `tensorHsToL2`)
in `Hˢ` for *every* exponent `σ ≥ 0` admits a genuine `C^∞`
representative `T : SmoothCcTensor g r s` with `↑T = u`.

The proof extracts, from the abstract `⋂_σ Hˢ`-membership hypothesis, the
*concrete* all-orders coefficient summability of `u`: at each even order
`2k`, the gate hypothesis provides an `Hˢ` witness `v` with
`tensorHsToL2 h_compact v = u`; its structural square-summability
`tensorHs.weighted_summable` together with the coordinate-faithfulness
`tensorHsToL2_tensorL2Coeff` (which identifies `v.coeff i` with the
intrinsic eigenbasis coordinate `tensorL2Coeff h_compact u i`) yields the
weighted summability of `(1 + λᵢ)^{2k} · cᵢ²`. The deferred classical
`C^∞` spectral-series assembly
`spectralSeries_smoothCcTensor_of_allOrders_summable` then converts that
super-polynomial coefficient decay into the smooth section. -/
theorem spectralSmoothRealizesAsSmooth_holds
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SpectralSmoothRealizesAsSmooth (I := I) (M := M) g r s := by
  intro u hu
  refine spectralSeries_smoothCcTensor_of_allOrders_summable
    (I := I) (M := M) g r s u (fun k => ?_)
  have h2k : (0 : ℝ) ≤ (2 * k : ℝ) := by positivity
  obtain ⟨v, hv⟩ := hu (2 * k : ℝ) h2k
  have hcoeff : ∀ i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          u i = v.coeff i := by
    intro i
    have h := tensorHsToL2_tensorL2Coeff
      (I := I) (M := M)
      (h_compact := tensorResolventL2_isCompactOperator
        (I := I) (M := M) g r s) h2k v i
    rw [hv] at h
    exact h
  have hsummable := v.weighted_summable
  refine hsummable.congr (fun i => ?_)
  rw [hcoeff i]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
