import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2Pointwise
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.AppCcJetWindowTame
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes

/-!
# Split-envelope member of the `appCc` estimate family

Every existing member of the `appCc` operator-action family
(`appCc_h2_h3_h1`, `appCc_h2_h4_h2`, `appCc_h2_h2_h2`, …) bounds the action of a
mixed coefficient field on `nabla^2 U` by a **single** envelope `A` controlling
both the pointwise fibre norm of the coefficient and its covariant `L2` jet; the
only two-constant member, `appCc_c1_h2_h1`, *adds* the two constants.  Neither
shape can carry a dissipation ladder, because the ladder needs the coefficient's
`k`-free pointwise smallness to multiply the *top* data order while the
coefficient's (merely bounded) jet multiplies a *lower* data order.

This file supplies the missing member: an order-generic estimate in which each
coefficient norm is paired with its own data factor,

`‖appCc Φ (∇²U)‖_{H^{k+1}} ≤ C k * (‖Φ‖_{C⁰} ‖U‖_{H^{k+3}} + ‖Φ‖_{H^{k+1}} Λ)`,

with `Λ` a pointwise fibre bound for `∇²U`.  The main statement is gate-free and
carries no dimension hypothesis; the dimension-three corollary converts `Λ` into
a spectral norm through the sharp `C⁰` window, which costs two Sobolev orders and
therefore lands the literal ladder shape
`C k * (‖Φ‖_{C⁰} ‖U‖_{H^{m+3}} + ‖Φ‖_{H^{m+1}} ‖U‖_{H^{m+2}})` at the rungs
`m ≥ 2` (`m = 0, 1` are the pre-existing fixed-order members).

The proof composes two order-generic facts that already exist in the tree: the
pointwise Leibniz diagonal product grid
`appCc_iteratedCovGrad_diagonalProductGrid_le` and the integrated
Gagliardo–Nirenberg two-arm bound for that grid,
`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le`.  The whole
content of the split is that the two-arm bound is applied with the coefficient in
the `L∞` slot and the data in the `L2`-jet slot on one arm, and the other way
round on the other arm.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The covariant `L2` jet of `nabla^2 U` below order `n` is controlled by the
spectral `H^m` norm of `U` whenever `n + 1 ≤ m`.  Order-generic form of the
two-derivative shift used by every rung of the dissipation ladder. -/
private theorem icg2_jet_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
      ∀ n m : ℕ, n + 1 ≤ m → ∀ U : SmoothCcTensor g 0 s,
        ∑ l ∈ Finset.range n,
            ‖iteratedCovGrad (I := I) g 0 (s + 2) l
              (iteratedCovGrad (I := I) g 0 s 2 U)‖ ≤
          C m * ‖ccTensorToHs (I := I) (M := M) g s (m : ℝ) U‖ := by
  classical
  choose C hC hjet using fun m : ℕ => hsJet_le (I := I) (M := M) g s m
  refine ⟨C, hC, ?_⟩
  intro n m hnm U
  refine le_trans ?_ (hjet m U)
  calc
    ∑ l ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g 0 (s + 2) l
          (iteratedCovGrad (I := I) g 0 s 2 U)‖
        = ∑ l ∈ Finset.range n,
            ‖iteratedCovGrad (I := I) g 0 s (2 + l) U‖ :=
      Finset.sum_congr rfl
        (fun l _ => icg_comp_norm (I := I) (M := M) g s 2 l U)
    _ ≤ ∑ i ∈ Finset.range (2 + n),
            ‖iteratedCovGrad (I := I) g 0 s i U‖ := by
      rw [Finset.sum_range_add
        (fun i => ‖iteratedCovGrad (I := I) g 0 s i U‖) 2 n]
      exact le_add_of_nonneg_left
        (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    _ ≤ ∑ i ∈ Finset.range (m + 1),
            ‖iteratedCovGrad (I := I) g 0 s i U‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (by omega))
        (fun _ _ _ => norm_nonneg _)

/-- **Split-envelope member of the `appCc` family, order-generic.**

For every `k`, a mixed coefficient `Φ` acting on `nabla^2 U` satisfies

`‖appCc Φ (∇²U)‖_{H^{k+1}} ≤ C k * (A * ‖U‖_{H^{k+3}} + B * Λ)`,

where `A` bounds the *pointwise* fibre norm of `Φ`, `B` bounds the covariant
`L2` jet of `Φ` through order `k + 1`, and `Λ` bounds the pointwise fibre norm of
`nabla^2 U`.  The point is the pairing: the pointwise coefficient bound `A`
multiplies the **top** data order `H^{k+3}`, while the coefficient jet `B`
multiplies only the data factor `Λ`.  No dimension hypothesis and no gate.

`C k` grows with `k` (it contains the `k`-th Leibniz grid weight
`appCcGdiag`, which is exponential in `k`); the statement asserts no `k`-uniform
constant. -/
theorem appCc_split_env
    (g : SmoothRiemannianMetric I M) (s c : ℕ) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ (k : ℕ) (Φ : SmoothCcTensor g (s + 2) c) (U : SmoothCcTensor g 0 s)
        (A B Λ : ℝ), 0 ≤ A → 0 ≤ B → 0 ≤ Λ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (s + 2) c x
              (Φ.toSection x) ≤ A ^ 2) →
        (∑ i ∈ Finset.range (k + 2),
          ‖iteratedCovGrad (I := I) g (s + 2) c i Φ‖ ^ 2) ≤ B ^ 2 →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 2) x
              ((iteratedCovGrad (I := I) g 0 s 2 U).toSection x) ≤ Λ ^ 2) →
        ‖ccTensorToHs (I := I) (M := M) g c ((k + 1 : ℕ) : ℝ)
            (appCc (I := I) (M := M) g (s + 2) c Φ
              (iteratedCovGrad (I := I) g 0 s 2 U))‖ ≤
          C k * (A * ‖ccTensorToHs (I := I) (M := M) g s ((k + 3 : ℕ) : ℝ) U‖ +
            B * Λ) := by
  classical
  choose Csp hCsp hsp using fun k : ℕ => hs_le_jet (I := I) (M := M) g c (k + 1)
  obtain ⟨Cin, hCin, hin⟩ := icg2_jet_le (I := I) (M := M) g s
  choose Cg hCg hgrid using fun j : ℕ =>
    exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g (s + 2) 0 c (s + 2) j
  refine ⟨fun k => Csp k *
    (∑ j ∈ Finset.range (k + 2),
      Real.sqrt (appCcGdiag (E := E) j * Cg j)) * (Cin (k + 3) + 1), ?_, ?_⟩
  · intro k
    refine mul_nonneg (mul_nonneg (hCsp k)
      (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))) ?_
    linarith only [hCin (k + 3)]
  intro k Φ U A B Λ hA hB hΛ hΦsup hΦjet hWsup
  have hNnn : (0 : ℝ) ≤
      ‖ccTensorToHs (I := I) (M := M) g s ((k + 3 : ℕ) : ℝ) U‖ := norm_nonneg _
  -- the data jet, two derivatives above `U`, sits in the top spectral order
  have hWjet :
      ∑ l ∈ Finset.range (k + 2),
          ‖iteratedCovGrad (I := I) g 0 (s + 2) l
            (iteratedCovGrad (I := I) g 0 s 2 U)‖ ^ 2 ≤
        (Cin (k + 3) *
          ‖ccTensorToHs (I := I) (M := M) g s ((k + 3 : ℕ) : ℝ) U‖) ^ 2 := by
    refine (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)).trans ?_
    exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      (hin (k + 2) (k + 3) (by omega) U) 2
  set W : SmoothCcTensor g 0 (s + 2) :=
    iteratedCovGrad (I := I) g 0 s 2 U with hW_def
  set N : ℝ := ‖ccTensorToHs (I := I) (M := M) g s ((k + 3 : ℕ) : ℝ) U‖
    with hN_def
  have hXnn : (0 : ℝ) ≤ A * (Cin (k + 3) * N) + B * Λ :=
    add_nonneg (mul_nonneg hA (mul_nonneg (hCin (k + 3)) hNnn))
      (mul_nonneg hB hΛ)
  -- every covariant jet of the action, one order at a time
  have hterm : ∀ j ∈ Finset.range (k + 2),
      ‖iteratedCovGrad (I := I) g 0 c j
          (appCc (I := I) (M := M) g (s + 2) c Φ W)‖ ≤
        Real.sqrt (appCcGdiag (E := E) j * Cg j) *
          (A * (Cin (k + 3) * N) + B * Λ) := by
    intro j hj
    have hjk : j + 1 ≤ k + 2 := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    obtain ⟨hint, hbnd⟩ := hgrid j Φ W A Λ hA hΛ hΦsup hWsup
    have hΦj :
        ∑ i ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g (s + 2) c i Φ‖ ^ 2 ≤ B ^ 2 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr hjk) (fun _ _ _ => sq_nonneg _)) hΦjet
    have hWj :
        ∑ l ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g 0 (s + 2) l W‖ ^ 2 ≤
          (Cin (k + 3) * N) ^ 2 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr hjk) (fun _ _ _ => sq_nonneg _)) hWjet
    have hinner :
        Cg j * (Λ ^ 2 * ∑ i ∈ Finset.range (j + 1),
              ‖iteratedCovGrad (I := I) g (s + 2) c i Φ‖ ^ 2 +
            A ^ 2 * ∑ l ∈ Finset.range (j + 1),
              ‖iteratedCovGrad (I := I) g 0 (s + 2) l W‖ ^ 2) ≤
          Cg j * (A * (Cin (k + 3) * N) + B * Λ) ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ (hCg j)
      have h1 := mul_le_mul_of_nonneg_left hΦj (sq_nonneg Λ)
      have h2 := mul_le_mul_of_nonneg_left hWj (sq_nonneg A)
      have hab : (0 : ℝ) ≤ (A * (Cin (k + 3) * N)) * (B * Λ) :=
        mul_nonneg (mul_nonneg hA (mul_nonneg (hCin (k + 3)) hNnn))
          (mul_nonneg hB hΛ)
      nlinarith [h1, h2, hab]
    have hquad :
        ‖iteratedCovGrad (I := I) g 0 c j
            (appCc (I := I) (M := M) g (s + 2) c Φ W)‖ ^ 2 ≤
          (appCcGdiag (E := E) j * Cg j) *
            (A * (Cin (k + 3) * N) + B * Λ) ^ 2 := by
      refine le_trans ?_ (le_of_eq (by ring :
        appCcGdiag (E := E) j * (Cg j * (A * (Cin (k + 3) * N) + B * Λ) ^ 2) =
          (appCcGdiag (E := E) j * Cg j) *
            (A * (Cin (k + 3) * N) + B * Λ) ^ 2))
      refine le_trans ?_ (mul_le_mul_of_nonneg_left (hbnd.trans hinner)
        (appCcGdiag_nonneg (E := E) j))
      rw [← MeasureTheory.integral_const_mul]
      exact normSq_le_integral_of_pointwise_fiberNormSq_le_rs
        (I := I) (M := M) g 0 (c + j) _ _ (hint.const_mul _)
        (fun x => appCc_iteratedCovGrad_diagonalProductGrid_le
          (I := I) (M := M) g (s + 2) c Φ W j x)
    refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) hXnn)
    rw [mul_pow, Real.sq_sqrt
      (mul_nonneg (appCcGdiag_nonneg (E := E) j) (hCg j))]
    exact hquad
  have hsum :
      ∑ j ∈ Finset.range (k + 2),
          ‖iteratedCovGrad (I := I) g 0 c j
            (appCc (I := I) (M := M) g (s + 2) c Φ W)‖ ≤
        (∑ j ∈ Finset.range (k + 2),
          Real.sqrt (appCcGdiag (E := E) j * Cg j)) *
          (A * (Cin (k + 3) * N) + B * Λ) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hterm
  have hspY :
      ‖ccTensorToHs (I := I) (M := M) g c ((k + 1 : ℕ) : ℝ)
          (appCc (I := I) (M := M) g (s + 2) c Φ W)‖ ≤
        Csp k * ∑ j ∈ Finset.range (k + 2),
          ‖iteratedCovGrad (I := I) g 0 c j
            (appCc (I := I) (M := M) g (s + 2) c Φ W)‖ := by
    have h := hsp k (appCc (I := I) (M := M) g (s + 2) c Φ W)
    rw [show k + 1 + 1 = k + 2 from by omega] at h
    exact h
  have hSnn : (0 : ℝ) ≤
      ∑ j ∈ Finset.range (k + 2),
        Real.sqrt (appCcGdiag (E := E) j * Cg j) :=
    Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hfin :
      (∑ j ∈ Finset.range (k + 2),
          Real.sqrt (appCcGdiag (E := E) j * Cg j)) *
        (A * (Cin (k + 3) * N) + B * Λ) ≤
      (∑ j ∈ Finset.range (k + 2),
          Real.sqrt (appCcGdiag (E := E) j * Cg j)) *
        ((Cin (k + 3) + 1) * (A * N + B * Λ)) := by
    refine mul_le_mul_of_nonneg_left ?_ hSnn
    nlinarith [mul_nonneg hA hNnn,
      mul_nonneg (hCin (k + 3)) (mul_nonneg hB hΛ)]
  calc
    ‖ccTensorToHs (I := I) (M := M) g c ((k + 1 : ℕ) : ℝ)
        (appCc (I := I) (M := M) g (s + 2) c Φ W)‖
        ≤ Csp k * ∑ j ∈ Finset.range (k + 2),
            ‖iteratedCovGrad (I := I) g 0 c j
              (appCc (I := I) (M := M) g (s + 2) c Φ W)‖ := hspY
    _ ≤ Csp k * ((∑ j ∈ Finset.range (k + 2),
          Real.sqrt (appCcGdiag (E := E) j * Cg j)) *
        (A * (Cin (k + 3) * N) + B * Λ)) :=
      mul_le_mul_of_nonneg_left hsum (hCsp k)
    _ ≤ Csp k * ((∑ j ∈ Finset.range (k + 2),
          Real.sqrt (appCcGdiag (E := E) j * Cg j)) *
        ((Cin (k + 3) + 1) * (A * N + B * Λ))) :=
      mul_le_mul_of_nonneg_left hfin (hCsp k)
    _ = Csp k * (∑ j ∈ Finset.range (k + 2),
          Real.sqrt (appCcGdiag (E := E) j * Cg j)) * (Cin (k + 3) + 1) *
        (A * N + B * Λ) := by ring

/-- **Dimension-three spectral split envelope, at the dissipation rungs `≥ 2`.**

Converting the pointwise factor `Λ` of `appCc_split_env` into a spectral norm
costs two Sobolev orders (the sharp `C⁰` window is `H²` in dimension three), so
the literal ladder shape

`‖appCc Φ (∇²U)‖_{H^{m+1}} ≤ C * (A ‖U‖_{H^{m+3}} + B ‖U‖_{H^{m+2}})`

is obtained here at the rungs `m = k + 2`.  `A` bounds the pointwise fibre norm
of `Φ`, `B` its covariant `L2` jet through order `m + 1 = k + 3`.  The rungs
`m = 0, 1` are the pre-existing fixed-order members `appCc_h2_h3_h1` and
`appCc_h2_h4_h2`. -/
theorem appCc_split_hs
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (s c : ℕ) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ (k : ℕ) (Φ : SmoothCcTensor g (s + 2) c) (U : SmoothCcTensor g 0 s)
        (A B : ℝ), 0 ≤ A → 0 ≤ B →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (s + 2) c x
              (Φ.toSection x) ≤ A ^ 2) →
        (∑ i ∈ Finset.range (k + 4),
          ‖iteratedCovGrad (I := I) g (s + 2) c i Φ‖ ^ 2) ≤ B ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g c ((k + 3 : ℕ) : ℝ)
            (appCc (I := I) (M := M) g (s + 2) c Φ
              (iteratedCovGrad (I := I) g 0 s 2 U))‖ ≤
          C k * (A * ‖ccTensorToHs (I := I) (M := M) g s ((k + 5 : ℕ) : ℝ) U‖ +
            B * ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖) := by
  classical
  obtain ⟨C0, hC0, hsplit⟩ := appCc_split_env (I := I) (M := M) g s c
  obtain ⟨Cpt, hCpt, hpt⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g 0 (s + 2)
  obtain ⟨Cj, hCj, hjet⟩ := icg2_jet_le (I := I) (M := M) g s
  refine ⟨fun k => C0 (k + 2) * (Cpt * Cj (k + 4) + 1), ?_, ?_⟩
  · intro k
    exact mul_nonneg (hC0 (k + 2))
      (by linarith only [mul_nonneg hCpt (hCj (k + 4))])
  intro k Φ U A B hA hB hΦsup hΦjet
  have hN4 : (0 : ℝ) ≤
      ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖ := norm_nonneg _
  have hN5 : (0 : ℝ) ≤
      ‖ccTensorToHs (I := I) (M := M) g s ((k + 5 : ℕ) : ℝ) U‖ := norm_nonneg _
  have hΛnn : (0 : ℝ) ≤
      Cpt * Cj (k + 4) *
        ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖ :=
    mul_nonneg (mul_nonneg hCpt (hCj (k + 4))) hN4
  -- the sharp `C⁰` window on `∇²U`, paid for by two extra Sobolev orders
  have hWsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 2) x
          ((iteratedCovGrad (I := I) g 0 s 2 U).toSection x) ≤
        (Cpt * Cj (k + 4) *
          ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖) ^ 2 := by
    intro x
    have h := hpt (iteratedCovGrad (I := I) g 0 s 2 U) x
    rw [show Module.finrank ℝ E / 2 + 2 = 3 by rw [hDim]] at h
    refine h.trans ?_
    have hsq :
        ∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 (s + 2) i
              (iteratedCovGrad (I := I) g 0 s 2 U)‖ ^ 2 ≤
          (Cj (k + 4) *
            ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖) ^ 2 :=
      (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)).trans
        (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
          (hjet 3 (k + 4) (by omega) U) 2)
    calc
      Cpt ^ 2 * ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 (s + 2) i
            (iteratedCovGrad (I := I) g 0 s 2 U)‖ ^ 2
          ≤ Cpt ^ 2 * (Cj (k + 4) *
              ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg Cpt)
      _ = (Cpt * Cj (k + 4) *
            ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖) ^ 2 := by
        ring
  have hΦjet' :
      ∑ i ∈ Finset.range (k + 2 + 2),
        ‖iteratedCovGrad (I := I) g (s + 2) c i Φ‖ ^ 2 ≤ B ^ 2 := by
    rw [show k + 2 + 2 = k + 4 from by omega]
    exact hΦjet
  have hmain := hsplit (k + 2) Φ U A B
    (Cpt * Cj (k + 4) *
      ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖)
    hA hB hΛnn hΦsup hΦjet' hWsup
  rw [show k + 2 + 1 = k + 3 from by omega,
    show k + 2 + 3 = k + 5 from by omega] at hmain
  refine hmain.trans ?_
  have hstep :
      A * ‖ccTensorToHs (I := I) (M := M) g s ((k + 5 : ℕ) : ℝ) U‖ +
          B * (Cpt * Cj (k + 4) *
            ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖) ≤
        (Cpt * Cj (k + 4) + 1) *
          (A * ‖ccTensorToHs (I := I) (M := M) g s ((k + 5 : ℕ) : ℝ) U‖ +
            B * ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖) := by
    nlinarith [mul_nonneg (mul_nonneg hCpt (hCj (k + 4)))
        (mul_nonneg hA hN5), mul_nonneg hB hN4]
  calc
    C0 (k + 2) *
        (A * ‖ccTensorToHs (I := I) (M := M) g s ((k + 5 : ℕ) : ℝ) U‖ +
          B * (Cpt * Cj (k + 4) *
            ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖))
        ≤ C0 (k + 2) * ((Cpt * Cj (k + 4) + 1) *
            (A * ‖ccTensorToHs (I := I) (M := M) g s ((k + 5 : ℕ) : ℝ) U‖ +
              B * ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖)) :=
      mul_le_mul_of_nonneg_left hstep (hC0 (k + 2))
    _ = C0 (k + 2) * (Cpt * Cj (k + 4) + 1) *
        (A * ‖ccTensorToHs (I := I) (M := M) g s ((k + 5 : ℕ) : ℝ) U‖ +
          B * ‖ccTensorToHs (I := I) (M := M) g s ((k + 4 : ℕ) : ℝ) U‖) := by
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
