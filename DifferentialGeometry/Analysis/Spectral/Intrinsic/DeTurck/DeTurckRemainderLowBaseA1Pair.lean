import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseH2Pair

/-!
# The pairwise Lipschitz estimate for the first-order low-base action

`DeTurckRemainderLowBaseC2Lip` carries the second-order pair `c2_pair_lip` /
`a2_pair_lip`: on a common spectral `H²` ball the complete canonical
second-order coefficient, and both adjacent-scale completions of its action,
are Lipschitz in the state with modulus `C · ‖T - U‖_{H²}` and **no** dependence
on the higher jets of the states.

This module is the first-order sibling.  Both halves of the two-jet coefficient
difference already exist:

* `c0Diff_h2_tame` (`DeTurckRemainderLowBaseH2Pair`) bounds the `H²` jet of the
  zero-order coefficient difference;
* `c1Diff_tame` (`DeTurckRemainderLowBaseLip`) bounds the `H²` jet of the
  order-one coefficient difference.

`c1_pair_lip` glues them along `lowC0_sub` / `lowC1_sub` into the single
two-jet input that `a1_diff` consumes, and `a1_pair_lip` pushes that through
`a1_diff` to the two completed actions `a1Hi` (`H³ → H²`) and `a1Lo`
(`H² → H¹`).

## The modulus is genuinely not uniform in the state

Unlike the second-order coefficient, which is algebraic in the state, the
first-order coefficient is `∇`-linear in the state with metric-inverse
coefficients.  Its difference therefore carries the cross term
`(P(g_T⁻¹) - P(g_U⁻¹)) ∗ ∇T`, whose `H²` jet costs `‖T - U‖ · ‖T‖_{H³}`; this
is the `B1 · A · D2` slot of `c1Diff_tame` and it is sharp, not lossy.  The
modulus recorded here is accordingly

  `K R · (1 + A + A₄) · (D₄ + D₃ + D₂ + N)`

with `A`, `A₄` the third and fourth jet sizes of the states and
`D₂, D₃, D₄, N` the second/third/fourth-jet and spectral differences.  **No
estimate of the shape `C · ‖T - U‖_{H³}` with `C` independent of the states can
hold** — see the same-name `.md`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

/-! ### Scalar bookkeeping

The two producers deliver their moduli in different shapes.  These two purely
real lemmas merge them into the single admissible envelope
`K · (1 + A + A₄) · (D₄ + D₃ + D₂ + N)`. -/

private theorem a1PairArith
    (c0 c1 e0 e1 a a4 d2 d3 d4 n nrm : ℝ)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (he0 : 0 ≤ e0) (he1 : 0 ≤ e1)
    (ha : 0 ≤ a) (ha4 : 0 ≤ a4) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3)
    (hd4 : 0 ≤ d4) (hn : 0 ≤ n) (hnrm : 0 ≤ nrm) (hle : nrm ≤ n) :
    c0 * (1 + a) * (d4 + d3 + d2 + n) + c1 * a4 * (d3 + n) +
        (e0 * d3 + e1 * nrm + e1 * a * nrm) ≤
      (c0 + c1 + e0 + 2 * e1) * (1 + a + a4) * (d4 + d3 + d2 + n) := by
  have hS : (0 : ℝ) ≤ d4 + d3 + d2 + n := by linarith
  have hP0 : (0 : ℝ) ≤ 1 + a + a4 := by linarith
  have haS : (0 : ℝ) ≤ a * (d4 + d3 + d2 + n) := mul_nonneg ha hS
  have ha4S : (0 : ℝ) ≤ a4 * (d4 + d3 + d2 + n) := mul_nonneg ha4 hS
  have t1 : c0 * (1 + a) * (d4 + d3 + d2 + n) ≤
      c0 * (1 + a + a4) * (d4 + d3 + d2 + n) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) hc0) hS
  have t2 : c1 * a4 * (d3 + n) ≤
      c1 * (1 + a + a4) * (d4 + d3 + d2 + n) :=
    mul_le_mul
      (mul_le_mul_of_nonneg_left (by linarith) hc1)
      (by linarith) (by linarith) (mul_nonneg hc1 hP0)
  have t3 : e0 * d3 ≤ e0 * (1 + a + a4) * (d4 + d3 + d2 + n) := by
    have h : d3 ≤ (1 + a + a4) * (d4 + d3 + d2 + n) := by nlinarith
    calc
      e0 * d3 ≤ e0 * ((1 + a + a4) * (d4 + d3 + d2 + n)) :=
        mul_le_mul_of_nonneg_left h he0
      _ = e0 * (1 + a + a4) * (d4 + d3 + d2 + n) := by ring
  have t4 : e1 * nrm ≤ e1 * (1 + a + a4) * (d4 + d3 + d2 + n) := by
    have h : nrm ≤ (1 + a + a4) * (d4 + d3 + d2 + n) := by nlinarith
    calc
      e1 * nrm ≤ e1 * ((1 + a + a4) * (d4 + d3 + d2 + n)) :=
        mul_le_mul_of_nonneg_left h he1
      _ = e1 * (1 + a + a4) * (d4 + d3 + d2 + n) := by ring
  have t5 : e1 * a * nrm ≤ e1 * (1 + a + a4) * (d4 + d3 + d2 + n) := by
    have h : a * nrm ≤ (1 + a + a4) * (d4 + d3 + d2 + n) :=
      mul_le_mul (by linarith) (by linarith) hnrm hP0
    calc
      e1 * a * nrm = e1 * (a * nrm) := by ring
      _ ≤ e1 * ((1 + a + a4) * (d4 + d3 + d2 + n)) :=
        mul_le_mul_of_nonneg_left h he1
      _ = e1 * (1 + a + a4) * (d4 + d3 + d2 + n) := by ring
  nlinarith [t1, t2, t3, t4, t5]

private theorem sqSumLe (x y z j0 j1 : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxyz : x + y ≤ z)
    (h0 : j0 ≤ x ^ 2) (h1 : j1 ≤ y ^ 2) :
    j0 + j1 ≤ z ^ 2 := by
  have hxy : (0 : ℝ) ≤ x + y := by linarith
  have hsq : (x + y) ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ hxy hxyz 2
  nlinarith [mul_nonneg hx hy]

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- **The two-jet `H²` bound for the pairwise first-order low-base
coefficient.**  On a common spectral `H²` ball the sum of the `H²` jets of the
zero- and order-one coefficient differences obeys the admissible envelope
`(K R · (1 + A + A₄) · (D₄ + D₃ + D₂ + N))²`.  This is the exact input shape of
`a1_diff`, and the first-order sibling of `c2_pair_lip`. -/
theorem c1_pair_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ K : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ K R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      let AT := lowBaseData (I := I) (M := M) g g T
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδT hδZ
      let AU := lowBaseData (I := I) (M := M) g g U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδU hδZ
      lowJetSq (I := I) (M := M) g 2 (AT.C0 - AU.C0) +
          lowJetSq (I := I) (M := M) g 2 (AT.C1 - AU.C1) ≤
        (K R * (1 + A + A4) * (D4 + D3 + D2 + N)) ^ 2 := by
  obtain ⟨ρ0, C0f, C1f, hρ0, hC0f, hC1f, hc0⟩ :=
    c0Diff_h2_tame (I := I) (M := M) hDim g
  obtain ⟨ρ1, E0, E1, hρ1, hE0, hE1, hc1⟩ :=
    c1Diff_tame (I := I) (M := M) hDim g
  refine ⟨min ρ0 ρ1, fun R => C0f R + C1f R + E0 + 2 * E1,
    lt_min hρ0 hρ1, ?_, ?_⟩
  · intro R hR
    have h0 := hC0f R hR
    have h1 := hC1f R hR
    linarith
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ R A A4 D2 D3 D4 N
    hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4
    hTU2 hTU3 hTU4 hTn hUn hTUn
  dsimp only
  have hM0 := hc0 T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    (hTn.trans (min_le_left _ _)) (hUn.trans (min_le_left _ _)) hTUn
  have hM1 := hc1 T U hT hU hδ_le hδ0 hδT hδU hδZ
    (hTn.trans (min_le_right _ _)) (hUn.trans (min_le_right _ _))
    A D3 hA hD3 hT3 hTU3
  have hC0eq := lowC0_sub (I := I) (M := M) g T U
    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδT hδU hδZ
  have hC1eq := lowC1_sub (I := I) (M := M) g T U
    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδT hδU hδZ
  have hNrm : (0 : ℝ) ≤
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ :=
    norm_nonneg _
  have hX0 : (0 : ℝ) ≤
      C0f R * (1 + A) * (D4 + D3 + D2 + N) + C1f R * A4 * (D3 + N) :=
    add_nonneg
      (mul_nonneg (mul_nonneg (hC0f R hR) (by linarith)) (by linarith))
      (mul_nonneg (mul_nonneg (hC1f R hR) hA4) (by linarith))
  have hY0 : (0 : ℝ) ≤ E0 * D3 + E1 * N + E1 * A * N :=
    add_nonneg
      (add_nonneg (mul_nonneg hE0 hD3) (mul_nonneg hE1 hN))
      (mul_nonneg (mul_nonneg hE1 hA) hN)
  have hYraw : (0 : ℝ) ≤
      E0 * D3 + E1 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ +
        E1 * A * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ :=
    add_nonneg
      (add_nonneg (mul_nonneg hE0 hD3) (mul_nonneg hE1 hNrm))
      (mul_nonneg (mul_nonneg hE1 hA) hNrm)
  have hYle :
      E0 * D3 + E1 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ +
          E1 * A * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤
        E0 * D3 + E1 * N + E1 * A * N := by
    have h1 := mul_le_mul_of_nonneg_left hTUn hE1
    have h2 := mul_le_mul_of_nonneg_left hTUn (mul_nonneg hE1 hA)
    linarith
  have hM1' : lowJetSq (I := I) (M := M) g 2
      (lowC1Diff (I := I) (M := M) g T U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        hδT hδU hδZ) ≤ (E0 * D3 + E1 * N + E1 * A * N) ^ 2 :=
    hM1.trans (pow_le_pow_left₀ hYraw hYle 2)
  have hXY :
      (C0f R * (1 + A) * (D4 + D3 + D2 + N) + C1f R * A4 * (D3 + N)) +
          (E0 * D3 + E1 * N + E1 * A * N) ≤
        (C0f R + C1f R + E0 + 2 * E1) * (1 + A + A4) *
          (D4 + D3 + D2 + N) :=
    a1PairArith (C0f R) (C1f R) E0 E1 A A4 D2 D3 D4 N N
      (hC0f R hR) (hC1f R hR) hE0 hE1 hA hA4 hD2 hD3 hD4 hN hN le_rfl
  refine sqSumLe
    (C0f R * (1 + A) * (D4 + D3 + D2 + N) + C1f R * A4 * (D3 + N))
    (E0 * D3 + E1 * N + E1 * A * N)
    ((C0f R + C1f R + E0 + 2 * E1) * (1 + A + A4) * (D4 + D3 + D2 + N))
    _ _ hX0 hY0 hXY ?_ ?_
  · rw [hC0eq]
    exact hM0
  · rw [hC1eq]
    exact hM1'

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- **The pairwise Lipschitz bound for both completed first-order actions.**
On a common spectral `H²` ball, the operator-norm differences of the two
adjacent-scale completions `a1Hi : H³ → H²` and `a1Lo : H² → H¹` of the
canonical first-order low-base action obey the admissible envelope
`K R · (1 + A + A₄) · (D₄ + D₃ + D₂ + N)`.  This is the first-order sibling of
`a2_pair_lip`; the extra `(1 + A + A₄)` factor is unavoidable. -/
theorem a1_pair_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ K : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ K R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        lowJetSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      let AT := lowBaseData (I := I) (M := M) g g T
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδT hδZ
      let AU := lowBaseData (I := I) (M := M) g g U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδU hδZ
      ‖AT.a1Hi (I := I) (M := M) - AU.a1Hi (I := I) (M := M)‖ ≤
          K R * (1 + A + A4) * (D4 + D3 + D2 + N) ∧
        ‖AT.a1Lo (I := I) (M := M) - AU.a1Lo (I := I) (M := M)‖ ≤
          K R * (1 + A + A4) * (D4 + D3 + D2 + N) := by
  obtain ⟨ρ, K1, hρ, hK1, hjet⟩ := c1_pair_lip (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, hdiff⟩ := a1_diff (I := I) (M := M) hDim g
  refine ⟨ρ, fun R => Ca * K1 R, hρ, fun R hR => mul_nonneg hCa (hK1 R hR), ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ R A A4 D2 D3 D4 N
    hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4
    hTU2 hTU3 hTU4 hTn hUn hTUn
  dsimp only
  have hK : (0 : ℝ) ≤ K1 R * (1 + A + A4) * (D4 + D3 + D2 + N) :=
    mul_nonneg (mul_nonneg (hK1 R hR) (by linarith)) (by linarith)
  have hin := hjet T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4 hTn hUn hTUn
  obtain ⟨hHi, hLo⟩ :=
    hdiff
      (lowBaseData (I := I) (M := M) g g T
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδT hδZ)
      (lowBaseData (I := I) (M := M) g g U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδU hδZ)
      (K1 R * (1 + A + A4) * (D4 + D3 + D2 + N)) hK hin
  exact ⟨hHi.trans_eq (by ring), hLo.trans_eq (by ring)⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
