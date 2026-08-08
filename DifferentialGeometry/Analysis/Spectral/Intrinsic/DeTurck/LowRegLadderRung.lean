import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegC2JetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegC01JetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNorm

/-!
# The `k`-uniform ladder for the low-base second-order arm

`LowRegDissipRung.lean` records the `k = 0` rung of the zero-based
Ricci--DeTurck dissipation ladder.  This module records the *whole* ladder for
its top-order arm `LowBaseActionData.a2`, i.e. the family of estimates

`‖a₂ T‖_{H^m} ≤ Cδ₀ ‖T‖_{H^{m+2}} + Clower m ‖T‖_{H^{m+1}}`,   `m : ℕ`,

whose top constant `Cδ₀` does **not** depend on the rung `m`.

The mechanism is the one identified in `ShortTime/L4_UNIFORMITY_AUTOPSY.md`:
the top-order constant is a *pointwise* fibre cap on the coefficient, held
outside the induction on the Sobolev order, while raising the order costs only
a commutator against the resolvent and therefore only feeds the lower-order
constant.  Concretely the two inputs are

* `lowData_split`, whose second clause caps the complete second-order
  coefficient `A.C2` pointwise by `K · δ/(1-δ)²` — a quantity free of the
  Sobolev order, of the state `T`, and of the rung;
* the order-generic, coefficient-abstract operator-norm engine
  `exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le`, which converts
  that pointwise cap into the top constant at *every* rung.

The single missing input is the coefficient's all-order jet tower, stated here
as the named frontier `c2_jet_tower`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The `m`-form of the order-generic, coefficient-abstract operator-norm
engine, at the engine's **own** derivative budget
`max 2 (finrank ℝ E / 2 * 2 + 1) ≤ a` (in dimension three: `3 ≤ a`):

`‖appCc C₂ (∇²T₀)‖_{H^m} ≤ εC ‖T₀‖_{H^{m+2}} + Cop m ‖T₀‖_{H^{m+1}}`,

where `εC` is a pointwise fibre cap on the coefficient `C₂`.  The top constant
is `εC` itself and carries no `m`.

This is a de-gated companion of
`exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le`, whose signature
demands the strictly stronger budget `2 * finrank ℝ E + 10 ≤ a`.  That excess
is an artefact: of the two halves it composes, the `m = 0` half never uses the
budget at all and the `m = k+1` half forwards it to
`exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le` through `by omega`,
which needs only `max 2 (finrank ℝ E / 2 * 2 + 1) ≤ a`.  Reading the engine on the constant
resolvent family (`p = 0`, where `oneMinusConnLapSmoothIter … 0 T₀ = T₀`) and
closing with the constant-one spectral shift
`smoothCcToTensorHs_rawTensorConnLapSmooth_le` therefore halves the required
order of the a-priori ball, and also drops the fibre factor
`deTurckArmFibreConst` from the top constant. -/
theorem appCc_cap_hs_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : max 2 (Module.finrank ℝ E / 2 * 2 + 1) ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (εC : ℝ) (hεC_nn : 0 ≤ εC) (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
            (C₂.toSection x) ≤ εC ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
                (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ ≤
            εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Clower, hCl_nn, hfam⟩ :=
    exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le
      (I := I) (M := M) g₀ a ha hR₀ εC hεC_nn Kc hKc_nn
  refine ⟨Clower, hCl_nn, ?_⟩
  intro C₂ T₀ hball hsup hjets m
  have h := hfam C₂ T₀ hball hsup hjets m T₀ ⟨0, rfl⟩
  have hshift : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ) T₀‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
      (by push_cast; ring) T₀
  rw [hshift] at h
  have hmul : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
      εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ :=
    mul_le_mul_of_nonneg_left
      (smoothCcToTensorHs_rawTensorConnLapSmooth_le
        (I := I) (M := M) g₀ (m : ℝ) T₀) hεC_nn
  exact le_trans h (by linarith only [hmul])

/-- Monotonicity of the spectral `H^σ` norm in the order `σ`.

Local copy of the private `smoothCcToTensorHs_norm_mono`
(`DeTurckPrincipalArmEnergyCrossTerm.lean`), needed here to descend from the
`H⁵` radius of `a2LadderQ` to the `H⁴` radius of `a1LadderQ`. -/
private lemma hsMono (g₀ : SmoothRiemannianMetric I M)
    {σ τ : ℝ} (hστ : σ ≤ τ) (w : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ w‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ τ w‖ := by
  have hbσ : smoothCcToTensorHs (I := I) (M := M) g₀ σ w =
      ccSpectralEmbed (I := I) (M := M) g₀ σ w :=
    Analysis.Parabolic.TensorHeatEquation.tensorHs.ext (funext fun i => rfl)
  have hbτ : smoothCcToTensorHs (I := I) (M := M) g₀ τ w =
      ccSpectralEmbed (I := I) (M := M) g₀ τ w :=
    Analysis.Parabolic.TensorHeatEquation.tensorHs.ext (funext fun i => rfl)
  rw [hbσ, hbτ]
  exact ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ hστ w

/-- **The all-order `L²` jet tower of `A.C2`, sharp window, no a-priori ball.**

`‖∇ⁱ (lowBaseData g g_bg T …).C2‖² ≤ Kc i * (1 + ∑_{j < i+1} ‖∇ʲ T‖²)`,
with `Kc` chosen before the state — background metrics and order only.

The window is the **sharp** one: order `i` of the coefficient costs order `i`
of the state, not `i + 1`.  This is what the tower-direct rung-`k` pairing
consumes: the worst Leibniz term at rung `k` calls the tower at index `k + 1`,
so a window `j ≤ k + 2` would put the coefficient's `L^∞` cost above `E_{k+1}`
and make the bottom block circular, while `j ≤ k + 1` lands exactly on the
pairing factor (PSTOP §6.4 adapter G / (B-WIN)).

`c2JetTowerQ` below is the `range (i + 2)` compatibility form, and
`c2_jet_tower` its ball-carrying wrapper.  Like `c1JetTowerQ` and unlike
`c0_jet_tower_quad`, no quadratic correction term is needed: the `H^{a+2}`
ball binder of `c2_jet_tower` was **vestigial**, since the whole proof runs
through `topKerJetSharp`, which takes only `hDim` and the background metrics,
and the estimate is driven by `hδ_le : δ ≤ 1/3` alone (which bounds `T` in
`L^∞`). -/
theorem c2JetTowerSharp
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ),
          ‖iteratedCovGrad (I := I) g 4 2 i
              (lowBaseData (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).C2‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨Kk, hKk_nn, hker⟩ := topKerJetSharp (I := I) (M := M) hDim g g_bg
  refine ⟨Kk, hKk_nn, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hΛ : 0 ≤ Kk i * (1 + ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) :=
    mul_nonneg (hKk_nn i) (by linarith only [hsum])
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  -- the coefficient is a single cancellation-preserving path integral; bind the
  -- witness opaquely and pass the order-`i` jet bound through the integral
  obtain ⟨X, hXdef, hXjet⟩ :
      ∃ X : SmoothCcTensor g 4 2,
        (lowBaseData (I := I) (M := M) g g_bg T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).C2 = X ∧
          lowJetSq (I := I) (M := M) g i X ≤
            Kk i * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) :=
    ⟨rhsRefoldTopInt (I := I) (M := M) g g_bg T hδ_lt hδg hδZ +
        LowBaseInternal.selfTopInt (I := I) (M := M) g T hδ_lt hδg hδZ -
        deTurckPhiMetTotal (I := I) (M := M) g g_bg g, rfl,
      path_add_sub_jet (I := I) (M := M) g 4 i hSI
        (rhsRefoldTop (I := I) (M := M) g g_bg T hδg hδZ)
        (LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hδg hδZ)
        (deTurckPhiMetTotal (I := I) (M := M) g g_bg g)
        (rhsRefoldTop_joint (I := I) (M := M) g g_bg T hδ_lt hδg hδZ)
        (LowBaseInternal.selfTop_joint (I := I) (M := M) g T hδg hδZ)
        hΛ (hker T hT hδ0 hδ_le hδg hδZ i)⟩
  rw [hXdef]
  clear hXdef
  refine le_trans ?_ hXjet
  unfold lowJetSq
  exact Finset.single_le_sum
    (fun q _ => sq_nonneg ‖iteratedCovGrad (I := I) g 4 2 q X‖)
    (Finset.mem_range.mpr (Nat.lt_succ_self i))

set_option linter.unusedVariables false in
/-- **The `range (i + 2)` compatibility form of `c2JetTowerSharp`.**

Byte-identical to the statement this file carried before the window
sharpening, so that every consumer written against the wider window
(`a2LadderQ`, `c2_jet_tower`, and the operator-norm engines that take the
tower as a hypothesis) keeps working unchanged.  The mathematical content is
`c2JetTowerSharp`; this is its one-step weakening by
`Finset.sum_le_sum_of_subset_of_nonneg`. -/
theorem c2JetTowerQ
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ),
          ‖iteratedCovGrad (I := I) g 4 2 i
              (lowBaseData (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).C2‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  obtain ⟨Kc, hKc_nn, htower⟩ := c2JetTowerSharp (I := I) (M := M) hDim g g_bg
  refine ⟨Kc, hKc_nn, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i
  refine (htower T hT hδ0 hδ_le hδg hδZ i).trans ?_
  have hsub : Finset.range (i + 1) ⊆ Finset.range (i + 2) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hmono : ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤
      ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (by linarith only [hmono]) (hKc_nn i)

set_option linter.unusedVariables false in
/-- **The all-order `L²` jet tower of the complete zero-based second-order
coefficient `A.C2`.**

The `i`-th covariant jet of the canonical top coefficient is controlled, with a
constant depending only on the background metric and the order `i`, by the
state's own jets through order `i + 1`:

`‖∇ⁱ (lowBaseData g g_bg T …).C2‖² ≤ Kc i * (1 + ∑_{j < i+2} ‖∇ʲ T‖²)`.

This is exactly hypothesis (b) of the order-generic operator-norm engine
`exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le`, and it is the last
input of `a2_ladder`.  The `i = 0` case is the second clause of `c2_h2_small`.

`A.C2` is the path integral `rhsRefoldTopInt + selfTopInt - deTurckPhiMetTotal`
(`DeTurckRemainderLowBaseAction.lean:3359`), so the proof has two layers, both
in `LowRegC2JetTower.lean`: `path_add_sub_jet` passes an order-`i` covariant
jet bound through the parameter integral of the *cancellation-preserving*
integrand with the same constant, and `topKer_jet` bounds that integrand's
order-`i` jet uniformly in the path parameter.  The second is the campaign's
single remaining frontier.

The `H^{a+2}` ball hypothesis is inert: this statement quantifies over an
arbitrary `a`, so at `a = 0` the ball supplies no low-order control, and the
estimate is in fact driven by `hδ_le : δ ≤ 1/3`, which bounds `T` in `L^∞`.
The binder is kept because `a2_ladder` and the operator-norm engine carry it.
The ball-free content is `c2JetTowerQ`, of which this is the compatibility
wrapper. -/
theorem c2_jet_tower
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g 4 2 i
              (lowBaseData (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).C2‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  obtain ⟨Kc, hKc_nn, h⟩ := c2JetTowerQ (I := I) (M := M) hDim g g_bg
  refine ⟨Kc, hKc_nn, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ _ i
  exact h T hT hδ0 hδ_le hδg hδZ i

set_option linter.unusedVariables false in
/-- **The `k`-uniform ladder for the low-base second-order arm, ball-free.**

In dimension three there are a constant `κ` and a *radius-indexed* constant
family `Clower : ℝ → ℕ → ℝ` such that **every** symmetric state `T` whose fibre
deviation is bounded by `δ ≤ 1/3` satisfies, at every rung `m` and for every
`R` with `‖T‖_{H⁵} ≤ R`,

`‖a₂ T‖_{H^m} ≤ κ · δ/(1-δ)² · ‖T‖_{H^{m+2}} + Clower R m · ‖T‖_{H^{m+1}}`.

This is `a2_ladder` with the a-priori-ball *binder* removed: there is no `a`,
no `R₀` fixed before the state, and no hypothesis restricting which states the
estimate applies to — the consumer may take `R := ‖T‖_{H⁵}` and get an
unconditional tame estimate.  `Clower` is still chosen before the state
(TK3), now as a function of the radius; `κ` is still produced before `δ`
(A2-ABS), and is `lowData_split`'s own `δ`-free constant `K`.

The DeTurck background `g_bg` is arbitrary and fixed throughout; all Sobolev
norms and covariant derivatives remain based at the initial metric `g`.

**The `H⁵` radius is structural, not an artefact.**  Unlike the `c1`/`c2`
towers, whose ball binders were vestigial, the `H⁵` order is what the tame
commutator engine
`exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le` genuinely trades
against: its Leibniz region two pairs a coefficient jet of order `i + dc` with
a data jet of order `q - i + (finrank/2 + 1) + dd`, and the log-convexity swap
`f α · f β ≤ f A · f Γ` is available only when `α + β ≤ A + Γ`, i.e. only when
`A ≥ dc + dd + finrank ℝ E / 2 + 1 - 3`.  With the coefficient shifts
`(dc, dd) ∈ {(3,2), (2,3)}` forced by the two commutator derivatives, that is
`A ≥ 4`, realized here as `A = a + 2 = 5`.  So the lower constant cannot be
made to depend on `H²` or `H³` data alone; see `LowRegLadderRung.md`. -/
theorem a2LadderQBg
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, 0 ≤ κ ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3),
      ∃ Clower : ℝ → ℕ → ℝ, (∀ R m, 0 ≤ Clower R m) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}
        (hR : ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖ ≤ R)
        (m : ℕ),
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              ((lowBaseData (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).a2
                  (I := I) (M := M) T)‖ ≤
            κ * (δ / (1 - δ) ^ 2) *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 2) T‖ +
              Clower R m *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ := by
  classical
  obtain ⟨K, hK, hsplit⟩ := lowData_split (I := I) (M := M) g g_bg
  obtain ⟨Kc, hKc_nn, htower⟩ := c2JetTowerQ (I := I) (M := M) hDim g g_bg
  refine ⟨K, hK, ?_⟩
  intro δ hδ0 hδ_le
  have hεC_nn : (0 : ℝ) ≤ K * (δ / (1 - δ) ^ 2) :=
    mul_nonneg hK (div_nonneg hδ0 (sq_nonneg _))
  -- the engine's lower constants, one family per admissible radius
  choose Cop hCop_nn hop using fun R : ℝ =>
    appCc_cap_hs_le (I := I) (M := M) g 3 (by omega) (abs_nonneg R)
      (K * (δ / (1 - δ) ^ 2)) hεC_nn Kc hKc_nn
  refine ⟨Cop, hCop_nn, ?_⟩
  intro T hT hδg hδZ R hR m
  have hball : ‖smoothCcToTensorHs (I := I) (M := M) g (((3 : ℕ) : ℝ) + 2) T‖ ≤ |R| := by
    refine le_trans (le_of_eq ?_) (le_trans hR (le_abs_self R))
    exact smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g
      (by push_cast; norm_num) T
  -- the low-base coefficient bundle, bound opaquely so that no later step
  -- unfolds the path-integral witnesses
  obtain ⟨A, hAdef, hc2pt, hc2jet⟩ :
      ∃ A : LowBaseActionData g,
        lowBaseData (I := I) (M := M) g g_bg T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ = A ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              (A.C2.toSection x) ≤ (K * (δ / (1 - δ) ^ 2)) ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g 4 2 i A.C2‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) :=
    ⟨lowBaseData (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ, rfl,
      (hsplit T hT hδ_le hδ0 hδg hδZ).2,
      htower T hT hδ0 hδ_le hδg hδZ⟩
  rw [hAdef]
  clear hAdef
  have hshape : A.a2 (I := I) (M := M) T =
      appCc (I := I) (M := M) g (2 + 2) 2 A.C2
        (iteratedCovGrad (I := I) g 0 2 2 T) := rfl
  rw [hshape]
  exact le_trans (hop R A.C2 T hball hc2pt hc2jet m) (le_of_eq (by ring))

/-- Diagonal-background compatibility wrapper for `a2LadderQBg`. -/
theorem a2LadderQ
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, 0 ≤ κ ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3),
      ∃ Clower : ℝ → ℕ → ℝ, (∀ R m, 0 ≤ Clower R m) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}
        (hR : ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖ ≤ R)
        (m : ℕ),
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              ((lowBaseData (I := I) (M := M) g g T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).a2
                  (I := I) (M := M) T)‖ ≤
            κ * (δ / (1 - δ) ^ 2) *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 2) T‖ +
              Clower R m *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ :=
  a2LadderQBg (I := I) (M := M) hDim g g

set_option linter.unusedVariables false in
/-- **The `k`-uniform ladder for the low-base second-order arm.**

In dimension three, on the spectral `H^{a+2}` ball of radius `R₀`, there are a
constant `κ` and a rung-dependent constant family `Clower` such that every
symmetric state `T` in the ball whose fibre deviation is bounded by `δ ≤ 1/3`
satisfies, at **every** rung `m`,

`‖a₂ T‖_{H^m} ≤ κ · δ/(1-δ)² · ‖T‖_{H^{m+2}} + Clower m · ‖T‖_{H^{m+1}}`,

where `a₂` is the canonical second-order action of the zero-based low-base
split `lowData_split`.

The top-order constant `κ · δ/(1-δ)²` carries **no `m`**: it is exactly the
pointwise fibre cap of the coefficient supplied by `lowData_split`, so a single
smallness threshold on `δ` makes it a contraction simultaneously at every rung.
All rung-dependent cost is confined to `Clower m`, which multiplies the *lower*
order `H^{m+1}` only.  This is the `k`-uniformity that `F6_ESTIMATE_RECON.md`
§5.3 clause 1 left open and that the Leibniz-grid route of
`AppCcSplitEnvelope.lean` could not supply.

The hypothesis `ha : 3 ≤ a` is the operator-norm engine's derivative budget; it
fixes the order of the a-priori ball only (here `H⁵` at the bottom), and does
not enter the top constant.  It is the dimension-three reading of the engine's
sharp budget `max 2 (finrank ℝ E / 2 * 2 + 1) ≤ a`, which the parameterized
Leibniz split threshold of `master_appCc_jet_le_sharp` makes available.

**Binder order (A2-ABS).**  `κ` is produced *before* `δ` is bound: it is
`lowData_split`'s own `δ`-free constant `K`, so choosing the fibre threshold
`δ*` from `κ` — the absorption condition `κ · δ*/(1-δ*)² < 1` — is not
circular.  The lower constant family `Clower` is bound *after* `δ`, because it
genuinely depends on it: the operator-norm engine
`exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le` returns a lower
constant affine in its fibre cap `εC = κ · δ/(1-δ)²`.  That is harmless for the
absorption, which only constrains the top constant, and matches the intended
order of choices (fix `δ*` from `κ`, then the rung constants). -/
theorem a2_ladder
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 3 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ κ : ℝ, 0 ≤ κ ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3),
      ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x u v =
            ccTensorBilin (I := I) g₀ T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              ((lowBaseData (I := I) (M := M) g₀ g₀ T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).a2
                  (I := I) (M := M) T)‖ ≤
            κ * (δ / (1 - δ) ^ 2) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T‖ +
              Clower m *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T‖ := by
  classical
  obtain ⟨κ, hκ, hQ⟩ := a2LadderQ (I := I) (M := M) hDim g₀
  refine ⟨κ, hκ, ?_⟩
  intro δ hδ0 hδ_le
  obtain ⟨C, hC_nn, hC⟩ := hQ hδ0 hδ_le
  refine ⟨fun m => C R₀ m, fun m => hC_nn R₀ m, ?_⟩
  intro T hT hδg hδZ hball m
  refine hC T hT hδg hδZ ?_ m
  refine le_trans (hsMono (I := I) (M := M) g₀ ?_ T) hball
  have h3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  linarith

/-- **Uniform pointwise fibre cap of a low-base coefficient on the a-priori
ball.**

A coefficient whose covariant jets obey the all-order tower
`‖∇ⁱ C‖² ≤ Kc i · (1 + ∑_{j < i+2} ‖∇ʲ T₀‖²)` has a fibre norm bounded uniformly
over the states `T₀` of the spectral `H^{a+2}` ball: the supercritical Sobolev
embedding consumes only the jets `∇ʲ C` with `j ≤ finrank ℝ E / 2 + 1`, whose
tower windows `∑_{l < j+2} ‖∇ˡ T₀‖²` stay inside the ball as soon as
`finrank ℝ E / 2 ≤ a`.

This supplies the fibre-cap hypothesis of
`exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le` for the
first-order arms, where — unlike the second-order arm, whose cap is the
smallness statement of `lowData_split` — no smallness is claimed and the cap
only has to exist. -/
private theorem coeffCap
    (g₀ : SmoothRiemannianMetric I M) (b a : ℕ)
    (ha : Module.finrank ℝ E / 2 ≤ a) {R₀ : ℝ}
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (C : SmoothCcTensor g₀ b 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ b 2 i C‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ b 2 x (C.toSection x) ≤
            Λ ^ 2 := by
  classical
  obtain ⟨Csh, hCsh_nn, hCsh⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g₀ b 2
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general
      (I := I) (M := M) g₀ (a + 2)
  have hW_nn : (0 : ℝ) ≤ Csh ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
      Kc j * (1 + (C2 * R₀) ^ 2) := by
    refine mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun j _ => ?_))
    exact mul_nonneg (hKc_nn j) (by positivity)
  refine ⟨Real.sqrt (Csh ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
      Kc j * (1 + (C2 * R₀) ^ 2)), Real.sqrt_nonneg _, ?_⟩
  intro C T₀ hball henv x
  rw [Real.sq_sqrt hW_nn]
  refine le_trans (hCsh C x) ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j hj => ?_)) (sq_nonneg _)
  have hjw : j < Module.finrank ℝ E / 2 + 2 := Finset.mem_range.mp hj
  refine le_trans (henv j) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hKc_nn j)
  have hwin : ∑ l ∈ Finset.range (j + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤
      ∑ l ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun l hl => Finset.mem_range.mpr
        (by have := Finset.mem_range.mp hl; omega))
      (fun l _ _ => sq_nonneg _)
  have hball_sq : ∑ l ∈ Finset.range (a + 2 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤ (C2 * R₀) ^ 2 := by
    have hnn : ∀ l ∈ Finset.range (a + 2 + 1),
        (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ := fun l _ => norm_nonneg _
    have hsq_le : ∑ l ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤
        (∑ l ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖) ^ 2 := by
      have hstep : ∀ l ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤
            ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ *
              ∑ i ∈ Finset.range (a + 2 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ := by
        intro l hl
        rw [sq]
        exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hnn hl) (norm_nonneg _)
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.sum_mul, sq]
    refine le_trans hsq_le ?_
    have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (by push_cast; ring) T₀
    have hjets := hC2 T₀
    rw [hcast] at hjets
    exact pow_le_pow_left₀ (Finset.sum_nonneg hnn)
      (le_trans hjets (mul_le_mul_of_nonneg_left hball hC2_nn)) 2
  linarith only [hwin, hball_sq]

set_option linter.unusedVariables false in
/-- **The `k`-uniform ladder for the low-base first-order arm.**

In dimension three, on the spectral `H^{a+2}` ball of radius `R₀`, there is a
rung-dependent constant family `Clower` such that every symmetric state `T` in
the ball whose fibre deviation is bounded by `δ ≤ 1/3` satisfies, at **every**
rung `m`,

`‖a₁ T‖_{H^m} ≤ Clower m · ‖T‖_{H^{m+1}}`,

where `a₁` is the genuinely first-order action of the fixed-background
low-base split `lowData_split g g_bg`.

This is the `a₁` sibling of `a2_ladder`, and its shape differs in two ways that
are forced by the arm itself.  The norm pair drops from `a₂`'s `+2 / +1` to
`+1 / +0`, because `a₁ W = appCc A.C0 W + appCc A.C1 (∇W)` carries only one
derivative of the state.  And there is **no top term**: `a₁` is a lower-slot
arm, so its whole contribution may be charged to a rung-dependent constant, and
no smallness — no `κ · δ/(1-δ)²` factor — is needed or available.  Making the
statement `κ`-free is what the dissipation hierarchy consumes: the ladder's
single small constant lives on `a₂`, where the contraction is proved.

The gate `2 ≤ a` is the dimension-three reading of the derivative budget
`2 * (finrank ℝ E / 2) ≤ a` of
`exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le`.  It is one
above the towers' own `1 ≤ a` because the ladder additionally has to keep the
coefficients' Sobolev jet window inside the a-priori ball, and it is one below
`a2_ladder`'s `3 ≤ a`, so it never binds in the assembled ladder.

**Binder order (A2-ABS).**  The whole constant family is produced *before* `δ`
is bound, and is `δ`-free: the first-order arm's inputs (the `C0`/`C1` jet
towers, their fibre caps, and the coefficient-abstract engine) never see the
fibre deviation. -/
theorem a1_ladder_bg
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              ((lowBaseData (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).a1
                  (I := I) (M := M) T)‖ ≤
            Clower m *
              ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ := by
  classical
  obtain ⟨Kc0, hKc0_nn, htow0⟩ :=
    c0_jet_tower_bg (I := I) (M := M) hDim g g_bg a (by omega) hR₀
  obtain ⟨Kc1, hKc1_nn, htow1⟩ :=
    c1_jet_tower_bg (I := I) (M := M) hDim g g_bg a hR₀
  obtain ⟨Λ0, hΛ0_nn, hcap0⟩ :=
    coeffCap (I := I) (M := M) g 2 a (by omega) (R₀ := R₀) Kc0 hKc0_nn
  obtain ⟨Λ1, hΛ1_nn, hcap1⟩ :=
    coeffCap (I := I) (M := M) g 3 a (by omega) (R₀ := R₀) Kc1 hKc1_nn
  obtain ⟨Cm0, hCm0_nn, heng0⟩ :=
    exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le
      (I := I) (M := M) g a (by omega) hR₀ Kc0 hKc0_nn Λ0 hΛ0_nn
  obtain ⟨Cm1, hCm1_nn, heng1⟩ :=
    exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le
      (I := I) (M := M) g a (by omega) hR₀ Kc1 hKc1_nn Λ1 hΛ1_nn
  choose Chs hChs_nn hhs using fun n : ℕ =>
    exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general (I := I) (M := M) g n
  choose Cjet hCjet_nn hjet using fun n : ℕ =>
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g n
  refine ⟨fun m => Chs m * (∑ q ∈ Finset.range (m + 1), (Cm0 q + Cm1 q)) *
      Cjet (m + 1),
    fun m => mul_nonneg (mul_nonneg (hChs_nn m)
      (Finset.sum_nonneg (fun q _ => add_nonneg (hCm0_nn q) (hCm1_nn q))))
      (hCjet_nn _), ?_⟩
  intro δ hδ0 hδ_le T hT hδg hδZ hball m
  -- the low-base coefficient bundle, bound opaquely so that no later step
  -- unfolds the path-integral witnesses
  obtain ⟨A, hAdef, hc0jet, hc1jet⟩ :
      ∃ A : LowBaseActionData g,
        lowBaseData (I := I) (M := M) g g_bg T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ = A ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g 2 2 i A.C0‖ ^ 2 ≤
              Kc0 i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g 3 2 i A.C1‖ ^ 2 ≤
              Kc1 i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) :=
    ⟨lowBaseData (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ, rfl,
      htow0 T hT hδ0 hδ_le hδg hδZ hball,
      htow1 T hT hδ0 hδ_le hδg hδZ hball⟩
  rw [hAdef]
  clear hAdef
  -- every covariant jet of the first-order arm costs one derivative of `T`
  have hq : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 0 2 q (A.a1 (I := I) (M := M) T)‖ ≤
        (Cm0 q + Cm1 q) * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
          ‖iteratedCovGrad (I := I) g 0 2 i T‖ ^ 2) := by
    intro q
    have h0 := heng0 0 (by norm_num) A.C0 T hball
      (hcap0 A.C0 T hball hc0jet) hc0jet q
    have h1 := heng1 1 (by norm_num) A.C1 T hball
      (hcap1 A.C1 T hball hc1jet) hc1jet q
    have hsplitArm : A.a1 (I := I) (M := M) T =
        appCc (I := I) (M := M) g 2 2 A.C0 T +
          appCc (I := I) (M := M) g 3 2 A.C1
            (iteratedCovGrad (I := I) g 0 2 1 T) := rfl
    rw [hsplitArm, iteratedCovGrad_add, add_mul]
    exact le_trans (norm_add_le _ _) (add_le_add h0 h1)
  -- the `H^{m+1}` ball controls every jet window that the rungs `q ≤ m` see
  have hwin : ∀ q ∈ Finset.range (m + 1),
      Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
          ‖iteratedCovGrad (I := I) g 0 2 i T‖ ^ 2) ≤
        Cjet (m + 1) * ‖smoothCcToTensorHs (I := I) (M := M) g
          ((m + 1 : ℕ) : ℝ) T‖ := by
    intro q hq'
    have hqm : q ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq')
    refine le_trans (sqrt_finset_sum_sq_le_sum _ _ (fun i _ => norm_nonneg _)) ?_
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi => Finset.mem_range.mpr
        (by have := Finset.mem_range.mp hi; omega))
      (fun i _ _ => norm_nonneg _)) (hjet (m + 1) T)
  -- assemble the rungs `q ≤ m` into the spectral `H^m` norm
  refine le_trans (hhs m (A.a1 (I := I) (M := M) T)) ?_
  have hsum : ∑ q ∈ Finset.range (m + 1),
      ‖iteratedCovGrad (I := I) g 0 2 q (A.a1 (I := I) (M := M) T)‖ ≤
      (∑ q ∈ Finset.range (m + 1), (Cm0 q + Cm1 q)) *
        (Cjet (m + 1) * ‖smoothCcToTensorHs (I := I) (M := M) g
          ((m + 1 : ℕ) : ℝ) T‖) := by
    refine le_trans (Finset.sum_le_sum (fun q hq' =>
      le_trans (hq q) (mul_le_mul_of_nonneg_left (hwin q hq')
        (add_nonneg (hCm0_nn q) (hCm1_nn q))))) (le_of_eq ?_)
    rw [Finset.sum_mul]
  have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g ((m + 1 : ℕ) : ℝ) T‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g
      (by push_cast; ring) T
  rw [← hcast]
  refine le_trans (mul_le_mul_of_nonneg_left hsum (hChs_nn m)) (le_of_eq (by ring))

set_option linter.unusedVariables false in
/-- Diagonal-background compatibility wrapper for `a1_ladder_bg`. -/
theorem a1_ladder
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              ((lowBaseData (I := I) (M := M) g g T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).a1
                  (I := I) (M := M) T)‖ ≤
            Clower m *
              ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ :=
  a1_ladder_bg (I := I) (M := M) hDim g g a ha hR₀

set_option linter.unusedVariables false in
/-- **The `k`-uniform ladder for the low-base first-order arm, ball-free.**

For **every** symmetric state `T` with fibre deviation `δ ≤ 1/3`, every rung
`m`, and every `R` with `‖T‖_{H⁴} ≤ R`,

`‖a₁ T‖_{H^m} ≤ Clower R m · ‖T‖_{H^{m+1}}`,

with the radius-indexed family `Clower : ℝ → ℕ → ℝ` chosen before the state
and, as in `a1_ladder_bg`, before `δ` — the first-order arm never sees the fibre
deviation.  This is `a1_ladder` with the a-priori-ball binder removed; the
consumer may take `R := ‖T‖_{H⁴}`.

The `H⁴` radius (one below `a2LadderQ`'s `H⁵`) is the ball order of the
low band of
`exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le`, whose
gate `2 * (finrank ℝ E / 2) ≤ a` is sharp in dimension three: the band split
at `finrank ℝ E / 2 + m` leaves `q ≤ 1` to the low band, which needs the
coefficient's Sobolev window `∇^{i+j} C`, `i ≤ q`, `j ≤ finrank ℝ E / 2 + 1`,
inside the ball.  So it too cannot be lowered to `H³`. -/
theorem a1LadderQBg
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Clower : ℝ → ℕ → ℝ, (∀ R m, 0 ≤ Clower R m) ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}
        (hR : ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ ≤ R)
        (m : ℕ),
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              ((lowBaseData (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).a1
                  (I := I) (M := M) T)‖ ≤
            Clower R m *
              ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ := by
  classical
  choose C hC_nn hC using fun R : ℝ =>
    a1_ladder_bg (I := I) (M := M) hDim g g_bg 2 le_rfl
      (R₀ := |R|) (abs_nonneg R)
  refine ⟨C, hC_nn, ?_⟩
  intro δ hδ0 hδ_le T hT hδg hδZ R hR m
  refine hC R hδ0 hδ_le T hT hδg hδZ ?_ m
  refine le_trans (le_of_eq ?_) (le_trans hR (le_abs_self R))
  exact smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g
    (by push_cast; norm_num) T

set_option linter.unusedVariables false in
/-- Diagonal-background compatibility wrapper for `a1LadderQBg`. -/
theorem a1LadderQ
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ Clower : ℝ → ℕ → ℝ, (∀ R m, 0 ≤ Clower R m) ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}
        (hR : ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ ≤ R)
        (m : ℕ),
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              ((lowBaseData (I := I) (M := M) g g T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).a1
                  (I := I) (M := M) T)‖ ≤
            Clower R m *
              ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ :=
  a1LadderQBg (I := I) (M := M) hDim g g

set_option linter.unusedVariables false in
/-- **The full low-regularity dissipation ladder of the zero-based
Ricci--DeTurck remainder, at every rung.**

In dimension three, on the spectral `H^{a+2}` ball of radius `R₀`, there are a
constant `κ` and a rung-dependent constant family `Clower` such that every
symmetric `T` in the ball whose fibre deviation is bounded by `δ ≤ 1/3`
satisfies, at **every** rung `m`,

`‖N T - N 0‖_{H^m} ≤ κ · δ/(1-δ)² · ‖T‖_{H^{m+2}} + Clower m · ‖T‖_{H^{m+1}}`,

where `N` is the zero-based smooth Ricci--DeTurck remainder over the background
`g₀`.  This is the all-rung form of `n_diff_h1_rung`, and it is the estimate
`F6_ESTIMATE_RECON.md` §7.3 row E0e asks for.

The proof is one triangle inequality over the canonical two-arm split
`N T - N 0 = a₂ T + a₁ T` of `lowData_split`, with `a2_ladder` on the
second-order arm and `a1_ladder` on the first-order one.  The top-order constant
`κ · δ/(1-δ)²` carries no `m` and comes entirely from `a₂`; the first-order arm
contributes only to `Clower m`, which multiplies the *lower* order `H^{m+1}`.
The gate `3 ≤ a` is `a2_ladder`'s and subsumes `a1_ladder`'s `2 ≤ a`.

**Binder order (A2-ABS).**  As in `a2_ladder`: the absorption constant `κ` is
produced *before* `δ` is bound (it is `lowData_split`'s `δ`-free `K`), so the
threshold `δ*` may be chosen from `κ`; the rung constants `Clower` are bound
after `δ`, inheriting `a2_ladder`'s dependence. -/
theorem n_diff_hm_rung
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 3 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ κ : ℝ, 0 ≤ κ ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3),
      ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x u v =
            ccTensorBilin (I := I) g₀ T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (deTurckSmoothRemainder (I := I) g₀ g₀ T
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδg -
                deTurckSmoothRemainder (I := I) g₀ g₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδZ)‖ ≤
            κ * (δ / (1 - δ) ^ 2) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T‖ +
              Clower m *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T‖ := by
  classical
  obtain ⟨κ, hκ, h2⟩ := a2_ladder (I := I) (M := M) hDim g₀ a ha hR₀
  obtain ⟨C1low, hC1low_nn, h1⟩ :=
    a1_ladder (I := I) (M := M) hDim g₀ a (by omega) hR₀
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g₀
  refine ⟨κ, hκ, ?_⟩
  intro δ hδ0 hδ_le
  obtain ⟨C2low, hC2low_nn, h2δ⟩ := h2 hδ0 hδ_le
  refine ⟨fun m => C2low m + C1low m,
    fun m => add_nonneg (hC2low_nn m) (hC1low_nn m), ?_⟩
  intro T hT hδg hδZ hball m
  rw [(hsplit T hT hδ_le hδ0 hδg hδZ).1, smoothCcToTensorHs_add]
  refine le_trans (norm_add_le _ _) ?_
  exact le_trans
    (add_le_add (h2δ T hT hδg hδZ hball m)
      (h1 hδ0 hδ_le T hT hδg hδZ hball m))
    (le_of_eq (by ring))

set_option linter.unusedVariables false in
/-- **The full low-regularity dissipation ladder, ball-free.**

For **every** symmetric state `T` with fibre deviation `δ ≤ 1/3`, every rung
`m`, and every `R` with `‖T‖_{H⁵} ≤ R`,

`‖N T - N 0‖_{H^m} ≤ κ · δ/(1-δ)² · ‖T‖_{H^{m+2}} + Clower R m · ‖T‖_{H^{m+1}}`,

where `N` is the zero-based smooth Ricci--DeTurck remainder over the arbitrary
fixed background `g_bg`.  This is the fixed-background analogue of
`n_diff_hm_rung` with the a-priori-ball binder removed: no `a`, no `R₀` fixed
before the state, no admissibility hypothesis on `T`.  The proof is the same
single triangle inequality over `lowData_split`'s two-arm split, now with
`a2LadderQ` and `a1LadderQ`; the two arms' sharp radii `H⁵` and `H⁴` are
merged into the single `H⁵` slot by order-monotonicity of the spectral norm.

`κ` is produced before `δ` and `Clower` before the state, so the absorption
threshold `δ*` may still be chosen from `κ` alone (A2-ABS).

**What this does and does not buy.**  It removes the quantifier obstruction —
the ladder now applies to every state, and the consumer supplies the radius
*after* seeing the state.  It does **not** make the lower constant depend on
`H²`/`H³` data: the `H⁵` radius is structural (see `a2LadderQ`), so for a
Galerkin trajectory the coefficient `Clower ‖U_N(t)‖_{H⁵} m` is not a priori
`N`-uniform.  That is the residual obstruction recorded in
`LowRegLadderRung.md`. -/
theorem nDiffHmQBg
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, 0 ≤ κ ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3),
      ∃ Clower : ℝ → ℕ → ℝ, (∀ R m, 0 ≤ Clower R m) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}
        (hR : ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖ ≤ R)
        (m : ℕ),
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              (deTurckSmoothRemainder (I := I) g g_bg T
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδg -
                deTurckSmoothRemainder (I := I) g g_bg
                  (0 : SmoothCcTensor g 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδZ)‖ ≤
            κ * (δ / (1 - δ) ^ 2) *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 2) T‖ +
              Clower R m *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ := by
  classical
  obtain ⟨κ, hκ, h2⟩ := a2LadderQBg (I := I) (M := M) hDim g g_bg
  obtain ⟨C1low, hC1low_nn, h1⟩ := a1LadderQBg (I := I) (M := M) hDim g g_bg
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g g_bg
  refine ⟨κ, hκ, ?_⟩
  intro δ hδ0 hδ_le
  obtain ⟨C2low, hC2low_nn, h2δ⟩ := h2 hδ0 hδ_le
  refine ⟨fun R m => C2low R m + C1low R m,
    fun R m => add_nonneg (hC2low_nn R m) (hC1low_nn R m), ?_⟩
  intro T hT hδg hδZ R hR m
  have hR4 : ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ ≤ R :=
    le_trans (hsMono (I := I) (M := M) g (by norm_num) T) hR
  rw [(hsplit T hT hδ_le hδ0 hδg hδZ).1, smoothCcToTensorHs_add]
  refine le_trans (norm_add_le _ _) ?_
  exact le_trans
    (add_le_add (h2δ T hT hδg hδZ hR m)
      (h1 hδ0 hδ_le T hT hδg hδZ hR4 m))
    (le_of_eq (by ring))

/-- Diagonal-background compatibility wrapper for `nDiffHmQBg`. -/
theorem nDiffHmQ
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, 0 ≤ κ ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3),
      ∃ Clower : ℝ → ℕ → ℝ, (∀ R m, 0 ≤ Clower R m) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}
        (hR : ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖ ≤ R)
        (m : ℕ),
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              (deTurckSmoothRemainder (I := I) g g T
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδg -
                deTurckSmoothRemainder (I := I) g g
                  (0 : SmoothCcTensor g 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδZ)‖ ≤
            κ * (δ / (1 - δ) ^ 2) *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 2) T‖ +
              Clower R m *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ :=
  nDiffHmQBg (I := I) (M := M) hDim g g

/-- A fixed top coefficient for the all-order low-regularity DeTurck remainder
ladder at an arbitrary fixed DeTurck background.  The coefficient is selected
before the fibre threshold, state, `H⁵` radius, and rung. -/
def IsHmRungOrdBg (g g_bg : SmoothRiemannianMetric I M) (κ : ℝ) : Prop :=
  0 ≤ κ ∧
    ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3),
      ∃ Clower : ℝ → ℕ → ℝ, (∀ R m, 0 ≤ Clower R m) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}
        (hR : ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖ ≤ R)
        (m : ℕ),
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              (deTurckSmoothRemainder (I := I) g g_bg T
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδg -
                deTurckSmoothRemainder (I := I) g g_bg
                  (0 : SmoothCcTensor g 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδZ)‖ ≤
            κ * (δ / (1 - δ) ^ 2) *
                ‖smoothCcToTensorHs (I := I) (M := M) g
                  ((m : ℝ) + 2) T‖ +
              Clower R m *
                ‖smoothCcToTensorHs (I := I) (M := M) g
                  ((m : ℝ) + 1) T‖

/-- A fixed top coefficient for the all-order low-regularity DeTurck remainder
ladder.  The coefficient is selected before the fibre threshold, state, `H⁵`
radius, and rung. -/
def IsHmRungOrd (g : SmoothRiemannianMetric I M) (κ : ℝ) : Prop :=
  IsHmRungOrdBg (I := I) (M := M) g g κ

/-- Package the arbitrary-background ordered coefficient supplied by
`nDiffHmQBg`. -/
theorem lowregHmPackBg
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, IsHmRungOrdBg (I := I) (M := M) g g_bg κ := by
  obtain ⟨κ, hκ, hord⟩ := nDiffHmQBg (I := I) (M := M) hDim g g_bg
  exact ⟨κ, hκ, hord⟩

/-- Diagonal-background compatibility wrapper for `lowregHmPackBg`. -/
theorem lowregHmPack
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, IsHmRungOrd (I := I) (M := M) g κ := by
  simpa only [IsHmRungOrd] using
    (lowregHmPackBg (I := I) (M := M) hDim g g)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
