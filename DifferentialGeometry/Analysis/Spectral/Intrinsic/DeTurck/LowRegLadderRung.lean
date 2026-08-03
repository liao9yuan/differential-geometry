import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegC2JetTower
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

set_option linter.unusedVariables false in
/-- **The all-order `L²` jet tower of the complete zero-based second-order
coefficient `A.C2`.**

The `i`-th covariant jet of the canonical top coefficient is controlled, with a
constant depending only on the background metric and the order `i`, by the
state's own jets through order `i + 1`:

`‖∇ⁱ (lowBaseData g g T …).C2‖² ≤ Kc i * (1 + ∑_{j < i+2} ‖∇ʲ T‖²)`.

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
The binder is kept because `a2_ladder` and the operator-norm engine carry it. -/
theorem c2_jet_tower
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (a : ℕ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
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
              (lowBaseData (I := I) (M := M) g g T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).C2‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨Kk, hKk_nn, hker⟩ := topKer_jet (I := I) (M := M) hDim g
  refine ⟨Kk, hKk_nn, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ hball i
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hΛ : 0 ≤ Kk i * (1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) :=
    mul_nonneg (hKk_nn i) (by linarith only [hsum])
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  -- the coefficient is a single cancellation-preserving path integral; bind the
  -- witness opaquely and pass the order-`i` jet bound through the integral
  obtain ⟨X, hXdef, hXjet⟩ :
      ∃ X : SmoothCcTensor g 4 2,
        (lowBaseData (I := I) (M := M) g g T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).C2 = X ∧
          lowJetSq (I := I) (M := M) g i X ≤
            Kk i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) :=
    ⟨rhsRefoldTopInt (I := I) (M := M) g g T hδ_lt hδg hδZ +
        LowBaseInternal.selfTopInt (I := I) (M := M) g T hδ_lt hδg hδZ -
        deTurckPhiMetTotal (I := I) (M := M) g g g, rfl,
      path_add_sub_jet (I := I) (M := M) g 4 i hSI
        (rhsRefoldTop (I := I) (M := M) g g T hδg hδZ)
        (LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hδg hδZ)
        (deTurckPhiMetTotal (I := I) (M := M) g g g)
        (rhsRefoldTop_joint (I := I) (M := M) g g T hδ_lt hδg hδZ)
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
Leibniz split threshold of `master_appCc_jet_le_sharp` makes available. -/
theorem a2_ladder
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 3 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) :
    ∃ (κ : ℝ) (Clower : ℕ → ℝ), 0 ≤ κ ∧ (∀ m, 0 ≤ Clower m) ∧
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
  obtain ⟨K, hK, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g₀
  obtain ⟨Kc, hKc_nn, htower⟩ := c2_jet_tower (I := I) (M := M) hDim g₀ a hR₀
  have hεC_nn : (0 : ℝ) ≤ K * (δ / (1 - δ) ^ 2) :=
    mul_nonneg hK (div_nonneg hδ0 (sq_nonneg _))
  obtain ⟨Cop, hCop_nn, hop⟩ :=
    appCc_cap_hs_le (I := I) (M := M) g₀ a (by omega) hR₀
      (K * (δ / (1 - δ) ^ 2)) hεC_nn Kc hKc_nn
  refine ⟨K, Cop, hK, hCop_nn, ?_⟩
  intro T hT hδg hδZ hball m
  -- the low-base coefficient bundle, bound opaquely so that no later step
  -- unfolds the path-integral witnesses
  obtain ⟨A, hAdef, hc2pt, hc2jet⟩ :
      ∃ A : LowBaseActionData g₀,
        lowBaseData (I := I) (M := M) g₀ g₀ T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ = A ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              (A.C2.toSection x) ≤ (K * (δ / (1 - δ) ^ 2)) ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ 4 2 i A.C2‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) :=
    ⟨lowBaseData (I := I) (M := M) g₀ g₀ T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ, rfl,
      (hsplit T hT hδ_le hδ0 hδg hδZ).2,
      htower T hT hδ0 hδ_le hδg hδZ hball⟩
  rw [hAdef]
  clear hAdef
  have hshape : A.a2 (I := I) (M := M) T =
      appCc (I := I) (M := M) g₀ (2 + 2) 2 A.C2
        (iteratedCovGrad (I := I) g₀ 0 2 2 T) := rfl
  rw [hshape]
  exact le_trans (hop A.C2 T hball hc2pt hc2jet m) (le_of_eq (by ring))

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
