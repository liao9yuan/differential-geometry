import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegOpJetWindows

/-!
# All-order jet towers of the low-base first- and zeroth-order coefficients

`LowRegC2JetTower.lean` supplies the all-order jet tower of the second-order
coefficient `A.C2`.  This module supplies the two remaining coefficients of the
same split,

* `A.C1 = rhsLow1PathIntegral g g T 0 …`, valence `(3,2)`, and
* `A.C0 = selfLowInt g g T … + phiMetCurvCoeff g g g`, valence `(2,2)`,

whose actions assemble `LowBaseActionData.a1`.  Because `a1` carries only **one**
derivative of the state, both towers may spend an `m`-dependent constant; no
smallness beyond `δ ≤ 1/3` is used, and neither the resolvent commutator nor an
a-priori Sobolev ball enters.

Both coefficients are path integrals over the radial segment, so each tower has
two layers: a uniform-in-`s` jet bound for the integrand (`low1Ker_jet`,
`selfLow_jet`), obtained on the ball-free Moser route of
`LowRegOpJetWindows.lean`, and the passage through the parameter integral, which
is `path_jetL2_le`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open LowBaseInternal

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

section Integrand

/-- **The all-order jet window of the order-one path integrand.**

Uniformly in the radial parameter `s ∈ [0,1]`, the order-one integrand
`rhsLow1Coeff g g T 0 s` has its `i`-th covariant `L²` jet controlled by the
state's own jets through order `i + 1`, with constants depending on neither the
state nor `s`.

This is the `C1` sibling of `topKer_jet`.  It is the campaign frontier of brick
A1a; see `LowRegC01JetTower.md` for why the `IsMoserWin` vocabulary of
`LowRegOpJetWindows.lean` cannot express it (the bare connection difference
carries no order-zero fibre cap) and which radius-free engine is the right
currency. -/
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
theorem low1Ker_jet
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ Kk : ℕ → ℝ, (∀ i, 0 ≤ Kk i) ∧
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
        (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        lowJetSq (I := I) (M := M) g i
            (rhsLow1Coeff (I := I) (M := M) g g T
              (0 : SmoothCcTensor g 0 2) hδg hδZ s) ≤
          Kk i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  sorry

/-- **Cancellation-preserving normal form of the zero-arm self-action
integrand.**

At the frozen background the second-derivative heads of the DeTurck Lie
coefficient and of the `lieCorr0` insertion arm cancel pairwise
(`insert_base`), leaving the Palatini covariant-derivative arm against the
subtracted edge pairing, plus the three residual `lieCorr0` pieces:

`rhsSelfLow = (-2)•ricciGoodLow + (deTurckLieCovDerivArmField − edgeLiePairFam)
  + lc0VB + lc0AMix + lc0Riem`.

This is the grouping in which every summand costs only **one** derivative of the
state — the individual summands `deTurckLieCoeffField` and `lieCorr0Field` cost
two — so it is the only grouping in which `c0_jet_tower`'s `range (i + 2)`
budget is honest. -/
theorem selfLow_split
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    rhsSelfLow (I := I) (M := M) g g T hδ hδZ s =
      let gm := realizedFam (I := I) g T 0 hδ hδZ s
      (-2 : ℝ) • ricciGoodLow (I := I) (M := M) g gm (s • T) +
          (deTurckLieCovDerivArmField (I := I) (M := M) g gm g -
            edgeLiePairFam (I := I) (M := M) g T hδ hδZ
              lieRefoldQ lieRefoldEps s) +
          lc0VB (I := I) (M := M) g gm +
          lc0AMix (I := I) (M := M) g gm g +
          lc0Riem (I := I) (M := M) g gm := by
  have h := tail_base_split (I := I) (M := M) g
    (realizedFam (I := I) g T 0 hδ hδZ s) g
  rw [sub_self, zero_add] at h
  have h' : lieCorr0Field (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ s) g =
      lc0VB (I := I) (M := M) g (realizedFam (I := I) g T 0 hδ hδZ s) +
        lc0AMix (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ s) g +
        lc0Riem (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ s) -
        deTurckLieEndoArmField (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ s) g := by
    rw [← h]; abel
  rw [selfLow_good (I := I) (M := M) g g T hT hδ_lt hδ hδZ hs]
  simp only [deTurckLieCoeffField_eq_covDerivArm_add_endoArm, h']
  abel

/-- **The all-order jet window of the zero-order path integrand.**

Uniformly in the radial parameter `s ∈ [0,1]`, the zero-arm self-action
integrand `rhsSelfLow g g T s` has its `i`-th covariant `L²` jet controlled by
the state's own jets through order `i + 1`.

This is the `C0` sibling of `topKer_jet`.  The Palatini refold that trades the
second metric derivative of the DeTurck Lie arm for curvature is what keeps the
derivative offset at one: it is the subtracted `edgeLiePairFam` inside
`rhsSelfLow` itself, and `selfLow_split` is the grouping in which that
cancellation is visible.  It is the campaign frontier of brick A1b; see
`LowRegC01JetTower.md`. -/
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
theorem selfLow_jet
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ Kk : ℕ → ℝ, (∀ i, 0 ≤ Kk i) ∧
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
        (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        lowJetSq (I := I) (M := M) g i
            (rhsSelfLow (I := I) (M := M) g g T hδg hδZ s) ≤
          Kk i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  sorry

end Integrand

section Towers

set_option linter.unusedVariables false in
/-- **The all-order `L²` jet tower of the low-base first-order coefficient
`A.C1`.**

`‖∇ⁱ (lowBaseData g g T …).C1‖² ≤ Kc i * (1 + ∑_{j < i+2} ‖∇ʲ T‖²)`.

This is hypothesis (b) of the order-generic operator-norm engine for the
first-order arm, and it is the `C1` input of `a1_ladder`.  Statement shape is
`c2_jet_tower`'s with valence `4 2` replaced by `3 2`: constants before the
state, `range (i + 2)` budget, `δ ≤ 1/3` the only smallness input.

The `H^{a+2}` ball hypothesis is inert — the statement quantifies over an
arbitrary `a` — and is kept only because `a1_ladder` and the operator-norm
engine carry it. -/
theorem c1_jet_tower
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
          ‖iteratedCovGrad (I := I) g 3 2 i
              (lowBaseData (I := I) (M := M) g g T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).C1‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨Kk, hKk_nn, hker⟩ := low1Ker_jet (I := I) (M := M) hDim g
  refine ⟨Kk, hKk_nn, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ hball i
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set Λ : ℝ := Kk i * (1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hΛdef
  have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hΛ : 0 ≤ Λ := mul_nonneg (hKk_nn i) (by linarith only [hsum])
  have hsΛ : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hΛ
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hpath := path_jetL2_le (I := I) (M := M) g 3 2 i
    (fun s => rhsLow1Coeff (I := I) (M := M) g g T
      (0 : SmoothCcTensor g 0 2) hδg hδZ s)
    (realizedSmallSet (δ := δ) (δ' := δ))
    realizedSmallSet_isOpen hSI
    (rhsLow1_path_joint (I := I) (M := M) g g T
      (0 : SmoothCcTensor g 0 2) hδg hδZ)
    (Real.sqrt_nonneg Λ)
    (fun s hs => by
      rw [hsΛ, hΛdef]
      simpa only [lowJetSq] using
        hker T hT hδ0 hδ_le hδg hδZ i s hs)
  rw [hsΛ] at hpath
  have hjet : lowJetSq (I := I) (M := M) g i
      (lowBaseData (I := I) (M := M) g g T hδ_lt hδg hδZ).C1 ≤ Λ := by
    rw [c1_eq (I := I) (M := M) g g T hδ_lt hδg hδZ]
    simpa only [rhsLow1PathIntegral, lowJetSq] using hpath
  refine le_trans ?_ hjet
  unfold lowJetSq
  exact Finset.single_le_sum
    (fun q _ => sq_nonneg ‖iteratedCovGrad (I := I) g 3 2 q
      (lowBaseData (I := I) (M := M) g g T hδ_lt hδg hδZ).C1‖)
    (Finset.mem_range.mpr (Nat.lt_succ_self i))

set_option linter.unusedVariables false in
/-- **The all-order `L²` jet tower of the low-base zeroth-order coefficient
`A.C0`.**

`‖∇ⁱ (lowBaseData g g T …).C0‖² ≤ Kc i * (1 + ∑_{j < i+2} ‖∇ʲ T‖²)`.

Statement shape is `c2_jet_tower`'s with valence `4 2` replaced by `2 2`.  The
fixed curvature summand `phiMetCurvCoeff g g g` of `A.C0` is state-free, so it
contributes only to the constant. -/
theorem c0_jet_tower
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
          ‖iteratedCovGrad (I := I) g 2 2 i
              (lowBaseData (I := I) (M := M) g g T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).C0‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨Kk, hKk_nn, hker⟩ := selfLow_jet (I := I) (M := M) hDim g
  refine ⟨fun i => 2 * (Kk i +
      lowJetSq (I := I) (M := M) g i (-phiMetCurvCoeff (I := I) g g g)),
    fun i => by
      have := jetNn (I := I) (M := M) (m := i) g
        (-phiMetCurvCoeff (I := I) g g g)
      have := hKk_nn i
      linarith, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ hball i
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set Λ : ℝ := Kk i * (1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hΛdef
  have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hΛ : 0 ≤ Λ := mul_nonneg (hKk_nn i) (by linarith only [hsum])
  have hsΛ : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hΛ
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hpath := path_jetL2_le (I := I) (M := M) g 2 2 i
    (rhsSelfLow (I := I) (M := M) g g T hδg hδZ)
    (realizedSmallSet (δ := δ) (δ' := δ))
    realizedSmallSet_isOpen hSI
    (selfLow_joint (I := I) (M := M) g g T hδg hδZ)
    (Real.sqrt_nonneg Λ)
    (fun s hs => by
      rw [hsΛ, hΛdef]
      simpa only [lowJetSq] using
        hker T hT hδ0 hδ_le hδg hδZ i s hs)
  rw [hsΛ] at hpath
  have hint : lowJetSq (I := I) (M := M) g i
      (selfLowInt (I := I) (M := M) g g T hδ_lt hδg hδZ) ≤ Λ := by
    simpa only [selfLowInt, lowJetSq] using hpath
  have hfix : (0 : ℝ) ≤ lowJetSq (I := I) (M := M) g i
      (-phiMetCurvCoeff (I := I) g g g) :=
    jetNn (I := I) (M := M) (m := i) g (-phiMetCurvCoeff (I := I) g g g)
  have hjet : lowJetSq (I := I) (M := M) g i
      (lowBaseData (I := I) (M := M) g g T hδ_lt hδg hδZ).C0 ≤
      2 * (Kk i +
        lowJetSq (I := I) (M := M) g i (-phiMetCurvCoeff (I := I) g g g)) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
    have hsplit := jetSub (I := I) (M := M) g i
      (selfLowInt (I := I) (M := M) g g T hδ_lt hδg hδZ)
      (-phiMetCurvCoeff (I := I) g g g)
    rw [sub_neg_eq_add] at hsplit
    rw [c0_eq (I := I) (M := M) g g T hδ_lt hδg hδZ]
    refine hsplit.trans ?_
    have : Λ + lowJetSq (I := I) (M := M) g i
          (-phiMetCurvCoeff (I := I) g g g) ≤
        (Kk i + lowJetSq (I := I) (M := M) g i
            (-phiMetCurvCoeff (I := I) g g g)) *
          (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
      rw [hΛdef]
      nlinarith [hsum, hfix]
    linarith only [hint, this]
  refine le_trans ?_ hjet
  unfold lowJetSq
  exact Finset.single_le_sum
    (fun q _ => sq_nonneg ‖iteratedCovGrad (I := I) g 2 2 q
      (lowBaseData (I := I) (M := M) g g T hδ_lt hδg hδZ).C0‖)
    (Finset.mem_range.mpr (Nat.lt_succ_self i))

end Towers

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
