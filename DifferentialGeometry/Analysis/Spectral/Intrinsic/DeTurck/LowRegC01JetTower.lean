import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegOpJetWindows
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Low1KerRadiusFree
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SelfLowCapWindows
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SelfLowArmCaps

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

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **The all-order jet window of the order-one path integrand.**

Uniformly in the radial parameter `s ∈ [0,1]`, the order-one integrand
`rhsLow1Coeff g g T 0 s` has its `i`-th covariant `L²` jet controlled by the
state's own jets through order `i + 1`, with constants depending on neither the
state nor `s`.

This is the `C1` sibling of `topKer_jet`.  The `IsMoserWin` vocabulary of
`LowRegOpJetWindows.lean` cannot express it — the bare connection difference
carries no order-zero fibre cap — so the currency is the radius-free
antidiagonal-grid window of `Low1KerRadiusFree.lean`: `low1Atgw` bounds the
integrand's fibre jets pointwise at offset `+2`, and `atgwToJet` integrates that
into the `range (i + 2)` budget.  `pathPert_rad` supplies the perturbation data
uniformly in `s`, which is why no constant here sees the path parameter. -/
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
  classical
  have h30 : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have h31 : (1 / 3 : ℝ) < 1 := by norm_num
  have hΛ₀0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * (1 / 3) :=
    mul_nonneg (Nat.cast_nonneg _) h30
  obtain ⟨Kw, hKw_nn, hw⟩ := low1Atgw (I := I) (M := M) g h31 hΛ₀0
  obtain ⟨Kint, hKint_nn, hint⟩ := atgwToJet (I := I) (M := M) g hΛ₀0
  refine ⟨fun i => ∑ q ∈ Finset.range (i + 1),
      Kw q * (∑ k ∈ Finset.range (q + 2), Kint k),
    fun i => Finset.sum_nonneg (fun q _ => mul_nonneg (hKw_nn q)
      (Finset.sum_nonneg (fun k _ => hKint_nn k))), ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le h31
  -- the state is its own `L∞` witness: symmetry identifies it with `symmS g T`
  have hTsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (T.toSection x) ≤ ((Module.finrank ℝ E : ℝ) * (1 / 3)) ^ 2 := by
    intro x
    have h := rfns_symmS_zero_le_fibreSmall
      (I := I) (M := M) g h30 T hδ_le hδ0 hδg x
    rwa [symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g T hT] at h
  obtain ⟨⟨δ', hδ'0, hδ'_le, hP⟩, htie, hPsup, hPjet⟩ :=
    pathPert_rad (I := I) (M := M) g T hδ0 hδ_le hδ_lt hδg hδZ hTsup hs
  -- the integrand, in the shape the radius-free window covers
  have heq : rhsLow1Coeff (I := I) (M := M) g g T
        (0 : SmoothCcTensor g 0 2) hδg hδZ s =
      (-2 : ℝ) • linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδg hδZ s) +
        deTurckLieArm1Coeff (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδg hδZ s) g := rfl
  -- the per-order jet bound, uniformly in `s`
  have hq : ∀ q : ℕ, ‖iteratedCovGrad (I := I) g 3 2 q
        (rhsLow1Coeff (I := I) (M := M) g g T
          (0 : SmoothCcTensor g 0 2) hδg hδZ s)‖ ^ 2 ≤
      Kw q * (∑ k ∈ Finset.range (q + 2), Kint k) *
        (1 + ∑ j ∈ Finset.range (q + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j
            (convexPerturbation (I := I) g T 0 s)‖ ^ 2) := by
    intro q
    refine hint (convexPerturbation (I := I) g T 0 s) hPsup 3 2 q 2 _ (Kw q)
      (hKw_nn q) ?_
    intro x
    rw [heq]
    exact hw (realizedFam (I := I) g T 0 hδg hδZ s)
      (convexPerturbation (I := I) g T 0 s) htie hδ'_le hδ'0 hP hPsup q x
  -- the state dominates the perturbation's jets, at every order below `i + 1`
  have hPS : ∀ q : ℕ, q ≤ i →
      (∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j
          (convexPerturbation (I := I) g T 0 s)‖ ^ 2) ≤
        ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := by
    intro q hqi
    have h1 : (∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j
          (convexPerturbation (I := I) g T 0 s)‖ ^ 2) ≤
        ∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
      hPjet (q + 1)
    refine h1.trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun _ _ _ => sq_nonneg _)
  have hS_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold lowJetSq
  calc ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g 3 2 q
          (rhsLow1Coeff (I := I) (M := M) g g T
            (0 : SmoothCcTensor g 0 2) hδg hδZ s)‖ ^ 2
      ≤ ∑ q ∈ Finset.range (i + 1),
          Kw q * (∑ k ∈ Finset.range (q + 2), Kint k) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
        refine Finset.sum_le_sum (fun q hqm => ?_)
        refine (hq q).trans ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (hKw_nn q) (Finset.sum_nonneg (fun k _ => hKint_nn k)))
        have := hPS q (by have := Finset.mem_range.mp hqm; omega)
        linarith only [this]
    _ = (∑ q ∈ Finset.range (i + 1),
          Kw q * (∑ k ∈ Finset.range (q + 2), Kint k)) *
          (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
        rw [Finset.sum_mul]

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

set_option linter.unusedVariables false in
/-- **Capped window of the symmetrized first-order Ricci coefficient.**

`ricciGoodLow g₀ g₁ P = ccInputSymm (ricciAAArm g₀ g₁ + ricciDALow g₀ g₁ P)`.
Both arms are quadratic in `∇P` — `A·A` for the first, `∇A ⋆ ∇P` for the second
— so both need the `Λ`-capped currency; the input-slot symmetrization is a
product with a fixed slot-swap field and therefore free. -/
private theorem ricciGoodCap (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ Λ)
        (hP1 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 1 ≤ Λ),
        HasCapWin (I := I) (M := M) g₀ P
          (ricciGoodLow (I := I) (M := M) g₀ g₁ P) K := by
  classical
  obtain ⟨KAA, hKAA_nn, hAA⟩ := ricciAACap (I := I) (M := M) g₀ hδ₀ hΛ1
  obtain ⟨KDA, hKDA_nn, hDA⟩ := ricciDACap (I := I) (M := M) g₀ hδ₀ hΛ1
  choose SSw hSSw_nn hSSw using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i (ccSlotSwapField (I := I) (M := M) g₀)))
  set KL : ℕ → ℝ := fun i => 2 * KAA i + 2 * KDA i with hKL_def
  have hKL_nn : ∀ i, 0 ≤ KL i := fun i => by
    have := hKAA_nn i; have := hKDA_nn i; simp only [hKL_def]; linarith
  refine ⟨fun i => (1 / 2 : ℝ) ^ 2 * (2 * KL i + 2 * foldConst (E := E) 0 0 KL SSw i),
    fun i => by
      have h1 := hKL_nn i
      have h2 := foldConst_nn (E := E) (u := 0) (v := 0) hKL_nn hSSw_nn i
      have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 2 := by positivity
      nlinarith [h1, h2], ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 hP1
  have hLow : HasCapWin (I := I) (M := M) g₀ P
      (ricciAAArm (I := I) (M := M) g₀ g₁ +
        ricciDALow (I := I) (M := M) g₀ g₁ P) KL :=
    capAdd (I := I) (M := M) g₀ P (hAA g₁ P htie hδ_le hδ0 hδ hP0 hP1)
      (hDA g₁ P htie hδ_le hδ0 hδ hP0 hP1)
  have hSw : HasCapWin (I := I) (M := M) g₀ P
      (ccSlotSwapField (I := I) (M := M) g₀) SSw :=
    capOfBnd (I := I) (M := M) g₀ P _ hSSw_nn (fun i x => hSSw i x)
  have happ := capApp (I := I) (M := M) g₀ P
    (ricciAAArm (I := I) (M := M) g₀ g₁ + ricciDALow (I := I) (M := M) g₀ g₁ P)
    (ccSlotSwapField (I := I) (M := M) g₀) hKL_nn hSSw_nn hLow hSw
  exact capSmul (I := I) (M := M) g₀ P (1 / 2 : ℝ)
    (capAdd (I := I) (M := M) g₀ P hLow happ)

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **The all-order jet window of the zero-order path integrand.**

Uniformly in the radial parameter `s ∈ [0,1]`, the zero-arm self-action
integrand `rhsSelfLow g g T s` has its `i`-th covariant `L²` jet controlled by
the state's own jets through order `i + 1`, for states in a fixed `H^{a+2}`
ball.

This is the `C0` sibling of `topKer_jet`.  The Palatini refold that trades the
second metric derivative of the DeTurck Lie arm for curvature is what keeps the
derivative offset at one: it is the subtracted `edgeLiePairFam` inside
`rhsSelfLow` itself, and `selfLow_split` is the grouping in which that
cancellation is visible.

**Why the ball is a hypothesis and not decoration.**  Unlike the `C1` sibling
`low1Ker_jet`, which is *linear* in the connection difference and therefore
holds radius-free, two of `selfLow_split`'s five summands are *quadratic* in
`∇P`: the `A·A` arm inside `ricciGoodLow`, and `lc0VB`.  With only the fibre
bound `δ ≤ 1/3` on `P` the `range (i + 2)` budget is **false** — concentrate a
bump at `i = 0` and `‖T‖, ‖∇T‖` stay bounded in `L²` while `‖ |∇T|² ‖_{L²}`
blows up.  Gagliardo–Nirenberg closes the gap only through a cap on `∇P`, and
the `H^{a+2}` ball supplies exactly that: `1 ≤ a` gives `H³ ⊂ C¹` in dimension
three.  The gate is stated at its weakest useful value, so any consumer with a
larger bottom (`a2_ladder`'s `3 ≤ a`) discharges it arithmetically.

The six per-arm capped windows it consumes are `SelfLowCapWindows.lean`'s
(`ricciAACap`, `lc0AMixCap`, `lc0RiemCap`), `Lc0VBCapWindow.lean`'s
(`lc0VBCapAtgw`) and `SelfLowArmCaps.lean`'s (`ricciDACap`, `lieCovCap`); see
`LowRegC01JetTower.md`. -/
theorem selfLow_jet
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (a : ℕ) (ha : 1 ≤ a)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
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
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        lowJetSq (I := I) (M := M) g i
            (rhsSelfLow (I := I) (M := M) g g T hδg hδZ s) ≤
          Kk i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  have h30 : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have h31 : (1 / 3 : ℝ) < 1 := by norm_num
  -- the two pointwise caps, both fixed before the state is seen
  obtain ⟨Λ₁, hΛ₁0, hΛ₁⟩ := gradCapOfBall (I := I) (M := M) hDim g a ha hR₀
  set Λ : ℝ := max 1 (max (((Module.finrank ℝ E : ℝ) * (1 / 3)) ^ 2) (Λ₁ ^ 2)) with hΛdef
  have hΛ1 : (1 : ℝ) ≤ Λ := le_max_left _ _
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  have hΛA : ((Module.finrank ℝ E : ℝ) * (1 / 3)) ^ 2 ≤ Λ :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hΛB : Λ₁ ^ 2 ≤ Λ := le_trans (le_max_right _ _) (le_max_right _ _)
  -- the five capped windows and the capped integration step
  obtain ⟨K1, hK1_nn, w1⟩ := ricciGoodCap (I := I) (M := M) g h31 hΛ1
  obtain ⟨K2, hK2_nn, w2⟩ := lieCovCap (I := I) (M := M) g h31 hΛ1
  obtain ⟨K3, hK3_nn, w3⟩ := lc0VBCapAtgw (I := I) (M := M) g h31 hΛ1
  obtain ⟨K4, hK4_nn, w4⟩ := lc0AMixCap (I := I) (M := M) g g h31 hΛ1
  obtain ⟨K5, hK5_nn, w5⟩ := lc0RiemCap (I := I) (M := M) g h31 hΛ1
  obtain ⟨Kint, hKint_nn, hint⟩ := capJet (I := I) (M := M) g hΛ0
  set KS : ℕ → ℝ := fun i =>
    2 * (2 * (2 * (2 * ((-2 : ℝ) ^ 2 * K1 i) + 2 * K2 i) + 2 * K3 i) + 2 * K4 i) +
      2 * K5 i with hKS_def
  have hKS_nn : ∀ i, 0 ≤ KS i := by
    intro i
    have h1 := hK1_nn i; have h2 := hK2_nn i; have h3 := hK3_nn i
    have h4 := hK4_nn i; have h5 := hK5_nn i
    simp only [hKS_def]
    nlinarith [h1, h2, h3, h4, h5]
  refine ⟨fun i => ∑ q ∈ Finset.range (i + 1),
      KS q * (∑ k ∈ Finset.range (q + 1), Kint k),
    fun i => Finset.sum_nonneg (fun q _ => mul_nonneg (hKS_nn q)
      (Finset.sum_nonneg (fun k _ => hKint_nn k))), ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ hball i s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le h31
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  -- the state is its own `L∞` witness
  have hTsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (T.toSection x) ≤ ((Module.finrank ℝ E : ℝ) * (1 / 3)) ^ 2 := by
    intro x
    have h := rfns_symmS_zero_le_fibreSmall
      (I := I) (M := M) g h30 T hδ_le hδ0 hδg x
    rwa [symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g T hT] at h
  obtain ⟨⟨δ', hδ'0, hδ'_le, hP⟩, htie, hPsup, hPjet⟩ :=
    pathPert_rad (I := I) (M := M) g T hδ0 hδ_le hδ_lt hδg hδZ hTsup hs
  set P : SmoothCcTensor g 0 2 := convexPerturbation (I := I) g T 0 s with hP_def
  have hPeq : P = s • T := by
    rw [hP_def, convexPerturbation, smul_zero, zero_add]
  -- the two caps on the perturbation
  have hP0 : ∀ x : M, gridBase (I := I) (M := M) g P x 0 ≤ Λ := by
    intro x
    refine le_trans ?_ hΛA
    simpa using hPsup x
  have hP1 : ∀ x : M, gridBase (I := I) (M := M) g P x 1 ≤ Λ := by
    intro x
    refine le_trans ?_ hΛB
    have hsq : s ^ 2 ≤ 1 := by nlinarith [hs0, hs1]
    have hsm : riemannianFiberNormSq (I := I) (M := M) g 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x) =
        s ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) := by
      rw [hPeq, iteratedCovGrad_smul_real (I := I) (M := M) g 0 2 1 s T,
        SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
        riemannianFiberNormSq_smul (I := I) (M := M) g 0 (2 + 1) x s _]
    have hT1 := hΛ₁ T hball x
    have hnn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) :=
      riemannianFiberNormSq_nonneg _ _ _ _ _
    have hgb : gridBase (I := I) (M := M) g P x 1 =
        riemannianFiberNormSq (I := I) (M := M) g 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x) := rfl
    rw [hgb, hsm]
    nlinarith [hT1, hnn, hsq]
  -- the capped window of the whole integrand, summand by summand
  have hwin : HasCapWin (I := I) (M := M) g P
      (rhsSelfLow (I := I) (M := M) g g T hδg hδZ s) KS := by
    have e1 := capSmul (I := I) (M := M) g P (-2 : ℝ)
      (w1 (realizedFam (I := I) g T 0 hδg hδZ s) P htie hδ'_le hδ'0 hP hP0 hP1)
    have e2 := w2 T hT hδ_le hδ0 hδg hδZ hs hP0 hP1
    have e3 : HasCapWin (I := I) (M := M) g P
        (lc0VB (I := I) (M := M) g (realizedFam (I := I) g T 0 hδg hδZ s)) K3 :=
      fun n x => w3 (realizedFam (I := I) g T 0 hδg hδZ s) P htie hδ'_le hδ'0 hP hP0 hP1 n x
    have e4 := w4 (realizedFam (I := I) g T 0 hδg hδZ s) P htie hδ'_le hδ'0 hP hP0 hP1
    have e5 := w5 (realizedFam (I := I) g T 0 hδg hδZ s) P htie hδ'_le hδ'0 hP hP0 hP1
    have hsum := capAdd (I := I) (M := M) g P
      (capAdd (I := I) (M := M) g P
        (capAdd (I := I) (M := M) g P
          (capAdd (I := I) (M := M) g P e1 e2) e3) e4) e5
    refine capCongr (I := I) (M := M) g P ?_ hsum
    rw [selfLow_split (I := I) (M := M) g T hT hδ_lt hδg hδZ hs, hPeq]
  -- integrate, and dominate the perturbation's jets by the state's
  have hq : ∀ q : ℕ, ‖iteratedCovGrad (I := I) g 2 2 q
        (rhsSelfLow (I := I) (M := M) g g T hδg hδZ s)‖ ^ 2 ≤
      KS q * (∑ k ∈ Finset.range (q + 1), Kint k) *
        (1 + ∑ j ∈ Finset.range (q + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) :=
    fun q => hint P hP1 _ hKS_nn hwin q
  have hPS : ∀ q : ℕ, q ≤ i →
      (∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤
        ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := by
    intro q hqi
    have h1 : (∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤
        ∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
      hPjet (q + 1)
    refine h1.trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun _ _ _ => sq_nonneg _)
  have hS_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold lowJetSq
  calc ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g 2 2 q
          (rhsSelfLow (I := I) (M := M) g g T hδg hδZ s)‖ ^ 2
      ≤ ∑ q ∈ Finset.range (i + 1),
          KS q * (∑ k ∈ Finset.range (q + 1), Kint k) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
        refine Finset.sum_le_sum (fun q hqm => ?_)
        refine (hq q).trans ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (hKS_nn q) (Finset.sum_nonneg (fun k _ => hKint_nn k)))
        have := hPS q (by have := Finset.mem_range.mp hqm; omega)
        linarith only [this]
    _ = (∑ q ∈ Finset.range (i + 1),
          KS q * (∑ k ∈ Finset.range (q + 1), Kint k)) *
          (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
        rw [Finset.sum_mul]

/-! ### The quadratic (cap-free) sibling

`selfLow_jet` spends the `H^{a+2}` ball on a pointwise cap `Λ`, and its constant
carries a `Λ`-degree growing with the order.  The *marked* currency
(`TameMarkWin.lean`) replaces the cap by a single explicit power of `‖T‖²_{H³}`:
every arm of `selfLow_split` now has a marked window with STATE-FREE constants,
and `markJet`/`markJet0` integrate them into the same `range (i + 2)` budget.  The
resulting `selfLow_jet_quad` has no `R₀` and no ball hypothesis at all. -/

set_option linter.unusedVariables false in
/-- **Marked window of the symmetrized first-order Ricci coefficient.**

The marked sibling of `ricciGoodCap`.  Both arms of `ricciGoodLow` are twice
marked — `ricciAAArm` by `ricciAAMark` and `ricciDALow` by `ricciDAMark` — and the
input-slot symmetrization is a product with the fixed slot-swap field, so the
mark count survives it. -/
private theorem ricciGoodMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ 1),
        HasMarkWin (I := I) (M := M) g₀ P
          (ricciGoodLow (I := I) (M := M) g₀ g₁ P) 2 K := by
  classical
  obtain ⟨KAA, hKAA_nn, hAA⟩ := ricciAAMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨KDA, hKDA_nn, hDA⟩ := ricciDAMark (I := I) (M := M) g₀ hδ₀
  choose SSw hSSw_nn hSSw using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i (ccSlotSwapField (I := I) (M := M) g₀)))
  set KL : ℕ → ℝ := fun i => 2 * KAA i + 2 * KDA i with hKL_def
  have hKL_nn : ∀ i, 0 ≤ KL i := fun i => by
    have := hKAA_nn i; have := hKDA_nn i; simp only [hKL_def]; linarith
  refine ⟨fun i => (1 / 2 : ℝ) ^ 2 * (2 * KL i + 2 * foldConst (E := E) 0 0 KL SSw i),
    fun i => by
      have h1 := hKL_nn i
      have h2 := foldConst_nn (E := E) (u := 0) (v := 0) hKL_nn hSSw_nn i
      have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 2 := by positivity
      nlinarith [h1, h2], ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0
  have hLow : HasMarkWin (I := I) (M := M) g₀ P
      (ricciAAArm (I := I) (M := M) g₀ g₁ +
        ricciDALow (I := I) (M := M) g₀ g₁ P) 2 KL :=
    mkAdd (I := I) (M := M) g₀ P (hAA g₁ P htie hδ_le hδ0 hδ)
      (hDA g₁ P htie hδ_le hδ0 hδ hP0)
  have hSw : HasMarkWin (I := I) (M := M) g₀ P
      (ccSlotSwapField (I := I) (M := M) g₀) 0 SSw :=
    mkOfBnd (I := I) (M := M) g₀ P _ hSSw_nn (fun i x => hSSw i x)
  have happ := mkApp (I := I) (M := M) g₀ P
    (ricciAAArm (I := I) (M := M) g₀ g₁ + ricciDALow (I := I) (M := M) g₀ g₁ P)
    (ccSlotSwapField (I := I) (M := M) g₀) hKL_nn hSSw_nn hLow hSw
  exact mkSmul (I := I) (M := M) g₀ P (1 / 2 : ℝ)
    (mkAdd (I := I) (M := M) g₀ P hLow happ)

set_option linter.unusedSectionVars false in
/-- Summing a per-order tame bound over `range (i + 1)`: the constants add and
the single power of the `H³` factor is preserved. -/
private lemma jetFold (g : SmoothRiemannianMetric I M) {r c : ℕ}
    (X : SmoothCcTensor g r c) (i : ℕ) (A B : ℕ → ℝ) {u v : ℝ}
    (hstep : ∀ q ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g r c q X‖ ^ 2 ≤ (A q + B q * u) * v) :
    lowJetSq (I := I) (M := M) g i X ≤
      ((∑ q ∈ Finset.range (i + 1), A q) +
        (∑ q ∈ Finset.range (i + 1), B q) * u) * v := by
  unfold lowJetSq
  refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
  have hterm : ∀ q : ℕ, (A q + B q * u) * v = A q * v + B q * (u * v) :=
    fun q => by ring
  simp only [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

set_option linter.unusedSectionVars false in
/-- **From a per-order tame bound in the perturbation to a jet bound in the
state.**

Both the `H³` factor and the `range (q + 2)` budget are monotone along
`‖∇ᵏP‖ ≤ ‖∇ᵏT‖`, which is what `P = s·T` with `s ∈ [0,1]` supplies; the constants
then add over `q ≤ i` by `jetFold`, and the single power of the `H³` factor is
preserved. -/
private lemma jetTrans (g : SmoothRiemannianMetric I M) {r c : ℕ}
    (X : SmoothCcTensor g r c) (i : ℕ) (A B : ℕ → ℝ)
    (hA : ∀ q, 0 ≤ A q) (hB : ∀ q, 0 ≤ B q)
    (P T : SmoothCcTensor g 0 2)
    (hPk : ∀ k : ℕ, ‖iteratedCovGrad (I := I) g 0 2 k P‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g 0 2 k T‖ ^ 2)
    (hX : ∀ q : ℕ, ‖iteratedCovGrad (I := I) g r c q X‖ ^ 2 ≤
      (A q + B q * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 (1 + j) P‖ ^ 2) *
        (1 + ∑ j ∈ Finset.range (q + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2)) :
    lowJetSq (I := I) (M := M) g i X ≤
      ((∑ q ∈ Finset.range (i + 1), A q) +
        (∑ q ∈ Finset.range (i + 1), B q) *
          ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  refine jetFold (I := I) (M := M) g X i A B (fun q hq => ?_)
  have hqi : q ≤ i := by have := Finset.mem_range.mp hq; omega
  refine le_trans (hX q) ?_
  have hHP_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hHT_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hH3 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) P‖ ^ 2) ≤
      ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2 :=
    Finset.sum_le_sum (fun j _ => hPk (1 + j))
  have hbud : (1 + ∑ j ∈ Finset.range (q + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤
      1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := by
    have h1 : (∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤
        ∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
      Finset.sum_le_sum (fun j _ => hPk j)
    have h2 : (∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤
        ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) (fun _ _ _ => sq_nonneg _)
    linarith
  have hbud_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (q + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2 := by
    have : (0 : ℝ) ≤ ∑ j ∈ Finset.range (q + 2),
        ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    linarith
  refine mul_le_mul (by nlinarith [hB q]) hbud hbud_nn ?_
  nlinarith [hA q, hB q, hHT_nn]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Tame `L²` jet bound of the symmetrized first-order Ricci coefficient.**

`ricciGoodMark` integrated by `markJet`; the sibling of `ricciAAJet` for the
whole `ricciGoodLow` arm. -/
private theorem ricciGoodJet (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciGoodLow (I := I) (M := M) g₀ g₁ P)‖ ^ 2 ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨KG, hKG_nn, wG⟩ := ricciGoodMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨K0', hK0'_nn, hjet⟩ := markJet (I := I) (M := M) g₀
  obtain ⟨cg, hcg_nn, hcg⟩ := gradCapLin (I := I) (M := M) hDim g₀
  refine ⟨fun i => KG i * K0' i, fun i => KG i * K0' i * cg,
    fun i => mul_nonneg (hKG_nn i) (hK0'_nn i),
    fun i => mul_nonneg (mul_nonneg (hKG_nn i) (hK0'_nn i)) hcg_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 i
  set H3 : ℝ := ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2 with hH3_def
  have hH3_nn : 0 ≤ H3 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  set Λ₁ : ℝ := Real.sqrt (cg * H3) with hΛ₁_def
  have hΛ₁0 : 0 ≤ Λ₁ := Real.sqrt_nonneg _
  have hΛ₁sq : Λ₁ ^ 2 = cg * H3 := Real.sq_sqrt (mul_nonneg hcg_nn hH3_nn)
  have hcap : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2 := by
    intro x
    rw [hΛ₁sq]
    exact hcg P x
  have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
      (P.toSection x) ≤ (1 : ℝ) ^ 2 := by
    intro x; rw [one_pow]; exact hP0 x
  have hP0g : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ 1 := by
    intro x; simpa [gridBase] using hP0 x
  have hres := hjet P (Λ₀ := 1) zero_le_one (le_refl _) hΛ₁0 hsup hcap
    (ricciGoodLow (I := I) (M := M) g₀ g₁ P) hKG_nn
    (wG g₁ P htie hδ_le hδ0 hδ hP0g) i
  refine hres.trans (le_of_eq ?_)
  rw [hΛ₁sq]
  ring

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **The all-order jet window of the zero-order path integrand, at quadratic
cost and with no ball.**

```
lowJetSq i (rhsSelfLow g g T …) ≤
  (K₀ i + K₂ i · ‖T‖²_{H³}) · (1 + ∑_{j < i+2} ‖∇ʲT‖²)
```

with `K₀, K₂` chosen before the state — background metric and order only — and
`‖T‖²_{H³}` spelled `∑_{j<3} ‖∇^{1+j}T‖²` (`gradCapLin`'s convention).  Compare
`selfLow_jet`, which buys the same left-hand side with an `H^{a+2}` ball and a
constant of `Λ`-degree growing with `i`.

The six per-arm tame jets it consumes are `TameArmJets.lean`'s `ricciAAMark`,
`SelfLowArmCaps.lean`'s `ricciDAMark` (through `ricciGoodMark`) and `lieCovJet`,
and `TameLieCorrJets.lean`'s `lc0VBJet`, `lc0AMixJet`, `lc0RiemJet`.  The δ-anchor
`|P|²_∞ ≤ 1` that each of them spends is supplied by `hDim` together with
`δ ≤ 1/3`: `(dim · 1/3)² = 1` in dimension three.

Class-3 residuals of the marked integration flow through the single declared
frontier `gridIntHigh`; nothing else in the chain is conditional. -/
theorem selfLow_jet_quad
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
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
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  have h30 : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have h31 : (1 / 3 : ℝ) < 1 := by norm_num
  obtain ⟨A1, B1, hA1_nn, hB1_nn, w1⟩ := ricciGoodJet (I := I) (M := M) hDim g h31
  obtain ⟨A2, B2, hA2_nn, hB2_nn, w2⟩ := lieCovJet (I := I) (M := M) hDim g h31
  obtain ⟨A3, B3, hA3_nn, hB3_nn, w3⟩ := lc0VBJet (I := I) (M := M) hDim g h31
  obtain ⟨A4, B4, hA4_nn, hB4_nn, w4⟩ := lc0AMixJet (I := I) (M := M) hDim g h31
  obtain ⟨A5, hA5_nn, w5⟩ := lc0RiemJet (I := I) (M := M) g h31
  refine ⟨fun i => 64 * (∑ q ∈ Finset.range (i + 1), A1 q) +
      16 * (∑ q ∈ Finset.range (i + 1), A2 q) +
      8 * (∑ q ∈ Finset.range (i + 1), A3 q) +
      4 * (∑ q ∈ Finset.range (i + 1), A4 q) +
      2 * (∑ q ∈ Finset.range (i + 1), A5 q),
    fun i => 64 * (∑ q ∈ Finset.range (i + 1), B1 q) +
      16 * (∑ q ∈ Finset.range (i + 1), B2 q) +
      8 * (∑ q ∈ Finset.range (i + 1), B3 q) +
      4 * (∑ q ∈ Finset.range (i + 1), B4 q),
    fun i => by
      have s1 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), A1 q :=
        Finset.sum_nonneg (fun q _ => hA1_nn q)
      have s2 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), A2 q :=
        Finset.sum_nonneg (fun q _ => hA2_nn q)
      have s3 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), A3 q :=
        Finset.sum_nonneg (fun q _ => hA3_nn q)
      have s4 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), A4 q :=
        Finset.sum_nonneg (fun q _ => hA4_nn q)
      have s5 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), A5 q :=
        Finset.sum_nonneg (fun q _ => hA5_nn q)
      linarith,
    fun i => by
      have s1 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), B1 q :=
        Finset.sum_nonneg (fun q _ => hB1_nn q)
      have s2 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), B2 q :=
        Finset.sum_nonneg (fun q _ => hB2_nn q)
      have s3 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), B3 q :=
        Finset.sum_nonneg (fun q _ => hB3_nn q)
      have s4 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), B4 q :=
        Finset.sum_nonneg (fun q _ => hB4_nn q)
      linarith, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le h31
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hTsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (T.toSection x) ≤ ((Module.finrank ℝ E : ℝ) * (1 / 3)) ^ 2 := by
    intro x
    have h := rfns_symmS_zero_le_fibreSmall
      (I := I) (M := M) g h30 T hδ_le hδ0 hδg x
    rwa [symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g T hT] at h
  obtain ⟨⟨δ', hδ'0, hδ'_le, hP⟩, htie, hPsup, hPjet⟩ :=
    pathPert_rad (I := I) (M := M) g T hδ0 hδ_le hδ_lt hδg hδZ hTsup hs
  set gm : SmoothRiemannianMetric I M := realizedFam (I := I) g T 0 hδg hδZ s with hgm_def
  set P : SmoothCcTensor g 0 2 := convexPerturbation (I := I) g T 0 s with hP_def
  have hPeq : P = s • T := by
    rw [hP_def, convexPerturbation, smul_zero, zero_add]
  have hone : ((Module.finrank ℝ E : ℝ) * (1 / 3)) ^ 2 = 1 := by
    rw [hDim]; norm_num
  have hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (P.toSection x) ≤ 1 := by
    intro x
    have h := hPsup x
    rwa [hone] at h
  -- the perturbation's jets are dominated by the state's, order by order
  have hPk : ∀ k : ℕ, ‖iteratedCovGrad (I := I) g 0 2 k P‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g 0 2 k T‖ ^ 2 := by
    intro k
    rw [hPeq, iteratedCovGrad_smul_real (I := I) (M := M) g 0 2 k s T, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    have hsq : s ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g 0 2 k T‖, hsq]
  set H3 : ℝ := ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2 with hH3_def
  set JS : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 with hJS_def
  -- the five summands
  have e1 : lowJetSq (I := I) (M := M) g i
      ((-2 : ℝ) • ricciGoodLow (I := I) (M := M) g gm P) ≤
      4 * (((∑ q ∈ Finset.range (i + 1), A1 q) +
        (∑ q ∈ Finset.range (i + 1), B1 q) * H3) * JS) := by
    rw [opJetSmul (I := I) (M := M) g i (-2 : ℝ)
      (ricciGoodLow (I := I) (M := M) g gm P)]
    have h := jetTrans (I := I) (M := M) g
      (ricciGoodLow (I := I) (M := M) g gm P) i A1 B1 hA1_nn hB1_nn P T hPk
      (fun q => w1 gm P htie hδ'_le hδ'0 hP hP0 q)
    have hnn : (0 : ℝ) ≤ (4 : ℝ) := by norm_num
    nlinarith [h, hnn]
  have e2 : lowJetSq (I := I) (M := M) g i
      (deTurckLieCovDerivArmField (I := I) (M := M) g gm g -
        edgeLiePairFam (I := I) (M := M) g T hδg hδZ lieRefoldQ lieRefoldEps s) ≤
      ((∑ q ∈ Finset.range (i + 1), A2 q) +
        (∑ q ∈ Finset.range (i + 1), B2 q) * H3) * JS :=
    jetTrans (I := I) (M := M) g _ i A2 B2 hA2_nn hB2_nn P T hPk
      (fun q => w2 T hT hδ_le hδ0 hδg hδZ hs hP0 q)
  have e3 : lowJetSq (I := I) (M := M) g i (lc0VB (I := I) (M := M) g gm) ≤
      ((∑ q ∈ Finset.range (i + 1), A3 q) +
        (∑ q ∈ Finset.range (i + 1), B3 q) * H3) * JS :=
    jetTrans (I := I) (M := M) g _ i A3 B3 hA3_nn hB3_nn P T hPk
      (fun q => w3 gm P htie hδ'_le hδ'0 hP hP0 q)
  have e4 : lowJetSq (I := I) (M := M) g i (lc0AMix (I := I) (M := M) g gm g) ≤
      ((∑ q ∈ Finset.range (i + 1), A4 q) +
        (∑ q ∈ Finset.range (i + 1), B4 q) * H3) * JS :=
    jetTrans (I := I) (M := M) g _ i A4 B4 hA4_nn hB4_nn P T hPk
      (fun q => w4 gm P htie hδ'_le hδ'0 hP hP0 q)
  have e5 : lowJetSq (I := I) (M := M) g i (lc0Riem (I := I) (M := M) g gm) ≤
      ((∑ q ∈ Finset.range (i + 1), A5 q) +
        (∑ q ∈ Finset.range (i + 1), (0 : ℝ)) * H3) * JS := by
    refine jetTrans (I := I) (M := M) g _ i A5 (fun _ => 0) hA5_nn
      (fun _ => le_refl 0) P T hPk (fun q => ?_)
    have h := w5 gm P htie hδ'_le hδ'0 hP hP0 q
    refine h.trans (le_of_eq ?_)
    ring
  -- assemble along `selfLow_split`
  have hrw : rhsSelfLow (I := I) (M := M) g g T hδg hδZ s =
      ((((-2 : ℝ) • ricciGoodLow (I := I) (M := M) g gm P +
        (deTurckLieCovDerivArmField (I := I) (M := M) g gm g -
          edgeLiePairFam (I := I) (M := M) g T hδg hδZ lieRefoldQ lieRefoldEps s)) +
        lc0VB (I := I) (M := M) g gm) +
        lc0AMix (I := I) (M := M) g gm g) +
        lc0Riem (I := I) (M := M) g gm := by
    rw [selfLow_split (I := I) (M := M) g T hT hδ_lt hδg hδZ hs, hPeq]
  rw [hrw]
  have j4 := opJetAdd (I := I) (M := M) g i
    ((((-2 : ℝ) • ricciGoodLow (I := I) (M := M) g gm P +
      (deTurckLieCovDerivArmField (I := I) (M := M) g gm g -
        edgeLiePairFam (I := I) (M := M) g T hδg hδZ lieRefoldQ lieRefoldEps s)) +
      lc0VB (I := I) (M := M) g gm) +
      lc0AMix (I := I) (M := M) g gm g)
    (lc0Riem (I := I) (M := M) g gm)
  have j3 := opJetAdd (I := I) (M := M) g i
    (((-2 : ℝ) • ricciGoodLow (I := I) (M := M) g gm P +
      (deTurckLieCovDerivArmField (I := I) (M := M) g gm g -
        edgeLiePairFam (I := I) (M := M) g T hδg hδZ lieRefoldQ lieRefoldEps s)) +
      lc0VB (I := I) (M := M) g gm)
    (lc0AMix (I := I) (M := M) g gm g)
  have j2 := opJetAdd (I := I) (M := M) g i
    ((-2 : ℝ) • ricciGoodLow (I := I) (M := M) g gm P +
      (deTurckLieCovDerivArmField (I := I) (M := M) g gm g -
        edgeLiePairFam (I := I) (M := M) g T hδg hδZ lieRefoldQ lieRefoldEps s))
    (lc0VB (I := I) (M := M) g gm)
  have j1 := opJetAdd (I := I) (M := M) g i
    ((-2 : ℝ) • ricciGoodLow (I := I) (M := M) g gm P)
    (deTurckLieCovDerivArmField (I := I) (M := M) g gm g -
      edgeLiePairFam (I := I) (M := M) g T hδg hδZ lieRefoldQ lieRefoldEps s)
  have hfin : (64 * (∑ q ∈ Finset.range (i + 1), A1 q) +
      16 * (∑ q ∈ Finset.range (i + 1), A2 q) +
      8 * (∑ q ∈ Finset.range (i + 1), A3 q) +
      4 * (∑ q ∈ Finset.range (i + 1), A4 q) +
      2 * (∑ q ∈ Finset.range (i + 1), A5 q) +
      (64 * (∑ q ∈ Finset.range (i + 1), B1 q) +
        16 * (∑ q ∈ Finset.range (i + 1), B2 q) +
        8 * (∑ q ∈ Finset.range (i + 1), B3 q) +
        4 * (∑ q ∈ Finset.range (i + 1), B4 q)) * H3) * JS =
      16 * (4 * (((∑ q ∈ Finset.range (i + 1), A1 q) +
          (∑ q ∈ Finset.range (i + 1), B1 q) * H3) * JS)) +
        16 * (((∑ q ∈ Finset.range (i + 1), A2 q) +
          (∑ q ∈ Finset.range (i + 1), B2 q) * H3) * JS) +
        8 * (((∑ q ∈ Finset.range (i + 1), A3 q) +
          (∑ q ∈ Finset.range (i + 1), B3 q) * H3) * JS) +
        4 * (((∑ q ∈ Finset.range (i + 1), A4 q) +
          (∑ q ∈ Finset.range (i + 1), B4 q) * H3) * JS) +
        2 * (((∑ q ∈ Finset.range (i + 1), A5 q) +
          (∑ q ∈ Finset.range (i + 1), (0 : ℝ)) * H3) * JS) := by
    simp only [Finset.sum_const_zero]
    ring
  rw [hfin]
  linarith [j1, j2, j3, j4, e1, e2, e3, e4, e5]

end Integrand

section Towers

/-- **The all-order `L²` jet tower of `A.C1`, with no a-priori ball.**

`‖∇ⁱ (lowBaseData g g T …).C1‖² ≤ Kc i * (1 + ∑_{j < i+2} ‖∇ʲ T‖²)`,
with `Kc` chosen before the state — background metric and order only.

This is the ball-free form of `c1_jet_tower`.  No quadratic correction term is
needed here (unlike `c0_jet_tower_quad`): the `H^{a+2}` ball binder of
`c1_jet_tower` was **vestigial**, because the whole first-order integrand
window `low1Ker_jet` is driven by `hδ_le : δ ≤ 1/3` alone.  `c1_jet_tower` is
now the ball-carrying wrapper of this statement. -/
theorem c1JetTowerQ
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
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
          ‖iteratedCovGrad (I := I) g 3 2 i
              (lowBaseData (I := I) (M := M) g g T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).C1‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨Kk, hKk_nn, hker⟩ := low1Ker_jet (I := I) (M := M) hDim g
  refine ⟨Kk, hKk_nn, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i
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
/-- **The all-order `L²` jet tower of the low-base first-order coefficient
`A.C1`.**

`‖∇ⁱ (lowBaseData g g T …).C1‖² ≤ Kc i * (1 + ∑_{j < i+2} ‖∇ʲ T‖²)`.

This is hypothesis (b) of the order-generic operator-norm engine for the
first-order arm, and it is the `C1` input of `a1_ladder`.  Statement shape is
`c2_jet_tower`'s with valence `4 2` replaced by `3 2`: constants before the
state, `range (i + 2)` budget, `δ ≤ 1/3` the only smallness input.

The `H^{a+2}` ball hypothesis is inert — the statement quantifies over an
arbitrary `a` — and is kept only because `a1_ladder` and the operator-norm
engine carry it.  The ball-free content is `c1JetTowerQ`, of which this is the
compatibility wrapper. -/
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
  obtain ⟨Kc, hKc_nn, h⟩ := c1JetTowerQ (I := I) (M := M) hDim g
  refine ⟨Kc, hKc_nn, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ _ i
  exact h T hT hδ0 hδ_le hδg hδZ i

set_option linter.unusedVariables false in
/-- **The all-order `L²` jet tower of the low-base zeroth-order coefficient
`A.C0`.**

`‖∇ⁱ (lowBaseData g g T …).C0‖² ≤ Kc i * (1 + ∑_{j < i+2} ‖∇ʲ T‖²)`.

Statement shape is `c2_jet_tower`'s with valence `4 2` replaced by `2 2`.  The
fixed curvature summand `phiMetCurvCoeff g g g` of `A.C0` is state-free, so it
contributes only to the constant.

Unlike `c1_jet_tower`, the `H^{a+2}` ball hypothesis here is **live**: it is
consumed by the integrand window `selfLow_jet`, whose quadratic-in-`∇P`
summands are unbounded on the ball-free class.  The gate `1 ≤ a` is inherited
from that window (dimension three: `H³ ⊂ C¹`) and is below `a2_ladder`'s
`3 ≤ a` bottom. -/
theorem c0_jet_tower
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (a : ℕ) (ha : 1 ≤ a)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
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
  obtain ⟨Kk, hKk_nn, hker⟩ := selfLow_jet (I := I) (M := M) hDim g a ha hR₀
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
        hker T hT hδ0 hδ_le hδg hδZ hball i s hs)
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

set_option linter.unusedVariables false in
/-- **The all-order `L²` jet tower of `A.C0` at quadratic cost, with no ball.**

```
‖∇ⁱ (lowBaseData g g T …).C0‖² ≤
  (K0 i + K2 i · ‖T‖²_{H³}) · (1 + ∑_{j < i+2} ‖∇ʲT‖²)
```

with `K0, K2` chosen before the state — background metric and order only — and
`‖T‖²_{H³}` spelled `∑_{j<3}‖∇^{1+j}T‖²` (`gradCapLin`'s convention).

This is `c0_jet_tower`'s sibling with the `H^{a+2}` ball hypothesis **replaced**
by an explicit quadratic dependence on the state's own `H³` norm.  The ball
entered `c0_jet_tower` only through the integrand window `selfLow_jet`; the
ball-free `selfLow_jet_quad` buys the same left-hand side, so the passage
through the radial parameter integral (`path_jetL2_le`) and the treatment of
the state-free curvature summand `phiMetCurvCoeff g g g` — which still
contributes to `K0` alone — are unchanged.  This is the shape the low-mass
consumer reads: no `a`, no `R₀`, no `Λ`-degree growth in `i`. -/
theorem c0_jet_tower_quad
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
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
          ‖iteratedCovGrad (I := I) g 2 2 i
              (lowBaseData (I := I) (M := M) g g T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).C0‖ ^ 2 ≤
            (K0 i + K2 i * ∑ j ∈ Finset.range 3,
                ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
              (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨Kk0, Kk2, hKk0_nn, hKk2_nn, hker⟩ :=
    selfLow_jet_quad (I := I) (M := M) hDim g
  refine ⟨fun i => 2 * (Kk0 i +
      lowJetSq (I := I) (M := M) g i (-phiMetCurvCoeff (I := I) g g g)),
    fun i => 2 * Kk2 i,
    fun i => by
      have := jetNn (I := I) (M := M) (m := i) g
        (-phiMetCurvCoeff (I := I) g g g)
      have := hKk0_nn i
      linarith,
    fun i => by have := hKk2_nn i; linarith, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hH3 : (0 : ℝ) ≤ ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  set Λ : ℝ := (Kk0 i + Kk2 i * ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
    (1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hΛdef
  have hΛ : 0 ≤ Λ := by
    rw [hΛdef]
    exact mul_nonneg (add_nonneg (hKk0_nn i) (mul_nonneg (hKk2_nn i) hH3))
      (by linarith)
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
      (2 * (Kk0 i + lowJetSq (I := I) (M := M) g i
            (-phiMetCurvCoeff (I := I) g g g)) +
          2 * Kk2 i * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
    have hsplit := jetSub (I := I) (M := M) g i
      (selfLowInt (I := I) (M := M) g g T hδ_lt hδg hδZ)
      (-phiMetCurvCoeff (I := I) g g g)
    rw [sub_neg_eq_add] at hsplit
    rw [c0_eq (I := I) (M := M) g g T hδ_lt hδg hδZ]
    refine hsplit.trans ?_
    have hstep : 2 * (Λ + lowJetSq (I := I) (M := M) g i
          (-phiMetCurvCoeff (I := I) g g g)) ≤
        (2 * (Kk0 i + lowJetSq (I := I) (M := M) g i
              (-phiMetCurvCoeff (I := I) g g g)) +
            2 * Kk2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
          (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
      rw [hΛdef]
      nlinarith [mul_nonneg hfix hsum, hfix, hsum, hH3,
        hKk0_nn i, hKk2_nn i, mul_nonneg (hKk2_nn i) hH3]
    linarith only [hint, hstep]
  refine le_trans ?_ hjet
  unfold lowJetSq
  exact Finset.single_le_sum
    (fun q _ => sq_nonneg ‖iteratedCovGrad (I := I) g 2 2 q
      (lowBaseData (I := I) (M := M) g g T hδ_lt hδg hδZ).C0‖)
    (Finset.mem_range.mpr (Nat.lt_succ_self i))

end Towers

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
