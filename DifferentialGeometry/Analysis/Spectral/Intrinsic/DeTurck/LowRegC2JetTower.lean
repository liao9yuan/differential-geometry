import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegOpJetWindows

/-!
# The all-order jet tower of the low-base second-order coefficient

The complete zero-based second-order coefficient

`A.C2 = rhsRefoldTopInt + selfTopInt - deTurckPhiMetTotal`

is a *path integral* over the radial segment joining the background carrier to
the state, so its `i`-th covariant jet is not accessible by algebra.  This
module supplies the two layers that turn a per-parameter jet bound into an
all-order jet tower for `A.C2`:

* `path_add_sub_jet` — the order-generic differentiation-under-the-integral
  layer.  It is the covariant-jet sibling of `path_add_sub_cap`
  (`LowRegPathSplit.lean`, fibre-pointwise) and the order-generic form of the
  fixed-order `h2` step used inside `c2_h2_small`: a uniform covariant `L²` jet
  bound of order `n` for the *cancellation-preserving* integrand passes to the
  sum of the two integrated pieces minus the fixed coefficient, with the same
  constant, at every order `n`.
* `topKer_jet` — the estimate: the per-order jet tower of the integrand
  itself, uniform in the path parameter, on the ball-free Moser route.

Both are sorry-free, so `c2_jet_tower` and `a2_ladder` are unconditional.
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

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- A constant coefficient family is jointly smooth along the realized
segment. -/
private theorem armConst
    (g : SmoothRiemannianMetric I M) {r : ℕ}
    (A : SmoothCcTensor g r 2) {δ δ' : ℝ} :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g r
      (fun _ => A) (δ := δ) (δ' := δ') :=
  (A.toSection.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)

set_option maxHeartbeats 800000 in
/-- **Differentiation under the path integral, at every order.**

If the cancellation-preserving integrand `t ↦ Φ t + Ψ t - C` has covariant
`L²` jet of order `n` bounded by `Λ` uniformly for `t ∈ [0,1]`, then so does
`∫Φ + ∫Ψ - C`, with the *same* constant `Λ` and at *every* order `n`.

This is the order-generic form of the fixed-order step that `c2_h2_small`
carries out at `n = 2`, and the covariant-jet sibling of the fibre-pointwise
`path_add_sub_cap`.  Unlike those two it does not take the joint smoothness of
the combined integrand as an extra input: it is assembled from `hΦ` and `hΨ`
by `threeArmJoint_add`/`threeArmJoint_sub`. -/
theorem path_add_sub_jet
    (g : SmoothRiemannianMetric I M) (r n : ℕ)
    {δ δ' : ℝ}
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ'))
    (Φ Ψ : ℝ → SmoothCcTensor g r 2) (C : SmoothCcTensor g r 2)
    (hΦ : linearizedRicciThreeArmHjoint (I := I) (M := M) g r Φ
      (δ := δ) (δ' := δ'))
    (hΨ : linearizedRicciThreeArmHjoint (I := I) (M := M) g r Ψ
      (δ := δ) (δ' := δ'))
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hcap : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      lowJetSq (I := I) (M := M) g n (Φ t + Ψ t - C) ≤ Λ) :
    lowJetSq (I := I) (M := M) g n
        (pathIntegralCoeffField (I := I) (M := M) g r 2 Φ
              (realizedSmallSet (δ := δ) (δ' := δ'))
              realizedSmallSet_isOpen hSI hΦ +
          pathIntegralCoeffField (I := I) (M := M) g r 2 Ψ
              (realizedSmallSet (δ := δ) (δ' := δ'))
              realizedSmallSet_isOpen hSI hΨ -
          C) ≤ Λ := by
  classical
  have hK : linearizedRicciThreeArmHjoint (I := I) (M := M) g r
      (fun t => Φ t + Ψ t - C) (δ := δ) (δ' := δ') :=
    threeArmJoint_sub (I := I) (M := M) g _ _
      (threeArmJoint_add (I := I) (M := M) g _ _ hΦ hΨ)
      (armConst (I := I) (M := M) g C)
  have heq :
      pathIntegralCoeffField (I := I) (M := M) g r 2 Φ
            (realizedSmallSet (δ := δ) (δ' := δ'))
            realizedSmallSet_isOpen hSI hΦ +
          pathIntegralCoeffField (I := I) (M := M) g r 2 Ψ
            (realizedSmallSet (δ := δ) (δ' := δ'))
            realizedSmallSet_isOpen hSI hΨ -
          C =
        pathIntegralCoeffField (I := I) (M := M) g r 2
          (fun t => Φ t + Ψ t - C)
          (realizedSmallSet (δ := δ) (δ' := δ'))
          realizedSmallSet_isOpen hSI hK := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro y
    apply TensorRSSpace.toModel_injective
    have hcΦ := jointContMDiff_toModel_continuous_slice
      (I := I) g r 2 Φ (realizedSmallSet (δ := δ) (δ' := δ')) hΦ y
    have hcΨ := jointContMDiff_toModel_continuous_slice
      (I := I) g r 2 Ψ (realizedSmallSet (δ := δ) (δ' := δ')) hΨ y
    have hIΦ : IntervalIntegrable (fun t : ℝ =>
        TensorRSSpace.toModel ((Φ t).toSection y))
        MeasureTheory.volume 0 1 :=
      (hcΦ.mono hSI).intervalIntegrable
    have hIΨ : IntervalIntegrable (fun t : ℝ =>
        TensorRSSpace.toModel ((Ψ t).toSection y))
        MeasureTheory.volume 0 1 :=
      (hcΨ.mono hSI).intervalIntegrable
    simp only [pathIntegralCoeffField_toModel, SmoothCcTensor.toSection_add,
      SmoothCcTensor.toSection_sub, ContMDiffSection.coe_add,
      ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply,
      TensorRSSpace.toModel_add, TensorRSSpace.toModel_sub]
    rw [intervalIntegral.integral_sub (hIΦ.add hIΨ) intervalIntegrable_const,
      intervalIntegral.integral_add hIΦ hIΨ, intervalIntegral.integral_const]
    norm_num
  have hsq : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hΛ
  have hcap' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∑ q ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g r 2 q (Φ t + Ψ t - C)‖ ^ 2) ≤
        Real.sqrt Λ ^ 2 := by
    intro t ht
    rw [hsq]
    exact hcap t ht
  have hmain := path_jetL2_le (I := I) (M := M) g r 2 n
    (fun t => Φ t + Ψ t - C) (realizedSmallSet (δ := δ) (δ' := δ'))
    realizedSmallSet_isOpen hSI hK (Real.sqrt_nonneg Λ) hcap'
  rw [heq]
  exact le_of_le_of_eq hmain hsq

set_option linter.unusedVariables false in
/-- **The per-order jet tower of the complete top path integrand, uniform in
the path parameter.**

For every order `i` and every `s ∈ [0,1]`, the covariant `L²` jet of order `i`
of the integrand

`rhsRefoldTop g g T s + rhsSelfTop g T s - deTurckPhiMetTotal g g g`

is controlled by the state's own jets through order `i + 1`, with a constant
depending only on the background metric and `i` — in particular on neither the
state nor the path parameter.

**Why no a-priori ball appears.**  `c2_jet_tower` — the consumer — is stated at
an *arbitrary* order `a`, so the `H^{a+2}` ball it carries gives no usable
low-order control at `a = 0`; the ball is vestigial there.  The only smallness
input used here is `hδ_le : δ ≤ 1/3`, which through `hδg` bounds `T` in `L^∞`.
That is exactly what the Moser pairing consumes: `appRS_hn_sup`
(`Tensor/Estimates/AppCcRSJetMul.lean`) multiplies each arm's `L^∞` bound by
the *other* arm's full `L²` jet, so a product of affine jet windows is again
affine, with no Sobolev ball and no order gate.

**Route.**  `topKernel_eq` expands the integrand into `lieRefold2 g T s`, the
metric deviation `Φmet(gm) - Φmet(g)`, and `(-2s) • ricciTop g gm T`, where
`gm = realizedFam g T 0 s` is the radial metric.  Along that path the
perturbation is `s • T`, which carries the *same* fibre bound `δ` and jets
dominated by `T`'s (`pathPert_rad`); the three summands are then the
all-order Moser windows `moserWin_lieRef2`, `moserWin_phiDev` and
`moserWin_ricciTop` of `LowRegOpJetWindows.lean`, combined by `moserWin_add`
and `moserWin_smul`.  Every window has derivative offset `w = 0`, i.e. order
`i` on the left costs order `i` of `T`, so the `range (i + 2)` budget here has
a full order of slack.

The two scalars cost nothing: `|-2s| ≤ 2` and `s ≤ 1` on `[0,1]`, absorbed by
`moserWin_mono`, which is why no constant below mentions `s`.

The existing all-order `lieRefold2` producer
`exists_deTurckLieCovDerivRefoldC2Family_cap_l2JetWindow`
(`RicciLinearization/RiemannCoefficientPalatiniRefold.lean:18865`) is
deliberately *not* used: it gates on `2 * finrank ℝ E + 10 ≤ a` (dimension
three: `a ≥ 16`), which would undo `a2_ladder`'s `3 ≤ a` bottom, and its data
hypothesis is a pointwise jet window rather than an `L^∞` bound.  The Moser
route reaches the same conclusion ball-free and gate-free. -/
theorem topKer_jet
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
            (rhsRefoldTop (I := I) (M := M) g g T hδg hδZ s +
              LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hδg hδZ s -
              deTurckPhiMetTotal (I := I) (M := M) g g g) ≤
          Kk i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  have h30 : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have h31 : (1 / 3 : ℝ) < 1 := by norm_num
  obtain ⟨AL, SL, hL⟩ := moserWin_lieRef2 (I := I) (M := M) g (δ₀ := 1 / 3) h30 h31
  obtain ⟨AP, SP, hP⟩ :=
    moserWin_phiDev (I := I) (M := M) g g (δ₀ := 1 / 3) h30 h31
  obtain ⟨AR, SR, hR⟩ :=
    moserWin_ricciTop (I := I) (M := M) g (δ₀ := 1 / 3) h30 h31
  refine ⟨fun i => |2 * (2 * (AL i + AP i) + 4 * AR i)|,
    fun i => abs_nonneg _, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le h31
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  -- the state is its own `L^∞` witness: symmetry identifies it with `symmS g T`
  have hTsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (T.toSection x) ≤ ((Module.finrank ℝ E : ℝ) * (1 / 3)) ^ 2 := by
    intro x
    have h := rfns_symmS_zero_le_fibreSmall
      (I := I) (M := M) g h30 T hδ_le hδ0 hδg x
    rwa [symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g T hT] at h
  have hpert := pathPert_rad (I := I) (M := M) g T hδ0 hδ_le hδ_lt hδg hδZ hTsup hs
  -- the three summands, each an affine window with `s`-free constants
  have hLw := hL T hTsup hδ0 hδ_le hδ_lt hδg hδZ hs
  have hPw := hP T (realizedFam (I := I) g T 0 hδg hδZ s)
    (convexPerturbation (I := I) g T 0 s) hpert
  have hRw := hR T hTsup (realizedFam (I := I) g T 0 hδg hδZ s)
    (convexPerturbation (I := I) g T 0 s) hpert
  have hAR : ∀ n, 0 ≤ AR n := fun n => moserWin_nnA (I := I) (M := M) hRw n
  have hSR : 0 ≤ SR := hRw.1
  have hRs : IsMoserWin (I := I) (M := M) g T (fun n => 4 * AR n) (2 * SR)
      ((-2 * s : ℝ) • LowBaseInternal.ricciTop (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδg hδZ s) T) := by
    refine moserWin_mono (I := I) (M := M)
      (moserWin_smul (I := I) (M := M) (-2 * s : ℝ) hRw) (fun n => ?_) ?_
    · have hexp : (-2 * s : ℝ) ^ 2 = 4 * s ^ 2 := by ring
      rw [hexp]
      nlinarith [mul_nonneg (by nlinarith : (0 : ℝ) ≤ 1 - s ^ 2) (hAR n)]
    · rw [abs_mul, abs_of_nonneg hs0, show |(-2 : ℝ)| = 2 from by norm_num]
      nlinarith [hSR]
  have hfin := moserWin_add (I := I) (M := M)
    (moserWin_add (I := I) (M := M) hLw hPw) hRs
  rw [LowBaseInternal.topKernel_eq (I := I) (M := M) g g T hδg hδZ s]
  refine (hfin.2.2 i).trans ?_
  have hjetT : (0 : ℝ) ≤ lowJetSq (I := I) (M := M) g i T :=
    jetNn (I := I) (M := M) (m := i) g T
  have hsub : Finset.range (i + 1) ⊆ Finset.range (i + 2) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hmono : lowJetSq (I := I) (M := M) g i T ≤
      ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := by
    unfold lowJetSq
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  calc
    2 * (2 * (AL i + AP i) + 4 * AR i) *
        (1 + lowJetSq (I := I) (M := M) g i T) ≤
        |2 * (2 * (AL i + AP i) + 4 * AR i)| *
          (1 + lowJetSq (I := I) (M := M) g i T) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith only [hjetT])
    _ ≤ |2 * (2 * (AL i + AP i) + 4 * AR i)| *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [hmono]) (abs_nonneg _)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
