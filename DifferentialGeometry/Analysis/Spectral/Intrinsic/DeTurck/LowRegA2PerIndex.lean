import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegLadderRung
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ParametricAppCcJetBound

/-!
# The ball-free per-index `appCc` assembly of the low-base second-order arm

The tower-direct energy rungs of the bottom block need the `H^{k-1}` size of
the second-order arm `a₂ T = appCc C₂ (∇²T)` **without** an a-priori Sobolev
ball, and with the Leibniz sum priced index by index: the Hölder split is
chosen *separately* for each Leibniz index `i`, because only `i = 0` may be
charged to the small pointwise fibre cap of the coefficient.

The integrated per-index assembly itself already exists in the tree:
`app_jet_sq_le` (`Analysis/Sobolev/TensorHilbert/ParametricAppCcJetBound.lean`)
turns per-index pointwise caps on the coefficient's jets into exactly this
per-index `L²` Leibniz sum with the diagonal constant `appCcGdiag`.  (The two
collapsing engines,
`exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le` and
`exists_moserTameProduct_iteratedCovGrad_l2Norm_le`, do refuse the per-index
split — but they were never the only producers.)  `appCcPerIdxL2` below is a
thin `∃`-packaged wrapper around `app_jet_sq_le`; the content of this file is
the `a₂` *instantiation*: the per-index fibre caps `Λ i` built from the sup
embedding and the sharp tower window of `c2JetTowerSharp`.

## Main results

* `appCcPerIdxL2` — the interface (a wrapper around `app_jet_sq_le`).  For an
  arbitrary sequence `Λ` of pointwise fibre bounds for the coefficient's own
  jets, the order-`q` covariant `L²` jet of `appCc Φ W` obeys

  `‖∇^q(appCc Φ W)‖² ≤ G q · ∑_{i ≤ q} (Λ i)² · ∑_{l ≤ q-i} ‖∇^l W‖²`,

  with `G q = appCcGdiag q` fixed before every argument.  Each Leibniz index
  keeps its own constant and its own data window `l ≤ q - i`; nothing is
  collapsed and no ball appears.
* `icgWinShift`, `sqrtAdd2`, `sqrtFinSum` — the shared window/square-root
  algebra, public because `LowRegA1PerIndex` runs the same bookkeeping.
* `a2PerIdxJet` — the `a₂` instance.  `Λ 0` is the coefficient's fibre cap
  (`δ`-only, from `lowData_split`), and for `i ≥ 1` the sup embedding plus the
  **sharp** window of `c2JetTowerSharp` give
  `Λ i ≲ √(Kc (i+2)) · (1 + jet_{i+2}(T))`, so that the state never appears
  above order `q + 2`.

## The per-index Hölder choice, and why the window is sharp

For `i ≥ 1` the split is `L^∞` on the *coefficient* and `L²` on the state.  The
coefficient's sup norm at Leibniz index `i` costs `+2` `L²` orders
(`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`), so it
reads the `a₂` tower at index `i + 2`; with the **sharp** state window
`range (i + 1)` of `c2JetTowerSharp` that is a state jet of order `i + 2`, and
the companion data factor is `∇^{q-i} W = ∇^{q-i+2} T`.  Both indices stay at or
below `q + 2`, which is what makes the rung-`k` pairing (`q = k - 1`) close
against `‖T‖_{H^{k+1}}` instead of `‖T‖_{H^{k+2}}`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
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

/-- **The per-index `L²` Leibniz assembly of `appCc`, ball-free.**

A thin `∃`-packaged wrapper around `app_jet_sq_le`.

Each Leibniz index `i` of the coefficient carries its *own* pointwise fibre
bound `Λ i` and pairs with the data jets through order `q - i` only:

`‖∇^q(appCc Φ W)‖² ≤ appCcGdiag q · ∑_{i ≤ q} (Λ i)² · ∑_{l ≤ q-i} ‖∇^l W‖²`.

The constant is fixed before the coefficient, the data and the bounds, and no
Sobolev ball occurs.  This is the shape the tower-direct rungs consume: the
consumer chooses the small fibre cap at `i = 0` and pays the sup embedding only
for `i ≥ 1`, instead of collapsing the whole sum onto one lower slot. -/
theorem appCcPerIdxL2 (g₀ : SmoothRiemannianMetric I M) (b₀ s₀ q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g₀ b₀ s₀) (W : SmoothCcTensor g₀ 0 b₀) (Λ : ℕ → ℝ),
        (∀ (i : ℕ) (x : M),
          riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + i) x
            ((iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ).toSection x) ≤ Λ i ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ q
            (appCc (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
          C * ∑ i ∈ Finset.range (q + 1), Λ i ^ 2 *
            ∑ l ∈ Finset.range (q + 1 - i),
              ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2 := by
  refine ⟨appCcGdiag (E := E) q, appCcGdiag_nonneg (E := E) q, ?_⟩
  intro Φ W Λ hsup
  exact app_jet_sq_le (I := I) (M := M) g₀ b₀ s₀ q Φ W (fun i => Λ i ^ 2)
    (fun i _ => sq_nonneg (Λ i)) (fun i _ x => hsup i x)

/-! ## Shared helpers

Public because the `a₁` instance (`LowRegA1PerIndex`) reads exactly the same
window and square-root algebra.  The `L²` composition identity itself is *not*
restated here: it already exists as `icgNormComp` (`GradCapAtgw.lean`). -/

set_option linter.unusedSectionVars false in
/-- **The shifted `L²` jet window.**  The order-`≤ p` jet window of `∇^m Ψ`
sits inside the order-`≤ p + m` jet window of `Ψ`. -/
theorem icgWinShift (g : SmoothRiemannianMetric I M) (r s m p : ℕ)
    (Ψ : SmoothCcTensor g r s) :
    (∑ l ∈ Finset.range (p + 1),
      ‖iteratedCovGrad (I := I) g r (s + m) l
        (iteratedCovGrad (I := I) g r s m Ψ)‖ ^ 2) ≤
      ∑ j ∈ Finset.range (p + m + 1),
        ‖iteratedCovGrad (I := I) g r s j Ψ‖ ^ 2 := by
  classical
  rw [show (∑ l ∈ Finset.range (p + 1),
        ‖iteratedCovGrad (I := I) g r (s + m) l
          (iteratedCovGrad (I := I) g r s m Ψ)‖ ^ 2) =
      ∑ l ∈ Finset.range (p + 1),
        ‖iteratedCovGrad (I := I) g r s (m + l) Ψ‖ ^ 2 from
    Finset.sum_congr rfl (fun l _ => by
      rw [icgNormComp (I := I) (M := M) g r s m l Ψ])]
  set f : ℕ → ℝ := fun j => ‖iteratedCovGrad (I := I) g r s j Ψ‖ ^ 2 with hf_def
  have hinj : ∀ l₁ ∈ Finset.range (p + 1), ∀ l₂ ∈ Finset.range (p + 1),
      m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
  have himg : (Finset.range (p + 1)).image (fun l => m + l) ⊆
      Finset.range (p + m + 1) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨l, hl, rfl⟩ := hi
    rw [Finset.mem_range] at hl ⊢
    omega
  calc (∑ l ∈ Finset.range (p + 1), f (m + l))
      = ∑ j ∈ (Finset.range (p + 1)).image (fun l => m + l), f j :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ j ∈ Finset.range (p + m + 1), f j :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => sq_nonneg _)

set_option linter.unusedSectionVars false in
/-- Subadditivity of the square root on two nonnegative reals. -/
theorem sqrtAdd2 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hsq : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have hxx := Real.sq_sqrt hx
    have hyy := Real.sq_sqrt hy
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

set_option linter.unusedSectionVars false in
/-- Subadditivity of the square root over a finite sum of nonnegative terms. -/
theorem sqrtFinSum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    Real.sqrt (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine le_trans (sqrtAdd2 _ _ (hf a)
        (Finset.sum_nonneg (fun i _ => hf i))) ?_
      exact add_le_add le_rfl ih

/-! ## The `a₂` instance: per-index constants from the sharp tower -/

set_option linter.unusedSectionVars false in
/-- **Per-index sup bounds for the jets of the low-base top coefficient.**

For every Leibniz index `i` the coefficient's own jet `∇^i C₂` is bounded
pointwise by a constant chosen before the state times `1 + ` the state's jet
sum through order `i + 2`.  The `+2` is the sup embedding's cost; the fact that
it stops at `i + 2` rather than `i + 3` is exactly the sharp window of
`c2JetTowerSharp`. -/
private theorem c2SupJet (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Ks : ℕ → ℝ, (∀ i, 0 ≤ Ks i) ∧
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
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g (2 + 2) (2 + i) x
            ((iteratedCovGrad (I := I) g (2 + 2) 2 i
              (lowBaseData (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).C2).toSection x) ≤
          Ks i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨Kc, hKc_nn, htower⟩ := c2JetTowerSharp (I := I) (M := M) hDim g g_bg
  choose Csh hCsh_nn hCsh using fun i : ℕ =>
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g (2 + 2) (2 + i)
  refine ⟨fun i => Csh i ^ 2 * ∑ j ∈ Finset.range 3, Kc (i + j),
    fun i => mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg (fun j _ => hKc_nn (i + j))), ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i x
  set C₂ := (lowBaseData (I := I) (M := M) g g_bg T
    (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).C2 with hC₂
  set J : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 with hJ
  have hJ_nn : ∀ n, 0 ≤ J n := fun n =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hJ_mono : ∀ {a b : ℕ}, a ≤ b → J a ≤ J b := by
    intro a b hab
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  -- the sup embedding at the coefficient's own jet, then the sharp tower
  have hwin : Module.finrank ℝ E / 2 + 2 = 3 := by rw [hDim]
  have hemb := hCsh i (iteratedCovGrad (I := I) g (2 + 2) 2 i C₂) x
  rw [hwin] at hemb
  refine hemb.trans ?_
  have hstep : ∀ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g (2 + 2) (2 + i) j
        (iteratedCovGrad (I := I) g (2 + 2) 2 i C₂)‖ ^ 2 ≤
        Kc (i + j) * (1 + J (i + 2)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [icgNormComp (I := I) (M := M) g (2 + 2) 2 i j C₂]
    refine (htower T hT hδ0 hδ_le hδg hδZ (i + j)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKc_nn (i + j))
    have := hJ_mono (a := i + j) (b := i + 2) (by omega)
    linarith only [this]
  calc Csh i ^ 2 * ∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (2 + 2) (2 + i) j
          (iteratedCovGrad (I := I) g (2 + 2) 2 i C₂)‖ ^ 2
      ≤ Csh i ^ 2 * ∑ j ∈ Finset.range 3, Kc (i + j) * (1 + J (i + 2)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) (sq_nonneg _)
    _ = Csh i ^ 2 * (∑ j ∈ Finset.range 3, Kc (i + j)) * (1 + J (i + 2)) := by
        rw [← Finset.sum_mul]; ring

set_option linter.unusedSectionVars false in
/-- **The ball-free per-index `H^{q}`-jet assembly of the low-base `a₂` arm.**

`‖∇^q(a₂ T)‖² ≤ Cq q · (Cδ² · J(q+2) + ∑_{1 ≤ i ≤ q} K i · (1 + J(i+2)) · J(q-i+2))`,

where `J(n) = ∑_{j ≤ n} ‖∇^j T‖²` and `Cδ` is *any* pointwise fibre cap for the
coefficient `A.C2` — in the intended use `lowData_split`'s `K·δ/(1-δ)²`, which
is `δ`-only.

The Hölder split is per Leibniz index and explicit:

* `i = 0` is charged to the fibre cap alone, so the top state jet `∇^{q+2}T`
  meets the **small** constant `Cδ` and nothing else;
* `i ≥ 1` puts the coefficient in `L^∞` and the state in `L²`.  The `L^∞` factor
  costs the sup embedding's `+2` orders, so it reads the tower at index `i+2`
  and — by the *sharp* window of `c2JetTowerSharp` — the state at order `i+2`;
  its companion state jet is of order `q-i+2`.  Both indices are `≤ q+2`; the
  top order `q+2` occurs in exactly two slots — the `i = 0` term (against `Cδ`
  alone) and the `i = q` term's coefficient factor `1 + J(q+2)` (against `K q`
  and the class radius, PSTOP's `K_R·R` cost).  Interior slots `1 ≤ i ≤ q-1`
  stay strictly below `q+2`.

Nothing is collapsed onto a lower slot and no a-priori Sobolev ball is used:
`Cq` and `K` are fixed before `T`, `δ` and `Cδ`.  At the rung `k = q+1` this is
the estimate that keeps the coefficient's cost at `‖T‖_{H^{k+1}}` instead of
`‖T‖_{H^{k+2}}`; the `i = q` term is the one priced by the class radius
(`J 2 ≤ R²`), which is where PSTOP's adapter H (`Cδ* + K_R·R + 2ε < 1`) enters
the consumer. -/
theorem a2PerIdxJet (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Cq K : ℕ → ℝ, (∀ q, 0 ≤ Cq q) ∧ (∀ i, 0 ≤ K i) ∧
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
        {Cδ : ℝ}
        (hfib : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (2 + 2) 2 x
            ((lowBaseData (I := I) (M := M) g g_bg T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).C2.toSection x) ≤
            Cδ ^ 2)
        (q : ℕ),
        ‖iteratedCovGrad (I := I) g 0 2 q
            ((lowBaseData (I := I) (M := M) g g_bg T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).a2
                (I := I) (M := M) T)‖ ^ 2 ≤
          Cq q * (Cδ ^ 2 * ∑ j ∈ Finset.range (q + 3),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 +
            ∑ i ∈ Finset.Icc 1 q, K i *
              (1 + ∑ j ∈ Finset.range (i + 3),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) *
              ∑ j ∈ Finset.range (q - i + 3),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨Ks, hKs_nn, hsup⟩ := c2SupJet (I := I) (M := M) hDim g g_bg
  choose Cq hCq_nn hCq using fun q : ℕ => appCcPerIdxL2 (I := I) (M := M) g (2 + 2) 2 q
  refine ⟨Cq, Ks, hCq_nn, hKs_nn, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ Cδ hfib q
  set A := lowBaseData (I := I) (M := M) g g_bg T
    (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ with hA
  set J : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 with hJ
  have hJ_nn : ∀ n, 0 ≤ J n := fun n =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  -- the per-index fibre bounds: the cap at `i = 0`, the tower for `i ≥ 1`
  set Λ : ℕ → ℝ := fun i =>
    if i = 0 then |Cδ| else Real.sqrt (Ks i * (1 + J (i + 2))) with hΛ
  have hΛsup : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g (2 + 2) (2 + i) x
        ((iteratedCovGrad (I := I) g (2 + 2) 2 i A.C2).toSection x) ≤ Λ i ^ 2 := by
    intro i x
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      have hΛ0 : Λ 0 ^ 2 = Cδ ^ 2 := by simp only [hΛ]; norm_num [sq_abs]
      rw [hΛ0]
      simpa only [iteratedCovGrad_zero] using hfib x
    · have hne : i ≠ 0 := by omega
      rw [hΛ]
      simp only [if_neg hne]
      rw [Real.sq_sqrt (mul_nonneg (hKs_nn i) (by linarith only [hJ_nn (i + 2)]))]
      exact hsup T hT hδ0 hδ_le hδg hδZ i x
  have hshape : A.a2 (I := I) (M := M) T =
      appCc (I := I) (M := M) g (2 + 2) 2 A.C2
        (iteratedCovGrad (I := I) g 0 2 2 T) := rfl
  rw [hshape]
  refine (hCq q A.C2 (iteratedCovGrad (I := I) g 0 2 2 T) Λ hΛsup).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (hCq_nn q)
  -- the data window: `∑_{l ≤ q-i} ‖∇^l(∇²T)‖² ≤ J (q-i+2)`
  have hdata : ∀ i ∈ Finset.range (q + 1),
      (∑ l ∈ Finset.range (q + 1 - i),
        ‖iteratedCovGrad (I := I) g 0 (2 + 2) l
          (iteratedCovGrad (I := I) g 0 2 2 T)‖ ^ 2) ≤ J (q - i + 2) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hq : q + 1 - i = (q - i) + 1 := by omega
    rw [hq]
    simp only [hJ]
    exact icgWinShift (I := I) g 0 2 2 (q - i) T
  -- split the Leibniz index `i = 0` off the sum
  have hsplit : Finset.range (q + 1) = insert 0 (Finset.Icc 1 q) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnotmem : (0 : ℕ) ∉ Finset.Icc 1 q := by simp
  rw [hsplit, Finset.sum_insert hnotmem]
  refine add_le_add ?_ ?_
  · -- the `i = 0` term: the small fibre cap against the top state jet
    have h0 : Λ 0 ^ 2 = Cδ ^ 2 := by simp only [hΛ]; norm_num [sq_abs]
    rw [h0]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have hd := hdata 0 (Finset.mem_range.mpr (by omega))
    simp only [hJ] at hd
    rw [show q - 0 + 2 + 1 = q + 3 from by omega] at hd
    exact hd
  · -- the `i ≥ 1` terms: `L^∞` on the coefficient, `L²` on the state
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [Finset.mem_Icc] at hi
    have hne : i ≠ 0 := by omega
    have hΛi : Λ i ^ 2 = Ks i * (1 + J (i + 2)) := by
      simp only [hΛ, if_neg hne]
      exact Real.sq_sqrt (mul_nonneg (hKs_nn i) (by linarith only [hJ_nn (i + 2)]))
    have hd := hdata i (Finset.mem_range.mpr (by omega))
    simp only [hJ] at hΛi hd
    rw [show i + 2 + 1 = i + 3 from by omega] at hΛi
    rw [show q - i + 2 + 1 = q - i + 3 from by omega] at hd
    rw [hΛi]
    refine mul_le_mul_of_nonneg_left hd ?_
    refine mul_nonneg (hKs_nn i) ?_
    have : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 3),
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    linarith only [this]

/-! ## The linear form the rung pairing consumes -/

set_option linter.unusedSectionVars false in
/-- **The per-index `a₂` assembly in the linear form the pairing consumes.**

`‖∇^q(a₂ T)‖ ≤ Cq q · (Cδ · jet_{q+2}(T)
    + ∑_{1 ≤ i ≤ q} K i · (1 + jet_{i+2}(T)) · jet_{q-i+2}(T))`,

with `jet_n(T) = (∑_{j ≤ n} ‖∇^j T‖²)^{1/2}`, the square root of
`a2PerIdxJet`'s windows.  This is PSTOP §6.4's displayed shape at `q = k-1`:
the `i = 0` slot carries the small fibre constant `Cδ` against the top state
jet `jet_{k+1}`; the `i = q` slot is the one priced by the class radius
(`jet_2(T) ≤ R`, giving the `K_R·R·‖U‖_{H^{k+1}}` term); the intermediate slots
are products of two strictly lower jets, i.e. the `L¹_t`-Grönwall coefficients.

**Where the absorption hypothesis goes.**  The prefactor `Cq q` (the square
root of `appCcGdiag q`) multiplies the small constant as well, so a consumer
absorbing the top slot must assume `Cq q · Cδ + K_R·R + 2ε < 1` rather than
`Cδ + K_R·R + 2ε < 1`.  The ordering is still legal — `Cq` depends only on the
metrics and `q`, hence is fixed before `δ` and before `R` — but it is
a genuine (small) strengthening of PSTOP adapter H, and it is *not* discharged
here: the consumer threads it as an explicit hypothesis. -/
theorem a2PerIdxLin (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Cq K : ℕ → ℝ, (∀ q, 0 ≤ Cq q) ∧ (∀ i, 0 ≤ K i) ∧
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
        {Cδ : ℝ} (hCδ : 0 ≤ Cδ)
        (hfib : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (2 + 2) 2 x
            ((lowBaseData (I := I) (M := M) g g_bg T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).C2.toSection x) ≤
            Cδ ^ 2)
        (q : ℕ),
        ‖iteratedCovGrad (I := I) g 0 2 q
            ((lowBaseData (I := I) (M := M) g g_bg T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).a2
                (I := I) (M := M) T)‖ ≤
          Cq q * (Cδ * Real.sqrt (∑ j ∈ Finset.range (q + 3),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) +
            ∑ i ∈ Finset.Icc 1 q, K i *
              (1 + Real.sqrt (∑ j ∈ Finset.range (i + 3),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) *
              Real.sqrt (∑ j ∈ Finset.range (q - i + 3),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨Cq, K, hCq_nn, hK_nn, hsq⟩ := a2PerIdxJet (I := I) (M := M) hDim g g_bg
  refine ⟨fun q => Real.sqrt (Cq q), fun i => Real.sqrt (K i),
    fun q => Real.sqrt_nonneg _, fun i => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ Cδ hCδ hfib q
  set J : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (n + 3),
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 with hJ
  have hJ_nn : ∀ n, 0 ≤ J n := fun n =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hterm_nn : ∀ i, 0 ≤ K i * (1 + J i) * J (q - i) := fun i =>
    mul_nonneg (mul_nonneg (hK_nn i) (by linarith only [hJ_nn i])) (hJ_nn (q - i))
  have hsum_nn : (0 : ℝ) ≤ ∑ i ∈ Finset.Icc 1 q, K i * (1 + J i) * J (q - i) :=
    Finset.sum_nonneg (fun i _ => hterm_nn i)
  have hbase_nn : (0 : ℝ) ≤ Cδ ^ 2 * J q := mul_nonneg (sq_nonneg _) (hJ_nn q)
  have h : ‖iteratedCovGrad (I := I) g 0 2 q
      ((lowBaseData (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).a2
          (I := I) (M := M) T)‖ ^ 2 ≤
      Cq q * (Cδ ^ 2 * J q +
        ∑ i ∈ Finset.Icc 1 q, K i * (1 + J i) * J (q - i)) :=
    hsq T hT hδ0 hδ_le hδg hδZ hfib q
  -- take the square root of the squared per-index bound
  have hroot : ‖iteratedCovGrad (I := I) g 0 2 q
      ((lowBaseData (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).a2 (I := I) (M := M) T)‖ ≤
      Real.sqrt (Cq q) * Real.sqrt (Cδ ^ 2 * J q +
        ∑ i ∈ Finset.Icc 1 q, K i * (1 + J i) * J (q - i)) := by
    have hs := Real.sqrt_le_sqrt h
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (hCq_nn q)] at hs
    exact hs
  refine hroot.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  -- split the root of the sum, then peel each Leibniz slot
  refine le_trans (sqrtAdd2 _ _ hbase_nn hsum_nn) ?_
  have hbase : Real.sqrt (Cδ ^ 2 * J q) = Cδ * Real.sqrt (J q) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hCδ]
  rw [hbase]
  refine add_le_add le_rfl ?_
  refine le_trans (sqrtFinSum (Finset.Icc 1 q)
    (fun i => K i * (1 + J i) * J (q - i)) hterm_nn) ?_
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h1 : Real.sqrt (K i * (1 + J i) * J (q - i)) =
      Real.sqrt (K i) * Real.sqrt (1 + J i) * Real.sqrt (J (q - i)) := by
    rw [Real.sqrt_mul (mul_nonneg (hK_nn i) (by linarith only [hJ_nn i])),
      Real.sqrt_mul (hK_nn i)]
  rw [h1]
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hle : (1 : ℝ) + J i ≤ (1 + Real.sqrt (J i)) ^ 2 := by
    have := Real.sq_sqrt (hJ_nn i)
    nlinarith [Real.sqrt_nonneg (J i)]
  calc Real.sqrt (1 + J i)
      ≤ Real.sqrt ((1 + Real.sqrt (J i)) ^ 2) := Real.sqrt_le_sqrt hle
    _ = 1 + Real.sqrt (J i) := Real.sqrt_sq (by positivity)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
