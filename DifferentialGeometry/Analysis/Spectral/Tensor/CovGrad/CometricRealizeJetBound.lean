import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLichnerowiczCore
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.IteratedCovGradChartJetPeel
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeRawComponents

/-! # The supercritical ball-uniform covariant-jet bound on the realize-tie cometric trace field

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)`, a supercritical order `a`
(`2 · finrank E + 10 ≤ a`) and a covariant-`L²` ball radius `R ≥ 0`, this file proves the **single
ball-uniform fibre-norm-square bound** on the order-`≤ a` iterated covariant gradients of the realize-tie
endpoint cometric trace field `cometricTraceFieldG₀Tag g₀ (realize(g₀ + T)) 2`.

The cometric trace field's covariant jets `∇^{≤ a}` are exactly the covariant jets of the inverse metric
`g₁⁻¹ = (g₀ + h_sym T)⁻¹` (read through the frame-free double trace), a *nonlinear* (Moser-algebra)
function of the metric perturbation `T`.  The closure splits the deep content cleanly:

* the **genuine deep PDE input** is one named classical child,
  `exists_iteratedCovGrad_inverseMetric_moser_bound`, the ball-uniform bound on the *chart Fréchet
  jets* (`bareChartJetContent`) of the cometric trace field over the realize-tie family — the intrinsic
  inverse-metric covariant-jet Moser/Sobolev-algebra estimate;
* everything else is **proved, reusable** chart-jet infrastructure: the forward covariant-gradient
  chart-jet peel `iteratedFDeriv_rawPullR_iteratedCovGrad_le_bareChartJetContent_uniform` (which exhibits
  the residual as genuinely the inverse-metric jet content, up to the uniform `g₀`-Christoffel constant),
  and the reverse fibre-norm/raw-component bridge `riemannianFiberNormSq_le_raw_components_on_pouTsupport`,
  composed over the finite chart atlas.

The headline `exists_ballUniform_cometricTraceField_iteratedCovGrad_bound` is the downstream the
Lichnerowicz coefficient-jet envelope consumes (through the `dropTowerPsi`/`iteratedCovGrad` jet bridge).
Consumers transitively depend on the posited child's `sorryAx`.
-/

noncomputable section

set_option linter.style.setOption false

open Bundle Manifold MeasureTheory Set Filter Topology Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-! ## The deep PDE input: the ball-uniform inverse-metric covariant-jet Moser bound (POSITED leaf) -/

set_option linter.unusedVariables false in
/-- **(POSITED deep bedrock — the supercritical ball-uniform bound on the chart Fréchet jets of the
realize-tie cometric trace field over the radius-`R` ball.)**

For `g₀`, a supercritical order `a` (`2 · finrank E + 10 ≤ a`), a covariant-`L²` ball radius `R ≥ 0`,
and a chart base point `α`, there is one nonnegative constant `K` such that, for every `g₀`-fibre-small
smooth perturbation `T` whose covariant-`L²` jets up to order `a + 2` lie in the radius-`R` ball, the
order-`j` (`j ≤ a`) chart bare-jet content of the cometric trace field
`cometricTraceFieldG₀Tag g₀ (realize(g₀ + T)) 2` at the chart-`α` Euclidean kernel point over the closed
partition-of-unity support is bounded by `K`:
```
bareChartJetContent g₀ 4 2 (cometricTraceFieldG₀Tag g₀ (realize(g₀ + T)) 2) α j
    (toEuclidean (extChartAt I α b)) ≤ K   for all b ∈ tsupport ρ_α.
```

**Why this is the genuine deep content.**  `bareChartJetContent g₀ 4 2 C α j y` is the sum, over chart
component multi-index pairs and Fréchet orders `m ≤ j`, of the chart-Euclidean Fréchet jets of the raw
chart components of `C = cometricTraceFieldG₀Tag g₀ g₁ 2`; these are exactly the chart-coordinate
covariant jets of the inverse metric `g₁⁻¹ = (g₀ + h_sym T)⁻¹` (the frame-free double trace of the
cometric).  The realized metric `g₁`'s chart jets up to order `a + 2` are controlled by `C₀ + C · R`
(`g₀` jets plus the bounded `ccTensorBilinSymm` perturbation jets on the `R`-ball), and the `δ < 1`
fibre-operator bound keeps `g₁` uniformly positive-definite, so `g₁⁻¹` and all its chart jets are smooth
(Moser-algebra / Faà-di-Bruno) functions of the order-`≤ a + 2` jets of `T`; the supercritical embedding
`2 · finrank E + 10 ≤ a` controls those pointwise by the `R`-ball `L²` data.  Composing through the smooth
inverse and the frame-free double trace yields the single ball-uniform chart-jet bound `K`.  Consumers
transitively depend on its `sorryAx`.

**Non-vacuity.**  A `K ≡ 0` bound is rejected by the nonvanishing genuine (non-zero) cometric chart jets
on the supercritical ball; `K` is uniform over the ball while the cometric chart jets vary with the
realize-tie endpoint. -/
theorem exists_iteratedCovGrad_inverseMetric_moser_bound
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
          ∀ j : ℕ, j ≤ a → ∀ {b : M},
            b ∈ tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
              bareChartJetContent (I := I) (M := M) g₀ 4 2
                  (cometricTraceFieldG₀Tag (I := I) g₀
                    (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) 2) α j
                  ((toEuclidean (E := E)) (extChartAt I α b)) ≤ K :=
  sorry

/-! ## Per-chart ball-uniform fibre-norm-square bound on the cometric-trace jets -/

set_option linter.unusedVariables false in
/-- **Per-chart ball-uniform fibre-norm-square bound on the cometric-trace covariant jets.**  Combining
the proved forward covariant-gradient chart-jet peel (each raw chart component of `∇^j C` is dominated by
the order-`j` bare chart-jet content of `C`, up to a uniform `g₀`-Christoffel constant) with the posited
ball-uniform inverse-metric Moser bound (the bare chart-jet content is `≤ K` on the `R`-ball), gives a
single per-chart constant `Kα` bounding the chart-component-square sum of `∇^j C` over the closed
partition-of-unity support, uniformly over the radius-`R` ball and the order window `j ≤ a`. -/
private theorem exists_cometricTraceField_iteratedCovGrad_rawComponents_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) (α : M) :
    ∃ Kα : ℝ, 0 ≤ Kα ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
          ∀ j : ℕ, j ≤ a → ∀ {b : M},
            b ∈ tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
              (∑ Idx : Fin 4 → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin (2 + j) → Fin (Module.finrank ℝ E),
                  (tensorChartComponentRaw (I := I) (M := M) g₀ 4 (2 + j)
                    (iteratedCovGrad (I := I) g₀ 4 2 j
                      (cometricTraceFieldG₀Tag (I := I) g₀
                        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) 2)) α Idx Jdx b) ^ 2) ≤
                Kα := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n); exact_mod_cast this
  -- The proved forward peel constant (window `P = a`, uniform over all sections `X`).
  obtain ⟨Cpeel, hCpeel_nn, hCpeel⟩ :=
    iteratedFDeriv_rawPullR_iteratedCovGrad_le_bareChartJetContent_uniform
      (I := I) (M := M) g₀ 4 2 α a
  -- The posited ball-uniform inverse-metric Moser bound for this chart.
  obtain ⟨K, hK_nn, hK⟩ :=
    exists_iteratedCovGrad_inverseMetric_moser_bound (I := I) (M := M) g₀ a ha_super hR α
  -- The multi-index count factor `n^{4 + 2 + a}` dominates `n^{4 + (2 + j)}` for `j ≤ a`.
  refine ⟨(n : ℝ) ^ (4 + (2 + a)) * (Cpeel * K) ^ 2, by positivity, ?_⟩
  intro T δ hδ_lt hδ hTball j hj b hb
  set g₁ : SmoothRiemannianMetric I M := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁
  set C : SmoothCcTensor g₀ 4 2 := cometricTraceFieldG₀Tag (I := I) g₀ g₁ 2 with hC_def
  -- Chart-`α` setup: `b` lies in the chart source; the kernel point round-trips to `b`.
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact chartAtlasPOU_isSubordinate I M α hb
  set yb : EuclideanSpace ℝ (Fin n) := (toEuclidean (E := E)) (extChartAt I α b) with hyb_def
  have hy_kernel : yb ∈ chartImagePOUTsupport (I := I) (M := M) α :=
    ⟨extChartAt I α b, ⟨b, hb, rfl⟩, rfl⟩
  -- The posited bare-content bound at `b`, threaded for this `(T, j)`.
  have hcontent : bareChartJetContent (I := I) (M := M) g₀ 4 2 C α j yb ≤ K := by
    rw [hyb_def, hC_def, hg₁]
    exact hK T hδ_lt hδ hTball j hj hb
  -- Each raw chart component of `∇^j C` (an order-`0` Fréchet jet at `yb`) is `≤ Cpeel · K`.
  have hper : ∀ (Idx : Fin 4 → Fin n) (Jdx : Fin (2 + j) → Fin n),
      |tensorChartComponentRaw (I := I) (M := M) g₀ 4 (2 + j)
          (iteratedCovGrad (I := I) g₀ 4 2 j C) α Idx Jdx b| ≤ Cpeel * K := by
    intro Idx Jdx
    -- Convert the chart component at `b` to the `rawPullR` value at the kernel point `yb`.
    have hval : tensorChartComponentRaw (I := I) (M := M) g₀ 4 (2 + j)
          (iteratedCovGrad (I := I) g₀ 4 2 j C) α Idx Jdx b =
        rawPullR (I := I) (M := M) g₀ 4 (2 + j)
          (iteratedCovGrad (I := I) g₀ 4 2 j C) α Idx Jdx yb := by
      rw [hyb_def]
      simp only [rawPullR, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      rw [(extChartAt I α).left_inv hb_src]
    rw [hval]
    -- The forward peel at covariant order `p = j`, Fréchet order `l = 0`.
    have hpeel := hCpeel C j 0 (by omega) Idx Jdx yb hy_kernel
    rw [Nat.zero_add] at hpeel
    have hzero : ‖iteratedFDeriv ℝ 0
        (rawPullR (I := I) (M := M) g₀ 4 (2 + j)
          (iteratedCovGrad (I := I) g₀ 4 2 j C) α Idx Jdx) yb‖ =
        |rawPullR (I := I) (M := M) g₀ 4 (2 + j)
          (iteratedCovGrad (I := I) g₀ 4 2 j C) α Idx Jdx yb| := by
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    rw [hzero] at hpeel
    exact hpeel.trans (mul_le_mul_of_nonneg_left hcontent hCpeel_nn)
  -- Square each component bound and sum over the `n^{4 + (2 + j)}` multi-index pairs.
  have hperSq : ∀ (Idx : Fin 4 → Fin n) (Jdx : Fin (2 + j) → Fin n),
      (tensorChartComponentRaw (I := I) (M := M) g₀ 4 (2 + j)
          (iteratedCovGrad (I := I) g₀ 4 2 j C) α Idx Jdx b) ^ 2 ≤ (Cpeel * K) ^ 2 := by
    intro Idx Jdx
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hper Idx Jdx) 2
  calc (∑ Idx : Fin 4 → Fin n, ∑ Jdx : Fin (2 + j) → Fin n,
          (tensorChartComponentRaw (I := I) (M := M) g₀ 4 (2 + j)
            (iteratedCovGrad (I := I) g₀ 4 2 j C) α Idx Jdx b) ^ 2)
      ≤ ∑ _Idx : Fin 4 → Fin n, ∑ _Jdx : Fin (2 + j) → Fin n, (Cpeel * K) ^ 2 := by
        refine Finset.sum_le_sum (fun Idx _ => Finset.sum_le_sum (fun Jdx _ => ?_))
        exact hperSq Idx Jdx
    _ = ((n : ℝ) ^ 4 * (n : ℝ) ^ (2 + j)) * (Cpeel * K) ^ 2 := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
          nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc]
        congr 1
        simp only [Fintype.card_fun, Fintype.card_fin]
        push_cast; ring
    _ = (n : ℝ) ^ (4 + (2 + j)) * (Cpeel * K) ^ 2 := by
        rw [← pow_add]
    _ ≤ (n : ℝ) ^ (4 + (2 + a)) * (Cpeel * K) ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact pow_le_pow_right₀ hn1 (by omega)

/-! ## The headline supercritical ball-uniform covariant-jet bound -/

set_option linter.unusedVariables false in
/-- **(The supercritical ball-uniform fibre-norm-square bound on the order-`≤ a` iterated covariant
gradients of the realize-tie cometric trace field.)**

For `g₀`, a supercritical order `a` (`2 · finrank E + 10 ≤ a`) and a covariant-`L²` ball radius `R ≥ 0`,
there is one nonnegative constant `B` such that, for every `g₀`-fibre-small smooth perturbation `T` whose
covariant-`L²` jets up to order `a + 2` lie in the radius-`R` ball, the intrinsic fibre-norm-square of
every order-`j` (`j ≤ a`) iterated covariant gradient of the cometric trace field
`cometricTraceFieldG₀Tag g₀ (realize(g₀ + T)) 2` is bounded by `B` at **every** base point `x`:
```
riemannianFiberNormSq g₀ 4 (2 + j) x ((∇^j (cometricTraceFieldG₀Tag g₀ (realize(g₀ + T)) 2)).toSection x)
  ≤ B   for all j ≤ a, x : M.
```

This is the genuine deep PDE downstream that the Lichnerowicz coefficient-jet envelope consumes (through
the `dropTowerPsi`/`iteratedCovGrad` jet bridge): the `∇^{≤ a}` covariant jets of the cometric trace
field are the covariant jets of the inverse metric `g₁⁻¹ = (g₀ + h_sym T)⁻¹`, and their ball-uniform
fibre control is the supercritical inverse-metric Moser estimate.

**Closure.**  Per chart `α` of the finite atlas, the reverse fibre-norm/raw-component bridge
`riemannianFiberNormSq_le_raw_components_on_pouTsupport` (uniform over all sections) reduces the intrinsic
fibre-norm-square to the chart-component-square sum, which the per-chart ball-uniform constant
`exists_cometricTraceField_iteratedCovGrad_rawComponents_ballUniform` (proved peel + posited inverse-metric
Moser bound) controls by a single `Kα`; the atlas sum `B := ∑_α Cbridge_α · Kα` is the single
ball-uniform constant.

**Non-vacuity.**  A `B = 0` bound is rejected by a nonvanishing covariant jet of the genuine (non-zero)
cometric trace field on the supercritical ball; `B` is uniform over the ball while the cometric jets vary
with the realize-tie endpoint. -/
theorem exists_ballUniform_cometricTraceField_iteratedCovGrad_bound
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
          ∀ j : ℕ, j ≤ a → ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 4 2 j
                  (cometricTraceFieldG₀Tag (I := I) g₀
                    (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) 2)).toSection x) ≤ B := by
  classical
  -- Per chart `α`, per order `j ≤ a`: the reverse fibre-norm/raw-component bridge constant `Cbridge α j`
  -- (uniform over all sections) times the ball-uniform chart-component constant `Kα α` gives a single
  -- per-`(α, j)` bound; supremise over `j ≤ a` and sum over the finite atlas.
  set Cbridge : M → ℕ → ℝ := fun α j =>
    (riemannianFiberNormSq_le_raw_components_on_pouTsupport
      (I := I) (M := M) g₀ 4 (2 + j) α).choose with hCbridge_def
  have hCbridge_nn : ∀ (α : M) (j : ℕ), 0 ≤ Cbridge α j := fun α j =>
    (riemannianFiberNormSq_le_raw_components_on_pouTsupport
      (I := I) (M := M) g₀ 4 (2 + j) α).choose_spec.1
  have hCbridge : ∀ (α : M) (j : ℕ) (S : SmoothCcTensor g₀ 4 (2 + j)) {b : M},
      b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + j) b (S.toSection b) ≤
        Cbridge α j *
          (∑ Idx : Fin 4 → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin (2 + j) → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g₀ 4 (2 + j) S α Idx Jdx b) ^ 2) :=
    fun α j =>
      (riemannianFiberNormSq_le_raw_components_on_pouTsupport
        (I := I) (M := M) g₀ 4 (2 + j) α).choose_spec.2
  -- The per-chart ball-uniform chart-component constant.
  set Kα : M → ℝ := fun α =>
    (exists_cometricTraceField_iteratedCovGrad_rawComponents_ballUniform
      (I := I) (M := M) g₀ a ha_super hR α).choose with hKα_def
  have hKα_nn : ∀ α : M, 0 ≤ Kα α := fun α =>
    (exists_cometricTraceField_iteratedCovGrad_rawComponents_ballUniform
      (I := I) (M := M) g₀ a ha_super hR α).choose_spec.1
  have hKα := fun α =>
    (exists_cometricTraceField_iteratedCovGrad_rawComponents_ballUniform
      (I := I) (M := M) g₀ a ha_super hR α).choose_spec.2
  -- The per-chart constant `Cα α := (max_{j ≤ a} Cbridge α j) · Kα α`, summed over the atlas.
  set Bj : M → ℕ → ℝ := fun α j => Cbridge α j * Kα α with hBj_def
  have hBj_nn : ∀ (α : M) (j : ℕ), 0 ≤ Bj α j := fun α j =>
    mul_nonneg (hCbridge_nn α j) (hKα_nn α)
  set Cα : M → ℝ := fun α => (Finset.range (a + 1)).sup' (by simp) (Bj α) with hCα_def
  have hCα_nn : ∀ α : M, 0 ≤ Cα α := fun α =>
    le_trans (hBj_nn α 0) (Finset.le_sup' (Bj α) (by simp))
  set B : ℝ := ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Cα α with hB_def
  have hB_nn : 0 ≤ B := Finset.sum_nonneg (fun α _ => hCα_nn α)
  refine ⟨B, hB_nn, ?_⟩
  intro T δ hδ_lt hδ hTball j hj x
  set g₁ : SmoothRiemannianMetric I M := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁
  set Cf : SmoothCcTensor g₀ 4 (2 + j) :=
    iteratedCovGrad (I := I) g₀ 4 2 j (cometricTraceFieldG₀Tag (I := I) g₀ g₁ 2) with hCf_def
  -- Choose a chart `α` whose closed POU support contains `x`.
  obtain ⟨α, hα_pos⟩ := (chartAtlasPOU I M).exists_pos_of_mem (Set.mem_univ x)
  have hα_finset : α ∈ chartAtlasPOU_finset (I := I) (M := M) := by
    rw [chartAtlasPOU_finset_mem]
    exact ⟨x, Function.mem_support.mpr (ne_of_gt hα_pos)⟩
  have hx_tsupport : x ∈ tsupport (fun y : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) :=
    subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hα_pos))
  -- The raw-component sum is nonnegative.
  set RawSq : ℝ := ∑ Idx : Fin 4 → Fin (Module.finrank ℝ E),
    ∑ Jdx : Fin (2 + j) → Fin (Module.finrank ℝ E),
      (tensorChartComponentRaw (I := I) (M := M) g₀ 4 (2 + j) Cf α Idx Jdx x) ^ 2 with hRawSq_def
  have hRawSq_nn : 0 ≤ RawSq :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- Reverse bridge at `x` for chart `α`, applied to `Cf = ∇^j C`.
  have hbridge : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + j) x (Cf.toSection x) ≤
      Cbridge α j * RawSq := hCbridge α j Cf hx_tsupport
  -- Ball-uniform chart-component bound at `x` for chart `α`.
  have hraw : RawSq ≤ Kα α := by
    rw [hRawSq_def, hCf_def, hg₁]
    exact hKα α T hδ_lt hδ hTball j hj hx_tsupport
  -- Combine, then majorise by the per-order sup and the atlas sum.
  have hBj_le_Cα : Bj α j ≤ Cα α := by
    rw [hCα_def]
    exact Finset.le_sup' (Bj α) (Finset.mem_range.mpr (by omega))
  have hCα_le_B : Cα α ≤ B := by
    rw [hB_def]
    exact Finset.single_le_sum (fun β _ => hCα_nn β) hα_finset
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + j) x (Cf.toSection x)
      ≤ Cbridge α j * RawSq := hbridge
    _ ≤ Cbridge α j * Kα α := mul_le_mul_of_nonneg_left hraw (hCbridge_nn α j)
    _ = Bj α j := by rw [hBj_def]
    _ ≤ Cα α := hBj_le_Cα
    _ ≤ B := hCα_le_B

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
