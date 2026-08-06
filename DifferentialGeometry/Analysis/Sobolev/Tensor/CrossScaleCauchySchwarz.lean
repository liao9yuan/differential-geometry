import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

lemma tensorSobolevWeight_eq_sqrt_succ_mul_sqrt_pred
    (i : TensorEigenIdx (I := I) (M := M) g r s) (σ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i σ =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ + 1)) *
        Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ - 1)) := by
  have hbase : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  set x := 1 + TensorEigenIdx.lambda (I := I) (M := M) i with hx
  unfold tensorSobolevWeight
  rw [← hx]
  have hsqrt_u : Real.sqrt (x ^ (σ + 1)) = x ^ ((σ + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase.le]
    congr 1; ring
  have hsqrt_l : Real.sqrt (x ^ (σ - 1)) = x ^ ((σ - 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase.le]
    congr 1; ring
  rw [hsqrt_u, hsqrt_l, ← Real.rpow_add hbase]
  congr 1; ring

lemma sq_sum_crossScale_le
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s)) (σ : ℝ)
    (f h : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i)) ^ 2 ≤
      (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (f i) ^ 2) *
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (h i) ^ 2 := by
  set p : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ + 1)) * f i with hp_def
  set q : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ - 1)) * h i with hq_def
  have hsummand : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i) = p i * q i := by
    intro i
    rw [hp_def, hq_def,
      tensorSobolevWeight_eq_sqrt_succ_mul_sqrt_pred (I := I) (M := M) i σ]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsummand i)]
  have hCS : (∑ i ∈ S, p i * q i) ^ 2 ≤
      (∑ i ∈ S, (p i) ^ 2) * ∑ i ∈ S, (q i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq S p q
  have hp_sq : ∀ i, (p i) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (f i) ^ 2 := by
    intro i
    rw [hp_def, mul_pow,
      Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ + 1))]
  have hq_sq : ∀ i, (q i) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (h i) ^ 2 := by
    intro i
    rw [hq_def, mul_pow,
      Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ - 1))]
  rw [Finset.sum_congr rfl (fun i _ => hp_sq i),
    Finset.sum_congr rfl (fun i _ => hq_sq i)] at hCS
  exact hCS

theorem abs_sum_crossScale_le
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s)) (σ : ℝ)
    (f h : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    |∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i)| ≤
      Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (f i) ^ 2) *
        Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (h i) ^ 2) := by
  have hhi_nonneg :
      0 ≤ ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (f i) ^ 2 :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ + 1)) (sq_nonneg _))
  have hlo_nonneg :
      0 ≤ ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (h i) ^ 2 :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ - 1)) (sq_nonneg _))
  have hsq := sq_sum_crossScale_le (I := I) (M := M) S σ f h
  have hprod_nonneg :
      0 ≤ Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (f i) ^ 2) *
        Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (h i) ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine abs_le_of_sq_le_sq ?_ hprod_nonneg
  rw [mul_pow, Real.sq_sqrt hhi_nonneg, Real.sq_sqrt hlo_nonneg]
  exact hsq

theorem two_mul_sum_crossScale_le_eps
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s)) (σ : ℝ)
    (f h : TensorEigenIdx (I := I) (M := M) g r s → ℝ) {ε : ℝ} (hε : 0 < ε) :
    2 * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i) ≤
      ε * (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (f i) ^ 2) +
        ε⁻¹ * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (h i) ^ 2 := by
  set A := ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (f i) ^ 2 with hA
  set B := ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (h i) ^ 2 with hB
  have hA_nonneg : 0 ≤ A :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ + 1)) (sq_nonneg _))
  have hB_nonneg : 0 ≤ B :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ - 1)) (sq_nonneg _))
  have habs := abs_sum_crossScale_le (I := I) (M := M) S σ f h
  rw [← hA, ← hB] at habs
  have hle :
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i) ≤
        Real.sqrt A * Real.sqrt B :=
    le_trans (le_abs_self _) habs
  have hyoung : 2 * (Real.sqrt A * Real.sqrt B) ≤ ε * A + ε⁻¹ * B := by
    set sA := Real.sqrt A with hsA_def
    set sB := Real.sqrt B with hsB_def
    set sε := Real.sqrt ε with hsε_def
    set sεinv := Real.sqrt ε⁻¹ with hsεinv_def
    have hsqA : sA ^ 2 = A := Real.sq_sqrt hA_nonneg
    have hsqB : sB ^ 2 = B := Real.sq_sqrt hB_nonneg
    have hsqε : sε ^ 2 = ε := Real.sq_sqrt hε.le
    have hsqεinv : sεinv ^ 2 = ε⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hε.le)
    have hmix : sε * sεinv = 1 := by
      rw [hsε_def, hsεinv_def, ← Real.sqrt_mul hε.le, mul_inv_cancel₀ hε.ne', Real.sqrt_one]
    have hkey : 0 ≤ (sε * sA - sεinv * sB) ^ 2 := sq_nonneg _
    have hcross : (sε * sA) * (sεinv * sB) = sA * sB := by
      calc (sε * sA) * (sεinv * sB) = (sε * sεinv) * (sA * sB) := by ring
        _ = sA * sB := by rw [hmix, one_mul]
    nlinarith [hkey, hsqA, hsqB, hsqε, hsqεinv, hcross]
  nlinarith [hle, hyoung]

lemma sq_sum_sameScale_le
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s)) (σ : ℝ)
    (f h : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i)) ^ 2 ≤
      (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i) ^ 2) *
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (h i) ^ 2 := by
  set p : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * f i with hp_def
  set q : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * h i with hq_def
  have hsummand : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i) = p i * q i := by
    intro i
    simp only [hp_def, hq_def]
    have hsq : Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
        Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) =
        tensorSobolevWeight (I := I) (M := M) i σ :=
      Real.mul_self_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i σ)
    rw [show Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * f i *
          (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * h i) =
        (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ)) * (f i * h i) by ring,
      hsq]
  rw [Finset.sum_congr rfl (fun i _ => hsummand i)]
  have hCS : (∑ i ∈ S, p i * q i) ^ 2 ≤
      (∑ i ∈ S, (p i) ^ 2) * ∑ i ∈ S, (q i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq S p q
  have hp_sq : ∀ i, (p i) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i σ * (f i) ^ 2 := by
    intro i
    rw [hp_def, mul_pow,
      Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i σ)]
  have hq_sq : ∀ i, (q i) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i σ * (h i) ^ 2 := by
    intro i
    rw [hq_def, mul_pow,
      Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i σ)]
  rw [Finset.sum_congr rfl (fun i _ => hp_sq i),
    Finset.sum_congr rfl (fun i _ => hq_sq i)] at hCS
  exact hCS

theorem two_mul_sum_sameScale_le_sqrt
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s)) (σ : ℝ)
    (f h : TensorEigenIdx (I := I) (M := M) g r s → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hh : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (h i) ^ 2 ≤ c ^ 2) :
    2 * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i) ≤
      2 * c * Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i) ^ 2) := by
  set A := ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i) ^ 2 with hA
  set B := ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (h i) ^ 2 with hB
  have hA_nonneg : 0 ≤ A :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _))
  have hB_nonneg : 0 ≤ B :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _))
  have hsq := sq_sum_sameScale_le (I := I) (M := M) S σ f h
  rw [← hA, ← hB] at hsq
  set P := ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i) with hP
  have hP_sq : P ^ 2 ≤ A * B := hsq
  have hP_le_sqrtAB : P ≤ Real.sqrt (A * B) := by
    have h1 : P ≤ |P| := le_abs_self _
    have h2 : |P| ≤ Real.sqrt (A * B) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hP_sq
    exact le_trans h1 h2
  have hsqrtAB : Real.sqrt (A * B) = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA_nonneg B
  have hsqrtB_le : Real.sqrt B ≤ c := by
    have := Real.sqrt_le_sqrt hh
    rwa [Real.sqrt_sq hc] at this
  have hmono : Real.sqrt A * Real.sqrt B ≤ Real.sqrt A * c :=
    mul_le_mul_of_nonneg_left hsqrtB_le (Real.sqrt_nonneg A)
  have hP_le : P ≤ Real.sqrt A * Real.sqrt B := by rw [← hsqrtAB]; exact hP_le_sqrtAB
  calc 2 * P ≤ 2 * (Real.sqrt A * Real.sqrt B) := by linarith [hP_le]
    _ ≤ 2 * (Real.sqrt A * c) := by linarith [hmono]
    _ = 2 * c * Real.sqrt A := by ring

/-- **Parabolic energy closure from a ladder bound on the forcing.**

The forcing coordinates split as `f = fd + fs` on `S`, where the *difference* part
`fd` obeys a ladder bound one scale below (`α` on the top scale `σ + 1`, `β` on the
middle scale `σ`) and the *static* part `fs` is bounded at the middle scale by `D`.
Then the pairing `2 ∑ w^σ · u · f` — the source term of the `H^σ` energy identity —
is dominated by

  `(2α + ε) · E_{σ+1}(u) + (β²/ε) · E_σ(u) + 2D · √(E_σ(u))`,

which is exactly the closure hypothesis of the parabolic energy hierarchy: a small
multiple of the dissipation, a benign multiple of the energy at the same scale, and
a `√`-seed carrying the static source.  The dissipation constant is `2α + ε`, so the
absorption margin is available as soon as `α < 1`, with `ε` free to be chosen inside
the remaining room.

The two halves are `abs_sum_crossScale_le` (the weight-split Cauchy–Schwarz that
shifts one derivative from the forcing to the state) and
`two_mul_sum_sameScale_le_sqrt` (the same-scale pairing of the static source); the
only extra ingredient is one Young inequality on the mixed term `√E_{σ+1}·√E_σ`. -/
theorem two_mul_sum_ladder_le
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s)) (σ : ℝ)
    (u fd fs f : TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    {α β D ε : ℝ} (hD : 0 ≤ D) (hε : 0 < ε)
    (hsplit : ∀ i ∈ S, f i = fd i + fs i)
    (hladder :
      Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (fd i) ^ 2) ≤
        α * Real.sqrt
            (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (u i) ^ 2) +
          β * Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i) ^ 2))
    (hstat : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (fs i) ^ 2 ≤ D ^ 2) :
    2 * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i * f i) ≤
      (2 * α + ε) *
          (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (u i) ^ 2) +
        (β ^ 2 / ε) * (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i) ^ 2) +
        2 * D * Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i) ^ 2) := by
  set A := ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (u i) ^ 2 with hAdef
  set Eσ := ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i) ^ 2 with hEdef
  set B := ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (fd i) ^ 2 with hBdef
  have hA0 : 0 ≤ A :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ + 1)) (sq_nonneg _))
  have hE0 : 0 ≤ Eσ :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _))
  set sA := Real.sqrt A with hsAdef
  set sE := Real.sqrt Eσ with hsEdef
  have hsA0 : 0 ≤ sA := Real.sqrt_nonneg _
  have hsE0 : 0 ≤ sE := Real.sqrt_nonneg _
  have hsA2 : sA ^ 2 = A := Real.sq_sqrt hA0
  have hsE2 : sE ^ 2 = Eσ := Real.sq_sqrt hE0
  -- split the pairing into its difference and static halves
  have hsum : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i * f i) =
      (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i * fd i)) +
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i * fs i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hsplit i hi]; ring
  -- the difference half: Cauchy-Schwarz across scales, then the ladder, then Young
  have hcross : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i * fd i) ≤
      sA * Real.sqrt B :=
    le_trans (le_abs_self _) (abs_sum_crossScale_le (I := I) (M := M) S σ u fd)
  have hstep : sA * Real.sqrt B ≤ sA * (α * sA + β * sE) :=
    mul_le_mul_of_nonneg_left hladder hsA0
  have hyoung : 2 * β * (sA * sE) ≤ ε * A + (β ^ 2 / ε) * Eσ := by
    set sε := Real.sqrt ε with hsεdef
    have hsεpos : 0 < sε := Real.sqrt_pos.mpr hε
    have hsε2 : sε ^ 2 = ε := Real.sq_sqrt hε.le
    have hexpand : (sε * sA - (β / sε) * sE) ^ 2 =
        sε ^ 2 * sA ^ 2 - 2 * (sε * (β / sε)) * (sA * sE) + (β ^ 2 / sε ^ 2) * sE ^ 2 := by
      field_simp
      ring
    have hcancel : sε * (β / sε) = β := by field_simp
    rw [hcancel, hsε2, hsA2, hsE2] at hexpand
    nlinarith [sq_nonneg (sε * sA - (β / sε) * sE), hexpand]
  have hdiff : 2 * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i * fd i) ≤
      (2 * α + ε) * A + (β ^ 2 / ε) * Eσ := by
    have hchain : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i * fd i) ≤
        α * A + β * (sA * sE) := by
      refine le_trans (le_trans hcross hstep) ?_
      have : sA * (α * sA + β * sE) = α * (sA ^ 2) + β * (sA * sE) := by ring
      rw [this, hsA2]
    nlinarith [hchain, hyoung]
  -- the static half: same-scale pairing
  have hstatle := two_mul_sum_sameScale_le_sqrt (I := I) (M := M) S σ u fs hD hstat
  rw [← hEdef, ← hsEdef] at hstatle
  rw [hsum]
  linarith [hdiff, hstatle]

/-- **Parabolic energy closure from a ladder bound carrying an additive constant.**

`two_mul_sum_ladder_le` with the ladder hypothesis widened by a constant term
`γ`, i.e. `‖fd‖_{σ-1} ≤ α‖u‖_{σ+1} + β‖u‖_σ + γ`.  A low-regularity ladder
produces such a `γ` whenever a Leibniz slot is priced by a fixed radius rather
than by the state, so the closure must carry it.

The extra term is absorbed by one further Young inequality
`2γ√E_{σ+1} ≤ ε·E_{σ+1} + γ²/ε` at the *same* `ε` as the mixed term, so the
dissipation constant is `2α + 2ε` — the absorption margin is available as soon
as `α + ε < 1` — and the closure gains the additive slot `γ²/ε`, which the
single-scale Grönwall engine consumes. -/
theorem two_sum_ladder_add_le
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s)) (σ : ℝ)
    (u fd fs f : TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    {α β γ D ε : ℝ} (hD : 0 ≤ D) (hε : 0 < ε)
    (hsplit : ∀ i ∈ S, f i = fd i + fs i)
    (hladder :
      Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (fd i) ^ 2) ≤
        α * Real.sqrt
            (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (u i) ^ 2) +
          β * Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i) ^ 2) +
          γ)
    (hstat : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (fs i) ^ 2 ≤ D ^ 2) :
    2 * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i * f i) ≤
      (2 * α + 2 * ε) *
          (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (u i) ^ 2) +
        (β ^ 2 / ε) * (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i) ^ 2) +
        2 * D * Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i) ^ 2) +
        γ ^ 2 / ε := by
  set A := ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (u i) ^ 2 with hAdef
  set Eσ := ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i) ^ 2 with hEdef
  set B := ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (fd i) ^ 2 with hBdef
  have hA0 : 0 ≤ A :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ + 1)) (sq_nonneg _))
  have hE0 : 0 ≤ Eσ :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _))
  set sA := Real.sqrt A with hsAdef
  set sE := Real.sqrt Eσ with hsEdef
  have hsA0 : 0 ≤ sA := Real.sqrt_nonneg _
  have hsE0 : 0 ≤ sE := Real.sqrt_nonneg _
  have hsA2 : sA ^ 2 = A := Real.sq_sqrt hA0
  have hsE2 : sE ^ 2 = Eσ := Real.sq_sqrt hE0
  have hsum : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i * f i) =
      (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i * fd i)) +
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i * fs i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hsplit i hi]; ring
  have hcross : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i * fd i) ≤
      sA * Real.sqrt B :=
    le_trans (le_abs_self _) (abs_sum_crossScale_le (I := I) (M := M) S σ u fd)
  have hstep : sA * Real.sqrt B ≤ sA * (α * sA + β * sE + γ) :=
    mul_le_mul_of_nonneg_left hladder hsA0
  have hyoung : 2 * β * (sA * sE) ≤ ε * A + (β ^ 2 / ε) * Eσ := by
    set sε := Real.sqrt ε with hsεdef
    have hsεpos : 0 < sε := Real.sqrt_pos.mpr hε
    have hsε2 : sε ^ 2 = ε := Real.sq_sqrt hε.le
    have hexpand : (sε * sA - (β / sε) * sE) ^ 2 =
        sε ^ 2 * sA ^ 2 - 2 * (sε * (β / sε)) * (sA * sE) + (β ^ 2 / sε ^ 2) * sE ^ 2 := by
      field_simp
      ring
    have hcancel : sε * (β / sε) = β := by field_simp
    rw [hcancel, hsε2, hsA2, hsE2] at hexpand
    nlinarith [sq_nonneg (sε * sA - (β / sε) * sE), hexpand]
  -- the new Young step, at the same `ε`: `2γ·√A ≤ ε·A + γ²/ε`
  have hyoung' : 2 * γ * sA ≤ ε * A + γ ^ 2 / ε := by
    have hkey : ε * (ε * A + γ ^ 2 / ε - 2 * γ * sA) = (ε * sA - γ) ^ 2 := by
      rw [← hsA2]; field_simp; ring
    nlinarith [sq_nonneg (ε * sA - γ), hkey, hε]
  have hdiff : 2 * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i * fd i) ≤
      (2 * α + 2 * ε) * A + (β ^ 2 / ε) * Eσ + γ ^ 2 / ε := by
    have hchain : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (u i * fd i) ≤
        α * A + β * (sA * sE) + γ * sA := by
      refine le_trans (le_trans hcross hstep) ?_
      have hexp : sA * (α * sA + β * sE + γ) =
          α * (sA ^ 2) + β * (sA * sE) + γ * sA := by ring
      rw [hexp, hsA2]
    nlinarith [hchain, hyoung, hyoung']
  have hstatle := two_mul_sum_sameScale_le_sqrt (I := I) (M := M) S σ u fs hD hstat
  rw [← hEdef, ← hsEdef] at hstatle
  rw [hsum]
  linarith [hdiff, hstatle]

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
