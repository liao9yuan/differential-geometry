import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseLip

/-!
# `H²` jet algebra and the `lc0VB` pairwise estimate

This module carries two things.

* The **`H²` jet-algebra layer** shared by every class of the second-order
  low-base telescope: the local jet algebra (`jetNn`, `jetSmul`, `jetAdd`,
  `jetMono`), the exact spectral interpolation of the third jet
  (`jetInterp3`, from `specInterp3` and the two-sided `Hˢ`/jet equivalences),
  the slot / reindex / trace transfer lemmas, the `H²×H²→H²` product engine
  `appH2`, and the scalar re-pairing endgame `amixScalar`.  These used to live
  privately inside `DeTurckRemainderLowBaseH2Pair`; they are exported here so
  that both files stay under the source-size limit and no fact is duplicated.

* **Class 3 of the second-order telescope**: the vector--bundle zero head
  `lc0VB` obeys the admissible modulus
  `(B0 R · (1+A) · (D4 + D3 + D2 + N) + B1 R · A4 · (D3 + N))²`.

The class-3 route mirrors the `H¹` sibling `vb_pair_h1`: `vb_refold_rf` writes
`lc0VB = 2 • app₂₄₂(lc0RiemLive, app₂₁₄(vbMcdArm, ipLowCc (wOmega)))`, and
`wOmega_refold` writes the DeTurck covector as `app₀₃₁(Tr₁, connDiffLoweredCc)`.
The inner arm carries a connection difference (size `1+A`) against `wOmega`
(size `A`), i.e. an `A²` passenger, which is inadmissible against a difference.
Both `A`-carrying producers are therefore re-read at the interpolated third-jet
size `a = √(Cip·R·A4)` (`jetInterp3`), after which `(1+a)⁴ ≤ 8(1 + (Cip R A4)²)`
puts the whole excess into the single `A4`-linear arm (`amixScalar`).  The two
connection-difference pair moduli (`mcd_pair_h2`, `wXi_sub_tame`) are fed with
`D2 := D3`, legitimate since `J2 (T-U) ≤ J3 (T-U)`.
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

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
/-! ### Local jet algebra

The corresponding helpers of `DeTurckRemainderLowBaseLip` are private to that
module; the four facts below are re-established here so that the `H²` chain is
self-contained. -/

omit [BoundarylessManifold I M] in
theorem jetNn
    (g : SmoothRiemannianMetric I M) {r s m : ℕ}
    (S : SmoothCcTensor g r s) :
    0 ≤ lowJetSq (I := I) (M := M) g m S :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem jetSmul
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m (c • S) =
      c ^ 2 * lowJetSq (I := I) (M := M) g m S := by
  unfold lowJetSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [iteratedCovGrad_smul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]

theorem jetAdd
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S V : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m (S + V) ≤
      2 * (lowJetSq (I := I) (M := M) g m S +
        lowJetSq (I := I) (M := M) g m V) := by
  unfold lowJetSq
  calc
    ∑ q ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r s q (S + V)‖ ^ 2 ≤
        ∑ q ∈ Finset.range (m + 1),
          2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      refine Finset.sum_le_sum fun q _ => ?_
      rw [iteratedCovGrad_add]
      have htri := norm_add_le
        (iteratedCovGrad (I := I) g r s q S)
        (iteratedCovGrad (I := I) g r s q V)
      calc
        ‖iteratedCovGrad (I := I) g r s q S +
            iteratedCovGrad (I := I) g r s q V‖ ^ 2 ≤
            (‖iteratedCovGrad (I := I) g r s q S‖ +
              ‖iteratedCovGrad (I := I) g r s q V‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
        _ ≤ 2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
          nlinarith [sq_nonneg
            (‖iteratedCovGrad (I := I) g r s q S‖ -
              ‖iteratedCovGrad (I := I) g r s q V‖)]
    _ = 2 * ((∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q S‖ ^ 2) +
        ∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

omit [BoundarylessManifold I M] in
theorem sqAdd2 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by
  nlinarith [mul_nonneg ha hb]

/-! ### Spectral interpolation of the third jet

The `A²`-sized passengers of classes 1--3 are re-paired through the exact
spectral interpolation `‖·‖²_{H³} ≤ ‖·‖_{H²}·‖·‖_{H⁴}`, which on the
eigencoefficient representation is a weight-wise AM--GM (no covariant
integration by parts, no Gagliardo--Nirenberg leaf), and is then transported to
the covariant jet currency by the public two-sided equivalences `hsJet_le` /
`hs_le_jet`.

Canonical home once a second consumer appears:
`Analysis/Spectral/Tensor/SobolevScale/IteratedCovGradHsJetBound.lean`. -/

omit [BoundarylessManifold I M] in
/-- Young's inequality against a free parameter promotes to the sharp product
bound.  Used to turn the parametric interpolation into `X ≤ a·b`. -/
theorem prodOfParam {X a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ t : ℝ, 0 < t → X ≤ (t * a ^ 2 + b ^ 2 / t) / 2) :
    X ≤ a * b := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ : ℝ := ε / (a + b + 1) with hδdef
  have hden : 0 < a + b + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hbδ : 0 < b + δ := by linarith
  have haδ : 0 < a + δ := by linarith
  have ht : 0 < (b + δ) / (a + δ) := div_pos hbδ haδ
  have hX := h _ ht
  have h1 : (b + δ) / (a + δ) * a ^ 2 ≤ a * b + δ * a := by
    have hkey : a ^ 2 ≤ a * (a + δ) := by nlinarith
    have hstep : (b + δ) / (a + δ) * a ^ 2 ≤
        (b + δ) / (a + δ) * (a * (a + δ)) :=
      mul_le_mul_of_nonneg_left hkey (le_of_lt ht)
    refine hstep.trans (le_of_eq ?_)
    field_simp
  have h2 : b ^ 2 / ((b + δ) / (a + δ)) ≤ a * b + δ * b := by
    rw [div_div_eq_mul_div]
    rw [div_le_iff₀ hbδ]
    nlinarith [mul_nonneg ha hδ.le, mul_nonneg hb hδ.le,
      mul_nonneg (mul_nonneg hb hδ.le) hδ.le, sq_nonneg b]
  have hsum : (( (b + δ) / (a + δ)) * a ^ 2 +
      b ^ 2 / ((b + δ) / (a + δ))) / 2 ≤ a * b + δ * (a + b) / 2 := by
    have := add_le_add h1 h2
    linarith
  have hfin : δ * (a + b) / 2 ≤ ε := by
    rw [hδdef]
    rw [div_mul_eq_mul_div, div_div]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (a + b + 1) * 2)]
    nlinarith [hε.le, ha, hb]
  linarith [hX, hsum, hfin]

omit [BoundarylessManifold I M] in
/-- The Sobolev weights obey the AM--GM interpolation `w³ ≤ (t·w² + w⁴/t)/2`
mode by mode. -/
theorem wgtAmgm
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 s) {t : ℝ} (ht : 0 < t) :
    tensorSobolevWeight (I := I) (M := M) i ((3 : ℕ) : ℝ) ≤
      (t * tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) +
        tensorSobolevWeight (I := I) (M := M) i ((4 : ℕ) : ℝ) / t) / 2 := by
  have e2 : tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) =
      (1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 := by
    simp only [tensorSobolevWeight]
    exact Real.rpow_natCast _ 2
  have e3 : tensorSobolevWeight (I := I) (M := M) i ((3 : ℕ) : ℝ) =
      (1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) ^ 3 := by
    simp only [tensorSobolevWeight]
    exact Real.rpow_natCast _ 3
  have e4 : tensorSobolevWeight (I := I) (M := M) i ((4 : ℕ) : ℝ) =
      (1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) ^ 4 := by
    simp only [tensorSobolevWeight]
    exact Real.rpow_natCast _ 4
  rw [e2, e3, e4]
  set w : ℝ := 1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i with hwdef
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have hcancel : t * (w ^ 4 / t) = w ^ 4 := by
    field_simp
  have hprod : t * (w ^ 3 * 2) ≤ t * (t * w ^ 2 + w ^ 4 / t) := by
    have hq : t * (t * w ^ 2 + w ^ 4 / t) = t ^ 2 * w ^ 2 + w ^ 4 := by
      rw [mul_add, hcancel]
      ring
    rw [hq]
    nlinarith [sq_nonneg (t * w - w ^ 2)]
  exact le_of_mul_le_mul_left hprod ht

/-- **Spectral interpolation, parametric form.**  Exact on the eigencoefficient
representation: no integration by parts and no Gagliardo--Nirenberg input. -/
theorem specInterp3
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {t : ℝ} (ht : 0 < t) :
    ‖ccTensorToHs (I := I) (M := M) g s ((3 : ℕ) : ℝ) S‖ ^ 2 ≤
      (t * ‖ccTensorToHs (I := I) (M := M) g s ((2 : ℕ) : ℝ) S‖ ^ 2 +
        ‖ccTensorToHs (I := I) (M := M) g s ((4 : ℕ) : ℝ) S‖ ^ 2 / t) / 2 := by
  classical
  set c : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 s → ℝ := fun i =>
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
      (SmoothCcTensor.toL2 S) i with hcdef
  have hn : ∀ σ : ℝ, ‖ccTensorToHs (I := I) (M := M) g s σ S‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2 := by
    intro σ
    rw [tensorHs.norm_sq_eq_tsum]
    rfl
  have hsm : ∀ σ : ℝ, Summable (fun i =>
      tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2) := by
    intro σ
    exact (ccTensorToHs (I := I) (M := M) g s σ S).weighted_summable
  have hkey : ∀ i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 s,
      tensorSobolevWeight (I := I) (M := M) i ((3 : ℕ) : ℝ) * (c i) ^ 2 ≤
        (t * (tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) *
            (c i) ^ 2) +
          tensorSobolevWeight (I := I) (M := M) i ((4 : ℕ) : ℝ) *
            (c i) ^ 2 / t) / 2 := by
    intro i
    have hA := wgtAmgm (I := I) (M := M) g i ht
    have hstep := mul_le_mul_of_nonneg_right hA (sq_nonneg (c i))
    refine hstep.trans (le_of_eq ?_)
    field_simp
  have hsumR : Summable (fun i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 s =>
      (t * (tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) *
          (c i) ^ 2) +
        tensorSobolevWeight (I := I) (M := M) i ((4 : ℕ) : ℝ) *
          (c i) ^ 2 / t) / 2) :=
    (((hsm _).mul_left t).add ((hsm _).div_const t)).div_const 2
  have hle := Summable.tsum_le_tsum hkey (hsm _) hsumR
  have htsum : (∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 s,
      (t * (tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) *
          (c i) ^ 2) +
        tensorSobolevWeight (I := I) (M := M) i ((4 : ℕ) : ℝ) *
          (c i) ^ 2 / t) / 2) =
      (t * (∑' i, tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) *
          (c i) ^ 2) +
        (∑' i, tensorSobolevWeight (I := I) (M := M) i ((4 : ℕ) : ℝ) *
          (c i) ^ 2) / t) / 2 := by
    rw [tsum_div_const,
      Summable.tsum_add ((hsm _).mul_left t) ((hsm _).div_const t),
      tsum_mul_left, tsum_div_const]
  rw [hn ((3 : ℕ) : ℝ), hn ((2 : ℕ) : ℝ), hn ((4 : ℕ) : ℝ)]
  rw [← htsum]
  exact hle

omit [BoundarylessManifold I M] in
/-- The squared covariant jet is dominated by the square of the jet-norm sum. -/
theorem jetSumSq
    (g : SmoothRiemannianMetric I M) {s : ℕ} (n : ℕ)
    (S : SmoothCcTensor g 0 s) :
    lowJetSq (I := I) (M := M) g n S ≤
      (∑ j ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g 0 s j S‖) ^ 2 := by
  unfold lowJetSq
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

omit [BoundarylessManifold I M] in
/-- Cauchy--Schwarz in the jet index: the jet-norm sum is dominated by
`√((n+1)·lowJetSq n)`. -/
theorem jetSumLe
    (g : SmoothRiemannianMetric I M) {s : ℕ} (n : ℕ)
    (S : SmoothCcTensor g 0 s) :
    (∑ j ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g 0 s j S‖) ^ 2 ≤
      ((n : ℝ) + 1) * lowJetSq (I := I) (M := M) g n S := by
  unfold lowJetSq
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n + 1))
    (fun _ => (1 : ℝ)) (fun j => ‖iteratedCovGrad (I := I) g 0 s j S‖)
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one] using h

/-- **The interpolated third jet.**  On a fixed background `g` there is a
constant with `J3 S ≤ C · R · A4` whenever `J2 S ≤ R²` and `J4 S ≤ A4²`.  This
is the re-pairing device: an `A²`-sized passenger becomes `A4`-linear with a
factor of the small `H²` radius `R`. -/
theorem jetInterp3
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g 0 s) (R A4 : ℝ), 0 ≤ R → 0 ≤ A4 →
        lowJetSq (I := I) (M := M) g 2 S ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 4 S ≤ A4 ^ 2 →
      lowJetSq (I := I) (M := M) g 3 S ≤ C * (R * A4) := by
  obtain ⟨C3, hC3, hjet3⟩ := hsJet_le (I := I) (M := M) g s 3
  obtain ⟨K2, hK2, hhs2⟩ := hs_le_jet (I := I) (M := M) g s 2
  obtain ⟨K4, hK4, hhs4⟩ := hs_le_jet (I := I) (M := M) g s 4
  refine ⟨C3 ^ 2 * (K2 * Real.sqrt 3) * (K4 * Real.sqrt 5),
    by positivity, ?_⟩
  intro S R A4 hR hA4 h2 h4
  set N2 : ℝ := ‖ccTensorToHs (I := I) (M := M) g s ((2 : ℕ) : ℝ) S‖ with hN2
  set N3 : ℝ := ‖ccTensorToHs (I := I) (M := M) g s ((3 : ℕ) : ℝ) S‖ with hN3
  set N4 : ℝ := ‖ccTensorToHs (I := I) (M := M) g s ((4 : ℕ) : ℝ) S‖ with hN4
  -- (i) the jet is controlled by the spectral `H³` norm
  have hup : lowJetSq (I := I) (M := M) g 3 S ≤ C3 ^ 2 * N3 ^ 2 := by
    refine (jetSumSq (I := I) (M := M) g 3 S).trans ?_
    have h := hjet3 S
    have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (3 + 1),
        ‖iteratedCovGrad (I := I) g 0 s j S‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc (∑ j ∈ Finset.range (3 + 1),
          ‖iteratedCovGrad (I := I) g 0 s j S‖) ^ 2 ≤
        (C3 * N3) ^ 2 := pow_le_pow_left₀ hnn h 2
      _ = C3 ^ 2 * N3 ^ 2 := by ring
  -- (ii) the spectral `H²` and `H⁴` norms are controlled by `R` and `A4`
  have hN2le : N2 ≤ K2 * Real.sqrt 3 * R := by
    refine (hhs2 S).trans ?_
    have hcs := jetSumLe (I := I) (M := M) g 2 S
    have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (2 + 1),
        ‖iteratedCovGrad (I := I) g 0 s j S‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hbd : (∑ j ∈ Finset.range (2 + 1),
        ‖iteratedCovGrad (I := I) g 0 s j S‖) ≤ Real.sqrt 3 * R := by
      have hstep : (∑ j ∈ Finset.range (2 + 1),
          ‖iteratedCovGrad (I := I) g 0 s j S‖) ^ 2 ≤
          (Real.sqrt 3 * R) ^ 2 := by
        refine hcs.trans ?_
        have h3 : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
        rw [h3]
        have hsq : (Real.sqrt 3 * R) ^ 2 = 3 * R ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        rw [hsq]
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      have hb : (0 : ℝ) ≤ Real.sqrt 3 * R :=
        mul_nonneg (Real.sqrt_nonneg _) hR
      have hsq := Real.sqrt_le_sqrt hstep
      rwa [Real.sqrt_sq hnn, Real.sqrt_sq hb] at hsq
    calc K2 * (∑ j ∈ Finset.range (2 + 1),
        ‖iteratedCovGrad (I := I) g 0 s j S‖) ≤
        K2 * (Real.sqrt 3 * R) := mul_le_mul_of_nonneg_left hbd hK2
      _ = K2 * Real.sqrt 3 * R := by ring
  have hN4le : N4 ≤ K4 * Real.sqrt 5 * A4 := by
    refine (hhs4 S).trans ?_
    have hcs := jetSumLe (I := I) (M := M) g 4 S
    have hbd : (∑ j ∈ Finset.range (4 + 1),
        ‖iteratedCovGrad (I := I) g 0 s j S‖) ≤ Real.sqrt 5 * A4 := by
      have hstep : (∑ j ∈ Finset.range (4 + 1),
          ‖iteratedCovGrad (I := I) g 0 s j S‖) ^ 2 ≤
          (Real.sqrt 5 * A4) ^ 2 := by
        refine hcs.trans ?_
        have h5 : ((4 : ℕ) : ℝ) + 1 = 5 := by norm_num
        rw [h5]
        have hsq : (Real.sqrt 5 * A4) ^ 2 = 5 * A4 ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
        rw [hsq]
        exact mul_le_mul_of_nonneg_left h4 (by norm_num)
      have hb : (0 : ℝ) ≤ Real.sqrt 5 * A4 :=
        mul_nonneg (Real.sqrt_nonneg _) hA4
      have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (4 + 1),
          ‖iteratedCovGrad (I := I) g 0 s j S‖ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hsq := Real.sqrt_le_sqrt hstep
      rwa [Real.sqrt_sq hnn, Real.sqrt_sq hb] at hsq
    calc K4 * (∑ j ∈ Finset.range (4 + 1),
        ‖iteratedCovGrad (I := I) g 0 s j S‖) ≤
        K4 * (Real.sqrt 5 * A4) := mul_le_mul_of_nonneg_left hbd hK4
      _ = K4 * Real.sqrt 5 * A4 := by ring
  -- (iii) interpolate, then promote the parametric bound to the product
  have hprod : N3 ^ 2 ≤ (K2 * Real.sqrt 3 * R) * (K4 * Real.sqrt 5 * A4) := by
    refine prodOfParam (X := N3 ^ 2)
      (mul_nonneg (mul_nonneg hK2 (Real.sqrt_nonneg _)) hR)
      (mul_nonneg (mul_nonneg hK4 (Real.sqrt_nonneg _)) hA4) ?_
    intro t ht
    refine (specInterp3 (I := I) (M := M) g s S ht).trans ?_
    have e1 : t * N2 ^ 2 ≤ t * (K2 * Real.sqrt 3 * R) ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ ht.le
      exact pow_le_pow_left₀ (norm_nonneg _) hN2le 2
    have e2 : N4 ^ 2 / t ≤ (K4 * Real.sqrt 5 * A4) ^ 2 / t := by
      have hinv : (0 : ℝ) ≤ t⁻¹ := (inv_pos.mpr ht).le
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hN4le 2) hinv
    linarith
  calc lowJetSq (I := I) (M := M) g 3 S ≤ C3 ^ 2 * N3 ^ 2 := hup
    _ ≤ C3 ^ 2 * ((K2 * Real.sqrt 3 * R) * (K4 * Real.sqrt 5 * A4)) :=
      mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
    _ = C3 ^ 2 * (K2 * Real.sqrt 3) * (K4 * Real.sqrt 5) * (R * A4) := by
      ring

/-! ### Slot, reindex and product algebra at the `H²` level

The corresponding helpers of the `H¹` chain are `private` to
`DeTurckRemainderLowBaseLip`; the facts below are re-established here from the
public `rfns` transfer layer and the public product engine
`appRS_h2_h2_h2`. -/

omit [BoundarylessManifold I M] in
/-- Scalar splitting of a binomial square, used to keep the modulus algebra out
of `nlinarith` over tensor-sized monomials. -/
theorem sqTwo (p q : ℝ) : (p + q) ^ 2 ≤ 2 * p ^ 2 + 2 * q ^ 2 := by
  nlinarith [sq_nonneg (p - q)]

omit [BoundarylessManifold I M] in
/-- The scalar face of the `(1+√x)⁴ ≤ 8(1+x²)` envelope collapse. -/
theorem quadFour (x : ℝ) : 4 * (1 + 2 * x + x * x) ≤ 8 * (1 + x ^ 2) := by
  nlinarith [sq_nonneg (1 - x)]

omit [BoundarylessManifold I M] in
/-- **The scalar re-pairing step of class 4.**  An envelope which is quartic in
the interpolated third-jet size `x = √(cip·R·A4)` collapses, against a `(D3, N)`
difference budget, into the admissible modulus: `(1+x)⁴ ≤ 8(1 + (cip R A4)²)`
puts the whole excess into a single `A4`-linear arm.  Stated separately so that
the tensor telescope never hands a big context to `linarith`. -/
theorem amixScalar
    {bh cip R A A4 D2 D3 D4 N x : ℝ}
    (hbh : 0 ≤ bh) (hcip : 0 ≤ cip) (hR : 0 ≤ R) (hA : 0 ≤ A) (hA4 : 0 ≤ A4)
    (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3) (hD4 : 0 ≤ D4) (hN : 0 ≤ N)
    (hxsq : x ^ 2 = cip * (R * A4)) :
    bh * (((1 + x) ^ 2 * (1 + x) ^ 2) * (D3 ^ 2 + N ^ 2)) ≤
      (Real.sqrt (8 * bh) * (1 + A) * (D4 + D3 + D2 + N) +
        Real.sqrt (8 * bh) * cip * R * A4 * (D3 + N)) ^ 2 := by
  set u : ℝ := D3 ^ 2 + N ^ 2 with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  have hbh8 : (0 : ℝ) ≤ 8 * bh := by linarith
  have hsq : Real.sqrt (8 * bh) ^ 2 = 8 * bh := Real.sq_sqrt hbh8
  have hsn : 0 ≤ Real.sqrt (8 * bh) := Real.sqrt_nonneg _
  have hu1 : u ≤ (D3 + N) ^ 2 := by
    rw [hu]
    exact sqAdd2 hD3 hN
  have hgeu : u ≤ (1 + A) ^ 2 * (D4 + D3 + D2 + N) ^ 2 := by
    have h2 : (D3 + N) ^ 2 ≤ (D4 + D3 + D2 + N) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hone : (1 : ℝ) ≤ (1 + A) ^ 2 := by nlinarith [hA]
    have h3 : (D4 + D3 + D2 + N) ^ 2 ≤
        (1 + A) ^ 2 * (D4 + D3 + D2 + N) ^ 2 := by
      calc (D4 + D3 + D2 + N) ^ 2 = 1 * (D4 + D3 + D2 + N) ^ 2 :=
          (one_mul _).symm
        _ ≤ (1 + A) ^ 2 * (D4 + D3 + D2 + N) ^ 2 :=
          mul_le_mul_of_nonneg_right hone (sq_nonneg _)
    linarith
  have hpl0 : (0 : ℝ) ≤ (1 + x) ^ 2 := sq_nonneg _
  have hpl4 : (1 + x) ^ 2 * (1 + x) ^ 2 ≤ 8 * (1 + (cip * R * A4) ^ 2) := by
    have hX : x ^ 2 = cip * R * A4 := by
      rw [hxsq]
      ring
    have hp : (1 + x) ^ 2 ≤ 2 * (1 + x ^ 2) := by
      nlinarith [sq_nonneg (1 - x)]
    have hq : (1 + x) ^ 2 * (1 + x) ^ 2 ≤
        (2 * (1 + x ^ 2)) * (2 * (1 + x ^ 2)) :=
      mul_le_mul hp hp hpl0 (by positivity)
    refine hq.trans ?_
    have he : (2 * (1 + x ^ 2)) * (2 * (1 + x ^ 2)) =
        4 * (1 + 2 * x ^ 2 + x ^ 2 * x ^ 2) := by ring
    rw [he, hX]
    exact quadFour (cip * R * A4)
  have hXnn : 0 ≤ Real.sqrt (8 * bh) * (1 + A) * (D4 + D3 + D2 + N) :=
    mul_nonneg (mul_nonneg hsn (by linarith)) (by linarith)
  have hYnn : 0 ≤ Real.sqrt (8 * bh) * cip * R * A4 * (D3 + N) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hsn hcip) hR) hA4)
      (by linarith)
  have hX2 : 8 * bh * u ≤
      (Real.sqrt (8 * bh) * (1 + A) * (D4 + D3 + D2 + N)) ^ 2 := by
    have he : (Real.sqrt (8 * bh) * (1 + A) * (D4 + D3 + D2 + N)) ^ 2 =
        Real.sqrt (8 * bh) ^ 2 *
          ((1 + A) ^ 2 * (D4 + D3 + D2 + N) ^ 2) := by ring
    rw [he, hsq]
    exact mul_le_mul_of_nonneg_left hgeu hbh8
  have hY2 : 8 * bh * (cip * R * A4) ^ 2 * u ≤
      (Real.sqrt (8 * bh) * cip * R * A4 * (D3 + N)) ^ 2 := by
    have he : (Real.sqrt (8 * bh) * cip * R * A4 * (D3 + N)) ^ 2 =
        Real.sqrt (8 * bh) ^ 2 *
          ((cip * R * A4) ^ 2 * (D3 + N) ^ 2) := by ring
    have hcu : (cip * R * A4) ^ 2 * u ≤ (cip * R * A4) ^ 2 * (D3 + N) ^ 2 :=
      mul_le_mul_of_nonneg_left hu1 (sq_nonneg _)
    rw [he, hsq]
    have hstep := mul_le_mul_of_nonneg_left hcu hbh8
    refine le_trans (le_of_eq ?_) hstep
    ring
  have hstep1 : ((1 + x) ^ 2 * (1 + x) ^ 2) * u ≤
      (8 * (1 + (cip * R * A4) ^ 2)) * u :=
    mul_le_mul_of_nonneg_right hpl4 hu0
  have hstep2 : bh * (((1 + x) ^ 2 * (1 + x) ^ 2) * u) ≤
      bh * ((8 * (1 + (cip * R * A4) ^ 2)) * u) :=
    mul_le_mul_of_nonneg_left hstep1 hbh
  have hstep3 : bh * ((8 * (1 + (cip * R * A4) ^ 2)) * u) =
      8 * bh * u + 8 * bh * (cip * R * A4) ^ 2 * u := by ring
  have hsum := sqAdd2 hXnn hYnn
  linarith [hX2, hY2, hstep2, hsum]

omit [BoundarylessManifold I M] in
/-- The covariant jet is monotone in its order. -/
theorem jetMono
    (g : SmoothRiemannianMetric I M) {r s m n : ℕ}
    (hmn : m ≤ n) (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m S ≤
      lowJetSq (I := I) (M := M) g n S := by
  unfold lowJetSq
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.add_le_add_right hmn 1))
    (fun _ _ _ => sq_nonneg _)

/-- Slot extension costs one factor of the fibre dimension, order by order. -/
theorem slotL2
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
        (slotExtend (I := I) (M := M) g r s Φ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) *
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
      ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i Φ)).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (r + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (r + 1) (s + 1) i
      (slotExtend (I := I) (M := M) g r s Φ))
    F hF (fun x =>
      rfns_iteratedCovGrad_slotExtend_le
        (I := I) (M := M) g r s Φ i x)
  have hint : (∫ x,
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g r (s + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

/-- Slot extension costs one factor of the fibre dimension at `H²`. -/
theorem slotH2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g r s Φ) ≤
      (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g 2 Φ := by
  unfold lowJetSq
  calc
    ∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
          (slotExtend (I := I) (M := M) g r s Φ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 3, (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        slotL2 (I := I) (M := M) g r s i Φ
    _ = (Module.finrank ℝ E : ℝ) *
        ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
      rw [Finset.mul_sum]

/-- Coefficient-slot reindexing is a jet isometry. -/
theorem reindexJet
    (g : SmoothRiemannianMetric I M) {r s m : ℕ}
    (R : SmoothCcTensor g r s) (σ : Equiv.Perm (Fin r)) :
    lowJetSq (I := I) (M := M) g m
        (reindexCoeffGen (I := I) (M := M) g r s R σ) =
      lowJetSq (I := I) (M := M) g m R := by
  unfold lowJetSq
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    rfns_iteratedCovGrad_reindexCoeffGen_eq
      (I := I) (M := M) g r s R σ q x

/-- Coefficient-slot reindexing is additive. -/
theorem reindexSub
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A B : SmoothCcTensor g r s) (σ : Equiv.Perm (Fin r)) :
    reindexCoeffGen (I := I) (M := M) g r s (A - B) σ =
      reindexCoeffGen (I := I) (M := M) g r s A σ -
        reindexCoeffGen (I := I) (M := M) g r s B σ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    reindexCoeffGen_toSection, reindexCoeffGen_toSection,
    reindexCoeffGen_toSection,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply, reindexCoeffFibGen_apply,
    reindexCoeffFibGen_apply, reindexCoeffFibGen_apply,
    ContinuousLinearMap.sub_apply]

/-- The moving trace factor differences fold through the reindexing. -/
theorem trSub
    (g gT gU : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) :
    lc0TraceRF (I := I) (M := M) g gT p σ -
      lc0TraceRF (I := I) (M := M) g gU p σ =
      reindexCoeffGen (I := I) (M := M) g (p + 2) p
        (pureTrace (I := I) (M := M) g gT p -
          pureTrace (I := I) (M := M) g gU p) σ := by
  rw [lc0TraceRF, lc0TraceRF, ← reindexSub]

/-- The moving trace factor has the jet of its unpermuted trace. -/
theorem trJet
    (g gm : SmoothRiemannianMetric I M) (p m : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) :
    lowJetSq (I := I) (M := M) g m
        (lc0TraceRF (I := I) (M := M) g gm p σ) =
      lowJetSq (I := I) (M := M) g m
        (pureTrace (I := I) (M := M) g gm p) := by
  rw [lc0TraceRF, reindexJet]

/-- The `H²` jet is an algebra for `appCcRS`, in `lowJetSq` currency. -/
theorem appH2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        lowJetSq (I := I) (M := M) g 2
            (appCcRS (I := I) (M := M) g p r c Φ W) ≤
          C * lowJetSq (I := I) (M := M) g 2 Φ *
            lowJetSq (I := I) (M := M) g 2 W := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g p r c
  refine ⟨C₀ ^ 2, sq_nonneg _, ?_⟩
  intro Φ W
  have hΦ0 : 0 ≤ lowJetSq (I := I) (M := M) g 2 Φ :=
    jetNn (I := I) (M := M) g Φ
  have hW0 : 0 ≤ lowJetSq (I := I) (M := M) g 2 W :=
    jetNn (I := I) (M := M) g W
  have hsΦ :
      Real.sqrt (lowJetSq (I := I) (M := M) g 2 Φ) ^ 2 =
        lowJetSq (I := I) (M := M) g 2 Φ :=
    Real.sq_sqrt hΦ0
  have hsW :
      Real.sqrt (lowJetSq (I := I) (M := M) g 2 W) ^ 2 =
        lowJetSq (I := I) (M := M) g 2 W :=
    Real.sq_sqrt hW0
  have h := happ Φ W
    (Real.sqrt (lowJetSq (I := I) (M := M) g 2 Φ))
    (Real.sqrt (lowJetSq (I := I) (M := M) g 2 W))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (by
      unfold lowJetSq
      exact le_of_eq hsΦ.symm)
    (by
      unfold lowJetSq
      exact le_of_eq hsW.symm)
  calc
    lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g p r c Φ W) ≤
      (C₀ *
        Real.sqrt (lowJetSq (I := I) (M := M) g 2 Φ) *
        Real.sqrt (lowJetSq (I := I) (M := M) g 2 W)) ^ 2 := by
      simpa only [lowJetSq, Nat.reduceAdd] using h
    _ = C₀ ^ 2 * lowJetSq (I := I) (M := M) g 2 Φ *
        lowJetSq (I := I) (M := M) g 2 W := by
      rw [mul_pow, mul_pow, hsΦ, hsW]

omit [BoundarylessManifold I M] in
/-- **The two-arm folding of a connection-difference pair modulus.**  Both
`mcd_pair_h2` and `wXi_sub_tame` deliver `(b0·D3 + b1·D3 + b1·a·D3)²` once their
`D2` slot is fed with `D3`; against the envelope `pl2` this collapses to a
single constant times `pl2·u`.  Hoisted out of the tensor telescope so that the
modulus algebra never reaches `linarith` with tensor-sized monomials. -/
theorem pairFold3 {b0 b1 a pl2 u D3 : ℝ}
    (hpl21 : (1 : ℝ) ≤ pl2) (hplA2 : a ^ 2 ≤ pl2)
    (hu0 : 0 ≤ u) (hD3le : D3 ^ 2 ≤ u) :
    (b0 * D3 + b1 * D3 + b1 * a * D3) ^ 2 ≤
      (2 * (b0 + b1) ^ 2 + 2 * b1 ^ 2) * (pl2 * u) := by
  have hpl20 : (0 : ℝ) ≤ pl2 := le_trans zero_le_one hpl21
  have hD3u : D3 ^ 2 ≤ pl2 * u := by
    calc D3 ^ 2 ≤ u := hD3le
      _ = 1 * u := (one_mul u).symm
      _ ≤ pl2 * u := mul_le_mul_of_nonneg_right hpl21 hu0
  have hA2D : a ^ 2 * D3 ^ 2 ≤ pl2 * u := by
    have h1 : a ^ 2 * D3 ^ 2 ≤ pl2 * D3 ^ 2 :=
      mul_le_mul_of_nonneg_right hplA2 (sq_nonneg _)
    have h2 : pl2 * D3 ^ 2 ≤ pl2 * u :=
      mul_le_mul_of_nonneg_left hD3le hpl20
    linarith
  have hstep : (b0 * D3 + b1 * D3 + b1 * a * D3) ^ 2 ≤
      2 * (b0 + b1) ^ 2 * D3 ^ 2 + 2 * b1 ^ 2 * (a ^ 2 * D3 ^ 2) := by
    have hre : b0 * D3 + b1 * D3 + b1 * a * D3 =
        (b0 + b1) * D3 + b1 * a * D3 := by ring
    rw [hre]
    refine (sqTwo ((b0 + b1) * D3) (b1 * a * D3)).trans (le_of_eq ?_)
    ring
  have e1 : 2 * (b0 + b1) ^ 2 * D3 ^ 2 ≤ 2 * (b0 + b1) ^ 2 * (pl2 * u) :=
    mul_le_mul_of_nonneg_left hD3u (by positivity)
  have e2 : 2 * b1 ^ 2 * (a ^ 2 * D3 ^ 2) ≤ 2 * b1 ^ 2 * (pl2 * u) :=
    mul_le_mul_of_nonneg_left hA2D (by positivity)
  have hsum : (2 * (b0 + b1) ^ 2 + 2 * b1 ^ 2) * (pl2 * u) =
      2 * (b0 + b1) ^ 2 * (pl2 * u) + 2 * b1 ^ 2 * (pl2 * u) := by ring
  rw [hsum]
  linarith

/-! ### The `lc0VB` factor algebra

The corresponding helpers of the `H¹` chain are `private` to
`DeTurckRemainderLowBaseLip`; the facts below are re-established here at the
`H²` level.  From here on the output-slot permutation layer is used, so the
finite-dimensional completeness instance is turned on. -/

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem icgZero
    (g : SmoothRiemannianMetric I M) (r s m : ℕ) :
    iteratedCovGrad (I := I) g r s m
        (0 : SmoothCcTensor g r s) = 0 := by
  induction m with
  | zero => rw [iteratedCovGrad_zero]
  | succ m ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]

omit [BoundarylessManifold I M] in
theorem jetZero
    (g : SmoothRiemannianMetric I M) {r s m : ℕ} :
    lowJetSq (I := I) (M := M) g m
        (0 : SmoothCcTensor g r s) = 0 := by
  unfold lowJetSq
  apply Finset.sum_eq_zero
  intro q hq
  rw [icgZero, norm_zero, zero_pow (by norm_num)]

theorem wXiZero
    (g : SmoothRiemannianMetric I M) :
    wXi (I := I) (M := M) g g g = 0 := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  apply ContinuousMultilinearMap.ext
  intro m
  rw [wXi_unitModel_apply]
  simp only [PDE.DeTurck.connDiff_self, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, map_zero]
  rfl
set_option linter.unusedVariables false in
theorem wXiSelfTame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g) ≤
        (B R * A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hw⟩ :=
    wXi_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let B : ℝ → ℝ := fun R => B0 0 + B1 0 + B1 0 * R
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact add_nonneg
      (add_nonneg (hB0 0 (by norm_num)) (hB1 0 (by norm_num)))
      (mul_nonneg (hB1 0 (by norm_num)) hR)
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  let J2 : ℝ := lowJetSq (I := I) (M := M) g 2 T
  let D2 : ℝ := Real.sqrt J2
  have hJ2 : 0 ≤ J2 :=
    jetNn (I := I) (M := M) g T
  have hD2 : 0 ≤ D2 := Real.sqrt_nonneg _
  have hD2sq : D2 ^ 2 = J2 := by
    simpa only [D2] using Real.sq_sqrt hJ2
  have hJ23 : J2 ≤ lowJetSq (I := I) (M := M) g 3 T := by
    simpa only [J2] using
      jetMono (I := I) (M := M) g (by omega : 2 ≤ 3) T
  have hD2A : D2 ≤ A := by
    nlinarith
  have hD2R : D2 ≤ R := by
    have : J2 ≤ R ^ 2 := by simpa only [J2] using hT2
    nlinarith
  have hZsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g
          (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  have hZtie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  have hraw := hw gT g g T (0 : SmoothCcTensor g 0 2)
    hT hZsymm hTtie hZtie
    hδ_le hδ0 hδT hδ_le hδ0 hδZ
    0 A D2 A (by norm_num) hA hD2 hA
    (by
      rw [jetZero]
      norm_num)
    hT3
    (by
      rw [sub_zero]
      change J2 ≤ D2 ^ 2
      rw [hD2sq])
    (by simpa only [sub_zero] using hT3)
  have hraw' :
      lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g) ≤
        (B0 0 * A + B1 0 * D2 + B1 0 * A * D2) ^ 2 := by
    simpa only [wXiZero, sub_zero] using hraw
  have hB00 : 0 ≤ B0 0 := hB0 0 (by norm_num)
  have hB10 : 0 ≤ B1 0 := hB1 0 (by norm_num)
  have hmid : B1 0 * D2 ≤ B1 0 * A :=
    mul_le_mul_of_nonneg_left hD2A hB10
  have hlast : B1 0 * A * D2 ≤ B1 0 * A * R :=
    mul_le_mul_of_nonneg_left hD2R (mul_nonneg hB10 hA)
  have hlin :
      B0 0 * A + B1 0 * D2 + B1 0 * A * D2 ≤ B R * A := by
    simp only [B]
    nlinarith
  have hlin0 :
      0 ≤ B0 0 * A + B1 0 * D2 + B1 0 * A * D2 :=
    add_nonneg
      (add_nonneg (mul_nonneg hB00 hA) (mul_nonneg hB10 hD2))
      (mul_nonneg (mul_nonneg hB10 hA) hD2)
  exact hraw'.trans (pow_le_pow_left₀ hlin0 hlin 2)

theorem rspermL2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g r s i
        (rsDomDomCongrSection (I := I) (M := M) g r s σ S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s i S‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g r s σ S
      (rsDomDomCongrSection (I := I) (M := M) g r s σ S)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection,
          toModel_rsDomDomCongr_apply]) i x

theorem rspermH2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 2
        (rsDomDomCongrSection (I := I) (M := M) g r s σ S) =
      lowJetSq (I := I) (M := M) g 2 S := by
  unfold lowJetSq
  apply Finset.sum_congr rfl
  intro i _
  exact rspermL2 (I := I) (M := M) g σ S i

theorem rspermSub
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : SmoothCcTensor g r s) :
    rsDomDomCongrSection (I := I) (M := M) g r s σ (A - B) =
      rsDomDomCongrSection (I := I) (M := M) g r s σ A -
        rsDomDomCongrSection (I := I) (M := M) g r s σ B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change rsDomDomCongr σ ((A - B).toSection x) =
    rsDomDomCongr σ (A.toSection x) - rsDomDomCongr σ (B.toSection x)
  rw [show (A - B).toSection x = A.toSection x - B.toSection x from rfl]
  simp only [rsDomDomCongr]
  rfl

noncomputable def ipHead (g : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 3 1 :=
  reindexCoeffGen (I := I) (M := M) g 3 1
    (cometricDoubleTraceField (I := I) g 1) ipTracePerm

theorem ipForm
    (g : SmoothRiemannianMetric I M) (om : SmoothCcTensor g 0 1) :
    ipLowCc (I := I) (M := M) g om =
      appCcRS (I := I) (M := M) g 2 3 1 (ipHead (I := I) (M := M) g)
        (slotExtend (I := I) (M := M) g 1 2
          (slotExtend (I := I) (M := M) g 0 1 om)) := rfl

theorem ipSub
    (g : SmoothRiemannianMetric I M) (a b : SmoothCcTensor g 0 1) :
    ipLowCc (I := I) (M := M) g (a - b) =
      ipLowCc (I := I) (M := M) g a - ipLowCc (I := I) (M := M) g b := by
  rw [ipForm, ipForm, ipForm, slotExtend_sub, slotExtend_sub,
    appCcRS_sub_right]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M] in
lemma vbRank0Smul (x : M) (c : Tensor0SSpace 0 I x) :
    c = Tensor0SSpace.toModel c (fun i : Fin 0 => i.elim0) •
      unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  have h1 : Tensor0SSpace.toModel
      (unitTensor (I := I) (M := M) x) v = (1 : ℝ) := rfl
  rw [h1, mul_one]
  congr 1
  funext i
  exact i.elim0

lemma vbMcdUnit (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀) x m =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E)
          (E := (TangentSpace I : M → Type _)) x).smulRight
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ g₀ x m

lemma vbPKSlot (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (B : Tensor0SSpace 1 I x) :
    Tensor0SSpace.toModel
        (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) B) =
      Tensor0SSpace.toModel
        (slotExtendFib (I := I) (M := M) g₀ 0 3 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀).toSection x)
          B) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro u
  rw [show (u : Fin 4 → E) = Fin.cons (u 0) (Fin.tail u) from
    (Fin.cons_self_tail u).symm]
  rw [tensor0SProdKappaFib_apply, Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 0 3 x
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀).toSection x)
    B (u 0) (Fin.tail u)]
  have hc : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x B (u 0) =
      Tensor0SSpace.toModel B (fun _ : Fin 1 => u 0) •
        unitTensor (I := I) (M := M) x := by
    have h2 := vbRank0Smul (I := I) (M := M) x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x B (u 0))
    rw [h2]
    congr 1
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := B) (v0 := u 0) (vs := fun i : Fin 0 => i.elim0)]
    congr 1
    funext k
    fin_cases k
    rfl
  rw [hc, ContinuousLinearMap.map_smul, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀).toSection x)
        (unitTensor (I := I) (M := M) x)) (Fin.tail u) =
      unitModel (I := I) (M := M) g₀ 3
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀) x
        (fun j => Fin.tail u j) from by rw [unitModel]]
  rw [vbMcdUnit (I := I) (M := M) g₀ g₁ x (fun j => Fin.tail u j)]
  have hcast : ((Fin.cons (u 0) (Fin.tail u) : Fin 4 → E) ∘
      Fin.castAdd 3) = (fun _ : Fin 1 => u 0) := by
    funext i
    fin_cases i
    rfl
  have hnat : ((Fin.cons (u 0) (Fin.tail u) : Fin 4 → E) ∘
      Fin.natAdd 1) = Fin.tail u := by
    funext j
    have hj : Fin.natAdd 1 j = Fin.succ j := by
      apply Fin.ext
      simp [Fin.natAdd, Fin.succ, Nat.add_comm]
    change Fin.cons (u 0) (Fin.tail u) (Fin.natAdd 1 j) = Fin.tail u j
    rw [hj, Fin.cons_succ]
  rw [hcast, hnat]
  rw [metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ g₀ x
    (fun j => Fin.tail u j)]

lemma vbmcdRel (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∀ (y : M) (d : Tensor0SSpace 1 I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
            (vbMcdArm (I := I) (M := M) g₀ g₁).toSection y) d) =
        ContinuousMultilinearMap.domDomCongr LieCorr0Core.lieCorr0VBPerm
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
              (slotExtend (I := I) (M := M) g₀ 0 3
                (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀)).toSection
                  y) d)) := by
  intro y d
  rw [show ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
      (vbMcdArm (I := I) (M := M) g₀ g₁).toSection y) d) =
      domDomCongrFibRank (I := I) 4 LieCorr0Core.lieCorr0VBPerm y
        (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) y
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ y) d) from rfl]
  rw [domDomCongrFibRank_apply, Tensor0SSpace.toModel_ofModel]
  exact congrArg
    (ContinuousMultilinearMap.domDomCongr LieCorr0Core.lieCorr0VBPerm)
    (vbPKSlot (I := I) (M := M) g₀ g₁ y d)

theorem vbmcdPerm
    (g gm : SmoothRiemannianMetric I M) :
    vbMcdArm (I := I) (M := M) g gm =
      rsDomDomCongrSection (I := I) (M := M) g 1 4
        LieCorr0Core.lieCorr0VBPerm
        (slotExtend (I := I) (M := M) g 0 3
          (metricConnDiffLoweredCc (I := I) (M := M) g gm g)) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  beta_reduce
  rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]
  exact vbmcdRel (I := I) (M := M) g gm x d

theorem vbmcdH2
    (g gm : SmoothRiemannianMetric I M) :
    lowJetSq (I := I) (M := M) g 2 (vbMcdArm (I := I) (M := M) g gm) ≤
      (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g 2
          (metricConnDiffLoweredCc (I := I) (M := M) g gm g) := by
  rw [vbmcdPerm, rspermH2]
  exact slotH2 (I := I) (M := M) g 0 3 _

/-- The `H²` jet of the `lc0VB` head difference is dominated by the jet of the
connection-difference difference, at one factor of the fibre dimension. -/
theorem vbmcdSub
    (g gT gU : SmoothRiemannianMetric I M) :
    lowJetSq (I := I) (M := M) g 2
        (vbMcdArm (I := I) (M := M) g gT -
          vbMcdArm (I := I) (M := M) g gU) ≤
      (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g 2
          (metricConnDiffLoweredCc (I := I) (M := M) g gT g -
            metricConnDiffLoweredCc (I := I) (M := M) g gU g) := by
  rw [vbmcdPerm, vbmcdPerm, ← rspermSub, ← slotExtend_sub, rspermH2]
  exact slotH2 (I := I) (M := M) g 0 3 _

theorem riemLiveEq
    (g gm : SmoothRiemannianMetric I M) :
    lc0RiemLive (I := I) (M := M) g gm =
      pureTrace (I := I) (M := M) g gm 2 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0RiemLive (I := I) (M := M) g gm).toSection x) =
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (pureTrace (I := I) (M := M) g gm 2).toSection x)
  calc
    _ = cometricDoubleTraceFib (I := I) gm 2 x :=
      lc0RiemLive_fiber (I := I) (M := M) g gm x
    _ = _ := (pureTrace_toSection
      (I := I) (M := M) g gm 2 x).symm

set_option maxHeartbeats 6400000 in
set_option linter.unusedVariables false in
/-- **Class 3 of the `H²` five-class telescope** — the vector-bundle zero head
`lc0VB`.  On a common spectral `H²` ball the difference of the two realized
states obeys the admissible second-order modulus
`(B0 R · (1+A) · (D4+D3+D2+N) + B1 R · A4 · (D3+N))²`. -/
theorem vbH2Pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 2
          (lc0VB (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδT hδZ s) -
            lc0VB (I := I) (M := M) g
              (realizedFam (I := I) g U 0 hδU hδZ s)) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 := by
  obtain ⟨Cout, hCout, happOut⟩ := appH2 (I := I) (M := M) hDim g 2 4 2
  obtain ⟨Cin, hCin, happIn⟩ := appH2 (I := I) (M := M) hDim g 2 1 4
  obtain ⟨Cipp, hCipp, happIp⟩ := appH2 (I := I) (M := M) hDim g 2 3 1
  obtain ⟨Cw, hCw, happW⟩ := appH2 (I := I) (M := M) hDim g 0 3 1
  obtain ⟨ρt1, Ct1, hρt1, hCt1, htp1⟩ :=
    LowBaseInternal.trace1_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb1, Bt1, hρb1, hBt1, htb1⟩ :=
    LowBaseInternal.trace1_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨ρt2, Ct2, hρt2, hCt2, htp2⟩ :=
    LowBaseInternal.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb2, Bt2, hρb2, hBt2, htb2⟩ :=
    LowBaseInternal.trace2_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨B0m, B1m, hB0m, hB1m, hmcdp⟩ :=
    LowBaseInternal.mcd_pair_h2 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bm, hBm, hmcdb⟩ :=
    LowBaseInternal.mcd_h2_bdd (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨W0, W1, hW0, hW1, hwxip⟩ :=
    wXi_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bs, hBs, hwxib⟩ := wXiSelfTame (I := I) (M := M) hDim g
  obtain ⟨Cip, hCip, hinterp⟩ := jetInterp3 (I := I) (M := M) g 2
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hfr2 : (0 : ℝ) ≤ fr ^ 2 := sq_nonneg _
  set Jp : ℝ := lowJetSq (I := I) (M := M) g 2 (ipHead (I := I) (M := M) g)
    with hJpdef
  have hJp : 0 ≤ Jp := jetNn (I := I) (M := M) (m := 2) g _
  set ρ : ℝ := min (min ρt1 ρb1) (min ρt2 ρb2) with hρdef
  have hρ0 : 0 < ρ :=
    lt_min (lt_min hρt1 hρb1) (lt_min hρt2 hρb2)
  let Cs : ℝ → ℝ := fun R => (Bs R) ^ 2
  let M5 : ℝ → ℝ := fun R => 2 * (B0m R + B1m R) ^ 2 + 2 * (B1m R) ^ 2
  let M5w : ℝ → ℝ := fun R => 2 * (W0 R + W1 R) ^ 2 + 2 * (W1 R) ^ 2
  let Wb : ℝ → ℝ := fun R => Cw * Bt1 ^ 2 * Cs R
  let Wm : ℝ → ℝ := fun R =>
    2 * (Cw * Ct1 ^ 2 * Cs R + Cw * Bt1 ^ 2 * M5w R)
  let Ib : ℝ → ℝ := fun R => Cipp * Jp * fr ^ 2 * Wb R
  let Im : ℝ → ℝ := fun R => Cipp * Jp * fr ^ 2 * Wm R
  let Vb : ℝ → ℝ := fun R => fr * (Bm R) ^ 2
  let Vd : ℝ → ℝ := fun R => fr * M5 R
  let Sin : ℝ → ℝ := fun R => Cin * Vb R * Ib R
  let Kv : ℝ → ℝ := fun R => Cin * Vd R * Ib R
  let Ki : ℝ → ℝ := fun R => Cin * Vb R * Im R
  let K1 : ℝ → ℝ := fun R => Cout * Ct2 ^ 2 * Sin R
  let K2 : ℝ → ℝ := fun R => Cout * Bt2 ^ 2 * (2 * (Kv R + Ki R))
  let Bh : ℝ → ℝ := fun R => 4 * (2 * (K1 R + K2 R))
  let B0 : ℝ → ℝ := fun R => Real.sqrt (8 * Bh R)
  let B1 : ℝ → ℝ := fun R => Real.sqrt (8 * Bh R) * Cip * R
  have hCs : ∀ R : ℝ, 0 ≤ R → 0 ≤ Cs R := fun R hR => sq_nonneg _
  have hM5 : ∀ R : ℝ, 0 ≤ R → 0 ≤ M5 R := fun R hR => by
    have h1 : (0 : ℝ) ≤ 2 * (B0m R + B1m R) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (B1m R) ^ 2 := by positivity
    simp only [M5]
    linarith
  have hM5w : ∀ R : ℝ, 0 ≤ R → 0 ≤ M5w R := fun R hR => by
    have h1 : (0 : ℝ) ≤ 2 * (W0 R + W1 R) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (W1 R) ^ 2 := by positivity
    simp only [M5w]
    linarith
  have hWb : ∀ R : ℝ, 0 ≤ R → 0 ≤ Wb R := fun R hR =>
    mul_nonneg (mul_nonneg hCw (sq_nonneg _)) (hCs R hR)
  have hWm : ∀ R : ℝ, 0 ≤ R → 0 ≤ Wm R := fun R hR => by
    have h1 : (0 : ℝ) ≤ Cw * Ct1 ^ 2 * Cs R :=
      mul_nonneg (mul_nonneg hCw (sq_nonneg _)) (hCs R hR)
    have h2 : (0 : ℝ) ≤ Cw * Bt1 ^ 2 * M5w R :=
      mul_nonneg (mul_nonneg hCw (sq_nonneg _)) (hM5w R hR)
    simp only [Wm]
    linarith
  have hIb : ∀ R : ℝ, 0 ≤ R → 0 ≤ Ib R := fun R hR =>
    mul_nonneg (mul_nonneg (mul_nonneg hCipp hJp) hfr2) (hWb R hR)
  have hIm : ∀ R : ℝ, 0 ≤ R → 0 ≤ Im R := fun R hR =>
    mul_nonneg (mul_nonneg (mul_nonneg hCipp hJp) hfr2) (hWm R hR)
  have hVb : ∀ R : ℝ, 0 ≤ R → 0 ≤ Vb R := fun R hR =>
    mul_nonneg hfr (sq_nonneg _)
  have hVd : ∀ R : ℝ, 0 ≤ R → 0 ≤ Vd R := fun R hR =>
    mul_nonneg hfr (hM5 R hR)
  have hSin : ∀ R : ℝ, 0 ≤ R → 0 ≤ Sin R := fun R hR =>
    mul_nonneg (mul_nonneg hCin (hVb R hR)) (hIb R hR)
  have hKv : ∀ R : ℝ, 0 ≤ R → 0 ≤ Kv R := fun R hR =>
    mul_nonneg (mul_nonneg hCin (hVd R hR)) (hIb R hR)
  have hKi : ∀ R : ℝ, 0 ≤ R → 0 ≤ Ki R := fun R hR =>
    mul_nonneg (mul_nonneg hCin (hVb R hR)) (hIm R hR)
  have hK1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K1 R := fun R hR =>
    mul_nonneg (mul_nonneg hCout (sq_nonneg _)) (hSin R hR)
  have hK2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K2 R := fun R hR =>
    mul_nonneg (mul_nonneg hCout (sq_nonneg _))
      (by
        have := hKv R hR
        have := hKi R hR
        linarith)
  have hBhnn : ∀ R : ℝ, 0 ≤ R → 0 ≤ Bh R := fun R hR => by
    have := hK1 R hR
    have := hK2 R hR
    simp only [Bh]
    linarith
  refine ⟨ρ, B0, B1, hρ0,
    fun R hR => by
      simp only [B0]
      exact Real.sqrt_nonneg _,
    fun R hR => by
      simp only [B1]
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCip) hR, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith [hs.1, hs.2]
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem
        (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem
        (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : lowJetSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : lowJetSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP4 : lowJetSq (I := I) (M := M) g 4 P ≤ A4 ^ 2 := by
    rw [hcP, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 4) g T) hs2).trans hT4
  have hQ4 : lowJetSq (I := I) (M := M) g 4 Q ≤ A4 ^ 2 := by
    rw [hcQ, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 4) g U) hs2).trans hU4
  have hPQ3 : lowJetSq (I := I) (M := M) g 3 (P - Q) ≤ D3 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, jetSmul]
    exact (mul_le_of_le_one_left
      (jetNn (I := I) (M := M) (m := 3) g (T - U)) hs2).trans hTU3
  have hPQ2 : lowJetSq (I := I) (M := M) g 2 (P - Q) ≤ D3 ^ 2 :=
    (jetMono (I := I) (M := M) g (by norm_num : (2 : ℕ) ≤ 3) (P - Q)).trans hPQ3
  have hball : ∀ ρ' : ℝ, ρ ≤ ρ' →
      (‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ' ∧
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ') := by
    intro ρ' hρ'
    constructor
    · rw [hcP, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hTn.trans hρ'))
    · rw [hcQ, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hUn.trans hρ'))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  -- the interpolated third-jet size of the two states
  set a : ℝ := Real.sqrt (Cip * (R * A4)) with hadef
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hasq : a ^ 2 = Cip * (R * A4) :=
    Real.sq_sqrt (mul_nonneg hCip (mul_nonneg hR hA4))
  have hP3i : lowJetSq (I := I) (M := M) g 3 P ≤ a ^ 2 := by
    rw [hasq]
    exact hinterp P R A4 hR hA4 hP2 hP4
  have hQ3i : lowJetSq (I := I) (M := M) g 3 Q ≤ a ^ 2 := by
    rw [hasq]
    exact hinterp Q R A4 hR hA4 hQ2 hQ4
  set pl2 : ℝ := (1 + a) ^ 2 with hpl2
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    nlinarith [ha0]
  have hpl20 : 0 ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : a ^ 2 ≤ pl2 := by
    rw [hpl2]
    nlinarith [ha0]
  set u : ℝ := D3 ^ 2 + N ^ 2 with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  have hD3le : D3 ^ 2 ≤ u := by
    rw [hu]
    linarith [sq_nonneg N]
  have hD3u : D3 ^ 2 ≤ pl2 * u := by
    calc D3 ^ 2 ≤ u := hD3le
      _ = 1 * u := (one_mul u).symm
      _ ≤ pl2 * u := mul_le_mul_of_nonneg_right hpl21 hu0
  have hNu : N ^ 2 ≤ u := by
    rw [hu]
    linarith [sq_nonneg D3]
  have hpl2u : 0 ≤ pl2 * u := mul_nonneg hpl20 hu0
  -- the moving factors
  set mcdT : SmoothCcTensor g 0 3 :=
    metricConnDiffLoweredCc (I := I) (M := M) g gmT g with hmT
  set mcdU : SmoothCcTensor g 0 3 :=
    metricConnDiffLoweredCc (I := I) (M := M) g gmU g with hmU
  set cdT : SmoothCcTensor g 0 3 :=
    connDiffLoweredCc (I := I) g gmT with hcdT
  set cdU : SmoothCcTensor g 0 3 :=
    connDiffLoweredCc (I := I) g gmU with hcdU
  set Tr1T : SmoothCcTensor g 3 1 :=
    lc0TraceRF (I := I) (M := M) g gmT 1 (Equiv.refl (Fin 3)) with hTr1T
  set Tr1U : SmoothCcTensor g 3 1 :=
    lc0TraceRF (I := I) (M := M) g gmU 1 (Equiv.refl (Fin 3)) with hTr1U
  set WT : SmoothCcTensor g 0 1 :=
    wOmega (I := I) (M := M) g gmT g with hWTdef
  set WU : SmoothCcTensor g 0 1 :=
    wOmega (I := I) (M := M) g gmU g with hWUdef
  set IpT : SmoothCcTensor g 2 1 := ipLowCc (I := I) (M := M) g WT with hIpT
  set IpU : SmoothCcTensor g 2 1 := ipLowCc (I := I) (M := M) g WU with hIpU
  set VmT : SmoothCcTensor g 1 4 := vbMcdArm (I := I) (M := M) g gmT with hVmT
  set VmU : SmoothCcTensor g 1 4 := vbMcdArm (I := I) (M := M) g gmU with hVmU
  set LvT : SmoothCcTensor g 4 2 :=
    lc0RiemLive (I := I) (M := M) g gmT with hLvT
  set LvU : SmoothCcTensor g 4 2 :=
    lc0RiemLive (I := I) (M := M) g gmU with hLvU
  set InT : SmoothCcTensor g 2 4 :=
    appCcRS (I := I) (M := M) g 2 1 4 VmT IpT with hInT
  set InU : SmoothCcTensor g 2 4 :=
    appCcRS (I := I) (M := M) g 2 1 4 VmU IpU with hInU
  -- trace moduli (ρ-cascade)
  have hρc : ρ ≤ ρt1 ∧ ρ ≤ ρb1 ∧ ρ ≤ ρt2 ∧ ρ ≤ ρb2 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · rw [hρdef]
        first
        | exact le_trans (min_le_left _ _) (min_le_left _ _)
        | exact le_trans (min_le_left _ _) (min_le_right _ _)
        | exact le_trans (min_le_right _ _) (min_le_left _ _)
        | exact le_trans (min_le_right _ _) (min_le_right _ _)
  have htrp : ∀ (p : ℕ) (Cp : ℝ) (ρp' : ℝ),
      (∀ (T' U' : SmoothCcTensor g 0 2)
        (gT' gU' : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T' y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g U' y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ ρp' →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U'‖ ≤ ρp' →
        lowJetSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT' p -
              pureTrace (I := I) (M := M) g gU' p) ≤
          (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T' - U')‖) ^ 2) →
      0 ≤ Cp → ρ ≤ ρp' →
      lowJetSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmT p -
            pureTrace (I := I) (M := M) g gmU p) ≤
        Cp ^ 2 * u := by
    intro p Cp ρp' hpair hCp hρp'
    obtain ⟨hPn, hQn⟩ := hball ρp' hρp'
    have h := hpair P Q gmT gmU hPtie hQtie hPn hQn
    refine h.trans ?_
    have h1 : Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖ ≤ Cp * N :=
      mul_le_mul_of_nonneg_left hPQn hCp
    have h2 : (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖) ^ 2 ≤ (Cp * N) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hCp (norm_nonneg _)) h1 2
    refine h2.trans ?_
    have he : (Cp * N) ^ 2 = Cp ^ 2 * N ^ 2 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hNu (sq_nonneg Cp)
  have htrb : ∀ (p : ℕ) (Bp : ℝ) (ρp' : ℝ),
      (∀ (T' : SmoothCcTensor g 0 2)
        (gT' : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T' y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ ρp' →
        lowJetSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT' p) ≤ Bp ^ 2) →
      ρ ≤ ρp' →
      (lowJetSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmT p) ≤ Bp ^ 2 ∧
        lowJetSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmU p) ≤ Bp ^ 2) := by
    intro p Bp ρp' hbdd hρp'
    obtain ⟨hPn, hQn⟩ := hball ρp' hρp'
    exact ⟨hbdd P gmT hPtie hPn, hbdd Q gmU hQtie hQn⟩
  have htp1' := htrp 1 Ct1 ρt1 htp1 hCt1 hρc.1
  have htb1' := htrb 1 Bt1 ρb1 htb1 hρc.2.1
  have htp2' := htrp 2 Ct2 ρt2 htp2 hCt2 hρc.2.2.1
  have htb2' := htrb 2 Bt2 ρb2 htb2 hρc.2.2.2
  -- the two connection-difference producers
  have hmbT : lowJetSq (I := I) (M := M) g 2 mcdT ≤ (Bm R) ^ 2 * pl2 := by
    have h := hmcdb gmT P hPsymm hPtie hδ_le hδ0 hδP R a hR ha0 hP2 hP3i
    rw [hmT]
    refine h.trans (le_of_eq ?_)
    rw [hpl2]
    ring
  have hmbU : lowJetSq (I := I) (M := M) g 2 mcdU ≤ (Bm R) ^ 2 * pl2 := by
    have h := hmcdb gmU Q hQsymm hQtie hδ_le hδ0 hδQ R a hR ha0 hQ2 hQ3i
    rw [hmU]
    refine h.trans (le_of_eq ?_)
    rw [hpl2]
    ring
  have hmpd : lowJetSq (I := I) (M := M) g 2 (mcdT - mcdU) ≤
      M5 R * (pl2 * u) := by
    have h := hmcdp gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R a D3 D3 hR ha0 hD3 hD3 hQ2 hP3i hPQ2 hPQ3
    rw [hmT, hmU]
    refine h.trans ?_
    refine (pairFold3 (b0 := B0m R) (b1 := B1m R) (a := a) (pl2 := pl2)
      (u := u) (D3 := D3) hpl21 hplA2 hu0 hD3le).trans (le_of_eq ?_)
    simp only [M5]
  have hcdT2 : lowJetSq (I := I) (M := M) g 2 cdT ≤ Cs R * pl2 := by
    rw [hcdT, ← wXi_self_eq (I := I) (M := M) g gmT]
    refine (hwxib gmT P hPsymm hPtie hδ_le hδ0 hδP hδZ R a hR ha0
      hP2 hP3i).trans ?_
    have he : (Bs R * a) ^ 2 = (Bs R) ^ 2 * a ^ 2 := by ring
    rw [he]
    refine (mul_le_mul_of_nonneg_left hplA2 (sq_nonneg (Bs R))).trans
      (le_of_eq ?_)
    simp only [Cs]
  have hcdd2 : lowJetSq (I := I) (M := M) g 2 (cdT - cdU) ≤
      M5w R * (pl2 * u) := by
    rw [hcdT, hcdU, ← wXi_self_eq (I := I) (M := M) g gmT,
      ← wXi_self_eq (I := I) (M := M) g gmU]
    refine (hwxip gmT gmU g P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R a D3 D3 hR ha0 hD3 hD3
      hQ2 hP3i hPQ2 hPQ3).trans ?_
    refine (pairFold3 (b0 := W0 R) (b1 := W1 R) (a := a) (pl2 := pl2)
      (u := u) (D3 := D3) hpl21 hplA2 hu0 hD3le).trans (le_of_eq ?_)
    simp only [M5w]
  -- level ω : `wOmega`
  have hTr1T2 : lowJetSq (I := I) (M := M) g 2 Tr1T ≤ Bt1 ^ 2 := by
    rw [hTr1T, trJet]
    exact htb1'.1
  have hTr1U2 : lowJetSq (I := I) (M := M) g 2 Tr1U ≤ Bt1 ^ 2 := by
    rw [hTr1U, trJet]
    exact htb1'.2
  have hTr1d2 : lowJetSq (I := I) (M := M) g 2 (Tr1T - Tr1U) ≤
      Ct1 ^ 2 * u := by
    rw [hTr1T, hTr1U, trSub, reindexJet]
    exact htp1'
  have hWTform : WT = appCcRS (I := I) (M := M) g 0 3 1 Tr1T cdT := by
    rw [hWTdef, hTr1T, hcdT, wOmega_refold]
  have hWUform : WU = appCcRS (I := I) (M := M) g 0 3 1 Tr1U cdU := by
    rw [hWUdef, hTr1U, hcdU, wOmega_refold]
  have hWT2 : lowJetSq (I := I) (M := M) g 2 WT ≤ Wb R * pl2 := by
    rw [hWTform]
    refine (happW Tr1T cdT).trans ?_
    calc
      Cw * lowJetSq (I := I) (M := M) g 2 Tr1T *
          lowJetSq (I := I) (M := M) g 2 cdT ≤
          Cw * Bt1 ^ 2 * (Cs R * pl2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hTr1T2 hCw) hcdT2
          (jetNn (I := I) (M := M) (m := 2) g cdT)
          (mul_nonneg hCw (sq_nonneg _))
      _ = Wb R * pl2 := by
        simp only [Wb]
        ring
  have hWd2 : lowJetSq (I := I) (M := M) g 2 (WT - WU) ≤ Wm R * (pl2 * u) := by
    have hdel : WT - WU =
        appCcRS (I := I) (M := M) g 0 3 1 (Tr1T - Tr1U) cdT +
          appCcRS (I := I) (M := M) g 0 3 1 Tr1U (cdT - cdU) := by
      rw [hWTform, hWUform, appCcRS_sub_left, appCcRS_sub_right]
      module
    rw [hdel]
    have h1 : lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 0 3 1 (Tr1T - Tr1U) cdT) ≤
        Cw * Ct1 ^ 2 * Cs R * (pl2 * u) := by
      refine (happW _ cdT).trans ?_
      calc
        Cw * lowJetSq (I := I) (M := M) g 2 (Tr1T - Tr1U) *
            lowJetSq (I := I) (M := M) g 2 cdT ≤
            Cw * (Ct1 ^ 2 * u) * (Cs R * pl2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hTr1d2 hCw) hcdT2
            (jetNn (I := I) (M := M) (m := 2) g cdT)
            (mul_nonneg hCw (mul_nonneg (sq_nonneg _) hu0))
        _ = Cw * Ct1 ^ 2 * Cs R * (pl2 * u) := by ring
    have h2 : lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 0 3 1 Tr1U (cdT - cdU)) ≤
        Cw * Bt1 ^ 2 * M5w R * (pl2 * u) := by
      refine (happW Tr1U _).trans ?_
      calc
        Cw * lowJetSq (I := I) (M := M) g 2 Tr1U *
            lowJetSq (I := I) (M := M) g 2 (cdT - cdU) ≤
            Cw * Bt1 ^ 2 * (M5w R * (pl2 * u)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hTr1U2 hCw) hcdd2
            (jetNn (I := I) (M := M) (m := 2) g _)
            (mul_nonneg hCw (sq_nonneg _))
        _ = Cw * Bt1 ^ 2 * M5w R * (pl2 * u) := by ring
    calc
      lowJetSq (I := I) (M := M) g 2 (_ + _) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 _ +
          lowJetSq (I := I) (M := M) g 2 _) :=
        jetAdd (I := I) (M := M) g 2 _ _
      _ ≤ 2 * (Cw * Ct1 ^ 2 * Cs R * (pl2 * u) +
          Cw * Bt1 ^ 2 * M5w R * (pl2 * u)) := by
        linarith [h1, h2]
      _ = Wm R * (pl2 * u) := by
        simp only [Wm]
        ring
  -- level ip : `ipLowCc`
  have hIpT2 : lowJetSq (I := I) (M := M) g 2 IpT ≤ Ib R * pl2 := by
    rw [hIpT, ipForm]
    refine (happIp (ipHead (I := I) (M := M) g) _).trans ?_
    have hslot : lowJetSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 2
          (slotExtend (I := I) (M := M) g 0 1 WT)) ≤
        fr * (fr * lowJetSq (I := I) (M := M) g 2 WT) :=
      le_trans (slotH2 (I := I) (M := M) g 1 2 _)
        (mul_le_mul_of_nonneg_left (slotH2 (I := I) (M := M) g 0 1 _) hfr)
    calc
      Cipp * lowJetSq (I := I) (M := M) g 2 (ipHead (I := I) (M := M) g) *
          lowJetSq (I := I) (M := M) g 2
            (slotExtend (I := I) (M := M) g 1 2
              (slotExtend (I := I) (M := M) g 0 1 WT)) ≤
          Cipp * Jp * (fr * (fr * (Wb R * pl2))) := by
        refine mul_le_mul (le_of_eq (by rw [hJpdef]))
          (le_trans hslot
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hWT2 hfr) hfr))
          (jetNn (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCipp hJp)
      _ = Ib R * pl2 := by
        simp only [Ib]
        ring
  have hIpd2 : lowJetSq (I := I) (M := M) g 2 (IpT - IpU) ≤
      Im R * (pl2 * u) := by
    rw [hIpT, hIpU, ← ipSub, ipForm]
    refine (happIp (ipHead (I := I) (M := M) g) _).trans ?_
    have hslot : lowJetSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 2
          (slotExtend (I := I) (M := M) g 0 1 (WT - WU))) ≤
        fr * (fr * lowJetSq (I := I) (M := M) g 2 (WT - WU)) :=
      le_trans (slotH2 (I := I) (M := M) g 1 2 _)
        (mul_le_mul_of_nonneg_left (slotH2 (I := I) (M := M) g 0 1 _) hfr)
    calc
      Cipp * lowJetSq (I := I) (M := M) g 2 (ipHead (I := I) (M := M) g) *
          lowJetSq (I := I) (M := M) g 2
            (slotExtend (I := I) (M := M) g 1 2
              (slotExtend (I := I) (M := M) g 0 1 (WT - WU))) ≤
          Cipp * Jp * (fr * (fr * (Wm R * (pl2 * u)))) := by
        refine mul_le_mul (le_of_eq (by rw [hJpdef]))
          (le_trans hslot
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hWd2 hfr) hfr))
          (jetNn (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCipp hJp)
      _ = Im R * (pl2 * u) := by
        simp only [Im]
        ring
  -- level vbMcd
  have hVmT2 : lowJetSq (I := I) (M := M) g 2 VmT ≤ Vb R * pl2 := by
    rw [hVmT]
    refine (vbmcdH2 (I := I) (M := M) g gmT).trans ?_
    calc
      fr * lowJetSq (I := I) (M := M) g 2
          (metricConnDiffLoweredCc (I := I) (M := M) g gmT g) ≤
          fr * ((Bm R) ^ 2 * pl2) := by
        have h := hmbT
        rw [hmT] at h
        exact mul_le_mul_of_nonneg_left h hfr
      _ = Vb R * pl2 := by
        simp only [Vb]
        ring
  have hVmU2 : lowJetSq (I := I) (M := M) g 2 VmU ≤ Vb R * pl2 := by
    rw [hVmU]
    refine (vbmcdH2 (I := I) (M := M) g gmU).trans ?_
    calc
      fr * lowJetSq (I := I) (M := M) g 2
          (metricConnDiffLoweredCc (I := I) (M := M) g gmU g) ≤
          fr * ((Bm R) ^ 2 * pl2) := by
        have h := hmbU
        rw [hmU] at h
        exact mul_le_mul_of_nonneg_left h hfr
      _ = Vb R * pl2 := by
        simp only [Vb]
        ring
  have hVmd2 : lowJetSq (I := I) (M := M) g 2 (VmT - VmU) ≤
      Vd R * (pl2 * u) := by
    rw [hVmT, hVmU]
    refine (vbmcdSub (I := I) (M := M) g gmT gmU).trans ?_
    calc
      fr * lowJetSq (I := I) (M := M) g 2
          (metricConnDiffLoweredCc (I := I) (M := M) g gmT g -
            metricConnDiffLoweredCc (I := I) (M := M) g gmU g) ≤
          fr * (M5 R * (pl2 * u)) := by
        have h := hmpd
        rw [hmT, hmU] at h
        exact mul_le_mul_of_nonneg_left h hfr
      _ = Vd R * (pl2 * u) := by
        simp only [Vd]
        ring
  -- level In (inner `appCcRS`)
  have hInT2 : lowJetSq (I := I) (M := M) g 2 InT ≤ Sin R * (pl2 * pl2) := by
    rw [hInT]
    refine (happIn VmT IpT).trans ?_
    calc
      Cin * lowJetSq (I := I) (M := M) g 2 VmT *
          lowJetSq (I := I) (M := M) g 2 IpT ≤
          Cin * (Vb R * pl2) * (Ib R * pl2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hVmT2 hCin) hIpT2
          (jetNn (I := I) (M := M) (m := 2) g IpT)
          (mul_nonneg hCin (mul_nonneg (hVb R hR) hpl20))
      _ = Sin R * (pl2 * pl2) := by
        simp only [Sin]
        ring
  have hInd2 : lowJetSq (I := I) (M := M) g 2 (InT - InU) ≤
      2 * (Kv R * ((pl2 * pl2) * u) + Ki R * ((pl2 * pl2) * u)) := by
    have hdel : InT - InU =
        appCcRS (I := I) (M := M) g 2 1 4 (VmT - VmU) IpT +
          appCcRS (I := I) (M := M) g 2 1 4 VmU (IpT - IpU) := by
      rw [hInT, hInU, appCcRS_sub_left, appCcRS_sub_right]
      module
    rw [hdel]
    have h1 : lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 2 1 4 (VmT - VmU) IpT) ≤
        Kv R * ((pl2 * pl2) * u) := by
      refine (happIn (VmT - VmU) IpT).trans ?_
      calc
        Cin * lowJetSq (I := I) (M := M) g 2 (VmT - VmU) *
            lowJetSq (I := I) (M := M) g 2 IpT ≤
            Cin * (Vd R * (pl2 * u)) * (Ib R * pl2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hVmd2 hCin) hIpT2
            (jetNn (I := I) (M := M) (m := 2) g IpT)
            (mul_nonneg hCin (mul_nonneg (hVd R hR) hpl2u))
        _ = Kv R * ((pl2 * pl2) * u) := by
          simp only [Kv]
          ring
    have h2 : lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 2 1 4 VmU (IpT - IpU)) ≤
        Ki R * ((pl2 * pl2) * u) := by
      refine (happIn VmU (IpT - IpU)).trans ?_
      calc
        Cin * lowJetSq (I := I) (M := M) g 2 VmU *
            lowJetSq (I := I) (M := M) g 2 (IpT - IpU) ≤
            Cin * (Vb R * pl2) * (Im R * (pl2 * u)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hVmU2 hCin) hIpd2
            (jetNn (I := I) (M := M) (m := 2) g _)
            (mul_nonneg hCin (mul_nonneg (hVb R hR) hpl20))
        _ = Ki R * ((pl2 * pl2) * u) := by
          simp only [Ki]
          ring
    calc
      lowJetSq (I := I) (M := M) g 2 (_ + _) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 _ +
          lowJetSq (I := I) (M := M) g 2 _) :=
        jetAdd (I := I) (M := M) g 2 _ _
      _ ≤ 2 * (Kv R * ((pl2 * pl2) * u) + Ki R * ((pl2 * pl2) * u)) := by
        linarith [h1, h2]
  -- level Lv (outer live trace) and the outer telescope
  have hLvd2 : lowJetSq (I := I) (M := M) g 2 (LvT - LvU) ≤ Ct2 ^ 2 * u := by
    rw [hLvT, hLvU, riemLiveEq, riemLiveEq]
    exact htp2'
  have hLvU2 : lowJetSq (I := I) (M := M) g 2 LvU ≤ Bt2 ^ 2 := by
    rw [hLvU, riemLiveEq]
    exact htb2'.2
  have hFormT : lc0VB (I := I) (M := M) g gmT =
      (2 : ℝ) • appCcRS (I := I) (M := M) g 2 4 2 LvT InT := by
    rw [hLvT, hInT, hVmT, hIpT, hWTdef, vb_refold_rf, lc0VBFormRF]
  have hFormU : lc0VB (I := I) (M := M) g gmU =
      (2 : ℝ) • appCcRS (I := I) (M := M) g 2 4 2 LvU InU := by
    rw [hLvU, hInU, hVmU, hIpU, hWUdef, vb_refold_rf, lc0VBFormRF]
  have hdel1 : lc0VB (I := I) (M := M) g gmT -
      lc0VB (I := I) (M := M) g gmU =
      (2 : ℝ) • (appCcRS (I := I) (M := M) g 2 4 2 (LvT - LvU) InT +
        appCcRS (I := I) (M := M) g 2 4 2 LvU (InT - InU)) := by
    rw [hFormT, hFormU, appCcRS_sub_left, appCcRS_sub_right]
    module
  have h1 : lowJetSq (I := I) (M := M) g 2
      (appCcRS (I := I) (M := M) g 2 4 2 (LvT - LvU) InT) ≤
      K1 R * ((pl2 * pl2) * u) := by
    refine (happOut (LvT - LvU) InT).trans ?_
    calc
      Cout * lowJetSq (I := I) (M := M) g 2 (LvT - LvU) *
          lowJetSq (I := I) (M := M) g 2 InT ≤
          Cout * (Ct2 ^ 2 * u) * (Sin R * (pl2 * pl2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hLvd2 hCout) hInT2
          (jetNn (I := I) (M := M) (m := 2) g InT)
          (mul_nonneg hCout (mul_nonneg (sq_nonneg _) hu0))
      _ = K1 R * ((pl2 * pl2) * u) := by
        simp only [K1]
        ring
  have h2 : lowJetSq (I := I) (M := M) g 2
      (appCcRS (I := I) (M := M) g 2 4 2 LvU (InT - InU)) ≤
      K2 R * ((pl2 * pl2) * u) := by
    refine (happOut LvU (InT - InU)).trans ?_
    calc
      Cout * lowJetSq (I := I) (M := M) g 2 LvU *
          lowJetSq (I := I) (M := M) g 2 (InT - InU) ≤
          Cout * Bt2 ^ 2 *
            (2 * (Kv R * ((pl2 * pl2) * u) + Ki R * ((pl2 * pl2) * u))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hLvU2 hCout) hInd2
          (jetNn (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCout (sq_nonneg _))
      _ = K2 R * ((pl2 * pl2) * u) := by
        simp only [K2]
        ring
  have hsum : lowJetSq (I := I) (M := M) g 2
      (appCcRS (I := I) (M := M) g 2 4 2 (LvT - LvU) InT +
        appCcRS (I := I) (M := M) g 2 4 2 LvU (InT - InU)) ≤
      2 * (K1 R * ((pl2 * pl2) * u) + K2 R * ((pl2 * pl2) * u)) := by
    calc
      lowJetSq (I := I) (M := M) g 2 (_ + _) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 _ +
          lowJetSq (I := I) (M := M) g 2 _) :=
        jetAdd (I := I) (M := M) g 2 _ _
      _ ≤ 2 * (K1 R * ((pl2 * pl2) * u) + K2 R * ((pl2 * pl2) * u)) := by
        linarith [h1, h2]
  have hwhole : lowJetSq (I := I) (M := M) g 2
      (lc0VB (I := I) (M := M) g gmT - lc0VB (I := I) (M := M) g gmU) ≤
      Bh R * ((pl2 * pl2) * u) := by
    rw [hdel1, jetSmul]
    have h4 : ((2 : ℝ)) ^ 2 = 4 := by norm_num
    rw [h4]
    calc
      (4 : ℝ) * lowJetSq (I := I) (M := M) g 2
          (appCcRS (I := I) (M := M) g 2 4 2 (LvT - LvU) InT +
            appCcRS (I := I) (M := M) g 2 4 2 LvU (InT - InU)) ≤
          4 * (2 * (K1 R * ((pl2 * pl2) * u) +
            K2 R * ((pl2 * pl2) * u))) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = Bh R * ((pl2 * pl2) * u) := by
        simp only [Bh]
        ring
  refine hwhole.trans ?_
  rw [hpl2, hu]
  simp only [B0, B1]
  exact amixScalar (hBhnn R hR) hCip hR hA hA4 hD2 hD3 hD4 hN hasq

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
