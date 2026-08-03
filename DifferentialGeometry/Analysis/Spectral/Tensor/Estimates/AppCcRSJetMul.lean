import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H1H2AppCcRS

/-!
# All-order product jet estimate for the mixed operator-field action `appCcRS`

The `appCc`/`appCcRS` estimate family in this directory is stocked at *fixed*
jet order: `appRS_h1_h2_h1`, `appRS_h2_h1_h1` and `appRS_h2_h2_h2` all pin the
covariant `L2` jet window to order one or two.  Everything that consumes them
downstream (the `app_h2_mul`-style product bounds of the DeTurck low-base
action) is therefore fixed-order too, which is what blocks an all-order jet
tower for the DeTurck remainder coefficients.

This file supplies the order-generic members.  Three statements, in increasing
strength of hypothesis:

* `appRS_hn_sup` — the engine.  For every order `n`, the order-`n` covariant
  `L2` jet of `appCcRS g p r c Φ W` is bounded by the **Moser pairing**
  `C n * (B² · jet_n Φ + A² · jet_n W)`, where `A`, `B` are pointwise fibre
  bounds for `Φ`, `W`.  No dimension hypothesis, no order gate, and *sharp in
  the jet order*: order `n` on the right for order `n` on the left.
* `appCcRS_jet_mul` — the product form
  `jet_n (appCcRS g p r c Φ W) ≤ C n * jet_n Φ * jet_n W`,
  i.e. the statement that the covariant `H^n` jet is an algebra for the
  operator-field action.  This needs the supercritical gate
  `finrank ℝ E / 2 + 1 ≤ n` (in dimension three: `2 ≤ n`), and the gate is
  necessary: at `n = 0` the claim is the false `L²·L² ⊆ L²`.
* `appRS_hn_hn_hn` — the same fact in the envelope shape used by the rest of the
  family, on a closed three-manifold.  At `n = 2` it is `appRS_h2_h2_h2`.

`C n` grows with `n` (it contains the `n`-th Leibniz grid weight `appCcGdiag`,
exponential in `n`); no `n`-uniform constant is asserted.

The proof composes three order-generic facts that already exist in the tree and
adds no new tensor calculus: the pointwise Leibniz diagonal product grid at
arbitrary contravariant rank
(`rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le`), its integrated
Gagliardo--Nirenberg two-arm companion
(`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le`), and the
sharp `C0` jet-sum Sobolev window
(`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`).  The
only content is that the per-order cells of the grid are summed against a single
window instead of a fixed one, which is exactly what removes the order gate.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

set_option linter.unusedSectionVars false

open scoped ContDiff Manifold Topology BigOperators ENNReal
open MeasureTheory
open Tensor0SBundle
open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **All-order Moser jet estimate for the mixed operator-field action.**

For every order `n`, arbitrary valences `p, r, c`, and pointwise fibre bounds
`A` for `Φ` and `B` for `W`,

`∑_{j ≤ n} ‖∇ʲ(appCcRS g p r c Φ W)‖² ≤ C n * (B² ∑_{j ≤ n} ‖∇ʲΦ‖² +
  A² ∑_{j ≤ n} ‖∇ʲW‖²)`.

The pairing is the Moser one: each arm's `L∞` bound multiplies the *other* arm's
full `L2` jet, so the estimate is sharp in the jet order and needs neither a
dimension hypothesis nor an order gate.  `C n` grows with `n`. -/
theorem appRS_hn_sup (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (n : ℕ) (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
        0 ≤ A → 0 ≤ B →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r c x
          (Φ.toSection x) ≤ A ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g p r x
          (W.toSection x) ≤ B ^ 2) →
        (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g p c j
              (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤
          C n * (B ^ 2 * ∑ j ∈ Finset.range (n + 1),
                ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2 +
              A ^ 2 * ∑ j ∈ Finset.range (n + 1),
                ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) := by
  classical
  choose G hG hgrid using fun j : ℕ =>
    exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g r p c r j
  refine ⟨fun n => ∑ j ∈ Finset.range (n + 1), appCcGdiag (E := E) j * G j, ?_, ?_⟩
  · intro n
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (appCcGdiag_nonneg (E := E) j) (hG j)
  intro n Φ W A B hA hB hΦsup hWsup
  set SΦ : ℝ := ∑ j ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2 with hSΦ_def
  set SW : ℝ := ∑ j ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2 with hSW_def
  have hSΦ_nn : (0 : ℝ) ≤ SΦ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSW_nn : (0 : ℝ) ≤ SW := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hR_nn : (0 : ℝ) ≤ B ^ 2 * SΦ + A ^ 2 * SW := by positivity
  have hterm : ∀ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) g p c j
          (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2 ≤
        appCcGdiag (E := E) j * G j * (B ^ 2 * SΦ + A ^ 2 * SW) := by
    intro j hj
    have hjn : j + 1 ≤ n + 1 := by
      simp only [Finset.mem_range] at hj; omega
    set grid : M → ℝ := fun x =>
      ∑ m ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g r (c + m) x
            ((iteratedCovGrad (I := I) g r c m Φ).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - m),
            riemannianFiberNormSq (I := I) (M := M) g p (r + l) x
              ((iteratedCovGrad (I := I) g p r l W).toSection x) with hgrid_def
    obtain ⟨hgInt, hgBound⟩ := hgrid j Φ W A B hA hB hΦsup hWsup
    have hgInt' : Integrable grid (riemannianVolumeMeasure (I := I) (M := M) g) := by
      simpa only [hgrid_def] using hgInt
    have hgBound' :
        (∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          G j * (B ^ 2 * (∑ m ∈ Finset.range (j + 1),
                ‖iteratedCovGrad (I := I) g r c m Φ‖ ^ 2) +
            A ^ 2 * ∑ l ∈ Finset.range (j + 1),
              ‖iteratedCovGrad (I := I) g p r l W‖ ^ 2) := by
      simpa only [hgrid_def] using hgBound
    have hΦwin : (∑ m ∈ Finset.range (j + 1),
        ‖iteratedCovGrad (I := I) g r c m Φ‖ ^ 2) ≤ SΦ := by
      rw [hSΦ_def]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjn)
        (fun m _ _ => sq_nonneg _)
    have hWwin : (∑ l ∈ Finset.range (j + 1),
        ‖iteratedCovGrad (I := I) g p r l W‖ ^ 2) ≤ SW := by
      rw [hSW_def]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjn)
        (fun l _ _ => sq_nonneg _)
    have hgFinal : (∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
        G j * (B ^ 2 * SΦ + A ^ 2 * SW) := by
      refine hgBound'.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (hG j))
      · exact mul_le_mul_of_nonneg_left hΦwin (sq_nonneg B)
      · exact mul_le_mul_of_nonneg_left hWwin (sq_nonneg A)
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g p (c + j)
      (iteratedCovGrad (I := I) g p c j
        (appCcRS (I := I) (M := M) g p r c Φ W))
      (fun x => appCcGdiag (E := E) j * grid x)
      (hgInt'.const_mul (appCcGdiag (E := E) j))
      (fun x => by
        simpa only [hgrid_def] using
          (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
            (I := I) (M := M) g j p r c Φ W x))
    calc ‖iteratedCovGrad (I := I) g p c j
            (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2
        ≤ ∫ x, appCcGdiag (E := E) j * grid x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := hkey
      _ = appCcGdiag (E := E) j *
            ∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ appCcGdiag (E := E) j * (G j * (B ^ 2 * SΦ + A ^ 2 * SW)) :=
          mul_le_mul_of_nonneg_left hgFinal (appCcGdiag_nonneg (E := E) j)
      _ = appCcGdiag (E := E) j * G j * (B ^ 2 * SΦ + A ^ 2 * SW) := by ring
  calc (∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g p c j
            (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2)
      ≤ ∑ j ∈ Finset.range (n + 1),
          appCcGdiag (E := E) j * G j * (B ^ 2 * SΦ + A ^ 2 * SW) :=
        Finset.sum_le_sum hterm
    _ = (∑ j ∈ Finset.range (n + 1), appCcGdiag (E := E) j * G j) *
          (B ^ 2 * SΦ + A ^ 2 * SW) := by
        rw [Finset.sum_mul]

/-- **All-order product jet estimate for the mixed operator-field action.**

Above the Sobolev supercritical threshold `finrank ℝ E / 2 + 1 ≤ n` (in
dimension three: `2 ≤ n`), the covariant `L2` jet through order `n` is an
algebra for `appCcRS`:

`∑_{j ≤ n} ‖∇ʲ(appCcRS g p r c Φ W)‖² ≤ C n * (∑_{j ≤ n} ‖∇ʲΦ‖²) *
  (∑_{j ≤ n} ‖∇ʲW‖²)`.

This is the order-generic replacement for the fixed-order-two product bounds of
the DeTurck low-base action.  The gate is necessary, not technical: below the
threshold the jet sum does not control the pointwise fibre norm and the claim
degenerates to `L² · L² ⊆ L²`, which is false.  `C n` grows with `n`. -/
theorem appCcRS_jet_mul (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (n : ℕ), Module.finrank ℝ E / 2 + 1 ≤ n →
        ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
          (∑ j ∈ Finset.range (n + 1),
              ‖iteratedCovGrad (I := I) g p c j
                (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤
            C n * (∑ j ∈ Finset.range (n + 1),
                ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) *
              ∑ j ∈ Finset.range (n + 1),
                ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2 := by
  classical
  obtain ⟨CΦ, hCΦ, hΦpt⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g r c
  obtain ⟨CW, hCW, hWpt⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g p r
  obtain ⟨K, hK, hKle⟩ := appRS_hn_sup (I := I) (M := M) g p r c
  refine ⟨fun n => K n * (CW ^ 2 + CΦ ^ 2), ?_, ?_⟩
  · intro n
    exact mul_nonneg (hK n) (by positivity)
  intro n hn Φ W
  set SΦ : ℝ := ∑ j ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2 with hSΦ_def
  set SW : ℝ := ∑ j ∈ Finset.range (n + 1),
    ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2 with hSW_def
  have hSΦ_nn : (0 : ℝ) ≤ SΦ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSW_nn : (0 : ℝ) ≤ SW := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hwin : Module.finrank ℝ E / 2 + 2 ≤ n + 1 := by omega
  set A : ℝ := CΦ * Real.sqrt SΦ with hA_def
  set B : ℝ := CW * Real.sqrt SW with hB_def
  have hA : (0 : ℝ) ≤ A := mul_nonneg hCΦ (Real.sqrt_nonneg _)
  have hB : (0 : ℝ) ≤ B := mul_nonneg hCW (Real.sqrt_nonneg _)
  have hA2 : A ^ 2 = CΦ ^ 2 * SΦ := by
    rw [hA_def, mul_pow, Real.sq_sqrt hSΦ_nn]
  have hB2 : B ^ 2 = CW ^ 2 * SW := by
    rw [hB_def, mul_pow, Real.sq_sqrt hSW_nn]
  have hΦsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r c x
      (Φ.toSection x) ≤ A ^ 2 := by
    intro x
    refine (hΦpt Φ x).trans ?_
    rw [hA2]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg CΦ)
    rw [hSΦ_def]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hwin)
      (fun j _ _ => sq_nonneg _)
  have hWsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g p r x
      (W.toSection x) ≤ B ^ 2 := by
    intro x
    refine (hWpt W x).trans ?_
    rw [hB2]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg CW)
    rw [hSW_def]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hwin)
      (fun j _ _ => sq_nonneg _)
  calc (∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g p c j
            (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2)
      ≤ K n * (B ^ 2 * SΦ + A ^ 2 * SW) :=
        hKle n Φ W A B hA hB hΦsup hWsup
    _ = K n * (CW ^ 2 + CΦ ^ 2) * SΦ * SW := by
        rw [hA2, hB2]; ring

/-- **Dimension-three envelope form of the all-order product jet estimate.**

The `appRS_h*` family's envelope shape, at every order `n ≥ 2`: if the covariant
`L2` jets of `Φ` and `W` through order `n` are bounded by `A²` and `B²`, so is
the jet of `appCcRS g p r c Φ W` by `(C n * A * B)²`.  At `n = 2` this is
`appRS_h2_h2_h2`. -/
theorem appRS_hn_hn_hn (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (n : ℕ), 2 ≤ n →
        ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
          0 ≤ A → 0 ≤ B →
          (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
          (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) ≤ B ^ 2 →
          (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g p c j
              (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤ (C n * A * B) ^ 2 := by
  classical
  obtain ⟨K, hK, hKle⟩ := appCcRS_jet_mul (I := I) (M := M) g p r c
  refine ⟨fun n => Real.sqrt (K n), fun n => Real.sqrt_nonneg _, ?_⟩
  intro n hn Φ W A B hA hB hΦ hW
  have hgate : Module.finrank ℝ E / 2 + 1 ≤ n := by rw [hDim]; omega
  have hSΦ_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : Real.sqrt (K n) ^ 2 = K n := Real.sq_sqrt (hK n)
  calc (∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g p c j
            (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2)
      ≤ K n * (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) *
          ∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2 := hKle n hgate Φ W
    _ ≤ K n * A ^ 2 * B ^ 2 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hΦ (hK n)) hW
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (mul_nonneg (hK n) (sq_nonneg A))
    _ = (Real.sqrt (K n) * A * B) ^ 2 := by
        rw [mul_pow, mul_pow, hsq]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
