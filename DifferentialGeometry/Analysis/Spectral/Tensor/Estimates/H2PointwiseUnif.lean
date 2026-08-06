import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2Pointwise
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.UnifBochnerGap

/-!
# Class-uniform `H²` → fibre-operator control (item-6 packet, bricks E2 and E5)

`H2Pointwise.lean` proves the per-metric chain

* `hs2_fiber_sq` — `|T|²_g(x) ≤ C² ‖T‖²_{H²}` pointwise, and
* `hs2_op_bound` — the fibrewise operator bound `gFibreOpBound g (ccTensorBilinSymm g T)
  (C · ‖T‖_{H²})` consumed by the metric-realization radius `realize_at_thr`,

but both conclude with an `∃ C` whose witness is built from two `Classical.choose`
constants: the fibre-Morrey constant of
`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical` and the Gårding
constant of `hsJet_le`.  Two metrics of the same `Λ`-comparability class therefore receive
unrelated radii, and the realization radius `P` cannot floor a class-level horizon.

This file removes the second `Classical.choose` and parameterizes the first.

* **Brick E2** — the rank-`(0,2)` `smoothCcToTensorHs` face of the class-uniform Sobolev
  comparison.  `ccHs_eq_smoothHs` identifies the two smooth spectral embeddings (they have
  the same eigenbasis coordinates by construction), and `hsCovsum_smoothCc` /
  `covsumHs_smoothCc` restate `UnifBochnerGap`'s constant-exposed endpoints
  `hsCovsum_unif_const` / `covsum_hs_unif_const` in the currency the DeTurck stack speaks.
* **Brick E5** — `hs2_op_bound_unif`, the class-uniform sibling of `hs2_op_bound`, whose
  constant is the closed `hs2OpC Cpt Fc d = Cpt · covsumHsC Fc d 2 + 1`, and the resulting
  closed realization radius `unifRealizeRad = θ(d) / hs2OpC` together with
  `realize_at_unif`, the class-uniform sibling of `realize_at_thr`.
* **Finite `H²` face** — `realize_at_action` replaces the all-order `Fc`/`hcurv` input by the
  exact rank-two, order-zero package `IsCurvAction0 g 2 K`. Its radius `actionRealizeRad` is
  closed in the Morrey constant, `K`, and the dimension.

**Parameterized input (brick E4 is not landed).**  The fibre-Morrey constant `Cpt` is taken
as an explicit hypothesis `hmorrey`, stated verbatim in the shape of
`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`, so that E4's
`Λ`-uniform producer drops in without restatement.  Everything else — the whole Gårding /
Bochner backbone — is closed in `(Fc, finrank ℝ E)` through `covsumHsC`.

The legacy all-order endpoints retain `hcurv` for compatibility. The realization-facing finite
endpoints need only `IsCurvAction0 g 2 K`; no differentiated curvature action enters `H²`.
-/

noncomputable section

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open Tensor0SBundle

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### Brick E2: the rank-`(0,2)` `smoothCcToTensorHs` face -/

/-- **The two smooth spectral embeddings agree at rank `(0,2)`.**

`ccTensorToHs g₀ 2 σ` (`IteratedCovGradHsJetBound.lean`, rank-generic, the currency of the
Gårding/Bochner layer) and `smoothCcToTensorHs g₀ σ` (`DeTurckRemainderDefs.lean`,
rank-`(0,2)` only, the currency of the DeTurck stack and of the realization radius) are
defined by the SAME eigenbasis coordinates, so they are equal.  This is the bridge that lets
the class-uniform `H^n` ↔ covariant-jet endpoints be read by the DeTurck files. -/
theorem ccHs_eq_smoothHs (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g₀ 0 2) :
    ccTensorToHs (I := I) (M := M) g₀ 2 σ T =
      smoothCcToTensorHs (I := I) (M := M) g₀ σ T :=
  tensorHs.ext (funext fun _ => rfl)

/-- Norm face of `ccHs_eq_smoothHs`. -/
theorem norm_ccHs_eq_smoothHs (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g₀ 0 2) :
    ‖ccTensorToHs (I := I) (M := M) g₀ 2 σ T‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ T‖ := by
  rw [ccHs_eq_smoothHs]

/-- **Class-uniform spectral `H^n` ≤ covariant jet, in `smoothCcToTensorHs` currency**
(brick E2, easy direction).  The rank-`(0,2)` face of `hsCovsum_unif_const`, with the same
closed constant `hsCovsumC Fc d n`. -/
theorem hsCovsum_smoothCc
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (n : ℕ) (T : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) T‖ ≤
      hsCovsumC Fc (Module.finrank ℝ E) n * ∑ j ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
  rw [← norm_ccHs_eq_smoothHs]
  exact hsCovsum_unif_const (I := I) (M := M) g₀ Fc hFc hcurv 2 n T

/-- **Class-uniform covariant jet ≤ spectral `H^n`, in `smoothCcToTensorHs` currency**
(brick E2, hard direction).  The rank-`(0,2)` face of `covsum_hs_unif_const`, with the same
closed constant `covsumHsC Fc d n`.  Constant-exposed sibling of the `∃ C` wrapper
`exists_iteratedCovGrad_sum_le_smoothCcToTensorHs`. -/
theorem covsumHs_smoothCc
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (n : ℕ) (T : SmoothCcTensor g₀ 0 2) :
    ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤
      covsumHsC Fc (Module.finrank ℝ E) n *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) T‖ := by
  rw [← norm_ccHs_eq_smoothHs]
  exact covsum_hs_unif_const (I := I) (M := M) g₀ Fc hFc hcurv 2 n T

/-- The rank-`(0,2)` DeTurck-currency face of the finite curvature-action `H²` comparison.

This endpoint needs only the order-zero action package `IsCurvAction0 g₀ 2 K`; unlike
`covsumHs_smoothCc`, it does not quantify over differentiated actions or unrelated tensor ranks. -/
theorem covsumHs2_smoothCc
    (g₀ : SmoothRiemannianMetric I M) {K : ℝ}
    (hact : IsCurvAction0 (I := I) (M := M) g₀ 2 K)
    (T : SmoothCcTensor g₀ 0 2) :
    ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤
      h2CovsumC K * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T‖ := by
  rw [← norm_ccHs_eq_smoothHs]
  exact covsum_hs_two (I := I) (M := M) g₀ 2 hact T

/-! ### Brick E5: the closed constants -/

/-- The closed pointwise-fibre constant of `hs2_fiber_sq_unif`: the fibre-Morrey constant
`Cpt` times the closed Gårding constant `covsumHsC Fc d 2` at spectral order `2`. -/
def hs2FibreC (Cpt : ℝ) (Fc : ℕ → ℝ) (d : ℕ) : ℝ := Cpt * covsumHsC Fc d 2

/-- The closed constant of `hs2_op_bound_unif`, `hs2FibreC + 1`.  The shift keeps it
strictly positive, so it may be divided by (`unifRealizeRad`), exactly as `hs2_op_bound`'s
`C0 + 1`. -/
def hs2OpC (Cpt : ℝ) (Fc : ℕ → ℝ) (d : ℕ) : ℝ := hs2FibreC Cpt Fc d + 1

theorem hs2FibreC_nonneg {Cpt : ℝ} (hCpt : 0 ≤ Cpt) {Fc : ℕ → ℝ}
    (hFc : ∀ p, 0 ≤ Fc p) (d : ℕ) : 0 ≤ hs2FibreC Cpt Fc d :=
  mul_nonneg hCpt (covsumHsC_nonneg (d := d) hFc 2)

theorem hs2OpC_pos {Cpt : ℝ} (hCpt : 0 ≤ Cpt) {Fc : ℕ → ℝ}
    (hFc : ∀ p, 0 ≤ Fc p) (d : ℕ) : 0 < hs2OpC Cpt Fc d := by
  have h := hs2FibreC_nonneg hCpt hFc d
  unfold hs2OpC
  linarith

theorem hs2FibreC_le_opC (Cpt : ℝ) (Fc : ℕ → ℝ) (d : ℕ) :
    hs2FibreC Cpt Fc d ≤ hs2OpC Cpt Fc d := by
  unfold hs2OpC
  linarith

/-- The finite-action pointwise-fibre constant: the Morrey constant times `h2CovsumC`. -/
def hs2FibreActionC (Cpt K : ℝ) : ℝ := Cpt * h2CovsumC K

/-- The strictly positive finite-action fibre-operator constant. -/
def hs2OpActionC (Cpt K : ℝ) : ℝ := hs2FibreActionC Cpt K + 1

/-- The finite-action pointwise-fibre constant is nonnegative for nonnegative Morrey input. -/
theorem hs2FibreAct_nonneg {Cpt : ℝ} (hCpt : 0 ≤ Cpt) (K : ℝ) :
    0 ≤ hs2FibreActionC Cpt K :=
  mul_nonneg hCpt (h2CovsumC_nonneg K)

/-- The shifted finite-action fibre-operator constant is strictly positive. -/
theorem hs2OpActionC_pos {Cpt : ℝ} (hCpt : 0 ≤ Cpt) (K : ℝ) :
    0 < hs2OpActionC Cpt K := by
  have h := hs2FibreAct_nonneg hCpt K
  unfold hs2OpActionC
  linarith

/-! ### Brick E5: the class-uniform pointwise and operator bounds -/

/-- **Class-uniform pointwise `H²` fibre bound** (brick E5).  The sibling of `hs2_fiber_sq`
with the closed constant `hs2FibreC Cpt Fc d = Cpt · covsumHsC Fc d 2`: in dimension three
the spectral `H²` norm controls the pointwise squared fibre norm of a smooth covariant
tensor with a constant depending only on the fibre-Morrey input `Cpt`, the curvature-jet
family `Fc`, and `d = finrank ℝ E`.

`hmorrey` is stated verbatim in the shape of
`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`; brick E4 supplies a
`Λ`-uniform `Cpt`. -/
theorem hs2_fiber_sq_unif
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g 0 r),
        ‖iteratedCovGrad (I := I) g 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g 0 r a S‖)
    {Cpt : ℝ}
    (hmorrey : ∀ (T : SmoothCcTensor g 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x (T.toSection x) ≤
          Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g 0 s j T‖ ^ 2)
    (T : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x (T.toSection x) ≤
      hs2FibreC Cpt Fc (Module.finrank ℝ E) ^ 2 *
        ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖ ^ 2 := by
  classical
  have hrange : Finset.range (Module.finrank ℝ E / 2 + 2) = Finset.range 3 := by
    rw [hDim]
  have hpt := hmorrey T x
  rw [hrange] at hpt
  have hsq :
      ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 s j T‖ ^ 2 ≤
        (∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 s j T‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)
  have hsum :
      ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 s j T‖ ≤
        covsumHsC Fc (Module.finrank ℝ E) 2 *
          ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖ := by
    simpa using covsum_hs_unif_const (I := I) (M := M) g Fc hFc hcurv s 2 T
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 s x (T.toSection x)
        ≤ Cpt ^ 2 * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 s j T‖ ^ 2 := hpt
    _ ≤ Cpt ^ 2 *
          (∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 s j T‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg Cpt)
    _ ≤ Cpt ^ 2 *
          (covsumHsC Fc (Module.finrank ℝ E) 2 *
            ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀
          (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hsum 2)
        (sq_nonneg Cpt)
    _ = hs2FibreC Cpt Fc (Module.finrank ℝ E) ^ 2 *
          ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖ ^ 2 := by
      unfold hs2FibreC
      ring

/-- Pointwise `H²` fibre control from the finite rank-two curvature-action package.

The only geometric comparison input is `IsCurvAction0 g 2 K`; the Morrey hypothesis is the
existing rank-two three-jet estimate. -/
theorem hs2_fiber_sq_action
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {K : ℝ}
    (hact : IsCurvAction0 (I := I) (M := M) g 2 K)
    {Cpt : ℝ}
    (hmorrey : ∀ (T : SmoothCcTensor g 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
          Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)
    (T : SmoothCcTensor g 0 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
      hs2FibreActionC Cpt K ^ 2 *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ^ 2 := by
  classical
  have hrange : Finset.range (Module.finrank ℝ E / 2 + 2) = Finset.range 3 := by
    rw [hDim]
  have hpt := hmorrey T x
  rw [hrange] at hpt
  have hsq :
      ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤
        (∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 2 j T‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)
  have hsum :
      ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 2 j T‖ ≤
        h2CovsumC K * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ := by
    have h := covsumHs2_smoothCc (I := I) (M := M) g hact T
    rw [← norm_ccHs_eq_smoothHs] at h
    exact h
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x)
        ≤ Cpt ^ 2 * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := hpt
    _ ≤ Cpt ^ 2 *
          (∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 2 j T‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg Cpt)
    _ ≤ Cpt ^ 2 *
          (h2CovsumC K * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀
          (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hsum 2)
        (sq_nonneg Cpt)
    _ = hs2FibreActionC Cpt K ^ 2 *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ^ 2 := by
      unfold hs2FibreActionC
      ring

omit [BoundarylessManifold I M] in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **A uniform pointwise fibre bound is a fibrewise operator bound.**

If the `g`-fibre norm of the smooth `(0,2)`-tensor `T` is bounded by `K` at every point, its
symmetrization `ccTensorBilinSymm g T` is `K`-small in the `g`-operator sense.  This is the
reusable Cauchy–Schwarz + symmetrization algebra of `hs2_op_bound`, isolated so that the
per-metric and the class-uniform bounds share it instead of duplicating it. -/
theorem gFibreOp_of_fiberSq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) {K : ℝ}
    (hK : 0 ≤ K)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤ K ^ 2) :
    gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T) K := by
  intro x v w
  letI instTens : Bundle.RiemannianBundle
      (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
  letI instNormed : ∀ b : M,
      NormedAddCommGroup (Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    fun b =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) b
  have hnorm : ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ≤ K := by
    rw [norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g 0 2 x (T.toSection x),
      ← riemannianFiberNormSq_eq_tensorInnerPointwise
        (I := I) (M := M) g 0 2 x (T.toSection x)]
    calc
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x))
          ≤ Real.sqrt (K ^ 2) := Real.sqrt_le_sqrt (hpt x)
      _ = K := Real.sqrt_sq hK
  have hcs := ccTensorBilin_abs_le_fibreNorm_mul_sqrt (I := I) (M := M) g T x
  have hsv : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  have hsw : 0 ≤ Real.sqrt (g.inner x w w) := Real.sqrt_nonneg _
  have hvw : |ccTensorBilin (I := I) g T x v w| ≤
      K * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) :=
    (hcs v w).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm hsv) hsw)
  have hwv : |ccTensorBilin (I := I) g T x w v| ≤
      K * Real.sqrt (g.inner x w w) * Real.sqrt (g.inner x v v) :=
    (hcs w v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm hsw) hsv)
  rw [ccTensorBilinSymm_apply]
  calc
    |(1 / 2 : ℝ) *
        (ccTensorBilin (I := I) g T x v w + ccTensorBilin (I := I) g T x w v)|
        ≤ (1 / 2 : ℝ) *
          (|ccTensorBilin (I := I) g T x v w| +
            |ccTensorBilin (I := I) g T x w v|) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
          (K * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) +
            K * Real.sqrt (g.inner x w w) * Real.sqrt (g.inner x v v)) :=
      mul_le_mul_of_nonneg_left (add_le_add hvw hwv) (by norm_num)
    _ = K * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by ring

/-- **The class-uniform `H²` → fibre-operator bound** (brick E5).

The sibling of `hs2_op_bound` whose constant is the closed
`hs2OpC Cpt Fc d = Cpt · covsumHsC Fc d 2 + 1`: it depends only on the fibre-Morrey input
`Cpt`, the curvature-jet family `Fc`, and `d = finrank ℝ E`, so two metrics of the same
`Λ`-class sharing `(Cpt, Fc)` receive the SAME constant.  That is what makes the realization
radius `unifRealizeRad` — and hence the horizon it floors — class-uniform. -/
theorem hs2_op_bound_unif
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g 0 r),
        ‖iteratedCovGrad (I := I) g 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g 0 r a S‖)
    {Cpt : ℝ} (hCpt : 0 ≤ Cpt)
    (hmorrey : ∀ (T : SmoothCcTensor g 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
          Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)
    (T : SmoothCcTensor g 0 2) :
    gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T)
      (hs2OpC Cpt Fc (Module.finrank ℝ E) *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) := by
  have hN : (0 : ℝ) ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ :=
    norm_nonneg _
  have hFib : 0 ≤ hs2FibreC Cpt Fc (Module.finrank ℝ E) :=
    hs2FibreC_nonneg hCpt hFc _
  have hOp : 0 < hs2OpC Cpt Fc (Module.finrank ℝ E) := hs2OpC_pos hCpt hFc _
  refine gFibreOp_of_fiberSq (I := I) (M := M) g T (mul_nonneg hOp.le hN) ?_
  intro x
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x)
        ≤ hs2FibreC Cpt Fc (Module.finrank ℝ E) ^ 2 *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ^ 2 :=
      hs2_fiber_sq_unif (I := I) (M := M) hDim g 2 Fc hFc hcurv hmorrey T x
    _ ≤ hs2OpC Cpt Fc (Module.finrank ℝ E) ^ 2 *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      unfold hs2OpC
      nlinarith [hFib]
    _ = (hs2OpC Cpt Fc (Module.finrank ℝ E) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) ^ 2 := by ring

/-- The finite-action `H²` fibre-operator bound.

Its constant depends only on the Morrey input `Cpt` and the rank-two order-zero curvature-action
constant `K`; it has no all-order `Fc` or `hcurv` argument. -/
theorem hs2_op_bound_action
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {K : ℝ}
    (hact : IsCurvAction0 (I := I) (M := M) g 2 K)
    {Cpt : ℝ} (hCpt : 0 ≤ Cpt)
    (hmorrey : ∀ (T : SmoothCcTensor g 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
          Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)
    (T : SmoothCcTensor g 0 2) :
    gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T)
      (hs2OpActionC Cpt K *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) := by
  have hN : (0 : ℝ) ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ :=
    norm_nonneg _
  have hFib : 0 ≤ hs2FibreActionC Cpt K := hs2FibreAct_nonneg hCpt K
  have hOp : 0 < hs2OpActionC Cpt K := hs2OpActionC_pos hCpt K
  refine gFibreOp_of_fiberSq (I := I) (M := M) g T (mul_nonneg hOp.le hN) ?_
  intro x
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x)
        ≤ hs2FibreActionC Cpt K ^ 2 *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ^ 2 :=
      hs2_fiber_sq_action (I := I) (M := M) hDim g hact hmorrey T x
    _ ≤ hs2OpActionC Cpt K ^ 2 *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      unfold hs2OpActionC
      nlinarith [hFib]
    _ = (hs2OpActionC Cpt K *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) ^ 2 := by ring

/-- `smoothCcToTensorHs` face of `hs2_op_bound_unif` (brick E2 × E5): the class-uniform
operator bound in the currency of the DeTurck stack and of the realization radius. -/
theorem hs2_op_smoothCc_unif
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g 0 r),
        ‖iteratedCovGrad (I := I) g 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g 0 r a S‖)
    {Cpt : ℝ} (hCpt : 0 ≤ Cpt)
    (hmorrey : ∀ (T : SmoothCcTensor g 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
          Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)
    (T : SmoothCcTensor g 0 2) :
    gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T)
      (hs2OpC Cpt Fc (Module.finrank ℝ E) *
        ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T‖) := by
  rw [← norm_ccHs_eq_smoothHs]
  exact hs2_op_bound_unif (I := I) (M := M) hDim g Fc hFc hcurv hCpt hmorrey T

/-! ### Brick E5: the class-uniform realization radius `P` -/

/-- **The class-uniform metric-realization radius** `P = θ(d) / hs2OpC Cpt Fc d`.

`θ(d) = deTurckArmContractionThreshold'' d` is a dimension-only quantity, and `hs2OpC` is
closed in `(Cpt, Fc, d)`, so `unifRealizeRad` is a single number for the whole
`Λ`-comparability class — the class-level replacement of the `∃ R` of `realize_at_thr`. -/
def unifRealizeRad (Cpt : ℝ) (Fc : ℕ → ℝ) (d : ℕ) : ℝ :=
  deTurckArmContractionThreshold'' d / hs2OpC Cpt Fc d

theorem unifRealizeRad_pos {Cpt : ℝ} (hCpt : 0 ≤ Cpt) {Fc : ℕ → ℝ}
    (hFc : ∀ p, 0 ≤ Fc p) (d : ℕ) : 0 < unifRealizeRad Cpt Fc d :=
  div_pos (deTurckArmContractionThreshold''_pos d) (hs2OpC_pos hCpt hFc d)

/-- The realization radius determined by the finite rank-two curvature-action package. -/
def actionRealizeRad (Cpt K : ℝ) (d : ℕ) : ℝ :=
  deTurckArmContractionThreshold'' d / hs2OpActionC Cpt K

/-- The finite-action realization radius is strictly positive. -/
theorem actionRealizeRad_pos {Cpt : ℝ} (hCpt : 0 ≤ Cpt) (K : ℝ) (d : ℕ) :
    0 < actionRealizeRad Cpt K d :=
  div_pos (deTurckArmContractionThreshold''_pos d) (hs2OpActionC_pos hCpt K)

/-- The metric-realization bound from the finite rank-two curvature-action package.

This is the realization producer consumed by the uniform low-regularity solve: its radius is closed
in `(Cpt, K, finrank)` and its hypotheses mention neither an all-order curvature family nor
differentiated curvature actions. -/
theorem realize_at_action
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {K : ℝ}
    (hact : IsCurvAction0 (I := I) (M := M) g 2 K)
    {Cpt : ℝ} (hCpt : 0 ≤ Cpt)
    (hmorrey : ∀ (T : SmoothCcTensor g 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
          Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) :
    ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) T‖ ≤
          actionRealizeRad Cpt K (Module.finrank ℝ E) →
        gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T)
          (deTurckArmContractionThreshold'' (Module.finrank ℝ E)) := by
  intro T hT
  have hOp : 0 < hs2OpActionC Cpt K := hs2OpActionC_pos hCpt K
  have hTtwo : ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T‖ ≤
      actionRealizeRad Cpt K (Module.finrank ℝ E) := by
    rw [Nat.cast_one] at hT
    rw [show (1 : ℝ) + 1 = 2 by norm_num] at hT
    exact hT
  have hT' : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤
      actionRealizeRad Cpt K (Module.finrank ℝ E) := by
    rw [norm_ccHs_eq_smoothHs]
    exact hTtwo
  have hdelta : hs2OpActionC Cpt K *
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤
        deTurckArmContractionThreshold'' (Module.finrank ℝ E) := by
    calc
      hs2OpActionC Cpt K *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
          ≤ hs2OpActionC Cpt K *
              actionRealizeRad Cpt K (Module.finrank ℝ E) :=
        mul_le_mul_of_nonneg_left hT' hOp.le
      _ = deTurckArmContractionThreshold'' (Module.finrank ℝ E) := by
        unfold actionRealizeRad
        field_simp
  have hsmall := hs2_op_bound_action (I := I) (M := M) hDim g hact hCpt hmorrey T
  intro x v w
  refine (hsmall x v w).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdelta (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

/-- **The class-uniform realization bound** (brick E5): the sibling of `realize_at_thr` whose
radius is the closed `unifRealizeRad Cpt Fc d`.

The conclusion is exactly the `hreal` hypothesis of `lowreg_partial_sol_of_bounds`
(`ShortTime/UnifClassBounds.lean`) at `P := unifRealizeRad Cpt Fc (finrank ℝ E)` and
`δ := deTurckArmContractionThreshold'' (finrank ℝ E)`, so the realization radius of the
six-number solve is no longer an existential. -/
theorem realize_at_unif
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g 0 r),
        ‖iteratedCovGrad (I := I) g 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g 0 r a S‖)
    {Cpt : ℝ} (hCpt : 0 ≤ Cpt)
    (hmorrey : ∀ (T : SmoothCcTensor g 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
          Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) :
    ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) T‖ ≤
          unifRealizeRad Cpt Fc (Module.finrank ℝ E) →
        gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T)
          (deTurckArmContractionThreshold'' (Module.finrank ℝ E)) := by
  intro T hT
  have hOp : 0 < hs2OpC Cpt Fc (Module.finrank ℝ E) := hs2OpC_pos hCpt hFc _
  have hTtwo : ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T‖ ≤
      unifRealizeRad Cpt Fc (Module.finrank ℝ E) := by
    rw [Nat.cast_one] at hT
    rw [show (1 : ℝ) + 1 = 2 by norm_num] at hT
    exact hT
  have hT' : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤
      unifRealizeRad Cpt Fc (Module.finrank ℝ E) := by
    rw [norm_ccHs_eq_smoothHs]
    exact hTtwo
  have hdelta : hs2OpC Cpt Fc (Module.finrank ℝ E) *
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤
        deTurckArmContractionThreshold'' (Module.finrank ℝ E) := by
    calc
      hs2OpC Cpt Fc (Module.finrank ℝ E) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
          ≤ hs2OpC Cpt Fc (Module.finrank ℝ E) *
              unifRealizeRad Cpt Fc (Module.finrank ℝ E) :=
        mul_le_mul_of_nonneg_left hT' hOp.le
      _ = deTurckArmContractionThreshold'' (Module.finrank ℝ E) := by
        unfold unifRealizeRad
        field_simp
  have hsmall := hs2_op_bound_unif (I := I) (M := M) hDim g Fc hFc hcurv hCpt hmorrey T
  intro x v w
  refine (hsmall x v w).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdelta (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
