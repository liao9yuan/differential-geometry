import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2Pointwise
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs

/-!
# Three-dimensional low-regularity metric realization

The spectral `H3` ball used by the low-regularity maximal-regularity solver
lies in a fixed fibre-small metric ball.  This is the dimension-three
replacement for the deliberately lossy high-order realization bound.
-/

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open scoped ContDiff Manifold Topology
open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [T2Space M] [SigmaCompactSpace M]

/-- **The `H²` metric-realization radius at an arbitrary fibre bound.**

In dimension three the pointwise `H²` operator bound `hs2_op_bound` converts any
*positive* fibre threshold `δ` into a positive spectral `H²` radius on which every
smooth compactly supported symmetric perturbation is `δ`-fibre-small.  The radius
is `δ / C` with `C` the dimension-three operator constant of `g`, so it shrinks
with `δ`.

This is the single realization lemma of the low-regularity layer: `realize_at_thr`,
`lowreg_realize_h2` and `lowreg_realize` are all instances.  Keeping `δ` a
parameter — rather than pinned at `deTurckArmContractionThreshold''` — is what
lets a caller choose the fibre threshold *after* the contraction constants of the
ladders are fixed. -/
theorem realize_at_delta
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧
      ∀ T : SmoothCcTensor g 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ := by
  obtain ⟨C, hC, hOp⟩ := hs2_op_bound (I := I) (M := M) hDim g
  refine ⟨δ / C, div_pos hδ hC, ?_⟩
  intro T hT
  rw [Nat.cast_one, show (1 : ℝ) + 1 = 2 by norm_num] at hT
  have htwo : ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T =
      smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T :=
    by ext i; rfl
  have hT' : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ δ / C := by
    simpa only [htwo] using hT
  have hdelta : C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ δ := by
    calc
      C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
          ≤ C * (δ / C) := mul_le_mul_of_nonneg_left hT' hC.le
      _ = δ := by field_simp
  have hsmall := hOp T
  intro x v w
  refine (hsmall x v w).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdelta (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- In dimension three, a positive spectral `H2` radius directly supplies
the fibre-smallness needed to realize every smooth perturbation in the state
ball as a metric.  The instance of `realize_at_delta` at the DeTurck contraction
threshold, in the `ℝ × ℝ` packaging. -/
theorem lowreg_realize_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ p : ℝ × ℝ, 0 < p.1 ∧
      p.2 ≤ deTurckArmContractionThreshold'' (Module.finrank ℝ E) ∧
      ∀ (T : SmoothCcTensor g 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T‖ ≤ p.1 →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) p.2 := by
  obtain ⟨R, hR, hreal⟩ :=
    realize_at_delta (I := I) (M := M) hDim g
      (deTurckArmContractionThreshold''_pos (Module.finrank ℝ E))
  refine ⟨(R, deTurckArmContractionThreshold'' (Module.finrank ℝ E)), hR,
    le_rfl, fun T hT => hreal T ?_⟩
  rw [Nat.cast_one, show (1 : ℝ) + 1 = 2 by norm_num]
  exact hT

/-- In dimension three, a positive spectral `H3` radius gives the exact
realizability witness used by the Sobolev Ricci--DeTurck nonlinearity.  The
instance of `realize_at_delta` at the DeTurck contraction threshold, read at the
`H³` radius through `ccToHs_norm_mono`. -/
theorem lowreg_realize
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ p : ℝ × ℝ, 0 < p.1 ∧
      p.2 ≤ deTurckArmContractionThreshold'' (Module.finrank ℝ E) ∧
      ∀ (T : SmoothCcTensor g 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) T‖ ≤ p.1 →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) p.2 := by
  obtain ⟨R, hR, hreal⟩ :=
    realize_at_delta (I := I) (M := M) hDim g
      (deTurckArmContractionThreshold''_pos (Module.finrank ℝ E))
  refine ⟨(R, deTurckArmContractionThreshold'' (Module.finrank ℝ E)), hR,
    le_rfl, fun T hT => hreal T ?_⟩
  rw [Nat.cast_one, show (1 : ℝ) + 1 = 2 by norm_num]
  have htwo : ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T =
      smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T :=
    by ext i; rfl
  have hthree : ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T =
      smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) T :=
    by ext i; rfl
  calc ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T‖
      = ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ := by rw [htwo]
    _ ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ :=
        ccToHs_norm_mono (I := I) (M := M) g 2 (by norm_num) T
    _ = ‖smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) T‖ := by rw [hthree]
    _ ≤ R := hT

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
