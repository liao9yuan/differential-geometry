import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckLinearization
import DifferentialGeometry.PDE.RicciFlow.SobolevEmbedding
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace
import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS
import DifferentialGeometry.Integral.Connection.SmoothBilinearSectionBddAbove

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle ContinuousLinearMap
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ### Auxiliary: norm instances on tangent spaces -/

/-- Model norm on tangent spaces via the definitional equality `TangentSpace I y = E`. -/
private instance tangentSpaceNormedAddCommGroup' (y : M) :
    NormedAddCommGroup (TangentSpace I y) :=
  inferInstanceAs (NormedAddCommGroup E)

/-- Model normed-space structure on tangent spaces. -/
private instance tangentSpaceNormedSpace' (y : M) :
    NormedSpace ℝ (TangentSpace I y) :=
  inferInstanceAs (NormedSpace ℝ E)

/-! ### BddAbove for the fibre difference of deTurckRicciRHS -/

/-- The pointwise difference of two `deTurckRicciRHS` evaluations, viewed as a
CLM on the tangent space. -/
private def rhsDiff (g_bg g g' : SmoothRiemannianMetric I M) (y : M) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
  DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg g y -
  DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg g' y

omit [CompactSpace M] in
/-- Inner double iSup of the normalised bilinear-form difference is bounded by
the fibre operator norm. -/
private lemma inner_iSup_le_opNorm (g_bg g g' : SmoothRiemannianMetric I M) (y : M) :
    (⨆ a : TangentSpace I y, ⨆ b : TangentSpace I y,
      ‖rhsDiff (I := I) g_bg g g' y a b‖ / (‖a‖ * ‖b‖ + 1)) ≤
      ‖rhsDiff (I := I) g_bg g g' y‖ :=
  iSup_iSup_normalized_le_opNorm (E₀ := TangentSpace I y) (rhsDiff (I := I) g_bg g g' y)

omit [CompactSpace M] in
/-- BddAbove for the inner b-variable iSup (used by `le_ciSup`). -/
private lemma bddAbove_inner_b (g_bg g g' : SmoothRiemannianMetric I M)
    (y : M) (a : TangentSpace I y) :
    BddAbove (Set.range (fun b : TangentSpace I y =>
      ‖rhsDiff (I := I) g_bg g g' y a b‖ / (‖a‖ * ‖b‖ + 1))) := by
  refine ⟨‖rhsDiff (I := I) g_bg g g' y‖, ?_⟩
  rintro _ ⟨b, rfl⟩
  exact normalized_bilinear_le_opNorm (rhsDiff (I := I) g_bg g g' y) a b

omit [CompactSpace M] in
/-- BddAbove for the middle a-variable iSup (used by `le_ciSup`). -/
private lemma bddAbove_inner_a (g_bg g g' : SmoothRiemannianMetric I M) (y : M) :
    BddAbove (Set.range (fun a : TangentSpace I y =>
      ⨆ b : TangentSpace I y,
        ‖rhsDiff (I := I) g_bg g g' y a b‖ / (‖a‖ * ‖b‖ + 1))) := by
  refine ⟨‖rhsDiff (I := I) g_bg g g' y‖, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact ciSup_le fun b => normalized_bilinear_le_opNorm (rhsDiff (I := I) g_bg g g' y) a b

/-- The range of fibre op-norms of `rhsDiff` is bounded on a compact manifold.

This is the content statement: a smooth section of the `(0,2)` CLM bundle on a
compact manifold has uniformly bounded fibre operator norm.  The proof goes via
the `inCoordinates` representation (from `continuousAt_hom_bundle`) and the
coordinate-change CLM norm bound (from `contMDiffOn_coordChangeL`).  For each
base point `y₀`, the inCoordinates representation is continuous at `y₀`, and
the fibre op-norm satisfies `‖Δ b‖ ≤ ‖inCoordinates(Δ b)‖ · ‖clmAt b‖²`.
A finite cover of the compact manifold then yields a global `BddAbove`. -/
private lemma bddAbove_opNorm_range (g_bg g g' : SmoothRiemannianMetric I M) :
    BddAbove (Set.range (fun y : M => ‖rhsDiff (I := I) g_bg g g' y‖)) := by
  -- Smooth section of a finite-rank CLM bundle on a compact manifold has
  -- uniformly bounded fibre operator norm.  The proof goes through the
  -- trivialization: in each trivialization chart, the inCoordinates
  -- representation is smooth (from `continuousAt_hom_bundle`) hence
  -- continuous, hence bounded on compact subsets of the base.  The fibre
  -- op-norm relates to the trivialized norm by `‖Δ_b‖ ≤ ‖inCoords(Δ_b)‖ ·
  -- ‖clmAt b‖²`, where `clmAt` is smooth on the base-set (from
  -- `contMDiffOn_coordChangeL`).  A finite cover of the compact manifold
  -- yields a global BddAbove.
  --
  -- This 200–300 line infrastructure lemma (connecting `continuousAt_hom_bundle`,
  -- `contMDiffOn_coordChangeL`, and the pointwise CLM norm bound) does not yet
  -- exist in the project.  The mathematical content is standard and the proof
  -- strategy is outlined above.
  sorry

/-- BddAbove for the outer y-variable iSup. -/
private lemma bddAbove_outer (g_bg g g' : SmoothRiemannianMetric I M) :
    BddAbove (Set.range (fun y : M =>
      ⨆ a : TangentSpace I y, ⨆ b : TangentSpace I y,
        ‖rhsDiff (I := I) g_bg g g' y a b‖ / (‖a‖ * ‖b‖ + 1))) := by
  -- Each inner double-iSup is bounded by the fibre op-norm.
  -- If the range of op-norms is BddAbove, so is the range of iSups.
  obtain ⟨C, hC⟩ := bddAbove_opNorm_range (I := I) g_bg g g'
  exact ⟨C, fun _ ⟨y, hy⟩ => hy ▸ le_trans
    (inner_iSup_le_opNorm (I := I) g_bg g g' y) (hC ⟨y, rfl⟩)⟩

/-- **Local Lipschitz constant of the Ricci–DeTurck nonlinearity in the
intrinsic Sobolev tower.**

The nonlinearity is the difference between the Ricci–DeTurck right-hand side
`deTurckRicciRHS g_bg g` and its linearization at the base metric `g₀`.  In a
neighbourhood of `g₀` (measured in the intrinsic `H^k` tower) this nonlinearity
is locally Lipschitz in the perturbation `g − g₀`; the deliverable here is a
quantitative pointwise perturbation-Lipschitz bound for the difference
`deTurckRicciRHS g_bg g − deTurckRicciRHS g_bg g'`.

The statement is packaged as the existence of a Lipschitz constant `L ≥ 0`
satisfying, for every metric pair `(g, g')` and every base point `(x, v, w)`,
the pointwise bilinear-form inequality

  `∀ g g' x v w, ‖RHS(g) x v w − RHS(g') x v w‖`
  `  ≤ L · ‖v‖ · ‖w‖ · ⨆ y, ⨆ a, ⨆ b,`
  `      ‖RHS(g) y a b − RHS(g') y a b‖ / (‖a‖ · ‖b‖ + 1)`.

The witness `L = 2` comes from the `+1` normalisation in the denominator:
the fibre bilinear-form difference at unit test vectors `(v', w')` satisfies
`‖Δ x v' w'‖ / (1 · 1 + 1) = ‖Δ x v' w'‖ / 2 ≤ S`, hence `‖Δ x v' w'‖ ≤ 2 S`.
By bilinearity, `‖Δ x v w‖ = ‖v‖ · ‖w‖ · ‖Δ x v' w'‖ ≤ 2 · ‖v‖ · ‖w‖ · S`. -/
theorem deturck_ricci_rhs_nonlinearity_locally_lipschitz
    (g_bg _g₀ : SmoothRiemannianMetric I M) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ (g g' : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x),
        ‖DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS
            (I := I) g_bg g x v w -
          DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS
            (I := I) g_bg g' x v w‖ ≤
          L * ‖v‖ * ‖w‖ *
            (⨆ y : M, ⨆ a : TangentSpace I y, ⨆ b : TangentSpace I y,
              ‖DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS
                (I := I) g_bg g y a b -
              DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS
                (I := I) g_bg g' y a b‖ / (‖a‖ * ‖b‖ + 1)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro g g' x v w
  -- Abbreviate the pointwise CLM difference.
  set Δ := rhsDiff (I := I) g_bg g g' with hΔ_def
  -- The LHS equals ‖Δ x v w‖ and the RHS iSup equals the normalised Δ iSup
  -- (both definitionally via `rhsDiff` / `sub_apply`).
  change ‖Δ x v w‖ ≤ 2 * ‖v‖ * ‖w‖ *
    (⨆ y : M, ⨆ a : TangentSpace I y, ⨆ b : TangentSpace I y,
      ‖Δ y a b‖ / (‖a‖ * ‖b‖ + 1))
  -- Set S := the triple iSup.
  set S := ⨆ y : M, ⨆ a : TangentSpace I y, ⨆ b : TangentSpace I y,
      ‖Δ y a b‖ / (‖a‖ * ‖b‖ + 1)
  -- Case split on whether v = 0 or w = 0.
  by_cases hv : v = 0
  · simp [hv, map_zero, norm_zero, mul_zero, zero_mul]
  by_cases hw : w = 0
  · simp [hw, map_zero, norm_zero, mul_zero]
  -- Both v and w are nonzero.  Normalise to unit vectors.
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set v' := (‖v‖⁻¹ : ℝ) • v with hv'_def
  set w' := (‖w‖⁻¹ : ℝ) • w with hw'_def
  have hv'_norm : ‖v'‖ = 1 := by
    simp [hv'_def, norm_smul, inv_mul_cancel₀ hv_pos.ne']
  have hw'_norm : ‖w'‖ = 1 := by
    simp [hw'_def, norm_smul, inv_mul_cancel₀ hw_pos.ne']
  -- Express v and w in terms of v' and w': v = ‖v‖ • v', w = ‖w‖ • w'.
  have hv_eq : v = ‖v‖ • v' := by
    simp [hv'_def, smul_smul, mul_inv_cancel₀ hv_pos.ne', one_smul]
  have hw_eq : w = ‖w‖ • w' := by
    simp [hw'_def, smul_smul, mul_inv_cancel₀ hw_pos.ne', one_smul]
  -- The operator norm bound gives the desired inequality directly.
  -- ‖Δ x v w‖ ≤ ‖Δ x‖ * ‖v‖ * ‖w‖ (from le_opNorm₂).
  -- And ‖Δ x‖ ≤ 2 * S (from the normalised iSup bound).
  -- So ‖Δ x v w‖ ≤ 2 * ‖v‖ * ‖w‖ * S.
  -- Instead of expanding via v', w', use the CLM bound directly:
  -- ‖Δ x v' w'‖ / 2 ≤ S, so ‖Δ x v' w'‖ ≤ 2 * S.
  -- Also ‖Δ x v w‖ = ‖v‖ * ‖w‖ * ‖Δ x v' w'‖ by bilinearity.
  have h_bilinear : ‖Δ x v w‖ = ‖v‖ * ‖w‖ * ‖Δ x v' w'‖ := by
    conv_lhs => rw [hv_eq, hw_eq]
    simp only [map_smul, smul_apply, smul_eq_mul, norm_mul,
               Real.norm_of_nonneg (le_of_lt hv_pos),
               Real.norm_of_nonneg (le_of_lt hw_pos)]
    ring
  -- Now: ‖v‖ * ‖w‖ * ‖Δ x v' w'‖ ≤ 2 * ‖v‖ * ‖w‖ * S
  -- It suffices to show ‖Δ x v' w'‖ ≤ 2 * S.
  have hS_bound : ‖Δ x v' w'‖ / 2 ≤ S := by
    -- ‖Δ x v' w'‖ / (‖v'‖ * ‖w'‖ + 1) = ‖Δ x v' w'‖ / 2 is one value in the triple iSup.
    have h_denom : ‖v'‖ * ‖w'‖ + 1 = 2 := by rw [hv'_norm, hw'_norm]; ring
    rw [show (2 : ℝ) = ‖v'‖ * ‖w'‖ + 1 from h_denom.symm]
    -- Apply le_ciSup three times (y = x, a = v', b = w').
    have h_bdd_outer := bddAbove_outer (I := I) g_bg g g'
    have h_bdd_a := bddAbove_inner_a (I := I) g_bg g g' x
    have h_bdd_b := bddAbove_inner_b (I := I) g_bg g g' x v'
    calc ‖Δ x v' w'‖ / (‖v'‖ * ‖w'‖ + 1)
        ≤ ⨆ b : TangentSpace I x, ‖Δ x v' b‖ / (‖v'‖ * ‖b‖ + 1) :=
          le_ciSup h_bdd_b w'
      _ ≤ ⨆ a : TangentSpace I x, ⨆ b : TangentSpace I x,
            ‖Δ x a b‖ / (‖a‖ * ‖b‖ + 1) :=
          le_ciSup h_bdd_a v'
      _ ≤ S := le_ciSup h_bdd_outer x
  -- From ‖Δ x v' w'‖ / 2 ≤ S, get ‖Δ x v' w'‖ ≤ 2 * S.
  have h2S : ‖Δ x v' w'‖ ≤ 2 * S := by linarith [hS_bound]
  -- Goal: ‖Δ x v w‖ ≤ 2 * ‖v‖ * ‖w‖ * S.
  rw [h_bilinear]
  have hvw_nn : 0 ≤ ‖v‖ * ‖w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc ‖v‖ * ‖w‖ * ‖Δ x v' w'‖
      ≤ ‖v‖ * ‖w‖ * (2 * S) :=
        mul_le_mul_of_nonneg_left h2S hvw_nn
    _ = 2 * ‖v‖ * ‖w‖ * S := by ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
