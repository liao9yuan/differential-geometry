import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalLowRegCore

/-!
# Principal-subtracted low-regularity Ricci--DeTurck residual

This module records the canonical smooth residual obtained after subtracting
the variable-cometric principal action from the zero-based Ricci--DeTurck
remainder.  Its exact low-base split keeps the remaining small second-order
action visible and separates the genuinely first-order diagonal term.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The zero-based smooth Ricci--DeTurck remainder after subtracting exactly
the moving-cometric principal action. -/
noncomputable def principalResidual
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 0 2 :=
  deTurckSmoothRemainder (I := I) g g T hδ_lt hδ -
    deTurckSmoothRemainder (I := I) g g
      (0 : SmoothCcTensor g 0 2) hδ_lt hδZ -
    deTurckPrincipalCometricArm (I := I) (M := M) g
      (tensorSectionRealizeMetric (I := I) g T hδ_lt hδ) T

/-- The spectral `H2` residual formed with the completed low-regularity
principal operator. -/
noncomputable def principalResidualH2
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) :=
  ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
      (deTurckSmoothRemainder (I := I) g g T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g g
          (0 : SmoothCcTensor g 0 2) hδ_lt hδZ) -
    lowRegPrincipal (I := I) (M := M) g
      (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T)
      (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T)

/-- The canonical lower residual obtained after subtracting the complete
low-base second-order action. -/
noncomputable def lowBaseResidual
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 0 2 :=
  deTurckSmoothRemainder (I := I) g g T hδ_lt hδ -
    deTurckSmoothRemainder (I := I) g g
      (0 : SmoothCcTensor g 0 2) hδ_lt hδZ -
    (lowBaseData (I := I) (M := M) g g T hδ_lt hδ hδZ).a2
      (I := I) (M := M) T

/-- The spectral `H2` realization of the complete-A2-subtracted lower
residual. -/
noncomputable def lowBaseResidualH2
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) :=
  ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
    (lowBaseResidual (I := I) (M := M) g T hδ_lt hδ hδZ)

/-- On the smooth metric core, the completed principal-subtracted residual is
the spectral realization of `principalResidual`. -/
theorem residualH2_core
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (hsmall : ‖perturbH2 (I := I) (M := M) g
      (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T)‖ < 1) :
    principalResidualH2 (I := I) (M := M) g T hδ_lt hδ hδZ =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (principalResidual (I := I) (M := M) g T hδ_lt hδ hδZ) := by
  let gm : SmoothRiemannianMetric I M :=
    tensorSectionRealizeMetric (I := I) g T hδ_lt hδ
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g T y v w := by
    intro y v w
    exact tensorSectionRealizeMetric_inner
      (I := I) g T hδ_lt hδ y v w
  have hprincipal :
      lowRegPrincipal (I := I) (M := M) g
          (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T)
          (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T) =
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (deTurckPrincipalCometricArm (I := I) (M := M) g gm T) := by
    rw [lowRegPrincipal_core (I := I) (M := M)
      hDim g gm T htie hsmall]
    exact principalOpH2_core (I := I) (M := M) hDim g gm T
  have hsub (S U : SmoothCcTensor g 0 2) :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - U) =
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U := by
    simpa only [ccToHsLin_apply] using
      map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) S U
  simp only [principalResidualH2, principalResidual]
  rw [hsub, hsub, hprincipal]
  rw [hsub]

/-- The canonical principal-subtracted residual is the sum of the unresolved
second-order tail and the genuinely first-order low-base action.  The latter
has the sharp diagonal `H3 → H2` estimate with constants depending only on the
lower `H2` radius. -/
theorem residual_split_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, ∃ D : ℝ → ℝ,
      0 ≤ κ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      let hδ_lt : δ < 1 :=
        lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
      let L : LowBaseActionData g :=
        lowBaseData (I := I) (M := M) g g T hδ_lt hδ hδZ
      principalResidual (I := I) (M := M) g T hδ_lt hδ hδZ =
          (L.a2 (I := I) (M := M) T -
            deTurckPrincipalCometricArm (I := I) (M := M) g
              (tensorSectionRealizeMetric (I := I) g T hδ_lt hδ) T) +
            L.a1 (I := I) (M := M) T ∧
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              (L.C2.toSection x) ≤
            (κ * (δ / (1 - δ) ^ 2)) ^ 2) ∧
        lowJetSq (I := I) (M := M) g 2
            (L.a1 (I := I) (M := M) T) ≤
          (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨κ, D, hκ, hD, hsplit⟩ :=
    remainder_diag_h2 (I := I) (M := M) hDim g
  refine ⟨κ, D, hκ, hD, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3
  have hmain :=
    hsplit T hT hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3
  dsimp only at hmain ⊢
  refine ⟨?_, hmain.2.1, hmain.2.2⟩
  simp only [principalResidual]
  rw [hmain.1]
  abel

/-- After subtracting the complete canonical second-order action, the smooth
lower residual is exactly the low-base first-order action and has the sharp
diagonal `H3 → H2` jet bound. -/
theorem lowResidual_diag
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ D : ℝ → ℝ, (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      let hδ_lt : δ < 1 :=
        lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
      let L : LowBaseActionData g :=
        lowBaseData (I := I) (M := M) g g T hδ_lt hδ hδZ
      lowBaseResidual (I := I) (M := M) g T hδ_lt hδ hδZ =
          L.a1 (I := I) (M := M) T ∧
        lowJetSq (I := I) (M := M) g 2
            (lowBaseResidual (I := I) (M := M)
              g T hδ_lt hδ hδZ) ≤
          (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨_, D, _, hD, hsplit⟩ :=
    remainder_diag_h2 (I := I) (M := M) hDim g
  refine ⟨D, hD, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3
  have hmain :=
    hsplit T hT hδ_le hδ0 hδ hδZ R A hR hA hT2 hT3
  dsimp only at hmain ⊢
  have heq :
      lowBaseResidual (I := I) (M := M) g T
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          hδ hδZ =
        (lowBaseData (I := I) (M := M) g g T
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          hδ hδZ).a1 (I := I) (M := M) T := by
    simp only [lowBaseResidual]
    rw [hmain.1]
    abel
  refine ⟨heq, ?_⟩
  rw [heq]
  exact hmain.2.2

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
