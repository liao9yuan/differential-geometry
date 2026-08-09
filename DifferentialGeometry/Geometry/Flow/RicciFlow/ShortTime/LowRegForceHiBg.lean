import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegForceHi
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgAffine

/-!
# High-scale fixed-background Ricci--DeTurck forcing

This module is the arbitrary-background analogue of the frozen high forcing in
`LowRegForceHi`.  It only assembles the three completed coefficient arms and
proves their compatibility with the lower frozen split; construction of those
completed maps remains a separate producer.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The fixed-background zero-state force is the scale inclusion of the
canonical order-two static force. -/
theorem lowBaseForceBg_eq
    (g gB : SmoothRiemannianMetric I M) :
    lowBaseForceBg (I := I) (M := M) g gB =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) ≤ 2 by norm_num)
        (staticForce (I := I) (M := M) g gB (2 : ℝ)) := by
  change
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) ≤ 2 by norm_num)
        (baseForceH2 (I := I) (M := M) g gB) = _
  rw [baseForceH2_eq_static]

/-- The frozen high-scale Ricci--DeTurck split with an independent fixed
background. -/
noncomputable def liftHiNBg
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (v : tensorHs (I := I) (M := M) g 0 2 (4 : ℝ)) :
    tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) :=
  staticForce (I := I) (M := M) g gB (2 : ℝ) +
    lowA2HiBg (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (4 : ℝ) by norm_num) v)
        (radialCLM (I := I) (M := M) g (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (4 : ℝ) by norm_num) v) v) +
    FHi (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v)
        (lowRadialH3 (I := I) (M := M) g ρ
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v))

/-- The lower frozen split formed from an explicitly supplied completed
first-order map. -/
noncomputable def lowBaseNBgWith
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FLo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)) :
    tensorHs (I := I) (M := M) g 0 2 (1 : ℝ) :=
  lowBaseForceBg (I := I) (M := M) g gB +
    lowA2LoBg (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)
      (lowRadialH3 (I := I) (M := M) g ρ u) +
    FLo u
      (lowRadialHs (I := I) (M := M) g ρ
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u))

/-- The fixed-background frozen high split agrees after inclusion with the
completed lower split formed from the same first-order maps. -/
theorem hiNBg_incl
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (FLo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (hA2sq : ∀ w : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (lowA2HiBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal w) =
        (lowA2LoBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal w).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ 4 by norm_num)))
    (hFComm : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)))
    (v : tensorHs (I := I) (M := M) g 0 2 (4 : ℝ)) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
        (liftHiNBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal FHi v) =
      lowBaseNBgWith (I := I) (M := M)
        g gB hρ.le hδ0 hδ_le hreal FLo
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v) := by
  set u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) :=
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v with hudef
  set w : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) :=
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (4 : ℝ) by norm_num) v with hwdef
  have hwu : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u = w := by
    rw [hudef, hwdef]
    exact (tensorHsInclusion_trans_apply (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
      (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v).symm
  have hrad4 : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (3 : ℝ) ≤ (4 : ℝ) by norm_num)
      (radialCLM (I := I) (M := M) g (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ
        w v) =
      radialCLM (I := I) (M := M) g (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ρ
        w u := by
    have h := DFunLike.congr_fun
      (radialCLM_incl (I := I) (M := M) g
        (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
        (show (0 : ℝ) ≤ (4 : ℝ) by norm_num)
        (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) ρ w) v
    simpa only [ContinuousLinearMap.comp_apply, hudef] using h
  have hrad3 : radialCLM (I := I) (M := M) g
      (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ρ w u =
      lowRadialH3 (I := I) (M := M) g ρ u := by
    rw [← hwu]
    exact radialCLM_h3 (I := I) (M := M) g hρ u
  have hradlo : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
      (lowRadialH3 (I := I) (M := M) g ρ u) =
      lowRadialHs (I := I) (M := M) g ρ
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u) :=
    lowRadialH3_incl (I := I) (M := M) g hρ u
  have hA2 : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
      (lowA2HiBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal w
        (radialCLM (I := I) (M := M) g
          (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ w v)) =
      lowA2LoBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)
        (lowRadialH3 (I := I) (M := M) g ρ u) := by
    have h := DFunLike.congr_fun (hA2sq w)
      (radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ w v)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h, hrad4, hrad3, hwu]
  have hA1 : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
      (FHi u (lowRadialH3 (I := I) (M := M) g ρ u)) =
      FLo u
        (lowRadialHs (I := I) (M := M) g ρ
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)) := by
    have h := DFunLike.congr_fun (hFComm u)
      (lowRadialH3 (I := I) (M := M) g ρ u)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h, hradlo]
  rw [show liftHiNBg (I := I) (M := M)
        g gB hρ.le hδ0 hδ_le hreal FHi v =
      staticForce (I := I) (M := M) g gB (2 : ℝ) +
        lowA2HiBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal w
          (radialCLM (I := I) (M := M) g
            (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ w v) +
        FHi u (lowRadialH3 (I := I) (M := M) g ρ u) from rfl,
    show lowBaseNBgWith (I := I) (M := M)
        g gB hρ.le hδ0 hδ_le hreal FLo u =
      lowBaseForceBg (I := I) (M := M) g gB +
        lowA2LoBg (I := I) (M := M) g gB hρ.le hδ0 hδ_le hreal
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)
          (lowRadialH3 (I := I) (M := M) g ρ u) +
        FLo u
          (lowRadialHs (I := I) (M := M) g ρ
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)) from rfl,
    map_add, map_add, (lowBaseForceBg_eq (I := I) (M := M) g gB).symm,
    hA2, hA1, hudef]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
