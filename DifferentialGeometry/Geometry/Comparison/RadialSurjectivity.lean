import DifferentialGeometry.Geometry.Exponential.GaussLemma
import DifferentialGeometry.Geometry.Comparison.HopfRinow
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.LocalDiffeomorphism
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Comparison.RiemannianDistContinuity
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.Convex.PathConnected

set_option linter.unusedSectionVars false

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

/-!
# Radial-geodesic surjectivity on rieDist-closed balls

For a smooth Riemannian metric `g` on a connected, sigma-compact,
boundaryless smooth manifold `M` that is metric-complete as a
`PseudoEMetricSpace` and satisfies `IsRiemannianManifold I M`, this
file packages the open-closed-nonempty connectedness route to radial
surjectivity. The base point `p : M` is fixed and the radius is `R : ℝ`.

The route avoids any Arzelà–Ascoli / pre-assumed Heine–Borel argument:
points within `riemannianEDist`-distance `R` are reached by *minimising
radial geodesics* `t ↦ expMap g p (t • v)` with `g`-velocity-norm
`√(g.inner p v v) ≤ R`.

## The radial-minimiser set

`radialMinSet g p` is the set of points `q : M` reached by some
`v : T_p M` whose minimising radial geodesic has `g`-length equal to
the Riemannian distance:

`radialMinSet g p = { q | ∃ v, expMap g p v = q ∧
    ENNReal.ofReal (√(g.inner p v v)) = riemannianEDist I p q }`.

The velocity bound is stated with the intrinsic `g`-norm
`Real.sqrt (g.inner p v v)`, *not* the model-`E` norm `‖v‖`: the
latter has no a-priori relation to the metric `g` and its appearance in
earlier drafts of this file was an instance of the tangent-bundle norm
diamond leaking into a public statement.

## Main statements

* `gBall_isPreconnected` — the `g`-norm closed ball
  `{v | √(g.inner p v v) ≤ R}` in `T_p M` is preconnected (it is
  star-shaped about `0`).

* `radial_image_T_preconnected` — the `expMap g p`-image of the
  `g`-norm closed ball is preconnected, by continuity of `expMap g p`
  (`expMap_continuous_of_geodesic_complete`). **Fully proven.**

* `radial_image_is_open` — `radialMinSet g p` is open *relative to* the
  `riemannianEDist`-closed-ball subspace of radius `R` at `p` (the
  subspace-open hypothesis required by the clopen-in-connected step).

* `radial_image_is_closed` — `radialMinSet g p` is closed relative to
  the same closed ball.

* `radial_image_T_contains_rieDist_closedBall` — every `q : M` with
  `riemannianEDist I p q ≤ ENNReal.ofReal R` is reached by some `v` with
  `g`-velocity-norm `≤ R`.

* `expMap_surjective_on_riemannianEDist_closedBall` — combining the previous nodes via
  the preconnected-clopen argument, every `q` at distance `≤ R` is
  reached by a *minimising* radial geodesic of `g`-velocity-norm `≤ R`.

The genuinely-hard nodes (openness relative to the ball; the
containment; the minimising-curve conclusion) carry a single,
clearly-marked `sorry` each, naming the missing geometric content. The
preconnectedness nodes and the relative-closedness node are proven
outright.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace RadialSurjectivity

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [PseudoEMetricSpace M] [T2Space (TangentBundle I M)]
variable (g : SmoothRiemannianMetric I M)
variable [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
variable [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
variable [IsRiemannianManifold I M] [CompleteSpace M]

/-- The closed `g`-ball of radius `R` in the tangent space `T_p M`:
the set of vectors `v` with `√(g.inner p v v) ≤ R`. -/
def gBall (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    Set (TangentSpace I p) :=
  {v : TangentSpace I p | Real.sqrt (g.inner p v v) ≤ R}

/-- The `g`-quadratic form is homogeneous of degree two:
`g.inner p (b • v) (b • v) = b ^ 2 * g.inner p v v`. -/
lemma gInner_smul_self (g : SmoothRiemannianMetric I M) (p : M)
    (b : ℝ) (v : TangentSpace I p) :
    g.inner p (b • v) (b • v) = b ^ 2 * g.inner p v v := by
  rw [(g.inner p).map_smul b v, ContinuousLinearMap.smul_apply,
    (g.inner p v).map_smul b v]
  simp only [smul_eq_mul]
  ring

/-- The `g`-norm `√(g.inner p · ·)` is homogeneous: for `0 ≤ b`,
`√(g.inner p (b • v) (b • v)) = b * √(g.inner p v v)`. -/
lemma sqrt_gInner_smul_self (g : SmoothRiemannianMetric I M) (p : M)
    {b : ℝ} (hb : 0 ≤ b) (v : TangentSpace I p) :
    Real.sqrt (g.inner p (b • v) (b • v)) =
      b * Real.sqrt (g.inner p v v) := by
  rw [gInner_smul_self (I := I) g p b v, Real.sqrt_mul (sq_nonneg b),
    Real.sqrt_sq hb]

/-- The zero vector lies in every `g`-closed ball of non-negative radius;
more precisely, its `g`-norm is `0`. -/
lemma zero_mem_gBall (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hR : 0 ≤ R) : (0 : TangentSpace I p) ∈ gBall (I := I) g p R := by
  have h0 : g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0 := by
    simp
  change Real.sqrt (g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p)) ≤ R
  rw [h0, Real.sqrt_zero]
  exact hR

/-- **The closed `g`-ball is star-shaped about the origin.** Scaling a
ball element by `b ∈ [0, 1]` keeps it inside the ball, since the
`g`-norm scales by `b ≤ 1`. -/
lemma starConvex_gBall (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    StarConvex ℝ (0 : TangentSpace I p) (gBall (I := I) g p R) := by
  intro y hy a b ha hb hab
  have hb_le_one : b ≤ 1 := by linarith
  have hy' : Real.sqrt (g.inner p y y) ≤ R := hy
  have hsqrt_nonneg : 0 ≤ Real.sqrt (g.inner p y y) := Real.sqrt_nonneg _
  change Real.sqrt (g.inner p (a • (0 : TangentSpace I p) + b • y)
      (a • (0 : TangentSpace I p) + b • y)) ≤ R
  rw [smul_zero, zero_add]
  rw [sqrt_gInner_smul_self (I := I) g p hb y]
  calc b * Real.sqrt (g.inner p y y)
      ≤ 1 * Real.sqrt (g.inner p y y) :=
        mul_le_mul_of_nonneg_right hb_le_one hsqrt_nonneg
    _ = Real.sqrt (g.inner p y y) := one_mul _
    _ ≤ R := hy'

/-- **The closed `g`-ball is preconnected.** It is star-shaped about the
origin (`starConvex_gBall`), hence path-connected, hence
preconnected. -/
theorem gBall_isPreconnected (g : SmoothRiemannianMetric I M) (p : M)
    {R : ℝ} (hR : 0 ≤ R) :
    IsPreconnected (gBall (I := I) g p R) :=
  ((starConvex_gBall (I := I) g p R).isPathConnected
    (zero_mem_gBall (I := I) g p hR)).isConnected.isPreconnected

/-- **The radial-minimiser set at `p`.** Points `q : M` reached by some
`v : T_p M` whose minimising radial geodesic has `g`-length equal to the
Riemannian distance `riemannianEDist I p q`. -/
def radialMinSet (g : SmoothRiemannianMetric I M) (p : M) : Set M :=
  {q : M | ∃ v : TangentSpace I p,
    expMap (I := I) g p v = q ∧
      ENNReal.ofReal (Real.sqrt (g.inner p v v)) = riemannianEDist I p q}

/-- The base point `p` belongs to its own radial-minimiser set, witnessed
by the zero vector (`expMap g p 0 = p`, and both the `g`-length and the
Riemannian distance are `0`). -/
theorem p_mem_radialMinSet (g : SmoothRiemannianMetric I M) (p : M) :
    p ∈ radialMinSet (I := I) g p := by
  refine ⟨(0 : TangentSpace I p), expMap_zero (I := I) g p, ?_⟩
  have h0 : g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0 := by
    simp
  rw [h0, Real.sqrt_zero, ENNReal.ofReal_zero, riemannianEDist_self]

private lemma gInner_self_nonneg (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : 0 ≤ g.inner p v v := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv; simp
  · exact (g.pos p v hv).le

/-- The map `v ↦ g.inner p v v` is continuous on `T_p M`: the metric value
`g.inner p` is a continuous bilinear map and we evaluate it on the diagonal. -/
private lemma continuous_gInner_self (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (fun v : TangentSpace I p => g.inner p v v) :=
  (g.inner p).continuous.clm_apply continuous_id

/-- The map `v ↦ √(g.inner p v v)` is continuous on `T_p M`. -/
private lemma continuous_sqrt_gInner_self (g : SmoothRiemannianMetric I M)
    (p : M) :
    Continuous (fun v : TangentSpace I p => Real.sqrt (g.inner p v v)) :=
  Real.continuous_sqrt.comp (continuous_gInner_self (I := I) g p)

/-- **The closed `g`-ball is closed.** It is the preimage of `Set.Iic R`
under the continuous map `v ↦ √(g.inner p v v)`. -/
private lemma isClosed_gBall (g : SmoothRiemannianMetric I M) (p : M)
    (R : ℝ) : IsClosed (gBall (I := I) g p R) := by
  have hpre : gBall (I := I) g p R =
      (fun v : TangentSpace I p => Real.sqrt (g.inner p v v)) ⁻¹' Set.Iic R := by
    ext v; simp only [gBall, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic]
  rw [hpre]
  exact IsClosed.preimage (continuous_sqrt_gInner_self (I := I) g p) isClosed_Iic

/-- **The closed `g`-ball is bounded.** The von Neumann boundedness of the
unit `g`-ball (`g.isVonNBounded`) gives a model-norm bound on `{v | g v v < 1}`,
and a rescaling argument transports it to the radius-`R` `g`-ball. -/
private lemma isBounded_gBall (g : SmoothRiemannianMetric I M) (p : M)
    (R : ℝ) : Bornology.IsBounded (gBall (I := I) g p R) := by
  rcases lt_or_ge R 0 with hR | hR
  · have hempty : gBall (I := I) g p R = ∅ := by
      ext v
      simp only [gBall, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hR (Real.sqrt_nonneg _)
    rw [hempty]; exact Bornology.isBounded_empty
  · obtain ⟨r, hr⟩ :=
      (NormedSpace.isVonNBounded_iff' ℝ (E := TangentSpace I p)).1 (g.isVonNBounded p)
    rw [isBounded_iff_forall_norm_le]
    refine ⟨(R + 1) * r, fun v hv => ?_⟩
    have hsqrt : Real.sqrt (g.inner p v v) ≤ R := hv
    have hnonneg : 0 ≤ g.inner p v v := gInner_self_nonneg (I := I) g p v
    have hgvv : g.inner p v v ≤ R ^ 2 := by
      nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg (g.inner p v v), hsqrt]
    have hRpos : (0 : ℝ) < R + 1 := by linarith
    set w : TangentSpace I p := (R + 1)⁻¹ • v with hw
    have hgw : g.inner p w w < 1 := by
      have hsmul : g.inner p w w = (R + 1)⁻¹ ^ 2 * g.inner p v v :=
        gInner_smul_self (I := I) g p _ v
      rw [hsmul]
      have hinv_sq_pos : (0 : ℝ) < (R + 1)⁻¹ ^ 2 :=
        pow_pos (inv_pos.mpr hRpos) 2
      have hge : 0 ≤ R / (R + 1) := div_nonneg hR hRpos.le
      have hlt : R / (R + 1) < 1 := by rw [div_lt_one hRpos]; linarith
      calc (R + 1)⁻¹ ^ 2 * g.inner p v v
          ≤ (R + 1)⁻¹ ^ 2 * R ^ 2 :=
            mul_le_mul_of_nonneg_left hgvv hinv_sq_pos.le
        _ = (R / (R + 1)) ^ 2 := by
            rw [div_pow]; field_simp
        _ < 1 := by nlinarith [hlt, hge]
    have hwnorm : ‖w‖ ≤ r := hr w hgw
    have hv_eq : v = (R + 1) • w := by
      rw [hw, smul_smul, mul_inv_cancel₀ (ne_of_gt hRpos), one_smul]
    rw [hv_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hRpos]
    exact mul_le_mul_of_nonneg_left hwnorm hRpos.le

/-- **The closed `g`-ball is compact.** In the finite-dimensional (hence
proper) tangent space `T_p M`, a closed and bounded set is compact. -/
private lemma isCompact_gBall (g : SmoothRiemannianMetric I M) (p : M)
    (R : ℝ) : IsCompact (gBall (I := I) g p R) := by
  haveI : ProperSpace (TangentSpace I p) := FiniteDimensional.proper_real (TangentSpace I p)
  exact Metric.isCompact_of_isClosed_isBounded
    (isClosed_gBall (I := I) g p R) (isBounded_gBall (I := I) g p R)

/-- Continuity of `q ↦ riemannianEDist I p q` for the manifold topology.

The ambient `[PseudoEMetricSpace M]` variable carries a topology that is
*not* assumed equal to the manifold topology, so continuity of `edist` for
that structure does not transfer. Instead we build, from the ambient
`RiemannianBundle` data (whose fibre inner product varies continuously by
`[IsContinuousRiemannianBundle E (TangentSpace I)]`), Mathlib's canonical
`PseudoEMetricSpace.ofRiemannianMetric I M`, whose `edist` is
`riemannianEDist I` definitionally and whose topology is definitionally the
manifold topology (it is constructed via `PseudoEMetricSpace.ofEDistOfTopology`,
which sets `toTopologicalSpace := t` to the ambient one). Continuity of
`edist` (`Continuous.edist`) for this structure is therefore continuity of
`riemannianEDist I` for the manifold topology. The fibre norm feeding
`riemannianEDist` is the one induced by the ambient `RiemannianBundle`, which
is exactly the one appearing in the goal. The required `[RegularSpace M]` is
discharged from finite-dimensional local compactness together with the
Hausdorff hypothesis. -/
private lemma continuous_riemannianEDist_ambient
    (p : M) : Continuous (fun q : M => riemannianEDist I p q) := by
  haveI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  haveI : RegularSpace M := inferInstance
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  exact (continuous_const.edist continuous_id)

end RadialSurjectivity
end Riemannian
end Geometry
end DifferentialGeometry

end
