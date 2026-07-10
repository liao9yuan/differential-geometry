import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAveragePOU
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringItem3
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCTransitionRefine

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 Step C: the C3 producer join

This file wires the concrete Step-A/Step-B data into the abstract finite-hat
center-average convergence capstone `NetLimitData.unifHatCageSelfComp`
(`StepCAveragePOU.lean`).

## Step (1): the cage↔chart-image bridge

`properBallImgOfRad` — general Gauss-lemma bridge (sibling of
`properBallSrcOfRad`): a realized proper-metric closed ball of radius `R <
expRadiusGp` is carried by the normal chart into the Euclidean ball of radius
`expMapC2Radius`.  `hatCageImg` composes it with `hatCageInClosed` to give the
finite-hat cage image inclusion consumed by the capstone's domain inputs
(`hKU`/`hKV`/`hmap`) and by `existsTransUniv`'s `hUx`/`hVy`/`hmaps` obligations.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [Module.Finite Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

/-- **Image form of `properBallSrcOfRad`.**  A realized proper-metric closed ball
`closedBall c R` with `R` strictly below the `g_p` radial normal radius
`expRadiusGp g c` is carried by the normal chart `normalChartAt g c` into the
Euclidean ball `ball 0 (expMapC2Radius g c)`.  Together with `properBallSrcOfRad`
(source membership) this pins both the chart domain and the chart-image radius
from the single scale input `R < expRadiusGp`.

Proof: for `q ∈ closedBall c R`, `dist c q ≤ R < expRadiusGp`, so
`metricBall_subset_normalBall` gives the chart vector `v` with `normalChartAt g c
q = v`, `√(g_c(v,v)) = dist c q < expRadiusGp`, and `‖v‖ < expMapC2Radius` via
`norm_lt_expMapC2Radius_of_sqrt_inner_lt` (the `g_p`-coercivity comparison). -/
theorem properBallImgOfRad
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {c : Y.M} {R : Real}
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R < expRadiusGp (I := I) Y.metric c) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    (NormalCoordinates.normalChartAt (I := I) Y.metric c) '' Metric.closedBall c R ⊆
      Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric c) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := P.ms
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm :
      ∀ x : Y.M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)) := by
    intro x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric x v)
  rintro a ⟨q, hq, rfl⟩
  have hdist_le : dist c q ≤ R := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hq)
  have hed : riemannianEDist I c q = ENNReal.ofReal (dist c q) := by
    have h := P.realizes c q
    simpa [PointedRiemannianManifold.emetricSpace] using h
  have hfin : riemannianEDist I c q ≠ (⊤ : ℝ≥0∞) := by
    rw [hed]; exact ENNReal.ofReal_ne_top
  have hsmall : (riemannianEDist I c q).toReal < expRadiusGp (I := I) Y.metric c := by
    rw [hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c q)]
    exact lt_of_le_of_lt hdist_le hR
  obtain ⟨v, hv_tgt, _hv_dom, hv_len, hy_eq⟩ :=
    metricBall_subset_normalBall (I := I) Y.metric c hEnorm hfin hsmall
  have hchart : NormalCoordinates.normalChartAt (I := I) Y.metric c q = v := by
    have hsymm : (NormalCoordinates.normalChartAt (I := I) Y.metric c).symm v = q := by
      rw [NormalCoordinates.normalChartAt_symm_apply (I := I) Y.metric c hv_tgt]
      exact hy_eq.symm
    rw [← hsymm]
    exact (NormalCoordinates.normalChartAt (I := I) Y.metric c).right_inv hv_tgt
  rw [Metric.mem_ball, dist_zero_right, hchart]
  have hsq : Real.sqrt (Y.metric.inner c v v) < expRadiusGp (I := I) Y.metric c := by
    rw [hv_len]; exact hsmall
  exact norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Y.metric c hsq

/-- **Coercive-tightened image form of `properBallImgOfRad`** (Ruling #4, no boundary analysis).
Same as `properBallImgOfRad` but into the *tighter* Euclidean ball `ball 0 σ` for any `σ` strictly
above `R / √(gpCoerciveConst g c)`.  The proof needs no strictness of the cage: from `dist c q ≤ R`
(closed ball) and the `g_p`-coercivity `gpCoerciveConst g c · ‖v‖² ≤ g_c(v,v)` we get
`√coercive · ‖v‖ ≤ √(g_c(v,v)) = dist c q ≤ R`, hence `‖v‖ ≤ R/√coercive < σ` by the strict
hypothesis.  This is the σ-refined cage-image bound `stepCJoin` consumes for `U γ := ball 0 (σ γ)`. -/
theorem properBallImgOfRad'
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {c : Y.M} {R σ : Real}
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R < expRadiusGp (I := I) Y.metric c)
    (hσ :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R / Real.sqrt (gpCoerciveConst (I := I) Y.metric c) < σ) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    (NormalCoordinates.normalChartAt (I := I) Y.metric c) '' Metric.closedBall c R ⊆
      Metric.ball (0 : E) σ := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := P.ms
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm :
      ∀ x : Y.M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)) := by
    intro x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric x v)
  rintro a ⟨q, hq, rfl⟩
  have hdist_le : dist c q ≤ R := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hq)
  have hed : riemannianEDist I c q = ENNReal.ofReal (dist c q) := by
    have h := P.realizes c q
    simpa [PointedRiemannianManifold.emetricSpace] using h
  have hfin : riemannianEDist I c q ≠ (⊤ : ℝ≥0∞) := by
    rw [hed]; exact ENNReal.ofReal_ne_top
  have hsmall : (riemannianEDist I c q).toReal < expRadiusGp (I := I) Y.metric c := by
    rw [hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c q)]
    exact lt_of_le_of_lt hdist_le hR
  obtain ⟨v, hv_tgt, _hv_dom, hv_len, hy_eq⟩ :=
    metricBall_subset_normalBall (I := I) Y.metric c hEnorm hfin hsmall
  have hchart : NormalCoordinates.normalChartAt (I := I) Y.metric c q = v := by
    have hsymm : (NormalCoordinates.normalChartAt (I := I) Y.metric c).symm v = q := by
      rw [NormalCoordinates.normalChartAt_symm_apply (I := I) Y.metric c hv_tgt]
      exact hy_eq.symm
    rw [← hsymm]
    exact (NormalCoordinates.normalChartAt (I := I) Y.metric c).right_inv hv_tgt
  rw [Metric.mem_ball, dist_zero_right, hchart]
  have hcoerc : 0 < gpCoerciveConst (I := I) Y.metric c := gpCoerciveConst_pos (I := I) Y.metric c
  have hsc : 0 < Real.sqrt (gpCoerciveConst (I := I) Y.metric c) := Real.sqrt_pos.mpr hcoerc
  have hcle : gpCoerciveConst (I := I) Y.metric c * ‖v‖ ^ 2 ≤ Y.metric.inner c v v :=
    gpCoerciveConst_le (I := I) Y.metric c v
  have hsqrt_le :
      Real.sqrt (gpCoerciveConst (I := I) Y.metric c) * ‖v‖ ≤
        Real.sqrt (Y.metric.inner c v v) := by
    have hrw : Real.sqrt (gpCoerciveConst (I := I) Y.metric c) * ‖v‖
        = Real.sqrt (gpCoerciveConst (I := I) Y.metric c * ‖v‖ ^ 2) := by
      rw [Real.sqrt_mul (le_of_lt hcoerc), Real.sqrt_sq (norm_nonneg v)]
    rw [hrw]
    exact Real.sqrt_le_sqrt hcle
  have hgc_le : Real.sqrt (Y.metric.inner c v v) ≤ R := by
    rw [hv_len, hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c q)]
    exact hdist_le
  have hbound : ‖v‖ ≤ R / Real.sqrt (gpCoerciveConst (I := I) Y.metric c) := by
    rw [le_div_iff₀ hsc]
    calc ‖v‖ * Real.sqrt (gpCoerciveConst (I := I) Y.metric c)
        = Real.sqrt (gpCoerciveConst (I := I) Y.metric c) * ‖v‖ := by ring
      _ ≤ Real.sqrt (Y.metric.inner c v v) := hsqrt_le
      _ ≤ R := hgc_le
  exact lt_of_le_of_lt hbound hσ

/-- **Finite-hat cage image inclusion.**  Under the `g_p`-scale input `hR`
(`4 λ^γ < expRadiusGp` at the live center — the `Item3GpScaleInput` field), the
normal chart at `center γ` carries the canonical source cage into the Euclidean
`expMapC2Radius` ball.  Composes `hatCageInClosed` with `properBallImgOfRad`. -/
theorem hatCageImg (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M) (gamma : Fin (pb.A r))
    (hcenter : seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf (gamma : Nat) <
        expRadiusGp (I := I) (X.obj (L.φ n)).metric (center gamma)) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
    (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
        NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
      Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ n)).metric (center gamma)) := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  refine Set.Subset.trans
    (Set.image_mono
      (NetLimitData.hatCageInClosed (I := I) (X := X) hd P L pb r n gamma hcenter)) ?_
  exact properBallImgOfRad (I := I) (X.obj (L.φ n)) (P (L.φ n))
    (c := center gamma) (R := 4 * L.lamInf (gamma : Nat)) hR

/-- **Coercive-tightened cage image inclusion** (Ruling #4, GREEN — no boundary analysis).
The normal chart at `center γ` carries the canonical source cage into the open Euclidean ball
`ball 0 (σ γ)`, for any `σ γ` strictly above the coercive radius `4 λ^γ / √(gpCoerciveConst (center γ))`
(`hσ`).  This is the σ-refined `hcage` that `stepCJoin` consumes for `U γ := Metric.ball 0 (σ γ)`;
the strict scale hypothesis dissolves the open/closed-ball gap (`hatCageInClosed` gives the *closed*
`4 λ^γ` ball, and `properBallImgOfRad'`'s coercivity turns that into `‖v‖ ≤ 4 λ^γ/√coercive < σ γ`).
`hR : 4 λ^γ < expRadiusGp` is the chart-domain scale (`= √coercive · expMapC2Radius`); both `hR` and
`hσ` are packaged in the sibling `SigmaScaleField` (below). -/
theorem hatCageImg' (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M) (gamma : Fin (pb.A r))
    (sigma : Fin (pb.A r) -> Real)
    (hcenter : seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf (gamma : Nat) <
        expRadiusGp (I := I) (X.obj (L.φ n)).metric (center gamma))
    (hσ :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf (gamma : Nat) /
          Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ n)).metric (center gamma)) <
        sigma gamma) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
    (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
        NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
      Metric.ball (0 : E) (sigma gamma) := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  refine Set.Subset.trans
    (Set.image_mono
      (NetLimitData.hatCageInClosed (I := I) (X := X) hd P L pb r n gamma hcenter)) ?_
  exact properBallImgOfRad' (I := I) (X.obj (L.φ n)) (P (L.φ n))
    (c := center gamma) (R := 4 * L.lamInf (gamma : Nat)) (σ := sigma gamma) hR hσ

/-- **σ-discharge of `stepCJoin`'s `hUx`/`hVy` domain-radius hypotheses** (Ruling #2 tail, green).
Given a per-hat radius family `σ` below the `expMapC2Radius` at every live center of every subsequence
index `k` (`hσ` — the `Item3RadiusInput`-shaped `g_p`-scale field, `k`-independent `σ γ`), the domain
`U γ := Metric.ball 0 (σ γ)` sits inside the `expMapC2Radius`-ball that `stepCJoin`'s `hUx`/`hVy`
demand.  This is `Metric.ball_subset_ball` — the σ-parametric domain inputs are discharged from the
single scale field, no per-`k` threading.  (Instantiate with `x`/`y` for `hUx`/`hVy` respectively.) -/
theorem hUx_of_sigma (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M) (σ : Fin (pb.A r) -> Real)
    (hσ : forall gamma : Fin (pb.A r), forall k : Nat,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
      σ gamma ≤ expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)) :
    forall gamma : Fin (pb.A r), forall k : Nat,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
      Metric.ball (0 : E) (σ gamma) ⊆
        Metric.ball (0 : E) (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)) := by
  intro gamma k
  exact Metric.ball_subset_ball (hσ gamma k)

/-- `min`-variant of `hUx_of_sigma` for the `r₁`-capped (`lbl418`-faithful) domain
hypotheses of `stepCJoin` (2026-07-05 statement fix): a per-hat radius `σ` below BOTH
the `lbl418` comparison scale `r₁` (`hσr₁`, the book's `σ ≪ r₁` choice) and the
per-center `expMapC2Radius` (`hσ`) puts `ball 0 (σ γ)` inside the capped ball. -/
theorem hUx_of_sigma_min (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r r₁ : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M) (σ : Fin (pb.A r) -> Real)
    (hσr₁ : forall gamma : Fin (pb.A r), σ gamma ≤ r₁)
    (hσ : forall gamma : Fin (pb.A r), forall k : Nat,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
      σ gamma ≤ expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)) :
    forall gamma : Fin (pb.A r), forall k : Nat,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
      Metric.ball (0 : E) (σ gamma) ⊆
        Metric.ball (0 : E)
          (min r₁ (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k))) := by
  intro gamma k
  exact Metric.ball_subset_ball (le_min (hσr₁ gamma) (hσ gamma k))

/-- **The sibling `g_p`-scale field for the σ-domain discharge** (Ruling #4, `lbl383` family, next to
`Item3GpScaleInput`).  A `k`-independent per-hat radius `σ γ` sandwiched, at every live center of
every subsequence index `k`, between the coercive cage radius and the chart `C²`-radius:
`4 λ^γ / √(gpCoerciveConst (x γ k)) < σ γ ≤ expMapC2Radius (x γ k)`.  The upper bound feeds
`hUx_of_sigma` (`hUx`/`hVy`), the strict lower bound feeds `hatCageImg'`'s `hσ`, and its
`expRadiusGp` consequence (`.expRadiusGp`) feeds `hatCageImg'`'s `hR` — so both cage-image and
domain hypotheses of `stepCJoin` come from this single honest field. -/
def SigmaScaleField (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M) (σ : Fin (pb.A r) -> Real) : Prop :=
  forall gamma : Fin (pb.A r), forall k : Nat,
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
    4 * L.lamInf (gamma : Nat) /
        Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ k)).metric (x gamma k)) < σ gamma ∧
      σ gamma ≤ expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)

/-- The `expRadiusGp` scale (`4 λ^γ < expRadiusGp`, `hatCageImg'`'s `hR`) is a consequence of the
sibling field: `4 λ^γ/√c < σ γ ≤ expMapC2Radius` gives `4 λ^γ < √c · expMapC2Radius = expRadiusGp`. -/
theorem SigmaScaleField.expRadiusGp {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P}
    {pb : hd.PackingBound D} {r : Real}
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M} {σ : Fin (pb.A r) -> Real}
    (hfield : SigmaScaleField (I := I) hd P L pb r x σ)
    (gamma : Fin (pb.A r)) (k : Nat) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
    4 * L.lamInf (gamma : Nat) <
      expRadiusGp (I := I) (X.obj (L.φ k)).metric (x gamma k) := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
  obtain ⟨hlo, hhi⟩ := hfield gamma k
  have hsc : 0 < Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ k)).metric (x gamma k)) :=
    Real.sqrt_pos.mpr (gpCoerciveConst_pos (I := I) (X.obj (L.φ k)).metric (x gamma k))
  have h1 : 4 * L.lamInf (gamma : Nat) /
      Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ k)).metric (x gamma k)) <
      expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k) := lt_of_lt_of_le hlo hhi
  rw [div_lt_iff₀ hsc] at h1
  exact h1.trans_eq (mul_comm _ _)

/-- **Limit-membership bridge for the capstone's `hKV`.**  If the two-index Step-B
maps `B a` each carry `v` into a CLOSED set `V'` and `B → Binf` in `C∞` on compacts
of `U ∋ v`, then the limit map lands in `V'` as well.  With `V' ⊆ V γ` a closed
sub-ball of the open domain `V γ`, this discharges `unifHatCageSelfComp`'s `hKV`
(`Binf γ v ∈ V γ`) from an all-index hypothesis `∀ a, B γ a v ∈ V'`. -/
theorem binfMemClosed {U V' : Set E} {B : Nat -> E -> E} {Binf : E -> E}
    (hB : MapCInfConvOnCompacts U B Binf) {v : E} (hv : v ∈ U)
    (hV'closed : IsClosed V') (hmem : forall a : Nat, B a v ∈ V') :
    Binf v ∈ V' :=
  hV'closed.mem_of_tendsto (tendsto_of_cInf hB hv) (Filter.Eventually.of_forall hmem)

set_option maxHeartbeats 800000 in
/-- **C3 join, fixed-subsequence form (shape A).**  `unifHatCageSelfComp` with the two
book-external/limit obligations discharged from the producer bridges: `hR` from the
`Item3GpScaleInput` honest scale field (`hgp`), and `hKV` from `binfMemClosed` (the two-index
maps land in a closed `V' γ ⊆ V γ`, so their `C∞`-limit `Binf γ` does too).  `B`/`A` stay
abstract; the concrete Step-B transition maps are plugged by the outer wrapper. -/
theorem stepCJoinFixed (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real -> (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hgp : Item3GpScaleInput (I := I) hd D P L)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n -> 0 < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma x ≠ 0 ->
            dist x (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
              (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y) x)
            join x (radSeq a b x))
    (hmap :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall a b : Nat, forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        A gamma b (B gamma a v) ∈
          (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma)
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r), MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r), MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆ U gamma)
    (V' : Fin (pb.A r) -> Set E)
    (hV'closed : forall gamma : Fin (pb.A r), IsClosed (V' gamma))
    (hV'sub : forall gamma : Fin (pb.A r), V' gamma ⊆ V gamma)
    (hKV0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        forall a : Nat, B gamma a v ∈ V' gamma) :
    let hcomplete := NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
                (centerAverage.activeFill
                  (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
                  (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y))
                join (fun y : (X.obj (L.φ n)).M => y) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFillSelf (I := I)
                  (g := (X.obj (L.φ n)).metric)
                  (μ := fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
                  (pts := ptsSeq a b) (join := join)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy) (hactive_mem a b y hy)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.1)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  exact NetLimitData.unifHatCageSelfComp hd P L pb r n rho hrho join radSeq center U V
    B Binf A Ainf hconn hX hcenter
    (fun gamma => hgp n (gamma : Nat) (center gamma) (hcenter gamma))
    hrad hactive_mem hstrict hmap hVopen hB hA hBcont hAcont hid hKU
    (fun gamma v hv =>
      hV'sub gamma (binfMemClosed (hB gamma) (hKU gamma hv) (hV'closed gamma)
        (hKV0 gamma v hv)))

set_option maxHeartbeats 800000 in
/-- **C3 join, fixed-subsequence explicit-weight form.**  This is the `4 * lamInf`
finite-hat endpoint matching `unifHatCageData`: it consumes an explicit normalized
`WeightDataOn` package instead of a bundled smooth partition of unity.  It is not yet the
book's `5 * lamInf` support-ball instantiation, which still needs a support-set adapter. -/
theorem stepCJoinDataFixed (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (mu : (X.obj (L.φ n)).M -> Fin (pb.A r) -> Real)
    (hmu :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      centerAverage.WeightDataOn
        (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
        (fun gamma : Fin (pb.A r) =>
          (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
            (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
            Set (X.obj (L.φ n)).M)) mu)
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hgp : Item3GpScaleInput (I := I) hd D P L)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n -> 0 < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), mu x gamma ≠ 0 ->
            dist x (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill mu (ptsSeq a b)
              (fun y : (X.obj (L.φ n)).M => y) x)
            join x (radSeq a b x))
    (hmap :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall a b : Nat, forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        A gamma b (B gamma a v) ∈
          (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma)
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r), MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r), MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆ U gamma)
    (V' : Fin (pb.A r) -> Set E)
    (hV'closed : forall gamma : Fin (pb.A r), IsClosed (V' gamma))
    (hV'sub : forall gamma : Fin (pb.A r), V' gamma ⊆ V gamma)
    (hKV0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        forall a : Nat, B gamma a v ∈ V' gamma) :
    let hcomplete := NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                mu
                (centerAverage.activeFill mu (ptsSeq a b)
                  (fun y : (X.obj (L.φ n)).M => y))
                join (fun y : (X.obj (L.φ n)).M => y) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFillSelf (I := I)
                  (g := (X.obj (L.φ n)).metric) (μ := mu)
                  (pts := ptsSeq a b) (join := join)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy) (hactive_mem a b y hy)
                  ((hmu.data hy).1.1) ((hmu.data hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  exact NetLimitData.unifHatCageData hd P L pb r n mu hmu join radSeq center U V
    B Binf A Ainf hconn hX hcenter
    (fun gamma => hgp n (gamma : Nat) (center gamma) (hcenter gamma))
    hrad hactive_mem hstrict hmap hVopen hB hA hBcont hAcont hid hKU
    (fun gamma v hv =>
      hV'sub gamma (binfMemClosed (hB gamma) (hKU gamma hv) (hV'closed gamma)
        (hKV0 gamma v hv)))

set_option maxHeartbeats 1600000 in
/-- **C3 producer join (shape B).**  Feeds the concrete Step-B same-manifold transition maps
`normalTransition` (indexed by the two sequence indices, over the reindexed sequence
`X ∘ L.φ`) into `stepCJoinFixed`: `existsTransUniv` produces the subsequence `phi` and the
`C∞` limit maps `Jinf`/`Jbarinf` with the two-sided cocycle, then `stepCJoinFixed` averages
them to the identity on the frozen source ball.  Overlap/cocycle/domain data for
`existsTransUniv` are honest parametric inputs (its own style); the map-dependent
`hactive0`/`hstrict0`/`hmap0`/`hKV0` are stated over ALL sequence indices and specialised at
`phi` (the `decodedCompPts` reindexing is a definitional identity). -/
theorem stepCJoin (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (input : ExpInverseDerivBoundInput (I := I) X)
    (x y : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M)
    (U V : Fin (pb.A r) -> Set E)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real -> (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hgp : Item3GpScaleInput (I := I) hd D P L)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (x gamma n))
    (hrad : forall a b : Nat, forall xx : (X.obj (L.φ n)).M,
      xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n -> 0 < radSeq a b xx)
    (hU : forall gamma : Fin (pb.A r), IsOpen (U gamma))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hovlJ : forall gamma : Fin (pb.A r), forall k : Nat,
      NormalOverlapOn (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k) (U gamma))
    (hovlJbar : forall gamma : Fin (pb.A r), forall k : Nat,
      NormalOverlapOn (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k) (V gamma))
    (hUx : forall gamma : Fin (pb.A r), forall k : Nat,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
      U gamma ⊆ Metric.ball (0 : E)
        (min input.r₁ (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k))))
    (hmapsJ : forall gamma : Fin (pb.A r), forall k : Nat,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (x gamma k) z) (U gamma)
        ((fun v : E => (expMap (I := I) (X.obj (L.φ k)).metric (y gamma k)
            (show TangentSpace I (y gamma k) from v) : (X.obj (L.φ k)).M)) ''
          Metric.ball (0 : E)
            (min input.r₁ (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (y gamma k)))))
    (hVy : forall gamma : Fin (pb.A r), forall k : Nat,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
      V gamma ⊆ Metric.ball (0 : E)
        (min input.r₁ (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (y gamma k))))
    (hmapsJbar : forall gamma : Fin (pb.A r), forall k : Nat,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (y gamma k) z) (V gamma)
        ((fun v : E => (expMap (I := I) (X.obj (L.φ k)).metric (x gamma k)
            (show TangentSpace I (x gamma k) from v) : (X.obj (L.φ k)).M)) ''
          Metric.ball (0 : E)
            (min input.r₁ (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)))))
    (hLeft : forall gamma : Fin (pb.A r), forall k : Nat, forall z, z ∈ U gamma ->
      normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k)
        (normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k) z) = z)
    (hRight : forall gamma : Fin (pb.A r), forall k : Nat, forall w, w ∈ V gamma ->
      normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k)
        (normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k) w) = w)
    (hactive0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall a b : Nat, forall xx : (X.obj (L.φ n)).M,
        xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma xx ≠ 0 ->
            dist xx (NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric
              (fun gamma => x gamma n)
              (fun gamma a => normalTransition (I := I) (X.obj (L.φ a)) (x gamma a) (y gamma a))
              (fun gamma b => normalTransition (I := I) (X.obj (L.φ b)) (y gamma b) (x gamma b))
              a b xx gamma) < radSeq a b xx)
    (hstrict0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      forall a b : Nat, forall xx : (X.obj (L.φ n)).M,
        xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun yy : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma yy)
              (NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric
                (fun gamma => x gamma n)
                (fun gamma a => normalTransition (I := I) (X.obj (L.φ a)) (x gamma a) (y gamma a))
                (fun gamma b => normalTransition (I := I) (X.obj (L.φ b)) (y gamma b) (x gamma b))
                a b)
              (fun yy : (X.obj (L.φ n)).M => yy) xx)
            join xx (radSeq a b xx))
    (hmap0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall a b : Nat, forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (x gamma n)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        normalTransition (I := I) (X.obj (L.φ b)) (y gamma b) (x gamma b)
          (normalTransition (I := I) (X.obj (L.φ a)) (x gamma a) (y gamma a) v) ∈
          (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (x gamma n)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (x gamma n)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆ U gamma)
    (V' : Fin (pb.A r) -> Set E)
    (hV'closed : forall gamma : Fin (pb.A r), IsClosed (V' gamma))
    (hV'sub : forall gamma : Fin (pb.A r), V' gamma ⊆ V gamma)
    (hKV0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (x gamma n)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        forall a : Nat, normalTransition (I := I) (X.obj (L.φ a)) (x gamma a) (y gamma a) v ∈ V' gamma) :
    exists phi : Nat -> Nat, StrictMono phi /\
      (let hcomplete := NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
       letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
       letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
       letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
       letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
       letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
       letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
       letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
       letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
         Manifold.metrizableSpace I (X.obj (L.φ n)).M
       letI : T3Space (X.obj (L.φ n)).M := inferInstance
       letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
         ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
       letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
         ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
       letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
       let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric
         (fun gamma => x gamma n)
         (fun gamma a => normalTransition (I := I) (X.obj (L.φ (phi a))) (x gamma (phi a)) (y gamma (phi a)))
         (fun gamma b => normalTransition (I := I) (X.obj (L.φ (phi b))) (y gamma (phi b)) (x gamma (phi b)))
       forall eps : Real, eps > 0 -> exists N : Nat,
         forall a : Nat, a >= N -> forall b : Nat, b >= N ->
           forall xx : (X.obj (L.φ n)).M,
             xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
               dist xx
                 (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                   (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                   (fun yy : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma yy)
                   (centerAverage.activeFill
                     (fun yy : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma yy)
                     (ptsSeq a b) (fun yy : (X.obj (L.φ n)).M => yy))
                   join (fun yy : (X.obj (L.φ n)).M => yy)
                   (fun xx => radSeq (phi a) (phi b) xx)
                   (fun yy : (X.obj (L.φ n)).M => yy)
                   (fun yy hy => centerAverage.inputOfFillSelf (I := I)
                     (g := (X.obj (L.φ n)).metric)
                     (μ := fun yy : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma yy)
                     (pts := ptsSeq a b) (join := join)
                     (r := fun xx => radSeq (phi a) (phi b) xx) (qstar := fun yy : (X.obj (L.φ n)).M => yy)
                     yy hcomplete (hrad (phi a) (phi b) yy hy) (hactive0 (phi a) (phi b) yy hy)
                     ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                       (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                       (rho := rho) (hrho := hrho) a b hy).1.1)
                     ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                       (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                       (rho := rho) (hrho := hrho) a b hy).1.2.1)
                     (hstrict0 (phi a) (phi b) yy hy)) xx) < eps) := by
  classical
  obtain ⟨phi, hphi, Jinf, Jbarinf, hspec⟩ :=
    existsTransUniv (I := I) (X := X.subseq L.φ) (input.subseq L.φ) x y U V
      hU hVopen hovlJ hovlJbar hUx hmapsJ hVy hmapsJbar hLeft hRight
  refine ⟨phi, hphi, ?_⟩
  exact stepCJoinFixed hd P L pb r n rho hrho join
    (fun a b => radSeq (phi a) (phi b))
    (fun gamma => x gamma n) U V
    (fun gamma a => normalTransition (I := I) (X.obj (L.φ (phi a))) (x gamma (phi a)) (y gamma (phi a)))
    Jinf
    (fun gamma b => normalTransition (I := I) (X.obj (L.φ (phi b))) (y gamma (phi b)) (x gamma (phi b)))
    Jbarinf
    hconn hX hcenter hgp
    (fun a b => hrad (phi a) (phi b))
    (fun a b => hactive0 (phi a) (phi b))
    (fun a b => hstrict0 (phi a) (phi b))
    (fun gamma a b => hmap0 gamma (phi a) (phi b))
    hVopen
    (fun gamma => (hspec gamma).2.2.2.2.1)
    (fun gamma => (hspec gamma).2.2.2.2.2.1)
    (fun gamma => (hspec gamma).2.2.1)
    (fun gamma => (hspec gamma).2.2.2.1)
    (fun gamma => (hspec gamma).2.2.2.2.2.2.1)
    hKU V' hV'closed hV'sub
    (fun gamma v hv a => hKV0 gamma v hv (phi a))

end HCGCompactness
end DifferentialGeometry


