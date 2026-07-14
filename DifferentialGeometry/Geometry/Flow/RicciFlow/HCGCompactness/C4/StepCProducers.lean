import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAveragePOU
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringItem3
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCTransitionRefine
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.MetricCompactnessInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtomConv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtomDiagonal
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCPairTail

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
(`hKU`/`hKV`) and by `existsTransUniv`'s `hUx`/`hVy`/`hmaps` obligations.
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

/-- **Finite-hat cage image inclusion.**  Under the packing-local `g_p` scale
fact `hR` (`4 λ^γ < expRadiusGp` at the live center), the
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
index `k` (`hσ` — the `SigmaScaleField` upper bound, with `k`-independent `σ γ`), the domain
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

/-- The sigma-scale inequalities at one index of the net-limit subsequence. -/
def SigmaScaleAt (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M)
    (σ : Fin (pb.A r) -> Real) (n : Nat) : Prop :=
  forall gamma : Fin (pb.A r),
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    4 * L.lamInf (gamma : Nat) /
        Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ n)).metric (x gamma n)) < σ gamma ∧
      σ gamma ≤ expMapC2Radius (I := I) (X.obj (L.φ n)).metric (x gamma n)

/-- The finite family of sigma-scale inequalities eventually holds along the
net-limit subsequence. -/
def SigmaScaleTail (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M)
    (σ : Fin (pb.A r) -> Real) : Prop :=
  ∀ᶠ n in Filter.atTop, SigmaScaleAt (I := I) hd P L pb r x σ n

/-- **The sibling `g_p`-scale field for the σ-domain discharge** (Ruling #4,
`lbl383` family).  A `k`-independent per-hat radius `σ γ` sandwiched, at every live center of
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

/-- Restrict an all-index sigma field to one sequence index. -/
theorem SigmaScaleField.at {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P}
    {pb : hd.PackingBound D} {r : Real}
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M}
    {σ : Fin (pb.A r) -> Real}
    (hfield : SigmaScaleField (I := I) hd P L pb r x σ) (n : Nat) :
    SigmaScaleAt (I := I) hd P L pb r x σ n := fun gamma => hfield gamma n

/-- An all-index sigma field gives the corresponding eventual tail. -/
theorem SigmaScaleField.to_tail {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P}
    {pb : hd.PackingBound D} {r : Real}
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M}
    {σ : Fin (pb.A r) -> Real}
    (hfield : SigmaScaleField (I := I) hd P L pb r x σ) :
    SigmaScaleTail (I := I) hd P L pb r x σ :=
  Filter.Eventually.of_forall hfield.at

/-- Reindex a sigma-scale tail along a further strict subsequence. -/
theorem SigmaScaleTail.subseq {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M}
    {σ : Fin (pb.A r) -> Real}
    (htail : SigmaScaleTail (I := I) hd P L pb r x σ)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    SigmaScaleTail (I := I) hd P (L.subseq hψ) pb r
      (fun gamma k => x gamma (ψ k)) σ := by
  filter_upwards [hψ.tendsto_atTop.eventually htail] with n hn
  intro gamma
  exact hn gamma

/-- Shift past an eventual sigma tail to obtain an all-index field on one
strictly refined subsequence. -/
theorem SigmaScaleTail.exists_field
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M}
    {σ : Fin (pb.A r) -> Real}
    (htail : SigmaScaleTail (I := I) hd P L pb r x σ) :
    ∃ ψ : Nat → Nat, ∃ hψ : StrictMono ψ,
      SigmaScaleField (I := I) hd P (L.subseq hψ) pb r
        (fun gamma k => x gamma (ψ k)) σ := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp htail
  let ψ : Nat → Nat := fun k => k + N
  have hψ : StrictMono ψ := by
    simpa only [ψ] using strictMono_id.add_const N
  refine ⟨ψ, hψ, ?_⟩
  intro gamma k
  exact hN (ψ k) (by simp only [ψ]; omega) gamma

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

/-- The H6 radius profile produces a uniform sigma tail at the canonical
totalized net centres, with `σ γ = 8 * λ^γ`. -/
theorem NormalRadiusProfile.sigmaCenterTail
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D : Real} (hD : 0 < D)
    (h16 : (16 : Real) < h.ratio * D)
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist)
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    SigmaScaleTail (I := I) hd P L pb r
      (fun gamma k => seqCenterD hd P L k (gamma : Nat))
      (fun gamma => 8 * L.lamInf (gamma : Nat)) := by
  have hwin : ∀ᶠ n in Filter.atTop, ∀ gamma ∈ Finset.range (pb.A r),
      L.lamInf gamma / 2 ≤
        hd.lambda D (seqRadius hd D P (L.φ n) gamma) :=
    (Filter.eventually_all_finset _).mpr fun gamma _ =>
      (L.lambda_window hd hD P gamma).mono fun _ hgamma => by
        simpa only [NetLimitData.lamInf] using hgamma.1
  filter_upwards [hwin] with n hn
  intro gamma
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  haveI : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have hx : hd.dist (L.φ n) (seqCenterD hd P L n (gamma : Nat))
      (X.obj (L.φ n)).basepoint ≤
      seqRadius hd D P (L.φ n) (gamma : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ n),
      ← seqCenterD_dist_eq hd P L n (gamma : Nat)]
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  constructor
  · have hhalf : (1 / 2 : Real) ≤ gpCoerciveConst (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat)) :=
      hb.half_le_gpConst (L.φ n) (seqCenterD hd P L n (gamma : Nat))
    have hsqrt_half : (1 / 2 : Real) < Real.sqrt (1 / 2 : Real) := by
      have hs := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 1 / 2)
      have hn := Real.sqrt_nonneg (1 / 2 : Real)
      nlinarith
    have hsqrt : (1 / 2 : Real) < Real.sqrt (gpCoerciveConst (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat))) :=
      hsqrt_half.trans_le (Real.sqrt_le_sqrt hhalf)
    have hsc : 0 < Real.sqrt (gpCoerciveConst (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat))) :=
      Real.sqrt_pos.mpr (gpCoerciveConst_pos (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat)))
    have hlam : 0 < L.lamInf (gamma : Nat) :=
      hd.lambda_pos hD (L.rInf (gamma : Nat))
    apply (div_lt_iff₀ hsc).2
    have hfour : (4 : Real) < 8 * Real.sqrt (gpCoerciveConst (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat))) := by
      nlinarith
    calc
      4 * L.lamInf (gamma : Nat) <
          (8 * Real.sqrt (gpCoerciveConst (I := I)
            (X.obj (L.φ n)).metric
              (seqCenterD hd P L n (gamma : Nat)))) *
            L.lamInf (gamma : Nat) :=
        mul_lt_mul_of_pos_right hfour hlam
      _ = (8 * L.lamInf (gamma : Nat)) *
          Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ n)).metric
            (seqCenterD hd P L n (gamma : Nat))) := by ring
  · calc
      8 * L.lamInf (gamma : Nat) =
          16 * (L.lamInf (gamma : Nat) / 2) := by ring
      _ ≤ 16 * hd.lambda D
          (seqRadius hd D P (L.φ n) (gamma : Nat)) :=
        mul_le_mul_of_nonneg_left
          (hn (gamma : Nat) (Finset.mem_range.mpr gamma.isLt)) (by norm_num)
      _ ≤ expMapC2Radius (I := I) (X.obj (L.φ n)).metric
          (seqCenterD hd P L n (gamma : Nat)) :=
        (h.mul_lambda_lt_exp (D := D) (c := 16)
          (R := seqRadius hd D P (L.φ n) (gamma : Nat)) hD h16 hx).le

/-- **Limit-membership bridge for the capstone's `hKV`.**  If the two-index Step-B
maps `B a` eventually carry `v` into a closed set `V'` and `B → Binf` in `C∞` on
compacts of `U ∋ v`, then the limit map lands in `V'` as well. -/
theorem binfMemClosed {U V' : Set E} {B : Nat -> E -> E} {Binf : E -> E}
    (hB : MapCInfConvOnCompacts U B Binf) {v : E} (hv : v ∈ U)
    (hV'closed : IsClosed V') (hmem : ∀ᶠ a in Filter.atTop, B a v ∈ V') :
    Binf v ∈ V' :=
  hV'closed.mem_of_tendsto (tendsto_of_cInf hB hv) hmem

/-- A nonzero normalized limit weight selects an interacting live target, and
the corresponding H6 transition limit lands in the closed six-lambda ball. -/
theorem HasAtomWeightLim.binf_of_weight
    (inp : MetricCompactnessInputs (I := I) X)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.hD P L inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat)) U aInf)
    (hsource : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (alpha.1 : Nat)) z)
        U (L.hatBall inp.decay inp.D P inp.pack r k alpha.1))
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (Binf : InterSlot L inp.pack r alpha -> E -> E)
    (hB : forall target : InterSlot L inp.pack r alpha,
      MapCInfConvOnCompacts U
        (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
        (Binf target))
    {z : E} (hz : z ∈ U) (gamma : Fin (inp.pack.A r))
    (hweight : rawWeights
      (cutRaw (aInf (baseIndex inp.decay inp.realizes inp.pack hr)) aInf
        (baseIndex inp.decay inp.realizes inp.pack hr)) z gamma ≠ 0) :
    ∃ target : InterSlot L inp.pack r alpha,
      target.1.1 = gamma ∧
        Binf target z ∈ Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
  classical
  have hdata := hlim
  dsimp only [HasAtomWeightLim] at hdata
  have hgammaLive : L.alive (gamma : Nat) = true := by
    cases hgamma : L.alive (gamma : Nat) with
    | false =>
        have haZero : aInf gamma = 0 := hdata.1 gamma hgamma
        have hnum : aInf gamma z ≠ 0 :=
          num_ne_of_cut_ne (num_ne_of_raw_ne hweight)
        exact False.elim (hnum (by rw [haZero]; rfl))
    | true => rfl
  have hinter : ∀ᶠ k in Filter.atTop,
      BInter inp.decay inp.D P L.lamInf
        (alpha.1 : Nat) (gamma : Nat) (L.φ k) :=
    hlim.binter_of_weight hgp alpha.1 gamma hz hsource hweight
  let target : InterSlot L inp.pack r alpha :=
    ⟨⟨gamma, hgammaLive⟩, hinter⟩
  have hweightTail := hphi.tendsto_atTop.eventually
    (hlim.weight_ne_tail hz hweight)
  have hrad : Item3RadiusTail (I := I) inp.decay inp.D P L inp.pack r
      (item3RadiusFactor inp.decay inp.D) :=
    inp.normalRadius.radiusScaleTail inp.hD
      (item3Factor_pos inp.decay inp.D) hradD hradRatio
      P inp.realizes L inp.pack r
  have hradTail := hphi.tendsto_atTop.eventually hrad
  have hgpTail := hphi.tendsto_atTop.eventually hgp
  have hcenterTail := hphi.tendsto_atTop.eventually
    (seqCenterD_live inp.decay P L (gamma : Nat) hgammaLive)
  have hmem : ∀ᶠ k in Filter.atTop,
      normalTransition (I := I) (X.obj (L.φ (phi k)))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi k) (gamma : Nat)) z ∈
        Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
    filter_upwards [hweightTail, hradTail, hgpTail, hcenterTail]
      with k hweightK hradK hgpK hcenterK
    letI : TopologicalSpace (X.obj (L.φ (phi k))).M :=
      (X.obj (L.φ (phi k))).topology
    letI : ChartedSpace H (X.obj (L.φ (phi k))).M :=
      (X.obj (L.φ (phi k))).charted
    letI : IsManifold I ∞ (X.obj (L.φ (phi k))).M :=
      (X.obj (L.φ (phi k))).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ (phi k))).M) :=
      (X.obj (L.φ (phi k))).t2TangentBundle
    have hExp : (1 : Real) ≤
        Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)) := by
      rw [show (1 : Real) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_le_exp.mpr
        (mul_nonneg inp.decay.C_nonneg
          (by nlinarith [(inp.decay.lambda_pos inp.hD 0).le]))
    have hfactor : (8 : Real) ≤ item3RadiusFactor inp.decay inp.D := by
      rw [item3RadiusFactor]
      nlinarith
    have hC2 : 8 * L.lamInf (gamma : Nat) ≤
        expMapC2Radius (I := I) (X.obj (L.φ (phi k))).metric
          (seqCenterD inp.decay P L (phi k) (gamma : Nat)) :=
      (mul_le_mul_of_nonneg_right hfactor
        (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat))).le).trans
          (hradK gamma
            (seqCenterD inp.decay P L (phi k) (gamma : Nat)) hcenterK).2
    exact Metric.ball_subset_closedBall
      (inp.weight_trans_small P L r (phi k) hgpK
        (fun j => seqCenterD inp.decay P L j (alpha.1 : Nat))
        (baseIndex inp.decay inp.realizes inp.pack hr) gamma hC2 z hweightK)
  refine ⟨target, rfl, ?_⟩
  exact binfMemClosed (hB target) hz Metric.isClosed_closedBall (by
    simpa only [target] using hmem)

/-- Extract one common H6 transition subsequence for every target interacting
with a fixed live source, while retaining the support-to-closed-ball readout for
the normalized atom limits on any smaller source domain. -/
theorem MetricCompactnessInputs.exists_supp_trans
    (inp : MetricCompactnessInputs (I := I) X)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (hUsub : U ⊆ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.hD P L inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat)) U aInf)
    (hsource : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (alpha.1 : Nat)) z)
        U (L.hatBall inp.decay inp.D P inp.pack r k alpha.1)) :
    ∃ phi : Nat -> Nat, StrictMono phi ∧
      ∃ Jinf : InterSlot L inp.pack r alpha -> E -> E,
      ∃ Jbarinf : InterSlot L inp.pack r alpha -> E -> E,
        (forall target : InterSlot L inp.pack r alpha,
          ContDiffOn Real (⊤ : ℕ∞) (Jinf target)
              (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
          ContDiffOn Real (⊤ : ℕ∞) (Jbarinf target)
              (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
          ContinuousOn (Jinf target)
              (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
          ContinuousOn (Jbarinf target)
              (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
          MapCInfConvOnCompacts
            (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
              (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
            (Jinf target) ∧
          MapCInfConvOnCompacts
            (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)))
            (Jbarinf target) ∧
          (forall z, z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) ->
            Jinf target z ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) ->
              Jbarinf target (Jinf target z) = z) ∧
          (forall w, w ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) ->
            Jbarinf target w ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) ->
              Jinf target (Jbarinf target w) = w)) ∧
        forall z : E, z ∈ U -> forall gamma : Fin (inp.pack.A r),
          rawWeights
            (cutRaw (aInf (baseIndex inp.decay inp.realizes inp.pack hr)) aInf
              (baseIndex inp.decay inp.realizes inp.pack hr)) z gamma ≠ 0 ->
            ∃ target : InterSlot L inp.pack r alpha,
              target.1.1 = gamma ∧
                Jinf target z ∈
                  Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
  classical
  letI : Finite (InterSlot L inp.pack r alpha) :=
    Finite.of_injective
      (fun target : InterSlot L inp.pack r alpha => target.1.1)
      (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact hab)
  obtain ⟨phi, hphi, Jinf, Jbarinf, hspec⟩ :=
    inp.exists_pair_trans hradD hradRatio P L r
      (fun _ : InterSlot L inp.pack r alpha => alpha)
      (fun target : InterSlot L inp.pack r alpha => target.1)
      (fun target : InterSlot L inp.pack r alpha => target.2)
  refine ⟨phi, hphi, Jinf, Jbarinf, hspec, ?_⟩
  intro z hz gamma hweight
  exact hlim.binf_of_weight inp hradD hradRatio P L r hr hgp alpha U aInf
    hsource phi hphi Jinf (fun target K hK hKU p =>
      (hspec target).2.2.2.2.1 K hK (hKU.trans hUsub) p)
    hz gamma hweight

/-- Extract one common H6 transition subsequence for the interacting targets of
every live source.  The dependent pair index avoids a second source-by-source
diagonal and retains each target in the original stabilized pair family. -/
theorem MetricCompactnessInputs.exists_supp_fin
    (inp : MetricCompactnessInputs (I := I) X)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (U : LiveSlot L inp.pack r → Set E)
    (hUsub : ∀ alpha, U alpha ⊆
      Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (hlim : ∀ alpha,
      HasAtomWeightLim (I := I) inp.decay inp.hD P L inp.realizes
        inp.pack r hr
        (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat))
        (U alpha) (aInf alpha))
    (hsource : ∀ alpha, ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (alpha.1 : Nat)) z)
        (U alpha) (L.hatBall inp.decay inp.D P inp.pack r k alpha.1)) :
    ∃ phi : Nat → Nat, StrictMono phi ∧
      ∃ Jinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E,
      ∃ Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E,
        (∀ alpha target,
          ContDiffOn Real (⊤ : ℕ∞) (Jinf alpha target)
              (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
          ContDiffOn Real (⊤ : ℕ∞) (Jbarinf alpha target)
              (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
          ContinuousOn (Jinf alpha target)
              (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
          ContinuousOn (Jbarinf alpha target)
              (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
          MapCInfConvOnCompacts
            (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
              (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
            (Jinf alpha target) ∧
          MapCInfConvOnCompacts
            (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)))
            (Jbarinf alpha target) ∧
          (∀ z, z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
            Jinf alpha target z ∈
                Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
              Jbarinf alpha target (Jinf alpha target z) = z) ∧
          (∀ w, w ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
            Jbarinf alpha target w ∈
                Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
              Jinf alpha target (Jbarinf alpha target w) = w)) ∧
        ∀ alpha z, z ∈ U alpha → ∀ gamma : Fin (inp.pack.A r),
          rawWeights
            (cutRaw
              (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
              (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
            z gamma ≠ 0 →
          ∃ target : InterSlot L inp.pack r alpha,
            target.1.1 = gamma ∧
              Jinf alpha target z ∈
                Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
  classical
  let PairSlot := Σ alpha : LiveSlot L inp.pack r, InterSlot L inp.pack r alpha
  letI (alpha : LiveSlot L inp.pack r) : Finite (InterSlot L inp.pack r alpha) :=
    Finite.of_injective
      (fun target : InterSlot L inp.pack r alpha => target.1.1)
      (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact hab)
  letI : Finite PairSlot := inferInstance
  obtain ⟨phi, hphi, J, Jbar, hspec⟩ :=
    inp.exists_pair_trans hradD hradRatio P L r
      (fun pair : PairSlot => pair.1)
      (fun pair : PairSlot => pair.2.1)
      (fun pair : PairSlot => pair.2.2)
  let Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E :=
    fun alpha target => J ⟨alpha, target⟩
  let Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E :=
    fun alpha target => Jbar ⟨alpha, target⟩
  refine ⟨phi, hphi, Jinf, Jbarinf, ?_, ?_⟩
  · intro alpha target
    exact hspec ⟨alpha, target⟩
  · intro alpha z hz gamma hweight
    exact (hlim alpha).binf_of_weight inp hradD hradRatio P L r hr hgp
      alpha (U alpha) (aInf alpha) (hsource alpha) phi hphi (Jinf alpha)
      (fun target K hK hKU p =>
        (hspec ⟨alpha, target⟩).2.2.2.2.1 K hK
          (hKU.trans (hUsub alpha)) p)
      hz gamma hweight

set_option maxHeartbeats 800000 in
/-- **C3 join, fixed-subsequence form (shape A).**  `unifHatCageSelfComp` with the two
limit obligations discharged from the producer bridges: `hR` from the fixed-index
`Item3GpScaleAt` fact (`hgp`), and `hKV` from `binfMemClosed` (the two-index
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
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r n)
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
    (fun gamma => hgp gamma (center gamma) (hcenter gamma))
    hrad hactive_mem hstrict hVopen hB hA hBcont hAcont hid hKU
    (fun gamma v hv =>
      hV'sub gamma (binfMemClosed (hB gamma) (hKU gamma hv) (hV'closed gamma)
        (Filter.Eventually.of_forall (hKV0 gamma v hv))))

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
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r n)
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
    (fun gamma => hgp gamma (center gamma) (hcenter gamma))
    hrad hactive_mem hstrict hVopen hB hA hBcont hAcont hid hKU
    (fun gamma v hv =>
      hV'sub gamma (binfMemClosed (hB gamma) (hKU gamma hv) (hV'closed gamma)
        (Filter.Eventually.of_forall (hKV0 gamma v hv))))

/-- **C3 producer join (shape B).**  Feeds the concrete Step-B same-manifold transition maps
`normalTransition` (indexed by the two sequence indices, over the reindexed sequence
`X ∘ L.φ`) into `stepCJoinFixed`: the H6-backed `existsTransUniv` produces the
subsequence `phi` and the `C∞` limit maps `Jinf`/`Jbarinf` with the two-sided cocycle,
then `stepCJoinFixed` averages them to the identity on the frozen source ball.  The
fixed convergence domains and independent H6 target-anchor domains, their
metric/exp-radius data, smoothness, overlap, maps-to, and cocycle data for
`existsTransUniv` are honest parametric inputs; the map-dependent
`hactive0`/`hstrict0`/`hKV0` are stated over ALL sequence indices and specialised at
`phi` (the `decodedCompPts` reindexing is a definitional identity). -/
theorem stepCJoin (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (metricInput : NormalCoordMetricBoundInput (I := I) X)
    (x y : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M)
    (U V Ua Va : Fin (pb.A r) -> Set E)
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
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r n)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (x gamma n))
    (hrad : forall a b : Nat, forall xx : (X.obj (L.φ n)).M,
      xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n -> 0 < radSeq a b xx)
    (hU : forall gamma : Fin (pb.A r), IsOpen (U gamma))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hUa : forall gamma : Fin (pb.A r), IsOpen (Ua gamma))
    (hVa : forall gamma : Fin (pb.A r), IsOpen (Va gamma))
    (hUanorm : forall gamma : Fin (pb.A r),
      ∃ Z : Real, ∀ z ∈ Ua gamma, ‖z‖ ≤ Z)
    (hVanorm : forall gamma : Fin (pb.A r),
      ∃ Z : Real, ∀ z ∈ Va gamma, ‖z‖ ≤ Z)
    (hUmetric : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      U gamma ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (x gamma k)))
    (hVmetric : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      V gamma ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (y gamma k)))
    (hUametric : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      Ua gamma ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (x gamma k)))
    (hVametric : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      Va gamma ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (y gamma k)))
    (hUexp : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      U gamma ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)))
    (hVexp : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      V gamma ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (y gamma k)))
    (hUaexp : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Ua gamma ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)))
    (hVaexp : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Va gamma ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (y gamma k)))
    (hJ : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      ContDiffOn Real (⊤ : ℕ∞)
        (normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k))
        (U gamma))
    (hJbar : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      ContDiffOn Real (⊤ : ℕ∞)
        (normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k))
        (V gamma))
    (hovlJ : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      NormalOverlapOn (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k) (U gamma))
    (hovlJbar : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      NormalOverlapOn (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k) (V gamma))
    (hmapJ : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      Set.MapsTo
        (normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k))
        (U gamma) (Va gamma))
    (hmapJbar : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      Set.MapsTo
        (normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k))
        (V gamma) (Ua gamma))
    (hLeft : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop, forall z, z ∈ U gamma ->
      normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k)
        (normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k) z) = z)
    (hRight : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop, forall w, w ∈ V gamma ->
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
  have htail (gamma : Fin (pb.A r)) : ∀ᶠ k in atTop,
      NormalTransAt (I := I)
        (NormalCoordMetricBoundInput.subseq (I := I) metricInput L.φ)
        x y U V Ua Va gamma k := by
    filter_upwards
      [hUmetric gamma, hVmetric gamma, hUametric gamma, hVametric gamma,
        hUexp gamma, hVexp gamma, hUaexp gamma, hVaexp gamma,
        hJ gamma, hJbar gamma, hovlJ gamma, hovlJbar gamma,
        hmapJ gamma, hmapJbar gamma, hLeft gamma, hRight gamma]
      with k hkUM hkVM hkUaM hkVaM hkUE hkVE hkUaE hkVaE
        hkJ hkJbar hkOvl hkOvlbar hkMap hkMapbar hkLeft hkRight
    exact
      { Umetric := hkUM
        Vmetric := hkVM
        Uametric := hkUaM
        Vametric := hkVaM
        Uexp := hkUE
        Vexp := hkVE
        Uaexp := hkUaE
        Vaexp := hkVaE
        J := hkJ
        Jbar := hkJbar
        ovlJ := hkOvl
        ovlJbar := hkOvlbar
        mapJ := hkMap
        mapJbar := hkMapbar
        left := hkLeft
        right := hkRight }
  obtain ⟨phi, hphi, Jinf, Jbarinf, hspec⟩ :=
    existsTransTail (I := I) (X := X.subseq L.φ)
      (NormalCoordMetricBoundInput.subseq (I := I) metricInput L.φ)
      x y U V Ua Va hU hVopen hUa hVa hUanorm hVanorm htail
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
    hVopen
    (fun gamma => by
      simpa only [PointedRiemannianSeq.subseq] using (hspec gamma).2.2.2.2.1)
    (fun gamma => by
      simpa only [PointedRiemannianSeq.subseq] using (hspec gamma).2.2.2.2.2.1)
    (fun gamma => (hspec gamma).2.2.1)
    (fun gamma => (hspec gamma).2.2.2.1)
    (fun gamma => (hspec gamma).2.2.2.2.2.2.1)
    hKU V' hV'closed hV'sub
    (fun gamma v hv a => hKV0 gamma v hv (phi a))

end HCGCompactness
end DifferentialGeometry


