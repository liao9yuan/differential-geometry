import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCNormalBump
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCWeights
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringItem3
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAveragePOU

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4: concrete Step-C atoms

This file specializes the intrinsic quadratic normal bump to the radii used by
the strict inner cover.  It then packages the live ordered-net centers as a
finite atom family and feeds that family to the generic pointwise Step-C weight
producer.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

/-! ## The fixed scalar bump -/

/-- The scalar bump used by the Step-C atoms: it is one through quadratic
radius `(3 * λ)^2` and supported through quadratic radius `(7 * λ / 2)^2`. -/
noncomputable def stepCBump (lam : Real) (hlam : 0 < lam) : ContDiffBump (0 : Real) where
  rIn := (3 * lam) ^ 2
  rOut := (7 * lam / 2) ^ 2
  rIn_pos := sq_pos_of_pos (by positivity)
  rIn_lt_rOut := by nlinarith

@[simp] theorem stepCBump_rIn (lam : Real) (hlam : 0 < lam) :
    (stepCBump lam hlam).rIn = (3 * lam) ^ 2 := rfl

@[simp] theorem stepCBump_rOut (lam : Real) (hlam : 0 < lam) :
    (stepCBump lam hlam).rOut = (7 * lam / 2) ^ 2 := rfl

@[simp] theorem stepCBump_sqrt (lam : Real) (hlam : 0 < lam) :
    Real.sqrt (stepCBump lam hlam).rOut = 7 * lam / 2 := by
  rw [stepCBump_rOut, Real.sqrt_sq_eq_abs, abs_of_pos]
  positivity

/-- The atom support radius lies strictly inside the `4 * λ` hat radius. -/
theorem stepCBump_out_lt (lam : Real) (hlam : 0 < lam) :
    Real.sqrt (stepCBump lam hlam).rOut < 4 * lam := by
  rw [stepCBump_sqrt lam hlam]
  linarith

/-! ## One intrinsic atom -/

/-- The intrinsic Step-C atom centered at `p`. -/
noncomputable def stepCAtom
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (p : Y.M)
    (lam : Real) (hlam : 0 < lam) : Y.M → Real :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  quadNormal Y.metric p (stepCBump lam hlam)

/-- A concrete Step-C atom takes values in `[0, 1]`. -/
theorem stepCAtom_Icc
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (p : Y.M)
    (lam : Real) (hlam : 0 < lam) (q : Y.M) :
    stepCAtom Y p lam hlam q ∈ Set.Icc (0 : Real) 1 := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact quadNormal_mem_Icc Y.metric p (stepCBump lam hlam) q

/-- A concrete Step-C atom is nonnegative. -/
theorem stepCAtom_nonneg
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (p : Y.M)
    (lam : Real) (hlam : 0 < lam) (q : Y.M) :
    0 ≤ stepCAtom Y p lam hlam q :=
  (stepCAtom_Icc Y p lam hlam q).1

/-- A nonzero Step-C atom lies in the four-lambda metric ball around its
center, provided that ball stays inside the intrinsic normal radius. -/
theorem stepCAtom_mem_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {p q : Y.M}
    (lam : Real) (hlam : 0 < lam)
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      4 * lam < expRadiusGp (I := I) Y.metric p)
    (hq : stepCAtom Y p lam hlam q ≠ 0) :
    letI : MetricSpace Y.M := P.ms
    q ∈ Metric.ball p (4 * lam) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := P.ms
  have hsupp : q ∈ Function.support
      (quadNormal Y.metric p (stepCBump lam hlam)) := by
    rw [Function.mem_support]
    simpa only [stepCAtom] using hq
  obtain ⟨v, hv, hqv⟩ := quadNormal_tsupport Y.metric p
    (stepCBump lam hlam) ((stepCBump_out_lt lam hlam).trans hR)
    (subset_tsupport _ hsupp)
  have hsqrt_lt : Real.sqrt (Y.metric.inner p v v) < 4 * lam :=
    (Real.sqrt_le_sqrt hv).trans_lt (stepCBump_out_lt lam hlam)
  have hsmall : Real.sqrt (Y.metric.inner p v v) <
      expRadiusGp (I := I) Y.metric p := hsqrt_lt.trans hR
  have hvnorm : ‖v‖ < expMapC2Radius (I := I) Y.metric p :=
    norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Y.metric p hsmall
  have hvtgt : v ∈ (normalChartAt (I := I) Y.metric p).target :=
    ball_subset_normalChartAt_target (I := I) Y.metric p hvnorm
  have hsymm : (normalChartAt (I := I) Y.metric p).symm v =
      expMap (I := I) Y.metric p (show TangentSpace I p from v) :=
    normalChartAt_symm_apply (I := I) Y.metric p hvtgt
  have hqexp : q =
      expMap (I := I) Y.metric p (show TangentSpace I p from v) :=
    hqv.symm.trans hsymm
  have hdist_eq : dist p q = Real.sqrt (Y.metric.inner p v v) := by
    rw [hqexp]
    exact properExpDist (I := I) Y P p hsmall
  rw [Metric.mem_ball, dist_comm, hdist_eq]
  exact hsqrt_lt

/-- Inside a four-lambda intrinsic normal radius, a Step-C atom is exactly the
fixed scalar bump of the squared realized distance from its center. -/
theorem stepCAtom_eq_dist
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {p q : Y.M}
    (lam : Real) (hlam : 0 < lam)
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      4 * lam < expRadiusGp (I := I) Y.metric p) :
    letI : MetricSpace Y.M := P.ms
    stepCAtom Y p lam hlam q =
      stepCBump lam hlam ((dist p q) ^ 2) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := P.ms
  have hlocal (hdist : dist p q < 4 * lam) :
      stepCAtom Y p lam hlam q =
        stepCBump lam hlam ((dist p q) ^ 2) := by
    obtain ⟨v, hvtgt, _hvdom, hvlen, hqexp⟩ :=
      properBallNormal (I := I) Y P hR (by
        rw [Metric.mem_ball, dist_comm]
        exact hdist)
    let ψ := normalChartAt (I := I) Y.metric p
    have hsymm : ψ.symm v =
        expMap (I := I) Y.metric p (show TangentSpace I p from v) := by
      simpa only [ψ] using
        normalChartAt_symm_apply (I := I) Y.metric p hvtgt
    have hqSymm : q = ψ.symm v := hqexp.trans hsymm.symm
    have hqsrc : q ∈ ψ.source := by
      rw [hqSymm]
      exact ψ.symm.map_source hvtgt
    have hchart : ψ q = v := by
      rw [hqSymm]
      exact ψ.toPartialEquiv.right_inv hvtgt
    have hquad_nonneg : 0 ≤ Y.metric.inner p v v := by
      exact (mul_nonneg
        (gpCoerciveConst_pos (I := I) Y.metric p).le
        (sq_nonneg ‖v‖)).trans
          (gpCoerciveConst_le (I := I) Y.metric p v)
    rw [stepCAtom, quadNormal_of_mem Y.metric p
      (stepCBump lam hlam) (by simpa only [ψ] using hqsrc)]
    rw [show normalChartAt (I := I) Y.metric p q = v by
      simpa only [ψ] using hchart]
    congr 1
    calc
      Y.metric.inner p v v =
          (Real.sqrt (Y.metric.inner p v v)) ^ 2 :=
        (Real.sq_sqrt hquad_nonneg).symm
      _ = (dist p q) ^ 2 := by rw [hvlen]
  by_cases hq : stepCAtom Y p lam hlam q = 0
  · by_cases hb : stepCBump lam hlam ((dist p q) ^ 2) = 0
    · exact hq.trans hb.symm
    · have hsupp : (dist p q) ^ 2 ∈
          Function.support (stepCBump lam hlam) := by
        simpa only [Function.mem_support] using hb
      rw [(stepCBump lam hlam).support_eq, Metric.mem_ball,
        dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (dist p q)), stepCBump_rOut] at hsupp
      have hdist : dist p q < 4 * lam := by
        have hdist0 : 0 ≤ dist p q := dist_nonneg
        nlinarith
      exact False.elim (hb ((hlocal hdist).symm.trans hq))
  · have hmem := stepCAtom_mem_ball (I := I) Y P lam hlam hR hq
    have hdist : dist p q < 4 * lam := by
      simpa only [Metric.mem_ball, dist_comm] using hmem
    exact hlocal hdist

/-! ## Ordered-net atom families -/

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

/-- The Step-C atom in one sequence member.  A dead ordered-net slot gives the
zero function; a live slot is the fixed scalar bump of squared intrinsic
distance from its center.  Normal-coordinate hypotheses are needed only to
prove smoothness, not to define the atom. -/
noncomputable def seqAtom (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) : (X.obj (L.φ k)).M → Real :=
  match seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none => 0
  | some c => by
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      exact fun q =>
        stepCBump (L.lamInf (gamma : Nat))
          (hd.lambda_pos hD (L.rInf (gamma : Nat))) ((dist c q) ^ 2)

/-- Refining the net-limit data only reindexes the stage of each Step-C atom. -/
@[simp] theorem seqAtom_subseq (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) (k : Nat) (gamma : Fin (pb.A r)) :
    seqAtom hd hD P (L.subseq hψ) pb r k gamma =
      seqAtom hd hD P L pb r (ψ k) gamma := by
  funext y
  unfold seqAtom
  simp only [NetLimitData.subseq_phi, NetLimitData.subseq_lamInf,
    Function.comp_apply]
  cases hcenter : seqCenter hd D P (L.φ (ψ k)) (gamma : Nat) with
  | none => rfl
  | some c => congr 2

@[simp] theorem seqAtom_none (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r))
    (hc : seqCenter hd D P (L.φ k) (gamma : Nat) = none) :
    seqAtom hd hD P L pb r k gamma = 0 := by
  simp [seqAtom, hc]

theorem seqAtom_some (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) {c : (X.obj (L.φ k)).M}
    (hc : seqCenter hd D P (L.φ k) (gamma : Nat) = some c) :
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    seqAtom hd hD P L pb r k gamma = fun q =>
      stepCBump (L.lamInf (gamma : Nat))
        (hd.lambda_pos hD (L.rInf (gamma : Nat))) ((dist c q) ^ 2) := by
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  simp [seqAtom, hc]

/-- Every ordered-net atom is globally smooth when the fixed hat scale stays
inside the intrinsic normal radius.  A dead slot is the zero function; a live
slot is the globally smooth quadratic normal bump. -/
theorem seqAtom_contMDiff (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r k) (gamma : Fin (pb.A r)) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    ContMDiff I (modelWithCornersSelf Real Real) ∞
      (seqAtom hd hD P L pb r k gamma) := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  cases hc : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none =>
      rw [seqAtom_none hd hD P L pb r k gamma hc]
      exact contMDiff_const
  | some c =>
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      let lam := L.lamInf (gamma : Nat)
      let hlam := hd.lambda_pos hD (L.rInf (gamma : Nat))
      have hR : 4 * lam <
          expRadiusGp (I := I) (X.obj (L.φ k)).metric c := by
        simpa only [lam] using hgp gamma c hc
      have heq :
          (fun q => stepCBump lam hlam ((dist c q) ^ 2)) =
            stepCAtom (X.obj (L.φ k)) c lam hlam := by
        funext q
        exact (stepCAtom_eq_dist (I := I)
          (X.obj (L.φ k)) (P (L.φ k)) lam hlam hR).symm
      rw [seqAtom_some hd hD P L pb r k gamma hc]
      rw [heq]
      simpa only [stepCAtom] using
        quadNormal_contMDiff (X.obj (L.φ k)).metric c
          (stepCBump lam hlam) ((stepCBump_out_lt lam hlam).trans hR)

/-- Every sequence atom takes values in `[0, 1]`. -/
theorem seqAtom_Icc (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) (q : (X.obj (L.φ k)).M) :
    seqAtom hd hD P L pb r k gamma q ∈ Set.Icc (0 : Real) 1 := by
  cases hc : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none => simp [seqAtom, hc]
  | some c =>
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      rw [seqAtom_some hd hD P L pb r k gamma hc]
      exact ⟨(stepCBump _ _).nonneg, (stepCBump _ _).le_one⟩

/-- Every sequence atom is nonnegative. -/
theorem seqAtom_nonneg (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) (q : (X.obj (L.φ k)).M) :
    0 ≤ seqAtom hd hD P L pb r k gamma q :=
  (seqAtom_Icc hd hD P L pb r k gamma q).1

/-- A live distance atom equals one on its associated strict inner ball,
without any normal-chart radius hypothesis. -/
theorem seqAtom_one_raw (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) {q : (X.obj (L.φ k)).M}
    (hq : q ∈ L.innerBall hd D P pb r k gamma) :
    seqAtom hd hD P L pb r k gamma q = 1 := by
  cases hc : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none =>
      simp [NetLimitData.innerBall, hc] at hq
  | some c =>
      let lam := L.lamInf (gamma : Nat)
      have hlam : 0 < lam := hd.lambda_pos hD (L.rInf (gamma : Nat))
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      have hdist_lt : dist c q < 3 * lam := by
        simpa only [NetLimitData.innerBall, hc, Metric.mem_ball, dist_comm] using hq
      rw [seqAtom_some hd hD P L pb r k gamma hc]
      apply (stepCBump lam hlam).one_of_mem_closedBall
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (dist c q)), stepCBump_rIn]
      exact (sq_le_sq₀ dist_nonneg (by positivity)).2 hdist_lt.le

/-- Compatibility form of `seqAtom_one_raw` retaining the legacy normal-radius
argument. -/
theorem seqAtom_one (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (_hgp : Item3GpScaleAt (I := I) hd D P L pb r k)
    (gamma : Fin (pb.A r)) {q : (X.obj (L.φ k)).M}
    (hq : q ∈ L.innerBall hd D P pb r k gamma) :
    seqAtom hd hD P L pb r k gamma q = 1 :=
  seqAtom_one_raw hd hD P L pb r k gamma hq

/-- A nonzero distance atom can occur only in its associated `4 * λ` hat,
without any normal-chart radius hypothesis. -/
theorem seqAtom_mem_hat_raw (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) {q : (X.obj (L.φ k)).M}
    (hq : seqAtom hd hD P L pb r k gamma q ≠ 0) :
    q ∈ L.hatBall hd D P pb r k gamma := by
  cases hc : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none =>
      exact False.elim (hq (by simp [seqAtom, hc]))
  | some c =>
      let lam := L.lamInf (gamma : Nat)
      have hlam : 0 < lam := hd.lambda_pos hD (L.rInf (gamma : Nat))
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      have hsupp : (dist c q) ^ 2 ∈
          Function.support (stepCBump lam hlam) := by
        rw [Function.mem_support]
        simpa [seqAtom, hc, lam] using hq
      rw [(stepCBump lam hlam).support_eq, Metric.mem_ball,
        dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (dist c q)),
        stepCBump_rOut] at hsupp
      simp only [NetLimitData.hatBall, hc, Metric.mem_ball]
      rw [dist_comm]
      have hdist0 : 0 ≤ dist c q := dist_nonneg
      nlinarith

/-- Compatibility form of `seqAtom_mem_hat_raw` retaining the legacy
normal-radius argument. -/
theorem seqAtom_mem_hat (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (_hgp : Item3GpScaleAt (I := I) hd D P L pb r k)
    (gamma : Fin (pb.A r)) {q : (X.obj (L.φ k)).M}
    (hq : seqAtom hd hD P L pb r k gamma q ≠ 0) :
    q ∈ L.hatBall hd D P pb r k gamma :=
  seqAtom_mem_hat_raw hd hD P L pb r k gamma hq

/-! ## Pointwise normalized data -/

/-- A strict-inner-ball cover produces the exact pointwise weight package
directly from the distance atoms, without a normal-chart radius hypothesis. -/
theorem seqWeights_data_raw (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (i0 : Fin (pb.A r))
    {s : Set (X.obj (L.φ k)).M}
    (hcover : s ⊆ ⋃ gamma : Fin (pb.A r), L.innerBall hd D P pb r k gamma) :
    centerAverage.WeightDataOn s
      (fun gamma : Fin (pb.A r) => L.hatBall hd D P pb r k gamma)
      (rawWeights
        (cutRaw (seqAtom hd hD P L pb r k i0)
          (seqAtom hd hD P L pb r k) i0)) := by
  apply cutWeights_data
  · intro x _hx
    exact seqAtom_Icc hd hD P L pb r k i0 x
  · intro x _hx gamma
    exact seqAtom_nonneg hd hD P L pb r k gamma x
  · intro x hx
    obtain ⟨gamma, hgamma⟩ := Set.mem_iUnion.mp (hcover hx)
    refine ⟨gamma, ?_⟩
    rw [seqAtom_one_raw hd hD P L pb r k gamma hgamma]
    exact zero_lt_one
  · intro x _hx hne
    exact lt_of_le_of_ne (seqAtom_nonneg hd hD P L pb r k i0 x) (Ne.symm hne)
  · intro x _hx gamma hne
    exact seqAtom_mem_hat_raw hd hD P L pb r k gamma hne

/-- A strict-inner-ball cover produces the exact pointwise weight package used
by the Step-C average.  The explicitly chosen slot `i0` supplies the base kill
factor; active normalized weights remain subordinate to the `4 * λ` hats. -/
theorem seqWeights_data (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (_hgp : Item3GpScaleAt (I := I) hd D P L pb r k) (i0 : Fin (pb.A r))
    {s : Set (X.obj (L.φ k)).M}
    (hcover : s ⊆ ⋃ gamma : Fin (pb.A r), L.innerBall hd D P pb r k gamma) :
    centerAverage.WeightDataOn s
      (fun gamma : Fin (pb.A r) => L.hatBall hd D P pb r k gamma)
      (rawWeights
        (cutRaw (seqAtom hd hD P L pb r k i0)
          (seqAtom hd hD P L pb r k) i0)) := by
  exact seqWeights_data_raw hd hD P L pb r k i0 hcover

/-- For every fixed source radius, the intrinsic Step-C atoms eventually give
the normalized weight package on the full frozen source ball. -/
theorem seqWeights_ev (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    (r : Real) (hgp : Item3GpScaleTail (I := I) hd D P L pb r)
    (i0 : Fin (pb.A r)) :
    ∀ᶠ k in Filter.atTop,
      centerAverage.WeightDataOn (L.hatSourceBall hd P r k)
        (fun gamma : Fin (pb.A r) => L.hatBall hd D P pb r k gamma)
        (rawWeights
          (cutRaw (seqAtom hd hD P L pb r k i0)
            (seqAtom hd hD P L pb r k) i0)) := by
  filter_upwards [L.innerBall_cover hd hD P hre pb r, hgp] with k hcover hgpAt
  exact seqWeights_data hd hD P L pb r k hgpAt i0 hcover

private theorem packA_pos (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hre : hd.RealizesEdist) (pb : hd.PackingBound D) {r : Real} (hr : 0 ≤ r) :
    0 < pb.A r := by
  let O := (X.obj 0).basepoint
  have hself : hd.dist 0 O O = 0 := by
    have hz : ENNReal.ofReal (hd.dist 0 O O) = 0 := by
      letI : EMetricSpace (X.obj 0).M := (X.obj 0).emetricSpace
      rw [← hre.edist_eq 0 O O, edist_self]
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hz) (hre.dist_nonneg 0 O O)
  have hcard := pb.card_le 0 r ({O} : Finset (X.obj 0).M) (by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst x
    change hd.dist 0 O O ≤ r
    simpa only [hself] using hr) (by
      intro x hx y hy hxy
      rw [Finset.mem_singleton] at hx hy
      exact False.elim (hxy (hx.trans hy.symm)))
  simpa only [Finset.card_singleton, Nat.succ_le_iff] using hcard

/-- The canonical Step-C base slot.  Nonnegative source radii force the packing
bound to contain slot zero because the basepoint singleton must be counted. -/
noncomputable def baseIndex (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hre : hd.RealizesEdist) (pb : hd.PackingBound D) {r : Real} (hr : 0 ≤ r) :
    Fin (pb.A r) :=
  ⟨0, packA_pos hd hre pb hr⟩

@[simp] theorem baseIndex_val (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hre : hd.RealizesEdist) (pb : hd.PackingBound D) {r : Real} (hr : 0 ≤ r) :
    (baseIndex hd hre pb hr : Nat) = 0 := rfl

/-- The zeroth distance atom is one at the pointed basepoint without a
normal-radius premise. -/
theorem seqAtom_base_raw (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    {r : Real} (hr : 0 ≤ r) (k : Nat) :
    seqAtom hd hD P L pb r k (baseIndex hd hre pb hr)
        (X.obj (L.φ k)).basepoint = 1 := by
  apply seqAtom_one_raw hd hD P L pb r k
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  simp only [NetLimitData.innerBall, baseIndex_val, seqCenter_zero, Metric.mem_ball,
    dist_self]
  exact mul_pos (by norm_num) (hd.lambda_pos hD (L.rInf 0))

/-- Compatibility form of `seqAtom_base_raw` retaining the legacy radius
premise. -/
theorem seqAtom_base (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    {r : Real} (hr : 0 ≤ r) (k : Nat)
    (_hgp : Item3GpScaleAt (I := I) hd D P L pb r k) :
    seqAtom hd hD P L pb r k (baseIndex hd hre pb hr)
        (X.obj (L.φ k)).basepoint = 1 :=
  seqAtom_base_raw hd hD P L hre pb hr k

/-- At the pointed basepoint the canonical cut-and-normalize construction is
the Kronecker delta at slot zero, without a normal-radius premise. -/
theorem seqWeights_base_raw (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    {r : Real} (hr : 0 ≤ r) (k : Nat) :
    let i0 := baseIndex hd hre pb hr
    let num := cutRaw (seqAtom hd hD P L pb r k i0)
      (seqAtom hd hD P L pb r k) i0
    rawWeights num (X.obj (L.φ k)).basepoint i0 = 1 ∧
      ∀ j, j ≠ i0 → rawWeights num (X.obj (L.φ k)).basepoint j = 0 := by
  dsimp only
  have hbase := seqAtom_base_raw hd hD P L hre pb hr k
  have hdelta := cutRaw_delta
    (cut := seqAtom hd hD P L pb r k (baseIndex hd hre pb hr))
    (a := seqAtom hd hD P L pb r k) (i0 := baseIndex hd hre pb hr)
    (x := (X.obj (L.φ k)).basepoint) hbase
  apply rawWeights_delta (baseIndex hd hre pb hr) hdelta.2
  rw [hdelta.1, hbase]
  exact one_ne_zero

/-- Compatibility form of `seqWeights_base_raw` retaining the legacy radius
premise. -/
theorem seqWeights_base (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    {r : Real} (hr : 0 ≤ r) (k : Nat)
    (_hgp : Item3GpScaleAt (I := I) hd D P L pb r k) :
    let i0 := baseIndex hd hre pb hr
    let num := cutRaw (seqAtom hd hD P L pb r k i0)
      (seqAtom hd hD P L pb r k) i0
    rawWeights num (X.obj (L.φ k)).basepoint i0 = 1 ∧
      ∀ j, j ≠ i0 → rawWeights num (X.obj (L.φ k)).basepoint j = 0 :=
  seqWeights_base_raw hd hD P L hre pb hr k

/-- The eventual source-ball package specialized to the canonical zeroth base
slot. -/
theorem seqWeights_zero_ev (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    {r : Real} (hr : 0 ≤ r) (hgp : Item3GpScaleTail (I := I) hd D P L pb r) :
    ∀ᶠ k in Filter.atTop,
      centerAverage.WeightDataOn (L.hatSourceBall hd P r k)
        (fun gamma : Fin (pb.A r) => L.hatBall hd D P pb r k gamma)
        (rawWeights
          (cutRaw (seqAtom hd hD P L pb r k (baseIndex hd hre pb hr))
            (seqAtom hd hD P L pb r k) (baseIndex hd hre pb hr))) :=
  seqWeights_ev hd hD P L hre pb r hgp (baseIndex hd hre pb hr)

end HCGCompactness
end DifferentialGeometry
