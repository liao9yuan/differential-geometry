import DifferentialGeometry.Geometry.Coordinates.LocalDiffeoOpen
import DifferentialGeometry.Geometry.Curvature.PullbackNaturalityLocalCross
import DifferentialGeometry.Geometry.Curvature.Rm04OperatorBound
import DifferentialGeometry.Geometry.Exponential.FramedNormalCoordinates
import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback
import DifferentialGeometry.Geometry.Metric.LocalPullback
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

/-- The open model-space ball carrying the raw framed-exponential pullback. -/
def rawPullBall (R : Real) : Opens E :=
  ⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩

/-- The raw framed exponential restricted to a centered model-space ball. -/
noncomputable def rawExpOn
    (g : SmoothRiemannianMetric I M) (p : M) (R : Real) :
    rawPullBall (E := E) R → M :=
  fun z => framedExpMap (I := I) g p z

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
/-- A raw framed exponential locally diffeomorphic on a ball remains locally
diffeomorphic after restriction to that ball. -/
theorem rawExpOn_local
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real}
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R)) :
    IsLocalDiffeomorph 𝓘(Real, E) I ∞
      (rawExpOn (I := I) g p R) := by
  exact hloc_restrict_open (rawPullBall (E := E) R) hloc

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
/-- The derivative of the restricted raw framed exponential is the derivative
of the ambient raw framed exponential. -/
theorem rawExpOn_mfderiv
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real}
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (z : rawPullBall (E := E) R) (v : E) :
    mfderiv 𝓘(Real, E) I (rawExpOn (I := I) g p R) z v =
      mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) (z : E) v := by
  have hF : MDifferentiableAt 𝓘(Real, E) I
      (framedExpMap (I := I) g p) (z : E) :=
    (hloc ⟨z, z.property⟩).mdifferentiableAt (by decide)
  have hval : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, E)
      (Subtype.val : rawPullBall (E := E) R → E) z :=
    ((contMDiff_subtype_val (I := 𝓘(Real, E))).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  change mfderiv 𝓘(Real, E) I
      ((framedExpMap (I := I) g p) ∘
        (Subtype.val : rawPullBall (E := E) R → E)) z v = _
  rw [mfderiv_comp_apply z hF hval v, mfderiv_subtype_val_apply]

/-- The Riemannian metric on a model-space ball pulled back through the raw
framed exponential. -/
noncomputable def rawPullMetric
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real}
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R)) :
    SmoothRiemannianMetric 𝓘(Real, E) (rawPullBall (E := E) R) := by
  letI : SigmaCompactSpace (rawPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (rawPullBall (E := E) R).isOpen)
  exact localPullMetric (I := 𝓘(Real, E)) (J := I) g
    (rawExpOn (I := I) g p R)
    (rawExpOn_local (I := I) g p hloc)

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
/-- Evaluation of the raw framed-exponential pullback metric. -/
theorem rawPullMetric_inner
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real}
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (z : rawPullBall (E := E) R) (v w : E) :
    (rawPullMetric (I := I) g p hloc).inner z v w =
      g.inner (framedExpMap (I := I) g p (z : E))
        (mfderiv 𝓘(Real, E) I
          (framedExpMap (I := I) g p) (z : E) v)
        (mfderiv 𝓘(Real, E) I
          (framedExpMap (I := I) g p) (z : E) w) := by
  letI : SigmaCompactSpace (rawPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (rawPullBall (E := E) R).isOpen)
  rw [rawPullMetric, localPullMetric_inner,
    rawExpOn_mfderiv (I := I) g p hloc,
    rawExpOn_mfderiv (I := I) g p hloc]
  rfl

section

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
/-- Restriction of the raw framed exponential preserves path length when its
source ball carries the pullback metric. -/
theorem rawPull_pathLen
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real}
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    {γ : Real → rawPullBall (E := E) R} {a b : Real}
    (hγ : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ (Set.Icc a b)) :
    letI : SigmaCompactSpace (rawPullBall (E := E) R) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen
          𝓘(Real, E) (rawPullBall (E := E) R).isOpen)
    letI : RiemannianBundle
        (fun y : rawPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) y) :=
      ⟨(rawPullMetric (I := I) g p hloc).toRiemannianMetric⟩
    Manifold.pathELength I
        (rawExpOn (I := I) g p R ∘ γ) a b =
      Manifold.pathELength 𝓘(Real, E) γ a b := by
  letI : SigmaCompactSpace (rawPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (rawPullBall (E := E) R).isOpen)
  simpa only [rawPullMetric] using
    (localPull_pathLen (I := 𝓘(Real, E)) (J := I) g hEnorm
      (rawExpOn (I := I) g p R)
      (rawExpOn_local (I := I) g p hloc) hγ)

end

section Curvature

/-- Curvature of the raw framed-exponential pullback metric is the ambient
curvature evaluated on the framed-exponential derivatives. -/
theorem rawPull_rm04
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real}
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (z : rawPullBall (E := E) R) (X Y Z W : E) :
    letI : SigmaCompactSpace (rawPullBall (E := E) R) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen
          𝓘(Real, E) (rawPullBall (E := E) R).isOpen)
    Geometry.Curvature.metricRm04StdAt
        (I := 𝓘(Real, E)) (M := rawPullBall (E := E) R)
        (rawPullMetric (I := I) g p hloc) z X Y Z W =
      Geometry.Curvature.metricRm04StdAt (I := I) (M := M) g
        (framedExpMap (I := I) g p (z : E))
        (mfderiv 𝓘(Real, E) I
          (framedExpMap (I := I) g p) (z : E) X)
        (mfderiv 𝓘(Real, E) I
          (framedExpMap (I := I) g p) (z : E) Y)
        (mfderiv 𝓘(Real, E) I
          (framedExpMap (I := I) g p) (z : E) Z)
        (mfderiv 𝓘(Real, E) I
          (framedExpMap (I := I) g p) (z : E) W) := by
  letI : T2Space M := gauss_t2Space_base I
  letI : SigmaCompactSpace (rawPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (rawPullBall (E := E) R).isOpen)
  rw [rawPullMetric, Integral.Connection.rm04_localPull,
    rawExpOn_mfderiv (I := I) g p hloc,
    rawExpOn_mfderiv (I := I) g p hloc,
    rawExpOn_mfderiv (I := I) g p hloc,
    rawExpOn_mfderiv (I := I) g p hloc]
  rfl

/-- An ambient raw curvature-norm bound controls the pullback curvature
quadratic form at the corresponding model point. -/
theorem rawPull_quad_le
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real}
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (z : rawPullBall (E := E) R) {K : Real}
    (hRm :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (framedExpMap (I := I) g p (z : E)) 4
        (Geometry.Curvature.metricRm04At
          (I := I) (M := M) g
          (framedExpMap (I := I) g p (z : E)))) ≤ K)
    (J V : E) :
    letI : SigmaCompactSpace (rawPullBall (E := E) R) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen
          𝓘(Real, E) (rawPullBall (E := E) R).isOpen)
    let gPull := rawPullMetric (I := I) g p hloc
    gPull.inner z
        (Geometry.Curvature.riemannOp
          (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gPull)
          z J V V)
        J ≤
      K * gPull.inner z J J * gPull.inner z V V := by
  letI : T2Space M := gauss_t2Space_base I
  letI : SigmaCompactSpace (rawPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (rawPullBall (E := E) R).isOpen)
  let gPull := rawPullMetric (I := I) g p hloc
  let F : E → M := framedExpMap (I := I) g p
  let q : M := F (z : E)
  let dJ : TangentSpace I q :=
    mfderiv 𝓘(Real, E) I F (z : E) J
  let dV : TangentSpace I q :=
    mfderiv 𝓘(Real, E) I F (z : E) V
  have hRm' :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
        (Geometry.Curvature.metricRm04At
          (I := I) (M := M) g q)) ≤ K := by
    simpa only [F, q] using hRm
  obtain ⟨basis, hON⟩ :=
    Geometry.Curvature.exists_gOrthonormalBasis (I := I) g q
  have hquad :=
    Integral.Connection.riemann_quad_le (I := I) g basis hON
      hRm' dJ dV
  have hJJ : gPull.inner z J J = g.inner q dJ dJ := by
    simp only [gPull, F, q, dJ]
    rw [rawPullMetric_inner (I := I) g p hloc]
  have hVV : gPull.inner z V V = g.inner q dV dV := by
    simp only [gPull, F, q, dV]
    rw [rawPullMetric_inner (I := I) g p hloc]
  calc
    gPull.inner z
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gPull)
            z J V V)
          J =
        gPull.inner z J
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gPull)
            z J V V) := gPull.symm _ _ _
    _ = Geometry.Curvature.metricRm04StdAt
          (I := 𝓘(Real, E)) (M := rawPullBall (E := E) R)
          gPull z J V V J := by
      rw [Integral.Connection.rm04_eq_inner]
    _ = Geometry.Curvature.metricRm04StdAt
          (I := I) (M := M) g q dJ dV dV dJ := by
      simpa only [gPull, F, q, dJ, dV] using
        rawPull_rm04 (I := I) g p hloc z J V V J
    _ = g.inner q dJ
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := I) g)
            q dJ dV dV) := by
      rw [Integral.Connection.rm04_eq_inner]
    _ = g.inner q
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := I) g)
            q dJ dV dV)
          dJ := g.symm _ _ _
    _ ≤ K * g.inner q dJ dJ * g.inner q dV dV := hquad
    _ = K * gPull.inner z J J * gPull.inner z V V := by
      rw [hJJ, hVV]

end Curvature

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
