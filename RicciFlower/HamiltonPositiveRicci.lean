import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.ProperAction.Basic
import RicciFlower.LeviCivita.Koszul
import RicciFlower.Realized.CurvatureProducers
import RicciFlower.RicciFlow.Basic
import RicciFlower.RicciFlow.Evolution.LocalPinching
import RicciFlower.RicciFlow.Evolution.ScalarFiniteTime
import RicciFlower.DimensionThree.RicciControlsRm

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Hamilton Positive Ricci Endpoint

This file states the global endpoint of Hamilton's three-dimensional positive
Ricci theorem in RicciFlower's current structures.

The policy here is deliberate: local tensor algebra, curvature identities,
evolution equations, maximum-principle cores, and dimension-three algebra stay
in their native RicciFlower files.  The theorem-shaped `sorry`s below are only
for the remaining global analytic or topological inputs in Hamilton's Section
12 completion: maximal-flow existence, point selection and rescaling,
noncollapsing, compactness, limit extraction, and spherical space-form
classification.
-/

noncomputable section

universe u

namespace RicciFlower
namespace HamiltonPositiveRicci

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

/-- Closed, connected, smooth, boundaryless, three-dimensional manifold
package used by the statement of Hamilton's theorem. -/
def Closed3Manifold : Prop :=
  CompactSpace M /\ ConnectedSpace M /\ I.Boundaryless /\
    Module.finrank Real E = 3

/-- Positive definiteness of a supplied symmetric two-tensor section, evaluated
on diagonal tangent vectors. -/
def PosDef02 (A : Curvature.Tensor02Section (I := I) (M := M)) : Prop :=
  forall x : M, forall v : TangentSpace I x, v ≠ 0 ->
    0 < A x (Curvature.vec2 (I := I) v v)

/-- The initial metric has positive Ricci curvature, expressed using the
current curvature-producer structure for the Levi-Civita connection of `g`. -/
def PosRicciMetric (g : SmoothRiemannianMetric I M) : Prop :=
  exists K : Realized.CurvatureSectionProducerData
      (I := I) (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g,
    PosDef02 (I := I) (M := M) K.ricci

/-- `M` admits a smooth Riemannian metric of positive Ricci curvature. -/
def AdmitsPosRicci : Prop :=
  exists g : SmoothRiemannianMetric I M, PosRicciMetric (I := I) (M := M) g

/-- Constant positive sectional curvature, expressed by the standard
two-plane curvature formula against RicciFlower's lowered curvature convention
`Rm04(W,X,Y,Z) = g(W,R(X,Y)Z)`. -/
def ConstPosSecMetric (g : SmoothRiemannianMetric I M) : Prop :=
  exists c : Real, 0 < c /\
    exists K : Realized.CurvatureSectionProducerData
        (I := I) (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) g,
      forall x : M, forall X Y : TangentSpace I x,
        K.rm04 x (Curvature.vec4 (I := I) X X Y Y) =
          c * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)

/-- `M` admits a smooth metric of constant positive sectional curvature. -/
def AdmitsConstPosSec : Prop :=
  exists g : SmoothRiemannianMetric I M, ConstPosSecMetric (I := I) (M := M) g

/-- The standard unit three-sphere in Euclidean four-space. -/
abbrev RoundSphere3 : Type :=
  {x : EuclideanSpace Real (Fin 4) // ‖x‖ = (1 : Real)}

/-- Orbit quotient of the round three-sphere by a group action. -/
abbrev SphereOrbitQuotient (Γ : Type*) [Group Γ] [MulAction Γ RoundSphere3] :
    Type :=
  Quotient (MulAction.orbitRel Γ RoundSphere3)

/-- The topology-side target: `M` is diffeomorphic to a spherical space form.

This is still a theorem-facing interface, but it now records the mathematical
object rather than a bare proposition: a finite group acting freely by
isometries on the round three-sphere, the orbit quotient, a chosen smooth
manifold structure on that quotient, and a smooth homeomorphism from `M` to
the quotient. -/
structure SpaceFormModel
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] : Type _ where
  Γ : Type
  [group : Group Γ]
  [finiteGroup : Fintype Γ]
  [action : MulAction Γ RoundSphere3]
  action_isometric : forall γ : Γ, Isometry (fun p : RoundSphere3 => γ • p)
  action_free : forall {γ : Γ} {p : RoundSphere3}, γ • p = p -> γ = 1
  [quotientCharted : ChartedSpace H (SphereOrbitQuotient Γ)]
  [quotientSmooth : IsManifold I ∞ (SphereOrbitQuotient Γ)]
  diffeo : M ≃ₜ SphereOrbitQuotient Γ
  smooth_toFun : ContMDiff I I ∞ diffeo
  smooth_invFun : ContMDiff I I ∞ diffeo.symm

/-- `M` is diffeomorphic to a spherical space form. -/
def SphericalSpaceForm : Prop :=
  Nonempty (SpaceFormModel I M)

/-- Current RicciFlower-structured global output of Hamilton's flow argument.

This is the black-box boundary rewritten in current structures: it contains a
folder-level Ricci-flow solution `SolutionOn`, its solution predicate
`IsSolutionOn`, and the initial metric relation.  Finite-time singularity,
point selection, noncollapsing, compactness, and the limiting
constant-curvature metric are theorem endpoints below, not fields in this data
package. -/
structure Ham3FlowPackage (g0 : SmoothRiemannianMetric I M) where
  D : Realized.RealTimeInterval
  S : RicciFlower.RicciFlow.SolutionOn (I := I) (M := M) D
  isSolution : RicciFlower.RicciFlow.IsSolutionOn (I := I) S
  startsAt : S.family.metric D.initial = g0

/-- Meaningful finite-time conclusion for Hamilton's maximal flow package.

The theorem statements in the scalar maximum-principle layer are normalized to
`[0, omega)`.  The interval-aware global package may later need a time-shift
adapter; this predicate records the current normalized Section 11.1 output. -/
def Ham3Finite
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0) : Prop :=
  exists omega c0 : Real, exists h0ω : 0 < omega,
    P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω /\
      0 < c0 /\ omega <= 3 / (2 * c0)

/-! ## Section 12 blow-up and compactness data -/

/-- Data carried by Hamilton's blow-up sequence in Section 12.

The predicates below state the mathematical properties of these functions; the
structure itself is data-only. -/
structure Ham3BlowupData (M : Type*) where
  point : Nat -> M
  time : Nat -> Real
  scale : Nat -> Real
  scalar : Nat -> Real -> M -> Real
  ricMin : Nat -> Real -> M -> Real
  rmNorm : Nat -> Real -> M -> Real
  ballVolume : Nat -> Real -> Real

/-- Point-selection and parabolic-rescaling normalization:
`R_i -> infinity`, `R_i t_i -> infinity`,
`R(g^{R_i})(x_i,0) = 1`, and scalar curvature is bounded above by `1`
on the rescaled backward time slab. -/
def Ham3PointSel (Q : Ham3BlowupData M) : Prop :=
  (forall i : Nat, 0 < Q.scale i) /\
    (forall i : Nat, 0 < Q.time i) /\
    (forall A : Real, exists N : Nat,
      forall i : Nat, N <= i -> A <= Q.scale i * Q.time i) /\
    (forall i : Nat, Q.scalar i 0 (Q.point i) = 1) /\
    (forall (i : Nat) (s : Real) (x : M),
      -(Q.scale i * Q.time i) <= s -> s <= 0 -> Q.scalar i s x <= 1)

/-- Nonnegative Ricci curvature on the rescaled flow slabs, represented by the
least Ricci eigenvalue in the chosen component model. -/
def Ham3RicNonneg (Q : Ham3BlowupData M) : Prop :=
  forall (i : Nat) (s : Real) (x : M),
    -(Q.scale i * Q.time i) <= s -> s <= 0 -> 0 <= Q.ricMin i s x

/-- Eigenvalue/sectional model carried by the rescaled blow-up sequence.

This is the component realization data needed by Corollary 11.4: the scalar is
the trace of three Ricci eigenvalues, `ricMin` is a lower bound for each
eigenvalue, and `rmNorm` is the nonnegative norm whose square is the 3D
sectional norm model. -/
def Ham3EigenModel (Q : Ham3BlowupData M) : Prop :=
  forall (i : Nat) (s : Real) (x : M),
    -(Q.scale i * Q.time i) <= s -> s <= 0 ->
      exists l1 l2 l3 : Real,
        Q.scalar i s x =
          DimensionThree.ricciEigenScalar3 l1 l2 l3 /\
        Q.ricMin i s x <= l1 /\
        Q.ricMin i s x <= l2 /\
        Q.ricMin i s x <= l3 /\
        0 <= Q.rmNorm i s x /\
        (Q.rmNorm i s x) ^ 2 =
          DimensionThree.rmSecNormSq3
            (DimensionThree.sec12Ric3 l1 l2 l3)
            (DimensionThree.sec13Ric3 l1 l2 l3)
            (DimensionThree.sec23Ric3 l1 l2 l3)

/-- Coarse curvature bound on the rescaled flow slabs. -/
def Ham3RmBound (Q : Ham3BlowupData M) (C : Real) : Prop :=
  forall (i : Nat) (s : Real) (x : M),
    -(Q.scale i * Q.time i) <= s -> s <= 0 -> Q.rmNorm i s x <= C

/-- The fixed radius used in Hamilton's Section 12 proof. -/
def ham3_r0 : Real := (1 : Real) / 10

theorem ham3_r0_pos : 0 < ham3_r0 := by
  norm_num [ham3_r0]

/-- The coarse constant `100` is the inverse-square scale of `r0 = 1/10`. -/
theorem ham3_hundred_eq : (100 : Real) = (ham3_r0⁻¹) ^ 2 := by
  norm_num [ham3_r0]

/-- Eventually the fixed backward time window `[-r0^2,0]` lies inside the
rescaled time slab `[-R_i t_i,0]`. -/
def Ham3Window (Q : Ham3BlowupData M) (r : Real) : Prop :=
  exists N : Nat, forall i : Nat, N <= i ->
    forall s : Real, -(r ^ 2) <= s -> s <= 0 ->
      -(Q.scale i * Q.time i) <= s /\ s <= 0

/-- The lower volume bound supplied by Perelman's noncollapsing theorem at the
fixed radius. -/
def Ham3Noncollapse (Q : Ham3BlowupData M) (kappa r : Real) : Prop :=
  0 < kappa /\ 0 < r /\
    exists N : Nat, forall i : Nat, N <= i ->
      kappa * r ^ 3 <= Q.ballVolume i r

/-- Data for a smooth Cheeger-Gromov-Hamilton limit produced from the rescaled
flows.  The structure is data-only; convergence and curvature conclusions are
theorem endpoints below. -/
structure Ham3LimitData (I : ModelWithCorners Real E H) (M : Type u) where
  N : Type u
  [topology : TopologicalSpace N]
  [charted : ChartedSpace H N]
  [smooth : IsManifold I ∞ N]
  [sigmaCompact : SigmaCompactSpace N]
  [t2 : T2Space N]
  metric : SmoothRiemannianMetric I N

/-- The CGH limit metric has constant positive sectional curvature. -/
def Ham3LimitConst (L : Ham3LimitData (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  ConstPosSecMetric (I := I) (M := L.N) L.metric

/-- Global analytic black box for Hamilton's maximal-flow setup.

This is only the Ricci-flow existence/setup stage: short-time existence,
maximal-time construction, and the verified Ricci-flow equation package. -/
theorem ham3_flow_exists
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0) :
    Nonempty (Ham3FlowPackage (I := I) (M := M) g0) := by
  sorry

/-- Chosen global Ricci-flow package supplied by `ham3_flow_exists`. -/
noncomputable def ham3_flow_box
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0) :
  Ham3FlowPackage (I := I) (M := M) g0 :=
  Classical.choice (ham3_flow_exists (I := I) (M := M) hM g0 hpos)

/-- Section 11/7 producer: extract the scalar package needed by Corollary 7.4
from Hamilton's normalized maximal Ricci-flow package.

This is now the precise remaining frontier behind Lemma 11.1: it must identify
the maximal interval with `[0, omega)`, choose the scalar trace and its
Laplacian/Ricci-norm data, and supply scalar evolution, WMP regularity, the
Laplacian realization, and the three-dimensional Ricci-norm lower bound. -/
theorem ham3_scalar74
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0) :
    exists omega : Real, exists h0ω : 0 < omega,
      P.D = Realized.RealTimeInterval.closedOpen 0 omega h0ω /\
      exists G : Realized.RealizedMetricFamily (I := I) (M := M) Real,
      exists c0 : Real,
      exists scalar scalarLap ricciNormSq : Real -> M -> Real,
      exists K : Real -> NNReal,
        RicciFlow.InitialScalarMinimum (M := M) scalar c0 /\
        (forall x : M, 0 < scalar 0 x) /\
        ContinuousOn
          (fun p : Real × M => scalar p.1 p.2)
          (Realized.spacetimeSlab (M := M)
            (RicciFlow.scalarBlowupTime 3 c0)) /\
        (forall T : Real, 0 < T -> T < omega ->
          T < RicciFlow.scalarBlowupTime 3 c0 ->
            RicciFlow.ScalarLowerBoundWMPRegularity
              (I := I) G T 3 c0 scalar (K T)) /\
        RicciFlow.ScalarEvolutionEquationOn
          (D := Realized.RealTimeInterval.closedOpen 0 omega h0ω)
          scalar scalarLap ricciNormSq /\
        (forall T : Real, 0 < T -> T < omega ->
          T < RicciFlow.scalarBlowupTime 3 c0 ->
            RicciFlow.ScalarLaplacianRealizesHeatOperatorOn
              (I := I) G T scalar scalarLap) /\
        (forall T : Real, 0 < T -> T < omega ->
          T < RicciFlow.scalarBlowupTime 3 c0 ->
            forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
              (1 / 3 : Real) * (scalar t x) ^ 2 <= ricciNormSq t x) /\
        (forall T : Real, 0 < T -> T < omega ->
          T < RicciFlow.scalarBlowupTime 3 c0 ->
            forall t : Real, t ∈ Set.Icc 0 T ->
              LipschitzOnWith (K T)
                (fun a : Real => RicciFlow.scalarLowerReaction 3 a t)
                (Realized.scalarWMPValueSet (M := M) T scalar
                  (RicciFlow.scalarLowerBarrier 3 c0))) := by
  sorry

/-- Lemma 11.1-style input: the maximal Ricci flow reaches a finite singular
time. -/
theorem ham3_finite_time
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0) :
    Ham3Finite (I := I) (M := M) P := by
  have hMcopy := hM
  rcases hM with ⟨hcompact, hconnected, hboundaryless, _hdim⟩
  letI : CompactSpace M := hcompact
  letI : ConnectedSpace M := hconnected
  letI : I.Boundaryless := hboundaryless
  letI : Nonempty M := inferInstance
  rcases ham3_scalar74 (I := I) (M := M) hMcopy g0 hpos P with
    ⟨omega, h0ω, hD, G, c0, scalar, scalarLap, ricciNormSq, K,
      hinit_min, hinit_pos, hscalar_cont, hreg, hevol, hlap, hricci, hF_lip⟩
  have hfinite :
      0 < c0 ∧ omega <= 3 / (2 * c0) :=
    RicciFlow.finiteTime3D (I := I) (M := M) h0ω G c0 scalar scalarLap
      ricciNormSq K hinit_min hinit_pos hscalar_cont hreg hevol hlap
      hricci hF_lip
  exact ⟨omega, c0, h0ω, hD, hfinite.1, hfinite.2⟩

/-- Lemma 11.6-style input: choose blow-up points, times, and parabolic
rescalings normalized by scalar curvature. -/
theorem ham3_point_select
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (_hfinite : Ham3Finite (I := I) (M := M) P) :
    exists Q : Ham3BlowupData M, Ham3PointSel Q /\ Ham3EigenModel Q := by
  sorry

/-- Lemma 9.1-style input: nonnegative Ricci curvature persists on the
rescaled flows. -/
theorem ham3_ric_nonneg
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (_hsel : Ham3PointSel Q) :
    Ham3RicNonneg Q := by
  sorry

/-- Hamilton's pinching improvement along the chosen flow. -/
theorem ham3_pinch_imp
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (_hsel : Ham3PointSel Q)
    (_hric : Ham3RicNonneg Q) :
    exists tracefreeRmNormSq scalar weight : Real -> M -> Real, exists C : Real,
      RicciFlow.HamiltonTracefreePinchingEstimateOn
        tracefreeRmNormSq scalar weight C := by
  sorry

/-- Corollary 11.4-style input: nonnegative Ricci controls the full curvature
tensor, coarsened to the constant `100` used in Section 12. -/
theorem ham3_rm_bound
    (_hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (_hpos : PosRicciMetric (I := I) (M := M) g0)
    (_P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel Q)
    (hric : Ham3RicNonneg Q)
    (heigen : Ham3EigenModel Q) :
    Ham3RmBound Q 100 := by
  rcases hsel with ⟨_hscale, _htime, _hprod, _hbase, hscalarMax⟩
  intro i s x hsleft hsright
  rcases heigen i s x hsleft hsright with
    ⟨l1, l2, l3, hscalar, hmin1, hmin2, hmin3, hrm_nonneg, hrm_sq⟩
  have hric_here : 0 <= Q.ricMin i s x := hric i s x hsleft hsright
  have h1 : 0 <= l1 := le_trans hric_here hmin1
  have h2 : 0 <= l2 := le_trans hric_here hmin2
  have h3 : 0 <= l3 := le_trans hric_here hmin3
  have hmodel :
      (Q.rmNorm i s x) ^ 2 <=
        (100 : Real) ^ 2 * (DimensionThree.ricciEigenScalar3 l1 l2 l3) ^ 2 := by
    simpa [hrm_sq] using
      DimensionThree.rmSqLe100ScalSq3 l1 l2 l3 h1 h2 h3
  have hmodel_scalar :
      (Q.rmNorm i s x) ^ 2 <=
        (100 : Real) ^ 2 * (Q.scalar i s x) ^ 2 := by
    simpa [hscalar] using hmodel
  have hscalar_nonneg : 0 <= Q.scalar i s x := by
    rw [hscalar]
    unfold DimensionThree.ricciEigenScalar3
    nlinarith
  have hscalar_le : Q.scalar i s x <= 1 :=
    hscalarMax i s x hsleft hsright
  have hscalar_sq_le : (Q.scalar i s x) ^ 2 <= (1 : Real) ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hscalar_nonneg] using hscalar_le)
  have hrm_sq_le : (Q.rmNorm i s x) ^ 2 <= (100 : Real) ^ 2 := by
    nlinarith [hmodel_scalar, hscalar_sq_le, sq_nonneg (Q.scalar i s x)]
  have habs : |Q.rmNorm i s x| <= |(100 : Real)| :=
    sq_le_sq.mp hrm_sq_le
  rw [abs_of_nonneg hrm_nonneg] at habs
  norm_num at habs
  exact habs

/-- The fixed window `[-r0^2,0]` eventually lies inside each selected rescaled
time interval.  This is just the arithmetic part of the Section 12 argument. -/
theorem ham3_r0_window
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel Q) :
    Ham3Window Q ham3_r0 := by
  rcases hsel with ⟨_hscale, _htime, hprod, _hbase, _hscalarMax⟩
  rcases hprod (ham3_r0 ^ 2) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i hi s hsleft hsright
  have hprod_i : ham3_r0 ^ 2 <= Q.scale i * Q.time i := hN i hi
  constructor
  · linarith
  · exact hsright

/-- Black box 11.8-style input: Perelman's no-local-collapsing theorem gives a
uniform volume lower bound at the fixed radius `r0`. -/
theorem ham3_noncollapse
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (_hsel : Ham3PointSel Q)
    (_hrm : Ham3RmBound Q 100)
    (_hwindow : Ham3Window Q ham3_r0) :
    exists kappa : Real, Ham3Noncollapse Q kappa ham3_r0 := by
  sorry

/-- Black box 11.12-style input: Hamilton compactness produces a pointed smooth
Cheeger-Gromov-Hamilton limit from curvature control and noncollapsing. -/
theorem ham3_cgh_limit
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (_hsel : Ham3PointSel Q)
    (_hrm : Ham3RmBound Q 100)
    (_hwindow : Ham3Window Q ham3_r0)
    (kappa : Real)
    (_hnoncollapse : Ham3Noncollapse Q kappa ham3_r0) :
    Nonempty (Ham3LimitData (I := I) M) := by
  sorry

/-- Pinching plus smooth CGH convergence gives a constant-positive-sectional
limit metric. -/
theorem ham3_limit_const
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (_hpinch :
      exists tracefreeRmNormSq scalar weight : Real -> M -> Real, exists C : Real,
        RicciFlow.HamiltonTracefreePinchingEstimateOn
          tracefreeRmNormSq scalar weight C)
    (_hlimit : Nonempty (Ham3LimitData (I := I) M)) :
    exists L : Ham3LimitData (I := I) M, Ham3LimitConst (I := I) L := by
  sorry

/-- Transfer the constant-curvature CGH limit back to a smooth metric on the
original closed three-manifold. -/
theorem ham3_limit_pullback
    (hM : Closed3Manifold (I := I) (M := M))
    (g0 : SmoothRiemannianMetric I M)
    (hpos : PosRicciMetric (I := I) (M := M) g0)
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (_hlimitConst :
      exists L : Ham3LimitData (I := I) M, Ham3LimitConst (I := I) L) :
    exists gInf : SmoothRiemannianMetric I M,
      ConstPosSecMetric (I := I) (M := M) gInf := by
  sorry

/-- If a limiting constant-positive-sectional metric has been produced, then
`M` admits such a metric. -/
theorem ham3_const_of_limit
    (hlim : exists gInf : SmoothRiemannianMetric I M,
      ConstPosSecMetric (I := I) (M := M) gInf) :
    AdmitsConstPosSec (I := I) (M := M) := by
  exact hlim

/-- Consumer endpoint: the global Ricci-flow package gives a constant positive
sectional-curvature metric. -/
theorem ham3_const_metric
    (hM : Closed3Manifold (I := I) (M := M))
    (hpos : AdmitsPosRicci (I := I) (M := M)) :
  AdmitsConstPosSec (I := I) (M := M) := by
  rcases hpos with ⟨g0, hg0⟩
  let P := ham3_flow_box (I := I) (M := M) hM g0 hg0
  have hfinite : Ham3Finite (I := I) (M := M) P :=
    ham3_finite_time (I := I) (M := M) hM g0 hg0 P
  rcases ham3_point_select (I := I) (M := M) hM g0 hg0 P hfinite with
    ⟨Q, hsel, heigen⟩
  have hric : Ham3RicNonneg Q :=
    ham3_ric_nonneg (I := I) (M := M) hM g0 hg0 P Q hsel
  have hpinch :
      exists tracefreeRmNormSq scalar weight : Real -> M -> Real, exists C : Real,
        RicciFlow.HamiltonTracefreePinchingEstimateOn
          tracefreeRmNormSq scalar weight C :=
    ham3_pinch_imp (I := I) (M := M) hM g0 hg0 P Q hsel hric
  have hrm : Ham3RmBound Q 100 :=
    ham3_rm_bound (I := I) (M := M) hM g0 hg0 P Q hsel hric heigen
  have hwindow : Ham3Window Q ham3_r0 :=
    ham3_r0_window (M := M) Q hsel
  rcases ham3_noncollapse (I := I) (M := M) hM g0 hg0 P Q hsel hrm hwindow with
    ⟨kappa, hnoncollapse⟩
  have hcgh : Nonempty (Ham3LimitData (I := I) M) :=
    ham3_cgh_limit (I := I) (M := M) hM g0 hg0 P Q hsel hrm hwindow
      kappa hnoncollapse
  have hlimitConst :
      exists L : Ham3LimitData (I := I) M, Ham3LimitConst (I := I) L :=
    ham3_limit_const (I := I) (M := M) hM g0 hg0 P Q hpinch hcgh
  have hlim :
      exists gInf : SmoothRiemannianMetric I M,
        ConstPosSecMetric (I := I) (M := M) gInf :=
    ham3_limit_pullback (I := I) (M := M) hM g0 hg0 P hlimitConst
  exact ham3_const_of_limit (I := I) (M := M) hlim

/-- Topological/global geometry black box: a closed connected smooth
three-manifold with a constant positive sectional-curvature metric is a
spherical space form. -/
theorem ham3_space_box
    (hM : Closed3Manifold (I := I) (M := M))
    (hconst : AdmitsConstPosSec (I := I) (M := M)) :
    SphericalSpaceForm (I := I) (M := M) := by
  sorry

/-- A spherical-space-form model carries a constant positive sectional-curvature
metric.

Mathematically this is the direct construction: take the round metric on
`S^3`, descend it through the finite free isometric quotient, and pull it back
to `M` along the smooth equivalence stored in `SpaceFormModel`. -/
theorem spaceForm_const_metric
    (model : SpaceFormModel I M) :
    AdmitsConstPosSec (I := I) (M := M) := by
  sorry

/-- Reverse presentation direction of the standard equivalence, obtained by
the quotient round metric construction. -/
theorem ham3_const_box
    (hM : Closed3Manifold (I := I) (M := M))
    (hsph : SphericalSpaceForm (I := I) (M := M)) :
    AdmitsConstPosSec (I := I) (M := M) := by
  have _hclosed : Closed3Manifold (I := I) (M := M) := hM
  rcases hsph with ⟨model⟩
  exact spaceForm_const_metric (I := I) (M := M) model

/-- The theorem-facing equivalence between constant positive sectional
curvature and spherical space-form topology. -/
theorem ham3_equiv
    (hM : Closed3Manifold (I := I) (M := M)) :
    AdmitsConstPosSec (I := I) (M := M) <-> SphericalSpaceForm (I := I) (M := M) := by
  constructor
  · exact ham3_space_box (I := I) (M := M) hM
  · exact ham3_const_box (I := I) (M := M) hM

/-- Hamilton's theorem in dimension three, Theorem 2.1 in the Hamilton
blueprint: positive initial Ricci curvature implies existence of a constant
positive sectional-curvature metric, equivalently spherical space-form
topology. -/
theorem ham3_main
    (hM : Closed3Manifold (I := I) (M := M))
    (hpos : AdmitsPosRicci (I := I) (M := M)) :
    AdmitsConstPosSec (I := I) (M := M) /\ SphericalSpaceForm (I := I) (M := M) := by
  have hconst : AdmitsConstPosSec (I := I) (M := M) :=
    ham3_const_metric (I := I) (M := M) hM hpos
  exact ⟨hconst, (ham3_equiv (I := I) (M := M) hM).1 hconst⟩

/-- Label alias for the LaTeX theorem `thm:main-hamilton-3d`. -/
theorem thm_2_1
    (hM : Closed3Manifold (I := I) (M := M))
    (hpos : AdmitsPosRicci (I := I) (M := M)) :
    AdmitsConstPosSec (I := I) (M := M) /\ SphericalSpaceForm (I := I) (M := M) :=
  ham3_main (I := I) (M := M) hM hpos

end HamiltonPositiveRicci
end RicciFlower
