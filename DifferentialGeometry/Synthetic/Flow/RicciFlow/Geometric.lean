import DifferentialGeometry.Synthetic.Flow.RicciFlow.Calculus
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.RicciNorm

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Manifold-Aware Ricci Flow Data

This file adds a geometric wrapper around the existing synthetic
`RicciFlowData`. The local evolution and tensor-calculus files should keep
using `RicciFlowData`; global statements such as blow-up, compactness, point
selection, and the Section 12 assembly should use this wrapper.
-/

open SyntheticTensor

section GeometricRicciFlowData

variable (k R V Time A Manifold Point Metric : Type*)
variable [Field k] [CommRing R] [Algebra k R] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- A manifold-aware Ricci-flow package.

The field `core` is the existing synthetic Ricci-flow object. The remaining
fields record the global realization data needed by singularity, compactness,
point-selection, and final Section 12 statements. The pointwise curvature
fields are intentionally accessors rather than new definitions of curvature:
the synthetic curvature definitions still live in `core`. -/
structure GeometricRicciFlowData where
  core : RicciFlowData k R V Time A
  manifold : Manifold
  pointMem : Point -> Prop
  timeDomain : Time -> Prop
  initialTime : Time
  initial_mem : timeDomain initialTime
  metricAt : Time -> Metric
  metricOn : Manifold -> Metric -> Prop
  metricAt_on : forall t, timeDomain t -> metricOn manifold (metricAt t)
  /-- Evaluation of a synthetic scalar in `R` at a manifold point. For concrete
  realizations, `R` is usually a scalar-function algebra. -/
  evalScalarAt : Point -> R -> R
  /-- Pointwise squared Riemann norm. This remains supplied until the
  synthetic core has a canonical `|Rm|^2` accessor. -/
  riemannNormSqAt : Point -> Time -> R
  /-- Global curvature quantity used by extension/blow-up alternatives. -/
  curvatureQuantityAt : Point -> Time -> R
  /-- Pointwise trace-free Ricci ratio used by the compactness/pinching bridge. -/
  pinchingRatioAt : Point -> Time -> R
  /-- Pointwise improved-pinching quantity before the parabolic rescaling decay
  factor is applied. -/
  pinchingDecayQuantityAt : Point -> Time -> R

namespace GeometricRicciFlowData

variable {k R V Time A Manifold Point Metric : Type*}
variable [Field k] [CommRing R] [Algebra k R] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- The spacetime domain of a geometric flow. -/
def spacetimeDomain
    (G : GeometricRicciFlowData k R V Time A Manifold Point Metric)
    (p : Point) (t : Time) : Prop :=
  G.pointMem p /\ G.timeDomain t

/-- Riemann tensor of the synthetic core at a time. -/
noncomputable def syntheticRiemannTensorAt
    (G : GeometricRicciFlowData k R V Time A Manifold Point Metric)
    (t : Time) : TensorData R V 1 3 :=
  Rm_tensor G.core.emb (G.core.conn_fam t) (G.core.ha_fam t) (G.core.hal_fam t)
    (G.core.hsl_fam t) (G.core.hl_fam t)

/-- Ricci tensor of the synthetic core at a time. -/
noncomputable def syntheticRicciTensorAt
    (G : GeometricRicciFlowData k R V Time A Manifold Point Metric)
    (t : Time) : TensorData R V 0 2 :=
  ricciForm_tensor G.core.emb (G.core.conn_fam t) (G.core.ha_fam t)
    (G.core.hal_fam t) (G.core.hsl_fam t) (G.core.hl_fam t) G.core.atr

/-- Scalar curvature of the synthetic core at a time. -/
noncomputable def syntheticScalarCurvatureAt
    (G : GeometricRicciFlowData k R V Time A Manifold Point Metric)
    (t : Time) : R :=
  ScalarCurvature G.core.emb (G.core.conn_fam t) (G.core.ha_fam t)
    (G.core.hal_fam t) (G.core.hsl_fam t) (G.core.hl_fam t) G.core.atr
    (G.core.g_fam t)

/-- Squared Ricci norm of the synthetic core at a time. -/
noncomputable def syntheticRicciNormSqAt
    (G : GeometricRicciFlowData k R V Time A Manifold Point Metric)
    (t : Time) : R :=
  ricci_norm_sq G.core.emb (G.core.conn_fam t) (G.core.ha_fam t)
    (G.core.hal_fam t) (G.core.hsl_fam t) (G.core.hl_fam t) G.core.atr
    (G.core.g_fam t)

/-- Squared trace-free Ricci norm of the synthetic core at a time. -/
noncomputable def syntheticTracefreeRicciNormSqAt
    (G : GeometricRicciFlowData k R V Time A Manifold Point Metric)
    (nInv : R) (t : Time) : R :=
  tracefree_ricci_norm_sq G.core.emb (G.core.conn_fam t) (G.core.ha_fam t)
    (G.core.hal_fam t) (G.core.hsl_fam t) (G.core.hl_fam t) G.core.atr
    (G.core.g_fam t) nInv

/-- Pointwise scalar curvature. -/
noncomputable def scalarAt
    (G : GeometricRicciFlowData k R V Time A Manifold Point Metric)
    (p : Point) (t : Time) : R :=
  G.evalScalarAt p (G.syntheticScalarCurvatureAt t)

/-- Pointwise squared Ricci norm. -/
noncomputable def ricciNormSqAt
    (G : GeometricRicciFlowData k R V Time A Manifold Point Metric)
    (p : Point) (t : Time) : R :=
  G.evalScalarAt p (G.syntheticRicciNormSqAt t)

/-- Pointwise squared trace-free Ricci norm. -/
noncomputable def tracefreeRicciNormSqAt
    (G : GeometricRicciFlowData k R V Time A Manifold Point Metric)
    (nInv : R) (p : Point) (t : Time) : R :=
  G.evalScalarAt p (G.syntheticTracefreeRicciNormSqAt nInv t)

@[simp] theorem scalarAt_def
    (G : GeometricRicciFlowData k R V Time A Manifold Point Metric)
    (p : Point) (t : Time) :
    G.scalarAt p t = G.evalScalarAt p (G.syntheticScalarCurvatureAt t) :=
  rfl

@[simp] theorem ricciNormSqAt_def
    (G : GeometricRicciFlowData k R V Time A Manifold Point Metric)
    (p : Point) (t : Time) :
    G.ricciNormSqAt p t = G.evalScalarAt p (G.syntheticRicciNormSqAt t) :=
  rfl

@[simp] theorem tracefreeRicciNormSqAt_def
    (G : GeometricRicciFlowData k R V Time A Manifold Point Metric)
    (nInv : R) (p : Point) (t : Time) :
    G.tracefreeRicciNormSqAt nInv p t =
      G.evalScalarAt p (G.syntheticTracefreeRicciNormSqAt nInv t) :=
  rfl

end GeometricRicciFlowData

/-- A point-time quantity is bounded above on a spacetime domain. -/
def BoundedAboveOnSpacetime {R Point Time : Type*} [Preorder R]
    (q : Point -> Time -> R) (domain : Point -> Time -> Prop) : Prop :=
  exists C, forall p t, domain p t -> q p t <= C

/-- A point-time quantity is unbounded above on a spacetime domain. -/
def UnboundedAboveOnSpacetime {R Point Time : Type*} [Preorder R]
    (q : Point -> Time -> R) (domain : Point -> Time -> Prop) : Prop :=
  forall C, exists p t, domain p t /\ C <= q p t

end GeometricRicciFlowData

section GeometricRicciFlowOnInterval

variable (k R V FlowTime AmbientTime A Manifold Point Metric : Type*)
variable [Field k] [CommRing R] [Algebra k R] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- A manifold-aware Ricci-flow package whose smooth calculus lives only on
`FlowTime`, while maximality and endpoint statements may use an ambient
interval type `AmbientTime`.

The field `core` is deliberately still the existing synthetic `RicciFlowData`.
Thus every local evolution identity quantifies only over regular flow times;
singular endpoints or infinity can be represented in `AmbientTime` without
pretending that `td.dt_apply` exists there. -/
structure GeometricRicciFlowOnInterval where
  core : RicciFlowData k R V FlowTime A
  manifold : Manifold
  pointMem : Point -> Prop
  toAmbientTime : FlowTime -> AmbientTime
  timeInterval : AmbientTime -> Prop
  regularTime : AmbientTime -> Prop
  regular_time_mem :
    forall t : FlowTime, timeInterval (toAmbientTime t) /\ regularTime (toAmbientTime t)
  initialTime : FlowTime
  metricAt : FlowTime -> Metric
  metricOn : Manifold -> Metric -> Prop
  metricAt_on : forall t, metricOn manifold (metricAt t)
  /-- Evaluation of a synthetic scalar in `R` at a manifold point. For concrete
  realizations, `R` is usually a scalar-function algebra. -/
  evalScalarAt : Point -> R -> R
  /-- Pointwise squared Riemann norm. This remains supplied until the
  synthetic core has a canonical `|Rm|^2` accessor. -/
  riemannNormSqAt : Point -> FlowTime -> R
  /-- Global curvature quantity used by extension/blow-up alternatives. -/
  curvatureQuantityAt : Point -> FlowTime -> R
  /-- Pointwise trace-free Ricci ratio used by the compactness/pinching bridge. -/
  pinchingRatioAt : Point -> FlowTime -> R
  /-- Pointwise improved-pinching quantity before the parabolic rescaling decay
  factor is applied. -/
  pinchingDecayQuantityAt : Point -> FlowTime -> R

namespace GeometricRicciFlowOnInterval

variable {k R V FlowTime AmbientTime A Manifold Point Metric : Type*}
variable [Field k] [CommRing R] [Algebra k R] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- The regular spacetime domain of an interval-aware geometric flow. -/
def spacetimeDomain
    (G : GeometricRicciFlowOnInterval k R V FlowTime AmbientTime A Manifold Point Metric)
    (p : Point) (t : FlowTime) : Prop :=
  G.pointMem p /\ G.timeInterval (G.toAmbientTime t) /\ G.regularTime (G.toAmbientTime t)

theorem initial_regular
    (G : GeometricRicciFlowOnInterval k R V FlowTime AmbientTime A Manifold Point Metric) :
    G.timeInterval (G.toAmbientTime G.initialTime) /\
      G.regularTime (G.toAmbientTime G.initialTime) :=
  G.regular_time_mem G.initialTime

/-- Riemann tensor of the synthetic core at a regular flow time. -/
noncomputable def syntheticRiemannTensorAt
    (G : GeometricRicciFlowOnInterval k R V FlowTime AmbientTime A Manifold Point Metric)
    (t : FlowTime) : TensorData R V 1 3 :=
  Rm_tensor G.core.emb (G.core.conn_fam t) (G.core.ha_fam t) (G.core.hal_fam t)
    (G.core.hsl_fam t) (G.core.hl_fam t)

/-- Ricci tensor of the synthetic core at a regular flow time. -/
noncomputable def syntheticRicciTensorAt
    (G : GeometricRicciFlowOnInterval k R V FlowTime AmbientTime A Manifold Point Metric)
    (t : FlowTime) : TensorData R V 0 2 :=
  ricciForm_tensor G.core.emb (G.core.conn_fam t) (G.core.ha_fam t)
    (G.core.hal_fam t) (G.core.hsl_fam t) (G.core.hl_fam t) G.core.atr

/-- Scalar curvature of the synthetic core at a regular flow time. -/
noncomputable def syntheticScalarCurvatureAt
    (G : GeometricRicciFlowOnInterval k R V FlowTime AmbientTime A Manifold Point Metric)
    (t : FlowTime) : R :=
  ScalarCurvature G.core.emb (G.core.conn_fam t) (G.core.ha_fam t)
    (G.core.hal_fam t) (G.core.hsl_fam t) (G.core.hl_fam t) G.core.atr
    (G.core.g_fam t)

/-- Squared Ricci norm of the synthetic core at a regular flow time. -/
noncomputable def syntheticRicciNormSqAt
    (G : GeometricRicciFlowOnInterval k R V FlowTime AmbientTime A Manifold Point Metric)
    (t : FlowTime) : R :=
  ricci_norm_sq G.core.emb (G.core.conn_fam t) (G.core.ha_fam t)
    (G.core.hal_fam t) (G.core.hsl_fam t) (G.core.hl_fam t) G.core.atr
    (G.core.g_fam t)

/-- Squared trace-free Ricci norm of the synthetic core at a regular flow time. -/
noncomputable def syntheticTracefreeRicciNormSqAt
    (G : GeometricRicciFlowOnInterval k R V FlowTime AmbientTime A Manifold Point Metric)
    (nInv : R) (t : FlowTime) : R :=
  tracefree_ricci_norm_sq G.core.emb (G.core.conn_fam t) (G.core.ha_fam t)
    (G.core.hal_fam t) (G.core.hsl_fam t) (G.core.hl_fam t) G.core.atr
    (G.core.g_fam t) nInv

/-- Pointwise scalar curvature at a regular flow time. -/
noncomputable def scalarAt
    (G : GeometricRicciFlowOnInterval k R V FlowTime AmbientTime A Manifold Point Metric)
    (p : Point) (t : FlowTime) : R :=
  G.evalScalarAt p (G.syntheticScalarCurvatureAt t)

/-- Pointwise squared Ricci norm at a regular flow time. -/
noncomputable def ricciNormSqAt
    (G : GeometricRicciFlowOnInterval k R V FlowTime AmbientTime A Manifold Point Metric)
    (p : Point) (t : FlowTime) : R :=
  G.evalScalarAt p (G.syntheticRicciNormSqAt t)

/-- Pointwise squared trace-free Ricci norm at a regular flow time. -/
noncomputable def tracefreeRicciNormSqAt
    (G : GeometricRicciFlowOnInterval k R V FlowTime AmbientTime A Manifold Point Metric)
    (nInv : R) (p : Point) (t : FlowTime) : R :=
  G.evalScalarAt p (G.syntheticTracefreeRicciNormSqAt nInv t)

@[simp] theorem scalarAt_def
    (G : GeometricRicciFlowOnInterval k R V FlowTime AmbientTime A Manifold Point Metric)
    (p : Point) (t : FlowTime) :
    G.scalarAt p t = G.evalScalarAt p (G.syntheticScalarCurvatureAt t) :=
  rfl

@[simp] theorem ricciNormSqAt_def
    (G : GeometricRicciFlowOnInterval k R V FlowTime AmbientTime A Manifold Point Metric)
    (p : Point) (t : FlowTime) :
    G.ricciNormSqAt p t = G.evalScalarAt p (G.syntheticRicciNormSqAt t) :=
  rfl

@[simp] theorem tracefreeRicciNormSqAt_def
    (G : GeometricRicciFlowOnInterval k R V FlowTime AmbientTime A Manifold Point Metric)
    (nInv : R) (p : Point) (t : FlowTime) :
    G.tracefreeRicciNormSqAt nInv p t =
      G.evalScalarAt p (G.syntheticTracefreeRicciNormSqAt nInv t) :=
  rfl

end GeometricRicciFlowOnInterval

end GeometricRicciFlowOnInterval
