import DifferentialGeometry.Synthetic.Algebra.VectorFieldAlgebra
import DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Analysis.NablaTimeInteraction
import DifferentialGeometry.Synthetic.Operator.Variation
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

open SyntheticTensor

structure SyntheticManifoldData (k R V : Type*)
    [Field k] [CommRing R] [Algebra k R]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V] where
  /-- Derivation embedding: vector fields as derivations. -/
  emb : DerivationEmbedding k R V
  /-- Abstract trace and tensor contraction. -/
  atr : AbstractTrace R V
  /-- Affine connection. -/
  conn : V → V → V
  /-- Connection: right additivity in the second argument. -/
  conn_add_right : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z
  /-- Connection: left additivity in the first argument. -/
  conn_add_left : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z
  /-- Connection: scalar multiplication in the first argument. -/
  conn_smul_left : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z
  /-- Connection: Leibniz rule in the second argument. -/
  conn_leibniz : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y
  /-- ∇ commutes with endomorphism trace. -/
  nabla_tr_comm : NablaTrComm emb atr conn conn_add_right conn_leibniz
  /-- ∇ commutes with tensor contraction. -/
  nabla_contract_comm : NablaTensorContractComm emb atr conn conn_add_right conn_leibniz

structure RiemannianManifoldData (k R V : Type*)
    [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    extends SyntheticManifoldData k R V where
  /-- Metric duality: metric tensor, inverse, sharp/flat. -/
  met : MetricDuality R V
  /-- The connection is metric-compatible. -/
  metric_compat : IsMetricCompatible emb conn met
  /-- The connection is torsion-free. -/
  torsion_free : IsTorsionFree emb conn

structure TimeEvolvingManifoldData (k R V Time A : Type*)
    [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A]
    extends RiemannianManifoldData k R V where
  /-- Time derivative as a Mathlib derivation. -/
  td : TimeDerivativeData R A Time
  /-- Regularity filter + closure axioms for `td`. -/
  [td_regular : TimeRegularFam td]
  /-- Spatial and temporal derivatives commute. -/
  spatial_temporal_comm : SpatialTemporalComm emb td
  /-- ∂_t commutes with trace. -/
  time_tr_comm : TimeTrComm atr td

attribute [instance] TimeEvolvingManifoldData.td_regular

/-- A time-evolving manifold carrying a scalar state `u(t)`. Base class for heat flow,
reaction-diffusion, gradient flow, Hamilton-Jacobi, etc. -/
structure ScalarTimeEvolvingManifoldData (k R V Time A : Type*)
    [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A]
    extends RiemannianManifoldData k R V where
  /-- Time derivative. -/
  td : TimeDerivativeData R A Time
  /-- Regularity filter + closure axioms for `td`. -/
  [td_regular : TimeRegularFam td]
  /-- Spatial/temporal commutation. -/
  spatial_temporal_comm : SpatialTemporalComm emb td
  /-- Time-dependent scalar state. -/
  u_fam : Time → R
  /-- The state is a regular time family. -/
  h_u : td.isSmoothFam u_fam

attribute [instance] ScalarTimeEvolvingManifoldData.td_regular

/-- A manifold carrying a time-dependent family of Riemannian metrics with Levi-Civita
connections at each time. Base class for Ricci flow, Yamabe flow, etc. -/
structure TimeEvolvingFamilyManifoldData (k R V Time A : Type*)
    [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A] where
  /-- Derivation embedding: vector fields as derivations. -/
  emb : DerivationEmbedding k R V
  /-- Abstract trace and tensor contraction. -/
  atr : AbstractTrace R V
  /-- Time derivative. -/
  td : TimeDerivativeData R A Time
  /-- Regularity filter. -/
  [td_regular : TimeRegularFam td]
  /-- Time-dependent family of metrics with their Levi-Civita connections. -/
  lc_fam : Time → LeviCivitaMetricData emb
  /-- Smoothness of the metric family's scalar slices. -/
  h_met : ∀ vs αs, td.isSmoothFam (fun τ => ((lc_fam τ).met).g_tensor vs αs)
  /-- Spatial/temporal commutation. -/
  spatial_temporal_comm : SpatialTemporalComm emb td
  /-- ∂_t commutes with trace. -/
  time_tr_comm : TimeTrComm atr td
  /-- ∇ commutes with endomorphism trace, for each time. -/
  nabla_tr_comm : ∀ s, NablaTrComm emb atr ((lc_fam s).conn)
    ((lc_fam s).conn_add_right) ((lc_fam s).conn_leibniz)
  /-- ∇ commutes with tensor contraction, for each time. -/
  nabla_contract_comm : ∀ s, NablaTensorContractComm emb atr ((lc_fam s).conn)
    ((lc_fam s).conn_add_right) ((lc_fam s).conn_leibniz)

attribute [instance] TimeEvolvingFamilyManifoldData.td_regular

namespace TimeEvolvingFamilyManifoldData

variable {k R V Time A : Type*}
variable [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

def g_fam (D : TimeEvolvingFamilyManifoldData k R V Time A) :
    Time → MetricDuality R V :=
  fun t => (D.lc_fam t).met

def conn_fam (D : TimeEvolvingFamilyManifoldData k R V Time A) :
    Time → V → V → V :=
  fun t => (D.lc_fam t).conn

theorem ha_fam (D : TimeEvolvingFamilyManifoldData k R V Time A) (s : Time) :
    forall X Y Z, D.conn_fam s X (Y + Z) = D.conn_fam s X Y + D.conn_fam s X Z :=
  (D.lc_fam s).conn_add_right

theorem hal_fam (D : TimeEvolvingFamilyManifoldData k R V Time A) (s : Time) :
    forall X Y Z, D.conn_fam s (X + Y) Z = D.conn_fam s X Z + D.conn_fam s Y Z :=
  (D.lc_fam s).conn_add_left

theorem hsl_fam (D : TimeEvolvingFamilyManifoldData k R V Time A) (s : Time) :
    forall (f : R) X Z, D.conn_fam s (f • X) Z = f • D.conn_fam s X Z :=
  (D.lc_fam s).conn_smul_left

theorem hl_fam (D : TimeEvolvingFamilyManifoldData k R V Time A) (s : Time) :
    forall X (f : R) Y,
      D.conn_fam s X (f • Y) = (D.emb.embed X) f • Y + f • D.conn_fam s X Y :=
  (D.lc_fam s).conn_leibniz

theorem levi_civita (D : TimeEvolvingFamilyManifoldData k R V Time A) (s : Time) :
    IsLeviCivita D.emb (D.conn_fam s) (D.g_fam s) :=
  (D.lc_fam s).levi_civita

end TimeEvolvingFamilyManifoldData


structure RicciFlowBundle (k R V Time A : Type*)
    [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A]
    extends TimeEvolvingFamilyManifoldData k R V Time A where
  /-- Joint (2-time) regularity for `td`, needed by the ∂_t/∇ product rule. -/
  [td_regular2 : TimeRegularFam2 td]
  /-- The Ricci flow equation: ∂_t g = -2 Rc, with Levi-Civita at each time. -/
  ricci_flow : IsRicciFlow emb td atr (fun t => (lc_fam t).met) h_met
    (fun t => (lc_fam t).conn) (fun t => (lc_fam t).conn_add_right)
    (fun t => (lc_fam t).conn_add_left) (fun t => (lc_fam t).conn_smul_left)
    (fun t => (lc_fam t).conn_leibniz)
  /-- Product rule for ∂_t and ∇ with varying connections. -/
  nabla_time_product_rule : NablaTimeProductRule emb td (fun t => (lc_fam t).conn)
    (fun t => (lc_fam t).conn_add_right) (fun t => (lc_fam t).conn_leibniz)

attribute [instance] RicciFlowBundle.td_regular2
