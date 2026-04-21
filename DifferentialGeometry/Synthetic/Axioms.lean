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
    [Field k] [CommRing R] [Algebra k R]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    extends SyntheticManifoldData k R V where
  /-- Metric duality: metric tensor, inverse, sharp/flat. -/
  met : MetricDuality R V
  /-- The connection is metric-compatible. -/
  metric_compat : IsMetricCompatible emb conn met
  /-- The connection is torsion-free. -/
  torsion_free : IsTorsionFree emb conn
  /-- Characteristic ≠ 2: 2a = 0 → a = 0. -/
  char_ne_2 : ∀ (a : R), (2 : R) * a = 0 → a = 0

structure TimeEvolvingManifoldData (k R V Time A : Type*)
    [Field k] [CommRing R] [Algebra k R]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A]
    extends RiemannianManifoldData k R V where
  /-- Time derivative as a Mathlib derivation. -/
  td : TimeDerivativeData R A Time
  /-- Spatial and temporal derivatives commute. -/
  spatial_temporal_comm : SpatialTemporalComm emb td
  /-- ∂_t commutes with trace. -/
  time_tr_comm : TimeTrComm atr td


structure RicciFlowBundle (k R V Time A : Type*)
    [Field k] [CommRing R] [Algebra k R]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A] where
  /-- Derivation embedding: vector fields as derivations. -/
  emb : DerivationEmbedding k R V
  /-- Abstract trace and tensor contraction. -/
  atr : AbstractTrace R V
  /-- Time derivative. -/
  td : TimeDerivativeData R A Time
  /-- Time-dependent family of metrics. -/
  g_fam : Time → MetricDuality R V
  /-- Smoothness of the metric family's scalar slices. -/
  h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs)
  /-- Time-dependent family of connections. -/
  conn_fam : Time → V → V → V
  /-- Connection right additivity for each time. -/
  ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z
  /-- Connection left additivity for each time. -/
  hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z
  /-- Connection scalar left for each time. -/
  hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z
  /-- Connection Leibniz for each time. -/
  hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y
  /-- Spatial and temporal derivatives commute. -/
  spatial_temporal_comm : SpatialTemporalComm emb td
  /-- ∂_t commutes with trace. -/
  time_tr_comm : TimeTrComm atr td
  /-- ∇ commutes with endomorphism trace, for each time. -/
  nabla_tr_comm : ∀ s, NablaTrComm emb atr (conn_fam s) (ha_fam s) (hl_fam s)
  /-- ∇ commutes with tensor contraction, for each time. -/
  nabla_contract_comm : ∀ s, NablaTensorContractComm emb atr (conn_fam s) (ha_fam s) (hl_fam s)
  /-- Characteristic ≠ 2. -/
  char_ne_2 : ∀ (a : R), (2 : R) * a = 0 → a = 0
  /-- The Ricci flow equation: ∂_t g = -2 Rc, with Levi-Civita at each time. -/
  ricci_flow : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam
  /-- Product rule for ∂_t and ∇ with varying connections. -/
  nabla_time_product_rule : NablaTimeProductRule emb td conn_fam ha_fam hl_fam
