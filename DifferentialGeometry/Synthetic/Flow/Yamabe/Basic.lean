import DifferentialGeometry.Synthetic.Geometry.ConnectionExtended
import DifferentialGeometry.Synthetic.Operator.Variation
import DifferentialGeometry.Synthetic.Axioms

/-!
# Yamabe Flow Bundle

PDE: `∂_t g = -S · g`, where `S` is the scalar curvature of `g(t)` and the
connection is Levi-Civita at each time.

This is the **unnormalized** Yamabe flow. The normalized Yamabe flow
`∂_t g = (S̄ − S) · g` requires the mean scalar curvature `S̄`, which
involves integration over the manifold — not available purely synthetically
without additional volume/measure infrastructure. The bundle here takes
an explicit `scalar_velocity : Time → R` so users can plug in either
the unnormalized `-S` form or a normalized `S̄(t) − S(t)` form if they
supply `S̄` externally.

Structurally parallel to `RicciFlowBundle`: the metric evolves with the
connection tracking Levi-Civita at each time. Only the specific PDE differs.
-/

set_option autoImplicit false

open SyntheticTensor

/-- Bundle for a conformal (Yamabe-like) metric flow
    `∂_t g = scalar_velocity(t) · g` with Levi-Civita connection at each time. -/
structure YamabeFlowBundle (k R V Time A : Type*)
    [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A] where
  /-- Derivation embedding. -/
  emb : DerivationEmbedding k R V
  /-- Abstract trace / tensor contraction. -/
  atr : AbstractTrace R V
  /-- Time derivative. -/
  td : TimeDerivativeData R A Time
  /-- Regularity filter + closure axioms. -/
  [td_regular : TimeRegularFam td]
  /-- Time-dependent family of metrics. -/
  g_fam : Time → MetricDuality R V
  /-- Smoothness of the metric family's scalar slices. -/
  h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs)
  /-- Time-dependent family of connections. -/
  conn_fam : Time → V → V → V
  /-- Connection right additivity. -/
  ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z
  /-- Connection left additivity. -/
  hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z
  /-- Connection scalar left. -/
  hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z
  /-- Connection Leibniz. -/
  hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y
  /-- ∂_t and spatial X commute on regular families. -/
  spatial_temporal_comm : SpatialTemporalComm emb td
  /-- ∂_t commutes with trace. -/
  time_tr_comm : TimeTrComm atr td
  /-- ∇ commutes with endomorphism trace, for each time. -/
  nabla_tr_comm : ∀ s, NablaTrComm emb atr (conn_fam s) (ha_fam s) (hl_fam s)
  /-- ∇ commutes with tensor contraction, for each time. -/
  nabla_contract_comm : ∀ s, NablaTensorContractComm emb atr (conn_fam s) (ha_fam s) (hl_fam s)
  /-- The connection is Levi-Civita for the metric at every time. -/
  levi_civita : ∀ s, IsLeviCivita emb (conn_fam s) (g_fam s)
  /-- Scalar velocity. For unnormalized Yamabe: `scalar_velocity t = -S(t)`;
      for normalized Yamabe: `scalar_velocity t = S̄(t) − S(t)`. -/
  scalar_velocity : Time → R
  /-- The Yamabe / conformal flow equation `∂_t g = scalar_velocity · g`. -/
  yamabe_eq : ∀ t : Time,
    metric_var_form td g_fam h_met t = scalar_velocity t • (g_fam t).g_tensor

attribute [instance] YamabeFlowBundle.td_regular
