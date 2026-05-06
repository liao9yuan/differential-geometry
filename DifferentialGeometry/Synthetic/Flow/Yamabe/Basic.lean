import DifferentialGeometry.Synthetic.Geometry.ConnectionExtended
import DifferentialGeometry.Synthetic.Operator.Variation
import DifferentialGeometry.Synthetic.Assembly

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
    [CommRing A] [Algebra R A]
    extends TimeEvolvingFamilyManifoldData k R V Time A where
  /-- Scalar velocity. For unnormalized Yamabe: `scalar_velocity t = -S(t)`;
      for normalized Yamabe: `scalar_velocity t = S̄(t) − S(t)`. -/
  scalar_velocity : Time → R
  /-- The Yamabe / conformal flow equation `∂_t g = scalar_velocity · g`. -/
  yamabe_eq : ∀ t : Time,
    metric_var_form td (fun τ => (lc_fam τ).met) h_met t =
      scalar_velocity t • ((lc_fam t).met).g_tensor
