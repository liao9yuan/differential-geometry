import DifferentialGeometry.Synthetic.Axioms

/-!
# Scalar Gradient Flow Bundle

Abstract scalar gradient flow on a fixed Riemannian manifold:

```
∂_t u = velocity(u)
```

where `velocity : R → R` is a user-specified velocity functional. Typically
`velocity = -grad E` for some energy `E`, but this bundle is agnostic about
the origin of `velocity`: it only requires that the PDE be of the given form.

Instances:
* `velocity = laplacian …`  → heat flow (`HeatFlowBundle`).
* `velocity u = laplacian u ^ m` → porous medium equation.
* `velocity u = laplacian u - f u` → reaction-diffusion (see `Flow/ReactionDiffusion`).
* `velocity u = laplacian u - ½ |∇u|²`  → viscous Hamilton-Jacobi (variant).

A vector-state gradient flow (`∂_t F = grad E(F)` with `F` valued in a module
`V'`) would require extending `TimeDerivativeData` to handle V'-valued time
families; deferred.
-/

set_option autoImplicit false

open SyntheticTensor

/-- Scalar gradient flow on a fixed Riemannian manifold. -/
structure ScalarGradientFlowBundle (k R V Time A : Type*)
    [Field k] [CommRing R] [Algebra k R]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A]
    extends RiemannianManifoldData k R V where
  /-- Time derivative. -/
  td : TimeDerivativeData R A Time
  /-- Regularity filter + closure axioms. -/
  [td_regular : TimeRegularFam td]
  /-- Spatial and temporal derivatives commute. -/
  spatial_temporal_comm : SpatialTemporalComm emb td
  /-- The velocity functional. Think of this as `-grad E` for some energy `E`. -/
  velocity : R → R
  /-- Time-dependent scalar state `u(t) : R`. -/
  u_fam : Time → R
  /-- The state is a regular time family. -/
  h_u : td.isSmoothFam u_fam
  /-- The gradient-flow equation `∂_t u = velocity(u)`. -/
  flow_eq : ∀ t : Time, td.dt_apply u_fam t = velocity (u_fam t)

attribute [instance] ScalarGradientFlowBundle.td_regular
