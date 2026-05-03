import DifferentialGeometry.Synthetic.Axioms

/-!
# Hamilton-Jacobi Bundle

PDE: `∂_t u + H(du) = 0` on a fixed Riemannian manifold, where `du` is the
abstract differential of `u` (an `R`-linear functional `V → R`) and `H` is
a user-specified Hamiltonian `(V →ₗ[R] R) → R`.

Instances:
* `H ω = ω(∇E) − L(∇E, x)` for a Lagrangian `L` → classical HJ.
* `H ω := met.g_inv ω ω / 2` → eikonal / geometric optics.
* `H ω := |ω|² / 2 + V(u)` for a potential V → HJ with potential (one must
  either fold the potential V into the velocity-only formulation, or extend
  `H` to also take `u`; see `HamiltonJacobiWithStateBundle` below).

Does NOT include the viscous Hamilton-Jacobi `∂_t u + H(du) = ε·Δu`; for
that, use a reaction-diffusion-style bundle with velocity `velocity u := ε·Δu − H(du)`,
OR extend this bundle to add a viscosity term.
-/

set_option autoImplicit false

open SyntheticTensor

namespace HamiltonJacobi

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Abstract differential of a scalar `u : R`, as an `R`-linear functional on `V`.
`differential emb u X = (emb.embed X) u = X(u)`. -/
noncomputable def differential (emb : DerivationEmbedding k R V) (u : R) :
    V →ₗ[R] R where
  toFun X := (emb.embed X) u
  map_add' X Y := by
    change (emb.embed (X + Y)) u = (emb.embed X) u + (emb.embed Y) u
    rw [map_add]
    rfl
  map_smul' c X := by
    change (emb.embed (c • X)) u = (RingHom.id R) c • (emb.embed X) u
    rw [map_smul]
    rfl

end HamiltonJacobi

/-- Bundle for a Hamilton-Jacobi equation `∂_t u + H(du) = 0`.

The Hamiltonian `H` depends only on the differential `du`. For state-dependent
Hamiltonians `H(x, u, du)`, fold the `x` dependence into `R = C^∞(M)` naturally,
and extend this bundle if `u`-dependence is needed (see `HamiltonJacobiWithStateBundle`). -/
structure HamiltonJacobiBundle (k R V Time A : Type*)
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
  /-- The Hamiltonian as a function on covectors `V →ₗ[R] R`. -/
  H : (V →ₗ[R] R) → R
  /-- Time-dependent scalar state `u(t) : R`. -/
  u_fam : Time → R
  /-- The state is a regular time family. -/
  h_u : td.isSmoothFam u_fam
  /-- The Hamilton-Jacobi equation `∂_t u + H(du) = 0`. -/
  hj_eq : ∀ t : Time,
    td.dt_apply u_fam t + H (HamiltonJacobi.differential emb (u_fam t)) = 0

attribute [instance] HamiltonJacobiBundle.td_regular

/-- Variant where the Hamiltonian depends on both `u` and `du`
(i.e. `∂_t u + H(u, du) = 0`). -/
structure HamiltonJacobiWithStateBundle (k R V Time A : Type*)
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
  /-- The state-dependent Hamiltonian `H(u, du)`. -/
  H : R → (V →ₗ[R] R) → R
  /-- Time-dependent scalar state. -/
  u_fam : Time → R
  /-- The state is a regular time family. -/
  h_u : td.isSmoothFam u_fam
  /-- Hamilton-Jacobi equation `∂_t u + H(u, du) = 0`. -/
  hj_eq : ∀ t : Time,
    td.dt_apply u_fam t + H (u_fam t) (HamiltonJacobi.differential emb (u_fam t)) = 0

attribute [instance] HamiltonJacobiWithStateBundle.td_regular
