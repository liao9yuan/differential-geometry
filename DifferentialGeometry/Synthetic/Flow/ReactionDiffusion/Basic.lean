import DifferentialGeometry.Synthetic.Operator.Laplacian
import DifferentialGeometry.Synthetic.Assembly

/-!
# Reaction-Diffusion Bundle

PDE: `∂_t u = Δu + f(u)` on a fixed Riemannian manifold.

Instances of the reaction term `f : R → R`:
* `f = 0` → heat flow.
* `f u = u (1 − u)` → Fisher-KPP (logistic reaction).
* `f u = u (u − a)(1 − u)` for `0 < a < 1` → Nagumo / bistable.
* `f u = u − u³` → Allen-Cahn.

`f` is specified by the bundle user; no structural assumption on `f` is
imposed at the bundle level.
-/

set_option autoImplicit false

open SyntheticTensor

/-- Bundle for a reaction-diffusion equation `∂_t u = Δu + f(u)`. -/
structure ReactionDiffusionBundle (k R V Time A : Type*)
    [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A]
    extends ScalarTimeEvolvingManifoldData k R V Time A where
  /-- The reaction term `f : R → R`. -/
  reaction : R → R
  /-- The reaction-diffusion equation `∂_t u = Δu + f(u)`. -/
  rd_eq : ∀ t : Time,
    td.dt_apply u_fam t =
      laplacian emb met atr conn conn_add_right conn_leibniz
        conn_add_left conn_smul_left (u_fam t) +
      reaction (u_fam t)
