import DifferentialGeometry.Synthetic.Operator.Laplacian
import DifferentialGeometry.Synthetic.Assembly

/-!
# Heat Flow Bundle

Demonstrates that the current Synthetic abstraction is flow-agnostic:
a heat-equation bundle is defined WITHOUT modifying any existing abstract
layer (`Synthetic/{Algebra,Analysis,Operator,Geometry}/`) or `RicciFlowBundle`.

PDE: `∂_t u = Δu` with a FIXED Riemannian metric + Levi-Civita connection.
-/

set_option autoImplicit false

open SyntheticTensor

/-- Bundle capturing a heat flow `∂_t u = Δu` on a fixed Riemannian manifold. -/
structure HeatFlowBundle (k R V Time A : Type*)
    [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    [CommRing A] [Algebra R A]
    extends ScalarTimeEvolvingManifoldData k R V Time A where
  /-- The heat equation `∂_t u = Δu`, for every time. -/
  heat_eq : ∀ t : Time,
    td.dt_apply u_fam t =
      laplacian emb met atr conn conn_add_right conn_leibniz
        conn_add_left conn_smul_left (u_fam t)
