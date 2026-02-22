import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V]

open DerivationAction

/-- Hessian of a function: `∇²u(X, Y) = X(Y(u)) - (∇_X Y)(u)`.
Input: (AffineConnection R V, R, V, V)
Output: R -/
def Hess (conn : AffineConnection R V) (u : R) (X Y : V) : R :=
  action X (action Y u) - action (conn.nabla X Y) u
