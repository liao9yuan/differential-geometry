import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

variable {R V : Type}
variable [Add R] [Mul R] [Sub R] [Neg R]
variable [Add V] [Sub V] [Neg V] [ScalarMul R V]
variable [DerivationAction R V]

open DerivationAction

/--
The Hessian of a function `u` is defined as the tensor field
$\nabla^2 u(X, Y) = X(Y(u)) - (\nabla_X Y)(u)$.
-/
def Hess (conn : AffineConnection R V) (u : R) (X Y : V) : R :=
  action X (action Y u) - action (conn.nabla X Y) u
