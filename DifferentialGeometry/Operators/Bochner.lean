import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Trace
import DifferentialGeometry.Geometry.Curvature
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import DifferentialGeometry.Geometry.Metric
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Operators.Hessian
import DifferentialGeometry.Operators.Laplacian

set_option autoImplicit false
set_option linter.style.longLine false

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V] [LieBracket V] [TraceOperator R V]

variable (metric : MetricTensor R V) [MetricTraceOperator R V metric]
variable (conn : AffineConnection R V)

-- Uninterpreted operations needed to state the formulas
variable (grad : R → V)
variable (laplacianV : V → V)
variable (norm_sq_V : V → R)
variable (norm_sq_T : (V → V → R) → R)

/--
Commutator of Laplacian and Gradient:
$\Delta \nabla u = \nabla \Delta u + \text{Rc}(\nabla u, \cdot)$

We express this by taking the inner product with an arbitrary vector field `X`.
-/
axiom laplacian_grad_commutator (u : R) (X : V) :
  metric.g (laplacianV (grad u)) X =
  metric.g (grad (laplacian metric conn u)) X + Rc conn (grad u) X

/--
The Bochner-Weitzenböck formula:
$\frac{1}{2} \Delta |\nabla u|^2 = |\nabla^2 u|^2 + \langle \nabla u, \nabla \Delta u \rangle + \text{Rc}(\nabla u, \nabla u)$

Since we might not have a general division by 2 in our abstract algebraic structures,
we express it as $A = B + B$:
$\Delta |\nabla u|^2 = 2 \left( |\nabla^2 u|^2 + \langle \nabla u, \nabla \Delta u \rangle + \text{Rc}(\nabla u, \nabla u) \right)$
-/
axiom bochner_weitzenbock (u : R) :
  laplacian metric conn (norm_sq_V (grad u)) =
    (norm_sq_T (Hess conn u) +
     metric.g (grad u) (grad (laplacian metric conn u)) +
     Rc conn (grad u) (grad u)) +
    (norm_sq_T (Hess conn u) +
     metric.g (grad u) (grad (laplacian metric conn u)) +
     Rc conn (grad u) (grad u))
