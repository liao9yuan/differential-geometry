import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Trace
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import DifferentialGeometry.Operators.Laplacian
import DifferentialGeometry.Operators.Gradient

set_option autoImplicit false

variable {R V : Type}
variable [Add R] [Mul R] [Sub R] [Neg R]
variable [Add V] [Sub V] [Neg V] [ScalarMul R V]
variable [DerivationAction R V] [LieBracket V] [TraceOperator R V]

-- A real parameter `t` for time
variable (Time : Type)

-- A family of metrics parametrized by `R`
variable (metric_family : R → MetricTensor R V)
variable (conn_family : R → AffineConnection R V)

-- An abstract time derivative operator for scalar functions of `R`
variable (partial_t : (R → R) → R → R)

/--
The Ricci flow equation:
$\partial_t g = -2 \text{Rc}$

For a family of metrics $g_t$ and their corresponding Levi-Civita connections $\nabla_t$,
we express the partial derivative of the metric components as $-2 \text{Rc}_t(X, Y)$.
Since our algebraic structures might only have addition, we write $-2\text{Rc}$ as
$-(\text{Rc} + \text{Rc})$.
-/
axiom ricci_flow (t : R) (X Y : V) :
  partial_t (fun s => (metric_family s).g X Y) t =
    -(Rc (conn_family t) X Y + Rc (conn_family t) X Y)

-- Uninterpreted norm squared of Rc for stating the evolution equation
variable (norm_sq_Rc : R → R)
variable (MetricTraceOperator_family : ∀ t, MetricTraceOperator R V (metric_family t))

/--
The evolution equation for scalar curvature under Ricci Flow:
$\partial_t R = \Delta R + 2|\text{Rc}|^2$

We express this using the abstract Laplacian we defined, applied to the
scalar curvature. Like before, we write $2|\text{Rc}|^2$ as
$|\text{Rc}|^2 + |\text{Rc}|^2$.
-/
axiom scalar_curvature_evolution (t : R) :
  let metric_t := metric_family t
  let conn_t := conn_family t
  partial_t (fun s => ScalarCurvature (conn_family s) (metric_family s)) t =
    laplacian metric_t conn_t (ScalarCurvature conn_t metric_t) +
    norm_sq_Rc t + norm_sq_Rc t

-- To express ⟨Rc, Hess u⟩, we need an inner product of tensors
variable (tensor_inner : (V → V → R) → (V → V → R) → R)

/--
The evolution of the Laplacian under Ricci flow:
$\partial_t (\Delta u) = \Delta (\partial_t u) + 2 \langle \text{Rc}, \nabla^2 u \rangle$
-/
axiom laplacian_evolution (t u : R) :
  let metric_t := metric_family t
  let conn_t := conn_family t
  partial_t (fun s => laplacian (metric_family s) (conn_family s) u) t =
    laplacian metric_t conn_t (partial_t (fun _ => u) t) +
    tensor_inner (Rc conn_t) (Hess conn_t u) +
    tensor_inner (Rc conn_t) (Hess conn_t u)

-- To express the gradient, we use the MusicalIsomorphism class
variable (MusicalIsomorphism_family : ∀ t, MusicalIsomorphism R V (metric_family t))

/--
The evolution of the gradient norm squared under Ricci flow:
$\partial_t |\nabla u|^2 = 2 \langle \nabla u, \nabla (\partial_t u) \rangle + 2 \text{Rc}(\nabla u, \nabla u)$

(Note: $|\nabla u|^2 = g(\nabla u, \nabla u)$ is the norm squared with respect to the
time-dependent metric $g_t$.)
-/
axiom gradient_norm_evolution (t u : R) :
  let metric_t := metric_family t
  let iso_t := MusicalIsomorphism_family t
  partial_t (fun s =>
    let metric_s := metric_family s
    have _ : MusicalIsomorphism R V metric_s := MusicalIsomorphism_family s
    metric_s.g (grad metric_s u) (grad metric_s u)) t =
    (have _ : MusicalIsomorphism R V metric_t := iso_t
     metric_t.g (grad metric_t u) (grad metric_t (partial_t (fun _ => u) t)) +
     metric_t.g (grad metric_t u) (grad metric_t (partial_t (fun _ => u) t))) +
    (have _ : MusicalIsomorphism R V metric_t := iso_t
     Rc (conn_family t) (grad metric_t u) (grad metric_t u) +
     Rc (conn_family t) (grad metric_t u) (grad metric_t u))
