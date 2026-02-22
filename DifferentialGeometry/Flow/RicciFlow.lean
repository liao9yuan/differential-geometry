import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Trace
import DifferentialGeometry.Geometry.Connection
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import DifferentialGeometry.Geometry.Curvature
import DifferentialGeometry.Operators.Laplacian
import DifferentialGeometry.Operators.Gradient

set_option autoImplicit false
set_option linter.style.longLine false

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V] [LieBracket V] [TraceOperator R V]

-- A real parameter `t` for time
variable (Time : Type)

-- A family of metrics parametrized by `R`
variable (metric_family : R → MetricTensor R V)
variable (conn_family : R → AffineConnection R V)

-- An abstract time derivative operator for scalar functions of `R`
variable (partial_t : (R → R) → R → R)

/-- Ricci flow equation: `∂_t g = -2Rc`.
Input: (R, V, V)
Output: Prop -/
axiom ricci_flow (t : R) (X Y : V) :
  partial_t (fun s => (metric_family s).g X Y) t =
    -(Rc (conn_family t) X Y + Rc (conn_family t) X Y)

-- Uninterpreted norm squared of Rc for stating the evolution equation
variable (norm_sq_Rc : R → R)
variable (MetricTraceOperator_family : ∀ t, MetricTraceOperator R V (metric_family t))

/-- Evolution of scalar curvature under Ricci flow: `∂_t R = ΔR + 2|Rc|²`.
Input: (R)
Output: Prop -/
axiom scalar_curvature_evolution (t : R) :
  let metric_t := metric_family t
  let conn_t := conn_family t
  partial_t (fun s => ScalarCurvature (conn_family s) (metric_family s)) t =
    laplacian metric_t conn_t (ScalarCurvature conn_t metric_t) +
    norm_sq_Rc t + norm_sq_Rc t

-- To express ⟨Rc, Hess u⟩, we need an inner product of tensors
variable (tensor_inner : (V → V → R) → (V → V → R) → R)

/-- Evolution of the Laplacian under Ricci flow: `∂_t (Δu) = Δ(∂_t u) + 2⟨Rc, ∇²u⟩`.
Input: (R, R)
Output: Prop -/
axiom laplacian_evolution (t u : R) :
  let metric_t := metric_family t
  let conn_t := conn_family t
  partial_t (fun s => laplacian (metric_family s) (conn_family s) u) t =
    laplacian metric_t conn_t (partial_t (fun _ => u) t) +
    tensor_inner (Rc conn_t) (Hess conn_t u) +
    tensor_inner (Rc conn_t) (Hess conn_t u)

-- To express the gradient, we use the MusicalIsomorphism class
variable (MusicalIsomorphism_family : ∀ t, MusicalIsomorphism R V (metric_family t))

/-- Evolution of the gradient norm squared under Ricci flow: `∂_t |∇u|² = 2⟨∇u, ∇(∂_t u)⟩ + 2Rc(∇u, ∇u)`.
Input: (R, R)
Output: Prop -/
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
