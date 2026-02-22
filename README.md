# Differential Geometry in Lean 4

A self-contained formalization of differential geometry in Lean 4. 

## Background

Thank you, algebra! We are treating:
- **Smooth Functions ($R$):**  as a commutative ring.
- **Vector Fields ($V$):**  as a module over $R$.
- **Vector Fields:**  as a derivations.

## Current Capabilities
- **Algebraic Foundations:** Scalar multiplication, derivation actions, Lie brackets, trace operators.
- **Riemannian Metrics:** Symmetric $C^\infty$-bilinear forms, metric trace operators.
- **Affine Connections:** Covariant derivatives, Koszul formula, torsion-free property, metric compatibility.
- **Curvature Tensors:** Riemann, Ricci, and Scalar curvature.
- **Levi-Civita Theorem:** Existence and uniqueness of the Levi-Civita connection via the Koszul formula.
- **Differential Operators:** Gradient, Hessian, Laplacian, Bochner operators.
- **Geometric Flows:** Ricci Flow equations, evolution of curvature and operators.

## Proven Theorems
- **`levi_civita_exists_unique`:** Existence and uniqueness of the Levi-Civita connection. (`DifferentialGeometry/Geometry/Connection.lean`)
- **`hessian_symm`:** Hessian symmetry for torsion-free connections. (`Examples/HessianSymmetry.lean`)
- **`norm_sq_deriv`:** Directional derivative of a squared vector norm. (`Examples/MetricCompatibility.lean`)
- **`metric_neg_left`, `metric_sub_left`:** Properties of the metric tensor. (`DifferentialGeometry/Geometry/Connection.lean`)
## Examples
- **`EuclideanSample.lean`:** Calculation of gradient, Hessian, Laplacian, metric variation, and Ricci curvature in $\mathbb{R}^3$.
- **`MetricCompatibility.lean`:** Proof of the metric compatibility product rule on norms.
- **`HessianSymmetry.lean`:** Proof of Hessian symmetry using Lie derivations.
## Installation

Ensure you have [Lean 4](https://lean-lang.org/lean4/doc/setup.html) installed.

```bash
# Clone the repository
git clone git@github.com:qinz1yang/differential-geometry.git
cd differential-geometry

# Build the library
lake build
```

## References
The abstractions and formalizations in this library are heavily inspired by and built upon the following texts:

- Chow, B., et al. Hamilton's Ricci Flow.
- Colding, T. H., & Minicozzi II, W. P. A Course in Minimal Surfaces.
- Hamilton, R., Chyba, M., & Cao, X. Differential Geometry and Applications.


