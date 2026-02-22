# Differential Geometry in Lean 4

A self-contained formalization of differential geometry in Lean 4. 

## Background

Thanks to modern algebra, we are treating:
- **Smooth Functions ($R$):**  as a commutative ring.
- **Vector Fields ($V$):**  as a module over $R$.
- **Vector Fields:**  as a derivations.

## Current Capabilities
- **Affine Connections:** Covariant derivatives, Koszul formula, torsion-free property, metric compatibility.
- **Algebraic Foundations:** Scalar multiplication, derivation actions, Lie brackets, trace operators.
- **Curvature Tensors:** Riemann, Ricci, and Scalar curvature.
- **Differential Operators:** Gradient, Hessian, Laplacian, Bochner operators.
- **Geometric Flows:** Ricci Flow equations, evolution of curvature and operators.
- **Levi-Civita Theorem:** Existence and uniqueness of the Levi-Civita connection via the Koszul formula.
- **Riemannian Metrics:** Symmetric $C^\infty$-bilinear forms, metric trace operators.

## Proven Theorems
- **Fundamental Theorem of Riemannian Geometry:** Existence and uniqueness of the Levi-Civita connection. Theorem: `levi_civita_exists_unique` in `DifferentialGeometry/Geometry/Connection.lean`
- **Hessian Symmetry:** Hessian symmetry for torsion-free connections. Theorem: `hessian_symm` in `DifferentialGeometry/Operators/Hessian.lean`
- **Metric Compatibility of Squared Norm:** Directional derivative of a squared vector norm. Theorem: `norm_sq_deriv` in `DifferentialGeometry/Geometry/Connection.lean`
- **Metric Tensor Properties:** Properties of the metric tensor. Theorems: `metric_neg_left`, `metric_sub_left` in `DifferentialGeometry/Geometry/Connection.lean`
## Examples
- **`EuclideanSample.lean`:** Calculation of gradient, Hessian, Laplacian, metric variation, and Ricci curvature in $\mathbb{R}^3$.
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
- Differential Geometry and Applications, Richard Hamilton, Monique Chyba and Xiaodong Cao
- Hongxi Wu, An Introduction to Riemannian Geometry. (2014). Higher Education Press.


