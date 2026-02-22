# Differential Geometry in Lean 4

A lightweighted, self-contained formalization of differential geometry in Lean 4. 

## Background

We are treating:
- **Smooth Functions ($R$):**  as a commutative ring.
- **Space of Smooth Vector Fields ($\Gamma(TM)$):**  as a module ($V$) over $R$.
- **Vector Fields:**  as derivations.

## Current Capabilities
- **Affine Connections:** Covariant derivatives, Koszul formula, torsion-free property, metric compatibility.
- **Algebraic Foundations:** Scalar multiplication, derivation actions, Lie brackets, trace operators.
- **Curvature Tensors:** Riemann, Ricci, and Scalar curvature.
- **Differential Operators:** Gradient, Hessian, Laplacian, Bochner operators.
- **Geometric Flows:** Ricci Flow equations, evolution of curvature and operators.
- **Levi-Civita Theorem:** Existence and uniqueness of the Levi-Civita connection via the Koszul formula.
- **Riemannian Metrics:** Symmetric $C^\infty$-bilinear forms, metric trace operators.

## Proven Theorems
- **[Fundamental Theorem of Riemannian Geometry](https://en.wikipedia.org/wiki/Fundamental_theorem_of_Riemannian_geometry):** Existence and uniqueness of the Levi-Civita connection. Theorem: `levi_civita_exists_unique` in `DifferentialGeometry/Geometry/Connection.lean`
- **Hessian Symmetry:** Hessian symmetry for torsion-free connections. Theorem: `hessian_symm` in `DifferentialGeometry/Operators/Hessian.lean`
- **Metric Compatibility of Squared Norm:** Directional derivative of a squared vector norm. Theorem: `norm_sq_deriv` in `DifferentialGeometry/Geometry/Connection.lean`
- **Metric Tensor Properties:** Properties of the metric tensor. Theorems: `metric_neg_left`, `metric_sub_left` in `DifferentialGeometry/Geometry/Connection.lean`

## Examples
- **`EuclideanSample.lean`:** Calculation of gradient, Hessian, Laplacian, metric variation, and Ricci curvature in $\mathbb{R}^3$.
- **`HessianSymmetry.lean`:** Proof of Hessian symmetry using Lie derivations.


## Limitations

This library trades analytical topology for algebraic elegance. By design, it inherently assumes:

* **No Local Coordinates:** There are no charts, atlases, or topological spaces. All operators are coordinate-free and defined strictly on global sections.
* **Intrinsic Smoothness:** Smoothness and convergence are absorbed by the type system. The framework cannot model Sobolev spaces, distributions, or measure-theoretic jump functions.
For singularities occured at time $T$, in like Ricci Flow, we would have to work on $t \in[0,T)$, before the metric degenerates.
* **Strict Non-degeneracy:** The musical isomorphism (`InverseMetric`) enforces a strict  bijection. The framework effectively assumes finite-dimensional manifolds.
* **Singularity as Resolution Failure:** Because the metric must remain non-degenerate, geometric singularities (such as finite-time neckpinches in Ricci Flow) are not modeled analytically; they simply manifest as typeclass resolution failures.

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


