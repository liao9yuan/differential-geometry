# Differential Geometry in Lean 4

A lightweighted, self-contained formalization of differential geometry in Lean 4. 

## Background

We are treating:
- **Smooth Functions ($R$):**  as a commutative ring.
- **Space of Smooth Vector Fields Γ(TM):**  as a module ($V$) over $R$.
- **Vector Fields:**  as derivations.

## Philosophy

This library prioritizes algebraic structure over topological construction. 

* **Coordinate Insensitivity:** The framework operates entirely without local charts. However, on the user side, concrete coordinate calculations can be executed seamlessly by instantiating the module with explicit spaces (see `EuclideanSample.lean`).
* **Axiomatic Injection:** Analytical bottlenecks (e.g., PDE existence, maximum principles) can be easily isolated and injected as axioms by the user. This permits strict algebraic verification of tensor evolutions (e.g., Ricci flow) without the prerequisite of building topological manifolds.
* **Compositional Operators:** Higher-order derivatives and complex geometric flows are constructed via pure functional composition rather than hardcoded index manipulations.

## Current Capabilities
- **Affine Connections:** Covariant derivatives, Koszul formula, torsion-free property, metric compatibility.
- **Algebraic Foundations:** Scalar multiplication, derivation actions, Lie brackets, trace operators.
- **Curvature Tensors:** Riemann, Ricci, and Scalar curvature, Ricci identities, First Bianchi identity.
- **Differential Operators:** Gradient, Hessian, Laplacian, Bochner identity, Second Covariant Derivative.
- **Geometric Flows:** Ricci Flow equations, evolution of curvature and operators.
- **Levi-Civita Theorem:** Existence and uniqueness of the Levi-Civita connection via the Koszul formula.
- **Riemannian Metrics:** Symmetric $C^\infty$-bilinear forms, metric trace operators.
- **Tensor Operations:** Smooth bilinear forms, covariant derivatives, second covariant derivatives, and inner products of $(0,2)$-tensors.

## Proven Theorems
- **[Bochner-Weitzenböck Identity](https://en.wikipedia.org/wiki/Bochner_formula):** 
  
  > If $u \colon M \rightarrow \mathbb{R}$ is a smooth function, then 
  > $$\frac{1}{2}\Delta |\nabla u|^2 = g(\nabla \Delta u, \nabla u) + |\nabla^2 u|^2 + \text{Ric}(\nabla u, \nabla u)$$
  
  `bochner_identity` in `DifferentialGeometry/Operators/Bochner.lean`
- **[First Bianchi Identity](https://en.wikipedia.org/wiki/Riemann_curvature_tensor#Symmetries_and_identities):** The cyclic sum of the Riemann curvature tensor vanishes for a torsion-free connection. Theorem: `first_bianchi` in `DifferentialGeometry/Geometry/Bianchi.lean`
- **[Fundamental Theorem of Riemannian Geometry](https://en.wikipedia.org/wiki/Fundamental_theorem_of_Riemannian_geometry):** Existence and uniqueness of the Levi-Civita connection. Theorem: `levi_civita_exists_unique` in `DifferentialGeometry/Geometry/Connection.lean`
- **[Ricci Identity](https://en.wikipedia.org/wiki/Riemann_curvature_tensor#Definition):** The commutator of the second covariant derivative equals the Riemann curvature tensor for a torsion-free connection. Theorem: `ricci_identity` in `DifferentialGeometry/Geometry/RicciIdentity.lean`

## Proven Properties
- **Hessian Symmetry:** Hessian symmetry for torsion-free connections. Theorem: `hessian_symm` in `DifferentialGeometry/Operators/Hessian.lean`
- **Metric Compatibility of Covariant Derivative:** The covariant derivative of the metric tensor is exactly zero. Theorem: `metric_covDerivOp_zero` in `DifferentialGeometry/Operators/CovariantDerivative.lean`
- **Metric Compatibility of Squared Norm:** Directional derivative of a squared vector norm. Theorem: `norm_sq_deriv` in `DifferentialGeometry/Geometry/Connection.lean`
- **Metric Subtraction Properties:** Properties of the metric tensor under subtraction. Theorem: `metric_sub_left` in `DifferentialGeometry/Geometry/Connection.lean`
- **Second Covariant Derivative Bilinearity:** $C^\infty$-linearity of the second covariant derivative operator with respect to both vector field arguments. Theorems: `secondCovDeriv_smul_X`, `secondCovDeriv_smul_Y` in `DifferentialGeometry/Operators/SecondCovariantDerivative.lean`
- **Tensor Inner Product Properties:** Symmetry, additivity, and scalar multiplication linearity of the inner product of (0,2)-tensors. Theorems: `tensorInnerProduct_symm`, `tensorInnerProduct_add_left`, `tensorInnerProduct_smul_left` in `DifferentialGeometry/Algebra/TensorInnerProduct.lean`

## How to use?
### There are examples in `Examples` folder. One illustrates calculation, one illustrates proof.
- **`EuclideanSample.lean`:** Calculation of gradient, Hessian, Laplacian, metric variation, and Ricci curvature in $\mathbb{R}^3$.
- **`HessianSymmetry.lean`:** Proof of Hessian symmetry using Lie derivations.


## Limitations

This library inherently assumes:
* **Intrinsic Smoothness:** Smoothness and convergence are absorbed by the type system. The framework cannot model Sobolev spaces, distributions, or measure-theoretic jump functions.
For singularities occured at time $T$, in like Ricci Flow, we would have to work on $t \in[0,T)$, before the metric degenerates.
* **Strict Non-degeneracy:** The musical isomorphism (`InverseMetric`) enforces a strict  bijection. The framework effectively assumes finite-dimensional manifolds.


## Installation

Ensure you have [Lean 4](https://lean-lang.org/lean4/doc/setup.html) installed.

```bash
# Clone the repository
git clone git@github.com:qinz1yang/differential-geometry.git
cd differential-geometry

# Build the library
lake build
```

## Contributing

Contributions and suggestions are welcome. Please discuss with me via email:
`zq + sqrt(1444) {at} cornell [dot] edu`

## References
The abstractions and formalizations in this library are heavily inspired by and built upon the following texts:

- Chow, B., et al. Hamilton's Ricci Flow (ISBN 978-1-4704-7369-3).
- Colding, T. H., & Minicozzi II, W. P. A Course in Minimal Surfaces (ISBN 978-1-4704-7640-3).
- Differential Geometry and Applications, Richard Hamilton, Monique Chyba and Xiaodong Cao
- Hongxi Wu, An Introduction to Riemannian Geometry. (2014). Higher Education Press. (This is not a book in English, but it can be found [here](https://www.overdrive.com/media/12444682/黎曼几何初步-preliminary-riemann-geometry). ISBN 978-7-04-040458-6)


