# Differential Geometry in Lean 4

A lightweight, self-contained formalization of differential geometry in Lean 4. 

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
- **Affine Connections:** Conformal transformations, covariant derivatives, Koszul formula, torsion-free property, metric compatibility.
- **Algebraic Foundations:** Scalar multiplication, derivation actions, Lie brackets, trace operators, Lie derivation rules.
- **Curvature Tensors:** Riemann, Ricci, and Scalar curvature, Ricci identities, First Bianchi identity, tensoriality of Riemann curvature.
- **Differential Operators:** Bochner identity, Divergence, Gradient, Hessian, Laplacian, Lie Derivative, Second Covariant Derivative.
- **Geometric Flows:** Ricci Flow equations, evolution of curvature and operators.
- **Global Integration:** Abstract integral operators and the Divergence Theorem.
- **Levi-Civita Theorem:** Existence and uniqueness of the Levi-Civita connection via the Koszul formula.
- **Riemannian Metrics:** Symmetric $C^\infty$-bilinear forms, metric trace operators.
- **Tensor Operations:** Smooth bilinear forms, covariant derivatives, second covariant derivatives, and inner products of $(0,2)$-tensors.

## Proven Theorems
- **[Bochner-Weitzenböck Identity](https://en.wikipedia.org/wiki/Bochner_formula):** 
  > If $f \colon M \rightarrow \mathbb{R}$ is a smooth function, then 
  > $$\Delta |\nabla f|^2 = 2 |\nabla^2 f|^2 + 2 \text{Ric}(\nabla f, \nabla f) + 2 g(\nabla f, \nabla \Delta f)$$
  
  Theorem: `bochner_identity` in `DifferentialGeometry/Operators/Bochner.lean`
- **[Conformal Modification of Connection](https://en.wikipedia.org/wiki/Conformal_map):** 
  > If $\nabla$ is a torsion-free connection on a manifold $M$, then its conformal transformation via a scalar function $u \in C^\infty(M)$ strictly preserves the torsion-free property.
  
  Theorem: `conformal_torsion_free` in `DifferentialGeometry/Geometry/Conformal.lean`
- **[First Bianchi Identity](https://en.wikipedia.org/wiki/Riemann_curvature_tensor#Symmetries_and_identities):** 
  > If $\nabla$ is a torsion-free connection on a manifold $M$, then for any vector fields $X, Y, Z \in \mathfrak{X}(M)$, the Riemann curvature tensor $R$ satisfies
  > $$R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0$$
  
  Theorem: `first_bianchi` in `DifferentialGeometry/Geometry/Bianchi.lean`
- **[Fundamental Theorem of Riemannian Geometry](https://en.wikipedia.org/wiki/Fundamental_theorem_of_Riemannian_geometry):** 
  > For any Riemannian manifold $(M, g)$, there exists a unique affine connection $\nabla$ (the Levi-Civita connection) such that for all vector fields $X, Y, Z \in \mathfrak{X}(M)$:
  > $$[X, Y] = \nabla_X Y - \nabla_Y X \quad \text{and} \quad X(g(Y, Z)) = g(\nabla_X Y, Z) + g(Y, \nabla_X Z)$$
  
  Theorem: `levi_civita_exists_unique` in `DifferentialGeometry/Geometry/Connection.lean`
- **[Integration by Parts (Green's First Identity)](https://en.wikipedia.org/wiki/Green%27s_identities):** 
  > Assuming the global integral of a divergence vanishes ($\int \text{div}(X) = 0$), then for any vector field $X$ and scalar function $f$, Green's first identity is algebraically satisfied:
  > $$\int f \text{div}(X) + \int X(f) = 0$$
  
  Theorem: `integration_by_parts` in `DifferentialGeometry/Operators/Divergence.lean`
- **[Lie Derivative of Metric Tensor](https://en.wikipedia.org/wiki/Lie_derivative#The_Lie_derivative_of_a_tensor_field):** 
  > If $\nabla$ is a torsion-free, metric-compatible connection on a manifold $M$, then for any vector fields $X, Y, Z \in \mathfrak{X}(M)$, the Lie derivative of the metric $g$ along $X$ is equivalently formulated using the symmetrized covariant derivative:
  > $$(\mathcal{L}_X g)(Y, Z) = g(\nabla_Y X, Z) + g(Y, \nabla_Z X)$$
  
  Theorem: `lieDerivMetric_eq_nabla` in `DifferentialGeometry/Operators/LieDerivative.lean`
- **[Ricci Identity](https://en.wikipedia.org/wiki/Riemann_curvature_tensor#Definition):** 
  > If $\nabla$ is a torsion-free connection on a manifold $M$, then for any vector fields $X, Y, Z \in \mathfrak{X}(M)$, the commutator of the second covariant derivative satisfies
  > $$\nabla^2_{X,Y} Z - \nabla^2_{Y,X} Z = R(X,Y)Z$$
  
  Theorem: `ricci_identity` in `DifferentialGeometry/Geometry/RicciIdentity.lean`

## Proven Properties
- **Divergence Product Rule:** The Leibniz rule for the divergence of a scalar-multiplied vector field. Theorem: `divergence_smul` in `DifferentialGeometry/Operators/Divergence.lean`
- **Hessian Symmetry:** Hessian symmetry for torsion-free connections. Theorem: `hessian_symm` in `DifferentialGeometry/Operators/Hessian.lean`
- **Metric Compatibility of Covariant Derivative:** The covariant derivative of the metric tensor is exactly zero. Theorem: `metric_covDerivOp_zero` in `DifferentialGeometry/Operators/CovariantDerivative.lean`
- **Metric Compatibility of Squared Norm:** Directional derivative of a squared vector norm. Theorem: `norm_sq_deriv` in `DifferentialGeometry/Geometry/Connection.lean`
- **Metric Sign and Subtraction Properties:** Algebraic behavior of the metric tensor under negation and subtraction in its arguments. Lemmas: `metric_neg_left_local`, `metric_sub_left_local`, `metric_sub_right_local` in `DifferentialGeometry/Operators/LieDerivative.lean`
- **Metric Subtraction Properties:** Properties of the metric tensor under subtraction. Theorem: `metric_sub_left` in `DifferentialGeometry/Geometry/Connection.lean`
- **Riemann Curvature Tensoriality:** $C^\infty$-linearity of the Riemann curvature tensor with respect to its first and third vector field arguments. Theorems: `Rm_smul_X`, `Rm_smul_Z` in `DifferentialGeometry/Geometry/CurvatureTensor.lean`
- **Second Covariant Derivative Bilinearity:** $C^\infty$-linearity of the second covariant derivative operator with respect to both vector field arguments. Theorems: `secondCovDeriv_smul_X`, `secondCovDeriv_smul_Y` in `DifferentialGeometry/Operators/SecondCovariantDerivative.lean`
- **Tensor Inner Product Properties:** Symmetry, additivity, and scalar multiplication linearity of the inner product of (0,2)-tensors. Theorems: `tensorInnerProduct_symm`, `tensorInnerProduct_add_left`, `tensorInnerProduct_smul_left` in `DifferentialGeometry/Algebra/TensorInnerProduct.lean`

## Limitations

This library inherently assumes:
* **Intrinsic Smoothness:** Smoothness and convergence are absorbed by the type system. The framework cannot model Sobolev spaces, distributions, or measure-theoretic jump functions.
For singularities occurred at time $T$, such as in Ricci Flow, we would have to work on $t \in [0,T)$, before the metric degenerates.
* **Strict Non-degeneracy:** The musical isomorphism (`InverseMetric`) enforces a strict bijection. The framework effectively assumes **finite-dimensional** manifolds.


## Installation

Ensure you have [Lean 4](https://lean-lang.org/lean4/doc/setup.html) installed.

```bash
# Clone the repository
git clone git@github.com:qinz1yang/differential-geometry.git
cd differential-geometry

# Build the library
lake build
```

## How to use?
### There are examples in `Examples` folder. One illustrates calculation, one illustrates proof.
- **`EuclideanSample.lean`:** Calculation of gradient, Hessian, Laplacian, metric variation, and Ricci curvature in $\mathbb{R}^3$.
- **`HessianSymmetry.lean`:** Proof of Hessian symmetry using Lie derivations. (This is already in the library, but it is a good example.)


## Contributing

Contributions and suggestions are welcome. Please discuss with me via email:
`zq + sqrt(1444) {at} cornell [dot] edu`

(all lower case, no symbols)

## References
The abstractions and formalizations in this library are heavily inspired by and built upon the following texts:

- Chow, B., et al. Hamilton's Ricci Flow (ISBN 978-1-4704-7369-3).
- Colding, T. H., & Minicozzi II, W. P. A Course in Minimal Surfaces (ISBN 978-1-4704-7640-3).
- Differential Geometry and Applications, Richard Hamilton, Monique Chyba and Xiaodong Cao
- Hongxi Wu, An Introduction to Riemannian Geometry. (2014). Higher Education Press. (This is not a book in English, but it can be found [here](https://www.overdrive.com/media/12444682/黎曼几何初步-preliminary-riemann-geometry). ISBN 978-7-04-040458-6)


