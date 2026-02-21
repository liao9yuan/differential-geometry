# Differential Geometry in Lean 4

A self-contained formalization of Differential Geometry in Lean 4. 

## Background

Currently, we take the advantage of algebraic aspects of geometry:
- **Smooth Functions ($R$):** Treated as a commutative ring.
- **Vector Fields ($V$):** Treated as a module over $R$.
- **Vector Fields:** treated as derivations.

## Current Capabilities

The library currently supports the following:
- **Algebraic Foundations:** Scalar multiplication, derivation actions, and Lie brackets.
- **Riemannian Metrics:** Symmetric $C^\infty$-bilinear forms and metric trace operators.
- **Affine Connections:** Covariant derivatives, torsion-free property, and metric compatibility.
- **Curvature Tensors:** Formal definition of Riemann, Ricci, and Scalar curvature.
- **Levi-Civita Theorem:** A blackboxed existence and uniqueness(of the ODE system) proof for the Levi-Civita connection.

## Installation

Ensure you have [Lean 4](https://lean-lang.org/lean4/doc/setup.html) installed.

```bash
# Clone the repository
git clone git@github.com:qinz1yang/differential-geometry.git
cd differential-geometry

# Build the library
lake build