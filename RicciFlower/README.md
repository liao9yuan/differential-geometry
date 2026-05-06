# RicciFlower

This folder is a fresh realized rebuild of the Ricci-flow stack. It imports
only `Mathlib.*` and `RicciFlower.*`; older prototype folders are historical
references and are not dependencies.

Build order:

1. vendored vector-bundle helpers and realized tensor bundles;
2. local scalar time calculus;
3. mathlib local-frame coordinate helpers;
4. realized metric families and connection predicates;
5. realized Ricci-flow and curvature interfaces;
6. realized gradient, divergence, and Laplacian;
7. scalar maximum-principle infrastructure.

Current status: the active root path is realized-only. The old synthetic V2
prototype modules were moved out of this folder so dependency checks over
`RicciFlower` stay clean.

The tensor foundation is copied from the concrete tensor/vector-bundle
development: `Tensor0SSpace`, `TensorRSSpace`, `Tensor0SField`, and
`TensorRSField` are section/fiber-based objects over the tangent bundle, not the
old fixed-vector-space `TensorData` shim.  The Riemannian pointwise-inner
tensor files are kept as inactive placeholders until the supporting analytic
measure layer is ready to vendor.

Section 12 work in the older Ricci-flow prototype should be mined theorem by
theorem for proof strategy and concrete target names, but RicciFlower should
port the realized definitions instead of importing that prototype.
