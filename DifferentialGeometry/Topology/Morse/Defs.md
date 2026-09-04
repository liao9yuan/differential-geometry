# Morse definitions: universe-polymorphic manifold carriers

## Purpose

The generic Morse definitions must accept finite-dimensional manifolds whose model and carrier
types live in arbitrary universes. The previous explicit `Type` binders unnecessarily restricted
`E`, `H`, and `M` to universe zero.

## Source change

- Generalized only the explicit generic model, chart, and manifold binders from `Type` to `Type*`.
- Made the codomain of `SublevelSpace` universe-inferred with `Type _`.
- Preserved all declaration names, definitions, hypotheses, and proof bodies.
- Left fixed universe-zero model types such as the real-valued Morse models unchanged.

## Verification status

The universe-polymorphic source passed a warning-free focused check and explicit
named module refresh.  No declaration name, mathematical statement, or proof
route changed.  Downstream Morse modules may consume the refreshed interface.
