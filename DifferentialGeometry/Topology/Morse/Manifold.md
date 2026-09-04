# Morse manifold API

## 2026-08-29 universe generalization

The Morse normal-form and regular-level-facing declarations are mathematical
statements about manifolds and model spaces in arbitrary universes. Their prior
explicit `Type` binders imposed an accidental universe-zero restriction that
prevented reuse by universe-polymorphic comparison geometry.

The source now uses `Type*` for the `H`/`M` binders of
`morse_lemma_of_contMDiff`, the critical-point chart equivalences, and
`morse_lemma`.  The two private translation/Hessian helpers remain at `Type`
because the Mathlib `fderiv_translate` API they use is universe-zero and their
only consumer is the fixed universe-zero `MorseModel`; widening those helpers
does not contribute to the generic manifold interface.  Declaration names,
hypotheses, conclusions, and public proof bodies are otherwise unchanged; no
new assumption or parallel API was introduced.

The generalized public API passed a warning-free focused check and explicit
named module refresh.  The required `MorseLemma` artifact was refreshed first
after the upstream definition's universe signature changed.  No mathematical
or API blocker remains in this module.
