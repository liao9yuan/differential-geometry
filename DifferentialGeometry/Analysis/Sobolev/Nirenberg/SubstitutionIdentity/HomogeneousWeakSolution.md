# Homogeneous weak-solution substitution

## Current result

The file now provides the witness-native substitution identities needed before
the quantitative Nirenberg difference-quotient estimate:

- `stdTestWitnessOn` constructs the standard Nirenberg test witness on an open
  domain whenever the closed translation thickening of `tsupport eta` stays in
  the domain.
- `stdTest_grad` identifies its weak-gradient components pointwise with the
  explicit formula formed from the original witness `hu.weakGrad`.
- `stdTest_memH01On` proves that the localized test is an admissible zero-trace
  test.
- `homSol_substOn` gives the directly usable finite-sum set-integral identity on
  the original domain. It does not hide the identity behind an opaque test
  witness or bilinear-form conclusion.
- `homSol_subst` is the corresponding whole-space identity.

No `CompactSpace` assumption, classical derivative of the rough solution, or
consumer-side compatibility hypothesis was introduced.

## Proof route

The local witness is multiplied by a smooth cutoff that equals one on a
buffered closed thickening of the translation region. The compactly supported
product is placed in `W₀¹`, zero-extended to the whole Euclidean space, and fed
to the checked whole-space standard-test witness. On the translation region,
local constancy of the cutoff gives zero cutoff derivative, so the zero-extended
product witness has exactly the original weak gradient. This pointwise identity
at both difference-quotient sample points rewrites the complete inner formula;
the outer difference quotient then rewrites by function equality. The final
local witness is rebuilt with that explicit gradient.

## Verification and failed shapes

Focused verification is warning-free GREEN, and the explicit named module
refresh is GREEN.

The first draft failed because existential data were eliminated from `Prop`
inside a definition returning witness data. Replacing those eliminations by
`Classical.choose` and its specification fixed the large-elimination error.
The next draft exposed an `ENNReal.ofReal 2 = 2` cast in the zero-extension
gradient. Rebuilding the two cast witnesses explicitly while preserving their
weak-gradient fields removed the coercion obstruction. The remaining issues
were local argument-order and already-closed-goal repairs; there was no
mathematical or missing-API blocker.

The named refresh makes the new declarations available to the immediate
downstream homogeneous-master module.

## Frontier and project scale

The desired local `H²` regularity theorem itself is not yet stated or proved
(0%). This file closes the genuine signed substitution-identity producer, but
the uniform difference-quotient estimate and weak-limit/MemWkp assembly remain.
As a conservative project view: the splitting endpoint remains 0%; its
dedicated P1c machinery is about 40--45%; P1c as a phase is about 60--65%; the
whole Poincare infrastructure is about 15--25%; the final Poincare endpoint is
0%.
