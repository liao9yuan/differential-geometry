# Weak divergence pairings

## Role

`WeakDivergence.lean` supplies the lower-layer bridge from component weak
partials to a vector weak divergence and then extends that divergence identity
from smooth compactly supported tests to arbitrary `H₀¹` tests.

## Public API

- `hasWeakDiv_of_parts` assembles weak partials of the components of `F` into
  `HasWeakDiv (fun x => ∑ i, G i x) F Ω`.  The component functions and their
  weak partials are required to be locally integrable.  These hypotheses are
  necessary because `HasWeakPartialDeriv` itself records only the test identity;
  it does not carry local integrability, while finite Bochner-integral
  additivity requires it.
- `weakRHS_eq_integral` says that if `Ω` is open, `F` and its weak divergence
  `g` are square-integrable, and `v ∈ H₀¹(Ω)`, then every supplied Sobolev
  witness for `v` gives
  `weakProblemRHSOfField F v = ∫ x in Ω, g x * v x`.

No coefficient, elliptic-solution predicate, Poincare inequality, boundedness
of the domain, or compact ambient-space assumption is introduced.

## Proof route

For `hasWeakDiv_of_parts`, each component weak-partial identity is summed after
local integrability makes both compact-test pairings integrable.  Finite-sum
linearity then gives the weak-divergence identity.

For `weakRHS_eq_integral`, unpack the smooth compactly supported approximation
carried by `MemH01`.  Holder continuity of `L²` pairings passes both the scalar
pairing and every vector component pairing to the limit.  The smooth weak-
divergence identities therefore converge to the desired `H₀¹` identity.
Witness independence is supplied by `weakProblemRHSOfField_eq_of_memH01`.

## Verification

Focused verification is warning-free GREEN.  The file contains no `sorry`,
`admit`, new axiom, or frontier wrapper.  The explicit named module refresh is
also warning-free GREEN, so the exported declarations are current for downstream
imports.

## Project position

Both declarations in this lower-layer producer are complete.  The downstream
divergence-source interior `W^{2,2}` theorem and the general
`homSol_memWkp_succ` endpoint remain unstated and are therefore 0% theorem
endpoints; this file only closes their first reusable weak-formulation input.
The current project-plan estimates remain unchanged: splitting-dedicated
machinery is about 58--62%, whole P1c machinery about 65--69%, and the final
splitting theorem itself remains unstated at 0%.
