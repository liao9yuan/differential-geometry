# RicciFromJetsCompact

## Scope

This downstream module isolates the compact-uniform extension of the pointwise
Ricci/scalar two-jet estimates from `RicciFromJets.lean`.  It imports that module
acyclically; `RicciFromJets.lean` does not import back.  The only intended public
declaration is `scalarSub_le_dNormOn`.

## Current status

- `scalarSub_le_dNormOn`: **100% implemented and focused-verified**; the final
  file check is warning-free GREEN in 35.2 seconds.  The named refresh is also
  warning-free GREEN at 4045/4045, so the exported declaration is fresh.
- Dedicated compact-uniform machinery for this theorem: **100% implemented and
  focused-verified**.
- P2a remains **100%**.
- The whole P0–P9 program remains roughly **15–25%**; this compact estimate is
  one P2b producer and does not complete the downstream pointed-action or
  reduced-volume convergence endpoints.

The first focused check exposed local integration failures before reaching the
theorem: the downstream file had not reopened the public
`DifferentialGeometry.Integral.DivergenceTheorem` namespace containing
`partialDeriv` and `chartRicciTensor`; iterated-derivative evaluations used an
explicit vector where `basis_apply_le` had produced the extensionally equal
`fun i => basis (![... ] i)`; three finrank constants omitted an explicit
`Nat`-to-`Real` coercion; and the finite active-chart set used a shadow-prone
local name in its membership rewrite.  The public
`chartGramOnE_contDiffOn_int` bridge already exists in
`DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients`.  The source now
uses these existing public namespaces, explicit finite-function extensionality,
explicit coercions, and an unshadowed active-set name.  No upstream wrapper,
`sorry`, or new axiom was added.  A coordinated retry was pending at that stage;
one reported
timeout was downstream of the earlier elaboration cascade and is not yet an
independent performance blocker.

The second focused check passed the namespace reopening but exposed the next
local layer: the zero-jet result tried to rewrite with local function values;
the smooth Gram bridge still needed its defining module imported directly;
three Christoffel bounds required specialization of a two-index inverse-Gram
bound at the output index; the Ricci difference needed the explicit algebraic
split `(A + B) - (C + D) = (A - C) + (B - D)` before `abs_add_le`; a two-term
absolute-value helper from the upstream affine file was private; and the scalar
inverse-Gram comparison needed to rewrite the chart inverse point by `hψ`.
These are now repaired respectively by `simpa only`, the narrow direct import
of `IteratedInvGramJetLipschitz`, explicit lambda specialization, the algebraic
rewrite, a private `abs_sub` corollary, and the inverse-point rewrite.  No public
API or hypothesis changed.  The reported timeouts and private-constant message
remain classified as cascades until this repaired source is retried.

The third focused check reduced the source failures to one mistaken use of the
three-point `abs_sub` API and three unspecialized Gram-bracket families in
`christoffel_abs_le`.  It also reported local unused-context warnings.  The
absolute-value helper now rewrites subtraction as addition of a negative and
uses `abs_add`; every Christoffel call specializes both the inverse-Gram and
Gram-bracket families at its fixed indices.  The private compact Gram helper no
longer carries an unused nonnegativity proof, and the unused section instances
are omitted from the two private algebra helpers.  Public assumptions and names
are unchanged.  A fourth focused retry was pending at that stage; the timeouts/private-constant
message are still treated as cascades rather than independent blockers.

The fourth focused check left exactly two source fixes before the remaining
cascade timeouts: Mathlib's two-argument `abs_sub a b` already has the helper's
target shape, and the absolute-Ricci compact helper still carried an unused
`hB`.  The helper now uses `exact abs_sub a b`; the unused private binder and
its sole call argument are removed.  The public theorem and its hypotheses are
unchanged.  The next coordinated retry was pending at that stage.

The fifth focused check found no new type or theorem-shape error.  The only two
remaining deterministic failures were WHNF heartbeat limits in the private
`jet2Diff_le_dNorm_on` and `chartRicci_sub_le_on` proofs; later private-constant
errors were their cascade.  The first proof has now been split by derivative
order into the private `jet0Diff_le_dNorm`, `jet1Diff_le_dNorm`, and
`jet2Sum_le_dNorm` producers.  Each order helper invokes the corresponding
`chartJet_sub_le` estimate and carries its own narrow 400k heartbeat allowance;
`jet2Diff_le_dNorm_on` now only adds their three finite-sum bounds and no longer
has a local heartbeat override.  The independent `chartRicci_sub_le_on` timeout
retains its narrow 800k allowance.  A sixth focused retry was pending at that
stage.  If this proof-shape split still
hits a performance wall, the existing `chartJet2_sub_le` jet-norm estimate plus
a smallest jet-norm-to-concrete-coordinate bridge is the reserved distinct
route; it has not been introduced while the present route remains coherent.

The finite-sum conclusions now unfold their local constants with `dsimp only`
before applying `Finset.sum_mul`, avoiding rewrite matching against a local
definition; their summands explicitly normalize the multiplicative factor order.
The private `chartRicci_sub_le_on` also no longer carries its unused proof that
the family bound is nonnegative.  Static audit then confirmed that this proof
was unused throughout `scalarSub_le_on` and the final assembly as well, so the
then-unverified and not-yet-consumed public `scalarSub_le_dNormOn` took the weaker
signature without `hB : 0 ≤ B`.  No other assumption or public name changed.

The next focused elaboration succeeded in 34.3 seconds and reported only the
same unused-section-variable warning on the three order helpers.  Each helper
now omits the unused `NeZero (Module.finrank ℝ E)` instance locally.  The
following focused elaboration succeeded in 35.6 seconds and left only the same
warning on the private main assembler `jet2Diff_le_dNorm_on`; it now has the
  same local omit.  An intermediate focused check then completed warning-free
  GREEN in 35.0 seconds, with no further proof or public-signature change.

## Implemented route

1. `jet2Diff_le_dNorm_on` upgrades the existing fixed-chart compact
   `chartJet_sub_le` estimates at orders zero, one, and two to the concrete
   `chartMetricJet2DiffSup` bound.
2. `gram12_le_on` applies `chartGram_iter_le` to the family of all metrics obeying
   the uniform covariant two-jet bound on the compact set.  This makes the first
   and second chart-Gram derivative bounds independent of the selected pair of
   metrics.
3. `chartRicci_sub_le_on` combines `invGram_le_of_lowOn` with the existing
   inverse-Gram, Christoffel, differentiated-Christoffel, and affine Ricci
   estimates.  Its constant is uniform over the bounded metric family on one
   fixed compact chart piece.
4. `chartRicci_abs_le_on` supplies the absolute Ricci component bound needed for
   the scalar contraction, using the same uniform inverse/Gram bounds rather
   than adding a scalar or Ricci bound as a hypothesis.
5. `scalarSub_le_on` uses the off-centre chart Ricci identity and the coordinate
   scalar trace.  It controls both terms in the difference of the inverse-metric
   Ricci contractions.
6. `scalarSub_le_dNormOn` uses the existing `chartAtlasPOU`.  Local finiteness
   gives finitely many supports meeting the requested compact set; each compact
   piece is the intersection with a POU `tsupport`, which lies in its subordinate
   chart.  Positivity of the partition selects an active chart at every point.

## Verification status

The final focused check completed warning-free GREEN in 35.2 seconds.  It
successfully elaborated the subtype family passed to
`chartGram_iter_le`, all three finite-order Fréchet-derivative bridges, the
finite-active partition-of-unity assembly, and the off-centre Ricci contraction.
The named refresh also completed warning-free GREEN at 4045/4045, making the
export fresh.  A direct axiom audit remains a downstream integration check; the
source file itself is now a checked producer.

An earlier refresh had reported style warnings because four theorem-local
heartbeat options followed their `omit` wrappers.  Those options now precede
the complete omit chain, each with a short reason for the enlarged budget,
matching the repository-clean pattern; the final refresh confirms the cleanup.
Proofs, option values, and APIs are unchanged.

## Remaining P2b endpoint blocker

Even after this estimate is checked, full fixed-curve pointed-action convergence
still needs the compact-uniform spacetime application: turn the existing
metric-jet convergence on the confined compact spacetime region into uniform
scalar pullback convergence, then combine it with the already checked pullback
velocity/kinetic identity.  Minimizer and full-mass wrappers remain downstream
and are not part of this module.
