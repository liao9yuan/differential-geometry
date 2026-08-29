# Tight

## Scope

`mass_tendsto_of_cc` is the generic no-mass-loss assembly lemma needed by the
fixed-manifold Perelman lane. It assumes convergence of real integrals against
every compactly supported continuous test function and a common compact set
whose exterior has eventually small mass for the approximating measures and
small mass for the limit measure.

The theorem is deliberately below Ricci flow and introduces no new tightness
predicate or convergence structure.

## Native route

Mathlib's locally compact Urysohn lemma supplies a compactly supported cutoff
which is one on the chosen compact set and takes values in `[0, 1]`. For any
finite measure, its cutoff integral lies between the mass of the compact set
and the total mass. Splitting total mass across the compact set and its
complement therefore bounds total mass above by the cutoff integral plus the
exterior tail. The claimed result follows from these two inequalities, cutoff
integral convergence, and the two tail bounds.

No existing theorem directly performs this upgrade. The finite-measure weak
convergence characterization is not a substitute: its constant-one test
already includes convergence of total mass and would make this argument
circular.

A second static signature audit confirmed that the cutoff theorem is in the
root namespace, the indicator-integral and real-measure complement split are
in `MeasureTheory`, and the complement split must be used symmetrically to
write total mass as compact mass plus tail. `NNReal.tendsto_coe` is oriented
from real-coercion convergence to nonnegative-real convergence, so the proof
rewrites the target in the reverse direction before applying the metric
epsilon criterion.

The full static proof audit also checked the coercion chain used here. A
`FiniteMeasure` supplies an `IsFiniteMeasure` instance for its underlying
measure, hence compactly supported functions and the constant function are
integrable. The compact indicator is integrated against the original measure
(not an independently controlled restricted measure), and its standard
indicator-integral identity is exactly the real-valued mass of the compact
set. The measurable-complement identity then converts this to the required
compact-mass-plus-tail formula. Both final inequalities live in `Real`; only
after their metric convergence is established is the result transported back
to `NNReal` masses.

## Verification and progress

The first focused check failed only at local API shape: compact measurability
requires an explicit Hausdorff instance, the complement-splitting theorem uses
the Unicode measure binder, and the final addition inequality needed its order
stated explicitly. After those repairs, the focused check and named module
refresh both passed without warnings. `mass_tendsto_of_cc` and its dedicated
generic assembly machinery are 100% implemented and verified.

The full book no-mass-loss theorem remains 0% implemented. This generic
assembly is only its final measure-theoretic step; chart transport, local
integral convergence, ball capture, and the geometric Gaussian-tail producers
remain separate inputs.
