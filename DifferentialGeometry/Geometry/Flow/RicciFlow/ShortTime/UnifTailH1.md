# UnifTailH1

## Source state

`tail_h1_unif` is source-written as a dimension-three class-first affine
`H1` cap for the cancellation-preserving `DLb + lieCorr0` tail. It combines
the five existing uniform leaves through `tail_h1_parts`; the output functions
are selected before the class metric, and the class consumes metric jets only
through order three.

The final comparison uses the explicit five-term inequality
`sum5_sq_le_sq`. The resulting affine cap is intentionally coarse: its base
and slope are five times the sums of the corresponding leaf coefficients.

## RHS endpoint boundary

No `rhs0_h1_unif` theorem is stated here. The existing `rhs0_h1_of_aux`
selects its Ricci and `DLa` functions only after `g₀` is fixed, via the
single-metric `ricci0_h1` and `dla_h1` producers. Its quantifier order therefore
cannot produce a class-first RHS cap from the five tail leaves alone. Closing
that endpoint requires the separate class-first `ricci0_h1_unif` and
`dla_h1_unif` producers, or a new honest uniform auxiliary assembly using them;
this file does not add a wrapper assumption or a `sorry` for that missing step.

## Verification and project status

Source was written on 2026-08-06 without running Lean, Lake, or LSP. Until a
focused check passes, `tail_h1_unif` is unverified source and the theorem is not
counted complete; its dedicated five-leaf assembly is approximately 90% done.
The class-first RHS endpoint and joint tame producer remain 0%, as do
`lowreg_bounds_unif`, `lowreg_dt_unif`, and `ricci_flow_unif_existence`. The
whole HCG theorem closure remains approximately 3%.

## 2026-08-06 verification closure

`tail_h1_unif` is now focused-green, directly exported, and axiom-audited with
only `propext`, `Classical.choice`, and `Quot.sound`.  The first check exposed
only missing namespace openings; adding the same realization, coefficient, and
class-bound namespaces used by the five leaves closed the file without changing
the theorem or constants.

The theorem and its five-leaf assembly are therefore 100% complete.  The next
class-first endpoint is the direct Ricci/DLa/tail assembly for `rhs0_h1_unif`;
the final low-bound packet and uniform-existence endpoint remain separate 0%
theorems.  Dedicated uniform-existence machinery remains approximately 99%,
and the whole HCG closure remains approximately 3%.
