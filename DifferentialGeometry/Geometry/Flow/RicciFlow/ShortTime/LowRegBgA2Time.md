# LowRegBgA2Time

## Role

This module supplies the complete second-order time packet for the
adjacent-scale low-regularity lift, at an **arbitrary fixed DeTurck background**
`gB` (since ledger №212; it was hardwired to the diagonal `gB = g` before).  Its
coefficient is `LowBaseActionData.C2`, which already contains the full principal
deviation after subtraction of the fixed rough Laplacian.  It must not be added
to the older separate principal family.

## Exports

- `radialA2Bg_pair` (new at №212) gives one positive cutoff cap and one
  nonnegative constant `C`; at every smaller cutoff `r` and every smooth `T`,
  the two actions of `lowCoreDataBg g gB … T` are bounded by `C * r` and form
  the adjacent-scale inclusion square.  Free-cutoff binder shape: `C` is chosen
  BEFORE `r`, which is what makes the radius a usable contraction knob
  downstream.
- `lowA2Bg_small` gives one positive cutoff cap and one nonnegative constant.
  At every smaller cutoff `r`, both completed coefficient maps are continuous,
  compatible, and bounded by `C * r`.  Now `(g, gB)`.
- `hiAffA2Bg` and `loAffA2Bg` freeze the same H2 radial scalar on the H4 and H3
  passenger scales.  **Still diagonal** (`g g`) — deliberately untouched at
  №212, they have no consumer on the lift's critical path.
- `hiAffA2Bg_le` and `loAffA2Bg_le` show that radializing the passenger does not
  enlarge either operator norm.
- `affA2Bg_comm` is the pointwise adjacent-scale commuting square.
- `affA2Bg_data` gives strong measurability and uniform bounds for both time
  families along any a.e. strongly measurable H3 trajectory.

## Proof route

The smooth-core pointwise and two-jet estimate comes from **`c2Bg_h2_small`**
(`LowRegBgC2Small.lean`, ledger №211) — the fixed-background sibling of
`c2_h2_small`, and the only place the background enters this file's estimates.
The high/low action bounds and their core compatibility come from `a2_pair`,
which is background-BLIND: it quantifies over every `A : LowBaseActionData g`
and never mentions a DeTurck background.  The fixed-background completed maps
and their Lipschitz/core read-offs come from `radialA2Bg_lip`, already
two-metric before №212.  Closed-set density transfers the uniform core bounds
to the whole completed H2 state space.  The time packet then uses the existing
measurability of `radialCLM` and its exact commutation with Sobolev inclusion.

## The №212 widening, and what was verified about it

`a2HiBg_total_le`, `a2LoBg_total_le`, `lowA2Bg_small` were widened from `g g` to
`(g gB)`.  The dossier's claim that the two private helpers' proof bodies never
touch the background was **verified declaration by declaration** and holds: both
are a `ccToHsLin_dense` density induction whose only inputs are the theorem's
own `hcont`/`hcore`/`hbd` hypotheses (`isClosed_le` + `DenseRange.induction_on`
+ `rw [← hcore S]`).  Nothing in either body mentions a metric other than `g`,
and neither uses `lowCoreData` (the diagonal bundle) — only `lowCoreDataBg`.
So both are pure token widenings.

`lowA2Bg_small` had **exactly one** genuine diagonal dependence: the call
`c2_h2_small hDim g`.  Everything else it used was already background-free
(`lowRadial_norm`/`_symm`, `a2_pair`) or already two-metric
(`radialA2Bg_lip g gB`).  Replacing that one call is precisely what
`radialA2Bg_pair` packages, so the widened `lowA2Bg_small` body got *shorter*:
the ~40-line inline `hcoreBd` block (radial cut, zero-fibre certificate,
`c2_h2_small` + `a2_pair` plumbing) collapsed to a three-line `obtain` from
`radialA2Bg_pair`.

Consumer census before widening (`rg`, tracked + untracked): `lowA2Bg_small`
had **zero** consumers anywhere; the two private helpers had only each other's
enclosing theorem.  So the widening is churn-free — no call site needed a `g g`
instantiation.

## Lean lessons from this pass

- **Statement-level `let` in a consumed theorem.**  `c2Bg_h2_small` and
  `radialA2Bg_pair` both carry `let A := …` / `let hreal' := …` in their
  conclusions.  `obtain ⟨…⟩ := h …` zeta-reduces through them fine (rcases
  whnfs), but any `have`/`exact` that must *state* the consumed fact needs the
  expected type written out — the `hcoreBd` block does exactly that.
- **Proof irrelevance carries the realization certificate.**  The `hreal'`
  produced inside `radialA2Bg_lip`, inside `radialA2Bg_pair`, and inside
  `lowA2Bg_small` are three *syntactically different* proof terms of the same
  `Prop`.  Nothing has to be transported: `exact` closes across them.  This is
  what makes the three-source assembly (lip + pair + total_le) cheap.
- **No new heartbeat options were needed.**  `radialA2Bg_pair` fits the default
  200000 budget, like its diagonal twin `radialA2_pairR`.  `lowA2Bg_small`
  retains its *pre-existing* `maxHeartbeats 1000000` pair (statement
  elaboration cost, not proof cost); nothing was added.

## Verification

Focused file check GREEN, targeted module build GREEN, no warnings attributable
to this file.  `#print axioms` on `lowA2Bg_small` and `radialA2Bg_pair` reports
only `propext`, `Classical.choice`, `Quot.sound`.  The file contains no `sorry`.

## Frontier and accounting

This module is no longer a frontier: with №212 both of its lift-facing exports
are two-metric and the `IsBgA2At` producer (`bgA2_of_radial`,
`LowRegBgLift.lean`) consumes them directly.

What is NOT done here: `hiAffA2Bg`/`loAffA2Bg`/`affA2Bg_comm`/`affA2Bg_data`
remain diagonal.  Widening them is mechanical (the same token substitution) but
should wait until a consumer needs the fixed-background time families; doing it
speculatively would just churn the file.

`ricci_flow_unif_existence` itself remains **0%** — its endpoint placeholder is
still unproved at `ExtendViaUniqueness.lean:98`.  The A2 dedicated machinery is
~100% after this pass (nothing analytic is left for A2).  The uniform-existence
machinery as a whole is ≈85%; the whole HCG compactness project remains ≈3%.
