# Consult prompt: redesign the Route-(c) absorption gate under a C3 metric class

Please audit the RicciFlower short-time-existence branch
`codex/short-time-existence-align`.  Use the exact commit supplied with this
prompt; the declarations named below may currently be local-only, so do not
claim to have inspected them unless they are visible in that commit or pasted
as an attachment.

## Target theorem and non-negotiable quantifiers

The target is the existing three-dimensional class-first theorem
`ricci_flow_unif_existence`.  Its class controls uniform metric equivalence to
one fixed `gBase` and background-covariant metric jets only through order three.
The common time and every scalar that restricts that time must be chosen before
the class metric `g` varies.  Do not strengthen the theorem to four metric jets,
do not choose a threshold/radius/time after seeing `g`, and do not use a
qualitative compactness argument without a formal class-first producer.

## What is now proved

The metricwise fixed-background direct-smoothing chain is complete and checked:

```text
IsAdaptedLowSolveBg
  -> lowreg_loMassBg
  -> bg_packet_of_adapt
  -> BgSmoothPacket
  -> existing jointly-smooth DeTurck endpoint
  -> existing Ricci gauge removal
```

Relevant new modules are:

- `LowRegBgRungThree.lean`, `LowRegBgRungFour.lean`,
  `LowRegBgRungFive.lean`;
- `LowRegBgRungPack.lean`, `LowRegBgAdaptedSolve.lean`;
- `LowRegBgGalerkinIdent.lean`, `LowRegBgFatouIdent.lean`,
  `LowRegBgRungClosure.lean`, `LowRegBgHigherRung.lean`,
  `LowRegBgAllMass.lean`;
- `LowRegBgBootstrap.lean`, theorem `bg_packet_of_adapt`.

This conditional chain is not the frontier.  The missing theorem is a
class-first producer of an adapted certificate.

## The stop condition that fired

The current metricwise `IsLowGateOrdBg` stores common envelopes `A,B` and the
adapted budget requires

```text
A * (threshold / (1 - threshold)^2)
  + B * lowregStateRad(top, slope, outer, realize)
  + epsilon < 1.
```

At rung three, the present radius coefficient has the declaration chain

```text
Kr1
  -> Kb1 1
  -> c1JetTowerQBg: Kc 3
  -> low1Ker_jet_bg
  -> low1AtgwBg
  -> bgCcAtgw
  -> fixCdAtgw 3
  -> nabla^3 (connDiff g gBase).
```

Because `connDiff g gBase` already contains one derivative of `g`, this reads
the fourth metric jet of the varying metric.  Rung four reads `Kc 4` and a
`galRepJet_le` bridge at order five; rung five reads `Kc 5` and the order-six
bridge.  These constants are actually consumed by `lowregRung5PathAtBg` in the
three absorption inequalities; they are not unused certificate fields.

The conformal family

```text
g_n = exp(2 f_n) gBase,
f_n = n^(-3) sin(n x_1)
```

keeps the permitted C3 data bounded while the fourth metric derivative is
unbounded.  Thus the current `IsLowGateOrdBg` cannot simply be uniformized.
Shrinking `T` does not help because the displayed budget contains no `T`.

## Requested audit/design

Give a verdict `CONTINUE-WITH-CORRECTIONS` or `STOP-AND-REDESIGN`, and answer:

1. Can the energy estimates be reorganized so the genuinely absorptive
   coefficient depends only on the elliptic principal part/fibre smallness and
   at most three metric jets, while the fixed-offset and higher-jet factors enter
   only metricwise Gronwall coefficients?
2. Identify the first exact inequality in Rung 3 where `fixCdAtgw 3` is placed in
   `Kr1 * stateRad`.  State the sharper replacement inequality and its Lean-level
   hypotheses/conclusion.
3. Perform the same audit for the `galRepJet_le` order-five/order-six factors in
   Rungs 4 and 5.  Which factors truly multiply the top energy and which can be
   treated as lower-order source/Gronwall terms?
4. Propose the smallest honest replacement package, tentatively
   `IsBgAbsGate`, containing only class-first small coefficients, while leaving
   metricwise continuation constants outside it.
5. Give the dependency-ordered Lean producers needed before one may state
   `lowreg_adapt_unif`.  Include an explicit stop condition for any remaining
   reader of the fourth jet of varying `g`.
6. Audit whether the high-order smoothing may instead start at positive times
   and pass to the one-sided endpoint without requiring a common all-order gate
   on the closed slab.  If so, give the exact replacement of the current
   all-rung/Fatou path and explain how endpoint smoothness at `t = 0` is retained.

Do not recommend the already rejected adjacent-scale `liftHiN` route unless you
show a new theorem that avoids its class-first H4 obstruction.  Do not treat the
proved metricwise wrappers as progress on the missing class-first producer.

## Required handoff format

End with:

- verdict;
- exact first theorem to implement (Lean-style signature);
- canonical file;
- existing lemmas to consume;
- whether it is a routine adapter, a new analytic estimate, or a substantial
  design change;
- what result would force abandonment of Route (c).
