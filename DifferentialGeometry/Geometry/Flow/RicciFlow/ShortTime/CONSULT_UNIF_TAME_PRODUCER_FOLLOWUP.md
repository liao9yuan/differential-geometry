# Follow-up consult prompt: finish the class-first tame producer design

## Submission

You previously returned `CONTINUE-WITH-CORRECTIONS` and made two useful points:

1. bounded-curvature Ricci-flow existence validates the class-first mathematical
   quantifier order of `(N)`; and
2. a curvature-first proof through Shi/Simon/Cai--Wang would require a genuine
   new bounded-curvature existence theorem in Lean and would not construct the
   fields of `LowRegBoundData` / `IsLowBoundsCap`.

Accept those points as settled for this follow-up.  Do **not** review the truth
of uniform Ricci-flow existence again, and do **not** propose
`unifRmNorm + ricciUnifOfRm` as the answer.  The repository is deliberately
continuing its existing fixed-background low-regularity route because
formalizing a Shi/Simon-level theorem is currently expected to be the larger
new frontier.

The original design request is in:

`DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/CONSULT_UNIF_TAME_PRODUCER.md`.

Your first response did not answer its central questions.  Answer them now.

## Fixed task

Design the smallest honest class-first producer for the **remaining tame face**
of

```lean
lowreg_bounds_unif : exists U, IsLowBoundsCap gBase Lambda U
```

The finite realization face and zero-state face are already packaged:

- `LowRegRealizeData`, `IsLowRealizeUnif`, `exists_lowRealize`;
- `LowRegZeroData`, `IsLowZeroUnif`, `exists_lowZero`, `lowZero_nfun`.

The realization predicate explicitly carries threshold nonnegativity, strict
threshold control, a positive common realization radius, and the uniform
realization theorem.  Do not redesign either completed face.

The remaining producer must choose, before the class metric `g` varies, enough
common upper caps and a positive lower radius floor to obtain the exact
metricwise `hcont`, `Continuous coreN`, and joint three-arm tame certificate
consumed by `IsLowBoundsAt`.  The class assumptions are uniform metric
equivalence to `gBase` and background-covariant metric jets through order three
in dimension three.

A fresh read-only call-graph audit gives this working hypothesis, which you must
confirm or correct from live declarations:

- Candidate C should be sufficient for `unif_solve_of_caps` if the existing
  estimates are monotone under enlarging `top/base/slope` and shrinking
  `outer`;
- the completed H2 realization route uses only the rank-two order-zero
  curvature-action cap, but the H3 top tame arm may additionally require the
  rank-three order-zero cap;
- the likely deeper gaps are class-uniform finite-order H1-to-L6, mixed
  Morrey/Gagliardo--Nirenberg, product, and application estimates used by
  `lower_jet_h1` and the RHS tame theorems;
- lines in the commented historical block of `LowRegRhs0Tame.lean` are not a
  live API and must not be cited as producers.

Do not blindly accept this hypothesis.  Identify the first live call that
requires each alleged rank or Sobolev comparison, or explicitly refute it.

## Mandatory comparison

Referee these three shapes from the original prompt and choose exactly one:

- **A: functional producer.** Choose `rho`, `Ctop`, and functions `B0 B1`
  before `g`, then specialize them after the common realization radius is fixed.
- **B: fixed-radius exact producer.** After fixing the common realization
  package, choose one exact `top/base/slope/outer` packet before `g`.
- **C: cap-oriented producer.** Choose only common `top/base/slope` upper caps
  and a positive `outer` lower floor; each metric retains an exact packet below
  or above those caps/floor.

You must decide whether monotone enlargement of `top/base/slope` and shrinkage
of `outer` make C sufficient for `unif_solve_of_caps`.  If they do, prefer C
unless a lower-layer theorem genuinely requires A.  If they do not, display the
exact failed monotonicity obligation.

## Mandatory repository audit

Trace the constants through the live per-metric chain:

```text
top_path_ball_h1
lower_jet_h1
rem_h1_of_jets
rhs0_h1_tame / rhs0_path_tame
rhs1_h2_tame / rhs1_path_tame
coreN_tame -> coreN_outer -> lowRegN_outer
```

For every existential constant selected after `g` in those declarations, give
this table:

```text
constant | exact source declaration | current dependence on g
         | reusable uniform API already present
         | smallest missing class-first lemma
         | varying-metric jet order consumed
```

Search `DifferentialGeometry/` before declaring an API missing.  Use
`RFreference/` only as reference.  Do not import it.

## Exact output required

Return all of the following; omitting any item is a failed review:

1. `CONTINUE`, `CONTINUE-WITH-CORRECTIONS`, or `STOP-AND-REDESIGN` **for the
   fixed-background tame producer**, not for the abstract existence theorem.
2. The chosen shape A, B, or C, with a short proof that its quantifier order is
   non-circular through
   `P -> Q -> base/slope -> R`.
3. Exact Lean signatures for the recommended data structure, proof predicate,
   and first producer theorem.  Names must be Mathlib-like and at most twenty
   letters.  No field may merely assume the final `htame` under a polished name.
4. The complete constant-dependency and jet-budget table above.
5. The first three implementation bricks, one declaration at a time, including
   canonical file placement and a focused verification/stop condition.
6. The single smallest genuine missing lemma.  Classify it as a routine local
   proof, missing API, substantial design choice, performance wall, or
   mathematical obstruction.
7. Explain how one `Continuous coreN` witness is shared by the tame and
   zero-state packages, and how the explicit `0 <= threshold` field is carried
   into final assembly.

## Hard exclusions

- Do not answer with Shi, Simon, Cai--Wang, or a new bounded-curvature existence
  axiom/theorem.  Those are an acknowledged alternative project, not this task.
- Do not use qualitative compactness to exchange `forall g, exists C` with
  `exists C, forall g`.
- Do not revive the all-rung `lowreg_gate_unif`; its rung-five route exceeds the
  order-three varying-metric jet budget.
- Do not mix in `LowRegBgA2Time`; it is a continuation/Galerkin packet, not a
  field of `IsLowBoundsAt`.
- Do not add a wrapper assumption named `htame`, `hbound`, `hsection`, or
  similar.  The answer must expose the lower analytic producer that proves the
  estimates.
- Do not assume an all-rank curvature-action family.  State the exact tensor
  rank and derivative order of every comparison lemma.
- Keep theorem completion honest: `lowreg_bounds_unif`, `lowreg_dt_unif`, and
  `ricci_flow_unif_existence` remain 0% until their Lean proofs exist.

---- PROMPT ENDS ----
