# Codex handoff — finish black box (B) `ricci_flow_forward_unique` (2026-07-26)

You are taking over the FORWARD-UNIQUENESS lane at its final brick.  Work in
`E:\testdifferential-geometry-ste-align` (branch `codex/short-time-existence-align`).
Read `AGENTS.md` first and follow it (lake-locked workflow, multi-agent rules,
reporting rules).  The lane's running source of truth is
`ShortTime/FORWARD_UNIQUE_PLAN.md` — resume from dispatch entries №45–№51, not
from scratch.  Do not re-audit settled stages.

## State (all committed and green through `8a0df5480`)

`Evolution/ForwardUniqueWiring.lean` proves `forward_unique_of_gram`: black box
(B)'s VERBATIM statement from (B)'s own hypotheses plus exactly
`fuSlab_of_gram … hrem hadot` and `energyEdgeCont`.  A scratch handoff example
(re-create it; do not skip) confirms the endpoint discharge is a one-liner once
`hrem`/`hadot` exist.  Everything else — the 16-member input bundle, the
Kotschwar evolution side, the density tower, hedge, 4 of 6 slab fields — is
done, 0-sorry, 3-axiom clean.

## Remaining work (one shared brick + two fields + the discharge)

0. **First: absorb or discard the in-flight executor output.**  An Opus agent
   (Agent-LAST) was still running at handoff time on exactly this brick, in
   `Analysis/Parabolic/RicciLinearization/RicciDifferenceMeanValueWithin.lean`,
   `Evolution/ForwardUniqueSup.lean`, `Evolution/ForwardUniqueWiring.lean`.
   `git status --short` these three: if dirty, audit the diff (0 sorry, hygiene
   grep below, direct-lean 3-axiom on new endpoints, targeted builds) and keep
   only what passes; otherwise `git checkout --` them.  Its report file (if any
   value) is not available to you — judge the code on its own.
1. **Within-tower derivative layer** (`RicciDifferenceMeanValueWithin.lean`,
   additive): `partRiemWithin` mirroring the existing `partChristWithin`, a
   ∇Ric-components corollary, consumer `…SlabContAt` forms on
   `Icc a c ×ˢ univ`.  Check FIRST whether the roughLap(Rm₂) sup can be reached
   via `normSq0S_jointContMDiffOn` + DensReg chart machinery on the
   by-type-smooth field instead of a second derivative layer.
2. **hadot**: `connDiffDot_normSq_le` (`ForwardUniqueConnBound.lean`, 0-sorry)
   instantiation — only `B₁ ≥ sup |∇Ric₂|²` is missing (step 1 +
   `normSqSlabSup`); Λric/Λ/B₃/hΓ/hA routes are recorded in
   `ForwardUniqueSup.md` §adotLe.
3. **hrem (ruling R13, plan №49)**: evaluation identities at the real families
   via `lowOfComp_eval` (`ForwardUniqueSdec.lean:257`) rewriting
   `lowOfComp g₁ b (rmDotRem @real)` and `gapDot g₁ g₂ (uhlRm2Vec @real)` as
   tensorial combinations (precedents `fuP_eq`, `mixLow_eq_rm04`), then
   `reLowerPairSq_le` + product/trace bounds + the sups.
4. **Make `fuSlab` argument-free**, re-check the handoff example, then replace
   the `sorry` of `ricci_flow_forward_unique`
   (`Evolution/ExtendViaUniqueness.lean`, currently `:215`) with the
   `forward_unique_of_gram` application.  The theorem STATEMENT must not change
   (audited black-box interface; MaximalTime consumes it).  Do NOT touch the
   other sorry (`:97`, box (N) — another lane).  Verify
   `#print axioms ricci_flow_forward_unique = [propext, Classical.choice,
   Quot.sound]` — the proof must NOT pass through (N).
5. **Full `./scripts/lake-locked.ps1 build`**: green, and the whole-tree sorry
   inventory = the №32 baseline MINUS ForwardUniqueConnBound MINUS the (B)
   sorry.  Then commit (small commits per brick; end messages with the
   Co-Authored-By line your tooling uses) and update
   `FORWARD_UNIQUE_PLAN.md` + the same-name `.md`s as you go.  Push is left to
   the user.

## Verification standards (planner-grade; do not lower)

- Hygiene grep on every touched Lean file:
  `grep -nE "^(@\[[^]]*\] *)?(noncomputable |private |protected |scoped |local |unsafe )*(axiom|instance|notation|opaque|macro|elab|syntax)\b"`
  (the 4 borel `private local instance` in DensReg/Energy are precedented).
- Axiom audit by DIRECT lean, never `lake env lean` (false-green history):
  toolchain `c:/Users/liao9/.elan/toolchains/leanprover--lean4---v4.29.0/bin/lean.exe`,
  `LEAN_PATH` = every `.lake/packages/*/.lake/build/lib/lean` +
  `E:\testdifferential-geometry-ste-align\.lake\build\lib\lean`, scratch probe
  OUTSIDE the repo.
- Warning-cleanliness is certified only by targeted `build`, not by `check`.
- Verify sorry claims against CODE, not `.md` history (a stale claim burned one
  pass).  Counterexample-first audit for any NEW pointwise estimate statement:
  collapse all difference carriers and check the hypotheses force LHS = 0.
- Grep-before-wall both directions: producer surface (`can*` family,
  `<object>*_smooth`, private decls) before declaring anything missing;
  predicate-shape match before declaring anything present.

## Known traps (all recorded in the lane `.md`s; the expensive ones)

- Never `rw` on `Tensor0SSpace` FunLike coercions (term-form
  `Tensor0SSpace.sub_apply`, `DFunLike.ext`); type ascriptions do NOT force
  elaboration — use thin typed wrapper `def`s.
- Never close a large-defeq match with `exact` (360 s KERNEL timeout);
  `simpa only [small defs] using h`.
- `n+k` vs literal: defeq for `exact`, fails for `rw`/`simp only`; house form
  of the derivative rank is `s+2+1`.
- `nlinarith` away from tensor atoms; explicit `mul_le_mul_of_nonneg_*` chains.
- IPS vs NormedSpace `SolutionOn` spines do not mix — file-level splits
  (`Rm04ProducerTail`, `TailChristoffel` precedents).
- `MovingEdgeEnergy.lean` has NO olean (does not compile) — reference text
  only, never import.  `first_var_joint` is IsOpen-gated — unusable at the
  edge; `integral_family_cont` is the moving-measure DCT.
- PowerShell 5.1 `Out-File utf8` writes a BOM lean rejects — write probes with
  a BOM-free tool.
- Foreign dirty files (other sessions): `HCGCompactness/ConnDiffDeriv2Bound.lean`,
  `Analysis/Sobolev/TensorHilbert/DeTurckVFJetRadiusFree.lean`,
  `HamiltonPositiveRicciAdapter.md` — never touch.  Never `lake clean`/
  `lake update`; never kill foreign `lean.exe` (wait-poll).

## Honest denominators (keep reporting this way)

`ricci_flow_forward_unique` is 0% until its sorry is gone; its machinery is
~90%.  (B) is one black box of the extension chain; (N) (`:97`) is another
lane's 0%.  The whole HCG-compactness program is ~10%.  When you finish (B),
say exactly that — do not let it read as more.
