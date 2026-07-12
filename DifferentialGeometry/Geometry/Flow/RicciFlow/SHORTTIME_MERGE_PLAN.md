# SHORT-TIME-EXISTENCE MERGE + FORWARD PLAN (uniqueness, `extends_of_rmBounded`)

2026-07-11.  Written at the decision to merge `qinz1yang/differential-geometry`
branch `short-time-existence` (fetched as remote `qinz`/`upstream`) into ours.
All facts below were verified against the fetched ref, not the GitHub UI.

## §0 What the fork proved (verified from the ref)

**Headline** `ricci_flow_short_time_existence`
(`Geometry/Flow/RicciFlow/ShortTimeExistence.lean`, their HEAD `9c01f29f`):
for a compact boundaryless `M` with smooth metric `g₀`: `∃ T > 0` and a family
`g_fam : ℝ → SmoothRiemannianMetric I M` with
- `g_fam 0 = g₀`;
- chart-Gram entries jointly `C^∞` on `Ico 0 T ×ˢ (chart baseSet)` — i.e.
  **joint smoothness up to and including `t = 0`** (strengthened form, their
  commit `d8782e10`);
- the Ricci-flow equation `∂ₜ g = −2 Ric` as `HasDerivWithinAt … (Ici 0) t` for
  every `t ∈ Ico 0 T` (one-sided at `0` included).

Proof spine: DeTurck gauge (`deTurckRicci_solution_with_jointReg`) → chart
regularity → conjugating-flow de-gauging (Seeley time extension of the DeTurck
vector-field flows, joint smoothness on an open interval ⊇ the closed window).
Axiom audit is baked at the declaration site (their `9d30f5ce`):
`[propext, Classical.choice, Quot.sound]`, and their HEAD claims the full
library builds green with the only remaining sorries being two deliberate de
Rham sorries in `Tensor/Exterior`.  Their engine inventory (all new since the
merge-base): quasilinear parabolic maximal-regularity, Galerkin/Picard +
per-mode Duhamel limits, Nemytskii operators on Sobolev scales, correction-field
envelope towers, a vendored De Giorgi–Nash–Moser development, ODE-flow
`C^k`/variational regularity, Seeley extension.

**What the fork does NOT have:** Ricci-flow-level **uniqueness** (only ODE-flow
uniqueness); any blow-up/extension criterion; our post-base geometry (their
HEAD `9c01f29f` in fact *deleted* their stale unfinished copies of Hopf–Rinow /
exp-smoothness / minimizing-geodesic developments — the proven versions live on
OUR branch).  Their README's new work-in-progress target is Hamilton 1982
(= our `ham3_main`): the two forks have converged on the same program.

## §1 Merge geometry (verified numbers)

- merge-base `987a57b4`; ours `e5d37bce` = **237 commits / 986 files** ahead;
  theirs `9c01f29f` = **1244 commits / 1557 files** ahead.
- **Both-modified files: 106** (the conflict surface).  Mostly: the root
  aggregate `DifferentialGeometry.lean`, `Analysis/Calculus/SmoothExtension/*`
  (both sides extended Seeley/Borel), `Analysis/ODE/Flow/*`, a few
  `ConnectionLaplacian`/`Green` files.
- **Delete(theirs)/modify(ours) conflicts: 15** incl.
  `Comparison/BonnetMyers/Headlines.lean` and the old `ShortTime/*` cluster.
- They touched **28 files under our `Geometry/Comparison`/`HCGCompactness`**
  (all base-era shared files: `GeodesicConvexity`, `EndpointContinuation`,
  `BonnetMyers/*`, `ChartVelocityConvergence`…), where our branch is far ahead.
- Their comment-strip commit makes textual conflicts likely wherever both sides
  touched a file, even when semantically compatible.

## §2 Merge strategy (M-track)

- **M0 (before merging anything):** commit our working tree (weeks of verified
  work are still uncommitted), and record baseline `lake build` green on both
  sides (theirs claims green at `9c01f29f`; ours per `PROJECT_MAP.md` §7).
- **M1 resolution policy — by lane ownership:**
  - THEIRS wins: `Analysis/{Parabolic,Spectral,PDE}`-side, `Analysis/ODE/*`,
    `ShortTimeFlow/*`, `ShortTimeExistence.lean`, the vendored DGNM tree, and
    their deletions *inside their own ShortTime cluster* (the old base-era
    files; our edits there were maintenance, not content — audit each of the
    15 delete/modify cases, expected resolution: accept deletion for their-lane
    files, keep ours for `Comparison/BonnetMyers/Headlines.lean`).
  - OURS wins: `Geometry/Comparison/*` (post-base rewrites: Hopf–Rinow chain,
    exp smoothness, CenterOfMass, HalfSqDistGrad…), `HCGCompactness/*` (whole
    tree), `Geometry/Topology/*` (DirectLimit*), `Geometry/Exponential/*`,
    `Evolution/*`, `Coordinates/LocalDiffeoIFT`.
  - REGENERATE: the root `DifferentialGeometry.lean` aggregate = union of both
    leaf-module lists (theirs was regenerated to ~1600 modules; ours added the
    HCG/C4/Topology modules).
  - Comment-strip noise: accept their stripped text in their lane; do NOT
    mass-restore docstrings there (cost accepted); our lane keeps our
    docstring conventions.
- **M2:** post-merge full `lake build`; re-run the axiom audit on BOTH
  headlines (`ricci_flow_short_time_existence`; our endpoint chain per
  `PROJECT_MAP.md` §7) — the false-green lesson applies doubly after a merge.
- **M3:** update `PROJECT_MAP.md` (§2 add the short-time endpoint as DONE-lane,
  §3 add the U/E lanes below), `CODEX_HANDOFF.md`, and `HAM3_BLACKBOX_PLAN.md`
  (frontier 1 = short-time: DONE by the merge).

## §3 Forward plan A — U-track: Ricci-flow forward uniqueness

Target = discharge **black box (B)** `ricci_flow_forward_unique`
(`Evolution/ExtendViaUniqueness.lean` ~L165): forward uniqueness of smooth
Ricci flows on closed `M` with the joint-regularity hypotheses (GSM77 Ch. 7
§5.2 route).  Keep the STATEMENT exactly as the consumer already cites it.

- **U1 — Ricci–DeTurck uniqueness** (the parabolic half).  First AUDIT their
  fixed-point layer: a Banach/Galerkin contraction usually yields
  uniqueness-in-the-ball for free — check whether
  `deTurckRicci_solution_with_jointReg`'s underlying operator has an
  extractable "any two solutions with the same data agree on a short window"
  clause; if yes, U1 is extraction + a continuation argument (cover `[0,T)` by
  short windows), not new analysis.  Fallback route: energy/Gronwall on the
  difference of two Ricci–DeTurck solutions (linearize; their maximal-regularity
  + Gronwall machinery suffices; no new estimates beyond what existence used).
- **U2 — de-gauging uniqueness** (the ODE half).  Two Ricci flows with equal
  initial data DeTurck-ize (harmonic-map heat flow = their conjugating-flow
  layer) to two Ricci–DeTurck solutions with equal data ⟹ equal by U1; the
  conjugating diffeomorphisms then solve the same time-dependent ODE with the
  same initial value ⟹ equal by their ODE-flow uniqueness; undo the gauge.
  All three ingredients exist in their tree post-merge; the work is the
  manifold-level bookkeeping (same shape as their existing de-gauging proof,
  run in reverse).
- **U3 — assemble** `ricci_flow_forward_unique` and DELETE the black-box status
  (per the discharge rule: replace downstream citations, no wrapper left).
- Sequencing: U1-audit is the first session (cheap, decides the route).  U-track
  is independent of the E-track's E1 and can run in parallel post-merge.

## §4 Forward plan B — E-track: `extends_of_rmBounded`

Goal: the extension theorem (|Rm| bounded on `[0,ω)` ⟹ the flow extends past
`ω`) — our `Evolution/` lane, ham3 frontiers 2–3.  The faithful decomposition
already in `ExtendViaUniqueness.lean`:

- **E1 — discharge black box (N)** `ricci_flow_unif_existence` (the ONE sorry
  in that file, ~L92).  Statement = **uniform** short-time existence: for fixed
  `gBase` there is a chart family `S`; for every `Λ ≥ 1` a uniform
  `τ₀(gBase, Λ, S) > 0` such that every `Λ`-comparable `g₀` with order-`≤3`
  chart-Gram bounds flows for time `≥ τ₀`.  **The fork's headline is per-metric
  (`∃T` for each `g₀`) — NOT directly sufficient.**  But their DeTurck
  fixed-point existence time depends only on ellipticity + data bounds, so the
  uniform version is extractable from their ENGINE: re-run
  `deTurckRicci_solution_with_jointReg`'s construction with the
  `(Λ, S)`-uniform hypotheses threaded through the contraction radius/time
  choice, or strengthen their headline to a `τ₀(Λ)`-quantified variant in
  their lane.  This is the main post-merge engineering item of the E-track;
  audit their proof's time-choice locus first (where `T_DT` is fixed) —
  that single lemma's hypotheses tell us the exact uniform-data form.
- **E2 — the restart wiring** `ricci_flow_interior_restart` (provable from
  (N); the route is already written in its docstring: choose `t_star` with
  `ω < t_star + τ₀`, apply (N) at `g₀ := g_fam t_star`).  Its two tail-bound
  hypotheses (`hell` uniform ellipticity, `hC3` chart-Gram C³ tail bounds) come
  from `|Rm| ≤ C` via Gronwall metric-equivalence + Shi (our Lemma-3.11/BBS
  machinery — Gate-L `C^∞`-up-to-`ω` is the remaining producer on OUR side).
- **E3 — glue** the restarted flow to the original by U-track uniqueness on the
  overlap `[t_star, ω)` (the seam-dissolving step the file is named for), then
  assemble `extends_of_rmBounded`.
- **E4 — consumers:** `MaximalTime` (one call-site), the hglue Gate-R (their
  DeTurck closed-endpoint work supersedes it — audit and retire), ham3
  frontiers 2–3, and the `MetricFamilySmoothOn ⊤→∞` cascade (currently HELD —
  re-audit after the merge since their lane reworked the smoothness plumbing).
  NOTE: 3.9/3.10's `hShi` remains a CITED hypothesis — `extends_of_rmBounded`
  does not reopen it.

## §5 Risks / open questions

1. The per-metric→uniform gap in E1 is the only place the fork's result does
   not directly plug into our consumer — if their time-choice locus is deeply
   entangled, the fallback is to state the uniform variant in their lane and
   re-run their construction (mechanical but long).
2. Merge scale: 106 both-modified + 15 delete/modify + comment-strip noise;
   budget a dedicated merge session with the M1 policy table in hand, and
   expect the root-aggregate regeneration to be the last step before M2.
3. Their tree retains two de Rham sorries (`Tensor/Exterior`) — confirm they
   are off both headline closures post-merge.
4. Program-level: both forks now target Hamilton 1982; after M3, ham3
   frontier 1 is DONE (their short-time), frontiers 2–3 are the E-track, and
   the HCG lanes (PROJECT_MAP) continue unchanged as `ham3_cgh_limit`'s
   producer.
