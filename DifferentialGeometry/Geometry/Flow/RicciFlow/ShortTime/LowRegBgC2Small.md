# LowRegBgC2Small.lean — the fixed-background `C2` smallness

Created 2026-08-07 by brick **R2-s1 item 2** (ledger `UNIF_EXISTENCE_PLAN7.md`
entries 210 → 211).  Status: **landed sorry-free, axiom-clean**, no
`maxHeartbeats`, 397 lines.

## What it provides

```
c2Bg_h2_small (hDim : finrank ℝ E = 3) (g gB : SmoothRiemannianMetric I M) :
  ∃ ρ C, 0 < ρ ∧ 0 ≤ C ∧ ∀ T (hT : symmetric) {δ} (hδ_le : δ ≤ 1/3) (hδ0 : 0 ≤ δ)
    (hδ : gFibreOpBound g (ccTensorBilinSymm g T) δ)
    (hδZ : gFibreOpBound g (ccTensorBilinSymm g 0) δ) {R}, 0 ≤ R → R ≤ ρ →
    ‖ccTensorToHs g 2 2 T‖ ≤ R →
    let A := lowBaseData g gB T (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ
    (∀ x, riemannianFiberNormSq g 4 2 x (A.C2.toSection x) ≤ (C*R)^2) ∧
      lowJetSq g 2 A.C2 ≤ (C*R)^2
```

This is `c2_h2_small` (`DeTurckRemainderLowBaseAction.lean:13267`) with the
diagonal `lowBaseData g g T` replaced by `lowBaseData g gB T`.  The binders are
mirrored exactly — including the statement-level `let A := …`, so consumers
must ascribe the expected type when they `have` an instance of it, exactly as
they already do for `c2_h2_small`.

**Certificate audit (asked for by the dispatch).**  `lowBaseData g gB T hδ_lt
hδ hδZ` demands `hδ`/`hδZ` **at `g` alone** — they are `gFibreOpBound g …`
bounds on the state and on the zero state, and `gB` is a bare parameter that
never appears in a hypothesis.  So the fixed-background statement needs *no*
extra δ-certificate at `gB`, and none was added.  Same for `phi_dev_h2`, whose
`g_bg` is likewise free.

## The route (the A2 dossier's, confirmed exactly)

`topKernel_eq` (`LowBaseAction.lean:3768`, public, two-metric) splits the
complete top path integrand at background `gb` as

```
rhsRefoldTop g gb T s + rhsSelfTop g T s − Φmet(g,gb,g)
  = lieRefold2 g T s + (Φmet(g,gb,gm) − Φmet(g,gb,g)) + (−2s) • ricciTop g gm T
```

with `gm = realizedFam g T 0 hδ hδZ s`.  The first and third summands do **not
mention `gb`**, so in the difference of the two integrands (at `gB` and at `g`)
they cancel identically — `kerBgDiff` is the whole content, and its proof is two
`rw [show … = _ from topKernel_eq …]` plus `abel`.  **No residual term beyond
the deviations survives**; the dossier's claim is confirmed, the corresponding
STOP condition did not fire.

The surviving deviation is bounded at each background by `phi_dev_h2`
(`LowRegPathSplit.lean:469`, public, two-metric, `g₀ g_bg` both free).  Its
conclusion **does** cover both clauses — a fibre-pointwise `≤ (C·R)²` and a
`∑ i ∈ Finset.range 3` jet bound, which is `lowJetSq g 2` after
`simp only [lowJetSq, Nat.reduceAdd]`.  Second STOP condition did not fire.

Assembly:

| step | lemma |
| --- | --- |
| `C2` at any background = ONE path integral | `c2BgPath` = `c2_eq` + `path_add_sub_eq` |
| difference of the two = ONE path integral | `path_sub_eq` |
| integrand cancels down to `Dev_gB − Dev_g` | `kerBgDiff` (`topKernel_eq` ×2 + `abel`) |
| that difference is small, both clauses | `devBgCap` = `phi_dev_h2` ×2 + `riemannianFiberNormSq_sub_le` / `jetSub` |
| both clauses pass through the integral | `pathBoth` = `riemannianFiberNormSq_pathIntegralCoeffField_le_sq` + `path_jetL2_le` |
| diagonal + difference | triangle: `riemannianFiberNormSq_add_le` / `opJetAdd` |

Constants: `Cd := 2(C₁+C₂)` for the difference, `C := 2(Cd+C₀)` overall,
`ρ := min ρ₀ ρd`.  Every combination step is `linarith` against one
pre-proved `nlinarith` scalar inequality (`2a² + 2b² ≤ (2(a+b))²`); no `nlinarith`
is ever asked to see a `riemannianFiberNormSq` atom.

## Why the *difference* route and not the direct one

The direct route — rerun `c2_h2_small`'s own proof at `g_bg := gB` — is
mathematically identical (only the `phi_dev_h2 hDim g g` call changes to
`hDim g gB`), but it is **blocked**: `lieRefold2_h2` (`:9493`), `ricciTop_h2`
(`:9656`), `path_add_sub_h2` (`:2889`), `jet2_fiber` (`:2958`), `jet_add`
(`:3959`) and `arm_const` (`:1739`) are all `private` in the read-only monolith.
That is precisely the R1 gate entry 210 called moot.  The difference route needs
only public API, which is why it is cheap.

## Reuse sweep (exhibit discipline — nothing new was written that existed)

| needed | found, public, reused |
| --- | --- |
| `lowJetSq (X − Y) ≤ 2(…)` | `jetSub`, `LowRegOpJetWindows.lean:124` |
| `lowJetSq (X + Y) ≤ 2(…)` | `opJetAdd`, `LowRegOpJetWindows.lean:170` |
| fibre 2-subadditivity, both signs | `riemannianFiberNormSq_add_le` / `_sub_le`, `CovGradRoughLap/FiberNormSubadditivity.lean:112,141` |
| jet bound through a path integral | `path_jetL2_le`, `ParametricJetIntegral.lean:331` |
| fibre bound through a path integral | `riemannianFiberNormSq_pathIntegralCoeffField_le_sq`, `PathIntegralFibreNormTransfer.lean:164` |

Only `path_sub_eq` / `path_add_sub_eq` / `armConst` (item 1, in
`LowRegC2JetTower.lean`) had to be created, and those were extractions of an
already-written inline proof, not new mathematics.

## Home

`ShortTime/` rather than `Analysis/…/DeTurck/`, matching the whole existing
`LowRegBg*` family (24 files) — `LowRegBgH2.lean` holds the sibling
`c0Bg_diff_tame` and likewise imports the DeTurck tree directly.  One import
(`…DeTurck.LowRegC2JetTower`) covers everything; nothing forces a monolith
re-elaboration.

## Lean lessons from this pass

1. **Do not leave the integrand as `_` when feeding a
   `linearizedRicciThreeArmHjoint` proof to a lemma that wants raw
   `ContMDiffOn`.**  The definitional unfolding cannot proceed through an
   unassigned metavariable, and the error surfaces as a bare "Application type
   mismatch" on the *hypothesis*.  Fix: give the family a name — here the tiny
   private `pathBoth`, whose `D` is an fvar, so both `path_jetL2_le` and
   `jointContMDiff_toModel_continuous_slice` unify instantly.  This also made
   the proof shorter than spelling the six-line lambda at three call sites.
2. **`simp only [SmoothCcTensor.toSection_sub, …]` must hit every hypothesis
   that shares an atom with the goal.**  Simping `hsub ⊢` but not `hB hG` split
   `(A − B).toSection x` on one side and not the other; `nlinarith` then failed
   with a goal that looked provable.  The failure mode is silent — it reads like
   a missing arithmetic hint.
3. **Prefer `linarith [triangle, boundA, boundB, scalarKey]` over one big
   `nlinarith`.**  Proving `2(C₁R)² + 2(C₂R)² ≤ (2(C₁+C₂)R)²` separately, then
   closing linearly, is both faster and immune to lesson 2's atom mismatch.
4. **Heartbeats are a *splitting* signal, not a `set_option` signal.**  The
   one-declaration version needed `maxHeartbeats 1600000`; after factoring
   `c2BgPath`, `devBgCap` and `pathBoth` out, every declaration fits the default
   200000 with room to spare.  Note `c2_h2_small` itself runs at the default,
   which was the hint that the monolithic version was carrying avoidable cost.
5. `linter.unusedVariables` fires on a **named binder inside a `∃ … ∀ …`
   statement** whose name does not occur in the conclusion, even when the proof
   uses it.  `phi_dev_h2` solves this with `_hδ_lt`; `devBgCap` now does too.

## Verification

Focused check green on both touched files; targeted builds green for
`…DeTurck.LowRegC2JetTower` and `…ShortTime.LowRegBgC2Small`.  Axiom probes for
`path_sub_eq`, `path_add_sub_eq`, `path_add_sub_jet`, `armConst`, `kerBgDiff`
and `c2Bg_h2_small` all report the three standard axioms only.

## R2-s2 — DONE (ledger №212)

`c2Bg_h2_small`'s sole consumer is **`radialA2Bg_pair`**
(`LowRegBgA2Time.lean`), which feeds the background-blind `a2_pair` at
`A := lowCoreDataBg g gB … T`; from there `lowA2Bg_small` → `bgA2_of_radial`
(`LowRegBgLift.lean`) → `IsBgA2At`, and `bgLift_of_radial` composes with
`bgA1_of_refold` for the whole per-`(g, gB)` `IsBgLiftAt`.

Both constraints this file pre-registered were real and were handled as stated:
(i) the `let A := …` needed the expected type written out in the consuming
`have`; (ii) the contraction knob is the **radius**, and additionally `C` had to
be bound OUTSIDE `∀ D : BgLiftData K` in `bgA2_of_radial`, or the domination
`C * D.coeffRadius ≤ D.contract` would be circular.  The δ-cap was never used.

What remains class-uniformly: a `_unif` version of this file's `C` (and of
`a2_pair`'s completion constant) — one new node on the G3 lane.
