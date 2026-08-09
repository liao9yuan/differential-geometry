# LowRegBgLift

## Role

This file is the metricwise certificate layer between class-first scalar data
and orbit realization.

- `BgLiftOps` contains only the completed high/low A1 maps.
- `IsBgA2At` (7 fields) proves the second-order continuity, contraction bounds,
  actual-core identities, and inclusion square.  It takes no `BgLiftOps`
  argument: no A2 field mentions `F`.
- `IsBgA1At` (7 fields) proves the same four kinds of fact for the first-order
  maps carried by `BgLiftOps`.  Its two core fields are stated against the
  REFOLDED bundle `c0CoreData g + oneCoreBg g gB` (ledger №199/№200), and
  `bgA1_of_refold` discharges all seven fields from `refold_aff_bg`.
- `IsBgLiftAt` is now their conjunction (`: Prop extends IsBgA2At …,
  IsBgA1At …`).  All fourteen original field statements are unchanged and stay
  reachable through the parent projections, so no consumer sees the split.
- A2 uses the canonical `lowA2HiBg` and `lowA2LoBg` maps.
- The realization witness at the coefficient radius is derived from
  `IsLowBoundsAt` and `BgLiftData.coeffRadius_le_realize`; it is not an extra
  assumption.

The certificate intentionally does not contain an orbit or temporary
measurability witnesses.

## Verification

Focused verification and targeted module build passed.  `bgA1_of_refold` was
confirmed sorry-free by an axiom probe (three standard axioms only).  The single
downstream consumer `ScratchIdentCensus.lean` also checks green; the missing
`LowRegForceHiBg` olean that blocked it at №198 has since been built.

## The A1 bound contract: what the diagonal actually does (ledger №198)

BG-2 was dispatched to restate `a1Hi_bound`/`a1Lo_bound` from affine to
quadratic, on ledger №197's premise that the diagonal lane consumes a quadratic
`D R·(A+A²)` shape.  Reading the diagonal chain first — as the brick required —
refutes that premise, so the restatement was NOT made and the two fields are
unchanged.  What the diagonal really does:

- The diagonal lift consumer is `lowreg_apply_two` (`LowRegApplyTwo.lean:256`).
  Its first-order hypotheses `hFHiBd`/`hFLoBd` (`:309–312`) are
  `∀ x : tensorHs g 0 2 3, ‖FHi x‖ ≤ Z + L * ‖x‖` — the AFFINE shape, verbatim
  what `IsBgA1At` already has with `Z ↦ D.zero`, `L ↦ D.slope`.
- The horizon algebra is built for exactly that split: `lowregLiftHorizon' c Z`
  (`LowRegLiftSmall.lean:282`) absorbs only the `√T`-carrying constant `Z`,
  while the slope `L` is capped by the separate `T`-free margin
  `6·(2L‖f‖) ≤ (1−c)/2` (`lift_aff_margin`, `:354`).  `BgLiftData.horizon` and
  `BgLiftData.force_margin` mirror these two one for one.
- The affine bound is PROVED in the diagonal, by `refold_aff`
  (`LowRegBgA1Refold.lean:488`), itself the `gB = g` case of the already
  arbitrary-background `refold_aff_bg` (`:345`), assembled from `c0_pack`
  (`LowRegBgC0Time.lean:322`) and `c1_bg_pack` (`LowRegBgC1Time.lean:763`).
- Decisive detail: `refold_aff`'s core identity is against the REFOLDED bundle
  (`c0CoreData … .a1Hi + oneCore … .a1Hi`), not `lowBaseData`/`lowCoreDataBg`.

So №196's scaling witness does not refute the bound SHAPE; it refutes affine
growth *against the un-refolded core* that `a1Hi_core`/`a1Lo_core` pin here.
The open design choice therefore sits in the CORE fields, and the honest mirror
of the diagonal is №196 option (c) (refold the Bg core), not option (a).  That
is cheaper than №197 assumed, because `refold_aff_bg` already exists at
arbitrary background and already discharges bound + core + square for the
refolded split; what is missing is the Bg analogue of `refold_low_split` (whose
C2 fibre bound `κδ/(1−δ)²` is currently diagonal only) — i.e. the same A2 gate
that G1 is blocked on.

`lowA1_act_tame` (`DeTurckRemainderLowBaseAction.lean:11893`) is not evidence
either way: it is private, its only consumer is `remainder_diag_h2` (`:13555`),
consumed in turn by `DeTurckRemainderLowBaseTime.lean:1767` and
`PrincipalResidualH2.lean:186,228` — modules that never import `UnifBgLift`.  It
also bounds the ACTION `a1[T](T)` (one tensor in both slots), which the affine
operator bound implies at `y = x`; it is strictly weaker, not a different
contract.

## Route (c) landed: the refolded core and its producer (ledger №200)

The planner adopted option (c) in №199 and BG-3 executed it.  Two facts made it
a one-file change, both established by reading before editing:

- **`refold_aff_bg` is not a smooth-core-level result.**  Its `FHi`/`FLo` are
  already COMPLETED maps `metricH3 g → (metricH3 g →L metricH2 g)` and
  `metricH3 g → (metricH2 g →L metricH1 g)` — exactly the two `BgLiftOps`
  fields — and it already exports their continuity, the affine bound, the
  smooth-core VALUE identities, and the adjacent-scale square, all at arbitrary
  `g gB`.  Nothing had to be completed, so the planned density-extension mirror
  of `lowA1HiBg`/`lowA1LoBg` was not needed.  (The brick's own hypothesis that
  these existed "only at the smooth-core level" was wrong; the completions are
  in the statement.)
- **`a1_square` needed no restatement.**  It is phrased on the `BgLiftOps` data
  `F`, so supplying the refolded maps makes it the refolded square with no edit.
  Only the two core fields changed, `lowCoreDataBg → c0CoreData + oneCoreBg`.

`bgA1_of_refold` is the producer.  Its shape mirrors the diagonal's
`lowreg_solve_open` (`LowRegApplyTwo.lean:645`), which likewise obtains the
packet before any trajectory and caps its radius against `L`:

    ∃ ρ0 > 0, ∀ D : BgLiftData K, D.coeffRadius ≤ ρ0 →
      ∃ Z L, 0 ≤ Z ∧ 0 ≤ L ∧
        (Z ≤ D.zero → L ≤ D.slope → ∃ F, IsBgA1At g gB K hK D F)

The two domination hypotheses are the honest seam, not a hidden assumption:
`refold_aff_bg` binds `Z`/`L` INSIDE its radius quantifier, so they still depend
on `g`, whereas `BgLiftData.zero`/`slope` are fixed before the class metric
varies.  Closing that seam is the G3/`_unif` lane's job, not this brick's — the
statement exposes it rather than papering over it.

Import note: `LowRegBgA1Refold` was added to this file's imports.  No cycle —
its transitive closure never reaches `UnifBgLift`/`LowRegBgLift`, whose only
importer is the leaf `ScratchIdentCensus.lean`.

## 2026-08-07 — brick B2c′: the core fields REPAIRED (ledger №206)

Route error #2 (ledger №203) was that `IsBgA1At`'s two core fields named the
pair `c0CoreData g`, `oneCoreBg g gB` — a bundle that does NOT reproduce the
arbitrary-background remainder, because the order-zero background correction
`lowCoreDataBg[gB].C0 − lowCoreDataBg[g].C0` is missing from it.  Both fields now
name the single bundle `refoldCoreBg g gB`, which is exactly the bundle
`refold_split_bg` certifies:

```
a1Hi_core : F.a1Hi (ι S) = (refoldCoreBg g gB … S).a1Hi
a1Lo_core : F.a1Lo (ι S) = (refoldCoreBg g gB … S).a1Lo
```

`bgA1_of_refold` is re-proved sorry-free from TWO packets: `refold_aff_bg` for
the first two summands (unchanged, NOT restated — its diagonal consumer chain
`refold_aff` → `lowreg_solve_open` stays byte-untouched) and the new registered
honest input `BgDeltaPack g gB` (`LowRegBgA1Refold.lean`) for the third.  The
maps are the pointwise sums, `ρ0 = min ρ₁ ρ₂`, `Z = Z₁+Z₀`, `L = L₁+L₀`; the two
core fields close by `refoldBg_a1Hi_split` / `refoldBg_a1Lo_split`.

**Honest status: the producer is CONDITIONAL.**  `BgDeltaPack` has no producer
yet — its affine half needs the tame ΔC⁰ layer (bricks B2a `c0Bg_diff_tame` and
B2b `c0bg_pack`, ledger №205).  Until then `IsBgA1At` is *stated correctly and
produced modulo one registered input*, not produced outright.  When B2b lands,
delete `bgA1_of_refold`'s `hΔ` argument and this qualifier.

**Lean lessons.**  (1) `norm_add_le _ _` on a sum of continuous linear maps
fails with a `Type mismatch` between `@instHAdd _ ContinuousLinearMap.add` (what
writing `+` yourself elaborates to) and `SeminormedAddGroup.…toAdd` (what
`norm_add_le` wants).  They are defeq but do not unify at instance transparency.
Cure: `have hsum := norm_add_le (FHi x) (GHi x)` with NO expected type, run the
affine `calc` on `‖FHi x‖ + ‖GHi x‖`, and close with `hsum.trans hx` — `exact`'s
defeq check at default transparency crosses the gap that unification will not.
This is the same workaround `refold_aff_bg` encodes as
`simpa only [FHi] using norm_add_le …`.  (2) `a1_comm` at `refoldCoreBg` does
NOT discharge `a1_square`: `a1_comm` relates one BUNDLE's two completions, so it
lands only at smooth `x = ι S`, whereas `a1_square` relates the two MAPS at an
arbitrary `x`.  The packet must carry its own square clause.  (3) The style
linter rejects `show` used to change a goal up to defeq — use `change`.

Verification passed (focused checks, targeted builds, axiom probes clean).

## 2026-08-07 — brick B2b: the A1 half is UNCONDITIONAL (ledger №208)

`bgA1_of_refold` lost its `(hΔ : BgDeltaPack g gB)` argument; the packet is now
supplied internally by `c0bg_pack` (`LowRegBgA1Refold.lean`, proved there — see
that file's note).  Nothing else in the proof changed: the single line
`obtain ⟨ρ2, hρ2, hdel⟩ := hΔ` became
`obtain ⟨ρ2, hρ2, hdel⟩ := c0bg_pack hDim g gB`.  Every "conditional" /
"registered honest input" qualifier for the A1 half was removed from both
`IsBgA1At`'s and `bgA1_of_refold`'s docstrings; the PDE-honesty paragraph
(`refold_split_bg` reconstructs the arbitrary-background remainder exactly, so
the `deltaCoreBg` summand may not be dropped) is unchanged and still load-bearing.

`bgA1_of_refold` had no Lean consumers outside this file, so the signature
change was free.

**The public API a consumer now uses for the A1 half**: `bgA1_of_refold hDim g
gB hK` → `∃ ρ0 > 0, ∀ D : BgLiftData K, D.coeffRadius ≤ ρ0 → ∃ Z L ≥ 0, (Z ≤
D.zero → L ≤ D.slope → ∃ F, IsBgA1At g gB K hK D F)`.  The two domination
hypotheses are the honest class-uniformity seam, unchanged.

Verification passed (focused checks, targeted builds, axiom probes clean).

## 2026-08-07 — brick R2-s2: the A2 half, and the WHOLE metricwise certificate
## per `(g, gB)` (ledger №212)

Three new declarations here.

**`IsLowBoundsAt.realizeCc`** — the radius-maximal form of the realization
certificate, in the `ccTensorToHs` spelling the coefficient layer wants.  This
had to exist: `radialA2Bg_lip` / `lowA2Bg_small` take `hreal` at a radius `ρ₀`
and *return* a smaller cap `ρ ≤ ρ₀`, so a producer whose output must be
quantified `∀ D : BgLiftData K` needs a `D`-INDEPENDENT radius to start from.
`K.realize` is that radius (`K.realize_pos`; `D.coeffRadius_le_realize` is
exactly the restriction).  `BgLiftData.realize` is now its one-line corollary —
same statement, same public name, proof body deleted.

**`bgA2_of_radial`** — `∃ ρ0 C, 0 < ρ0 ∧ 0 ≤ C ∧ ∀ D : BgLiftData K,
D.coeffRadius ≤ ρ0 → (C * D.coeffRadius ≤ D.contract → IsBgA2At g gB K hK D)`.
Seven fields from two sources: `radialA2Bg_lip` gives the two smooth-core
read-offs against `lowCoreDataBg g gB`; `lowA2Bg_small` (widened to `(g, gB)` at
this same brick) gives the two continuities, the inclusion square, and the two
operator bounds `≤ C * D.coeffRadius`, which meet `D.contract` through the
domination hypothesis.

*The contraction knob is the RADIUS, and the binder order is load-bearing.*
`C` is bound OUTSIDE `∀ D`, so a consumer may pick `D.coeffRadius ≤
min ρ0 (D.contract / C)` after seeing `C`.  Had `C` been produced per-`D`
(mirroring A1's `Z`/`L` literally) the knob would be circular and unusable.
The δ-cap is NOT a knob: `K.threshold ≤ 1/3` is pinned by the realization
certificate and carries no smallness of its own — ledger №210's pre-registered
trap, avoided.  Shrinking the radius is not free either: `BgLiftData` carries
`state_le_radius`, so it forces `K`'s state radius down alongside.

**`bgLift_of_radial`** — the conjunction, `ρ0 := min` of the two radii, built as
`{ toIsBgA2At := …, toIsBgA1At := … }`.  Per `(g, gB)` the fourteen-field
`IsBgLiftAt` is now a theorem, conditional on exactly three scalar dominations:
`Z ≤ D.zero`, `L ≤ D.slope`, `C * D.coeffRadius ≤ D.contract`.

**What this does NOT say.**  `Z`, `L` and `C` are all produced from
`g`-dependent coefficient estimates.  A single `BgLiftData K` serving EVERY
metric of the class still needs class-uniform versions of all three.  That is
the whole content of the remaining G3 lane, and this brick does not touch it.

Verification: focused checks green on both touched files, targeted build of
`…ShortTime.LowRegBgLift` green (10064 jobs, no warnings in the touched files),
axiom probes on `IsLowBoundsAt.realizeCc`, `BgLiftData.realize`,
`bgA2_of_radial`, `bgLift_of_radial` all report only the three standard axioms.

## Remaining frontier

`IsBgA1At` is stated on the CORRECT bundle and `bgA1_of_refold` proves it
sorry-free and unconditionally; `IsBgA2At` likewise via `bgA2_of_radial`, and
the conjunction via `bgLift_of_radial`.  What the CLASS-UNIFORM `IsBgLiftAt`
still needs:

- ~~the ΔC⁰ affine packet producing `BgDeltaPack`~~ — **DONE** (bricks B2a/B2b,
  ledger №207/№208): `c0bg_pack` proves it, so the A1 half is unconditional;
- ~~the A2 half `IsBgA2At`~~ — **DONE** (brick R2-s2, ledger №212):
  `bgA2_of_radial`.  The G1 stop condition never fired; the fixed-background
  smallness input `c2Bg_h2_small` (№211) was the whole missing analytic
  content; and
- ~~the arbitrary-background total-split identity~~ — **DISCHARGED by brick B1**
  (ledger №204): `refold_split_bg` (`LowRegBgA1Refold.lean:493`) is exactly the
  Bg total split, `remainder(S) − remainder(0) = F.a2 S + F.a1 S` for
  `F = refoldCoreBg g gB`.  It is what makes the repaired core fields of §B2c′
  PDE-honest: the lift consumes `a1 + a2` together, and both are now read off
  one bundle that provably reconstructs the remainder.
- the class-uniform coefficient radius (G3), re-scoped at №198 into a ~55-node
  `_unif` lane whose entry node was `invCoeff_h2_lip_unif` (2 nodes done as of
  №209).  **After №212 this is the ONLY thing left**: the three dominations
  `Z ≤ D.zero`, `L ≤ D.slope`, `C * D.coeffRadius ≤ D.contract` are precisely
  the seam that a class-uniform `Z`/`L`/`C` would close, and nothing else in
  `IsBgLiftAt` is open.
