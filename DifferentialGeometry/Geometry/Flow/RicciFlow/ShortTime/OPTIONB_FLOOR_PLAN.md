# OPTION (b) — lowering the floor horizon off `staticForce … 2`

Design recon for USER DECISION No. 99, ratified as option (b) in planner update
No. 105 (`UNIF_EXISTENCE_PLAN3.md:426`).  Read-only pass; no Lean edited.
Target: make the class-uniform `τ₀` free of `‖staticForce g₀ g₀ 2‖` (4 metric
derivatives) without touching (N)'s statement (`ExtendViaUniqueness.lean:80`,
budget `∀ a ≤ 3` at `:85`).

## 0. Headline

**The floor does not need re-deriving at a lower order.  It needs deleting.**

The engine's floor hypothesis exists only to make the trajectory's `H²` state
uniformly small.  The realized package `IsRealizedTwo` ALREADY carries that
smallness as a separate conjunct — the solver's own a.e. state ball
`∀ᵐ t, ‖u.lo.toFun t‖ ≤ R` at exactly the `H²` scale the engine measures — and
`R` is a *radius the solver chooses*, capped for free.  The `√T‖fHi‖ ≤ Kf`
floor is a second, redundant route to the same smallness, and it is the only one
that passes through `staticForce` at order 2.

So option (b) is executed by **relocating the smallness from the horizon to the
radius**: cap `P`, delete `lowregFloorHorizon`.  No new estimate, no
interpolation, no `H¹→H²` lifting.  This is stocked-wall instance **sixteen**.

## 1. The chain as it stands, measured

`LowRegApplyTwo.lean:228-231`:

```lean
def lowregFloorHorizon (g : SmoothRiemannianMetric I M) (c Kf : ℝ) : ℝ :=
  Kf * (1 - c) /
    (4 * (‖staticForce (I := I) (M := M) g g (2 : ℝ)‖ + 1))
```

It is folded into the reported `T₀` by `lowreg_solve_two` (`:820`), discharges
the `IsRealizedTwo` conjunct `Real.sqrt T * ‖fHi‖ ≤ Kf` (`:219`) via the Neumann
bound `norm_fix_le` (`:282`) against `norm_liftForceHi_le`
(`LowRegLiftNTerm.lean:259`), and is consumed at exactly one place:
`LowRegAllOrderJet.lean:1645-1660`, where `‖u.deriv‖ ≤ 2‖fHi‖` turns it into the
engine's `hfloor`.  `lowreg_joint_two` (`:1682-1730`) instantiates
`Kf := 1/(4C)`.  Nothing else in the tree reads either conjunct
(grep: `Real.sqrt T * ‖fHi‖ ≤ Kf` occurs at `LowRegApplyTwo.lean:219,555` and
`LowRegAllOrderJet.lean:1361,1653` only).

Engine: `MaxRegSolutionJointlySmooth.lean:1311`, slots at `:1341-1347`:

```lean
    (C : ℝ) (hC_pos : 0 < C)
    (hC : ∀ (S : SmoothCcTensor g₀ 0 2),
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ S)
        (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) S‖))
    (hfloor : Real.sqrt T * ‖u.deriv‖ ≤ 1 / (2 * C))
```

Sole caller: `LowRegAllOrderJet.lean:1550`.

## 2. Q1 — the slot's true role

`hfloor` is used **once**, inside `hF_small`, at `MaxRegSolutionJointlySmooth.lean:1495-1502`:

```lean
        calc ‖timeH1.toFun u t‖
            = ‖timeH1.toFun u t - u.init‖ := by rw [hinit, sub_zero]
          _ ≤ Real.sqrt t * ‖u.deriv‖ := u.norm_toFun_sub_init_le ht_icc
          _ ≤ Real.sqrt T * ‖u.deriv‖ := …
          _ ≤ 1 / (2 * C) := hfloor
```

and the result feeds `hC` to produce `gFibreOpBound … (F t) (1/2)` — the
condition that `g₀ + F t` is a genuine metric at every time.  So:

* the slot's **true content** is `sup_{t ∈ [0,T]} ‖u(t)‖_{H^a} ≤ 1/(2C)`, a
  smallness of the STATE, not of the derivative;
* `u.deriv` appears only through `timeH1.norm_toFun_sub_init_le`
  (`TimeH1Modulus.lean:105`), a *proxy* — the cheapest a-priori route to the
  state bound when nothing else is known;
* the `L²ₜH²` norm of `u.deriv` is therefore **not** genuinely needed.

Answers to the three sub-questions:

(i) an `L²ₜH¹`-type bound cannot replace it *at this slot* — the exponent is
tied to `hC`, and in dim 3 the fibre-operator embedding needs `> n/2 = 3/2`
(`hs2_op_bound`, `H2Pointwise.lean:323`, is stated at `H²`).  But an `H¹` bound
on the *forcing* does suffice, because the maximal-regularity state gains one
order — see §3, and the ready-made
`maxRegDuhamelSolField_inclusion_Ha1_ae_pointwise_le`
(`FieldHa1TimeSupTrace.lean:183`), `‖·‖_{H^{a+1}} ≤ √(1+T)·‖F‖_{L²ₜH^a}` a.e.

(ii) a bound on `fHi` in a lower norm is unnecessary: `fHi` can be dropped from
the argument entirely.

(iii) **a qualitative/relocated smallness is exactly right, and it is already
present.**  This is the winning route.

## 3. Q2 — the Lo side: the floor is already a conjunct

`IsRealizedTwo` (`LowRegApplyTwo.lean:107-219`) binds `R` with `hR : 0 < R`,
`R ≤ ρ`, and the conjunct

```lean
      (∀ᵐ t ∂timeMeasure T, ‖u.lo.toFun t‖ ≤ R) ∧
      Real.sqrt T * ‖fHi‖ ≤ Kf
```

`u.lo : timeH1 (tensorHs g 0 2 a) T` with `a = 2` (`CrossScaleParabolicTrace.lean:359`),
so `u.lo.toFun t : tensorHs g 0 2 (2:ℝ)` and `‖u.lo.toFun t‖` **is the `H²`
norm** — the same norm the engine's `hC` measures, and the same object
`timeH1.toFun u t` the engine bounds (`lowreg_allOrderJet` returns `u := ucs.lo`,
`LowRegAllOrderJet.lean:1433`).

Its proof (`LowRegApplyTwo.lean:517-548`) runs entirely on the **Lo** side: the
`H²` view of the `H³` state field of the order-one solver, bounded by the
solver's state ball `hball`.  And that ball's radius is closed and free:

* `lowreg_partial_sol_of_bounds` (`UnifClassBounds.lean:263`) last conjunct:
  `‖gforce‖ ≤ lowregStateRad Ctop B1 ρ P / 4`;
* `lowregStateRad_le_P` (`:131`): `lowregStateRad Ctop B1 ρ P ≤ P`
  (in fact `≤ P/4` through `lowregOuterRad_le_P`);
* `P` is chosen *inside* `lowreg_solve_two` (`LowRegApplyTwo.lean:797`) as
  `min (min ρ ρN) ((1-c)/(6*(L+1)))`, and every constraint on it is an upper
  bound, so a fourth `min` component is free.

So the answer to "what upgrades an `H¹` bound on `fLo` to the `H²` information
the engine needs" is: **nothing needs upgrading** — the Lo solver's state ball
is already stated at `H²`, because the order-one state space is `H³` and its
`H²` view is one order below.  The forcing-inclusion worry
(`timeL2Inclusion fHi = f` goes DOWN) never arises: `fHi` leaves the argument.

## 4. Q3 — `‖staticForce g₀ g₀ 1‖` IS class-boundable, and is already the `D`-number

`staticForce g₀ g_bg σ = smoothCcToTensorHs g₀ σ (deTurckRHSSection g_bg g₀)`
(`LowRegLiftNTerm.lean:142`).  At `σ = 1`:

* `staticN_h1_le` (`UnifNZeroBound.lean:430`) bounds it by the closed
  `nZeroC Ksup Λ volBase n` given a fibre sup bound `Ksup` on the covariant
  `j ≤ 1` jet of `deTurckRHSSection`;
* `nZero_unif` (`:526`) / `nZero_lowregNfun` (`:551`) put that in the exact
  `hzero` currency of `lowreg_partial_sol_of_bounds`;
* the class-uniform producer is `unifKsupLeOne` (`UnifDeTurckRHSOne.lean:1538`),
  whose hypotheses are literally `MetricCovDerivOrderBoundOn … 1`, `… 2`,
  `… 3` — **orders 1,2,3 only**, inside (N)'s `∀ a ≤ 3`.  (`deTurckRHSSection`
  is Ricci + the DeTurck vector term: 2 metric derivatives; one covariant
  derivative makes 3.  No `∇Ric`-at-4 term appears at `σ = 1`.)

Moreover `D` — that same bound — is **already in the horizon**
(`UnifClassBounds.lean:81`):

```lean
def lowregHorizon (Ctop B0 B1 D ρ P : ℝ) : ℝ :=
  min 1 (min (1 / (64 * (B0 + 1) ^ 2))
    ((lowregStateRad Ctop B1 ρ P / 4 / (2 * (D + 1))) ^ 2))
```

So option (b) adds **no** new class-uniform obligation at order 1; it removes
the order-2 one.  Front 3's item (C)1 (`FRONT3_ASSEMBLY_PLAN.md:140`) is
dissolved, not relocated.

## 5. The design (winning route and why the others lose)

**Winning route: relocate the smallness from the horizon to the radius.**

* engine slot lowered from the derivative proxy to the state itself;
* the state bound produced from the package's own `hballU`;
* `R ≤ 1/(2C)` bought by one extra `min` in `P`.

Cost: `τ₀` shrinks by the factor `(1/(2C))²` through `lowregHorizon`'s
`(R/4/(2(D+1)))²`, staying positive (`lowregHorizon_pos`) and monotone
(`lowregHorizon_mono`).  `C` is the `hs2_op_bound` constant, whose
constant-exposed sibling `hs2_op_bound_unif` (`H2PointwiseUnif.lean:278`) is
already front 3's (A)-class producer, so the new `τ₀` is closed in
class-uniform data: `τ₀ = τ₀(Ctop, B0, B1, D, ρ, P, C)`.

Rejected alternatives:

* **slot-lowering to `H^b`, `b < 2`** — the fibre embedding fails below
  `n/2 = 3/2` in dim 3, and `u.deriv` still lives at `H²`, so nothing is gained;
* **`H¹` floor on `f` via the trace gain** — mathematically fine and fully
  stocked (`FieldHa1TimeSupTrace.lean:183` gives
  `sup_t ‖u(t)‖_{H²} ≤ √(1+T)‖f‖_{L²ₜH¹}`), but it needs a Neumann bound on the
  Lo fixed point to make `‖f‖ ≲ √T‖staticForce g g 1‖`, i.e. a NEW mirror of
  `norm_fix_le` on the Lo side, when `‖f‖ ≤ R/4` is already in hand and `R` is
  already capped.  **Keep as fallback route B** (§8): it is the shortest repair
  if the radius cap turns out to be blocked;
* **keeping `Kf` and bounding `‖staticForce g g 2‖`** — that is option (c),
  retired.

## 6. Bricks

**B1 — engine slot lowering** (`Analysis/Spectral/Intrinsic/HeatSemigroup/MaxRegSolutionJointlySmooth.lean`).
Replace `hfloor` (`:1347`) by

```lean
    (hstate : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖timeH1.toFun u t‖ ≤ 1 / (2 * C))
```

and replace the four-line `calc` at `:1495-1502` by `hstate t ht_icc`.  Extract
the deleted calc as a reusable producer beside it (canonical home; keeps the old
route available and the `√t` narrative in `:1299` honest):

```lean
theorem state_le_of_sqrt_floor (u : MaxRegSolutionSpace … (a : ℝ) T)
    (htrace : timeH1.trace0 _ T u = 0) {K : ℝ}
    (hfloor : Real.sqrt T * ‖u.deriv‖ ≤ K) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖timeH1.toFun u t‖ ≤ K
```

Difficulty: LOW.  One call site (`LowRegAllOrderJet.lean:1550`).  No `sorry`
touched.  Docstring `:1299` needs one sentence updated.

**B2 — a.e. → everywhere for the state ball** (`ShortTime/LowRegAllOrderJet.lean`).
From `hballU : ∀ᵐ t, ‖ucs.lo.toFun t‖ ≤ R` produce
`∀ t ∈ Icc 0 T, ‖timeH1.toFun u t‖ ≤ R`.  The pattern is already in this file at
`:334-348` (the `min`-trick against `Measure.eqOn_Ico_of_ae_eq`); use
`Measure.eqOn_Icc_of_ae_eq` (mathlib `Measure/OpenPos.lean:194`, needs
`(0 : ℝ) ≠ T`, already used at `LowRegAllOrderJet.lean:657`) with
`timeH1.continuousOn_toFun` (`TimeH1.lean:293`).  Difficulty: LOW–MEDIUM,
~25 lines, entirely mechanical.  Best home: a private lemma next to
`coord_eq_smoothN`, or — better, since two files want it — beside
`norm_toFun_sub_init_le` in `TimeSobolev/TimeH1Modulus.lean` as
`timeH1.le_of_ae_le_of_continuous`.

**B3 — swap the package conjunct** (`ShortTime/LowRegApplyTwo.lean`).
In `IsRealizedTwo` replace `Real.sqrt T * ‖fHi‖ ≤ Kf` (`:219`) by `R ≤ Kf`
(rename the parameter `Kf → Rcap` throughout; it is a *state cap* now, not a
forcing floor).  In `lowreg_apply_two`: drop `hTfloor` (`:420`), delete the
`hfloorHi` block (`:555-590`), add `hRcap : R ≤ Rcap` to the hypotheses (`R` is
already in the binder block at `:345`).  The docstring's margin paragraph
(`:332-336`) loses its `hTfloor`/`norm_fix_le` sentence.  Delete the now-dead privates
`nonautL2Map_zero` (`:245`) and `norm_fix_le` (`:282`), and
`lowregFloorHorizon` + `lowregFloorHorizon_pos` (`:228-236`).
`norm_liftForceHi_le` (`LowRegLiftNTerm.lean:259`) loses its consumer but stays
as API.  Difficulty: MEDIUM (bookkeeping across a 40-field existential).

**B4 — cap `P` in `lowreg_solve_two`** (`ShortTime/LowRegApplyTwo.lean:797`).
`P := min (min (min ρ ρN) ((1-c)/(6*(L+1)))) Rcap`; every `hP*` fact gains one
`le_trans`; `hPpos` gains `0 < Rcap`.  Discharge `hRcap` by
`(lowregStateRad_le_P hPpos.le).trans (min_le_right _ _)`.  Drop
`lowregFloorHorizon` from the reported `T₀` (`:820-824`).  Difficulty: LOW.

**B5 — endpoint wiring** (`ShortTime/LowRegAllOrderJet.lean`).
`lowreg_allOrderJet` (`:1311`) exports the everywhere state bound in place of
`Real.sqrt T * ‖fHi‖ ≤ Kf` (`:1361`); `lowreg_joint_of_re` (`:1585`) replaces
its `hderiv`/`hfloor` block (`:1636-1660`) by that bound plus `hKfC`, now read
as `Rcap ≤ 1/(2C)`; `lowreg_joint_two` (`:1682`) instantiates
`Rcap := 1/(2C)` instead of `Kf := 1/(4C)`.  Difficulty: LOW.

Nothing outside these three files consumes `lowreg_solve_two`,
`lowreg_joint_of_re` or `lowreg_joint_two` (grep is empty), so the redesign is
contained.

## 7. First dispatchable brick

**B1**, and it is dispatchable now: `MaxRegSolutionJointlySmooth.lean` is not
claimed by the front-2/TK3 lane (which owns `DeTurck/LowRegOpJetWindows.lean`
and `DeTurck/LowRegC2JetTower.lean`), it has a single call site, and B2–B5 all
consume its new slot.  Acceptance: the file checks green and
`LowRegAllOrderJet.lean:1550` still elaborates after passing
`state_le_of_sqrt_floor … hfloor` at the new slot — i.e. B1 can land
*before* B2–B5 with the old floor still in place, as a pure refactor.  That
ordering makes B1 risk-free and keeps the tree green between bricks.

Note for the builder: B3/B4 touch `LowRegApplyTwo.lean`, which is presently
modified in the working tree (`git status`: ` M …/LowRegApplyTwo.lean`) — claim
it, and sequence after the front-2 lane releases, per `FRONT3_ASSEMBLY_PLAN.md`
R3.

## 8. Stop-signal — what triggers the fallback to option (a)

Fall back **only** on this conjunction:

1. B2 fails at the closed endpoint `t = T` (e.g. `Measure.eqOn_Icc_of_ae_eq`
   cannot be applied because some consumer needs the bound off `[0,T]`), **and**
2. the fallback route B (§5: `H¹` floor on `f` via
   `maxRegDuhamelSolField_inclusion_Ha1_ae_pointwise_le` plus a Lo-side mirror
   of `norm_fix_le` against `norm_liftForceLo_le`) also fails.

Either alone is not a stop: (1) alone is repaired by route B, which needs no
`t = T` upgrade beyond the same lemma; (2) alone is irrelevant because the
radius cap does not use it.

A *non*-signal, explicitly: shrinking `τ₀` by `(1/(2C))²` is not a failure.  The
horizon was never claimed to be sharp, and `C` is class-uniform.

The genuine mathematical stop — the one that would mean (b) is wrong rather than
awkward — would be a proof that `R` is bounded BELOW by something metric-
individual, i.e. that the solver cannot run at small radius.  Nothing in
`UnifClassBounds.lean:60-140` suggests that: every constraint on
`lowregStateRad` and `lowregOuterRad` is an upper bound.

## 9. Notes and residual risks

* **`.choose` is still there.**  `(hs2_opBound_at_two hDim g).choose` is an
  opaque witness; capping `P` against it is logically fine but class-uniformity
  needs the exposed sibling `hs2_op_bound_unif` (`H2PointwiseUnif.lean:278`).
  That swap is already front 3's (A)/(B) work (brick G3), unchanged by this
  design — option (b) neither fixes nor worsens it.
* **`staticForce … 2` survives as an object**, in `liftForceHi` and the `fHi`
  fixed-point equation (`LowRegApplyTwo.lean:153`).  Only its *norm* leaves the
  horizon.  Nothing needs to bound it any more.
* `lowregLiftHorizon' c Z` stays in the reported `T₀`; `Z` is an (B)-class
  refold constant, not an individual one.
* Two dead privates and one dead public def get removed (B3).  Per house rule
  ("discharge obsolete frontiers … remove unnecessary private helpers") that is
  part of the brick, not a follow-up.

## 10. Status

Design settled 2026-08-03, read-only recon.  Bricks B1–B5 above.

**B1 LANDED GREEN 2026-08-03.**  Engine slot swapped
(`MaxRegSolutionJointlySmooth.lean:1349` now `hstate : ∀ t ∈ Icc 0 T,
‖timeH1.toFun u t‖ ≤ 1/(2C)`; the calc collapsed to `exact hstate t ht_icc` at
`:1499`).  Producer extracted as
`TimeSobolev.timeH1.state_le_of_sqrt_floor`
(`Analysis/Parabolic/TimeSobolev/TimeH1Modulus.lean:136`) — stated generically
in `X` and in the bound `B`, taking `hinit : u.init = 0` rather than `htrace`,
and placed in the timeH1 API module rather than the engine file as §6 sketched:
that module has exactly ONE importer repo-wide, so the canonical home costs no
extra rebuild.  Single call site `LowRegAllOrderJet.lean:1556` passes
`u.state_le_of_sqrt_floor hinit hfloor`, so `lowreg_joint_smooth`'s public
statement is unchanged and the tree is green between bricks, exactly as §7
predicted.  Axiom census on the engine and on `lowreg_joint_smooth` is identical
to the pre-edit baseline: `[propext, Classical.choice, Quot.sound]`.

**B2 LANDED GREEN 2026-08-03**, compiled first try, ~12 lines.
`TimeSobolev.timeH1.norm_le_of_ae_le` (`TimeH1Modulus.lean:156`):
`0 < T` plus `∀ᵐ t ∂timeMeasure T, ‖u.toFun t‖ ≤ R` gives
`∀ t ∈ Icc 0 T, ‖u.toFun t‖ ≤ R`.  Named as the brick suggested; homed beside
`state_le_of_sqrt_floor` rather than beside `continuousOn_toFun` (that file,
`TimeH1.lean`, has 7 direct importers — the placement is the brick's sanctioned
fallback).  **The §8 stop-signal did NOT fire**: the closed endpoint `t = T` is
covered with no weakening to `Ico`.  `Measure.eqOn_Icc_of_ae_eq` differs from
its `Ico` sibling by exactly one hypothesis, `hne : (0:ℝ) ≠ T` (discharged by
`hT.ne`), because `closure (interior (Icc a b)) = Icc a b` holds precisely for
`a ≠ b`; the `min ‖·‖ R` truncation of `:334-348` transports it from `=` to `≤`.
Route B (the `H¹` floor via `FieldHa1TimeSupTrace`) is therefore NOT needed and
stays unused.  `norm_le_of_ae_le` has no consumer yet — B5 is its consumer.

Remaining: B3, B4 (`LowRegApplyTwo.lean`, front-2 shared file — claim after the
front-2 leaf releases) and B5.  Until those land, `‖staticForce g g 2‖` is still
in the horizon: B1/B2 are the refactor half and move no mathematics by
themselves.

Honest denominators (unchanged by this file — a design note moves no
mathematics): black box (N) is **stated, proof 0%**.  Front 3
(`UnifClassBounds` design) ~?%; this recon closes the *design* of front 3's one
genuinely individual constant, item (C)1, which is roughly one of ~8 front-3
work items, so front 3 advances by design only, ~0% in proved Lean.  Machinery
~88%.  Whole HCG compactness: low single digits.
