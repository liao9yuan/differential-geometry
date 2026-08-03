# LowRegForceHi

## Role

Lane C, brick C3 at `aHi = 2`: this file produces the **high-scale Nemytskii
map** `N₂` that `lowreg_force_id` (`LowRegRealizeTwo.lean:523`) asks for, and
turns it into the a.e. identity `fHi =ᵐ N₂ ∘ state` for the lifted trajectory.

## What is in this file

* `force_hi_smooth` — the older *smooth-era* variant (unchanged; see the
  historical section below).
* `liftHiN` — the frozen split `N v = N 0 + A₂(v) v + A₁(v) v` read at an `H⁴`
  state, `H²`-valued.
* `hiN_incl` — `incl_{1≤2} ∘ liftHiN = refoldBaseN ∘ incl_{3≤4}`, the commuting
  square against the low-scale frozen split of `LowRegLiftAffine`.
* `hiN_lowreg` — `hiN_incl` chained with `lowreg_N_affine`: the `N₂` slot of
  `lowreg_force_id`, in `H⁴` form.
* `force_hi_id` — the a.e. Nemytskii identity `fHi =ᵐ liftHiN ∘ hi` for any
  lifted `H⁴` field `hi` pinned to the low `H³` state.

## 2026-08-02 — the frozen-split `N₂` (ruling No. 96), GREEN

### Mathematical findings

**The `N₂` frontier was a domain problem, not an estimate problem.**
`LowRegRealizeTwo.md` had isolated the residual of C3 as one object: an
`H^σ`-valued Nemytskii map `N₂` on the lower state ball with
`tensorHsInclusion ∘ N₂ = lowRegN`.  It also recorded, correctly, that the
`H³ → H²` shape is too strong — the small second-order action `lowA2Hi` is an
`H⁴ → H²` operator, so it has an `H⁴` passenger.  The resolution is that **the
lifted solution's own field is `H⁴`**: `CrossScaleField.hiL2` at `a = 2` is
valued in `H^{a+2} = H⁴`.  So `N₂` never needed to be defined on the `H³` ball.
`liftHiN` is defined on `H⁴`, which costs nothing, and the pin
`incl_{3≤4}(hi t) = state t` is available from the realized package.

**No density argument was needed.**  Ruling No. 96 anticipated an
equalizer-closed density argument for `incl ∘ N₂ = lowRegN`.  In fact the
square splits **summand for summand** against the already-completed low-scale
frozen split `refoldBaseN`, because both maps select their coefficient
arguments from the *same* lower `H²` view of the state:

| summand of `liftHiN` | what discharges the inclusion square | low summand of `refoldBaseN` |
| --- | --- | --- |
| `staticForce g g 2` | `staticForce_incl` + `lowBaseForce_eq_static` | `lowBaseForce g` |
| `lowA2Hi (incl₄₂ v) (radialCLM_{H⁴} ρ (incl₄₂ v) v)` | `hA2sq` (from `lowA2_small`) + `radialCLM_incl` + `radialCLM_h3` + `tensorHsInclusion_trans_apply` | `lowA2Lo (incl₃₂ u) (lowRadialH3 ρ u)` |
| `FHi (incl₄₃ v) (lowRadialH3 ρ (incl₄₃ v))` | `hFComm` (from `refold_aff`) + `lowRadialH3_incl` | `FLo u (lowRadialHs ρ (incl₃₂ u))` |

The density work is therefore *entirely* inherited from `lowreg_N_affine`,
which already proves `congr(lowRegN w) = refoldBaseN (congr w.1)` on the whole
`H³` ball by the equalizer-closed argument.  `liftHiN` only has to be a lift of
`refoldBaseN`, and that is pure algebra of the banked squares.

So the smooth-core identities `lowCore_split` / `refold_split` / `a2Lo_core` /
`refoldLo_core` / `lowRadial_eq_self` **do** discharge the smooth-core
agreement, but one layer down, inside `lowreg_N_affine`; this file does not
re-enter them.  `liftHiN`'s shape mirrors `refoldBaseN` summand for summand,
which is how it stays faithful to `lowCore_split`'s
`N(S) - N(0) = A.a2 S + A.a1 S`.

**`radialCLM` versus `lowRadialH3`.**  The two spellings of the radial
retraction in the tree are reconciled by the banked `radialCLM_h3`
(`DeTurckRemainderLowBaseTime.lean:1250`):
`radialCLM (0 ≤ 3) ρ (incl₃₂ u) u = lowRadialH3 ρ u`.  `liftHiN` uses
`radialCLM` at `H⁴` (there is no `lowRadialH4`, and none is needed) and
`lowRadialH3` at `H³`, exactly the two objects whose inclusion behaviour is
already proved.

### The endpoint wiring

`IsRealizedTwo` (`LowRegApplyTwo.lean:90`) gained ONE conjunct,

```
fHi =ᵐ[timeMeasure T] fun t => liftHiN g … FHi (congr_{2+2=4} (u.hiL2 t))
```

rather than a standalone corollary, because the existential of `IsRealizedTwo`
binds `FHi`, `fHi` and `u`: a corollary consuming the package could not *name*
them in its conclusion without re-opening and re-closing the whole existential.
`IsRealizedTwo` has no other consumer in the tree, and `lowreg_solve_two`
transmits the new conjunct for free.  Details in `LowRegApplyTwo.md`.

### Lean lessons

* `tensorHsInclusion_refl` is the **CLM** identity
  (`tensorHsInclusion _ = ContinuousLinearMap.id`); the applied form is
  `tensorHsInclusion_refl_apply`.
* Statements in `DeTurckRemainderLowBaseTime.lean` are phrased with the
  *private* abbreviations `incl32`, `metricH2`, `metricH3`, `lowA2LoOp`.  They
  cannot be named downstream, but they are reducible, so the robust idiom is to
  bind the lemma to a `have` carrying the fully spelled
  `tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) (show …)`
  type and let unification unfold them — do **not** `rw` with the raw lemma,
  whose pattern is stated in the private spelling.
* `refoldBaseN` and `liftHiN` unfold by `rfl`; the
  `rw [show refoldBaseN … = … from rfl]` idiom already used by
  `lowreg_N_affine` keeps the goal readable and avoids `simp only [def]`
  re-matching traps.
* When appending a conjunct to a long `∧`-chain whose last conjunct ends in a
  `fun t => …` lambda, the new `∧` is parsed **inside the lambda body**; the
  previous conjunct must be parenthesised.  The error surfaces far away, as
  "argument … has type `tensorHs …` but is expected to have type `Prop`".

### Verification

Focused check GREEN for both edited files; targeted module builds
`+…ShortTime.LowRegForceHi` and `+…ShortTime.LowRegApplyTwo` GREEN, with no
warnings from either file.  No `sorry`, no `admit`, no `axiom`, no heartbeat
option.

## Historical: `force_hi_smooth` (kept, superseded for the low-regularity era)

`force_hi_smooth` identifies the lifted `H²` forcing almost everywhere with the
genuine order-two smooth Ricci--DeTurck nonlinearity along any smooth family
realizing the lower solution field, by the injectivity bridge
`lowReg_force_smooth` → high-to-low forcing identity → `deTurckSmoothN_incl` →
injectivity of `tensorHsInclusion`.  Its `F` / `hpin` inputs (a smooth-core
family realizing the trajectory field a.e.) have **no producer** in the
low-regularity solution packet: `lowreg_partial_sol` exports only the abstract
Duhamel field, and smooth-core membership of the actual trajectory is
a-posteriori regularity.  It therefore stays as the smooth-era statement; the
low-regularity era goes through `liftHiN` instead, which needs no
representative at all.

## Progress

* `ricci_flow_unif_existence`: unstated in this file; still **0%**.
* Lane C brick C3: the `N₂` residual is **closed** at `aHi = 2` and wired into
  the solved endpoint.  What `LowRegRealizeTwo.md` called "~55% of the C3
  theorem" is now the full statement for the `(1,2)` rung.
* Still open, unchanged by this pass: the a-posteriori fixed-horizon bootstrap
  to all orders, and the class-uniformity layer for `τ₀` (the actual `(N)`
  content) with its four mathematical walls.
