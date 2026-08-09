# LowRegLiftHfLo

## Migration micro-plan (2026-08-02): refolded FLo route

Trigger: `lowreg_N_affine` (`LowRegLiftAffine.lean`) was migrated to consume a
*supplied* refolded low action `FLo` (`Continuous FLo` + smooth-core formula
against `c0CoreData.a1Lo + oneCore.a1Lo`) and now concludes with `refoldBaseN`,
not `lowBaseN`.  This file (and `lowreg_N_radial` in `LowRegA1LoPair.lean`)
still calls the pre-refold signature, so both are currently RED.

Design chosen: **supplied `FLo` at the equation level, `refold_time` invoked at
the packet level.**  Rationale: `lowreg_hfLo` must hand an `FLo` to
`lowreg_N_affine`, so it mirrors `lowreg_N_affine` verbatim; `lowreg_hfLo_data`
is the endpoint that must be honest, so it calls `refold_time` once and
existentially exports the `FLo` it produced.  Exactly one route stays alive:
`lowA1Lo` is no longer used anywhere in this file.

New/changed declarations:

- `lowAffA1` → `refoldAffA1 g ρ FLo hT hT1 f`.  Only `ρ` and `FLo` are needed
  (no `hδ0`/`hδ_le`/`hreal`, since the coefficient is supplied).
- `lowAffA1_le` → `refoldAffA1_le` (same radial/congr contraction argument).
- `lowAffA1_data` → `refoldAffA1_data`.  Hypotheses `hpair : LowA1CorePair` and
  the `lowA1Lo_ball` call disappear; they are replaced by `Continuous FLo` and
  the affine bound `∀ x, ‖FLo x‖ ≤ Z + L * ‖x‖` that `refold_time` supplies.
  Uniform constant becomes `Z + L * R` on the a.e. `H3` ball of radius `R`.
- `lowAff_self` → `refoldAff_self`, restated directly against `refoldBaseN`
  (there is no `refoldBaseA`, so `lowBaseN_frozen` is replaced by an inline
  `radialCLM_h3` / `radialCLM_h2` rewrite inside this lemma).
- `lowreg_hfLo`: the `∃ ρ₀` wrapper is **dropped** (its only source was
  `lowA1Core_pair`; nothing internal constrains `ρ` any more).  New hypotheses
  `FLo`, `hFLo : Continuous FLo`, `hFcore`; `hA2core` is restated against
  `refoldCore … |>.a2Lo`.  Conclusion keeps the exact `nonautL2Map … A2 … A1 …
  f + liftForceLo` shape demanded by `lowreg_lift_two`'s `hfLo` slot
  (`LowRegLiftTwo.lean:206`); only the A1 slot's *term* changes, and that slot
  is a plain parameter there, so the match is unaffected.
- `lowreg_hfLo_data`: keeps `∃ ρ₀` (now sourced from `refold_time`), gains
  `∃ FLo` at the head of its conclusion, and drops `lowA1Core_pair`.
- `LowRegA1LoPair.lean`: `lowreg_N_radial` is deleted — it is the pre-refold
  consumer, and it cannot be re-proved with `FLo := lowA1Lo` because
  `refoldCore.C1 = c0CoreData.C1 + lowCoreDataBg.C1 ≠ lowCoreData.C1`.
  `lowA1Core_pair` / `lowA1Lo_ball` stay: they are still the honest producers
  for `lowBaseN`-shaped statements.

Risk watched: `refold_time` states its types through the *private* abbrevs
`metricH3/H2/H1` of `LowRegBgA1Refold.lean`; unification against
`tensorHs g 0 2 3` relies on those being `abbrev` (reducible).

## Status (2026-08-02) — migration landed, GREEN

Focused verification passed for both edited files; no `sorry`, `admit`,
`axiom`, or `set_option` remains in either.  `lowA1Lo` no longer occurs
anywhere in this module.

Realized structure (top to bottom): `affState` / `stateField` / `hsCongr_trans`
(unchanged) → `lowAffA2`, `lowAffA2_le`, `lowAffA2_data` (unchanged) →
`refoldAffA1`, `refoldAffA1_le`, `refoldAffA1_data` (new, replacing the
`lowA1Lo`-based trio) → `refoldAff_self` (private) → `lowreg_hfLo` →
`lowreg_hfLo_data`.

`refoldAff_self` is stated with `lowBaseForce` on the left, directly against
`refoldBaseN`; that is what removed the need for a `refoldBaseA` /
`refoldBaseN_frozen` pair.  The `radialCLM_h3` / `radialCLM_h2` collapse that
`lowBaseN_frozen` used to perform now happens inside it.

`lowreg_hfLo_data` calls `refold_time` once, at the `H3` Duhamel field
transported by `(tensorHsCongrL … ).compLpL`, and re-exports the `FLo` it
obtained.  The private `metricH3/H2/H1` abbrevs of `LowRegBgA1Refold.lean`
unified against `tensorHs g 0 2 3` etc. without any adapter, as hoped.

Hotspots for the next editor:

- `add_le_add_left` in this Mathlib version produces `b + a ≤ c + a`, not
  `a + b ≤ a + c`.  The affine-envelope step in `refoldAffA1_data` uses an
  explicit `mul_le_mul_of_nonneg_left` + `linarith` instead; do not "simplify"
  it back to `add_le_add_left`.
- `rw` will not fold `tensorHsCongr … (maxRegDuhamelSolField …)` back into
  `affState …` (`affState` is a plain `private def`, so `kabstract` cannot
  delta-unfold it).  `refoldAff_self` therefore pre-states its two `radialCLM`
  rewrites as `have`s whose types are checked at default transparency.
- Verification cost is ~26 s at `-LeanThreads 1`; the file needs no heartbeat
  bump.

## 2026-08-02 (second pass) — Hi side of `refold_time` re-exported, GREEN

Trigger: `lowreg_hfLo_data` invoked `refold_time` once and threw away the whole
high side (`FHi`, its continuity, smooth core and affine bound) plus the entire
`htime` certificate packet (both `MemLp`s, both `toLp` Minkowski bounds, and the
inclusion square).  Those are exactly the `A1Hi` / `hsmallHi` / `hsmallLo` /
`hA1compat` inputs of `lowreg_realize_two` at `aLo = 1`, `aHi = 2`.

### Exponent design decision

**The congr is baked into the definition**, mirroring `refoldAffA1`.
`refoldAffA1Hi` is declared at

```text
ℝ → tensorHs g 0 2 ((2 : ℝ) + 1) →L[ℝ] tensorHs g 0 2 (2 : ℝ)
```

i.e. the *arithmetic* domain exponent `aHi + 1` and the *literal* codomain
`aHi = 2`.  Only the domain needs normalizing (`(2 : ℝ) + 1 = 3`); the codomain
is already the literal exponent that `lowreg_realize_two` demands, so no
codomain congr is introduced.  Rationale for baking it in rather than exporting
at native `H³ → H²`:

- symmetry with `refoldAffA1`, whose domain congr `(1 : ℝ) + 1 = 2` is likewise
  internal.  The two families then differ only by scale, not by convention;
- the consumer slot is fixed, so leaving the transport outside would only move
  it to every call site;
- the inclusion square is provable *inside* this file with one application of
  `tensorHsCongr_incl`, so nothing upstream is needed.  Had the congr been left
  outside, the consumer would have had to redo the same square transport.

The `MemLp` / bound transport across the congr is never performed as a transport
at all — see below.

### New declarations

- `duhH3` (public): the order-one Duhamel field transported to the literal
  exponent `3`, i.e. exactly the `u` that `refold_time` is called at.  It was
  already written inline in `lowreg_hfLo_data`; naming it is what lets the two
  time-`L²` certificates be *stated* (`… ≤ L * ‖duhH3 …‖ + √T * Z`).
- `duhH3_ae` (private): `duhH3 … =ᵐ affState …` from `coeFn_compLpL`.  This is
  the only bridge between the `Lp`-valued state that `refold_time` sees and the
  pointwise `affState` that both families are built from.
- `affState_aemeas` (private): the measurability preamble that `lowAffA2_data`
  and `refoldAffA1_data` used to each carry inline.
- `refoldAffA1_aemeas`, `refoldAffA1Hi_aemeas`: extracted so that
  `refoldAffA1_data`, `refoldAffA1_memLp` and `refoldAffA1Hi_data` share it.
- `refoldAffA1Hi`, `refoldAffA1Hi_le`: high siblings of `refoldAffA1` /
  `refoldAffA1_le`, verbatim the same radial contraction argument at exponent
  `3` instead of `2`.
- `refoldAffA1_memLp`, `refoldAffA1Hi_data`: the two time-`L²` certificates.
- `refoldAffA1_compat`: the a.e. Sobolev-inclusion square of the two families.

### Route decision: re-derive, do not transport

The `htime` packet already contains `MemLp AHi 2` and `‖hHi.toLp AHi‖ ≤ …` for
the *native* families `AHi/ALo` built on `⇑(duhH3 …) t`.  Transporting those to
`refoldAffA1Hi`/`refoldAffA1` would need (i) an a.e. transfer along `duhH3_ae`
and (ii) a transfer across the domain congr — both at CLM-over-`tensorHs`
types, which is precisely the instance-tower defeq divergence documented in
`LowRegBgA1Refold.md`.

Instead both certificates are **re-derived** by calling `memLp_clm_affine`
directly on the normalized family, exactly as `refold_time` itself does.  The
input is the a.e. bound `‖refoldAffA1{Hi} … t‖ ≤ Z + L * ‖duhH3 … t‖`, obtained
from the pointwise `refoldAffA1{Hi}_le` plus the exported affine bound
`hFbd`/`hFHiBd`, after one `rw [hd]` with `duhH3_ae`.  The conclusion is
*identical* in shape to the discarded one (`L * ‖u‖ + √T * Z`), no `MemLp.add`,
`MemLp.toLp_congr` or `MemLp.toLp_add` is ever instantiated at a CLM type, and
the file still needs **no** `set_option` of any kind.  Consequently only
`hcomm` is taken out of `htime`; the four other components are dropped with `-`
on purpose, not by oversight.

The square is likewise proved pointwise (`ContinuousLinearMap.ext`, then
`DFunLike.congr_fun (hsq t) (Qhi x)`), never by an equality of whole operator
families.  Its only real content is
`tensorHsCongr_incl ((1:ℝ)+1 = 2) ((2:ℝ)+1 = 3) ((1:ℝ)+1 ≤ (2:ℝ)+1) ((2:ℝ) ≤ 3)`
(`Analysis/Spectral/Tensor/SobolevScale/ExponentCongr.lean:95`); the composed
sibling `tensorHsCongrL_incl` at line 110 there is the operator-level form if a
later brick wants it.

### New conclusion of `lowreg_hfLo_data`

Unchanged: the `∃ ρ₀` head, every hypothesis, and the whole low tail
(`C2`, `hA2`, `hC2`, `hA1`, `B1`, the `B1` bound, and the fixed-point equation
with the same `lowAffA2` / `refoldAffA1` / `liftForceLo` shapes).  Added, in
order: `∃ Z L, 0 ≤ Z ∧ 0 ≤ L`; `∃ FHi` before `FLo`; `Continuous FHi`; the `FHi`
smooth-core formula against `c0CoreData.a1Hi + oneCore.a1Hi`; the `FHi` affine
bound; `hA1Hi : MemLp (refoldAffA1Hi …) 2`; the two `toLp` bounds; the a.e.
`Z + L * B3` bound for the high family; and the a.e. inclusion square.

Deliberately **not** added (kept as the previous pass left them, per the brick's
scope): the low-side state facts `Continuous FLo`, the `FLo` smooth-core formula
and the `FLo` affine bound are still consumed internally and not re-exported,
even though the high-side analogues now are.  Adding them is a two-line
follow-up if a consumer needs to pin `FLo` to the DeTurck data.

### Read-only finding: is `lowAffA2` the low side of the total-A2 square?

**No — they are genuinely different families**, not definitionally equal and not
related by any existing lemma.

- `lowAffA2` (this file, line 156) is `lowA2Lo` alone, evaluated at
  `incl32 (affState … t)`, and *post*-composed with a second radial factor
  `radialCLM g (0 ≤ 3) ρ (incl32 (affState … t))`, at domain exponent
  `(1 : ℝ) + 2`.
- `lowRegA2TotalLo`
  (`Analysis/Parabolic/QuasiLinear/TensorMaximalRegularity/LowRegOperatorTime.lean:927`)
  is `lowRegA2TimeLo … t + lowA2Lo … (lowRegStateL2 … t)`, at domain exponent
  `(3 : ℝ)` and with **no** radial factor.

Three independent differences: (i) `lowRegA2TotalLo` carries the extra principal
summand `lowRegA2TimeLo` (`LowRegOperatorTime.lean:798`), which `lowAffA2` does
not have at all; (ii) `lowAffA2` carries the extra radial factor; (iii) the `H²`
state fed to `lowA2Lo` is `incl32 (affState … t)` here versus
`lowRegStateL2 … t` (`ShortTime/LowRegPrincipalTime.lean:55`) there — those two
agree only a.e., via `lowRegState_ae` (`LowRegPrincipalTime.lean:76`) plus
`orderOneH2Iso`.  Only the exponent spelling `(1 : ℝ) + 2` vs `(3 : ℝ)` is
cosmetic.

Consequence for the next brick.  `lowRegA2TotalLo_data`
(`LowRegOperatorTime.lean:956`, square at lines 987–995) is a ready-made
`hA2compat`, but it is a square for `lowRegA2Total` / `lowRegA2TotalLo`, and the
`A2Lo` slot of `lowreg_realize_two` is forced to be the *same term* that appears
in the `hfLo` fixed-point equation, i.e. `lowAffA2`.  So that square cannot be
cited: the `hA2compat` route needs a high sibling of `lowAffA2` (built from
`lowA2Hi`, `DeTurckRemainderLowBaseTime.lean:1555`, with the same radial factor
at exponent `4`) together with its own square — structurally the same work that
`refoldAffA1Hi` + `refoldAffA1_compat` just did for the first-order arm.  The
alternative is to restate `lowreg_hfLo`'s fixed point against `lowRegA2TotalLo`,
which changes `lowreg_hfLo` and is a larger, separate decision.

### Verification

Focused check passed and the targeted module build is green, with no warning
attributable to this file.  No `sorry`, `admit`, `axiom` or `set_option`; the
file remains free of heartbeat settings.  Check cost rose to roughly two
minutes at `-LeanThreads 1` (the file grew from 746 to 1053 lines).

## 2026-08-02 (third pass) — A2 high sibling + square, GREEN

Trigger: brick 2a of `LowRegApplyTwo.md`.  The `hA2compat` slot of
`lowreg_realize_two` is forced to the `A2Lo` term that appears in the proved
`hfLo` equation (= `lowAffA2`), so the ready-made `lowRegA2TotalLo_data` square
cannot be cited (see the second pass's read-only finding).  This pass builds the
missing high sibling.

### New declarations

- `loH4` (private abbrev, line 51): `tensorHs g 0 2 (4 : ℝ)`, for readability of
  the `H⁴` slots.
- `lowAffA2Hi` (line 313): `lowA2Hi` at the transported state, post-composed
  with the *same* radial factor selected by the same `H²` state, at Sobolev
  order `4`, and normalized to the arithmetic domain exponent `(2 : ℝ) + 2`.
  Codomain is the literal `2`, so only the domain congr is baked in — the same
  convention `refoldAffA1Hi` uses.
- `lowAffA2Hi_le` (line 337), `lowAffA2Hi_data` (line 378): verbatim the
  `lowAffA2_le` / `lowAffA2_data` arguments one scale up; `_data` reuses the
  extracted `affState_aemeas` instead of re-deriving it.
- `lowAffA2_compat` (line 450): the inclusion square of the two second-order
  families, **pointwise in `t`** (no measure needed, since the completed square
  it consumes is `∀ v`).  Consumers weaken with `Eventually.of_forall`.

### Provenance of the completed a2 square

The `∀ v` square of `lowA2Hi` / `lowA2Lo` **already exists and is proved**:
`radialA2_lip` (`DeTurck/DeTurckRemainderLowBaseTimeA2.lean:370`, last
conjunct), derived there by `DenseRange.induction_on` from `a2_comm` on the
smooth core.  It is re-exported together with continuity and the `C * ρ`
uniform bounds for *both* scales by `lowA2_small`
(`Analysis/Parabolic/QuasiLinear/TensorMaximalRegularity/LowRegOperatorTime.lean:667`).
So no density argument had to be redone here, and `lowAffA2_compat` takes that
square as a hypothesis exactly the way `refoldAffA1_compat` takes its pointwise
first-order square.  The genuine content added by `lowAffA2_compat` is the two
transports the completed square does *not* cover: `radialCLM_incl` at
`(3 ≤ 4)` for the radial passenger, and `tensorHsCongr_incl` at
`((1 : ℝ) + 2 = 3, (2 : ℝ) + 2 = 4)` for the exponent normalization.

### Additional exports of `lowreg_hfLo_data` (line 1120)

- The three low-side facts flagged as a two-line follow-up by the second pass:
  `Continuous FLo`, the `FLo` smooth-core formula against
  `c0CoreData.a1Lo + oneCore.a1Lo`, and the `FLo` affine bound.  They were
  already destructured internally; only the conclusion changed.
- `(C2 : ℝ) = B2`.  This is the resolution of Risk 2 of `LowRegApplyTwo.md`:
  the `C2` handed to `nonautL2Map` inside the fixed-point equation is *data*,
  so a consumer cannot swap in its own; without this identification the
  smallness condition `C2Lo ≤ c` is unreachable.  `lowAffA2_data` already
  proved it and the packet was discarding it.
- `stateField` was `private`, but it occurs in the `hball` hypothesis of
  `lowreg_hfLo_data`, so **no other module could state that hypothesis**.  It is
  now public with a docstring.  This is a usability fix, not a design change.

### Verification

Focused check and the targeted module build are both green; no `sorry`,
`admit`, `axiom` or `set_option`, and no warning attributable to this file.
Check cost is roughly half a minute at `-LeanThreads 1`.

## 2026-08-02 (fourth pass) — `B3` dissolved: the packet is `L²_t`-only, GREEN

Export-shape change (this is a **breaking** change to `lowreg_hfLo_data`).

Removed from the hypothesis block:

- the binder `B3` (the binder list is now `{R ρ δ T B2}`),
- `0 ≤ B3`,
- `∀ᵐ t, ‖maxRegDuhamelSolField 1 hT hT1 0 f t‖ ≤ B3`.

Removed from the conclusion:

- the a.e. high uniform bound `∀ᵐ t, ‖refoldAffA1Hi …‖ ≤ Z + L * B3`,
- the existential `∃ B1 ≥ 0, ∀ᵐ t, ‖refoldAffA1 …‖ ≤ B1` (the low fixed-point
  equality that was nested under it is now the last top-level conjunct).

Everything else is unchanged, in particular both `MemLp` certificates and both
Minkowski bounds `‖toLp …‖ ≤ L‖duhH3 f‖ + √T·Z`.  They never needed `hball3`:
they come from `memLp_clm_affine` against the `L²` envelope, so the only work
was to stop routing them through the pointwise `_data` lemmas.

Why: `hball3` is an `L^∞_t H³` bound on the trajectory.  Maximal regularity
puts the zero-initial Duhamel field in `L²_t H³` and nothing better, so the slot
had no producer anywhere in the chain (planner ruling No. 94, FINDING 2).

New declarations:

- `norm_congrLp` (public) — `‖(tensorHsCongrL … h).compLpL 2 μ u‖ = ‖u‖`.
  Proof is `Lp.norm_def` twice, `congr 1`, `eLpNorm_congr_norm_ae`, and
  `norm_tensorHsCongr` pointwise through `coeFn_compLpL`.  No `cases h` is
  needed, which is what makes it work at a non-`rfl` exponent equality.
  Canonical home is beside `tensorHsCongrL` in `SobolevScale/ExponentCongr.lean`
  once that file sees the time-`L²` layer.
- `norm_duhH3_le` (public) — `‖duhH3 g hT hT1 f‖ ≤ (1 + T) * ‖f‖`.  This is the
  CORE maximal-regularity estimate the ruling asked for, and it already existed
  upstream: `norm_maxRegDuhamelSolField_zero_le`
  (`Analysis/Spectral/Intrinsic/DeTurck/DeTurckQuasilinearExistence.lean:217`),
  proved from `maximalRegularitySolField_norm_le` plus the vanishing homogeneous
  part.  `norm_duhH3_le` is just its `duhH3` spelling, i.e. `norm_congrLp`
  composed with it.  Nothing new had to be proved analytically.
- `refoldAffA1Hi_memLp` (public) — the `hball`-free sibling of
  `refoldAffA1_memLp`.  `refoldAffA1Hi_data` is now proved from it, so the
  pointwise conjunct is the only thing left using the trajectory ball.

`refoldAffA1_data` and `refoldAffA1Hi_data` are now unused in the tree.  They
are kept (correct conditional statements) but both carry a WARNING docstring
saying their `hball` is the unproducible `L^∞_t H³` shape and that the lift uses
the `_memLp` route.  Do not re-wire them into the lift.

### Verification

Focused check and the targeted module build are both green; `#print axioms
lowreg_hfLo_data` is `[propext, Classical.choice, Quot.sound]`.  No `sorry`,
`admit`, `axiom`, `set_option`, and no warning attributable to this file.

## Project position

`ricci_flow_unif_existence` itself remains unstated here and 0% complete at its
endpoint placeholder.  The first pass moved the `hfLo` bridge off the
`LowA1CorePair` route and onto the refolded action, so the module no longer
depends on the `D₄`-free `a1Lo` pair estimate at all.  The second pass makes the
packet two-sided: of the six `lowreg_realize_two` first-order inputs at
`aLo = 1`, `aHi = 2` (`A1Hi`, `hA1Hi`, `hA1compat`, and the two `toLp` sizes
feeding `hsmallHi`/`hsmallLo`), all are now exported; the remaining
adjacent-scale gaps are the second-order pair (`A2Hi` + `hA2compat`, blocked by
the `lowAffA2` finding above), the high forcing datum `f0Hi`, and the two
smallness inequalities themselves.  Dedicated uniform-existence machinery is
approximately 79%.  The next mathematical frontier is unchanged: the field-level
Palatini difference identity feeding the `a = 1` envelope and class-uniform
`Ksup` at `j = 1`.


## 2026-08-02 (fifth pass) — `lowreg_hfLo_data` CONSUMES the packet, GREEN

The ordering obstruction recorded in `LowRegApplyTwo.md` (brick 4) is resolved
here and one layer up.  `lowreg_hfLo_data` no longer *produces* the first-order
action packet; it *takes* it.

### New shape of `lowreg_hfLo_data` (line 1117)

Gone from the statement: the `∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ …` prefix, the
`(_ : ρ ≤ ρ₀)` hypothesis, and the whole `∃ Z L FHi FLo, Continuous … ∧ core …
∧ affine …` block of the conclusion.

New hypotheses instead: `{Z L : ℝ}`, `hZ`, `hL`, `FHi`, `FLo`, `hFHi`, `hFLo`,
`hFLoCore`, `hFHiBd`, `hFLoBd`, `hFComm` — exactly what `refold_aff` reports at
the chosen radius.  The conclusion keeps only the per-trajectory data:
`∃ C2 hA2 hC2 hA1 hA1Hi, (C2:ℝ) = B2 ∧ two toLp bounds ∧ the a.e. square ∧ the
low fixed-point equality`.

`hFHiCore` (the *high* smooth-core formula) was **dropped**, not carried: it was
already unused inside the old proof and is unused by every consumer
(`lowreg_hfLo` needs only the `FLo` side).  Keeping it would have been an
unused hypothesis in a reusable lemma.  `refold_aff` still exports it.

### `refoldAffA1_compat` now takes the u-free square

Its `hsq` hypothesis used to be the *time-level* square at `duhH3 … t`, which is
what `refold_time` produced.  It now takes `hFComm : ∀ x, incl12 ∘ FHi x =
FLo x ∘ incl32` and derives the time-level square internally in 20 lines
(`DFunLike.congr_fun` on `hFComm` at `radialCLM₃ x`, then `radialCLM_incl` to
move the inclusion past the radial passenger).  The rest of the proof — the
`duhH3_ae` transport to `affState` and the two exponent normalizations — is
unchanged.  This was the only real content the old `refold_time` time half was
still supplying.

### Deleted (dead, both carried `L^∞_t H³` WARNING docstrings)

`refoldAffA1_data` (was line 648, 47 lines) and `refoldAffA1Hi_data` (was line
839, 36 lines).  Both were superseded by the unconditional `*_memLp` siblings in
the fourth pass and had zero consumers in the tree.

### Verification

Focused check + targeted `.olean` build GREEN (`LowRegLiftAffine` rebuilt with
it, unaffected).  `lowreg_hfLo_data` axiom-clean.  File 1304 → 1229 lines.
