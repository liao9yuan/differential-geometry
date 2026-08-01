# LowRegRealizeTwo

Lane C bricks **C2** (`lowreg_realize_two`) and **C3** (`lowreg_force_id`) of the
`(N)` / `ricci_flow_unif_existence` endgame, plus the exponent-normalized
Lane-B coefficient packets that the `aHi = 2` instantiation will consume.

## Naming

The brick list called for `ShortTime/LowRegRealize.lean`. **That file already
exists** and is unrelated (`lowreg_realize_h2` / `lowreg_realize`, the
dimension-three *fibre* realization radius; it is imported by
`LowRegDenseSolve`). This file is therefore `LowRegRealizeTwo.lean`, matching
the brick name `lowreg_realize_two`.

## What is in this file

Exponent normalization (reusable, three lines each — the transport is
`ContinuousLinearMap.id` after `cases` on the exponent equality):

* `congrOp_aemeas`, `congrOp_memLp`, `congrOp_norm_le` — strong measurability,
  time-`L²` membership and every uniform operator bound survive normalizing the
  *domain* exponent of an operator-valued time family.
* `norm_incl_congr` — the lower-scale size of a state is unchanged by the
  transport (`tensorHsCongr_incl` read through `norm_tensorHsCongr`).

Lane-B packets at the lift's exponents:

* `liftA2Two` / `liftA2Two_data` — the **complete** second-order family
  (`lowRegA2Total`, i.e. principal + extra `a2` arm) at domain `(2 : ℝ) + 2`,
  with strong measurability and the uniform bound `C * ρ`. **Unconditional**:
  consumed straight from `lowRegA2Total_data`, only `hDim`, `g` and one
  realization block.
* `liftA1Two` / `liftA1Two_data` — the first-order family (`lowRegA1Time`) at
  domain `(2 : ℝ) + 1`, with strong measurability and `MemLp _ 2`.
  **Conditional** on the two Lane-A facts that `lowRegA1_memLp` already isolates
  (`hcont`, and the *affine* operator bound `hlin`); they are passed straight
  through, not assumed silently.

C2:

* `lowreg_realize_two` — `lowreg_lift_two` composed with `nonautL2_realize`.
  Produces one `CrossScaleField` on the **unchanged** horizon: zero trace, the
  clean equation `∂ₜ u.lo = Δ u.hiL2 + fHi`, the fixed-point identity for `fHi`,
  the `L²`-class *and* pointwise a.e. forcing inclusion, `u.repr 0 = 0`,
  continuity of `t ↦ ‖u.repr t‖²`, the carrier/representative pins on the closed
  slab, and the a.e. inclusion of `u.repr` onto the order-one Duhamel field.
  Pure composition — no hypothesis beyond those of `lowreg_lift_two` and three
  extra *order* proofs (`hOrdUp : aHi ≤ aHi + 1`, `hOrdRp : aLo + 2 ≤ aHi + 1`)
  that only name inclusions.

C0 completion:

* `lowRadial_eq_self_sol` — both total radial maps are the identity a.e. along
  the transported order-one solution. The spectral-symmetry input of
  `lowRadial_eq_self_along_sol` is now **discharged** by `lowreg_sol_symm_h3`,
  and the ball input is taken in exactly the form `lowreg_partial_sol` exports
  (`field t ∈ lowerState g₀ 1 R`), converted through `norm_incl_congr`. So along
  the solution the *frozen radial* low-base coefficients are the genuine ones,
  with no unproved input left.

C3:

* `coreNAt`, `coreNAt_one`, `deTurckSmoothN_incl`, `coreNAt_incl` — the genuine
  smooth Ricci–DeTurck nonlinearity at an arbitrary spectral order, and the fact
  that raising the order and including back is the identity.
* `lowreg_force_lo` — **unconditional**: the lifted forcing, read at the lower
  scale, is `lowRegN` at the genuine states. It is exactly the composition of
  the pointwise a.e. inclusion identity exported by `lowreg_lift_two` with the
  forcing identification exported by `lowreg_partial_sol`.
* `lowreg_force_id` — the high-scale identity `fHi =ᵐ N2 ∘ state`, for **any**
  lift `N2` of `lowRegN` along the scale inclusion.

All thirteen declarations are sorry-free and axiom-clean (`propext`,
`Classical.choice`, `Quot.sound` only). Focused check passed and a real targeted
module build passed (the focused `lake env lean` result alone is not trusted).

## Mathematical findings

**The forcing identity is an injectivity statement, not an analytic one.**
`tensorHsInclusion` is injective on the spectral scale, so once the *lower*
scale identity `incl (fHi t) = lowRegN (state t)` is known — and that is
unconditional, `lowreg_force_lo` — the value of `fHi t` at the high scale is
already determined. Nothing about the coefficient families, the smallness
conditions or the fixed point is needed for the upgrade. Consequently the
residual of brick C3 is **not** an a.e.-lifting problem through the realize
layer, and it is not a density/`timeOp`-evaluation problem either. It is exactly
one object:

> an `H^σ`-valued Nemytskii map `N2` on the lower state ball with
> `tensorHsInclusion ∘ N2 = lowRegN`.

**Superseding fixed-trajectory route (2026-07-31).**  A global `N2` on the
entire lower state ball is not needed for the actual lifted trajectory, and in
the intended `H³ → H²` shape it is generally too strong because the small
second-order action has an `H⁴` passenger.  `LowRegForceHi.force_hi_smooth`
instead proves the honest `H²` identity along a supplied smooth representative:
it combines `lowReg_force_smooth`, `deTurckSmoothN_incl`, and injectivity of
`tensorHsInclusion`.  The remaining task is to supply that representative from
the solution packet, not to complete a global Nemytskii map on the whole ball.

`coreNAt_incl` exhibits `N2` on the dense smooth core (`deTurckSmoothN` has
order-independent spectral coordinates: `smoothN_eq_embed` plus
`tensorHsInclusion_smoothCcToTensorHs`). Completing it to the whole ball is a
dense-extension problem and therefore needs an `H^σ`-valued **tame estimate**
for the low-base nonlinearity — the same missing estimate as Lane A. The
alternative producer, and the one the brick list intended, is the frozen split
`N u = N 0 + (A2 u + A1 u) u` (`lowBaseN_frozen` / `lowCore_split`): its right
side is already `H2`-valued whenever the state is in `H4`, which is exactly the
regularity the lifted solution has. That route needs an `H2`-valued
`lowBaseForce` and the completed (dense-extended) version of `lowCore_split`.

**The `aHi = 2` instantiation is blocked on three *missing* Lane-B items, none
of them in this file.** They were located during this pass:

1. **CLOSED (conditionally).** *No completed first-order commuting square.*
   `radialA1_pair` (`DeTurckRemainderLowBaseTimeA1.lean:167`) gives
   `incl ∘ A.a1Hi = A.a1Lo ∘ incl` only at the smooth core.  The `∀ v` square
   for the completed `lowA1Hi` / `lowA1Lo` is now `lowA1_lip` / `lowA1_square`
   (`TensorMaximalRegularity/LowRegOperatorTime.lean`), with the time-family
   version `lowRegA1_square` and the low field `lowRegA1TimeLo` /
   `lowRegA1Lo_memLp`.  Route: `dense_lipschitz` + `DenseRange.induction_on`,
   the `radialA2_lip` idiom.  It is **conditional on exactly one** input, the
   first-order sibling of `a2_pair_lip`: smooth-core Lipschitz estimates for
   `a1Hi` and `a1Lo` against the `H3` state difference.  That is unavoidable —
   `lowA1Hi` is a `Dense.extend`, which carries no information at all without
   continuity of the core map, so no argument can produce the square without it.
2. **CLOSED (unconditionally).** *No low sibling of the principal second-order
   family.*  The scout report was based on `LowRegPrincipalTime.lean`; in fact
   `lowRegPrincipalLo`, `principal_comm` (the `H4→H2` / `H3→H1` square) and
   `principal_pair_norm` already existed in
   `Analysis/Spectral/Intrinsic/DeTurck/PrincipalLowRegPair.lean` — only the
   *time* layer was missing.  It is now `lowRegA2TimeLo` / `lowRegA2Lo_data` /
   `lowRegA2TotalLo` / `lowRegA2TotalLo_data`, all unconditional, giving
   measurability, the `C * ρ` bound, and the **total** `∀ t` square for
   `lowRegA2Total`.  One genuinely new upstream lemma was needed,
   `principalLo_cont` (continuity of `lowRegPrincipalLo` on the ball, from
   `NormedRing.inverse_continuousAt` — no Lipschitz estimate required), plus
   `norm_congr_comp` in `ExponentCongr.lean` for the `((1:ℕ):ℝ) → (1:ℝ)`
   codomain transport.
3. *No horizon smallness.* `hsmallHi` / `hsmallLo`
   (`C2 (1+T) + 2√(1+T)‖A1‖_{L²ₜ} < 1`) need a horizon shrink against the
   Lane-B constants; nothing in the tree produces it yet.  This is now the only
   remaining *packaging* obstruction in Lane B.

So the honest state is: **C1/C2 are complete as hypothesis-parameterized
theorems, and they cannot yet be applied.** That is a Lane-B gap, not a Lane-C
one.  Items 1 and 2 above were closed on 2026-07-30 (see
`TensorMaximalRegularity/LowRegOperatorTime.md`); item 3 and the Lane-A
first-order Lipschitz estimate are what still block application.

## Lean lessons

* `subst` the low-exponent name **first**, then call `lowreg_lift_two` with
  `rfl`. The order proofs (`hOrd`, `hOrdSt`, …) that this file names explicitly
  are definitionally equal to the `show … by linarith` proofs baked into
  `nonautL2_realize` by proof irrelevance, so `exact` accepts the realize output
  directly even though `rw` would not.
* Exponent transport is *free* for every operator-family property that matters
  (`AEStronglyMeasurable`, `MemLp`, uniform bounds): `cases hpq` turns
  `tensorHsCongrL` into `ContinuousLinearMap.id`, and
  `simpa only [tensorHsCongrL_refl, ContinuousLinearMap.comp_id]` closes the
  goal. Do **not** reach for `ContinuousLinearMap.compL`/`flip` continuity
  arguments; they are unnecessary.
* This file needs `open DifferentialGeometry.Integral.L2`,
  `… .Integral.Connection` and
  `… .PDE.RicciFlow.IntrinsicSpectral.MetricRealization` on top of the
  `LowRegLiftTwo` opens; without them `SmoothCcTensor`, `gFibreOpBound`,
  `ccTensorBilinSymm` and `smoothCcToTensorHs` silently become autoImplicits and
  the error surfaces as "Function expected at SmoothCcTensor".
* The private abbrevs of `LowRegOperatorTime` (`metricH1`, `solH3`, `a1Op`,
  `a2Op`) are reducible, so their unfolded spellings
  (`tensorHs g 0 2 (1 : ℝ)`, `tensorHs g 0 2 ((1 : ℝ) + 2)`, …) unify with the
  producers' signatures from another module. The `show … from` idiom that
  `LowRegOperatorTime` uses for operator norms had to be reproduced verbatim in
  `liftA1Two_data`'s `hlin`.

## Progress

* `ricci_flow_unif_existence`: unstated in this file; still **0%**.
* Lane C: C0 complete **and unconditional** (`lowRadial_eq_self_sol`);
  C1 complete (hypothesis-parameterized, `LowRegLiftTwo`); C2 complete
  (hypothesis-parameterized); C3 — its unconditional half (`lowreg_force_lo`)
  and its upgrade (`lowreg_force_id`) are proved, with the single residual
  `N2` + `tensorHsInclusion ∘ N2 = lowRegN` isolated and shown to hold on the
  dense smooth core. Call the C3 *theorem* ~55% and the whole of Lane C ~80%,
  measured against what Lane C owes lane D.
* Lane B: the two coefficient packets are now normalized to the lift's
  exponents, but the lane is **not** finished: the three items listed above
  (completed `a1` square, low principal `a2` family + square, horizon smallness)
  are new, precisely-located gaps.
