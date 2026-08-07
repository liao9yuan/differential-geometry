# UnifBgLift

## Role

`BgLiftData` is the class-first scalar layer for the arbitrary-fixed-background
adjacent-scale lift.  It deliberately contains no metricwise coefficient maps
and no orbit witness.

The force margin uses
`lowregStateRad K.top K.slope K.outer K.realize / 4`, exactly the bound exported
by `IsLowSolveBg.force_bound`.  It does not use `K.realize / 4`.

The coefficient radius lies between the realized state radius and
`K.realize`, so the low-bound realization certificate applies throughout the
whole coefficient-validity ball.

The file also defines the positive common low/lift horizon, exports its two
projection inequalities to the low-solve and lift horizons, and connects an
`IsLowSolveBg` force estimate to the stored `forceCap`.

## Which theorems read `zero` and `slope` (ledger №198)

Checked while BG-2 considered restating the A1 bound shape; recorded so the
question is not re-opened:

- `horizon = lowregLiftHorizon' contract zero` reads `zero` and NOT `slope`;
  `horizon_pos` therefore consumes `zero_nonneg`, `horizon_le_one` consumes
  nothing, and all four `commonHorizon_*` read `zero` only through `horizon`.
- `slope` is read by exactly one field, `force_margin`
  (`6 * (2 * slope * forceCap) ≤ (1 - contract) / 2`).
- `forceCap` / `force_le_cap` are independent of both.

This is not an accident of naming: `zero`/`slope` are the verbatim diagonal
`Z`/`L` of `lowreg_apply_two` (`LowRegApplyTwo.lean:309–312`), `horizon` mirrors
its `hTle : T ≤ lowregLiftHorizon' c Z`, and `force_margin` mirrors its
`hmargin : 6 * (2 * L * ‖f‖) ≤ (1 - c) / 2`.  The `√T`-carrying constant is
absorbed by the horizon and the slope by the `T`-free margin, so the two
constants are not interchangeable and neither may be dropped.  BG-2 left the
scalar layer unchanged; see `LowRegBgLift.md` for why the affine shape survived
the №196 refutation.

## Verification

Focused verification passed.

## Where a class-uniform `coeffRadius` has to come from (G3, ledger №198)

BG-2 was also asked to give `coeffRadius` a class-uniform closed-formula lower
bound below the three per-`g` coefficient radii (`radialA1HiBg_pair`,
`radialA1Bg_pair`, `radialA2Bg_lip`).  It was not landed, for two reasons worth
keeping.

First, a logical one.  Those three radii are `∃ ρ₀ > 0, ∀ ρ ≤ ρ₀, P(ρ)`, so
they are not terms of their own statements and validity is downward closed —
the infimum of valid radii is `0`, and "sits under the existential radii" is not
a statable proposition.  The statable goal is
`∃ ρ_class > 0, ∀ g in class, ∀ ρ ≤ ρ_class, P_g(ρ)`, i.e. the shape
`inv_coeff_h2_unif` (`UnifInvCoeffH2.lean:60`) already uses.

Second, a structural one, and it is good news.  A read-only trace shows the
radius arithmetic is fully explicit everywhere — `min`/verbatim, with no
`Classical.choose`, compactness, or unquantified cutoff — and all three chains
converge on a single bottom node, `inv_coeff_h2`
(`DeTurck/PrincipalCoeffH2.lean:202`), whose radius is `min 1 (4 * Cop)⁻¹`
(`:229`).  The only opaque ingredient is the scalar `Cop`, which comes from
`hs2_op_bound` and ultimately a `choose`+`sup'` over a partition-of-unity atlas
in `SobolevEmbeddingSharpC0JetSum.lean:748–749`.  That node has already been
replaced class-uniformly: `inv_coeff_h2_unif` uses the identical formula with
`Cop := hs2OpActionC (morreyTwoC gBase Λ) Kcurv.rankTwo`, which is
`lowRealizeData` quality.

So G3 is not blocked by mathematics but by threading.  The existing 54 `_unif`
theorems in `ShortTime/` have reached the *bound* family and not a single
`_pair_`/`_lip` node; about 55 nodes (`invCoeff_h2_lip` → the trace family →
the `*_pair_h1/h2/h3` families → `a1Hi_bg_pair`/`a1Lo_bg_pair`/`a2_pair_lip`)
lie in between, hosted in memory-walled monoliths and therefore to be rebuilt as
`_unif` siblings here.  Highest-leverage entry point, common to all three
chains: `invCoeff_h2_lip_unif`, in a new `ShortTime/UnifInvCoeffLip.lean`.

## Remaining frontier

The metricwise coefficient certificate and realized-orbit package remain
separate.  Their honest construction still needs the arbitrary-background high
A1 pair and a class-first A2 contraction packet, plus the class-uniform
coefficient radius above.  The scalar layer itself was NOT edited by BG-2: the
affine `zero`/`slope` pair survives the №196 refutation because the refutation
lands on `IsBgA1At`'s core fields, not on the bound shape.
