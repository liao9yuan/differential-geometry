# LowRegSmoothBridge

## Role

This file supplies the first faithful geometric bridge out of the genuine
low-regularity fixed-point nonlinearity.  It never replaces the solver horizon
by a later solution-dependent subinterval.

## Source status

- `symm_h2_of_state` transfers the lower `H2` state bound to the symmetrized
  smooth representative used by `coreN`.
- `lowRegN_on_core` applies `Dense.extend_eq` using the core continuity exported
  by `lowreg_partial_sol`'s construction.
- `lowRegN_on_smooth` identifies the dense extension with the concrete
  `deTurckSmoothN` value of a smooth representative.
- `lowRegSeedMass` (added by Brick A of the rung-3 campaign, ledger №157/№158)
  is the `a = 1` static seed-mass producer: every finite `(1+λ)^n`-weighted mode
  mass of `𝒩(0) = lowRegN … ⟨0, _⟩` is bounded by `Cseed n ^ 2`, with
  `Cseed n = ‖smoothCcToTensorHs g₀ n (deTurckSmoothRemainder g₀ g_bg (symmS g₀ 0))‖`
  — a `(g₀, g_bg, δ)`-only constant, hence free of the mode set and so of any
  Galerkin level `N`.  This is what the rung Grönwall's additive seed slot
  consumes (`(1/2ε)‖𝒩(0)‖² + c_cls` in PSTOP §6.4).
- `lowReg_force_smooth` transports the fixed-point forcing identity to the
  genuine smooth Ricci--DeTurck forcing on the same measure `timeMeasure T`.
  Its smooth-family and ball pins are geometric data to be produced by the
  remaining bootstrap, not a claimed existence result.

## Notes on `lowRegSeedMass`

Route — three links, all pre-existing:

1. the zero state is the embed of the zero smooth tensor (`tensorHs.ext` plus
   `map_zero` on `SmoothCcTensor.toL2`), so the subtype element
   `⟨0, zero_mem_lowerState …⟩` equals `⟨smoothCcToTensorHs g₀ 3 0, hS⟩` by
   `Subtype.ext`;
2. `lowRegN_on_smooth` at `S = 0` evaluates the dense extension there, giving
   `deTurckSmoothN g₀ g_bg 1 (symmS g₀ 0)`, whose coordinates are by
   `deTurckSmoothN_coeff` the `L²` coordinates of the genuine smooth remainder;
3. `cc_partial_le_norm` (`SobolevScale/IteratedCovGradHsJetBound.lean:165`) is
   the finite-set Bessel truncation at the `ccTensorToHs` norm; the rank-`(0,2)`
   bridge `ccTensorToHs g₀ 2 σ = smoothCcToTensorHs g₀ σ` is `tensorHs.ext` of
   `rfl`, the same bridge `exists_iteratedCovGrad_sum_le_smoothCcToTensorHs`
   already uses.

**Exhibit note (over-count).**  The dispatch expected the finite-set weighted
Bessel bound (`JOINT-BESSEL`) to be a genuinely new lemma, its only near-producer
being the private, `λ^j`/tsum-shaped `mode_le_jet`.  It exists twice already:
`cc_partial_le_norm` (public, exactly the dispatched `SmoothCcTensor` shape) and
the fully general `tensorHs`-level `weight_sum_le_normSq`
(`Spectral/Intrinsic/TensorHsInterpolationLimit.lean:210`, docstring
"Finite-set Bessel truncation in `Hˢ`", and its own docstring already names the
Galerkin use).  Only the first is in this file's import closure.  No new lemma
was written.

The `2·finrank + 10 ≤ a` gate of `deTurckGalerkinForcing_seed_mass`
(`HeatSemigroup/GalerkinParabolicEnergyDeTurck.lean:416`) is used there only to
identify the abstract `deTurckSobolevNHa2` at the zero state with a smooth
remainder; at the low base the dense extension supplies that identification
directly, so no supercriticality hypothesis appears in `lowRegSeedMass`.

Shape decision recorded: the statement quantifies over an ARBITRARY finite mode
set `F` and an arbitrary natural order `n`, not over `eigenIdxFinset N` at a
fixed order.  That is strictly stronger, is what `cc_partial_le_norm` proves
without loss, and leaves the consumer free to choose its truncation family.  The
constant is per-datum (it depends on `g₀`, `g_bg`, `δ`); the rung needs
`N`-freeness, not datum-freeness.

Lean lesson: `TensorEigenIdx` is ambiguous in this file (both
`Analysis.Parabolic.TensorHeatEquation` and `Analysis.Parabolic.TensorSpectral`
are open) — spell the `TensorHeatEquation` one out.  Also,
`TensorHsInterpolationLimit` is NOT in this file's import closure even though it
is only two hops away in the tree; check reachability before reaching for a
lemma there.

## Canonical API audit and exact frontier

The current `ForcingFiniteOrderTimeRegularity`,
`ForcingCoordinateTimeRegularity`, and
`MaxRegSolutionJointlySmooth` producers are specialized to a high base order
`a` (their hypotheses include `2 * dim + 10 <= a` or stronger) and return an
unknown `d <= T`.  The new fixed point has base order `a = 1`.  Therefore those
theorems cannot be applied directly, and their returned `d` cannot be renamed
to the solver's horizon without violating the uniform-horizon requirement.

The smallest next analytic producer is a low-regularity, same-horizon analogue
of the finite-order forcing bootstrap.  In consumer shape it must take the
`a = 1` Duhamel field, its `lowRegN` forcing equality and state-ball membership
on `timeMeasure T`, and return on `Set.Icc 0 T` a smooth representative family
`F` with all-order spectral jet-mass bounds, the spectral pin
`smoothCcToTensorHs g0 3 (F t) = field t`, and the lower `H2` ball bound for
every `t`.  Its proof must choose any auxiliary smoothing budget before the
final solver horizon, from explicitly controlled constants; it may not first
solve on `T` and then return an unknown solution-dependent `d <= T`.

Once that producer exists, `lowReg_force_smooth` feeds the existing
`RealizeTransport` and `DeTurckRicciPde` identities, after which the canonical
joint chart-Gram reconstruction can be used on the same `T`.

This remains fixed-`g0`, dimension-three machinery.  No generic-family
uniformization and neither public endpoint theorem is claimed here.

Focused Lean verification passed without local warnings on 2026-07-27, and
again after `lowRegSeedMass` was added (2026-08-05), together with a targeted
build of this module and an axiom census run (`ShortTime/ScratchIdentCensus.lean`)
reporting `[propext, Classical.choice, Quot.sound]` only.  The bridge is
therefore checked against the live `lowreg_partial_sol` interface.  No `sorry`,
`admit`, axiom, new class, instance, or notation is introduced.
