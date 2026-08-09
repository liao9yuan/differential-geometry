# LowRegLiftTwo

Lane C of the `(N)` / `ricci_flow_unif_existence` endgame: the solver-side
bricks `lowRadial_eq_self_along_sol` (C0) and `lowreg_lift_two` (C1).

## What is in this file

* `lowRadialHs_eq_self`, `lowRadialH3_eq_self` — the two honest `eq_self`
  bridges named as prerequisites in `DeTurckRemainderLowBaseFixedPoint.md`.
* `lowRadial_eq_self_along_sol` — the same two identities almost everywhere
  along a time-dependent `H3` state path.
* `liftCompat_congr` — transports a `pair`-shaped commuting inclusion square
  from literal domain exponents to the arithmetic ones the lift needs.
* `lowreg_lift_two` — the one-step adjacent-scale bootstrap through
  `nonautL2_lift`, on the unchanged horizon, plus the two *pointwise*
  a.e. inclusion identities that the engine does not produce.

All five are sorry-free and axiom-clean (`propext`, `Classical.choice`,
`Quot.sound` only). Focused verification passed, and a real targeted build of
the module passed as well (the focused `lake env lean` result alone is not
trusted for green).

## Mathematical findings

**Radialization is symmetrize-then-retract, not retract.** `lowRadialH3` is
`lowScaleCutoff (incl32) ρ ∘ symmHs`, and `lowRadialHs` is
`ballRetraction ρ ∘ symmHs`. So an `H2` ball bound alone does **not** make
either map the identity — this is exactly the warning already recorded in
`DeTurckRemainderLowBaseFixedPoint.md`, and it is why `hsymm` is a genuine
hypothesis of `lowRadial_eq_self_along_sol` and not a derived fact. The
`H2`-level symmetry needed by the second conclusion is *derived* from the
`H3`-level one through `symmHs_incl`, so only one symmetry input is required.

`lowRadial_eq_self_along_sol` is stated for an arbitrary path
`u : ℝ → tensorHs g 0 2 3` rather than for `maxRegDuhamelSolField` directly.
That is deliberate: the solver's field lives at the exponent `((1 : ℕ) : ℝ) + 2`,
not at the literal `(3 : ℝ)` that the whole `lowRadial*` layer uses, and tying
the lemma to the solver would have baked an exponent normalization into a
statement that does not need one.

**The remaining honest input is symmetry preservation.** Nothing here proves
that the rough fixed-point solution is spectrally symmetric. The plausible
route is that the forcing `N(field)` is symmetric and that `symmHs` commutes
with the spectral heat semigroup, hence with `maxRegDuhamelSolField`.

*Update (2026-07-30, `LowRegSymmPreserve.lean`):* that commutation is now
**proved** and axiom-clean. `symmHs_coeff` shows spectral symmetrization is
block diagonal in the rough-Laplacian eigenbasis (via slot-swap equivariance,
`SlotSwapEquivariance.lean`, plus finiteness of eigenvalue blocks), and
`symmHs_duhamel_comm` / `lowreg_sol_symm` give
`∀ᵐ t, symmHs (maxRegDuhamelSolField … 0 f t) = maxRegDuhamelSolField … 0 f t`
from spectral symmetry of the forcing alone. See `LowRegSymmPreserve.md`.

*Update (2026-07-30, `LowRegRHSSymm.lean`):* the forcing side is now proved too
(`symmS_remSymmS`: `deTurckSmoothRemainder g₀ g_bg (symmS T)` is slot-symmetric),
and the exponent transport from `((1 : ℕ) : ℝ) + 2` to the literal `(3 : ℝ)` is
done (`symmHs_congr`, `lowreg_sol_symm_h3`). **`lowreg_sol_symm_h3` has exactly
the shape of the `hsymm` argument of `lowRadial_eq_self_along_sol`**, so that
input is no longer a frontier; it only needs a `lowreg_partial_sol` witness for
its continuity/forcing hypotheses. See `LowRegRHSSymm.md`.

## The exponent-normalization obstruction (found here, now solved)

`nonautL2_lift` indexes its low scale as `a - 1` and its state scales as
`a + 1`, `a + 2`. The Time-layer families are at *literal* orders
(`lowA2Hi : H4 →L H2`, `lowA1Hi : H3 →L H2`, `lowA2Lo : H3 →L H1`,
`lowA1Lo : H2 →L H1`, and `lowRegA2Time : H4 →L H2`). Since `tensorHs` is
indexed by a **real** exponent, `(2 : ℝ) + 2` and `(4 : ℝ)` are equal but not
definitionally equal, and unification cannot solve `?a + 2 =?= 4`. So the two
sides cannot be connected by `apply`, by `subst`, or by choosing a clever
instantiation — an explicit transport is required.

What *does* work, and is used here:

* Only the low order needs a name. Writing the theorem with `aLo` and
  `hlo : aLo = aHi - 1` lets `subst hlo` put the goal in exactly the engine's
  shape (`aLo` is a free variable and does not occur in `aHi - 1`, so the
  substitution is legal). Trying instead to free the *derived* exponents
  (`hiSt = aHi + 2`, …) does **not** work: the statement is elaborated before
  any `subst`, and `maxRegDuhamelSolField aHi` forces its field into
  `tensorHs (aHi + 2)`, so a separate `hiSt` cannot appear in the same
  statement without `▸` casts.
* Instantiating at `aLo := (1 : ℝ)`, `aHi := (2 : ℝ)` already puts both forcing
  scales at literal orders, and the outer inclusion order `aLo ≤ aHi` is
  literally the `1 ≤ 2` of `a1_pair` / `a2_pair`. Only four normalizations
  survive: `2 + 2 ≡ 4`, `2 + 1 ≡ 3`, `1 + 2 ≡ 3`, `1 + 1 ≡ 2`, and they touch
  only the *domains* of the four coefficient families.
* `tensorHsCongr` / `tensorHsCongrL` (new, in
  `Analysis/Spectral/Tensor/SobolevScale/ExponentCongr.lean`) supply the
  transport, and `liftCompat_congr` moves a pair-shaped square across it. This
  was validated end-to-end on an `a2_pair`-shaped square before being promoted
  from a throwaway probe to a lemma.

## Lean lessons

* Proof arguments of `tensorHsInclusion` / `symmHs` differ syntactically
  between files but are definitionally equal by proof irrelevance. `rw` is not
  reliable across such a mismatch when the head symbol also differs (a private
  `abbrev` such as `incl32` has its *own* constant as head, so `kabstract` will
  not match it against `tensorHsInclusion`). Routing through `Eq.trans` /
  `congrArg` / `refine … .trans ?_` performs a defeq check instead and is
  robust; that is why the two `eq_self` proofs avoid `rw`.
* To turn an `L2`-class equality into a pointwise a.e. one, rewrite the
  *free variable* side first (`rw [← hforce]` on the goal, where `fLo` is an
  fvar) and then discharge with the `coeFn_compLpL` equality. Rewriting the
  compound side directly runs into the same proof-argument matching problem.
* Naturality of an exponent transport is definitional: `cases` on the exponent
  equality turns `tensorHsCongr` into `LinearIsometryEquiv.refl` and every
  compatibility statement closes by `rfl`. Use `cases`, not `subst`, when the
  equality proof itself occurs in the goal.

## Progress

* `ricci_flow_unif_existence`: unstated in this file; still 0%.
* Lane C bricks: C0 (`lowRadial_eq_self_along_sol`) complete modulo its
  symmetry input; C1 (`lowreg_lift_two`) complete as a hypothesis-parameterized
  theorem. C2 (`lowreg_realize_two`) and C3 (`lowreg_force_id`) landed in
  `LowRegRealizeTwo.lean` (2026-07-30) — see `LowRegRealizeTwo.md`; that file
  also discharges C0's symmetry input unconditionally
  (`lowRadial_eq_self_sol`), and records the three Lane-B gaps that still block
  applying `lowreg_lift_two` at `aHi = 2`.
* **`hsmallHi` / `hsmallLo` are no longer a frontier** (2026-07-30,
  `LowRegLiftSmall.lean`). `lowregLiftHorizon c M` is the closed horizon
  `min 1 (min ((1 - c)/(2(c + 1))) ((1 - c)²/(64 (M + 1)²)))`, and
  `lift_smallness` / `lift_small_two_bd` produce *both* smallness hypotheses
  verbatim from `C₂ ≤ c < 1` and either `‖A1‖_{L²(0,T)} ≤ M √T` or a pointwise
  `‖A1 t‖ ≤ M`. Note the `C₂` part is a *radius* condition, not a horizon one:
  `C₂(1 + T) → C₂` as `T → 0`. See `LowRegLiftSmall.md`.
* `lowreg_lift_two` cannot yet be *applied*: every coefficient-family input is
  a hypothesis parameter, and the producers are Lane B (`lowRegA1Time` /
  `lowRegA1_memLp`, `lowRegA2Total_data`), which does not exist. In particular
  the `MemLp A1 2` input is downstream of the Lane A linear-growth bound
  `a1Hi_lin`; with the current degree-six envelope it is false.
