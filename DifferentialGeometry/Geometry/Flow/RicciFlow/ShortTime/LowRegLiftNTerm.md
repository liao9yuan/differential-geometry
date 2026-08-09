# LowRegLiftNTerm

Lane C, the `N`-term residual of the `aHi = 2` rung: the **frozen forcing**
inputs `f0Hi`, `f0Lo` and the compatibility `hf0` that `lowreg_lift_two`
(`ShortTime/LowRegLiftTwo.lean`) consumes.

Status: **landed**, sorry-free, targeted build green (9891 jobs), all eighteen
declarations axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

## The finding that shaped the file

`lowreg_lift_two` has **no** `Nemytskii`-shaped `N`-hypothesis. Its hypothesis
list splits into

* order arithmetic (`hlo`, `hOrd`, `hOrdA1`, `hOrdSt`) and horizon (`hT`, `hT1`);
* the four coefficient families with their measurability / uniform bound /
  `MemLp` data and the two commuting squares — Lane B;
* the two contraction conditions `hsmallHi`, `hsmallLo` — `LowRegLiftSmall.lean`;
* the low affine fixed point `fLo`, `hfLo`;
* **`f0Hi`, `f0Lo`, `hf0`** — the only slots where the nonlinearity itself
  enters, and the ones this file produces.

That is exactly the frozen split of the R1τ ruling: writing
`N u = N 0 + (A2 u + A1 u) u` (`lowBaseN_frozen`, `lowCore_split`), the
state-dependent part is *already* carried by `A2`/`A1` (Lane B, landed), so the
whole `N`-side of the lift is the **static** term `N 0`.

## What `N 0` is, and why the lift is free on it

`N 0 = deTurckRHSSection g_bg g₀` (`deTurckRem_zero`, `nZero_eq_static`): Ricci
of `g₀` plus the `g_bg`-DeTurck vector-field term — no Laplacian, no third
metric under the ratified `g_bg := gBase`. Its spectral embedding

```
staticForce g₀ g_bg σ = smoothCcToTensorHs g₀ σ (deTurckRHSSection g_bg g₀)
```

exists at **every** real order `σ` and satisfies
`tensorHsInclusion hτσ (staticForce … σ) = staticForce … τ`
(`staticForce_incl`, one line from `tensorHsInclusion_smoothCcToTensorHs`).
Because the frozen forcing is a fixed smooth field, raising the Sobolev order
costs nothing and its `H^σ` norms are plain finite constants. This is why the
`N`-side of the adjacent-scale bootstrap is not an analytic frontier, in sharp
contrast with the *state-dependent* Nemytskii lift `N2` of `lowreg_force_id`
(`LowRegRealizeTwo.lean`), which is genuinely blocked.

## Contents

Reusable time layer (canonical home would be
`Analysis/Parabolic/TimeSobolev/BochnerL2.lean`; kept here so the low-level time
module is not invalidated while other lanes build):

* `timeConstL2 T x` — the constant-in-time class in `L²([0,T]; X)`;
* `timeConstL2_coeFn`, `norm_timeConstL2_le` (`‖·‖ ≤ ‖x‖ √T`, **reusing**
  `norm_toLp_le_bd` from `LowRegLiftSmall.lean` — not duplicated);
* `compLpL_timeConstL2` — any continuous linear map commutes with it;
* `timeL2Inclusion_const` — its scale-inclusion instance.

Frozen forcing layer:

* `staticForce`, `staticForce_incl`, `staticForce_congr` (exponent transport);
* `baseForceH2_eq_static` and `lowBaseForce_eq_static` — the two forcing objects
  the low-base layer already carries (`LowRegBaseForce.lean`,
  `DeTurckRemainderLowBaseFixedPoint.lean`) *are* this static field at orders
  `2` and `1`. Reuse, not a parallel hierarchy.
* `nZero_staticForce` (restatement of `nZero_eq_static` in this currency) and
  `nZero_h1_eq` (the same at the literal order `1` at which the lift is
  instantiated, through `tensorHsCongr`).

Endpoints:

* `liftForceHi` / `liftForceLo` — the `f0Hi` (`H²`) and `f0Lo` (`H¹`) inputs;
* **`lift_force_incl`** — the `hf0` slot verbatim, with the general-order
  `timeConst_static_incl` behind it;
* `norm_liftForceHi_le` / `norm_liftForceLo_le` — the size, closed in the frozen
  data: `‖f0‖ ≤ D √T` for any bound `D` on the static field's `H²` (resp. `H¹`)
  norm. No `A1`/`A2` constant enters.
* `liftForceLo_lowBase` — agreement with `lowBaseForce` at `g_bg := g`.

## Verification

* Focused check green; targeted module build green (9891 jobs).
* `#print axioms` on all eighteen declarations: `[propext, Classical.choice,
  Quot.sound]`.
* **Fit-tested by elaboration** (scratch probe, not committed): `lowreg_lift_two`
  instantiated at `aLo := (1 : ℝ)`, `aHi := (2 : ℝ)` accepts
  `liftForceHi g g_bg T`, `liftForceLo g g_bg T` and `lift_force_incl g g_bg T`
  in its `f0Hi` / `f0Lo` / `hf0` slots with no transport and no restatement.
  The `hOrd` proof argument is absorbed by proof irrelevance (a separate probe
  checks acceptance of an arbitrary `hOrd : (1 : ℝ) ≤ (2 : ℝ)`).

## What is NOT discharged here (honest boundary)

1. **`hfLo`.** `lowreg_partial_sol` exports the low forcing in the *Nemytskii*
   form `gforce =ᵐ lowRegN ∘ field`, whereas `lowreg_lift_two` wants the
   *affine* form `fLo = nonautL2Map … fLo + f0Lo`. Bridging them is the
   ball-level completion of `lowCore_split` / `lowBaseN_frozen`: one needs
   `lowRegN v = lowBaseForce + lowBaseA v v` for **every** `v` in the state
   ball, not only on the smooth core. That is a dense-extension statement about
   the *coefficient* maps (`lowA2Lo`, `lowA1Lo` are themselves `Dense.extend`s),
   i.e. Lane B/A territory, not a statement about `N 0`.
2. **The `A1` half of the lift** (`hA1Hi`/`hA1Lo`, `hA1compat`) remains
   conditional on the Lane-A affine bound (`c1_pair_lip` / `a1Hi_lin`).
3. **`N2` of `lowreg_force_id`.** The *state-dependent* `H^σ`-valued Nemytskii
   lift is still open and is a different object from the frozen forcing. Note
   the ruled frozen split does **not** produce it at the state ball: the
   high-rung second-order coefficient `lowA2Hi` is `H4 →L H2`, so
   `A2Hi(v) v` needs `v ∈ H4` while `lowerState g₀ 1 R` carries only `H3`. The
   split closes the `N`-term at the **time-field** level (where maximal
   regularity supplies the extra derivatives), which is precisely the `hfLo`
   route of item 1 — not the pointwise `N2` route.
4. A bound on `‖staticForce g₀ g_bg (2 : ℝ)‖` by class data (the `H²` sibling of
   `nZeroC`) is left as the caller's input `D`; it is `E3`'s `Ksup` at order
   `≤ 2` and is not available in the tree.

## Lean lessons

* `tensorHsCongr` is `by cases h; exact LinearIsometryEquiv.refl`, so a
  naturality statement about it must be phrased with **variable** exponents
  (`{a b : ℝ} (hab : a = b)`) and closed by `cases hab; rfl`. It cannot be
  proved directly at the closed pair `((1 : ℕ) : ℝ)` / `(1 : ℝ)`, since `cases`
  has no free variable to substitute (and those two are *not* `rfl`-equal).
* `ccTensorToHs g₀ 2 σ` and `smoothCcToTensorHs g₀ σ` have literally the same
  `coeff` field, so `tensorHs.ext (funext fun _ => rfl)` bridges them; this is
  the fifth rfl-copy of that identification in the tree (dedup chip already
  filed under planner update No. 64).
* Rewriting under a proof argument that was produced by a different `by norm_num`
  is unreliable (`kabstract` is syntactic); route through
  `congrArg f (lemma … _ _)` and let unification pick the proof arguments. Both
  `baseForceH2_eq_static` and `nZero_h1_eq` are written that way.

## Progress

* `ricci_flow_unif_existence`: unstated here; still **0%**.
* Lane C: C0/C1/C2 complete, C3's unconditional half complete. The `N`-term of
  the `aHi = 2` rung — the `f0Hi`/`f0Lo`/`hf0` triple — is now **complete and
  unconditional**. What remains before `lowreg_lift_two` can be *applied* is
  Lane-A's first-order affine bound and the `hfLo` bridge of item 1 above.
