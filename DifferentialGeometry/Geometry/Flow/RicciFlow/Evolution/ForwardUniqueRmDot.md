# `ForwardUniqueRmDot.lean` — Route-K bricks K2.1 + K2.6-core

Status: **OUTCOME (A)** — both parts delivered, 691 lines, 16 public + 9 private
declarations, **0 sorry**. Focused check, targeted module build, and an independent
`#print axioms` re-run on all 15 public declarations are all clean (standard axiom set
`propext / Classical.choice / Quot.sound` only). File is warning-free.

## What was built

### Part 1 (K2.1) — the `hS` feed, mirroring K1C-a one rank up

`ForwardUniqueEnergy.lean` (K3) consumes

```
hS : ∀ v : Fin 4 → TangentSpace I x,
  HasDerivAt (fun r => rmDiffLowAt (g₁ r) (g₂ r) x v) (Sdot t x v) t
```

`rmDiffLow_hasDerivAt` produces exactly that shape. The structure is a verbatim rank-4
mirror of `connDiffLow_hasDerivAt`:

* `rmDiffVec g₁ g₂ x := riemannOp (metricCov g₁) x − riemannOp (metricCov g₂) x`
  — the raised curvature difference as a genuine trilinear continuous map. This is the
  exact `(1,3)` analogue of K1C's `CovariantDerivative.difference`, and the reason no
  hypothesis-supplied "raised difference" carrier was needed.
* `lowerTri q A` — `(X,Y,Z,W) ↦ q(A X Y Z, W)` for an **arbitrary** `(0,2)` tensor `q`.
* `rmDiffDot g₁ g₂ Sdot t x := (−2) • lowerTri Ric₁ (rmDiffVec) + lowerTri g₁ (Sdot x)`.
* `rmDiffLowAt_eq_lowerTri` — `S₀₄` *is* `lowerTri (metricTensorField g₁ x) (rmDiffVec …)`.

**K1C's finding reproduced: `hPDE₂` is NOT needed.** Only `g₁` lowers, so the adapter
consumes the Ricci-flow equation of the carrier `g₁` alone plus

```
hRm : ∀ X Y Z, HasDerivAt (fun r => rmDiffVec (g₁ r) (g₂ r) x X Y Z) (Sdot x X Y Z) t
```

This is the *invariant* form, chosen over the two Uhlenbeck component hypotheses for the
K5 assembly: K3's `hS` is stated at every slot-vector `v`, so a component-level hypothesis
would have to be lifted through a frame anyway (K1C's `bilinOfComp` route), whereas the
invariant form plugs straight in. The frame → invariant lift for `hRm` (the quadrilinear
analogue of `connDiffVec_hasDerivAt` + `bilinOfComp`) is **not** in this file; it is the
same construction one rank up and should be a separate small brick if K5 needs it.

### Part 2 (K2.6-core) — the divergence-form capstone, componentwise

`rmDiffComp_deriv`: from the two Uhlenbeck hypotheses (planner ruling R1 — one per flow,
`Riemann04BTensorWithRicciDriftEvolutionInFrameOn`, `Uhlenbeck.lean:727`), subtraction plus
K2.3's spatial identity gives

```
∂ₜ(Rm₁ − Rm₂) = Δ_{g₁}(T₁ − T₂) + div_{g₁}(lapDiffFlux g₁ g₂ T₂) + rmDotRem
```

in the interface's own `HasDerivWithinAt … D.carrier t` convention. The algebraic core is

```
Δ₁T₁ − Δ₂T₂ = Δ₁(T₁ − T₂) + (Δ₁T₂ − Δ₂T₂)      -- roughLapSub_apply
            = Δ₁(T₁ − T₂) + div₁U + lapDiffRem  -- lapDiff_eq_div_flux (K2.3), evaluated
```

`rmDotRem` collects: K2.3's `lapDiffRem` of the **background** field `T₂`, the `B`-quadratic
difference termwise, and the Ricci-drift difference. `driftDiff_split` exhibits the last as
`(Ric₁−Ric₂) ∗ Rm₁ + Ric₂ ∗ (Rm₁−Rm₂)` so the "difference × background" shape needed by a
later K2.5-pattern norm bound is manifest. **The bound itself is deliberately not here.**

`rmLowComp_deriv` reads the same statement on the Kotschwar carrier `S₀₄`.

## Realization-hypothesis classification (the mission's flagged hard part)

Two kinds of realization input appear, and they are **not** of equal status.

1. `hL₁ / hL₂` — *the supplied `roughLapRm04` family is the frame reading of the intrinsic
   `roughLap0SField` of that flow's own metric and field.*
   **Classification: benign realization, no mathematical content beyond naming.** The
   Uhlenbeck interface leaves `roughLapRm04` a free component family; `hL₁`/`hL₂` simply
   say which operator it realizes. No existing predicate fits (`rm04Comp`
   `Evolution/Ricci/Trace.lean:469` and `RmRealizationBridge*.lean` realize the *curvature*
   family, not its rough Laplacian), so they are stated as plain `∀`-hypotheses at the one
   time `t` and one index tuple actually used — the weakest honest form. Both are pointwise
   equalities of reals; no smoothness, no frame regularity.

2. `hreal` (in `rmLowComp_deriv`) — *the two supplied families differ by the frame reading
   of `rmDiffLowAt`.*
   **Classification: a genuine standing input, strictly beyond ruling R1's two hypotheses.**
   This is the one real finding of the brick, and the planner should see it:

   > The two honest Uhlenbeck interfaces describe each flow's **own-metric-lowered**
   > `Rm04ᵢ = gᵢ(Rm¹³ᵢ ·, ·)`. Their difference is `metricRm04At g₁ − metricRm04At g₂`,
   > which is **not** `S₀₄ = rmDiffLowAt g₁ g₂ = metricRm04At g₁ − g₁(Rm¹³₂ ·, ·)`. The gap
   > is the `h₀₂`-lowered background curvature, `(g₁ − g₂)(Rm¹³₂ ·, ·)` — an `O(|h₀₂|)`
   > term (`rm2Low_eq_sub` is the exact bookkeeping).

   Consequences, both real:
   * ∂ₜ of the gap is fine for the energy (`∂ₜh = O(|S|)`, `h·∂ₜRm₂ = O(|h|)·background`).
   * `Δ₁` of the gap is **not** fine: it produces `∇¹∇¹h₀₂`, a second derivative of the
     metric difference, which the Kotschwar energy does not control. So one cannot simply
     swap carriers after the fact.

   Therefore either (i) the flow-2 interface must be taken at the `g₁`-lowered
   representative — a *different* standing input from the standard Uhlenbeck equation, and
   one whose honest producer is K2-B at mixed lowering; or (ii) K3's energy carrier is
   changed to the own-metric difference `metricRm04At g₁ − metricRm04At g₂`, which would
   ripple into `ForwardUniqueFields.lean`'s `rmDiffSq` and all of K2.4/K2.5. **This is a
   planner decision, not an executor one.** `rmDiffComp_deriv` is stated generically in
   `T₁ T₂` precisely so that either choice instantiates it without restatement.

Note the asymmetry: Part 1 (`rmDiffLow_hasDerivAt`) has **no** such gap — it works directly
on `S₀₄` via the raised difference, and is unconditional given `hPDE₁` + `hRm`.

## Design choices and why

* **`riemannOp` over a hypothesis-supplied raised carrier.** `riemannOp` (Curvature/
  CurvatureOperator/CurvatureBundling.lean:803) is the canonical bundled trilinear
  `T×T×V → V` curvature. Using it keeps `rmDiffDot` a closed definition with zero new
  frontier, exactly as K1C used `CovariantDerivative.difference`. The bridge to the
  `(0,4)` carrier is `riemannCurvature04At_apply_const` composed with
  `riemannCurvatureAux_tangentConst_eq_riemannOp` (MetricLeviCivitaReconcile.lean:111).
* **Cost paid: `[BoundarylessManifold I M]`** — required by that reconcile lemma. It is
  ubiquitous in this repo (712 files) and true in the Ricci-flow setting, but it is one
  instance more than the other Route-K lane files carry; K5 must discharge it.
* **`lowerTri` reuses K1C's `lowerBilin`** rather than rebuilding the tower: one
  `uncurryLeft` over the first slot with `X ↦ lowerBilin q (A X)`, then a single
  `domDomCongr (Equiv.swap 1 2)` to fix slot order. That needed only `lowerBilin_add` /
  `lowerBilin_smul` (linearity in the lowered bilinear map), which reduce to slot-`0`
  multilinearity of `q` (`tensor02_add_left` / `tensor02_smul_left`).
* **Generic-in-`T₁ T₂` capstone** rather than a hard-wired `S₀₄` one — see the
  classification above; this is what makes the pending planner decision cheap.

## Lean lessons (durable)

* **`LeviCivita_isContMDiff` is `InnerProductSpace ℝ E`-tainted.** The obvious way to get
  the `ContMDiffCovariantDerivative (metricCov g) ∞` instance that `riemannOp` needs is
  that producer, and it drags the forbidden model-space inner product in. The clean route
  is the *local* statement specialised to `univ`:
  `CovariantDerivative.contMDiffCovariantDerivativeOn_univ_iff.mp (metricCov_smooth g isOpen_univ)`
  — `NormedSpace`-only. Kept as a `private instance` so it never leaks. **Add to the
  campaign-end dedup list**: this is the 4th occurrence of the `InnerProductSpace`-at-the-
  producer pattern (cf. №3, №8); the real fix is an `omit` on `LeviCivita_isContMDiff`.
* **`ContMDiffCovariantDerivative` is a *Mathlib root-namespace* class**
  (`_root_.CovariantDerivative.ContMDiffCovariantDerivative`, Mathlib
  `Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean:409`), **not** a repo
  declaration under `DifferentialGeometry.Integral.Connection`. Grepping the repo for
  `class ContMDiffCovariantDerivative` finds nothing and wastes a cycle — search
  `.lake/packages/mathlib` too.
* **CLM towers `T →L T →L T →L T` blow the typeclass budget.** `AddGroup` synthesis on that
  type times out at the defaults; `sub_self _` with a metavariable is worse (it also times
  out at `isDefEq`). Fixes that worked: `set_option synthInstance.maxHeartbeats 1000000`
  (+ `maxHeartbeats` for the one `_self` lemma) and **always give `sub_self` its explicit
  argument** so the type is known before instance search starts.
* **Instance-diamond recurrence (K1C's lesson, confirmed again):** `rw [rmDiffVec]` produced
  a goal displaying `riemannOp … − riemannOp …` yet `rw [sub_self]` failed with "did not
  find `?a - ?a`" — the `Sub` instances are defeq but not syntactically equal. Cross with
  `exact`, never `rw`/`simp`.
* **`congr 1` closes more than expected** after `lowerBilin_apply`/`lowerTriOut_apply`: the
  `Fin.tail`/`Equiv.swap` index reductions are already rfl, so the habitual
  `funext a; fin_cases a <;> simp` tail errors with "No goals".
* **`metricTensorField_apply` leaves `if 0 = 0`/`if 1 = 0` unreduced.** Hoist the pattern
  once (`metricField_slot0` here) instead of sprinkling `; simp` — it also makes the
  `tensor02_expand` sum steps one-liners.
* **`rw [hv]` where `hv : v = vec4 (v 0) (v 1) (v 2) (v 3)` self-applies** and loops. State
  the eta lemma in the *other* direction (`vec4 (v 0) … = v`) and rewrite the specialized
  `_apply_const` fact, not the goal.
* **Do not append Lean text with PowerShell `Get-Content -Raw | Add-Content -Encoding utf8`** —
  it round-trips UTF-8 through ANSI and mojibakes every subscript (`g₁` → garbage), which
  surfaces only as a pile of "expected token" parse errors. Use Python with explicit
  `encoding='utf-8'`.

## Reuse / adaptation record

* **Reused directly:** `lowerBilin` + `tensor02_expand` (K1C `ForwardUniqueConnDot.lean`);
  `rmDiffLowAt`, `metricRm04At` (`ForwardUniqueFields.lean`); `lapDiff_eq_div_flux`,
  `lapDiffFlux`, `lapDiffRem`, `covDiv0SField`, `roughLap0SField`, `metricNabla0S_sub`,
  `covDiv0SField_sub` (K2.3 `ForwardUniqueRmDiff.lean`);
  `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`, `riemann04RicciDriftInFrame`,
  `FourComp`, `MatrixComp` (`Uhlenbeck.lean`); `riemannOp`,
  `riemannCurvature04At_apply_const`, `riemannCurvatureAux_tangentConst_eq_riemannOp`.
* **Adapted:** `connDiffDot` / `connDiffLow_hasDerivAt` were mirrored rank 3 → rank 4, not
  imported; `rmLapDiff_div_flux` is rank-4-specialised, so the generic
  `lapDiff_eq_div_flux` was used instead and evaluated pointwise here
  (`lapDiffFlux_apply_vec`).
* **Not used:** `rm04Comp` / `RmRealizationBridge*.lean` — they realize the curvature
  family, not its rough Laplacian, so they do not fit `hL₁`/`hL₂`. No new predicate class
  was invented; the realization inputs are plain `∀`-hypotheses per the mission.

## Next smallest steps

1. **Planner decision** on the carrier gap above (own-metric difference vs `g₁`-lowered
   representative). Everything downstream of K2 depends on it.
2. The frame → invariant lift for `hRm` (quadrilinear `bilinOfComp` analogue), if K5 needs
   to feed Part 1 from component-level data.
3. K2.5-pattern norm bound for `rmDotRem` (three summands, `driftDiff_split` already
   supplies the bilinear split of the hardest one).
4. Relocations listed in the file's `Relocation TODO`.
