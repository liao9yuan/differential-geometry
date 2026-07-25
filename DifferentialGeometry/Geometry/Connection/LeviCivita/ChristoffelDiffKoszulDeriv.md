# ChristoffelDiffKoszulDeriv — B2 P2.a (differentiated Christoffel-difference Koszul)

Companion for `ChristoffelDiffKoszulDeriv.lean`.  Full mission route: `HCGCompactness/UNIF_ITEM6_RECON.md`
(§4b = the confirmed 6-step plan for this file).

## Goal of this leaf

The differentiated Koszul identity (crux of B2 P2, the ungated a=1 connection-difference-derivative bound):
```
2·g₁(covDerivConnDiff g₂ g₁ W X Y x, Z) = [∇₂²g₁ combo] − 2·(∇₂_W g₁)(A(X,Y), Z),
```
`A = connDiff g₁ g₂ = difference (LC g₁) (LC g₂)`, `∇₂ = LeviCivita g₂`.  Obtained by differentiating
`connDiff_koszul` covariantly along `W`.

## Landed (verified, sorry-free, axioms = [propext, Classical.choice, Quot.sound])

- `connDiff_koszul_nabla` — the **a=0 differentiation base** in `nabla0SFun` currency:
  ```
  g₁(difference (LC g₁)(LC g₂) x (Y x)(X x), Z x)
    = ½·nabla0SFun 2 (LC g₂) X (metricTensorField g₁) x (Y,Z)
      + ½·nabla0SFun 2 (LC g₂) Y (metricTensorField g₁) x (X,Z)
      − ½·nabla0SFun 2 (LC g₂) Z (metricTensorField g₁) x (X,Y)
  ```
  = `koszul_difference` (`Tensor/RSTensor/NablaOnTensors/KoszulDifference.lean`) specialised to the
  Levi-Civita pair.  This is `connDiff_koszul` in the currency whose covariant derivative is
  Tensor-layer differentiable via `nabla0SFun_eval_smooth_slots` — the base the differentiation `rw`-uses.

## Key facts nailed (reuse for the next brick)

- `LeviCivita g = leviCivitaConnectionOfMetric g` **definitionally** (`LeviCivita_eq_leviCivitaConnectionOfMetric := rfl`),
  so `covDerivConnDiff`'s `LeviCivita` currency and `koszul_difference`'s connection are interchangeable.
- LC hypotheses for `koszul_difference`: `hmc := by simpa [LeviCivita] using
  leviCivitaConnectionOfMetric_isMetricCompatible g₁` (`IsMetricCompatible_gen`); `htf/htf' :=
  (leviCivitaConnectionOfMetric_isTorsionFree g) x` (`IsTorsionFreeAt`).
- HOME confirmed FEASIBLE: `Geometry/Connection/LeviCivita/` is entangled with `Curvature/`
  (`LeviCivita/Basic.lean` imports `Curvature.Realized.*`), so this leaf imports `RicciConnDiffPalatini`
  (`covDerivConnDiff`, Curvature) + `KoszulDifference` (Tensor) with no cycle.  The ratified home works.
- Instances: needs `[VectorBundle]` + `[ContMDiffVectorBundle 1]` (added as theorem hyps),
  `[IsManifold I 1]` + `[IsManifold I (∞+1)]` (`haveI ... IsManifold.of_le` / `change`),
  `CompleteSpace E` (`private local instance` from `FiniteDimensional.complete`).  `omit
  [InnerProductSpace] [NeZero] [BoundarylessManifold] in` before the a=0 lemma (they're for the later
  `covDerivConnDiff` bricks).  `omit ... in` must precede the docstring, not follow it.

## NEXT (the differentiation — recon §4b, 6 steps)

`nabla0SFun_eval_smooth_slots` (`Tensor/RSTensor/NablaOnTensors/Regularity/Tensor0S.lean`) is the
differentiability engine:
`(nabla0SFun s cov X α x)(V·x) = extDerivFun (fun p => α p (V·p)) x (X x) − ∑ₐ α x (update (V·x) a (∇_X V_a))`.
Threading cost: re-package `∇₂g₁` as a `Tensor0SField` (`totalNabla0S`) so the 2nd application has `W`
leading and X/Y/Z as slots; the three combo terms differentiate separately (leading dir X,Y,Z differ).
Then LHS metric-compat Leibniz + step-4 `covDerivDiff` unfold + step-5 `connDiff_koszul_nabla`-cancellation
of slot corrections.  Est. 200–400 lines, genuine multi-session.

## Landed session 3 (both differentiation engines, verified, axioms [propext, Classical.choice, Quot.sound])

- `metricField_totalReg` — regularity of `∇₂g₁ = totalNabla0SFun 2 (LC g₂)(metricTensorField g₁)` as a
  `(0,3)`-field (from `totalNabla0S_reg` + `leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally`),
  so it bundles via `totalNabla0S` and differentiates a second time.
- `nablaMetric_combo_extDeriv` — **RHS engine**: `extDerivFun` along `W` of a `∇₂g₁` combo term
  (direction `V 0`, slots `V 1, V 2`) `= nabla0SFun 3 (LC g₂) W (∇₂g₁-field)` (= `∇₂²g₁`) `+ Leibniz
  corrections`.  **V-parameterized ⟹ covers all THREE combo terms** of `connDiff_koszul_nabla`
  (`V = ![X,Y,Z]`, `![Y,X,Z]`, `![Z,X,Y]`).
- `metric_leibniz_extDeriv` — **LHS engine**: `extDerivFun` along `W` of `p ↦ metricTensorField g₁ p (V·p)`
  `= nabla0SFun 2 (LC g₂) W (metricTensorField g₁)` (= `(∇₂g₁)(a,b)`) `+ g₁(∇₂_W ·,·)` corrections.

Both engines = one `nabla0SFun_eval_smooth_slots` + `abel`; RHS also uses the slot-0 bridge
`totalNabla0SFun_apply_section` + `Fin.cons_self_tail`.  `extDerivFun` resolves UNQUALIFIED (it is
`DifferentialGeometry.extDerivFun`, not `Tensor0SBundle.extDerivFun`).  Pass section families as a
`V : Fin n → ContMDiffSection` PARAMETER — inlining `Fin.cons X (…)` in a statement fails constant-motive
inference ("Function expected at Fin.cons … a").

## REMAINING (the assembly — next session), all algebra now both engines exist

1. **Differentiate the identity:** `connDiff_koszul_nabla` holds ∀p, so `funext` ⟹ `extDerivFun LHS =
   extDerivFun RHS`; LHS by `metric_leibniz_extDeriv` (slots `[diffSec-section, Z]`), RHS by
   `nablaMetric_combo_extDeriv` ×3.  NEEDS: package `diffSec (LC g₂)(LC g₁) X Y` as a `ContMDiffSection`
   (grep `diffSec_contMDiff` first).
2. **Identify `covDerivConnDiff`:** `∇₂_W(diffSec …) = covDerivConnDiff g₂ g₁ W X Y x + A-slot corr` via
   `covDerivConnDiff_eq` + `covDerivDiff` def (`ConnectionDifferenceCurvature.lean:274`).
3. **Cancel** slot corrections via `connDiff_koszul_nabla` on `∇₂_W`-slot args ⟹
   `2·g₁(covDerivConnDiff g₂ g₁ W X Y x, Z) = [∇₂²g₁ combo] − 2·(∇₂_W g₁)(A(X,Y),Z)`.  Est. ~100–200 lines.

## Status

- 2026-07-25 (B2 session 3): BOTH differentiation engines LANDED (`metric_leibniz_extDeriv` +
  `nablaMetric_combo_extDeriv`) + `metricField_totalReg`, verified/axiom-clean.  Milestone (slot-0 bridge
  + one combo) EXCEEDED (general combo covers all 3 terms; LHS engine also done).  Remaining = the
  assembly (steps 1–3).  Verified-boundary stop.
- 2026-07-25 (B2 session 2): a=0 base `connDiff_koszul_nabla` LANDED (verified, axiom-clean); home + LC
  currency + instances confirmed in real Lean.
