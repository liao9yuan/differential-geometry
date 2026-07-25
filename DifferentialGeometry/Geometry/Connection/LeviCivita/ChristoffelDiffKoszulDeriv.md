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

## REMAINING (the assembly) — EXECUTABLE RECIPE + tools confirmed (session 4 recon)

Session-4 verdict (STOP-CLEANLY): the assembly is NOT pure algebra — it needs `extDerivFun` linearity over
a **sum-form** RHS, which requires `MDifferentiableAt` of each of the 3 combo terms (real analysis), plus a
delicate many-term cancellation.  Stopped at the green boundary (deep context, per planner's red-spill
guidance).  All tools are located; a fresh successor should close it in one pass:

**Tools confirmed present (do not re-recon):**
- `diffSec_contMDiff cov₀ cov₁ hX hZ` (`ConnectionDifferenceCurvature.lean:120`) — needs instances
  `[ContMDiffCovariantDerivative cov₀ ∞]` + `[..cov₁ ∞]`, `hX : ContMDiff … X`, `hZ : ContMDiff …
  ((∞:WithTop ℕ∞)+1) Z` (Z one level higher).  Instance: `LeviCivita_isContMDiff g :
  ContMDiffCovariantDerivative (LeviCivita g) ∞` (`LeviCivita/Defs.lean:393`).
- `extDerivFun_add` (used at `POUReduction.lean:304`) + `extDerivFun_sub'`
  (`RicciLinearizationConnDiffCoefficients.lean:2679`): `MDifferentiableAt f x → MDifferentiableAt g x →
  extDerivFun (f±g) x = extDerivFun f x ± extDerivFun g x`.  (Also `extDerivFun_neg_at`.)  For the `½`
  scalar use the `const_smul`/`smul` extDerivFun lemma or fold `½` in after.
- combo `MDifferentiableAt`: rewrite combo `nabla0SFun 2 (LC g₂) (V 0) (mtf g₁) p (V.succ·p) = α p (V·p)`
  (via `totalNabla0SFun_apply_section.symm` + `totalNabla0S_apply.symm` + `Fin.cons_self_tail`, `α =
  totalNabla0S 2 (LC g₂)(mtf g₁) (metricField_totalReg …)`), then
  `(TensorMultilinear.contMDiffAt_section_apply_gen (T := fun y => α y) (α.contMDiff.contMDiffAt)
  (v := fun a => V a) (hv := fun a => (V a).contMDiff.contMDiffAt)).mdifferentiableAt`
  (`Tensor/Multilinear/BundleSmoothEvalRealized.lean:856`; pattern copied from
  `nabla0SFun_eval_smooth_slots`'s `hpair`).
- `metricTensorField_apply` (`Tensor/RSTensor/MetricCompatibility.lean:53`): `metricTensorField g x
  slots = g.inner x (slots 0)(slots 1)` (s=2) — bridges `connDiff_koszul_nabla`'s LHS `g₁.inner …` to
  `metric_leibniz_extDeriv`'s `metricTensorField g₁ p (V'·p)` form.

**Recipe:**
0. `Adiff := ContMDiffSection.mk (diffSec (LC g₂)(LC g₁) X Y) (diffSec_contMDiff …)`.  Note
   `diffSec (LC g₂)(LC g₁) X Y p = difference (LC g₁)(LC g₂) p (Y p)(X p)` (defeq) = `connDiff_koszul_nabla`'s
   LHS vector.
1. `hfun : (fun p => g₁.inner p (Adiff p)(Z p)) = (fun p => ½cX p + ½cY p − ½cZ p)` by `funext p;
   exact connDiff_koszul_nabla …` (`cX/cY/cZ` = the three `nabla0SFun 2` combo terms).
2. `congrArg (extDerivFun · x (W x)) hfun` (no differentiability needed here).
3. LHS: rewrite `g₁.inner p (Adiff p)(Z p) = metricTensorField g₁ p (![Adiff, Z]·p)`
   (`metricTensorField_apply`), then `metric_leibniz_extDeriv (V := ![Adiff, Z])` ⟹
   `nabla0SFun 2 (LC g₂) W (mtf g₁) x (Adiff x, Z x) + g₁(∇₂_W Adiff, Z x) + g₁(Adiff x, ∇₂_W Z)`.
4. RHS: `extDerivFun_add/_sub'` + `½`-smul (using the 3 combo `MDifferentiableAt`), then
   `nablaMetric_combo_extDeriv` at `V = ![X,Y,Z]`, `![Y,X,Z]`, `![Z,X,Y]`.
5. Identify `∇₂_W Adiff = (LC g₂)(Adiff) x (W x)` and unfold `covDerivDiff` def
   (`ConnectionDifferenceCurvature.lean:274`, via `covDerivConnDiff_eq`): `covDerivConnDiff g₂ g₁ W X Y x =
   ∇₂_W(diffSec X Y) − difference(LC g₁)(LC g₂) x (Y x)(∇₂_W X) − difference(LC g₁)(LC g₂) x (∇₂_W Y)(X x)`,
   so `∇₂_W Adiff = covDerivConnDiff g₂ g₁ W X Y x + A(∇₂_W X, Y) + A(X, ∇₂_W Y)`-type terms.
6. **Cancel**: the step-3 `g₁(A(∇₂_W …), Z)` + step-4 slot corrections cancel via `connDiff_koszul_nabla`
   applied to the `∇₂_W`-slot args (each `2 g₁(A(∇₂_W s, ·), ·)` = its ∇₂g₁-combo).  Surviving:
   `2·g₁(covDerivConnDiff g₂ g₁ W X Y x, Z x) = [∇₂²g₁ combo from step 4 `nabla0SFun 3`] − 2·nabla0SFun 2
   (LC g₂) W (mtf g₁) x (Adiff x, Z x)` (= `[∇₂²g₁ combo] − 2·(∇₂_W g₁)(A(X,Y),Z)`).  Est. ~150–250 lines.

## Status

- 2026-07-25 (B2 session 4): assembly RECON complete; **clean stop at the green boundary (no new Lean)**.
  Verdict: the assembly needs `extDerivFun` linearity over a sum-form RHS ⟹ `MDifferentiableAt` of 3 combo
  terms (real analysis) + a delicate many-term cancellation — NOT pure algebra.  All tools located and the
  EXECUTABLE RECIPE recorded above (`diffSec_contMDiff`+`LeviCivita_isContMDiff`, `extDerivFun_add/_sub'`,
  `contMDiffAt_section_apply_gen` for combo `MDifferentiableAt`, `metricTensorField_apply`, `covDerivDiff`
  unfold).  Stopped rather than risk a red spill in deep (438k) context (planner-sanctioned); `.lean`
  unchanged = committed green (f1e4b8e38).  A fresh successor executes the recipe in one pass.
- 2026-07-25 (B2 session 3): BOTH differentiation engines LANDED (`metric_leibniz_extDeriv` +
  `nablaMetric_combo_extDeriv`) + `metricField_totalReg`, verified/axiom-clean.  Milestone (slot-0 bridge
  + one combo) EXCEEDED (general combo covers all 3 terms; LHS engine also done).
- 2026-07-25 (B2 session 2): a=0 base `connDiff_koszul_nabla` LANDED (verified, axiom-clean); home + LC
  currency + instances confirmed in real Lean.
