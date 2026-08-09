# ChristoffelDiffKoszulDeriv2 — the a=2 differentiated Koszul identity (`connDiff_koszul_deriv2`)

Companion to `ChristoffelDiffKoszulDeriv2.lean`.  Sibling of `ChristoffelDiffKoszulDeriv.md` (the a=1
model).  Discharges the FRONTIER ingredient 1 of `HCGCompactness/ConnDiffDeriv2Bound.lean`
(`covStepDiff2_exists_const`) — see `HCGCompactness/ConnDiffDeriv2Bound.md` for the route ruling.

## Target

`connDiff_koszul_deriv2` = **differentiate the a=1 lowered-eval Koszul identity `connDiff_koszul_deriv`
once more, along a new base direction `V`, under `∇₂ = LeviCivita g₂`.**  This is literally "the a=1
identity differentiated one more time", the natural meaning of the task's "second base-connection
differentiation".

The a=1 identity (`ChristoffelDiffKoszulDeriv.lean:227`) is
```
2 g₁(covDerivConnDiff g₂ g₁ W X Y x, Z x)
  = N3(W;X,Y,Z) + N3(W;Y,X,Z) − N3(W;Z,X,Y) − 2·N2q(W; A(Y,X), Z)         (a1)
```
with `N3(W;a,b,c) = nabla0SFun 3 (LC g₂) W field₁ x ![a,b,c]`, `field₁ = totalNabla0S 2 (LC g₂)(mtf g₁)`
(= ∇₂g₁, a (0,3) field), `N2q(W;u,c) = nabla0SFun 2 (LC g₂) W (mtf g₁) x ![u,c]` (= (∇₂_W g₁)(u,c)),
and `A(Y,X) = difference (LC g₁)(LC g₂) x (Y x)(X x)`.

## Route (RULED IN — recon route (i)): differentiate (a1) along V; SAME engines, one order up

Apply `∂_V := extDerivFun · x (V x)` to the pointwise identity (a1) (`funext` in x, then `congrArg`).
The RHS terms each differentiate by the SAME generic engine `nabla0SFun_eval_smooth_slots`
(`Tensor/RSTensor/NablaOnTensors/Regularity/Tensor0S.lean:651`), whose a=1 wrappers are
`nablaMetric_combo_extDeriv` and `metric_leibniz_extDeriv`.

* **Each `N3(W;a,b,c)` combo** → bridge `nabla0SFun 3 (LC g₂) W field₁ p slots
  = field₂ p (Fin.cons (W p) slots)` (via `totalNabla0SFun_apply_section`), then differentiate along V:
  ```
  ∂_V[N3(W;a,b,c)] = nabla0SFun 4 (LC g₂) V field₂ x ![W,a,b,c] + Σ_{j:Fin 4} field₂ x (update … ∇₂_V·)
  ```
  `field₂ = totalNabla0S 3 (LC g₂) field₁` (= ∇₂²g₁, a (0,4) field), `nabla0SFun 4 V field₂` = **∇₂³g₁
  combo**.  This is the NEW next-order engine `nablaMetric_combo_extDeriv2` (mirror of the a=1
  `nablaMetric_combo_extDeriv` at s=4).
* **The quadratic `−2 N2q(W; A(Y,X), Z)`** → `= −2 nabla0SFun 2 (LC g₂) W (mtf g₁) ![Adiff, Z]`
  (`Adiff := A(Y,X)` section).  Differentiate along V by the **EXISTING a=1
  `nablaMetric_combo_extDeriv`** (Vtuple = ![W, Adiff, Z], direction V):
  ```
  ∂_V[…] = nabla0SFun 3 (LC g₂) V field₁ x ![W,Adiff,Z] + Σ_{j:Fin 3} field₁ x (update … ∇₂_V·)
  ```
  `nabla0SFun 3 V field₁ ![W,Adiff,Z]` = **∇₂²g₁·A** (∇₂²g₁ paired with A); the j = Adiff-slot
  correction `field₁ x ![W, ∇₂_V Adiff, Z]` = **∇₂g₁·∇₂A** (∇₂g₁ paired with ∇₂A) — the split quadratic
  the recon predicted, appearing automatically from the Leibniz slot corrections.

So the once-differentiated identity has RHS = three ∇₂³g₁ combos (+ slot corrections) − 2·(∇₂²g₁·A +
∇₂g₁·∇₂A + Z-slot correction), staying entirely in `metricCovDeriv`/`nabla0SFun` currency, exactly as
ruled in `ConnDiffDeriv2Bound.md §2`.  The LHS is `∂_V` of the a=1 pairing (the raw second base
derivative of `A` paired with Z; the dual core will apply metric-compat Leibniz to it, exactly as the
a=1 dual core `covDerivConnDiff_g1_le` used the a=1 identity).

## KEY REUSABILITY FINDING (for a ≥ 3)

`nabla0SFun_eval_smooth_slots` and `totalNabla0S_reg` are **fully generic in the rank `s` and the
field `α`**.  So the per-order differentiation is a clean recursion: order `a` reuses the same two
engines with `field_a := totalNabla0S (a+1) (LC g₂) field_{a-1}` and its regularity
`totalNabla0S_reg (a+1)`.  The a=2 combo engine `nablaMetric_combo_extDeriv2` is a verbatim mirror of
the a=1 one; a ≥ 3 will mirror again.  **Differentiating the a=1 STATEMENT (not re-deriving from a=0)
is strictly cleaner** — the quadratic term's differentiation reuses the a=1 combo engine unchanged, and
only the leading combos need the next-order engine.

## Placement (sibling justified)

NEW sibling `ChristoffelDiffKoszulDeriv2.lean` (imports the a=1 file), NOT an edit of the a=1 file:
- the a=1 file carries `[InnerProductSpace ℝ E]` in its variable block (each a=1 decl `omit`s it); a
  fresh **NormedSpace-only** block is cleaner for the whole a≥2 unit (atom is fibre-only, honoured).
- the a=1 file is a committed, axiom-audited unit; keep it pristine.
- the a≥2 unit (this identity + its dual core + higher orders) is a coherent growing module.

## Status (session 1, 2026-07-25) — ALL THREE GREEN, PROOF FULLY CLOSED

- **`metricField_totalReg2`** (order-3 regularity, `field₂ = ∇₂²g₁` is a smooth (0,4) field): GREEN,
  `[NormedSpace ℝ E]`-only (via `omit`).  One-liner from `totalNabla0S_reg 3`.
- **`nablaMetric_combo_extDeriv2`** (the next-order combo differentiation engine): GREEN,
  `[NormedSpace ℝ E]`-only (via `omit`).  Verbatim mirror of a=1's `nablaMetric_combo_extDeriv` at s=4.
- **`connDiff_koszul_deriv2`** (master differentiated identity): **PROVED sorry-free** (no honest partial
  needed — the full proof closed this session).
- Axioms (all three): `[propext, Classical.choice, Quot.sound]` (literal, verified).  Targeted module
  build GREEN (3667 jobs), focused check 0 warnings.

### IPS finding (reported per the constraint)

The a=1 theorem `connDiff_koszul_deriv` carries `[InnerProductSpace ℝ E]` in its signature (it does NOT
`omit` it), and `diffSec_contMDiff` for the Levi-Civita pair needs `ContMDiffCovariantDerivative`
instances that in this project resolve under the a=1 environment (`InnerProductSpace`, `NeZero`,
`BoundarylessManifold`).  So `connDiff_koszul_deriv2` (which consumes both) **cannot** be NormedSpace-only
— it inherits IPS.  The variable block mirrors a=1; the two ENGINES are kept NormedSpace-only via `omit`
(they use only `nabla0SFun_eval_smooth_slots`/`totalNabla0S_reg`, both IPS-free), so the IPS dependence
is confined to the identity that genuinely needs it.

### Route that worked: "differentiate the a=1 STATEMENT" (cleaner than re-deriving)

`hmaster := congrArg (∂_V) (funext (connDiff_koszul_deriv …))` gives `∂_V[LHS_1] = ∂_V[RHS_1]` for free;
the whole proof is then expanding `∂_V[RHS_1]`: linearity split (`extDerivFun_add`/`extDerivFun_const_mul`
+ 4 `MDifferentiableAt` facts) then the four combo engines.  The three `∇₂³g₁` combos use the new
`nablaMetric_combo_extDeriv2`; **the quadratic reuses the a=1 `nablaMetric_combo_extDeriv` verbatim**
(tuple `![W, A(Y,X), Z]`).  Confirmed: differentiating the statement is strictly cleaner than
re-deriving from a=0 — a ≥ 3 should mirror again (bump the two engines one order, reuse all lower ones).

### Honest size

a=2's gate identity is DONE.  The whole `hAcc a≥2` frontier is ~1–2% of the multi-week HCG project; this
identity is its core new mathematics.  Remaining a=2 work (later sessions): (1) the a=2 dual core
`covDerivConnDiff2_g1_le` (pair against the output vector, CS-bound the RHS in `metricCovDeriv` currency,
divide by |∇₂²A| — mirror of B2's `covDerivConnDiff_g1_le`); (2) the a=2 base-Leibniz operator identity
`∇₂²(A⋆S) = (∇₂²A)⋆S + 2(∇₂A)⋆∇₂S + A⋆∇₂²S`; (3) the `covStepDiff2_exists_const` fibre-norm assembly in
`HCGCompactness/ConnDiffDeriv2Bound.lean`; (4) the `hAcc m=2` glue in `UnifCovSumCross.lean`.

## Lean lessons

- **`set` + `rw [← hfield]` on the dependent jet field fails (`motive is not type correct`).**  `field₂ =
  totalNabla0S 3 (LC g₂) field₁ (metricField_totalReg2 …)` — the regularity proof's TYPE mentions the
  spelled `field₁`, so `rw`-abstracting `field₁` breaks the motive.  `set` (definitional) folds the goal
  fine, but any later `rw [← hfield₁] at hR*` on hyps containing `field₂` fails.  Resolution used:
  **do not `set` — spell `field₁`/`field₂` everywhere** (the goal, `hmaster`, the engine outputs, and the
  MDiff/bridge helpers are then all syntactically identical, no folding).  Verbose but zero motive errors.
- **`Adiff` section vs `difference` spelling.**  `connDiff_koszul_deriv`'s RHS spells the quadratic slot
  `difference (LC g₁)(LC g₂) p (Y p)(X p)`; the engine needs the bundled section `Adiff := mk (diffSec …)`.
  `Adiff p ≡ difference…` by `rfl` but they are syntactically distinct, so `rw [hR4]` (Adiff form) won't
  fire on `hmaster` (difference form).  Fix: `hDA : ∀ p, difference… = Adiff p := fun _ => rfl`, then
  `simp only [hDA] at hmaster` right after building it moves everything to the `Adiff` form.
- **MDiff of the a=1-RHS terms:** bridge `nabla0SFun 3 (LC g₂) W field₁ · slots =
  field₂ · (Fin.cons (W ·) slots)` via `totalNabla0SFun_apply_section`, then
  `tensor0SField_eval_smooth_slots_contMDiffAt`.  A generic helper `hMDgen4/3` + `hV4/hV3 ▸ hMDgen`
  (transport along the slot-normalisation equality) gives all four with no per-term boilerplate.
- **Final matching = `simp only [e4x, Fin.sum_univ_three, Matrix.cons_val_*, hup0/1/2, hDA]` then `ring`.**
  The engine output and the stated RHS agree term-for-term after normalising the tuple-indexed slots
  (`e4x : (fun i => (![a,b,c,d] i) x) = ![a x,…]`) and expanding the quadratic `∑ : Fin 3`; they differ
  ONLY in `+`/`-` associativity, which `ring` discharges (it treats each `nabla0SFun`/`field₁ x ![…]`/`∑`
  as an opaque real atom).  `linarith` would also work; `ring` is shortest.
- **`extDerivFun` linearity is CLM-level.**  `extDerivFun_add`/`extDerivFun_const_mul` give CLM equalities;
  apply them to `extDerivFun (…) x` then `simp only [ContinuousLinearMap.add_apply, sub_apply, smul_apply,
  smul_eq_mul]` to distribute over `(V x)`.  Local `extDerivFun_sub'`-style `hsub'` built from
  `extDerivFun_add` (a=1's idiom).
