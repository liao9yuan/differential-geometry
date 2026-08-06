# `LowRegA2PerIndex.lean` — the ball-free per-index `appCc` assembly

Created 2026-08-05 by the J4-PREP part-(3) brick (PLAN5 No. 150-recon-§6.4,
ordered redispatch step 3).  Status: **landed, sorry-free, census-clean**
(`propext`, `Classical.choice`, `Quot.sound` only, for all three public
theorems).

## What is in the file

| name | shape | role |
|---|---|---|
| `appCcPerIdxL2` | `‖∇^q(appCc Φ W)‖² ≤ appCcGdiag q · ∑_{i≤q} (Λ i)² · ∑_{l≤q-i} ‖∇^l W‖²` | the engine: one sup constant *per Leibniz index*, data window `q-i` |
| `a2PerIdxJet` | `‖∇^q(a₂T)‖² ≤ Cq q · (Cδ²·J(q+2) + ∑_{1≤i≤q} K i·(1+J(i+2))·J(q-i+2))` | the `a₂` instance, `J(n) = ∑_{j≤n}‖∇^j T‖²` |
| `a2PerIdxLin` | same with `jet = √J`, linear: `Cq q · (Cδ·jet_{q+2} + ∑ K i (1+jet_{i+2}) jet_{q-i+2})` | the form the rung pairing consumes |

Private helpers: `contRfns` (fibre-norm continuity — third copy in the tree, see
below), `jetCompSq` (`‖∇^l(∇^m S)‖² = ‖∇^{m+l}S‖²`, general `(r,s)`),
`jetShiftLe`, `c2SupJet` (per-index coefficient sup bounds), `sqrtAdd2`,
`sqrtFinSum`.

## The mathematical point

`‖𝒩(U)−𝒩(0)‖_{H^{k−1}}` is a Leibniz **sum**, and the Hölder split must be
chosen per index: only `i = 0` may be charged to the small pointwise fibre cap
`Cδ` of the coefficient, every `i ≥ 1` puts the *coefficient* in `L^∞` and the
state in `L²`.  The two engines that existed both refuse this:

* `exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le`
  (`ConnLapCommutatorCoefficientTame.lean:1334`) and the band split
  `exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le`
  (`DeTurckRemainderPrincipalArmOpNorm.lean:4670`) collapse the whole `i ≥ 1`
  region onto one lower slot `Cm q·√(∑_{i≤q+1}…)` whose constant is a function
  of an a-priori **ball** radius;
* `exists_moserTameProduct_iteratedCovGrad_l2Norm_le` (`MoserTameProduct.lean:111`)
  prices the coefficient with one uniform `C^k`-sup, i.e. one `i`-independent
  split.

**Why the collapse is fatal here, concretely.**  The natural candidate
`appCc_topOrder_l2_twoArm_mixed_le` (`DeTurckRemainderHigherOrderTame.lean:512`)
bounds the whole sum by `C(Λ_W²·∑_i‖∇^iΦ‖² + Λ_Φ²·∑_l‖∇^lW‖²)`.  Its first
summand carries `Λ_W = ‖∇²U‖_∞ ≲ ‖U‖_{H⁴}` — order `X`, *not* small — against
`√(Kc)(1+‖U‖_{H²})`, so the pairing yields `C·X² = C·E_4` with `C` not small,
i.e. a non-absorbable `D_3`.  That is the ladder collapse in miniature and the
reason a new assembly was needed rather than a wiring job.

## The route that worked (first try, no dead ends)

`appCc_iteratedCovGrad_diagonalProductGrid_le`
(`Analysis/Spectral/Tensor/CovGrad/OperatorFieldFibreNormJet.lean:885`) is the
**pointwise per-index Leibniz grid**:

```
|∇^q(appCc Φ W)|²(x) ≤ appCcGdiag q · ∑_{i≤q} |∇^iΦ|²(x) · ∑_{l≤q-i} |∇^lW|²(x)
```

It was already there, public, and it is exactly the shape needed: the per-index
choice is made by bounding `|∇^iΦ|²(x)` by `(Λ i)²` *inside the integral*, index
by index, and then integrating the remaining data factor.  `appCcPerIdxL2` is
that one move; everything downstream is instantiation.  The `i ≥ 1` constants
come from the sup embedding
`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`
(`SobolevEmbeddingSharpC0JetSum.lean:717`, window `range (finrank/2+2) = range 3`
in dimension three) applied to `∇^i C₂`, composed with `jetCompSq` and read off
the **sharp** tower `c2JetTowerSharp` (adapter G, part 1 of the same dispatch).

Index bookkeeping, dimension three: coefficient index `i` ⇒ sup embedding costs
`+2` ⇒ tower index `i+2` ⇒ (sharp window) state jets `j ≤ i+2`; companion data
factor `∇^{q-i}W = ∇^{q-i+2}T`.  Both `≤ q+2`, and `q+2` occurs *only* in the
`i = 0` slot, where the constant is the small `Cδ`.  With the old `range (i+2)`
window the tower would have given `j ≤ i+3`, i.e. `H^{k+2}` at `i = q` — the
circularity PSTOP §6.3 missed.

## Findings the planner needs

1. **A prefactor rides on the small constant.**  `a2PerIdxLin`'s top slot is
   `Cq q · Cδ`, not `Cδ`, with `Cq q = √(appCcGdiag q) = (2(d+1))^{q/2}`.  The
   ordering is legal (`Cq` depends only on `g₀` and `q`, hence is fixed before
   `δ` and before `R`), but PSTOP adapter H must be read as
   `Cq q·Cδ* + K_R·R + 2ε < 1`.  At `k ≤ 5`, `q ≤ 4`, so finitely many `Cq`
   values — `δ*` is simply chosen after them.  **Not** discharged here.
2. **No `H^{k-1}`-*norm* version is provided, deliberately.**  Getting the
   spectral `H^q` norm on the left from jets costs `hs_le_jet` plus a sum over
   `j ≤ q`, which multiplies the top constant by another `C·(q+1)`.  That is
   harmless for the same ordering reason but pointless to bake in: the rung
   pairs against `‖U‖_{H^{k+1}}` and can use the jet form directly through
   `hsJet_le`/`hs_le_jet` at the point of use.  If a later consumer wants the
   `H^q` form, it is a corollary, not new mathematics.
3. **`contRfns` is now the third private copy** of the same four-line fibre-norm
   continuity fact (`DeTurckRemainderHigherOrderTame.lean:32`,
   `DeTurckRemainderTameLipschitz/TameL2.lean:927`).  Its canonical home is the
   `Integral/L2` layer; deduplicating is a separate, safe cleanup.

## Verification

Focused check green; targeted module build green; axiom census clean on
`appCcPerIdxL2`, `a2PerIdxJet`, `a2PerIdxLin`.  Downstream consumers of the
sharpened tower rebuilt green (`ScratchC01Census`).

## 2026-08-05 planner pass: exhibit FOURTEEN + fold + doc fix (№153)

The adversarial acceptance panel found that the "engine" here duplicated
pre-existing API: `app_jet_sq_le`
(`Analysis/Sobolev/TensorHilbert/ParametricAppCcJetBound.lean:40`) already
states the integrated per-index assembly (per-index caps `B i` ⟹
`appCcGdiag`-weighted per-index Leibniz sum).  The original "two engines refuse
this" census in this file's header missed it — over-count exhibit 14; the
census-grep lesson is to sweep the TensorHilbert/parametric layer, not just the
local engine family.

Repairs (this file): `appCcPerIdxL2` folded to a 5-line wrapper over
`app_jet_sq_le` (`B i := Λ i ^ 2`, `C := appCcGdiag q`; statement
byte-identical); private `contRfns` deleted; header rewritten;
`ParametricAppCcJetBound` import added.  Also fixed a FALSE doc sentence in
`a2PerIdxJet`: the top order `q+2` occurs in TWO slots — `i = 0` (against `Cδ`)
and the `i = q` coefficient factor `1 + J(q+2)` (against `K q`, adapter H's
`K_R·R`) — not "only `i = 0`".  The Lean statements needed no change.

Verification after the fold: focused check green; targeted module build green;
persisted axiom census green (`ScratchC01Census.lean` — all three theorems
`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`).

Note for the a₁/a₀ arms (part 4a): the same `app_jet_sq_le` wrapper pattern
serves `A.a1`/`A.a0` — do NOT re-derive the integration there either.  The
private `jetCompSq`/`c2SupJet` helpers here are C2-only; part 4a should
generalize/promote them rather than copy them.

## 2026-08-05 executor pass (brick 4a): dedup + helper promotion

Changes to this file, all statement-preserving:

* `jetCompSq` **deleted** — exhibit FIFTEEN.  The public `icgNormComp`
  (`Analysis/Sobolev/TensorHilbert/GradCapAtgw.lean`) already is that lemma in
  norm form and is in this file's import closure; `jetCompSq` was a
  re-derivation.  Its two call sites (`icgWinShift`, `c2SupJet`) now use
  `icgNormComp`.
* `jetShiftLe` **promoted and generalized** to the public valence-generic
  `icgWinShift (g r s m p Ψ)`; the `a₂` call site passes `0 2 2 (q-i)`.
* `sqrtAdd2`, `sqrtFinSum` **made public** and moved next to `icgWinShift` under
  a "Shared helpers" heading.

Nothing else moved; `appCcPerIdxL2`, `a2PerIdxJet`, `a2PerIdxLin` are untouched.
Focused check and targeted build green; census re-run green.  The consumer is
`LowRegA1PerIndex.lean` — see its `.md` for why the a₁ arm could **not** reuse
the `a₂` per-index recipe: with the `C₀`/`C₁` tower window `range (i+2)` (sharp,
unlike `C₂`'s), putting the coefficient in `L^∞` at index `i` reaches state
order `i+3`, i.e. `q+3` at the top index — over the §6.4 budget.  The `a₁` arm
flips the Hölder side from index `1` on instead.

## Lean lessons (durable)

* A new file in this tree **must** carry `open scoped … ContDiff` (or Manifold)
  before the `variable` block: without it the `∞` in `[IsManifold I ∞ M]` fails
  to parse, the rest of the variable block is silently dropped, and every later
  statement fails with `NeZero (Module.finrank ℝ ?m)` / `SmoothCcTensor ?m …`
  metavariable noise that looks like an instance problem and is not.
  Diagnose with `set_option autoImplicit false` in a scratch copy — it turns the
  cascade into one honest `Unknown identifier I`.
* `Finset.range_subset.mpr (by omega)` does **not** close
  `range (a+1) ⊆ range (b+1)` here (omega ends up with the membership variable in
  scope); the explicit `intro x hx; rw [Finset.mem_range] at hx ⊢; omega` does.
* In this Mathlib `add_le_add_left h a : b + a ≤ c + a` — for `a + b ≤ a + c`
  use `add_le_add le_rfl h`.
* `Real.le_sqrt_of_sq_le_sq` does not exist; use
  `Real.sqrt_le_sqrt h` then `rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul …]`.
* `Finset.sum_image` needs its function fixed first (`set f := …`), else the
  motive stays a metavariable.
* `set F : ℕ → ℝ := fun n => …` does not fold applied occurrences `∑ j ∈ range (q+3), …`
  into `F q` (higher-order match).  State the `have` with the `F`-form directly
  and let it typecheck by zeta/beta defeq instead of rewriting.
