# CurvatureCoefficientDifferenceJetTower

## 2026-07-12: fixed-frame independence elaboration

### Status

- `riemannMixedBiContrFib_eq_fixedFrame_on_nbhd`: proved and source-verified (100%).
- Its dedicated frame-independence machinery, including
  `double_frame_bilin_trace_indep`: available and reused (100%).
- This module's focused source verification and targeted build: passed (100%).
- Short-time-existence branch-alignment merge preparation: approximately 85%; the headline
  theorem is already proved, but downstream consumer and final merge-gate verification remain
  separate work.

### Simplification

The theorem differs from the nearby successful fixed-frame proofs only by an outer scalar factor
`2`. The old generic `congr 1` attempted to discover that congruence through a very large tensor
expression. It was replaced by the typed congruence
`congrArg (fun z : Real => 2 * z)`, after which the existing
`double_frame_bilin_trace_indep` theorem closes the actual geometric equality.

### Failed route and verification

The generic-congruence version hit a deterministic `whnf` heartbeat timeout and a retry with a
larger heartbeat budget consumed roughly 6 GB of memory. Increasing the budget is not a viable
route. The simplified proof passed focused verification and a targeted module build at the normal
heartbeat limit with two Lean threads. No new mathematical frontier remains in this theorem.

## 2026-07-15: antidiagonal product integral API

`grid_prod_int_le` exposes the existing antidiagonal product integration
engine.  Given a pointwise zeroth-jet bound, the top `L2` jet, and the
Gagliardo--Nirenberg intermediate estimates, it controls each product term by
the square of the top jet.  This is the reusable input needed for the
three-dimensional order-two inverse-metric estimate.

The mathematical proof was already present as the private product-term engine;
this change only gives it a public canonical name.  Verification is still
running because this module is unusually large.

## 2026-07-19: public moving-trace split

`pureTrace` gives a small public name to the canonical cometric double-trace
coefficient, and `pureTrace_split` exposes its exact decomposition into the
fixed parallel trace plus the inverse-metric-difference correction.  This is
the algebraic input for the low-regularity fixed-curvature `lieCorr0` arm; it
avoids estimating that arm as an undifferentiated whole.

These aliases are source-complete but await a focused recheck after the
exclusive shared artifact refresh.  No endpoint theorem is credited by this
source-only addition.

## 2026-07-26: THE GATE — radius-free top-separated grid integrator (UNIF item-2)

Implements the single lemma frontier of UNIF item-2 proper per the GPT Pro
ruling distilled in `ShortTime/THREEARM_RECON.md` §11.  Three new declarations
added next to the ballUniform sibling (`:14417` area):

- `antidiagonalTupleGrid_integral_radiusFree` — radius-free per-order antidiagonal
  grid integral bound.  Sibling of `antidiagonalTupleGrid_integral_ballUniform_tameWindow`
  (`:8556`).  Statement takes a FIXED zeroth-order fibre bound `Λ₀` (statement-level
  `{Λ₀} (hΛ₀0 : 0 ≤ Λ₀)`) + a per-`P` pointwise hypothesis
  `hsup : ∀ x, rfns g₀ 0 2 x (P.toSection x) ≤ Λ₀²`; output `K k · (1 + ‖∇ᵏP‖²)`
  with `K` R-free (depends only on `g₀`, `Λ₀`).  Proof is the `:8556` clone with the
  `Cemb·√(a+2)·R` embedding DROPPED (so no `a`, no ball) and the final `htop_le`
  lumping SKIPPED (top jet kept explicit).  The R^{7k} disease was a wrapper
  artifact: `grid_prod_int_le` (`:8154`) is already radius-free-capable — instantiate
  with `R := ‖∇ᵏP‖` (explicit top jet) and fixed `Λ := Λ₀`.

- `boundedFactorGridWindow_integral_radiusFree_topSeparated` — THE GATE.  Sibling of
  `boundedFactorGridWindow_integral_ballUniform_tameWindow_allOrders` (`:14417`) with
  the OPPOSITE constant choice: layers `0..i+1 → Klow i·(1 + ∑_{j≤i+1}‖∇ʲP‖²)`,
  layer `i+2 → Ktop i·‖∇^{i+2}P‖²`, both `Klow`,`Ktop` R-free (`Klow i = ∑_{k<i+3}Kt k`,
  `Ktop i = Kt(i+2)`).  Proof: window ≤ ∑ antidiagonal, integrate termwise via the
  per-order lemma, then distribute + peel top layer `k=i+2` + route low layers by
  `∑ aₖbₖ ≤ (∑aₖ)(∑bₖ)`.

- `rfns_symmS_zero_le_fibreSmall` — DELIVERABLE 1, the public δ₀ fibre-small bridge.
  Thin wrapper over the EXISTING private `rfns_symmS_zero_le_of_ball` (`:3111`, which
  is radius-free despite its name): `gFibreOpBound g₀ (ccTensorBilinSymm g₀ T) δ`,
  `δ ≤ δ₀` ⟹ `rfns g₀ 0 2 x (symmS g₀ T) ≤ ((dim E)·δ₀)²`.  Λ₀ := (dim E)·δ₀.

Design decisions (durable):
1. The GATE integrator is parametrized by ABSTRACT `Λ₀` (weakest-hypotheses), NOT
   by `δ₀`/`gFibreOpBound`.  It needs only the pointwise 0-jet bound, so it is fully
   decoupled from the bridge.  Consumer instantiates `Λ₀ := (dim E)·δ₀` and supplies
   `hsup` via `rfns_symmS_zero_le_fibreSmall` at `P := symmS g₀ T`.
2. The bridge only controls the SYMMETRIC part (`gFibreOpBound` is on the symmetrized
   form), so the honest object is `symmS g₀ T`, not raw `T`.  The committed grids use
   raw `T` (e.g. `bdOmRecover_gridWindow`); the R-free consumer must switch to `symmS T`
   grids (which is the geometrically correct perturbation, `ccTensorBilinSymm g₀ T ↔
   symmS T`).  That switch is the NEXT brick's concern.
3. HONESTY / route-viability: the top-layer subgrid argument GOES THROUGH.  At antidiagonal
   order `i+2`, `grid_prod_int_le` bounds EVERY cell (incl. the top-jet-only cell
   `n=1, e=(i+2)`) by `C·‖∇^{i+2}P‖²` with NO intermediate norm — the constraint
   `∑ eₘ = i+2` forces GN interpolation onto the top jet.  So the capped top layer is
   bounded by the pure top jet.  No resisting term.

Verification status: GREEN.  Targeted module build passed (`Build completed
successfully (9387 jobs)`, 2026-07-26).  `#print axioms` on all three new lemmas =
exactly `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

Fixes found during verification (recorded for future clones of the `:8556`/`:13180`
grid templates):
- The window lemma needs the `letI : MeasurableSpace E/M := borel …; haveI : BorelSpace …`
  block (as `:13180` has) for `integral_mono`; the per-order lemma (cloning `:8556`)
  does not.
- `Finset.single_le_sum` needs its `f` pinned explicitly `(f := fun j => ‖∇ʲP‖²)` or the
  summand stays a metavariable.
- `Finset.range_subset.mpr (by omega)` fed `omega` a metavariable-tainted (real-cast)
  goal; replaced with an explicit `intro k hk; simp only [Finset.mem_range] at hk ⊢; omega`.
