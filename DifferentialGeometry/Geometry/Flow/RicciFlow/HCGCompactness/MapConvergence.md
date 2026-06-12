# MapConvergence.lean — F7 convergence-of-maps + AA-for-maps engine (2026-06-11)

MSM135 Ch4 subsection *Compactness of maps*: the Euclidean `C^p`/`C^∞` convergence
definitions for maps (`lbl373`) and the Arzelà–Ascoli-for-maps engine the isometry
corollary `lbl374` consumes. **Now fully sorry-free and axiom-clean** (the former
engine `sorry` in `exists_cInf_subseq` is PROVED; `#print axioms` shows only
`propext, Classical.choice, Quot.sound` for `exists_cInf_subseq` and both
`IsometryCompactness` consumers).

## What's here

**F7 definitions (sorry-free).** For maps between real normed spaces, `∇` = the
iterated Fréchet derivative `iteratedFDeriv ℝ r` (Euclidean gradient):
- `mapDerivNorm r Φk Φinf x = ‖iteratedFDeriv ℝ r (fun y => Φk y - Φinf y) x‖`.
- `MapCPConvOn K p Φ Φinf` — `C^p` convergence on the compact `K` (direct
  `∀ r ≤ p, ∀ x ∈ K, ‖…‖ ≤ ε` form; equivalent to the book's displayed `sup ≤ ε`,
  avoids `sSup`).
- `MapCInfConvOnCompacts U Φ Φinf` — `C^∞` uniformly on compacts (`lbl373`).
- Parallel to `PointedConvergence.lean`'s `MetricCPConvOn`/`MetricCInfConvOnCompacts`.

**Order/subset/subsequence API (sorry-free).** `mapDerivNorm_nonneg`,
`MapCPConvOn.mono_order`, `.mono_set`, `MapCInfConvOnCompacts.cPConvOn`,
`MapCPConvOn.comp_subseq`, `MapCInfConvOnCompacts.comp_subseq`.

**Bridges (sorry-free).** `mapCPConvOn_of_tendstoUniformly`,
`tendstoUniformlyOn_of_cPConv`, `tendsto_of_cInf`.

**AA-for-maps engine (sorry-free, this pass).**
- `cmm_finiteDimensional` — `FiniteDimensional ℝ (E[×r]→L[ℝ] F)` for fin-dim `E, F`.
  Genuine Mathlib gap; curry induction via `continuousMultilinearCurryLeftEquiv`
  (base: `continuousMultilinearCurryFin0`), step instance
  `ContinuousLinearMap.instModuleFinite`.  Stated as a theorem, used via `haveI`
  (no new global instance per project rules).
- `equicont_iteratedFDeriv` (private) — order-`(r+1)` bound on `closedBall x₀ 1` ⇒
  `{∇ʳΦₖ}ₖ` uniformly Lipschitz there (MVT
  `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`, derivative supplied by the
  `HasFTaylorSeriesUpTo.fderiv` field, norm via
  `ContinuousMultilinearMap.curryLeft_norm`) ⇒ `Equicontinuous` via
  `Metric.equicontinuousAt_iff`.
- `exists_cInf_subseq` — the engine, signature unchanged.

## Proof route actually used (deviations from the planned route)

1. Equicontinuity: as planned (MVT on unit closed balls), but the fderiv of
   `∇ʳΦ` comes from the **Taylor-series field** `(contDiff_infty.mp hΦ
   (r+1)).ftaylorSeries.fderiv r`, not `fderiv_iteratedFDeriv` — avoids all
   curry-equiv rewriting, and the cast `(r : WithTop ℕ∞) < r+1` is Nat-only
   (`exact_mod_cast lt_add_one r`).
2. Vector AA: NOT componentwise scalar AA.  Mathlib's general
   `ArzelaAscoli.isCompact_closure_of_isClosedEmbedding` specialized to a proper
   normed target (`ArzelaAscoli.lean:arzelaAscoli_isCompact_closure`), with
   `cmm_finiteDimensional` + `FiniteDimensional.proper_real` for the
   `ContinuousMultilinearMap` targets.
3. NO explicit diagonal over orders: the all-order derivative tuple sequence
   `k ↦ (r ↦ ∇ʳΦₖ)` lives in `Π r, closure (range (Fb r))` — a countable product
   of compact (AA) metrizable (sigma-compact domain) fibers — so ONE
   `IsCompact.tendsto_subseq` extracts a subsequence converging at every order
   simultaneously (same pattern as `DiagonalSubseq.exists_subseq_tendsto_pi`).
4. Derivative-of-limit: per order, `hasFDerivAt_of_tendstoUniformlyOn` on
   `Metric.ball x₀ 1` (uniform convergence on the closed ball, `.mono` to the open
   ball; curried family via
   `(continuousMultilinearCurryLeftEquiv …).isometry.uniformContinuous.comp_tendstoUniformlyOn`).
   Then — instead of an induction on `ContDiff n` — the limits `G r` directly form
   `HasFTaylorSeriesUpTo ⊤ (fun y => (G 0 y).curry0) (fun y r => G r y)` (fields:
   `rfl` / `hGderiv` / `(G m).continuous`), and `HasFTaylorSeriesUpTo.contDiff` +
   `HasFTaylorSeriesUpTo.eq_iteratedFDeriv` give smoothness and `∇ʳΦ_∞ = G r` in
   one shot.  Both lemmas exist in Mathlib — no iterated induction needed.
5. Wrap-up via `mapCPConvOn_of_tendstoUniformly`, rewriting `⇑(G r)` to
   `fun y => iteratedFDeriv ℝ r Φ_∞ y` with a `funext` of `eq_iteratedFDeriv`.

## Lean gotchas
- ContDiff smoothness exponent: write `ContDiff ℝ (⊤ : ℕ∞)` (repo idiom); bare `∞`
  is not in scope.  `contDiff_infty.mp h n` is the clean way to get every finite
  level from it (avoids `WithTop ℕ∞` coercion friction); `(… : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)`
  is `by exact_mod_cast le_top` (established Bundle-files pattern).
- `norm_image_sub_le_of_norm_hasFDerivWithin_le` lives in the `Convex` namespace
  (declared via dot-notation receiver as 3rd explicit arg).
- `hasFDerivAt_of_tendstoUniformlyOn` takes the point membership `hx : x ∈ s` as
  its last arg with `x` implicit.
- `iteratedFDeriv_sub_apply` needs `ContDiffAt`, reduce from `ContDiff … |>.contDiffAt.of_le`.
- `FiniteDimensional` needs `import Mathlib.LinearAlgebra.FiniteDimensional.Defs`.
- `HasFTaylorSeriesUpTo` zero field is `(p x 0).curry0 = f x` (`curry0` is the
  *forward* evaluation `E[×0]→L F → F` in current Mathlib; `uncurry0` is `F → …`).
- `ftaylorSeries`/`ContinuousMap.mk` coercions all unify definitionally with the
  raw `iteratedFDeriv` lambdas — no `show`/`simp only` massage was needed.

## Verification
Focused check passed (no warnings); targeted builds of `MapConvergence` and
`IsometryCompactness` green; axiom audit clean (no `sorryAx`, no honest-input
axioms) for `exists_cInf_subseq`, `cmm_finiteDimensional`,
`arzelaAscoli_isCompact_closure`, `arzelaAscoli_subseq_vec`, `isometry_seq_cInf`,
`isometry_seq_diffeo`.
