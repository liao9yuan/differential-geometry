# LowRegBgSolveAt.lean — note

## Role

`IsBgSolveAt g₀ g_bg K hT hT1 u gforce Rcap`: the solve-package input of the
route-(c) Bg rung chain (ROUTE_C_PLAN.md brick 1).  Bundles the canonical
two-metric pieces (`bounds : IsLowBoundsAt`, `solve : IsLowSolveBg`, horizon
cap `hTτ`, radius cap `hcap`) instead of restating `IsLowSolveAt`'s 17
diagonal fields, and projects them back onto the diagonal field statements
(slot 2 freed to `g_bg`) under the same names so rung mirrors port
near-verbatim.

## Field map (diagonal `IsLowSolveAt` field → Bg source → shape delta)

| diagonal | Bg source | delta |
|---|---|---|
| `hδ` | `K.threshold_lt` | none (constants from `K`; bundle arg unused, binder `_h`) |
| `hCtop` | `K.top_nonneg` | none |
| `hB1` | `K.slope_nonneg` | none |
| `hρ` | `K.outer_pos` | none |
| `hP` | `K.realize_pos` | none |
| `hreal` | `bounds.hreal` | none |
| `hδ0` | `bounds.threshold_nonneg` | none |
| `hδ3` | `bounds.threshold_le_third` | none |
| `hcore` | `bounds.core_cont` | slot 2 freed (`coreN g₀ g_bg`); realization proof spelled `h.hreal` — definitionally equal to `bounds.hreal` by proof irrelevance |
| `hB0` | `K.base_nonneg` | none |
| `hcont` | `bounds.hcont` | slot 2 freed; `hreal` slot spelled `h.hreal` (proof irrelevance) |
| `htame` | `bounds.htame` | slot 2 freed; ∀-bound vars renamed `v w` (the diagonal's `u v` would shadow the bundle's solution `u`) — alpha-equivalent |
| `hzero` | `bounds.hzero` | none; bound is `K.zeroBd` |
| `hTτ` | structure field | `T ≤ lowregHorizon K.top K.base K.slope K.zeroBd K.outer K.realize` — exactly the hypothesis shape of `lowreg_sol_of_data` (:998), so the bundle is constructible from that producer |
| `hball` | `solve.force_bound` | none (`/4` preserved; diagonal `fLo` → `gforce`) |
| `hforce` | `solve.force_eq` | none (`fLo` → `gforce` in both occurrences; `g₀ g₀` → `g₀ g_bg`) |
| `hcap` | structure field | none (`lowregStateRad K.top K.slope K.outer K.realize ≤ Rcap`) |

No statement-level mismatch was found anywhere: every delta is either the
intended slot-2 freeing, a bound-variable rename, or a proof-term spelling
bridged by definitional proof irrelevance.  The diagonal's PDE facts
(`map_eq`, `field_mem`, `trace_zero`, `pde`), which `IsLowSolveAt` does not
carry, are available directly as `h.solve.*`.

Constructibility: given `hK : IsLowBoundsAt g₀ g_bg K` and
`hTτ : T ≤ lowregHorizon …`, `lowreg_sol_of_data` yields `u`, `gforce`,
`hsol`, and `⟨hK, hsol, hTτ, hcap⟩ : IsBgSolveAt …` (the `solve` field's
`hK`-argument is the `bounds` field, filled by the same term).

## Verification

Passed.  Focused check green and warning-free; axiom probe on
`hreal`/`hcore`/`hcont`/`htame`/`hforce` reported exactly
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`), probe lines
removed afterward and the final clean check rerun green.
