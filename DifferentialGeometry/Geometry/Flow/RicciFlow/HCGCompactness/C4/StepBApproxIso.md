# StepBApproxIso.lean — B-Falpha (`lbl399`) `C⁰` core + `lbl404` frontier (2026-06-13)

## Status: `lbl399` `C⁰` core COMPLETE; full `C^∞` `lbl399` and `lbl404` = one reported frontier

**Verification PASSED**: focused check + targeted build green (no warnings); axiom-clean
(`[propext, Classical.choice, Quot.sound]`) for `comp_tendsto_id_on`.

## Delivered (`lbl399`, `C⁰` core)
- `comp_tendsto_id_on` — two-parameter composition converges to the identity, **order-0
  (uniform on compacts)**. From `B_k → B∞` and `A_ℓ → A∞` in `C^∞`-on-compacts (the
  `isometry_seq_diffeo_on`/B-trans outputs) and the limit identity `A∞ (B∞ x) = x`, the
  family `A_ℓ ∘ B_k → id` uniformly on each compact `K ⊆ U` (with `B∞ '' K ⊆ V`) as
  `k, ℓ → ∞` independently: `∀ ε>0, ∃ N, ∀ k,ℓ ≥ N, ∀ x∈K, dist (A_ℓ (B_k x)) x < ε`.
  Proof: corral the moving point `B_k x` into the fixed compact `cthickening δ₀ (B∞''K)
  ⊆ V` (`exists_cthickening_subset_open`), Heine–Cantor uniform continuity of `A∞` there,
  and uniform convergence of `A_ℓ`; triangle split `A_ℓ(B_k x) − A∞(B_k x)` +
  `A∞(B_k x) − A∞(B∞ x)`. Inverse identity consumed conditionally on `B∞ x ∈ V` (`hKV`),
  matching `isometry_seq_diffeo_on`.

For the book's `F_{kℓ,β}^α = J̄_ℓ^{αβ} ∘ J_k^{βα}`: `B := J^{βα}`, `A := J̄^{αβ}`, the
limit cocycle `A∞ ∘ B∞ = id` is `exists_transitionLimit_on`'s output.

## Reported frontier (full `C^∞` `lbl399` AND `lbl404`) — Faà-di-Bruno composition convergence

The book's `lbl399` is `C^∞` convergence; `comp_tendsto_id_on` gives only `C⁰`. Upgrading
needs a **Faà-di-Bruno composition-convergence** lemma:

> if `B_k → B∞` and `A_k → A∞` in `C^∞` on compacts (open domains, uniform derivative
> bounds), then `A_ℓ ∘ B_k → A∞ ∘ B∞` in `C^∞` on compacts (two-parameter / tail).

`∇ʳ(A_ℓ ∘ B_k)` is the static Faà-di-Bruno polynomial in `(∇^{≤r}A_ℓ)∘B_k` and
`∇^{≤r}B_k`; the content is pushing two-parameter uniform-on-compacts convergence through
it **with the moving evaluation point `B_k x`** (the `C⁰` corralling above, applied at
every order, plus uniform continuity of each `∇^j A∞`). Mathlib has the static formula
(`Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno`) but **no convergence version**.

**`lbl404`** (almost-identity pullback `φ_k^* h_k → hInf`) reduces to the **same** lemma:
`(φ_k^* h_k)(z)(u,v) = h_k(φ_k z)(dφ_k u, dφ_k v)` is a composition `h_k ∘ φ_k` times the
bilinear factor `dφ_k ⊗ dφ_k`; its `C^p` convergence is exactly the composition + product
convergence the same Faà-di-Bruno lemma supplies. So **one** lemma unblocks both.

Per the plan ("do not invent a broad convergence framework; stop with the smallest
missing lemma"), `lbl404` was **not** attempted and the `C^∞` `lbl399` upgrade is left to
this single missing lemma. (Both also sit downstream of the Step-C-gated `lbl397`, the
hard stop.)
