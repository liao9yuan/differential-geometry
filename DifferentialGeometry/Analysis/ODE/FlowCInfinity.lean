import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# `C^∞` from finite-order regularity at every natural order

A function `f : E → F` is `C^∞` on a set `S` if and only if it is `C^k` on `S` for every
natural number `k`.  This file packages the `mpr` direction as a single named lemma
(`contDiffOn_top_of_forall_nat`) so that downstream regularity arguments can quote it
without exposing the underlying `iff`.

The proof is a direct application of Mathlib's `contDiffOn_infty`.
-/

namespace DifferentialGeometry.Analysis.ODE.Flow

open Set
open scoped ContDiff

/-- If `f` is `C^k` on `S` for every natural number `k`, then `f` is `C^∞` on `S`.

Here `∞` denotes the top element of `ℕ∞`, coerced into the smoothness-order space
`WithTop ℕ∞` consumed by `ContDiffOn` (notation introduced by `open scoped ContDiff`). -/
theorem contDiffOn_top_of_forall_nat
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {S : Set E}
    (h : ∀ k : ℕ, ContDiffOn 𝕜 (k : ℕ∞) f S) :
    ContDiffOn 𝕜 (∞ : WithTop ℕ∞) f S :=
  contDiffOn_infty.mpr h

end DifferentialGeometry.Analysis.ODE.Flow
