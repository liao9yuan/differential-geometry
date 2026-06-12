import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconv

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# P3 Brick C-I — countable diagonal + global limit (MSM135 Corollary lbl351)

This file holds the atlas×component diagonal that turns the per-(chart, component)
`C^∞` convergence `exists_chart_cInfConv` (Brick B) into ONE subsequence working
for every chart and every metric component of a σ-compact manifold.

* `exists_diag_subseq` (C0) — the abstract countable common-subsequence diagonal:
  given a family of subsequence-stable, tail-stable, refinable properties
  `P n`, one strictly monotone `φ` satisfies all of them.  Pure `ℕ`-combinatorics
  (no manifold content); the design (hypothesis shape) is fixed by the P3 planner.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

/-- **Abstract countable diagonal subsequence** (P3 Brick C-I, C0).

Given a countable family of predicates `P n` on subsequences `ℕ → ℕ` such that
* `hstep` — every `P n` is *refinable*: any subsequence `φ` has a further
  refinement `φ ∘ ψ` (with `ψ` strictly monotone) satisfying `P n`;
* `hsub` — every `P n` is *subsequence-stable*: it survives passing to a further
  refinement;
* `hextend` — every `P n` is *tail-stable*: it holds for `φ` as soon as it holds
  for some tail `fun k => φ (k + m)`,

there is one strictly monotone `φ` with `P n φ` for all `n`.

The three stabilities are exactly the ones convergence-type properties
(`∀ ε, ∃ k₀, ∀ k ≥ k₀, …` shapes such as `MapCPConvOn`/`MetricCPConvOn`) enjoy:
refinement = extracting a sub-subsequence; subsequence-stability = the asymptotic
`∃ k₀` is preserved by monotone reindexing; tail-stability = a property of a tail
of a convergent sequence is a property of the whole.

Construction: classical nested extractors `G 0 = id`, `G (n+1) = G n ∘ ρ n`
(`ρ n` from `hstep n`), diagonal `φ n = G (n+1) n`.  For each `n` the `n`-tail of
`φ` is a subsequence of `G (n+1)` (a single strictly monotone reindexing `τ`
built from the partial composition of the `ρ`'s past step `n+1`), so `hsub` gives
`P n` on the tail and `hextend` lifts it to all of `φ`. -/
theorem exists_diag_subseq
    (P : ℕ → (ℕ → ℕ) → Prop)
    (hstep : ∀ n : ℕ, ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P n (φ ∘ ψ))
    (hsub : ∀ n : ℕ, ∀ φ ψ : ℕ → ℕ, StrictMono ψ → P n φ → P n (φ ∘ ψ))
    (hextend : ∀ n : ℕ, ∀ φ : ℕ → ℕ, ∀ m : ℕ,
      P n (fun k => φ (k + m)) → P n φ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n : ℕ, P n φ := by
  classical
  -- nested extractors carried with their strict-monotonicity proofs
  let G : ℕ → {φ : ℕ → ℕ // StrictMono φ} := fun n =>
    Nat.rec ⟨id, strictMono_id⟩
      (fun m Gm => ⟨Gm.1 ∘ (hstep m Gm.1 Gm.2).choose,
        Gm.2.comp (hstep m Gm.1 Gm.2).choose_spec.1⟩) n
  set Gf : ℕ → (ℕ → ℕ) := fun n => (G n).1 with hGfdef
  have hGmono : ∀ n, StrictMono (Gf n) := fun n => (G n).2
  set ρ : ℕ → (ℕ → ℕ) := fun n => (hstep n (Gf n) (hGmono n)).choose with hρdef
  have hρmono : ∀ n, StrictMono (ρ n) := fun n => (hstep n (Gf n) (hGmono n)).choose_spec.1
  have hGstep : ∀ n, Gf (n + 1) = Gf n ∘ ρ n := fun n => rfl
  have hGP : ∀ n, P n (Gf (n + 1)) := fun n => by
    rw [hGstep]; exact (hstep n (Gf n) (hGmono n)).choose_spec.2
  set φ : ℕ → ℕ := fun n => Gf (n + 1) n with hφdef
  refine ⟨φ, ?_, ?_⟩
  · -- strict monotonicity of the diagonal
    apply strictMono_nat_of_lt_succ
    intro n
    have h1 : φ (n + 1) = Gf (n + 1) (ρ (n + 1) (n + 1)) := by
      show Gf (n + 2) (n + 1) = Gf (n + 1) (ρ (n + 1) (n + 1))
      rw [hGstep (n + 1)]; rfl
    show φ n < φ (n + 1)
    rw [h1]
    exact hGmono (n + 1) ((Nat.lt_succ_self n).trans_le (hρmono (n + 1)).le_apply)
  · -- each property holds, via the tail subsequence + hextend
    intro n
    -- partial composition of the extractors past step `n + 1`
    let Q : ℕ → (ℕ → ℕ) := fun m =>
      Nat.rec id (fun j Qj => Qj ∘ ρ (n + 1 + j)) m
    have hQstep : ∀ m, Q (m + 1) = Q m ∘ ρ (n + 1 + m) := fun m => rfl
    have hQmono : ∀ m, StrictMono (Q m) := by
      intro m
      induction m with
      | zero => exact strictMono_id
      | succ j ih => exact ih.comp (hρmono (n + 1 + j))
    have hGcomp : ∀ m, Gf (n + 1 + m) = Gf (n + 1) ∘ Q m := by
      intro m
      induction m with
      | zero => rfl
      | succ j ih =>
        show Gf (n + 1 + j) ∘ ρ (n + 1 + j) = Gf (n + 1) ∘ Q (j + 1)
        rw [ih, hQstep]
        rfl
    -- the reindexing of the `n`-tail of `φ` into `Gf (n + 1)`
    set τ : ℕ → ℕ := fun m => Q m (n + m) with hτdef
    have hτmono : StrictMono τ := by
      apply strictMono_nat_of_lt_succ
      intro m
      show Q m (n + m) < Q (m + 1) (n + (m + 1))
      rw [hQstep]
      show Q m (n + m) < Q m (ρ (n + 1 + m) (n + (m + 1)))
      apply hQmono m
      exact (Nat.lt_succ_self (n + m)).trans_le
        (by rw [show n + (m + 1) = (n + m) + 1 from by ring]; exact (hρmono (n + 1 + m)).le_apply)
    have htail : (fun m => φ (n + m)) = Gf (n + 1) ∘ τ := by
      funext m
      show φ (n + m) = Gf (n + 1) (Q m (n + m))
      show Gf (n + m + 1) (n + m) = Gf (n + 1) (Q m (n + m))
      rw [show n + m + 1 = n + 1 + m from by ring, hGcomp m]
      rfl
    have hPtail : P n (fun m => φ (n + m)) := by
      rw [htail]; exact hsub n (Gf (n + 1)) τ hτmono (hGP n)
    refine hextend n φ n ?_
    have hcomm : (fun k => φ (k + n)) = (fun m => φ (n + m)) := by
      funext k; rw [Nat.add_comm]
    rw [hcomm]; exact hPtail

end HCGCompactness
end DifferentialGeometry
