import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.TotalNabla0STimeDeriv
import DifferentialGeometry.Bundle.SectionRealized

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Time derivative of the iterated background covariant derivative (the `hevol` core)

The `p`-fold induction behind the `hevol` field of `MetricCovOrderEvolutionInput`:
if a time-family `A r` of `(0,2)` fields has pointwise-evaluated time derivative
`B t` (the flow equation, at `p = 0`), and the scalar mixed-derivative swaps hold
at every tower level (the regularity input, dischargeable from the solution's
joint `(t,x)` smoothness — the standing `(a')` track), then every level of the
fixed-background tower `covDerivOfField gRef (A r) p` has pointwise-evaluated
time derivative `covDerivOfField gRef (B t) p`.

The induction engine is the single-step parametric Clairaut
`totalNabla0SFun_hasDerivWithinAt` (`TotalNabla0STimeDeriv.lean`); the step of
the tower is `metricCovDerivStep = totalNabla0SFun (p+2)` definitionally
(`metricCovDerivStep_apply`).  The per-slot frozen-vector inputs of the Clairaut
are exactly the induction hypothesis, because the statement is quantified over
ALL slot tuples.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology
open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

/-- **The `hevol` induction core.**  If the `(0,2)` time-family `A` has
pointwise-evaluated time derivative `B` (`hbase`), and at every tower level
below `N` the scalar mixed-derivative swap holds for every choice of smooth
slot sections (`hswap` — the regularity input), then every tower level up to
`N` of the fixed-background derivative `covDerivOfField gRef · p` has
pointwise-evaluated time derivative the tower of `B`. -/
theorem covDerivOfField_eval_hasDerivWithinAt
    (gRef : SmoothRiemannianMetric I M)
    (A B : Real → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (T : Set Real) (N : ℕ)
    (hbase : ∀ t ∈ T, ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (A r) x v) ((B t) x v) T t)
    (hswap : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOn (I := I) T ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (A r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (B r) p) p'
          (fun a : Fin (p + 2) => V a p'))) :
    ∀ p : ℕ, p ≤ N → ∀ t ∈ T, ∀ x : M,
      ∀ v : Fin (p + 2) → TangentSpace I x,
        HasDerivWithinAt
          (fun r : Real => (covDerivOfField (I := I) gRef (A r) p) x v)
          ((covDerivOfField (I := I) gRef (B t) p) x v) T t := by
  intro p
  induction p with
  | zero =>
      intro _ t ht x v
      exact hbase t ht x v
  | succ p ih =>
      intro hpN t ht x v
      -- extend the slot vectors to global smooth sections
      have hext : ∀ a : Fin (p + 3),
          ∃ σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
            σ x = v a :=
        fun a => ContMDiffSection.exists_eq_at_gen x (v a)
      choose σ hσ using hext
      -- the single-step parametric Clairaut at level `p`
      have hcl := Tensor0SBundle.totalNabla0SFun_hasDerivWithinAt (I := I)
        (leviCivitaConnectionOfMetric (I := I) gRef)
        (σ 0) (fun a : Fin (p + 2) => σ a.succ)
        (fun r => covDerivOfField (I := I) gRef (A r) p)
        (fun t' => covDerivOfField (I := I) gRef (B t') p)
        T x t
        (hswap p (by omega) (fun a : Fin (p + 2) => σ a.succ) x)
        (fun a => ih (by omega) t ht x
          (Function.update (fun b : Fin (p + 2) => σ b.succ x) a
            (((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun q : M => σ a.succ q) x) (σ 0 x))))
      -- identify the slot tuple with `v`
      have hv : (Fin.cons (σ 0 x) (fun a : Fin (p + 2) => σ a.succ x) :
          Fin (p + 3) → TangentSpace I x) = v := by
        funext b
        refine Fin.cases ?_ ?_ b
        · simpa using hσ 0
        · intro a
          simpa using hσ a.succ
      rw [hv] at hcl
      exact hcl

end HCGCompactness
end DifferentialGeometry
