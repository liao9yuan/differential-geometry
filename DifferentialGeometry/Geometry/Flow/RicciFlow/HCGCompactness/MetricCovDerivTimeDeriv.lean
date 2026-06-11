import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.TotalNabla0STimeDeriv
import DifferentialGeometry.Bundle.SectionRealized
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic.Core
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Tangent
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Tensor0S

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Time derivative of the iterated background covariant derivative (the `hevol` core)

The `p`-fold induction behind the evolution input of
`MetricCovOrderEvolutionInput`: if a time-family `A r` of `(0,2)` fields has
pointwise-evaluated time derivative `B t` (the flow equation, at `p = 0`), and
the scalar mixed-derivative swaps hold at every tower level (the regularity
input, dischargeable from the solution's joint `(t,x)` smoothness — the
standing `(a')` track), then every level of the fixed-background tower
`covDerivOfField gRef (A r) p` has pointwise-evaluated time derivative
`covDerivOfField gRef (B t) p`.

The chain runs in the flow-interval shape (the order-1 precedent
`metricFrameComp_fixedBaseSwap_of_solution`): derivatives are within the time
carrier `T`, required only at the regular times `R`, with the swap input in
`FixedBaseExtDerivTimeDerivativeOnRegular` form.  The induction engine is the
single-step parametric Clairaut `totalNabla0SFun_hasDerivWithinAt_pt`
(`TotalNabla0STimeDeriv.lean`); the step of the tower is
`metricCovDerivStep = totalNabla0SFun (p+2)` definitionally
(`metricCovDerivStep_apply`).  The per-slot frozen-vector inputs of the
Clairaut are exactly the induction hypothesis, because the statement is
quantified over ALL slot tuples.

The flow wrapper `solnTower_hasDerivAt` instantiates the chain on a Ricci-flow
solution: `A r = ` the moving metric (`solnMetricField`), `B t = -2·Ric_t`
(`solnRicField`), `T = D.carrier`, `R = D.regular`, the base case from the
flow equation `IsSolutionOn.equation`, with the final upgrade
`HasDerivWithinAt → HasDerivAt` via `D.regular_mem_nhds`.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology
open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

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

/-- **The `hevol` induction core** (flow-interval shape).  If the `(0,2)`
time-family `A` has pointwise-evaluated time derivative `B` at the regular
times `R` within the time carrier `T` (`hbase`), and at every tower level
below `N` the scalar mixed-derivative swap holds at regular times for every
choice of smooth slot sections (`hswap` — the regularity input), then every
tower level up to `N` of the fixed-background derivative
`covDerivOfField gRef · p` has pointwise-evaluated time derivative the tower
of `B`, at every regular time within the carrier. -/
theorem covDerivOfField_eval_hasDerivWithinAt
    (gRef : SmoothRiemannianMetric I M)
    (A B : Real → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (T R : Set Real) (N : ℕ)
    (hbase : ∀ t ∈ R, ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (A r) x v) ((B t) x v) T t)
    (hswap : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) T R ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (A r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (B r) p) p'
          (fun a : Fin (p + 2) => V a p'))) :
    ∀ p : ℕ, p ≤ N → ∀ t ∈ R, ∀ x : M,
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
      have hcl := Tensor0SBundle.totalNabla0SFun_hasDerivWithinAt_pt (I := I)
        (leviCivitaConnectionOfMetric (I := I) gRef)
        (σ 0) (fun a : Fin (p + 2) => σ a.succ)
        (fun r => covDerivOfField (I := I) gRef (A r) p)
        (fun t' => covDerivOfField (I := I) gRef (B t') p)
        T x t
        ((hswap p (by omega) (fun a : Fin (p + 2) => σ a.succ) x) t ht x
          (Set.mem_singleton x) (σ 0 x))
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

/-- **The tower swap from joint regularity** (generic two-set form).  The
`hswap` input of `covDerivOfField_eval_hasDerivWithinAt`, produced from the
joint `(t, x)` `C²` smoothness and spatial differentiability of the tower
scalars via `fixedBaseOnReg_of_timeDerivWithin`; the `hTime` input of the
discharger at level `p` is the chain's own conclusion at level `p`, supplied by
strong induction (the swaps below `p` are the inductive hypothesis). -/
theorem covDerivOfField_swapReg
    (gRef : SmoothRiemannianMetric I M)
    (A B : Real → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (T R : Set Real) (hRT : R ⊆ T)
    (hRnhds : ∀ {t : Real}, t ∈ R → T ∈ 𝓝 t)
    (N : ℕ)
    (hbase : ∀ t ∈ R, ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (A r) x v) ((B t) x v) T t)
    (hSmooth : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ t ∈ R, ∀ x : M,
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun q : Real × M => (covDerivOfField (I := I) gRef (A q.1) p) q.2
          (fun a : Fin (p + 2) => V a q.2)) (t, x))
    (hFdiff : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ s ∈ T, ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (covDerivOfField (I := I) gRef (A s) p) y
          (fun a : Fin (p + 2) => V a y)) x)
    (hFtdiff : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ t ∈ R, ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (covDerivOfField (I := I) gRef (B t) p) y
          (fun a : Fin (p + 2) => V a y)) x) :
    ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) T R ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (A r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (B r) p) p'
          (fun a : Fin (p + 2) => V a p')) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ihp =>
    intro hpN V x₀
    refine fixedBaseOnReg_of_timeDerivWithin (I := I) hRT
      (fun {t} ht => hRnhds ht)
      (fun t ht x _ => hSmooth p hpN V t ht x)
      (fun s hs x _ => hFdiff p hpN V s hs x)
      (fun t ht x _ => hFtdiff p hpN V t ht x) ?_
    intro t ht x'
    exact covDerivOfField_eval_hasDerivWithinAt (I := I) gRef A B T R p hbase
      (fun q hq => ihp q hq (lt_trans hq hpN))
      p le_rfl t ht x' (fun a : Fin (p + 2) => V a x')

/-- **Joint smoothness of the tower scalars.**  If every slot evaluation of the
`(0,2)` time-family `A` is jointly `C^∞` at `(t, x)`, then so is every slot
evaluation of every tower level `covDerivOfField gRef (A r) p`.  The step
decomposes the level-`p+1` scalar through `nabla0SFun_eval_smooth_slots`: the
leading `extDerivFun` term is `prodExtDerivAt_inf` of the level-`p` scalar, and
the correction terms are level-`p` scalars at slot tuples updated by the smooth
sections `∇_{V 0}(V a)`. -/
theorem covDerivOfField_eval_contMDiffAt
    (gRef : SmoothRiemannianMetric I M)
    (A : Real → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    {t : Real} {x : M}
    (hbase : ∀ V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _),
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M => (A q.1) q.2 (fun a : Fin 2 => V a q.2)) (t, x)) :
    ∀ p : ℕ, ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _),
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun q : Real × M =>
          (covDerivOfField (I := I) gRef (A q.1) p) q.2
            (fun a : Fin (p + 2) => V a q.2)) (t, x) := by
  intro p
  induction p with
  | zero => intro V; exact hbase V
  | succ p ih =>
      intro V
      have hcov : CovariantDerivative.ContMDiffCovariantDerivative
          (leviCivitaConnectionOfMetric (I := I) gRef) (∞ : WithTop ℕ∞) :=
        ⟨leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) gRef isOpen_univ⟩
      -- the slot-update sections `∇_{V 0}(V a.succ)`
      have hWsec : ∀ a : Fin (p + 2),
          ContMDiff I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
            (fun y : M =>
              (⟨y, ((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun q : M => V a.succ q) y) ((V 0) y)⟩ :
                Bundle.TotalSpace E (TangentSpace I : M → Type _))) := by
        intro a
        simpa [TensorLieDeriv.covariantDeriv_vectorField] using
          TensorLieDeriv.covariantDeriv_vectorField_contMDiff (I := I)
            (leviCivitaConnectionOfMetric (I := I) gRef) hcov (V 0) (V a.succ)
      let W : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _) := fun a =>
        ⟨fun y : M =>
          ((leviCivitaConnectionOfMetric (I := I) gRef)
            (fun q : M => V a.succ q) y) ((V 0) y), hWsec a⟩
      -- the level-(p+1) scalar decomposed through the level-p scalars
      have hdec : ∀ q : Real × M,
          (covDerivOfField (I := I) gRef (A q.1) (p + 1)) q.2
              (fun a : Fin (p + 3) => V a q.2)
            = extDerivFun (I := I)
                (fun y : M => (covDerivOfField (I := I) gRef (A q.1) p) y
                  (fun a : Fin (p + 2) => V a.succ y)) q.2 ((V 0) q.2)
              - ∑ a : Fin (p + 2),
                  (covDerivOfField (I := I) gRef (A q.1) p) q.2
                    (fun b : Fin (p + 2) =>
                      (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                        b q.2) := by
        intro q
        have hv : (fun a : Fin (p + 3) => V a q.2)
            = Fin.cons ((V 0) q.2) (fun a : Fin (p + 2) => V a.succ q.2) := by
          funext b
          refine Fin.cases ?_ ?_ b
          · simp
          · intro a
            simp
        have hupd : ∀ a : Fin (p + 2),
            (fun b : Fin (p + 2) =>
              (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a)) b q.2)
              = Function.update (fun b : Fin (p + 2) => V b.succ q.2) a
                  (((leviCivitaConnectionOfMetric (I := I) gRef)
                    (fun z : M => V a.succ z) q.2) ((V 0) q.2)) := by
          intro a
          funext b
          by_cases hba : b = a
          · subst hba
            simp [W]
          · simp [Function.update_of_ne hba]
        rw [covDerivOfField_succ, metricCovDerivStep_apply, hv,
          Tensor0SBundle.totalNabla0SFun_apply_section,
          Tensor0SBundle.nabla0SFun_eval_smooth_slots]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hupd a]
      have h1 := prodExtDerivAt_inf (I := I)
        (F := fun q : Real × M =>
          (covDerivOfField (I := I) gRef (A q.1) p) q.2
            (fun a : Fin (p + 2) => V a.succ q.2))
        (X := fun y : M => (V 0) y) (t := t) (x := x)
        (ih (fun a : Fin (p + 2) => V a.succ))
        ((V 0).contMDiff.contMDiffAt)
      have h2 : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun q : Real × M =>
            ∑ a : Fin (p + 2),
              (covDerivOfField (I := I) gRef (A q.1) p) q.2
                (fun b : Fin (p + 2) =>
                  (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                    b q.2)) (t, x) :=
        ContMDiffAt.sum fun a _ =>
          ih (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
      have hfun : (fun q : Real × M =>
          (covDerivOfField (I := I) gRef (A q.1) (p + 1)) q.2
            (fun a : Fin (p + 3) => V a q.2))
          = fun q : Real × M =>
              extDerivFun (I := I)
                (fun y : M => (covDerivOfField (I := I) gRef (A q.1) p) y
                  (fun a : Fin (p + 2) => V a.succ y)) q.2 ((V 0) q.2)
              - ∑ a : Fin (p + 2),
                  (covDerivOfField (I := I) gRef (A q.1) p) q.2
                    (fun b : Fin (p + 2) =>
                      (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                        b q.2) :=
        funext hdec
      rw [hfun]
      exact h1.sub h2

/-- **Spatial smoothness of the tower scalars** (fixed-field form): if every
slot evaluation of the `(0,2)` field `A0` is `C^∞` at `x`, then so is every
slot evaluation of every tower level `covDerivOfField gRef A0 p`.  The same
induction as `covDerivOfField_eval_contMDiffAt`, with the spatial engine
`extDerivFun_apply_contMDiffAt`. -/
theorem covDerivOfField_eval_smoothAt
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    {x : M}
    (hbase : ∀ V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _),
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => A0 y (fun a : Fin 2 => V a y)) x) :
    ∀ p : ℕ, ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _),
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          (covDerivOfField (I := I) gRef A0 p) y
            (fun a : Fin (p + 2) => V a y)) x := by
  intro p
  induction p with
  | zero => intro V; exact hbase V
  | succ p ih =>
      intro V
      have hcov : CovariantDerivative.ContMDiffCovariantDerivative
          (leviCivitaConnectionOfMetric (I := I) gRef) (∞ : WithTop ℕ∞) :=
        ⟨leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) gRef isOpen_univ⟩
      have hWsec : ∀ a : Fin (p + 2),
          ContMDiff I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
            (fun y : M =>
              (⟨y, ((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun q : M => V a.succ q) y) ((V 0) y)⟩ :
                Bundle.TotalSpace E (TangentSpace I : M → Type _))) := by
        intro a
        simpa [TensorLieDeriv.covariantDeriv_vectorField] using
          TensorLieDeriv.covariantDeriv_vectorField_contMDiff (I := I)
            (leviCivitaConnectionOfMetric (I := I) gRef) hcov (V 0) (V a.succ)
      let W : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _) := fun a =>
        ⟨fun y : M =>
          ((leviCivitaConnectionOfMetric (I := I) gRef)
            (fun q : M => V a.succ q) y) ((V 0) y), hWsec a⟩
      have hdec : ∀ y : M,
          (covDerivOfField (I := I) gRef A0 (p + 1)) y
              (fun a : Fin (p + 3) => V a y)
            = extDerivFun (I := I)
                (fun z : M => (covDerivOfField (I := I) gRef A0 p) z
                  (fun a : Fin (p + 2) => V a.succ z)) y ((V 0) y)
              - ∑ a : Fin (p + 2),
                  (covDerivOfField (I := I) gRef A0 p) y
                    (fun b : Fin (p + 2) =>
                      (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                        b y) := by
        intro y
        have hv : (fun a : Fin (p + 3) => V a y)
            = Fin.cons ((V 0) y) (fun a : Fin (p + 2) => V a.succ y) := by
          funext b
          refine Fin.cases ?_ ?_ b
          · simp
          · intro a
            simp
        have hupd : ∀ a : Fin (p + 2),
            (fun b : Fin (p + 2) =>
              (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a)) b y)
              = Function.update (fun b : Fin (p + 2) => V b.succ y) a
                  (((leviCivitaConnectionOfMetric (I := I) gRef)
                    (fun z : M => V a.succ z) y) ((V 0) y)) := by
          intro a
          funext b
          by_cases hba : b = a
          · subst hba
            simp [W]
          · simp [Function.update_of_ne hba]
        rw [covDerivOfField_succ, metricCovDerivStep_apply, hv,
          Tensor0SBundle.totalNabla0SFun_apply_section,
          Tensor0SBundle.nabla0SFun_eval_smooth_slots]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hupd a]
      have h1 := extDerivFun_apply_contMDiffAt I
        (f := fun z : M => (covDerivOfField (I := I) gRef A0 p) z
          (fun a : Fin (p + 2) => V a.succ z))
        (x₀ := x)
        (ih (fun a : Fin (p + 2) => V a.succ))
        (V 0)
      have h2 : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun y : M =>
            ∑ a : Fin (p + 2),
              (covDerivOfField (I := I) gRef A0 p) y
                (fun b : Fin (p + 2) =>
                  (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                    b y)) x :=
        ContMDiffAt.sum fun a _ =>
          ih (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
      have hfun : (fun y : M =>
          (covDerivOfField (I := I) gRef A0 (p + 1)) y
            (fun a : Fin (p + 3) => V a y))
          = fun y : M =>
              extDerivFun (I := I)
                (fun z : M => (covDerivOfField (I := I) gRef A0 p) z
                  (fun a : Fin (p + 2) => V a.succ z)) y ((V 0) y)
              - ∑ a : Fin (p + 2),
                  (covDerivOfField (I := I) gRef A0 p) y
                    (fun b : Fin (p + 2) =>
                      (Function.update (fun c : Fin (p + 2) => V c.succ) a (W a))
                        b y) :=
        funext hdec
      rw [hfun]
      exact h1.sub h2

/-- **Spatial differentiability of every tower level** for any `(0,2)` field:
`tensor0SField_eval_smooth_slots_contMDiffAt` supplies the level-0 base of
`covDerivOfField_eval_smoothAt`. -/
theorem covDerivOfField_eval_mdiffAt
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        (covDerivOfField (I := I) gRef A0 p) y
          (fun a : Fin (p + 2) => V a y)) x :=
  (covDerivOfField_eval_smoothAt (I := I) gRef A0
    (fun W => Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt
      (I := I) A0 W x)
    p V).mdifferentiableAt (by simp)

/-! ## The flow wrapper: tower evolution from a Ricci-flow solution -/

/-- The moving metric of a flow solution as a `(0,2)` tensor-field family. -/
noncomputable def solnMetricField
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (r : Real) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
  Tensor0SBundle.metricTensorField (I := I) (S.family.metric r)

/-- The Ricci tensor of the moving metric as a `(0,2)` tensor-field family
(the bundled `ricciSection` of the moving Levi-Civita connection — the same
base field as `ricCovTower`). -/
noncomputable def solnRicField
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
  CovariantDerivative.ricciSection (I := I) (M := M)
    (leviCivitaConnectionOfMetric (I := I) (S.family.metric t))
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) (S.family.metric t))

/-- The Ricci-flow evolution field `-2·Ric_t` of the moving metric. -/
noncomputable def solnEvolField
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
  (-2 : Real) • solnRicField (I := I) S t

/-- The bundled Ricci field agrees pointwise with the solution's canonical
Ricci tensor (`ricciSection_apply` + the definitional chain
`S.ricciAt = metricRicciAt = ricciCurvatureAt ∘ leviCivitaConnectionOfMetric`). -/
theorem solnRicField_eq_ricciAt
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    (solnRicField (I := I) S t) x = S.ricciAt t x := by
  have h := CovariantDerivative.ricciSection_apply (I := I) (M := M)
    (leviCivitaConnectionOfMetric (I := I) (S.family.metric t))
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) (S.family.metric t)) x
  exact h

/-- **The evaluated flow equation in `(0,2)`-field form**: at every regular
time, `∂ₜ (g_t)(v₀, v₁) = (-2·Ric_t)(v₀, v₁)` within the time carrier. -/
theorem solnMetricDeriv
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    ∀ t ∈ D.regular, ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt
        (fun r : Real => (solnMetricField (I := I) S r) x v)
        ((solnEvolField (I := I) S t) x v)
        D.carrier t := by
  intro t ht x v
  have heq := metric_derivWithin_eq_neg_two_ricci (I := I) S hS ⟨t, ht⟩ x (v 0) (v 1)
  have hvec : vec2 (I := I) (v 0) (v 1) = v := by
    funext i
    fin_cases i <;> simp [vec2]
  rw [hvec] at heq
  have hfun : (fun r : Real => (solnMetricField (I := I) S r) x v)
      = fun s : Real => (S.family.metric s).inner x (v 0) (v 1) := by
    funext r
    exact Tensor0SBundle.metricTensorField_apply (I := I) (S.family.metric r) x v
  have hval : (solnEvolField (I := I) S t) x v
      = (-2 : Real) * S.ricciAt t x v := by
    simp only [solnEvolField]
    rw [ContMDiffSection.coe_smul, Pi.smul_apply, solnRicField_eq_ricciAt]
    simp
  rw [hfun, hval]
  exact heq

/-- **The metric-tower evolution from a Ricci-flow solution** (the solution-level
evolution producer).  Given the mixed-derivative swaps at the tower levels below
`N` (the regularity input `hswap`), every tower level `p ≤ N` of the
fixed-background covariant derivative of the moving metric has
pointwise-evaluated time derivative the tower of `-2·Ric` — as a full
`HasDerivAt` at every regular time (`D.regular_mem_nhds`). -/
theorem solnTower_hasDerivAt
    {D : RealTimeInterval}
    (gRef : SmoothRiemannianMetric I M)
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (N : ℕ)
    (hswap : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) D.carrier D.regular
        ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (solnMetricField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (solnEvolField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p'))) :
    ∀ p : ℕ, p ≤ N → ∀ t ∈ D.regular, ∀ x : M,
      ∀ v : Fin (p + 2) → TangentSpace I x,
        HasDerivAt
          (fun r : Real =>
            (covDerivOfField (I := I) gRef (solnMetricField (I := I) S r) p) x v)
          ((covDerivOfField (I := I) gRef (solnEvolField (I := I) S t) p) x v) t := by
  intro p hp t ht x v
  have h := covDerivOfField_eval_hasDerivWithinAt (I := I) gRef
    (fun r => solnMetricField (I := I) S r)
    (fun t' => solnEvolField (I := I) S t')
    D.carrier D.regular N
    (solnMetricDeriv (I := I) S hS) hswap p hp t ht x v
  exact h.hasDerivAt (D.regular_mem_nhds ht)

/-- **The solution tower swap from joint regularity.**  The `hswap` input of
`solnTower_hasDerivAt` / `hevComp_of_solutions`, discharged from the joint
`(t, x)` `C²` smoothness of the metric tower scalars and the spatial
differentiability of the metric/evolution tower scalars (the natural
regularity statements; the swap itself carries no further analytic content). -/
theorem solnTowerSwap_of_smooth
    {D : RealTimeInterval}
    (gRef : SmoothRiemannianMetric I M)
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (N : ℕ)
    (hSmooth : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ t ∈ D.regular, ∀ x : M,
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun q : Real × M =>
          (covDerivOfField (I := I) gRef (solnMetricField (I := I) S q.1) p) q.2
            (fun a : Fin (p + 2) => V a q.2)) (t, x))
    (hFdiff : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ s ∈ D.carrier, ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          (covDerivOfField (I := I) gRef (solnMetricField (I := I) S s) p) y
            (fun a : Fin (p + 2) => V a y)) x)
    (hFtdiff : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ t ∈ D.regular, ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          (covDerivOfField (I := I) gRef (solnEvolField (I := I) S t) p) y
            (fun a : Fin (p + 2) => V a y)) x) :
    ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) D.carrier D.regular
        ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (solnMetricField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (solnEvolField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p')) :=
  covDerivOfField_swapReg (I := I) gRef
    (fun r => solnMetricField (I := I) S r)
    (fun t => solnEvolField (I := I) S t)
    D.carrier D.regular D.regular_subset
    (fun ht => D.regular_mem_nhds ht) N
    (solnMetricDeriv (I := I) S hS) hSmooth hFdiff hFtdiff

/-- **The solution tower swap from joint smoothness alone.**  The two spatial
differentiability inputs of `solnTowerSwap_of_smooth` are discharged by
`covDerivOfField_eval_mdiffAt` (smooth fields on smooth slots); the joint
`(t, x)` `C²` smoothness of the metric tower scalars is the single remaining
regularity input. -/
theorem solnTowerSwap_of_joint
    {D : RealTimeInterval}
    (gRef : SmoothRiemannianMetric I M)
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (N : ℕ)
    (hSmooth : ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ t ∈ D.regular, ∀ x : M,
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun q : Real × M =>
          (covDerivOfField (I := I) gRef (solnMetricField (I := I) S q.1) p) q.2
            (fun a : Fin (p + 2) => V a q.2)) (t, x)) :
    ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) D.carrier D.regular
        ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (solnMetricField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (solnEvolField (I := I) S r) p) p'
          (fun a : Fin (p + 2) => V a p')) :=
  solnTowerSwap_of_smooth (I := I) gRef S hS N hSmooth
    (fun p _ V s _ x =>
      covDerivOfField_eval_mdiffAt (I := I) gRef (solnMetricField (I := I) S s) p V x)
    (fun p _ V t _ x =>
      covDerivOfField_eval_mdiffAt (I := I) gRef (solnEvolField (I := I) S t) p V x)

end HCGCompactness
end DifferentialGeometry
