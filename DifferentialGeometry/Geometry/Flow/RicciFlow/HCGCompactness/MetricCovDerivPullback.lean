import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Geometry.Curvature.PullbackNaturality
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Pullback Naturality For Metric Covariant Derivative Towers

This file starts the source-domain pullback bridge for the HCG compactness
layer.  The first producer is the order-one metric-covariant-derivative
naturality statement, proved from the scalar directional-derivative and
Levi-Civita connection naturality APIs in `Curvature/PullbackNaturality.lean`.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff BigOperators
open DifferentialGeometry.Integral.Connection
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

/-- Naturality of the first background covariant derivative of a metric tensor
under pullback by a diffeomorphism, evaluated on smooth section slots. -/
theorem metricCovDeriv_one_pullback_sections
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (h gRef : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (V : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    metricCovDeriv (I := I) (Diffeomorph.pullbackMetric (I := I) h Phi)
        (Diffeomorph.pullbackMetric (I := I) gRef Phi) 1 x
        (Fin.cons (X x) (fun a : Fin 2 => V a x)) =
      metricCovDeriv (I := I) h gRef 1 (Phi x)
        (Fin.cons ((pushFwdSection (I := I) Phi X) (Phi x))
          (fun a : Fin 2 => (pushFwdSection (I := I) Phi (V a)) (Phi x))) := by
  classical
  let hPb : SmoothRiemannianMetric I M := Diffeomorph.pullbackMetric (I := I) h Phi
  let refPb : SmoothRiemannianMetric I M :=
    Diffeomorph.pullbackMetric (I := I) gRef Phi
  have hleft :=
    metricCovDeriv_one_eval_smooth_slots (I := I) hPb refPb X V x
  have hright :=
    metricCovDeriv_one_eval_smooth_slots (I := I) h gRef
      (pushFwdSection (I := I) Phi X)
      (fun a : Fin 2 => pushFwdSection (I := I) Phi (V a)) (Phi x)
  rw [hleft, hright]
  have hdir := directionalDeriv_pullback (I := I) h Phi X (V 0) (V 1) x
  unfold directionalDeriv at hdir
  rw [hdir]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [Diffeomorph.pullbackMetric_inner]
  let covL : TangentSpace I x :=
    ((leviCivitaConnectionOfMetric (I := I) refPb) (fun p : M => V a p) x) (X x)
  let covR : TangentSpace I (Phi x) :=
    ((leviCivitaConnectionOfMetric (I := I) gRef)
      (fun p : N => pushFwdSection (I := I) Phi (V a) p) (Phi x))
      (pushFwdSection (I := I) Phi X (Phi x))
  have hcov : mfderiv I I (Phi : M -> N) x covL = covR := by
    have hcov' := metricCov_pullback (I := I) gRef Phi (V a) x (X x)
    simpa [covL, covR, refPb, metricCov, pushFwdSection_apply_at_image] using hcov'
  have hslot : ∀ b : Fin 2,
      mfderiv I I (Phi : M -> N) x
          (Function.update (fun b : Fin 2 => V b x) a covL b) =
        Function.update
          (fun b : Fin 2 => pushFwdSection (I := I) Phi (V b) (Phi x))
          a covR b := by
    intro b
    by_cases hba : b = a
    · subst b
      simpa [Function.update] using hcov
    · rw [Function.update_of_ne hba, Function.update_of_ne hba]
      simp [pushFwdSection_apply_at_image]
  rw [hslot 0, hslot 1]

/-- Pointwise naturality of the first background covariant derivative of a
metric tensor under pullback by a diffeomorphism. -/
theorem metricCovDeriv_one_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (h gRef : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (x : M) (v0 : TangentSpace I x) (v : Fin 2 -> TangentSpace I x) :
    metricCovDeriv (I := I) (Diffeomorph.pullbackMetric (I := I) h Phi)
        (Diffeomorph.pullbackMetric (I := I) gRef Phi) 1 x
        (Fin.cons v0 v) =
      metricCovDeriv (I := I) h gRef 1 (Phi x)
        (Fin.cons (mfderiv I I (Phi : M -> N) x v0)
          (fun a : Fin 2 => mfderiv I I (Phi : M -> N) x (v a))) := by
  classical
  obtain ⟨X, hX⟩ :=
    ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x v0
  let V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) x (v a)).choose
  have hV : ∀ a : Fin 2, V a x = v a := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) x (v a)).choose_spec
  simpa [hX, hV, pushFwdSection_apply_at_image] using
    metricCovDeriv_one_pullback_sections (I := I) h gRef Phi X V x

/-- Boundaryless-free smooth-slot recursion for one `metricCovDeriv` step.  The
coordinate-frame version lives in `MetricCovDerivCoordStep`; this local form is
the invariant formula needed by the pullback induction. -/
private theorem metricCovDeriv_succ_eval_smooth_slots'
    [SigmaCompactSpace M] [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (h gRef : SmoothRiemannianMetric I M) (a : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (V : Fin (a + 2) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    metricCovDeriv (I := I) h gRef (a + 1) x
        (Fin.cons (X x) (fun q : Fin (a + 2) => V q x)) =
      extDerivFun (I := I)
          (fun y : M => metricCovDeriv (I := I) h gRef a y
            (fun q : Fin (a + 2) => V q y)) x (X x) -
        ∑ p : Fin (a + 2),
          metricCovDeriv (I := I) h gRef a x
            (Function.update (fun q : Fin (a + 2) => V q x) p
              (((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun y : M => V p y) x) (X x))) := by
  rw [metricCovDeriv_succ, metricCovDerivStep_apply,
    Tensor0SBundle.totalNabla0SFun_apply_section]
  exact Tensor0SBundle.nabla0SFun_eval_smooth_slots
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (leviCivitaConnectionOfMetric (I := I) gRef) X V
    (metricCovDeriv (I := I) h gRef a) x

/-- Pointwise naturality of the full background metric-covariant derivative
tower under pullback by a diffeomorphism. -/
theorem metricCovDeriv_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (h gRef : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N) :
    ∀ a : Nat, ∀ x : M, ∀ slots : Fin (a + 2) -> TangentSpace I x,
      metricCovDeriv (I := I) (Diffeomorph.pullbackMetric (I := I) h Phi)
          (Diffeomorph.pullbackMetric (I := I) gRef Phi) a x slots =
        metricCovDeriv (I := I) h gRef a (Phi x)
          (fun q : Fin (a + 2) => mfderiv I I (Phi : M -> N) x (slots q)) := by
  classical
  intro a
  induction a with
  | zero =>
      intro x slots
      change
        Tensor0SBundle.metricTensorField (I := I) (M := M)
            (Diffeomorph.pullbackMetric (I := I) h Phi) x slots =
          Tensor0SBundle.metricTensorField (I := I) (M := N) h (Phi x)
            (fun q : Fin (0 + 2) => mfderiv I I (Phi : M -> N) x (slots q))
      rw [Tensor0SBundle.metricTensorField_apply, Tensor0SBundle.metricTensorField_apply,
        Diffeomorph.pullbackMetric_inner]
  | succ a ih =>
      intro x slots
      obtain ⟨X, hX⟩ :=
        ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
          (n := (⊤ : ℕ∞)) x (slots 0)
      let V : Fin (a + 2) ->
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
        fun q =>
          (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
            (n := (⊤ : ℕ∞)) x (slots q.succ)).choose
      have hV : ∀ q : Fin (a + 2), V q x = slots q.succ := by
        intro q
        exact
          (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
            (n := (⊤ : ℕ∞)) x (slots q.succ)).choose_spec
      have hsmooth :
          metricCovDeriv (I := I) (Diffeomorph.pullbackMetric (I := I) h Phi)
              (Diffeomorph.pullbackMetric (I := I) gRef Phi) (a + 1) x
              (Fin.cons (X x) (fun q : Fin (a + 2) => V q x)) =
            metricCovDeriv (I := I) h gRef (a + 1) (Phi x)
              (Fin.cons ((pushFwdSection (I := I) Phi X) (Phi x))
                (fun q : Fin (a + 2) =>
                  (pushFwdSection (I := I) Phi (V q)) (Phi x))) := by
        let hPb : SmoothRiemannianMetric I M := Diffeomorph.pullbackMetric (I := I) h Phi
        let refPb : SmoothRiemannianMetric I M :=
          Diffeomorph.pullbackMetric (I := I) gRef Phi
        have hleft :=
          metricCovDeriv_succ_eval_smooth_slots' (I := I) hPb refPb a X V x
        have hright :=
          metricCovDeriv_succ_eval_smooth_slots' (I := I) h gRef a
            (pushFwdSection (I := I) Phi X)
            (fun q : Fin (a + 2) => pushFwdSection (I := I) Phi (V q)) (Phi x)
        rw [hleft, hright]
        have hderiv :
            extDerivFun (I := I)
                (fun y : M => metricCovDeriv (I := I) hPb refPb a y
                  (fun q : Fin (a + 2) => V q y)) x (X x) =
              extDerivFun (I := I)
                (fun z : N => metricCovDeriv (I := I) h gRef a z
                  (fun q : Fin (a + 2) =>
                    pushFwdSection (I := I) Phi (V q) z)) (Phi x)
                ((pushFwdSection (I := I) Phi X) (Phi x)) := by
          have hscalar :
              (fun y : M => metricCovDeriv (I := I) hPb refPb a y
                (fun q : Fin (a + 2) => V q y)) =
                fun y : M => metricCovDeriv (I := I) h gRef a (Phi y)
                  (fun q : Fin (a + 2) =>
                    pushFwdSection (I := I) Phi (V q) (Phi y)) := by
            funext y
            simpa [hPb, refPb, pushFwdSection_apply_at_image] using
              ih y (fun q : Fin (a + 2) => V q y)
          have hf : MDifferentiableAt I 𝓘(Real, Real)
              (fun z : N => metricCovDeriv (I := I) h gRef a z
                (fun q : Fin (a + 2) => pushFwdSection (I := I) Phi (V q) z))
              (Phi x) :=
            (Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt
              (I := I) (metricCovDeriv (I := I) h gRef a)
              (fun q : Fin (a + 2) => pushFwdSection (I := I) Phi (V q))
              (Phi x)).mdifferentiableAt (by simp)
          rw [hscalar]
          simpa [pushFwdSection_apply_at_image] using
            extDerivFun_comp_diffeomorph (I := I)
              (f := fun z : N => metricCovDeriv (I := I) h gRef a z
                (fun q : Fin (a + 2) => pushFwdSection (I := I) Phi (V q) z))
              Phi x (X x) hf
        have hsum :
            (∑ p : Fin (a + 2),
              metricCovDeriv (I := I) hPb refPb a x
                (Function.update (fun q : Fin (a + 2) => V q x) p
                  (((leviCivitaConnectionOfMetric (I := I) refPb)
                      (fun y : M => V p y) x) (X x)))) =
              ∑ p : Fin (a + 2),
                metricCovDeriv (I := I) h gRef a (Phi x)
                  (Function.update
                    (fun q : Fin (a + 2) =>
                      pushFwdSection (I := I) Phi (V q) (Phi x)) p
                    (((leviCivitaConnectionOfMetric (I := I) gRef)
                        (fun z : N => pushFwdSection (I := I) Phi (V p) z)
                        (Phi x))
                      (pushFwdSection (I := I) Phi X (Phi x)))) := by
          apply Finset.sum_congr rfl
          intro p _
          let covL : TangentSpace I x :=
            ((leviCivitaConnectionOfMetric (I := I) refPb)
              (fun y : M => V p y) x) (X x)
          let covR : TangentSpace I (Phi x) :=
            ((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun z : N => pushFwdSection (I := I) Phi (V p) z) (Phi x))
              (pushFwdSection (I := I) Phi X (Phi x))
          have hcov : mfderiv I I (Phi : M -> N) x covL = covR := by
            have hcov' := metricCov_pullback (I := I) gRef Phi (V p) x (X x)
            simpa [covL, covR, refPb, metricCov, pushFwdSection_apply_at_image] using hcov'
          have hslots : (fun q : Fin (a + 2) =>
              mfderiv I I (Phi : M -> N) x
                (Function.update (fun q : Fin (a + 2) => V q x) p covL q)) =
              Function.update
                (fun q : Fin (a + 2) => pushFwdSection (I := I) Phi (V q) (Phi x))
                p covR := by
            funext q
            by_cases hqp : q = p
            · subst q
              simpa [Function.update] using hcov
            · rw [Function.update_of_ne hqp, Function.update_of_ne hqp]
              simp [pushFwdSection_apply_at_image]
          have hih := ih x (Function.update (fun q : Fin (a + 2) => V q x) p covL)
          calc
            metricCovDeriv (I := I) hPb refPb a x
                (Function.update (fun q : Fin (a + 2) => V q x) p covL) =
              metricCovDeriv (I := I) h gRef a (Phi x)
                (fun q : Fin (a + 2) =>
                  mfderiv I I (Phi : M -> N) x
                    (Function.update (fun q : Fin (a + 2) => V q x) p covL q)) := by
                simpa [hPb, refPb, covL] using hih
            _ =
              metricCovDeriv (I := I) h gRef a (Phi x)
                (Function.update
                  (fun q : Fin (a + 2) =>
                    pushFwdSection (I := I) Phi (V q) (Phi x))
                  p covR) := by
                congr 1
        rw [hderiv, hsum]
      have hslots :
          slots = Fin.cons (slots 0) (fun q : Fin (a + 2) => slots q.succ) := by
        funext q
        refine Fin.cases ?_ (fun p => ?_) q
        · rw [Fin.cons_zero]
        · rw [Fin.cons_succ]
      have hpushSlots :
          (fun q : Fin ((a + 1) + 2) =>
              mfderiv I I (Phi : M -> N) x (slots q)) =
            Fin.cons (mfderiv I I (Phi : M -> N) x (slots 0))
              (fun q : Fin (a + 2) =>
                mfderiv I I (Phi : M -> N) x (slots q.succ)) := by
        funext q
        refine Fin.cases ?_ (fun p => ?_) q
        · rw [Fin.cons_zero]
        · rw [Fin.cons_succ]
      rw [hpushSlots, hslots]
      simpa [hX, hV, pushFwdSection_apply_at_image] using hsmooth

/-- The metric-covariant difference tower transports under pullback by a
diffeomorphism, evaluated on arbitrary slots.  This is the algebraic bridge
from the all-orders tower naturality theorem to the seminorm transport layer. -/
theorem metricDiffCovDerivAt_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (gk gInf gRef : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (a : Nat) (x : M) (slots : Fin (a + 2) -> TangentSpace I x) :
    metricDiffCovDerivAt (I := I) a
        (Diffeomorph.pullbackMetric (I := I) gk Phi)
        (Diffeomorph.pullbackMetric (I := I) gInf Phi)
        (Diffeomorph.pullbackMetric (I := I) gRef Phi) x slots =
      metricDiffCovDerivAt (I := I) a gk gInf gRef (Phi x)
        (fun q : Fin (a + 2) => mfderiv I I (Phi : M -> N) x (slots q)) := by
  simp [metricDiffCovDerivAt, metricCovDeriv_pullback]

private lemma infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide

/-- Squared norms of covariant tensors are preserved by a pullback metric, in
an orthonormal source basis.  The tensor on the source is supplied by its
evaluated pullback relation `hT`, avoiding a separate cross-manifold tensor
object. -/
theorem normSq0S_pullback_eval_of_orthonormal
    [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 1 M] [IsManifold I 1 N]
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j : Idx,
      (Diffeomorph.pullbackMetric (I := I) g Phi).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (Tpb : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s x)
    (T : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := N) s (Phi x))
    (hT : ∀ slots : Fin s -> TangentSpace I x,
      Tpb slots =
        T (fun q : Fin s => mfderiv I I (Phi : M -> N) x (slots q))) :
    Tensor0SBundle.normSq0S (I := I)
        (Diffeomorph.pullbackMetric (I := I) g Phi) x s Tpb =
      Tensor0SBundle.normSq0S (I := I) g (Phi x) s T := by
  classical
  let dPhi : TangentSpace I x ≃L[Real] TangentSpace I (Phi x) :=
    Diffeomorph.mfderivToContinuousLinearEquiv Phi infty_ne_zero x
  let basis' : Module.Basis Idx Real (TangentSpace I (Phi x)) :=
    basis.map dPhi.toLinearEquiv
  have hdPhi_apply : ∀ v : TangentSpace I x,
      dPhi v = mfderiv I I (Phi : M -> N) x v := by
    intro v
    have h :=
      Diffeomorph.mfderivToContinuousLinearEquiv_coe
        (Φ := Phi) (x := x) infty_ne_zero
    exact congrArg (fun f : TangentSpace I x →L[Real] TangentSpace I (Phi x) => f v) h
  have hbasis'_apply : ∀ i : Idx,
      basis' i = mfderiv I I (Phi : M -> N) x (basis i) := by
    intro i
    have hmap : basis' i = dPhi (basis i) := by
      show (basis.map dPhi.toLinearEquiv) i = dPhi (basis i)
      rw [Module.Basis.map_apply]
      rfl
    rw [hmap, hdPhi_apply (basis i)]
  have hON' : ∀ i j : Idx,
      g.inner (Phi x) (basis' i) (basis' j) =
        if i = j then (1 : Real) else 0 := by
    intro i j
    have hsrc := hON i j
    rw [Diffeomorph.pullbackMetric_inner] at hsrc
    simpa [hbasis'_apply i, hbasis'_apply j] using hsrc
  have hinv :
      MetricInverseInBasis_gen (I := I)
        (Diffeomorph.pullbackMetric (I := I) g Phi) x basis
        (identityInvMetric (Idx := Idx)) := by
    have h :=
      metricInverseInBasis_of_orthonormal
        (I := I) (Diffeomorph.pullbackMetric (I := I) g Phi) basis hON
    simpa [identityInvMetric, diagonalInvMetric] using h
  have hinv' :
      MetricInverseInBasis_gen (I := I) g (Phi x) basis'
        (identityInvMetric (Idx := Idx)) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) g basis' hON'
    simpa [identityInvMetric, diagonalInvMetric] using h
  rw [normSq0S_identity_eq_sum_sq (I := I)
      (Diffeomorph.pullbackMetric (I := I) g Phi) x s basis hinv Tpb,
    normSq0S_identity_eq_sum_sq (I := I) g (Phi x) s basis' hinv' T]
  apply Finset.sum_congr rfl
  intro slots _
  congr 1
  rw [component0S_apply, component0S_apply, hT]
  exact congrArg T (funext fun q => (hbasis'_apply (slots q)).symm)

/-- Pointwise `metricDerivNorm` is preserved under pullback by a diffeomorphism,
once the source tensor norm is evaluated in an orthonormal basis for the
pullback reference metric.  The remaining task for the source-domain layer is
to package the choice of such a basis and lift this pointwise equality through
`metricDerivNormSupOn`. -/
theorem metricDerivNorm_pullback_of_orthonormal
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (gk gInf gRef : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (a : Nat) (x : M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j : Idx,
      (Diffeomorph.pullbackMetric (I := I) gRef Phi).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    metricDerivNorm (I := I) a
        (Diffeomorph.pullbackMetric (I := I) gk Phi)
        (Diffeomorph.pullbackMetric (I := I) gInf Phi)
        (Diffeomorph.pullbackMetric (I := I) gRef Phi) x =
      metricDerivNorm (I := I) a gk gInf gRef (Phi x) := by
  unfold metricDerivNorm
  rw [normSq0S_pullback_eval_of_orthonormal (I := I)
    (g := gRef) (Phi := Phi) (x := x) (s := a + 2)
    (basis := basis) hON
    (Tpb := metricDiffCovDerivAt (I := I) a
      (Diffeomorph.pullbackMetric (I := I) gk Phi)
      (Diffeomorph.pullbackMetric (I := I) gInf Phi)
      (Diffeomorph.pullbackMetric (I := I) gRef Phi) x)
    (T := metricDiffCovDerivAt (I := I) a gk gInf gRef (Phi x)) ?_]
  intro slots
  exact metricDiffCovDerivAt_pullback (I := I) gk gInf gRef Phi a x slots

/-- Pointwise `metricDerivNorm` is invariant under simultaneous pullback of the
two metrics being compared and the reference metric. -/
theorem metricDerivNorm_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (gk gInf gRef : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (a : Nat) (x : M) :
    metricDerivNorm (I := I) a
        (Diffeomorph.pullbackMetric (I := I) gk Phi)
        (Diffeomorph.pullbackMetric (I := I) gInf Phi)
        (Diffeomorph.pullbackMetric (I := I) gRef Phi) x =
      metricDerivNorm (I := I) a gk gInf gRef (Phi x) := by
  classical
  obtain ⟨basis, hON⟩ :=
    exists_gOrthonormalBasis
      (I := I) (Diffeomorph.pullbackMetric (I := I) gRef Phi) x
  exact
    metricDerivNorm_pullback_of_orthonormal
      (I := I) gk gInf gRef Phi a x basis hON

/-- Pullback invariance lifted to the raw `metricDerivNormSupOn` seminorm: the
source supremum over `K` equals the target supremum over `Phi '' K`. -/
theorem metricDerivNormSupOn_pullback_image
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (K : Set M) (p : Nat)
    (gk gInf gRef : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N) :
    metricDerivNormSupOn (I := I) K p
        (Diffeomorph.pullbackMetric (I := I) gk Phi)
        (Diffeomorph.pullbackMetric (I := I) gInf Phi)
        (Diffeomorph.pullbackMetric (I := I) gRef Phi) =
      metricDerivNormSupOn (I := I) (Phi '' K) p gk gInf gRef := by
  unfold metricDerivNormSupOn
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨a, ha, x, hxK, hr⟩
    refine ⟨a, ha, Phi x, ⟨x, hxK, rfl⟩, ?_⟩
    rw [← hr]
    exact (metricDerivNorm_pullback (I := I) gk gInf gRef Phi a x).symm
  · rintro ⟨a, ha, y, hy, hr⟩
    rcases hy with ⟨x, hxK, rfl⟩
    refine ⟨a, ha, x, hxK, ?_⟩
    rw [metricDerivNorm_pullback (I := I) gk gInf gRef Phi a x]
    exact hr

end HCGCompactness
end DifferentialGeometry
