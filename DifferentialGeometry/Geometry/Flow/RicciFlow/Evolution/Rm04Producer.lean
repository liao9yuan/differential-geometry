import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Rm04Reduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Trace
import DifferentialGeometry.Geometry.Curvature.CurvatureActionLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRmDiff

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Producers for the `Rm04Reduction` input packages

`Evolution/Rm04Reduction.lean` proves the static reduction
`rm04VarRHS = Δ Rm − 2(B − B + B − B) − drift` from ten named inputs.  This module
discharges those inputs from a Ricci-flow solution `S` (and `hS`) alone.

Current content: the canonical coordinate-frame lowered-curvature component array
`rmComp`, and the discharge of the algebraic-symmetry package `Rm04Symm` for it.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- The canonical lowered-curvature component array of a Ricci-flow solution in the
coordinate frame centred at `x₀`, in the `FourComp` currency of `Evolution/Uhlenbeck.lean`.

This is `realizedRmBase` written with `vec4` instead of a `Fin 4` slot map, so that the
tensor-level curvature-symmetry producers of `Evolution/Ricci/Trace.lean` apply to it
directly. -/
def rmComp
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M) :
    FourComp M (CoordinateIdx (𝕜 := Real) E) :=
  fun t x i j k l =>
    S.base.rm04 t x
      (DifferentialGeometry.Integral.Connection.vec4 (I := I)
        (coordinateFrameAt (I := I) x₀ i x) (coordinateFrameAt (I := I) x₀ j x)
        (coordinateFrameAt (I := I) x₀ k x) (coordinateFrameAt (I := I) x₀ l x))

/-- **`Rm04Symm` discharged from the solution.**  The algebraic curvature symmetries
— antisymmetry in each slot pair, pair symmetry, and the first Bianchi identity — hold
for `rmComp` at every regular time and every point, with `S` and `hS` as the only inputs.

This discharges the `hsym` package of `rm04Var_eq_uhl` (`Evolution/Rm04Reduction.lean`)
and the `Rm04Symm` argument of `rmQuad_eq_b`. -/
theorem rm04SymmOfSol
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) :
    Rm04Symm (rmComp (I := I) S x₀ (t : Real) x) := by
  have hRm13 :
      ∀ τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
          (S.family.connection (τ : Real)) (S.base.rm13 (τ : Real)) :=
    fun τ => rm13OfSol (I := I) S (τ : Real) (D.regular_subset τ.2)
  have hLower :
      ∀ (τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
        (y : M),
        DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I)
          (S.family.metric (τ : Real)) y
          (S.base.rm13 (τ : Real) y) (S.base.rm04 (τ : Real) y) :=
    fun τ y => solution_rm04LowersRm13At (I := I) S (τ : Real) y
  have hskew :=
    rm04InputSkew_regular (I := I) S S.base.rm13 S.base.rm04 hRm13 hLower t x
  have hpair :=
    rm04PairSymm_regular (I := I) S hS S.base.rm13 S.base.rm04 hRm13 hLower t x
  have hbi :=
    rm04FirstBianchi_regular (I := I) S hS S.base.rm13 S.base.rm04 hRm13 hLower t x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c d
    exact hskew (coordinateFrameAt (I := I) x₀ b x) (coordinateFrameAt (I := I) x₀ a x)
      (coordinateFrameAt (I := I) x₀ c x) (coordinateFrameAt (I := I) x₀ d x)
  · intro a b c d
    calc rmComp (I := I) S x₀ (t : Real) x a b c d
        = rmComp (I := I) S x₀ (t : Real) x c d a b :=
          hpair (coordinateFrameAt (I := I) x₀ a x) (coordinateFrameAt (I := I) x₀ b x)
            (coordinateFrameAt (I := I) x₀ c x) (coordinateFrameAt (I := I) x₀ d x)
      _ = -rmComp (I := I) S x₀ (t : Real) x d c a b :=
          hskew (coordinateFrameAt (I := I) x₀ d x) (coordinateFrameAt (I := I) x₀ c x)
            (coordinateFrameAt (I := I) x₀ a x) (coordinateFrameAt (I := I) x₀ b x)
      _ = -rmComp (I := I) S x₀ (t : Real) x a b d c :=
          neg_inj.mpr
            (hpair (coordinateFrameAt (I := I) x₀ d x)
              (coordinateFrameAt (I := I) x₀ c x) (coordinateFrameAt (I := I) x₀ a x)
              (coordinateFrameAt (I := I) x₀ b x))
  · intro a b c d
    exact hpair (coordinateFrameAt (I := I) x₀ a x) (coordinateFrameAt (I := I) x₀ b x)
      (coordinateFrameAt (I := I) x₀ c x) (coordinateFrameAt (I := I) x₀ d x)
  · intro a b c d
    exact hbi (coordinateFrameAt (I := I) x₀ a x) (coordinateFrameAt (I := I) x₀ b x)
      (coordinateFrameAt (I := I) x₀ c x) (coordinateFrameAt (I := I) x₀ d x)

/-! ## The once-differentiated second Bianchi identity

`Rm04LapIn.bianchi2` is the only input of `rm04Var_eq_uhl` with no pre-existing
producer.  It is the covariant derivative of the second Bianchi identity, which holds
for the canonical bundled `∇Rm` at *every* point; differentiating a globally vanishing
cyclic combination is what produces it. -/

/-- **Second Bianchi identity for the canonical bundled `∇Rm` of a solution.**
The cyclic sum over the derivative slot and the first two curvature slots vanishes at
every time and every point, with `S` as the only input. -/
theorem rmSecondAt
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    DifferentialGeometry.Integral.Connection.SecondBianchiAt (I := I)
      (nablaRm04Field (I := I) S t x) := by
  have h := DifferentialGeometry.Integral.Connection.canRmSecond
    (I := I) (M := M) (S.family.metric t) (x := x)
  simpa [nablaRm04Field, SolutionOn.family, SolutionFamily.connection,
    SolutionFamily.rm04, metricCov, metricRm04,
    DifferentialGeometry.Integral.Connection.metricCov,
    DifferentialGeometry.Integral.Connection.metricRm04] using h

/-- The three-cycle of the first three slots of a rank-`5` covariant tensor, fixing the
last two slots: the permutation appearing in the second Bianchi identity. -/
private def rotA : Equiv.Perm (Fin 5) :=
  ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide, by decide⟩

/-- The square of `rotA`. -/
private def rotB : Equiv.Perm (Fin 5) :=
  ⟨![2, 0, 1, 3, 4], ![1, 2, 0, 3, 4], by decide, by decide⟩

private theorem vec5_rotA {x : M} (A B C V W : TangentSpace I x) :
    DifferentialGeometry.Integral.Connection.vec5 (I := I) A B C V W ∘ rotA =
      DifferentialGeometry.Integral.Connection.vec5 (I := I) B C A V W := by
  funext i
  fin_cases i <;> rfl

private theorem vec5_rotB {x : M} (A B C V W : TangentSpace I x) :
    DifferentialGeometry.Integral.Connection.vec5 (I := I) A B C V W ∘ rotB =
      DifferentialGeometry.Integral.Connection.vec5 (I := I) C A B V W := by
  funext i
  fin_cases i <;> rfl

private theorem vec5_self {x : M} (u : Fin 5 → TangentSpace I x) :
    DifferentialGeometry.Integral.Connection.vec5 (I := I) (u 0) (u 1) (u 2) (u 3) (u 4) = u := by
  funext i
  fin_cases i <;> rfl

/-- `SecondBianchiAt` in slot-function form: the cyclic sum over `rotA` vanishes. -/
private theorem secondCyc {x : M}
    {al : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x}
    (h : DifferentialGeometry.Integral.Connection.SecondBianchiAt (I := I) al)
    (u : Fin 5 → TangentSpace I x) :
    al u + al (u ∘ rotA) + al (u ∘ rotB) = 0 := by
  have h5 := h (u 0) (u 1) (u 2) (u 3) (u 4)
  rw [← vec5_self (I := I) u, vec5_rotA, vec5_rotB]
  exact h5

/-- Local evaluation of `∇α` on a permuted family of smooth slot fields: the derivative
correction sum is reindexed so that the differentiated slot field, not its position, is
the summation variable. -/
private theorem nabPerm
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin 5 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (al : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (x : M) (sg : Equiv.Perm (Fin 5)) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 cov X al x
        (fun a : Fin 5 => V (sg a) x)
      = extDerivFun (I := I)
            (fun p : M => al p (fun a : Fin 5 => V (sg a) p)) x (X x)
        - ∑ c : Fin 5,
            al x (fun b : Fin 5 =>
              Function.update (fun d : Fin 5 => V d x) c
                ((cov (fun p : M => V c p) x) (X x)) (sg b)) := by
  classical
  refine (nabla0SFun_eval_smooth_slots (I := I) cov X (fun a : Fin 5 => V (sg a)) al x).trans ?_
  congr 1
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_)
    (Equiv.sum_comp sg (fun c : Fin 5 =>
      al x (fun b : Fin 5 =>
        Function.update (fun d : Fin 5 => V d x) c
          ((cov (fun p : M => V c p) x) (X x)) (sg b))))
  congr 1
  funext b
  by_cases hb : b = a
  · subst hb
    simp
  · have hne : sg b ≠ sg a := fun hh => hb (sg.injective hh)
    simp [hb, hne]

/-- **The cyclic sum of `∇α` vanishes when the cyclic sum of `α` vanishes everywhere.**
This is the differentiation step behind the once-differentiated second Bianchi identity:
the derivative of the identically vanishing cyclic scalar kills the leading term, and each
group of connection corrections is again a cyclic sum. -/
private theorem nabCyc
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin 5 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (al : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (hcyc : ∀ y : M, ∀ u : Fin 5 → TangentSpace I y,
      al y u + al y (u ∘ rotA) + al y (u ∘ rotB) = 0)
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 cov X al x
        (fun a : Fin 5 => V a x)
      + nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 cov X al x
        (fun a : Fin 5 => V (rotA a) x)
      + nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 cov X al x
        (fun a : Fin 5 => V (rotB a) x) = 0 := by
  classical
  have e0 := nabPerm (I := I) cov X V al x 1
  simp only [Equiv.Perm.coe_one, id_eq] at e0
  have e1 := nabPerm (I := I) cov X V al x rotA
  have e2 := nabPerm (I := I) cov X V al x rotB
  rw [e0, e1, e2]
  -- the leading derivative terms
  have hd0 : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => al p (fun a : Fin 5 => V a p)) x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt (I := I) al V x).mdifferentiableAt (by simp)
  have hd1 : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => al p (fun a : Fin 5 => V (rotA a) p)) x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt (I := I) al
      (fun a : Fin 5 => V (rotA a)) x).mdifferentiableAt (by simp)
  have hd2 : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => al p (fun a : Fin 5 => V (rotB a) p)) x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt (I := I) al
      (fun a : Fin 5 => V (rotB a)) x).mdifferentiableAt (by simp)
  have hd01 : MDifferentiableAt I 𝓘(Real, Real)
      ((fun p : M => al p (fun a : Fin 5 => V a p)) +
        fun p : M => al p (fun a : Fin 5 => V (rotA a) p)) x := hd0.add hd1
  have hzero :
      ((fun p : M => al p (fun a : Fin 5 => V a p)) +
          (fun p : M => al p (fun a : Fin 5 => V (rotA a) p)) +
          fun p : M => al p (fun a : Fin 5 => V (rotB a) p)) = (0 : M → Real) := by
    funext p
    exact hcyc p (fun b : Fin 5 => V b p)
  have estep := extDerivFun_add (I := I) hd01 hd2
  rw [hzero, extDerivFun_zero, extDerivFun_add (I := I) hd0 hd1] at estep
  have hD := congrArg (fun L : TangentSpace I x →L[Real] Real => L (X x)) estep
  simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.add_apply] at hD
  -- the connection-correction sums
  have hS :
      (∑ c : Fin 5,
          al x (fun b : Fin 5 =>
            Function.update (fun d : Fin 5 => V d x) c
              ((cov (fun p : M => V c p) x) (X x)) b))
        + (∑ c : Fin 5,
            al x (fun b : Fin 5 =>
              Function.update (fun d : Fin 5 => V d x) c
                ((cov (fun p : M => V c p) x) (X x)) (rotA b)))
        + (∑ c : Fin 5,
            al x (fun b : Fin 5 =>
              Function.update (fun d : Fin 5 => V d x) c
                ((cov (fun p : M => V c p) x) (X x)) (rotB b))) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun c _ => ?_
    exact hcyc x (Function.update (fun d : Fin 5 => V d x) c
      ((cov (fun p : M => V c p) x) (X x)))
  linarith [hD, hS]

/-- **The once-differentiated second Bianchi identity.**  The cyclic sum of the canonical
bundled `∇²Rm` of a Ricci-flow solution over the second derivative slot and the first two
curvature slots vanishes, at every time and every point, from `S` alone.

This is the tensor-level source of `Rm04LapIn.bianchi2`. -/
theorem rm2Bianchi
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (P A B C U W : TangentSpace I x) :
    nabla2Rm04Field (I := I) S t x
        (Fin.cons P (DifferentialGeometry.Integral.Connection.vec5 (I := I) A B C U W))
      + nabla2Rm04Field (I := I) S t x
        (Fin.cons P (DifferentialGeometry.Integral.Connection.vec5 (I := I) B C A U W))
      + nabla2Rm04Field (I := I) S t x
        (Fin.cons P (DifferentialGeometry.Integral.Connection.vec5 (I := I) C A B U W)) = 0 := by
  classical
  obtain ⟨X, hX⟩ :=
    ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x P
  have hVex : ∀ a : Fin 5,
      ∃ s : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
        s x = DifferentialGeometry.Integral.Connection.vec5 (I := I) A B C U W a := by
    intro a
    exact ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x _
  choose V hV using hVex
  have hstep : ∀ w : Fin 5 → TangentSpace I x,
      nabla2Rm04Field (I := I) S t x (Fin.cons P w)
        = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5
            (S.family.connection t) X (nablaRm04Field (I := I) S t) x w := by
    intro w
    rw [← hX]
    exact totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      5 (S.family.connection t) X (nablaRm04Field (I := I) S t) x w
  have hV0 : (fun a : Fin 5 => V a x)
      = DifferentialGeometry.Integral.Connection.vec5 (I := I) A B C U W := by
    funext a
    exact hV a
  have hVA : (fun a : Fin 5 => V (rotA a) x)
      = DifferentialGeometry.Integral.Connection.vec5 (I := I) B C A U W := by
    change (fun b : Fin 5 => V b x) ∘ rotA = _
    rw [hV0, vec5_rotA]
  have hVB : (fun a : Fin 5 => V (rotB a) x)
      = DifferentialGeometry.Integral.Connection.vec5 (I := I) C A B U W := by
    change (fun b : Fin 5 => V b x) ∘ rotB = _
    rw [hV0, vec5_rotB]
  rw [hstep, hstep, hstep, ← hV0, ← hVA, ← hVB]
  exact nabCyc (I := I) (S.family.connection t) X V (nablaRm04Field (I := I) S t)
    (fun y u => secondCyc (I := I) (rmSecondAt (I := I) S t y) u) x

/-- **The algebraic curvature symmetries of the canonical bundled `∇²Rm`.**  The two
derivative slots are inert: `∇²Rm` is antisymmetric in each curvature slot pair and
symmetric under exchanging the two pairs. -/
theorem rm2SymmAt
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    (∀ A B X Y Z W : TangentSpace I x,
        nabla2Rm04Field (I := I) S t x
            (Fin.cons A (DifferentialGeometry.Integral.Connection.vec5 (I := I) B X Y Z W)) =
          -nabla2Rm04Field (I := I) S t x
            (Fin.cons A (DifferentialGeometry.Integral.Connection.vec5 (I := I) B X Y W Z))) ∧
      (∀ A B X Y Z W : TangentSpace I x,
        nabla2Rm04Field (I := I) S t x
            (Fin.cons A (DifferentialGeometry.Integral.Connection.vec5 (I := I) B Y X Z W)) =
          -nabla2Rm04Field (I := I) S t x
            (Fin.cons A (DifferentialGeometry.Integral.Connection.vec5 (I := I) B X Y Z W))) ∧
        ∀ A B X Y Z W : TangentSpace I x,
          nabla2Rm04Field (I := I) S t x
              (Fin.cons A (DifferentialGeometry.Integral.Connection.vec5 (I := I) B X Y Z W)) =
            nabla2Rm04Field (I := I) S t x
              (Fin.cons A (DifferentialGeometry.Integral.Connection.vec5 (I := I) B Z W X Y)) := by
  have h := DifferentialGeometry.Integral.Connection.canRm2Symm
    (I := I) (M := M) (S.family.metric t) (x := x)
  simpa [nabla2Rm04Field, nablaRm04Field, SolutionOn.family, SolutionFamily.connection,
    SolutionFamily.rm04, metricCov, metricRm04,
    DifferentialGeometry.Integral.Connection.metricCov,
    DifferentialGeometry.Integral.Connection.metricRm04] using h

/-- The canonical second-covariant-derivative curvature component array of a solution in
the coordinate frame centred at `x₀`, in the `n2Rm` slot order of `Rm04LapIn`:
`nab2RmComp S x₀ t x a b c d e f = (∇_a ∇_b Rm)_{cdef}`. -/
def nab2RmComp
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M) :
    Real → M → CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E →
      CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E →
      CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real :=
  fun t x a b c d e f =>
    nabla2Rm04Field (I := I) S t x
      (Fin.cons (coordinateFrameAt (I := I) x₀ a x)
        (DifferentialGeometry.Integral.Connection.vec5 (I := I)
          (coordinateFrameAt (I := I) x₀ b x) (coordinateFrameAt (I := I) x₀ c x)
          (coordinateFrameAt (I := I) x₀ d x) (coordinateFrameAt (I := I) x₀ e x)
          (coordinateFrameAt (I := I) x₀ f x)))

/-! ### The metric traces relating `∇²Ric` to `∇²Rm` -/

/-- The canonical first covariant derivative of Ricci, spelled out so that the private
`nablaRicField` of `Evolution/Scalar/IntrinsicDerivation.lean` is nameable here. -/
private def solNabRic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    2 (S.family.connection t) (S.ricci t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      2 (S.family.connection t) (connSmoothInf (I := I) S t) (S.ricci t))

/-- The canonical second covariant derivative of Ricci. -/
private def solNab2Ric
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    3 (S.family.connection t) (solNabRic (I := I) S t) x

private theorem coordNab2Eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M) (t : Real)
    (d a i j : CoordinateIdx (𝕜 := Real) E) :
    coordNab2Ric (I := I) S x₀ t x₀ d a i j =
      solNab2Ric (I := I) S t x₀
        (DifferentialGeometry.Integral.Connection.vec4 (I := I)
          (coordinateFrameAt (I := I) x₀ d x₀) (coordinateFrameAt (I := I) x₀ a x₀)
          (coordinateFrameAt (I := I) x₀ i x₀) (coordinateFrameAt (I := I) x₀ j x₀)) := by
  simpa only [solNab2Ric, solNabRic] using
    coordNab2Ric_eq_nabla2RicField (I := I) S x₀ t d a i j

/-- **`∇²Ric` is the first metric trace of `∇²Rm`** in the coordinate frame at the centre.
This is `Rm04LapIn.n2RicTrace` for the canonical coordinate arrays. -/
theorem n2RicTr
    [I.Boundaryless] [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M) (t : Real)
    (a b c d : CoordinateIdx (𝕜 := Real) E) :
    coordNab2Ric (I := I) S x₀ t x₀ a b c d
      = ∑ p : CoordinateIdx (𝕜 := Real) E, ∑ q : CoordinateIdx (𝕜 := Real) E,
          coordInv (I := I) S x₀ t x₀ p q * nab2RmComp (I := I) S x₀ t x₀ a b p c d q := by
  classical
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ := coordinateFrameAt_mem (I := I) x₀
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  let basis := hframe.toBasisAt hx₀
  let gInvAt : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real :=
    fun k l => coordInv (I := I) S x₀ t x₀ k l
  have hinv :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric t) x₀ basis gInvAt := by
    have h :=
      DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) (S.family.metric t) x₀ hx₀
    simpa [basis, hframe, gInvAt, coordInv, IsLocalFrameOn.toBasisAt_coe] using h
  have hb : ∀ i : CoordinateIdx (𝕜 := Real) E,
      (basis i : TangentSpace I x₀) = coordinateFrameAt (I := I) x₀ i x₀ := by
    intro i
    simp [basis, IsLocalFrameOn.toBasisAt_coe]
  have h := DifferentialGeometry.Integral.Connection.canNabla2RicTrace
    (I := I) (M := M) (S.family.metric t) basis gInvAt hinv
    (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ b x₀)
    (coordinateFrameAt (I := I) x₀ c x₀) (coordinateFrameAt (I := I) x₀ d x₀)
  rw [coordNab2Eq (I := I) S x₀ t a b c d]
  simpa [solNab2Ric, solNabRic, nab2RmComp, nabla2Rm04Field, nablaRm04Field,
    SolutionOn.family, SolutionOn.ricci, SolutionFamily.connection, SolutionFamily.ricci,
    SolutionFamily.rm04, metricCov, metricRicci, metricRm04,
    DifferentialGeometry.Integral.Connection.metricCov,
    DifferentialGeometry.Integral.Connection.metricRicci,
    DifferentialGeometry.Integral.Connection.metricRm04, gInvAt, hb] using h

/-- **Ricci is the first metric trace of `Rm`** in the coordinate frame at the centre.
This is `Rm04LapIn.ricTrace` for the canonical coordinate arrays. -/
theorem ricTr
    [I.Boundaryless] [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (a b : CoordinateIdx (𝕜 := Real) E) :
    ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) (t : Real) x₀ a b
      = ∑ p : CoordinateIdx (𝕜 := Real) E, ∑ q : CoordinateIdx (𝕜 := Real) E,
          coordInv (I := I) S x₀ (t : Real) x₀ p q *
            rmComp (I := I) S x₀ (t : Real) x₀ p a b q := by
  classical
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ := coordinateFrameAt_mem (I := I) x₀
  have hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric (t : Real)) x₀
        (hframe.toBasisAt hx₀)
        (fun k l : CoordinateIdx (𝕜 := Real) E =>
          coordInv (I := I) S x₀ (t : Real) x₀ k l) :=
    metricInverseInBasis_of_local
      (I := I) S (coordInv (I := I) S x₀)
      (coordinateFrameAt (I := I) x₀) hframe
      (coordInvLocal (I := I) S x₀) (t : Real) hx₀
  have h := DifferentialGeometry.Integral.Connection.ricciFirstTraceAt_of_rm13_section
    (I := I) (S.family.metric (t : Real)) (hframe.toBasisAt hx₀)
    (fun k l : CoordinateIdx (𝕜 := Real) E => coordInv (I := I) S x₀ (t : Real) x₀ k l)
    hinvAt (S.ricci (t : Real)) (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real))
    (ricciTraceOfSol (I := I) S (t : Real) (D.regular_subset t.2))
    (solution_rm04LowersRm13At (I := I) S (t : Real) x₀)
    (fun i j => coordInvSymmOn (I := I) S x₀ (t : Real) hx₀ i j)
  simpa [ricciCompInFrame, SolutionOn.ricciAt, SolutionFamily.ricciAt, rmComp,
    IsLocalFrameOn.toBasisAt_coe] using h a b

private theorem sumSwap {Idx : Type*} [Fintype Idx] (F : Idx → Idx → Real) :
    (∑ p : Idx, ∑ r : Idx, F p r) = ∑ p : Idx, ∑ r : Idx, F r p :=
  Finset.sum_comm

private theorem sumMulPair
    {Idx : Type*} [Fintype Idx] (gInv : Idx → Idx → Real) (Xf Yf : Idx → Real) :
    (∑ p : Idx, (∑ r : Idx, gInv p r * Xf r) * Yf p)
      = ∑ p : Idx, ∑ r : Idx, gInv p r * (Xf r * Yf p) := by
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- **The `(0,4)` Ricci identity in coordinate-frame components at the centre.**
This is `Rm04LapIn.ricciId` for the canonical coordinate arrays. -/
theorem rmRicciId
    [I.Boundaryless] [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (a b c d e f : CoordinateIdx (𝕜 := Real) E) :
    nab2RmComp (I := I) S x₀ (t : Real) x₀ a b c d e f
        - nab2RmComp (I := I) S x₀ (t : Real) x₀ b a c d e f
      = -∑ q : CoordinateIdx (𝕜 := Real) E, ∑ r : CoordinateIdx (𝕜 := Real) E,
          coordInv (I := I) S x₀ (t : Real) x₀ q r *
            (rmComp (I := I) S x₀ (t : Real) x₀ a b c r *
                rmComp (I := I) S x₀ (t : Real) x₀ q d e f +
              rmComp (I := I) S x₀ (t : Real) x₀ a b d r *
                rmComp (I := I) S x₀ (t : Real) x₀ c q e f +
              rmComp (I := I) S x₀ (t : Real) x₀ a b e r *
                rmComp (I := I) S x₀ (t : Real) x₀ c d q f +
              rmComp (I := I) S x₀ (t : Real) x₀ a b f r *
                rmComp (I := I) S x₀ (t : Real) x₀ c d e q) := by
  classical
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ := coordinateFrameAt_mem (I := I) x₀
  have hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric (t : Real)) x₀
        (hframe.toBasisAt hx₀)
        (fun k l : CoordinateIdx (𝕜 := Real) E =>
          coordInv (I := I) S x₀ (t : Real) x₀ k l) :=
    metricInverseInBasis_of_local
      (I := I) S (coordInv (I := I) S x₀)
      (coordinateFrameAt (I := I) x₀) hframe
      (coordInvLocal (I := I) S x₀) (t : Real) hx₀
  have hb : ∀ i : CoordinateIdx (𝕜 := Real) E,
      ((hframe.toBasisAt hx₀) i : TangentSpace I x₀)
        = coordinateFrameAt (I := I) x₀ i x₀ := by
    intro i
    simp [IsLocalFrameOn.toBasisAt_coe]
  have hri := rm04_ricciIdentityAt (I := I) S hS t x₀
    (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ b x₀)
    (DifferentialGeometry.Integral.Connection.vec4 (I := I)
      (coordinateFrameAt (I := I) x₀ c x₀) (coordinateFrameAt (I := I) x₀ d x₀)
      (coordinateFrameAt (I := I) x₀ e x₀) (coordinateFrameAt (I := I) x₀ f x₀))
  rw [DifferentialGeometry.Integral.Connection.curvatureAction0SAt_eq_rm04
      (I := I) (S.family.metric (t : Real)) (hframe.toBasisAt hx₀)
      (fun k l : CoordinateIdx (𝕜 := Real) E => coordInv (I := I) S x₀ (t : Real) x₀ k l)
      hinvAt (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) x₀)
      (solution_rm04LowersRm13At (I := I) S (t : Real) x₀)] at hri
  have hin1 :
      DifferentialGeometry.Integral.Connection.metricTraceInput (I := I)
          (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ b x₀)
          (DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (coordinateFrameAt (I := I) x₀ c x₀) (coordinateFrameAt (I := I) x₀ d x₀)
            (coordinateFrameAt (I := I) x₀ e x₀) (coordinateFrameAt (I := I) x₀ f x₀))
        = Fin.cons (coordinateFrameAt (I := I) x₀ a x₀)
            (DifferentialGeometry.Integral.Connection.vec5 (I := I)
              (coordinateFrameAt (I := I) x₀ b x₀) (coordinateFrameAt (I := I) x₀ c x₀)
              (coordinateFrameAt (I := I) x₀ d x₀) (coordinateFrameAt (I := I) x₀ e x₀)
              (coordinateFrameAt (I := I) x₀ f x₀)) := by
    funext i
    fin_cases i <;> rfl
  have hin2 :
      DifferentialGeometry.Integral.Connection.metricTraceInput (I := I)
          (coordinateFrameAt (I := I) x₀ b x₀) (coordinateFrameAt (I := I) x₀ a x₀)
          (DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (coordinateFrameAt (I := I) x₀ c x₀) (coordinateFrameAt (I := I) x₀ d x₀)
            (coordinateFrameAt (I := I) x₀ e x₀) (coordinateFrameAt (I := I) x₀ f x₀))
        = Fin.cons (coordinateFrameAt (I := I) x₀ b x₀)
            (DifferentialGeometry.Integral.Connection.vec5 (I := I)
              (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
              (coordinateFrameAt (I := I) x₀ d x₀) (coordinateFrameAt (I := I) x₀ e x₀)
              (coordinateFrameAt (I := I) x₀ f x₀)) := by
    funext i
    fin_cases i <;> rfl
  rw [hin1, hin2] at hri
  refine hri.trans ?_
  congr 1
  have hs : ∀ (A B C W : TangentSpace I x₀),
      DifferentialGeometry.Integral.Connection.vec4 (I := I) A B C W 0 = A ∧
      DifferentialGeometry.Integral.Connection.vec4 (I := I) A B C W 1 = B ∧
      DifferentialGeometry.Integral.Connection.vec4 (I := I) A B C W 2 = C ∧
      DifferentialGeometry.Integral.Connection.vec4 (I := I) A B C W 3 = W :=
    fun _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩
  have hu : ∀ (A B C W Z : TangentSpace I x₀),
      Function.update (DifferentialGeometry.Integral.Connection.vec4 (I := I) A B C W) 0 Z =
          DifferentialGeometry.Integral.Connection.vec4 (I := I) Z B C W ∧
        Function.update (DifferentialGeometry.Integral.Connection.vec4 (I := I) A B C W) 1 Z =
          DifferentialGeometry.Integral.Connection.vec4 (I := I) A Z C W ∧
        Function.update (DifferentialGeometry.Integral.Connection.vec4 (I := I) A B C W) 2 Z =
          DifferentialGeometry.Integral.Connection.vec4 (I := I) A B Z W ∧
        Function.update (DifferentialGeometry.Integral.Connection.vec4 (I := I) A B C W) 3 Z =
          DifferentialGeometry.Integral.Connection.vec4 (I := I) A B C Z := by
    intro A B C W Z
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · funext i
        fin_cases i <;>
          simp [DifferentialGeometry.Integral.Connection.vec4]
  rw [Fin.sum_univ_four]
  simp only [(hs _ _ _ _).1, (hs _ _ _ _).2.1, (hs _ _ _ _).2.2.1, (hs _ _ _ _).2.2.2,
    (hu _ _ _ _ _).1, (hu _ _ _ _ _).2.1, (hu _ _ _ _ _).2.2.1, (hu _ _ _ _ _).2.2.2,
    hb, sumMulPair, rmComp]
  have hsum4 : ∀ F₁ F₂ F₃ F₄ :
      CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real,
      (∑ p : CoordinateIdx (𝕜 := Real) E, ∑ r : CoordinateIdx (𝕜 := Real) E, F₁ p r)
          + (∑ p : CoordinateIdx (𝕜 := Real) E, ∑ r : CoordinateIdx (𝕜 := Real) E, F₂ p r)
          + (∑ p : CoordinateIdx (𝕜 := Real) E, ∑ r : CoordinateIdx (𝕜 := Real) E, F₃ p r)
          + (∑ p : CoordinateIdx (𝕜 := Real) E, ∑ r : CoordinateIdx (𝕜 := Real) E, F₄ p r)
        = ∑ p : CoordinateIdx (𝕜 := Real) E, ∑ r : CoordinateIdx (𝕜 := Real) E,
            (F₁ p r + F₂ p r + F₃ p r + F₄ p r) := by
    intro F₁ F₂ F₃ F₄
    simp only [← Finset.sum_add_distrib]
  rw [hsum4]
  refine Eq.trans (sumSwap _) ?_
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  rw [coordInvSymmOn (I := I) S x₀ (t : Real) hx₀ r p]
  ring

/-- **`Rm04LapIn` discharged from the solution.**  All seven differential inputs of the
static reduction `rm04Var_eq_uhl` hold for the canonical coordinate-frame arrays at the
frame centre, at every regular time, from `S` and `hS` alone. -/
theorem rm04LapInOfSol
    [I.Boundaryless] [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) :
    Rm04LapIn (coordInv (I := I) S x₀ (t : Real) x₀)
      (rmComp (I := I) S x₀ (t : Real) x₀)
      (ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) (t : Real) x₀)
      (coordNab2Ric (I := I) S x₀ (t : Real) x₀)
      (nab2RmComp (I := I) S x₀ (t : Real) x₀) := by
  classical
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ := coordinateFrameAt_mem (I := I) x₀
  have hgi : ∀ p q : CoordinateIdx (𝕜 := Real) E,
      coordInv (I := I) S x₀ (t : Real) x₀ p q = coordInv (I := I) S x₀ (t : Real) x₀ q p :=
    fun p q => coordInvSymmOn (I := I) S x₀ (t : Real) hx₀ p q
  have hsymm := rm2SymmAt (I := I) S (t : Real) x₀
  have hswap12 : ∀ a b c d e f : CoordinateIdx (𝕜 := Real) E,
      nab2RmComp (I := I) S x₀ (t : Real) x₀ a b c d e f
        = -nab2RmComp (I := I) S x₀ (t : Real) x₀ a b d c e f := fun a b c d e f =>
    hsymm.2.1 (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ b x₀)
      (coordinateFrameAt (I := I) x₀ d x₀) (coordinateFrameAt (I := I) x₀ c x₀)
      (coordinateFrameAt (I := I) x₀ e x₀) (coordinateFrameAt (I := I) x₀ f x₀)
  have hpair : ∀ a b c d e f : CoordinateIdx (𝕜 := Real) E,
      nab2RmComp (I := I) S x₀ (t : Real) x₀ a b c d e f
        = nab2RmComp (I := I) S x₀ (t : Real) x₀ a b e f c d := fun a b c d e f =>
    hsymm.2.2 (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ b x₀)
      (coordinateFrameAt (I := I) x₀ c x₀) (coordinateFrameAt (I := I) x₀ d x₀)
      (coordinateFrameAt (I := I) x₀ e x₀) (coordinateFrameAt (I := I) x₀ f x₀)
  have hswap34 : ∀ a b c d e f : CoordinateIdx (𝕜 := Real) E,
      nab2RmComp (I := I) S x₀ (t : Real) x₀ a b c d e f
        = -nab2RmComp (I := I) S x₀ (t : Real) x₀ a b c d f e := by
    intro a b c d e f
    calc nab2RmComp (I := I) S x₀ (t : Real) x₀ a b c d e f
        = nab2RmComp (I := I) S x₀ (t : Real) x₀ a b e f c d := hpair a b c d e f
      _ = -nab2RmComp (I := I) S x₀ (t : Real) x₀ a b f e c d := hswap12 a b e f c d
      _ = -nab2RmComp (I := I) S x₀ (t : Real) x₀ a b c d f e :=
          neg_inj.mpr (hpair a b f e c d)
  refine ⟨?_, ?_, ?_, ?_, hswap12, hpair, ?_⟩
  · intro p a b c d e
    exact rm2Bianchi (I := I) S (t : Real) x₀
      (coordinateFrameAt (I := I) x₀ p x₀) (coordinateFrameAt (I := I) x₀ a x₀)
      (coordinateFrameAt (I := I) x₀ b x₀) (coordinateFrameAt (I := I) x₀ c x₀)
      (coordinateFrameAt (I := I) x₀ d x₀) (coordinateFrameAt (I := I) x₀ e x₀)
  · intro a b c d e f
    exact rmRicciId (I := I) S hS x₀ t a b c d e f
  · intro a b
    exact ricTr (I := I) S x₀ t a b
  · intro a b c d
    exact n2RicTr (I := I) S x₀ (t : Real) a b c d
  · intro a b c d
    have hcomm := Finset.sum_comm (s := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)))
      (t := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)))
      (f := fun p q : CoordinateIdx (𝕜 := Real) E =>
        coordInv (I := I) S x₀ (t : Real) x₀ p q *
          nab2RmComp (I := I) S x₀ (t : Real) x₀ a b p c d q)
    rw [n2RicTr (I := I) S x₀ (t : Real) a b c d,
      n2RicTr (I := I) S x₀ (t : Real) a b d c, hcomm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
    rw [hgi p q]
    congr 1
    calc nab2RmComp (I := I) S x₀ (t : Real) x₀ a b p c d q
        = nab2RmComp (I := I) S x₀ (t : Real) x₀ a b d q p c := hpair a b p c d q
      _ = -nab2RmComp (I := I) S x₀ (t : Real) x₀ a b q d p c := hswap12 a b d q p c
      _ = -(-nab2RmComp (I := I) S x₀ (t : Real) x₀ a b q d c p) :=
          congrArg Neg.neg (hswap34 a b q d p c)
      _ = nab2RmComp (I := I) S x₀ (t : Real) x₀ a b q d c p := neg_neg _

/-! ### The remaining scalar inputs of `rm04Var_eq_uhl` -/

private theorem rmCompBase
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M) (t : Real)
    (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    realizedRmBase (I := I) S x₀ t x₀ m
      = rmComp (I := I) S x₀ t x₀ (m 0) (m 1) (m 2) (m 3) := by
  rw [realizedRmBase_apply]
  unfold rmComp
  congr 1
  funext q
  fin_cases q <;> rfl

/-- **Index raising for the curvature coefficient.**  The `(1,3)` Christoffel curvature
coefficient at the frame centre is the inverse-metric raising of the last slot of the
lowered curvature component array.  This is the `hraise` input of `rm04Var_eq_uhl`. -/
theorem rmRaise
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (a b c d : CoordinateIdx (𝕜 := Real) E) :
    DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
        (I := I) (S.family.connection (t : Real)) x₀ a b c d
      = ∑ q : CoordinateIdx (𝕜 := Real) E,
          coordInv (I := I) S x₀ (t : Real) x₀ d q *
            rmComp (I := I) S x₀ (t : Real) x₀ a b c q := by
  classical
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ := coordinateFrameAt_mem (I := I) x₀
  have hlow : ∀ e : CoordinateIdx (𝕜 := Real) E,
      rmComp (I := I) S x₀ (t : Real) x₀ a b c e
        = ∑ p : CoordinateIdx (𝕜 := Real) E,
            DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
                (I := I) (S.family.connection (t : Real)) x₀ a b c p *
              metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
                (t : Real) x₀ e p := by
    intro e
    have h := realizedRmBase_eq_curvCoeff_lower (I := I) S x₀ (t : Real)
      (rm13OfSol (I := I) S (t : Real) (D.regular_subset t.2))
      (connCurvOfSol (I := I) S hS x₀ (t : Real) (D.regular_subset t.2))
      (fun q : Fin 4 => if q = 0 then a else if q = 1 then b else if q = 2 then c else e)
    rw [rmCompBase (I := I) S x₀ (t : Real)] at h
    simpa using h
  have hdelta : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      (∑ k : CoordinateIdx (𝕜 := Real) E,
        coordInv (I := I) S x₀ (t : Real) x₀ i k *
          metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) (t : Real) x₀ k j)
        = if i = j then 1 else 0 :=
    fun i j => (coordInvLocal (I := I) S x₀ (t : Real) x₀ hx₀ i j).1
  symm
  calc (∑ q : CoordinateIdx (𝕜 := Real) E,
        coordInv (I := I) S x₀ (t : Real) x₀ d q *
          rmComp (I := I) S x₀ (t : Real) x₀ a b c q)
      = ∑ q : CoordinateIdx (𝕜 := Real) E, ∑ p : CoordinateIdx (𝕜 := Real) E,
          DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
              (I := I) (S.family.connection (t : Real)) x₀ a b c p *
            (coordInv (I := I) S x₀ (t : Real) x₀ d q *
              metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
                (t : Real) x₀ q p) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hlow q, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ = ∑ p : CoordinateIdx (𝕜 := Real) E,
          DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
              (I := I) (S.family.connection (t : Real)) x₀ a b c p *
            (if d = p then 1 else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.mul_sum, hdelta d p]
    _ = DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
          (I := I) (S.family.connection (t : Real)) x₀ a b c d := by
        simp

/-! ### The `(0,2)` Ricci identity for `Ric` -/

/-- The canonical second covariant derivative of Ricci as a bundled field. -/
private def solNab2RicF
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    3 (S.family.connection t) (solNabRic (I := I) S t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      3 (S.family.connection t) (connSmoothInf (I := I) S t) (solNabRic (I := I) S t))

private theorem solNabRicReal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (S.family.connection t) (S.ricci t) (solNabRic (I := I) S t) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    2 (S.family.connection t) (S.ricci t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      2 (S.family.connection t) (connSmoothInf (I := I) S t) (S.ricci t))

private theorem solNab2RicReal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 (S.family.connection t) (solNabRic (I := I) S t) (solNab2RicF (I := I) S t) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    3 (S.family.connection t) (solNabRic (I := I) S t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      3 (S.family.connection t) (connSmoothInf (I := I) S t) (solNabRic (I := I) S t))

/-- **The `(0,2)` Ricci identity for the solution's Ricci tensor.**  The `s = 2` analogue
of `rm04_ricciIdentityAt`: the commutator of the canonical `∇²Ric` is the slotwise
curvature action on `Ric`, at every regular time and point. -/
theorem ricRicciIdAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) :
    DifferentialGeometry.Integral.Connection.Tensor0SRicciIdentityAt (I := I)
      (S.base.rm13 (t : Real)) (S.ricci (t : Real) x)
      (solNab2Ric (I := I) S (t : Real) x) := by
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection (t : Real)) (1 : WithTop ℕ∞) :=
    connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2)
  have htor : (S.family.connection (t : Real)).torsion x = 0 := by
    have htf :=
      DifferentialGeometry.Integral.Connection.torsionFree_of_isLeviCivita
        (I := I) (lcAt_regular (I := I) S hS t)
    simpa [DifferentialGeometry.Integral.Connection.IsTorsionFreeAt] using htf x
  have h20 :
      DifferentialGeometry.Integral.Connection.Nabla20SRealizesAt (I := I) 2
        (S.family.connection (t : Real)) (S.ricci (t : Real))
        (solNabRic (I := I) S (t : Real)) x
        (solNab2Ric (I := I) S (t : Real) x) := by
    refine ⟨?_, ?_⟩
    · intro y X slots
      exact solNabRicReal (I := I) S (t : Real) X y slots
    · intro X slots
      exact solNab2RicReal (I := I) S (t : Real) X x slots
  exact DifferentialGeometry.Integral.Connection.tensor0S_ricciIdentity_of_torsionFree
    (I := I) (S.family.connection (t : Real)) hcov (S.base.rm13 (t : Real))
    (S.ricci (t : Real)) (solNabRic (I := I) S (t : Real))
    (S.ricci (t : Real) x) (solNabRic (I := I) S (t : Real) x)
    (solNab2Ric (I := I) S (t : Real) x)
    (rm13OfSol (I := I) S (t : Real) (D.regular_subset t.2)) rfl rfl h20 htor

/-- **`RicCommAt` discharged from the solution.**  The `(0,2)` Ricci identity in
coordinate-frame components at the frame centre; the `hcomm` input of `rm04Var_eq_uhl`. -/
theorem ricCommOfSol
    [I.Boundaryless] [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) :
    RicCommAt
      (DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
        (I := I) (S.family.connection (t : Real)) x₀)
      (ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) (t : Real) x₀)
      (coordNab2Ric (I := I) S x₀ (t : Real) x₀) := by
  classical
  intro i j k l
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ := coordinateFrameAt_mem (I := I) x₀
  have hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric (t : Real)) x₀
        (hframe.toBasisAt hx₀)
        (fun p r : CoordinateIdx (𝕜 := Real) E =>
          coordInv (I := I) S x₀ (t : Real) x₀ p r) :=
    metricInverseInBasis_of_local
      (I := I) S (coordInv (I := I) S x₀)
      (coordinateFrameAt (I := I) x₀) hframe
      (coordInvLocal (I := I) S x₀) (t : Real) hx₀
  have hb : ∀ a : CoordinateIdx (𝕜 := Real) E,
      ((hframe.toBasisAt hx₀) a : TangentSpace I x₀)
        = coordinateFrameAt (I := I) x₀ a x₀ := by
    intro a
    simp [IsLocalFrameOn.toBasisAt_coe]
  have hri := ricRicciIdAt (I := I) S hS t x₀
    (coordinateFrameAt (I := I) x₀ i x₀) (coordinateFrameAt (I := I) x₀ j x₀)
    (DifferentialGeometry.Integral.Connection.vec2 (I := I)
      (coordinateFrameAt (I := I) x₀ k x₀) (coordinateFrameAt (I := I) x₀ l x₀))
  rw [DifferentialGeometry.Integral.Connection.curvatureAction0SAt_eq_rm04
      (I := I) (S.family.metric (t : Real)) (hframe.toBasisAt hx₀)
      (fun p r : CoordinateIdx (𝕜 := Real) E => coordInv (I := I) S x₀ (t : Real) x₀ p r)
      hinvAt (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) x₀)
      (solution_rm04LowersRm13At (I := I) S (t : Real) x₀)] at hri
  have hin : ∀ X Y : TangentSpace I x₀,
      DifferentialGeometry.Integral.Connection.metricTraceInput (I := I) X Y
          (DifferentialGeometry.Integral.Connection.vec2 (I := I)
            (coordinateFrameAt (I := I) x₀ k x₀) (coordinateFrameAt (I := I) x₀ l x₀))
        = DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y
            (coordinateFrameAt (I := I) x₀ k x₀) (coordinateFrameAt (I := I) x₀ l x₀) := by
    intro X Y
    funext m
    fin_cases m <;> rfl
  have hu : ∀ Z : TangentSpace I x₀,
      Function.update (DifferentialGeometry.Integral.Connection.vec2 (I := I)
            (coordinateFrameAt (I := I) x₀ k x₀)
            (coordinateFrameAt (I := I) x₀ l x₀)) 0 Z
          = DifferentialGeometry.Integral.Connection.vec2 (I := I) Z
              (coordinateFrameAt (I := I) x₀ l x₀) ∧
        Function.update (DifferentialGeometry.Integral.Connection.vec2 (I := I)
            (coordinateFrameAt (I := I) x₀ k x₀)
            (coordinateFrameAt (I := I) x₀ l x₀)) 1 Z
          = DifferentialGeometry.Integral.Connection.vec2 (I := I)
              (coordinateFrameAt (I := I) x₀ k x₀) Z := by
    intro Z
    constructor <;>
      · funext m
        fin_cases m <;> simp [DifferentialGeometry.Integral.Connection.vec2]
  have hRicC : ∀ a b : CoordinateIdx (𝕜 := Real) E,
      S.ricci (t : Real) x₀
          (DifferentialGeometry.Integral.Connection.vec2 (I := I)
            (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ b x₀))
        = ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) (t : Real) x₀ a b := by
    intro a b
    simp [ricciCompInFrame, SolutionOn.ricciAt, SolutionFamily.ricciAt]
  have hRmC : ∀ a b c d : CoordinateIdx (𝕜 := Real) E,
      S.base.rm04 (t : Real) x₀
          (DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ b x₀)
            (coordinateFrameAt (I := I) x₀ c x₀) (coordinateFrameAt (I := I) x₀ d x₀))
        = rmComp (I := I) S x₀ (t : Real) x₀ a b c d := fun _ _ _ _ => rfl
  rw [hin, hin, ← coordNab2Eq (I := I) S x₀ (t : Real) i j k l,
    ← coordNab2Eq (I := I) S x₀ (t : Real) j i k l, Fin.sum_univ_two] at hri
  simp only [(hu _).1, (hu _).2, hb, hRicC, hRmC,
    show DifferentialGeometry.Integral.Connection.vec2 (I := I)
        (coordinateFrameAt (I := I) x₀ k x₀) (coordinateFrameAt (I := I) x₀ l x₀) 0
      = coordinateFrameAt (I := I) x₀ k x₀ from rfl,
    show DifferentialGeometry.Integral.Connection.vec2 (I := I)
        (coordinateFrameAt (I := I) x₀ k x₀) (coordinateFrameAt (I := I) x₀ l x₀) 1
      = coordinateFrameAt (I := I) x₀ l x₀ from rfl] at hri
  have hterm : ∀ (c : CoordinateIdx (𝕜 := Real) E)
      (Rf : CoordinateIdx (𝕜 := Real) E → Real),
      (∑ p : CoordinateIdx (𝕜 := Real) E,
          DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
              (I := I) (S.family.connection (t : Real)) x₀ i j c p * Rf p)
        = ∑ p : CoordinateIdx (𝕜 := Real) E,
            (∑ r : CoordinateIdx (𝕜 := Real) E,
              coordInv (I := I) S x₀ (t : Real) x₀ p r * Rf r) *
              rmComp (I := I) S x₀ (t : Real) x₀ i j c p := by
    intro c Rf
    calc (∑ p : CoordinateIdx (𝕜 := Real) E,
          DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
              (I := I) (S.family.connection (t : Real)) x₀ i j c p * Rf p)
        = ∑ p : CoordinateIdx (𝕜 := Real) E,
            (∑ r : CoordinateIdx (𝕜 := Real) E,
              coordInv (I := I) S x₀ (t : Real) x₀ p r *
                rmComp (I := I) S x₀ (t : Real) x₀ i j c r) * Rf p := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [rmRaise (I := I) S hS x₀ t i j c p]
      _ = ∑ p : CoordinateIdx (𝕜 := Real) E, ∑ r : CoordinateIdx (𝕜 := Real) E,
            coordInv (I := I) S x₀ (t : Real) x₀ p r *
              (rmComp (I := I) S x₀ (t : Real) x₀ i j c r * Rf p) :=
          sumMulPair _ _ _
      _ = ∑ p : CoordinateIdx (𝕜 := Real) E, ∑ r : CoordinateIdx (𝕜 := Real) E,
            coordInv (I := I) S x₀ (t : Real) x₀ r p *
              (rmComp (I := I) S x₀ (t : Real) x₀ i j c p * Rf r) :=
          sumSwap _
      _ = ∑ p : CoordinateIdx (𝕜 := Real) E, ∑ r : CoordinateIdx (𝕜 := Real) E,
            coordInv (I := I) S x₀ (t : Real) x₀ p r *
              (Rf r * rmComp (I := I) S x₀ (t : Real) x₀ i j c p) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
          rw [coordInvSymmOn (I := I) S x₀ (t : Real) hx₀ r p]
          ring
      _ = _ := (sumMulPair _ _ _).symm
  rw [hterm k (fun p => ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
        (t : Real) x₀ p l),
    hterm l (fun p => ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
        (t : Real) x₀ k p)]
  linarith [hri]

/-- **The static Uhlenbeck reduction discharged from the solution.**  At the centre of the
coordinate frame and at a regular time, the `∇²Ric`-expanded lowered-Riemann variation
`rm04VarRHS` equals `ΔRm − 2(B − B + B − B) − drift` built entirely from the canonical
coordinate arrays.  Every input of `rm04Var_eq_uhl` is discharged from `S`/`hS`. -/
theorem rm04StaticOfSol
    [I.Boundaryless] [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    rm04VarRHS (I := I) S x₀ (coordNab2Ric (I := I) S x₀) (t : Real) m
      = rmLap (coordInv (I := I) S x₀ (t : Real) x₀)
            (nab2RmComp (I := I) S x₀ (t : Real) x₀) (m 0) (m 1) (m 2) (m 3)
        - 2 * (uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) (rmComp (I := I) S x₀)
                (t : Real) x₀ (m 0) (m 1) (m 2) (m 3)
            - uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) (rmComp (I := I) S x₀)
                (t : Real) x₀ (m 0) (m 1) (m 3) (m 2)
            + uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) (rmComp (I := I) S x₀)
                (t : Real) x₀ (m 0) (m 2) (m 1) (m 3)
            - uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) (rmComp (I := I) S x₀)
                (t : Real) x₀ (m 0) (m 3) (m 1) (m 2))
        - riemann04RicciDriftInFrame
            (ricciOneUpCompInFrame (I := I) S (coordInv (I := I) S x₀)
              (coordinateFrameAt (I := I) x₀))
            (rmComp (I := I) S x₀) (t : Real) x₀ (m 0) (m 1) (m 2) (m 3) := by
  classical
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ := coordinateFrameAt_mem (I := I) x₀
  exact rm04Var_eq_uhl (I := I) S x₀ (t : Real) (rmComp (I := I) S x₀)
    (ricciOneUpCompInFrame (I := I) S (coordInv (I := I) S x₀)
      (coordinateFrameAt (I := I) x₀))
    (coordNab2Ric (I := I) S x₀) (nab2RmComp (I := I) S x₀)
    (rm04SymmOfSol (I := I) S hS x₀ t x₀)
    (fun p q => coordInvSymmOn (I := I) S x₀ (t : Real) hx₀ p q)
    (fun p q => coordRicSymmOn (I := I) S x₀ (t : Real) hx₀ p q)
    (fun p q => (coordInvLocal (I := I) S x₀ (t : Real) x₀ hx₀ p q).2)
    (fun p q r s => rmRaise (I := I) S hS x₀ t p q r s)
    (fun p q => rfl)
    (ricCommOfSol (I := I) S hS x₀ t)
    (rm04LapInOfSol (I := I) S hS x₀ t) m

/-- **The Uhlenbeck curvature evolution at the frame centre.**  Along a Ricci-flow
solution, the canonical coordinate component of lowered Riemann satisfies

`∂ₜ Rm_{ijkl} = Δ Rm_{ijkl} − 2(B_{ijkl} − B_{ijlk} + B_{ikjl} − B_{iljk}) − drift_{ijkl}`

at the centre of the coordinate frame and at every regular time.

`gInvDt` and `hmetricReg` are the only inputs beyond `S`/`hS`: they record the
spacetime regularity of the coordinate-frame metric components together with a time
derivative for the coordinate inverse metric.  Every other input of `rm04Var_of_sol`
and of `rm04Var_eq_uhl` is discharged here. -/
theorem rm04Evol_at
    [I.Boundaryless] [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (gInvDt :
      Real → M → CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (hmetricReg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S (coordInv (I := I) S x₀) gInvDt
        (coordinateFrameAt (I := I) x₀) (coordinateFrameSet (I := I) x₀))
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real ↦ realizedRmBase (I := I) S x₀ s x₀ m)
      (rmLap (coordInv (I := I) S x₀ (t : Real) x₀)
            (nab2RmComp (I := I) S x₀ (t : Real) x₀) (m 0) (m 1) (m 2) (m 3)
        - 2 * (uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) (rmComp (I := I) S x₀)
                (t : Real) x₀ (m 0) (m 1) (m 2) (m 3)
            - uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) (rmComp (I := I) S x₀)
                (t : Real) x₀ (m 0) (m 1) (m 3) (m 2)
            + uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) (rmComp (I := I) S x₀)
                (t : Real) x₀ (m 0) (m 2) (m 1) (m 3)
            - uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) (rmComp (I := I) S x₀)
                (t : Real) x₀ (m 0) (m 3) (m 1) (m 2))
        - riemann04RicciDriftInFrame
            (ricciOneUpCompInFrame (I := I) S (coordInv (I := I) S x₀)
              (coordinateFrameAt (I := I) x₀))
            (rmComp (I := I) S x₀) (t : Real) x₀ (m 0) (m 1) (m 2) (m 3))
      D.carrier (t : Real) := by
  have hmix :=
    coordGammaMix (I := I) S hS x₀
      (coordGammaEvol (I := I) S hS x₀
        (coordMetricMix (I := I) S hS x₀ (coordMetricDeriv (I := I) S hS x₀)))
  have hbase :=
    rm04Var_of_sol (I := I) S hS x₀ gInvDt (coordNab2Ric (I := I) S x₀)
      hmetricReg (coordNab2Reg (I := I) S x₀) hmix
      (fun s hs => rm13OfSol (I := I) S s hs)
      (fun s hs => connCurvOfSol (I := I) S hS x₀ s hs) t m
  exact hbase.congr_deriv (rm04StaticOfSol (I := I) S hS x₀ t m)

/-! ## Per-point-centred global families

The centre-only limitation of the theorems above dissolves by letting every point be its
own frame centre.  These are the families the forward-uniqueness lane consumes. -/

/-- The coordinate frame at `y`, read at its own centre as a basis of `T_y M`.  This is
the `basisAt` argument of the forward-uniqueness lane. -/
def coordBasisAt (y : M) :
    Module.Basis (CoordinateIdx (𝕜 := Real) E) Real (TangentSpace I y) :=
  (coordinateFrameAt_isLocalFrame_one (I := I) y).toBasisAt
    (coordinateFrameAt_mem (I := I) y)

@[simp] theorem coordBasisAt_coe (y : M) (i : CoordinateIdx (𝕜 := Real) E) :
    (coordBasisAt (I := I) y i : TangentSpace I y) = coordinateFrameAt (I := I) y i y := by
  simp [coordBasisAt, IsLocalFrameOn.toBasisAt_coe]

/-- The per-point-centred lowered-curvature component family: at each point the coordinate
frame centred at that same point is used. -/
def rm04Fam
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    FourComp M (CoordinateIdx (𝕜 := Real) E) :=
  fun r y i j k l => rmComp (I := I) S y r y i j k l

/-- **`hreal` for the forward-uniqueness lane.**  The per-point-centred family is the
metric's own lowered curvature evaluated on the per-point coordinate basis. -/
theorem rm04Fam_real
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (r : Real) (y : M) (i j k l : CoordinateIdx (𝕜 := Real) E) :
    rm04Fam (I := I) S r y i j k l
      = metricRm04At (I := I) (S.family.metric r) y
          (DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (coordBasisAt (I := I) y i) (coordBasisAt (I := I) y j)
            (coordBasisAt (I := I) y k) (coordBasisAt (I := I) y l)) := by
  simp [rm04Fam, rmComp, SolutionFamily.rm04, SolutionOn.family]

/-- The per-point-centred rough-Laplacian component family. -/
def rm04LapFam
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    FourComp M (CoordinateIdx (𝕜 := Real) E) :=
  fun r y i j k l =>
    rmLap (coordInv (I := I) S y r y) (nab2RmComp (I := I) S y r y) i j k l

/-- The per-point-centred Uhlenbeck `B` component family. -/
def rm04BFam
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    FourComp M (CoordinateIdx (𝕜 := Real) E) :=
  fun r y i j k l =>
    uhlenbeckBTensorInFrame (coordInv (I := I) S y) (rmComp (I := I) S y) r y i j k l

/-- The per-point-centred once-raised Ricci component family. -/
def ricUpFam
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    MatrixComp M (CoordinateIdx (𝕜 := Real) E) :=
  fun r y i k =>
    ricciOneUpCompInFrame (I := I) S (coordInv (I := I) S y)
      (coordinateFrameAt (I := I) y) r y i k

/-- **`hev` for the forward-uniqueness lane.**  The per-point-centred families satisfy the
Uhlenbeck reaction–diffusion evolution with the Ricci drift, at every regular time and
every point.  The only input beyond `S`/`hS` is the per-centre coordinate-frame metric
spacetime regularity package. -/
theorem rm04EvolFam
    [I.Boundaryless] [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInvDt :
      M → Real → M → CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (hmetricReg : ∀ y : M,
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S (coordInv (I := I) S y) (gInvDt y)
        (coordinateFrameAt (I := I) y) (coordinateFrameSet (I := I) y)) :
    Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D)
      (rm04Fam (I := I) S) (rm04LapFam (I := I) S) (rm04BFam (I := I) S)
      (ricUpFam (I := I) S) := by
  intro t x i j k l
  have h := rm04Evol_at (I := I) S hS x (gInvDt x) (hmetricReg x) t
    (fun q : Fin 4 => if q = 0 then i else if q = 1 then j else if q = 2 then k else l)
  simpa only [rm04Fam, rm04LapFam, rm04BFam, ricUpFam, riemann04RicciDriftInFrame,
    rmCompBase (I := I) S x, if_pos, if_neg,
    show ((fun q : Fin 4 =>
        if q = 0 then i else if q = 1 then j else if q = 2 then k else l) 0) = i from rfl,
    show ((fun q : Fin 4 =>
        if q = 0 then i else if q = 1 then j else if q = 2 then k else l) 1) = j from rfl,
    show ((fun q : Fin 4 =>
        if q = 0 then i else if q = 1 then j else if q = 2 then k else l) 2) = k from rfl,
    show ((fun q : Fin 4 =>
        if q = 0 then i else if q = 1 then j else if q = 2 then k else l) 3) = l from rfl]
    using h

/-- **`hL` for the forward-uniqueness lane.**  The per-point-centred rough-Laplacian
component family realizes the metric rough Laplacian `Δ_g = div_g ∘ ∇^g` of the metric's
own lowered curvature field, read on the per-point coordinate basis.

The slot map is `frameVec4 (fun m z ↦ coordBasisAt z m) y i j k l` on the nose — that
definition unfolds to the `vec4` written here. -/
theorem rm04LapFam_real
    [I.Boundaryless] [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (r : Real) (y : M) (i j k l : CoordinateIdx (𝕜 := Real) E) :
    rm04LapFam (I := I) S r y i j k l
      = roughLap0SField (I := I) (S.family.metric r) (S.base.rm04 r) y
          (DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (coordBasisAt (I := I) y i) (coordBasisAt (I := I) y j)
            (coordBasisAt (I := I) y k) (coordBasisAt (I := I) y l)) := by
  classical
  have hy : y ∈ coordinateFrameSet (I := I) y := coordinateFrameAt_mem (I := I) y
  have hframe := coordinateFrameAt_isLocalFrame_one (I := I) y
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric r) y (coordBasisAt (I := I) y)
        (fun p q : CoordinateIdx (𝕜 := Real) E => coordInv (I := I) S y r y p q) :=
    metricInverseInBasis_of_local
      (I := I) S (coordInv (I := I) S y)
      (coordinateFrameAt (I := I) y) hframe (coordInvLocal (I := I) S y) r hy
  have hnab : ∀ v : Fin 6 → TangentSpace I y,
      metricNabla0S (I := I) (S.family.metric r)
          (metricNabla0S (I := I) (S.family.metric r) (S.base.rm04 r)) y v
        = nabla2Rm04Field (I := I) S r y v := fun _ => rfl
  rw [roughLap0SField, covDiv0SField,
    DifferentialGeometry.Integral.Connection.metricTraceFirstTwoField_apply,
    DifferentialGeometry.Integral.Connection.metricTraceFirstTwo0STensor_apply,
    DifferentialGeometry.Integral.Connection.metricTraceFirstTwo0SAt_eq_sum_basis
      (I := I) (S.family.metric r)
      (coordBasisAt (I := I) y)
      (fun p q : CoordinateIdx (𝕜 := Real) E => coordInv (I := I) S y r y p q) hinvAt]
  simp only [rm04LapFam, rmLap,
    DifferentialGeometry.Integral.Connection.metricTrace0S2InBasis]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  congr 1
  rw [hnab]
  unfold nab2RmComp
  simp only [coordBasisAt_coe]
  congr 1
  funext a
  fin_cases a <;> rfl

end DifferentialGeometry.PDE.RicciFlow
