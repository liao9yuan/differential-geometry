import RicciFlower.Coordinates.Christoffel
import RicciFlower.Coordinates.MetricCompatibility.Covariant
import RicciFlower.Coordinates.Tensor
import RicciFlower.LeviCivita.Torsion
import RicciFlower.Tensor.RSTensor.NablaOnTensors.ConnectionDifference
import RicciFlower.Tensor.RSTensor.TensorRSRiemannian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Christoffel Components of the Connection-Difference Tensor

This file is the coordinate projection of the invariant connection-difference
tensor.  It identifies the `(1,2)` tensor introduced in the tensor layer with
the existing local-frame Christoffel-difference components.
-/

namespace RicciFlower
namespace Coordinates

noncomputable section

open Bundle Module Tensor0SBundle
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

private theorem sub_swap_of_sub_eq_sub
    {V : Type*} [AddCommGroup V] {a b c d : V}
    (h : a - b = c - d) :
    a - c = b - d := by
  have ha : a = (c - d) + b := sub_eq_iff_eq_add.mp h
  calc
    a - c = ((c - d) + b) - c := by rw [ha]
    _ = b - d := by abel

/-- Local-frame `(1,2)` components of the invariant
`connectionDifferenceTensorAt` are the existing Christoffel-symbol difference
components. -/
theorem tensor12Comp_connectionDifferenceTensorAt
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (i j k : Idx) :
    tensor12CompInFrame (I := I)
        (fun y : M => connectionDifferenceTensorAt (I := I) cov cov' y)
        frame hframe x hx k i j =
      christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k := by
  unfold tensor12CompInFrame tensorRSComponentInFrame
    christoffelSymbolDifferenceInFrame
  change
    componentRS (I := I) (hframe.toBasisAt hx)
        (connectionDifferenceTensorAt (I := I) cov cov' x)
        (fun _ : Fin 1 => k)
        (fun q : Fin 2 => if q = 0 then i else j) =
      (hframe.coeff k x)
        (((CovariantDerivative.difference cov cov' x) (frame j x)) (frame i x))
  rw [componentRS_connectionDifferenceTensorAt]
  simp [IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe]

/-- In a local frame whose inverse-metric components are the identity, the
invariant squared norm of the connection-difference tensor is the sum of
squares of the Christoffel-symbol difference components. -/
theorem normSqRS_connectionDifferenceTensorAt_eq_christoffel_sum
    [IsManifold I ∞ M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g : SmoothMetric I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u)
    (hinv :
      MetricInverseInBasis (I := I) g x (hframe.toBasisAt hx)
        (identityInvMetric (Idx := Idx))) :
    normSqRS (I := I) (g := g) (x := x) 1 2
        (connectionDifferenceTensorAt (I := I) cov cov' x) =
      ∑ k : Idx, ∑ i : Idx, ∑ j : Idx,
        (christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k) ^ 2 := by
  rw [normSqRS_one_two_identity_eq_sum (I := I) g x
    (hframe.toBasisAt hx) hinv
    (connectionDifferenceTensorAt (I := I) cov cov' x)]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold christoffelSymbolDifferenceInFrame
  rw [componentRS_connectionDifferenceTensorAt]
  simp [IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe]

/-- Difference of two Levi-Civita connections is symmetric in its two tangent
inputs.  This is the invariant torsion-free content behind the symmetry of
`Gamma(g)-Gamma(h)`. -/
theorem lcDiffBasis_symm
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (a b : Idx) :
    ((CovariantDerivative.difference
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
        (basis b)) (basis a) =
      ((CovariantDerivative.difference
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
        (basis a)) (basis b) := by
  classical
  let covG := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis a)).choose
  let Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis b)).choose
  have hX : X x = basis a :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis a)).choose_spec
  have hY : Y x = basis b :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis b)).choose_spec
  have hXd :
      MDiffAt (T% (fun p : M => X p)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYd :
      MDiffAt (T% (fun p : M => Y p)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hdY :
      ((CovariantDerivative.difference covG covH x) (Y x)) (X x) =
        ((covG (fun p : M => Y p) x) (X x)) -
          ((covH (fun p : M => Y p) x) (X x)) := by
    have hdiff :=
      IsCovariantDerivativeOn.difference_apply
        (hcov := covG.isCovariantDerivativeOnUniv)
        (hcov' := covH.isCovariantDerivativeOnUniv)
        (σ := fun p : M => Y p) (x := x) (hx := by trivial) hYd
    exact congrArg (fun L : TangentSpace I x →L[Real] TangentSpace I x =>
      L (X x)) hdiff
  have hdX :
      ((CovariantDerivative.difference covG covH x) (X x)) (Y x) =
        ((covG (fun p : M => X p) x) (Y x)) -
          ((covH (fun p : M => X p) x) (Y x)) := by
    have hdiff :=
      IsCovariantDerivativeOn.difference_apply
        (hcov := covG.isCovariantDerivativeOnUniv)
        (hcov' := covH.isCovariantDerivativeOnUniv)
        (σ := fun p : M => X p) (x := x) (hx := by trivial) hXd
    exact congrArg (fun L : TangentSpace I x →L[Real] TangentSpace I x =>
      L (Y x)) hdiff
  have htorG :=
    LeviCivita.torsion_free_apply (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric_isTorsionFree
        (I := I) g)
      (X := fun p : M => X p) (Y := fun p : M => Y p) hXd hYd
  have htorH :=
    LeviCivita.torsion_free_apply (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric_isTorsionFree
        (I := I) h)
      (X := fun p : M => X p) (Y := fun p : M => Y p) hXd hYd
  have hsub :
      ((covG (fun p : M => Y p) x) (X x)) -
          ((covH (fun p : M => Y p) x) (X x)) =
        ((covG (fun p : M => X p) x) (Y x)) -
          ((covH (fun p : M => X p) x) (Y x)) := by
    have htor : ((covG (fun p : M => Y p) x) (X x)) -
          ((covG (fun p : M => X p) x) (Y x)) =
        ((covH (fun p : M => Y p) x) (X x)) -
          ((covH (fun p : M => X p) x) (Y x)) := by
      rw [htorG, htorH]
    exact sub_swap_of_sub_eq_sub htor
  calc
    ((CovariantDerivative.difference
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
        (basis b)) (basis a)
        = ((CovariantDerivative.difference covG covH x) (Y x)) (X x) := by
          simp [covG, covH, hX, hY]
    _ = ((covG (fun p : M => Y p) x) (X x)) -
          ((covH (fun p : M => Y p) x) (X x)) := hdY
    _ = ((covG (fun p : M => X p) x) (Y x)) -
          ((covH (fun p : M => X p) x) (Y x)) := hsub
    _ = ((CovariantDerivative.difference covG covH x) (X x)) (Y x) := hdX.symm
    _ = ((CovariantDerivative.difference
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
        (basis a)) (basis b) := by
          simp [covG, covH, hX, hY]

/-- Component form of `lcDiffBasis_symm`. -/
theorem lcDiff_symm
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (a b e : Idx) :
    componentRS (I := I) basis
        (connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
        (fun _ : Fin 1 => e)
        (fun q : Fin 2 => if q = 0 then a else b) =
      componentRS (I := I) basis
        (connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
        (fun _ : Fin 1 => e)
        (fun q : Fin 2 => if q = 0 then b else a) := by
  rw [componentRS_connectionDifferenceTensorAt]
  rw [componentRS_connectionDifferenceTensorAt]
  exact congrArg (basis.coord e)
    (lcDiffBasis_symm (I := I) g h basis a b)

/-- Local-frame components of `Gamma_g - Gamma_h`, the Levi-Civita
connection-difference tensor. -/
def lcDiffCompInFrame
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (a b e : Idx) : Real :=
  christoffelSymbolDifferenceInFrame
    (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
    (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
    frame hframe x a b e

/-- The local-frame component definition agrees with the invariant
connection-difference tensor. -/
theorem lcDiffCompInFrame_eq_component
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (a b e : Idx) :
    componentRS (I := I) (hframe.toBasisAt hx)
        (connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
        (fun _ : Fin 1 => e)
        (fun q : Fin 2 => if q = 0 then a else b) =
      lcDiffCompInFrame (I := I) g h frame hframe x a b e := by
  rw [componentRS_connectionDifferenceTensorAt]
  simp [lcDiffCompInFrame, christoffelSymbolDifferenceInFrame,
    IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe]

/-- Component form of `∇_h g` expressed by the connection difference
`D = Gamma(g) - Gamma(h)`. -/
theorem covMetric_lcDiff
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (a b c : Idx) :
    metricCovDerivForMetricCompInFrame
        (I := I) g
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x a b c =
      (∑ p : Idx,
        componentRS (I := I) (hframe.toBasisAt hx)
          (connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
          (fun _ : Fin 1 => p)
          (fun q : Fin 2 => if q = 0 then a else b) *
        metricCompForMetricInFrame (I := I) g frame x p c) +
      (∑ p : Idx,
        componentRS (I := I) (hframe.toBasisAt hx)
          (connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
          (fun _ : Fin 1 => p)
          (fun q : Fin 2 => if q = 0 then a else c) *
        metricCompForMetricInFrame (I := I) g frame x b p) := by
  classical
  let covG := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let G : Idx -> Idx -> Real := fun i j =>
    metricCompForMetricInFrame (I := I) g frame x i j
  let D : Idx -> Idx -> Idx -> Real := fun i j k =>
    componentRS (I := I) (hframe.toBasisAt hx)
      (connectionDifferenceTensorAt (I := I) covG covH x)
      (fun _ : Fin 1 => k)
      (fun q : Fin 2 => if q = 0 then i else j)
  have hframe_b : MDiffAt (T% (frame b)) x :=
    (hframe.contMDiffAt hu hx b).mdifferentiableAt one_ne_zero
  have hframe_c : MDiffAt (T% (frame c)) x :=
    (hframe.contMDiffAt hu hx c).mdifferentiableAt one_ne_zero
  have hDsub : ∀ i j k : Idx,
      D i j k =
        christoffelSymbolInFrame covG frame hframe x i j k -
          christoffelSymbolInFrame covH frame hframe x i j k := by
    intro i j k
    have hj : MDiffAt (T% (frame j)) x :=
      (hframe.contMDiffAt hu hx j).mdifferentiableAt one_ne_zero
    have hsub :=
      christoffelSymbolDifferenceInFrame_eq_sub
        covG covH frame hframe (x := x) i j k hj
    unfold D
    rw [componentRS_connectionDifferenceTensorAt]
    simpa [covG, covH, christoffelSymbolDifferenceInFrame,
      IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe] using hsub
  have hderiv :=
    metricCompForMetricInFrame_extDerivFun_eq_christoffel
      (I := I) g covG
      (LeviCivita.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
      frame hframe hu hx a b c
  unfold metricCovDerivForMetricCompInFrame
  rw [hderiv]
  change
    ((∑ p : Idx, christoffelSymbolInFrame covG frame hframe x a b p * G p c) +
        (∑ p : Idx, christoffelSymbolInFrame covG frame hframe x a c p * G b p)) -
      (∑ p : Idx, christoffelSymbolInFrame covH frame hframe x a b p * G p c) -
      (∑ p : Idx, christoffelSymbolInFrame covH frame hframe x a c p * G b p) =
    (∑ p : Idx, D a b p * G p c) + (∑ p : Idx, D a c p * G b p)
  simp only [hDsub]
  calc
    ((∑ p : Idx, christoffelSymbolInFrame covG frame hframe x a b p * G p c) +
          (∑ p : Idx, christoffelSymbolInFrame covG frame hframe x a c p * G b p)) -
        (∑ p : Idx, christoffelSymbolInFrame covH frame hframe x a b p * G p c) -
        (∑ p : Idx, christoffelSymbolInFrame covH frame hframe x a c p * G b p)
        =
      (∑ p : Idx,
        (christoffelSymbolInFrame covG frame hframe x a b p * G p c -
          christoffelSymbolInFrame covH frame hframe x a b p * G p c)) +
        (∑ p : Idx,
          (christoffelSymbolInFrame covG frame hframe x a c p * G b p -
            christoffelSymbolInFrame covH frame hframe x a c p * G b p)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
          ring
    _ =
      (∑ p : Idx,
        ((christoffelSymbolInFrame covG frame hframe x a b p -
          christoffelSymbolInFrame covH frame hframe x a b p) * G p c)) +
        (∑ p : Idx,
          ((christoffelSymbolInFrame covG frame hframe x a c p -
            christoffelSymbolInFrame covH frame hframe x a c p) * G b p)) := by
          congr 1
          · refine Finset.sum_congr rfl fun p _hp => ?_
            ring
          · refine Finset.sum_congr rfl fun p _hp => ?_
            ring

/-- Koszul-style combination of the three `∇_h g` components. -/
theorem lcDiff_combo
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (a b e : Idx) :
    metricCovDerivForMetricCompInFrame
        (I := I) g
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x a b e +
      metricCovDerivForMetricCompInFrame
        (I := I) g
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x b a e -
      metricCovDerivForMetricCompInFrame
        (I := I) g
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x e a b =
      2 * (∑ p : Idx,
        componentRS (I := I) (hframe.toBasisAt hx)
          (connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
          (fun _ : Fin 1 => p)
          (fun q : Fin 2 => if q = 0 then a else b) *
        metricCompForMetricInFrame (I := I) g frame x p e) := by
  classical
  let covG := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let basis := hframe.toBasisAt hx
  let A : Idx -> Idx -> Idx -> Real := fun i j k =>
    metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x i j k
  let D : Idx -> Idx -> Idx -> Real := fun i j k =>
    componentRS (I := I) basis
      (connectionDifferenceTensorAt (I := I) covG covH x)
      (fun _ : Fin 1 => k)
      (fun q : Fin 2 => if q = 0 then i else j)
  let G : Idx -> Idx -> Real := fun i j =>
    metricCompForMetricInFrame (I := I) g frame x i j
  have hA : ∀ i j k : Idx,
      A i j k = (∑ p : Idx, D i j p * G p k) +
        (∑ p : Idx, D i k p * G j p) := by
    intro i j k
    simpa [A, D, G, covG, covH, basis] using
      covMetric_lcDiff (I := I) g h frame hframe hu hx i j k
  have hsym : ∀ i j k : Idx, D i j k = D j i k := by
    intro i j k
    simpa [D, basis, covG, covH] using
      lcDiff_symm (I := I) g h basis i j k
  have hGsym : ∀ i j : Idx, G i j = G j i := by
    intro i j
    simpa [G, metricCompForMetricInFrame] using g.symm x (frame i x) (frame j x)
  have hcancel1 :
      (∑ p : Idx, D a e p * G b p) =
        (∑ p : Idx, D e a p * G p b) := by
    refine Finset.sum_congr rfl fun p _hp => ?_
    rw [hsym a e p, hGsym b p]
  have hcancel2 :
      (∑ p : Idx, D b e p * G a p) =
        (∑ p : Idx, D e b p * G a p) := by
    refine Finset.sum_congr rfl fun p _hp => ?_
    rw [hsym b e p]
  have hba :
      (∑ p : Idx, D b a p * G p e) =
        (∑ p : Idx, D a b p * G p e) := by
    refine Finset.sum_congr rfl fun p _hp => ?_
    rw [hsym b a p]
  change A a b e + A b a e - A e a b =
      2 * (∑ p : Idx, D a b p * G p e)
  rw [hA a b e, hA b a e, hA e a b]
  rw [hba]
  rw [hcancel1, hcancel2]
  ring

/-- DC1: local-frame Christoffel-difference equation
`Gamma_g - Gamma_h = 1/2 g^{-1} * sym(nabla_h g)`. -/
theorem lcDiffComp_eq
    [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g h : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hinv : InverseMetricComponentsForMetricInFrameOn (I := I) g gInv frame)
    (a b e : Idx) :
    2 *
        componentRS (I := I) (hframe.toBasisAt hx)
          (connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)
          (fun _ : Fin 1 => e)
          (fun q : Fin 2 => if q = 0 then a else b) =
      ∑ c : Idx,
        gInv x e c *
          (metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x a b c +
            metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x b a c -
            metricCovDerivForMetricCompInFrame
              (I := I) g
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x c a b) := by
  classical
  let covG := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let basis := hframe.toBasisAt hx
  let D : Idx -> Idx -> Idx -> Real := fun i j k =>
    componentRS (I := I) basis
      (connectionDifferenceTensorAt (I := I) covG covH x)
      (fun _ : Fin 1 => k)
      (fun q : Fin 2 => if q = 0 then i else j)
  let G : Idx -> Idx -> Real := fun i j =>
    metricCompForMetricInFrame (I := I) g frame x i j
  have hcombo : ∀ c : Idx,
      metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x a b c +
        metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x b a c -
        metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x c a b =
      2 * (∑ p : Idx, D a b p * G p c) := by
    intro c
    simpa [D, G, covG, covH, basis] using
      lcDiff_combo (I := I) g h frame hframe hu hx a b c
  have hGsym : ∀ i j : Idx, G i j = G j i := by
    intro i j
    simpa [G, metricCompForMetricInFrame] using g.symm x (frame i x) (frame j x)
  have hcollapse :
      (∑ c : Idx, gInv x e c * (∑ p : Idx, D a b p * G p c)) =
        D a b e := by
    calc
      (∑ c : Idx, gInv x e c * (∑ p : Idx, D a b p * G p c))
          = ∑ p : Idx, D a b p *
              (∑ c : Idx, gInv x e c * G c p) := by
            calc
              (∑ c : Idx, gInv x e c * (∑ p : Idx, D a b p * G p c))
                  =
                ∑ c : Idx, ∑ p : Idx, gInv x e c * (D a b p * G p c) := by
                  refine Finset.sum_congr rfl fun c _hc => ?_
                  rw [Finset.mul_sum]
              _ = ∑ p : Idx, ∑ c : Idx, gInv x e c * (D a b p * G p c) := by
                  rw [Finset.sum_comm]
              _ = ∑ p : Idx, D a b p *
                    (∑ c : Idx, gInv x e c * G c p) := by
                  refine Finset.sum_congr rfl fun p _hp => ?_
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun c _hc => ?_
                  rw [hGsym p c]
                  ring
      _ = ∑ p : Idx, D a b p * (if e = p then 1 else 0) := by
            refine Finset.sum_congr rfl fun p _hp => ?_
            rw [(hinv x e p).1]
      _ = D a b e := by
            simp
  change 2 * D a b e =
      ∑ c : Idx, gInv x e c *
        (metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x a b c +
          metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x b a c -
          metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x c a b)
  calc
    2 * D a b e =
        2 * (∑ c : Idx, gInv x e c * (∑ p : Idx, D a b p * G p c)) := by
          rw [hcollapse]
    _ = ∑ c : Idx, gInv x e c * (2 * (∑ p : Idx, D a b p * G p c)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _hc => ?_
          ring
    _ = ∑ c : Idx, gInv x e c *
        (metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x a b c +
          metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x b a c -
          metricCovDerivForMetricCompInFrame (I := I) g covH frame hframe x c a b) := by
          refine Finset.sum_congr rfl fun c _hc => ?_
          rw [hcombo c]

end

end Coordinates
end RicciFlower
