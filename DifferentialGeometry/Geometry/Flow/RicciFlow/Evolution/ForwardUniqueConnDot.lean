import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueFields
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueConnectionDiff

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option backward.isDefEq.respectTransparency false

/-!
# The invariant speed of the connection-difference carrier `A₀₃` (Route-K brick K1C)

`ForwardUniqueConnectionDiff.lean` (K1) differentiates the *frame components* of the
Christoffel difference `Γ¹ − Γ²`.  `ForwardUniqueEnergy.lean` (K3) consumes a completely
invariant fact: a `(0,3)`-tensor speed `Adot` together with

`∀ x v, HasDerivAt (fun r => connDiffLowAt (g₁ r) (g₂ r) x v) (Adot t x v) t`.

This file is the adapter between the two.  The lowering carrier `g₁(t)` is itself moving,
so the invariant speed of `A₀₃ = g₁(∇¹ − ∇², ·)` is a *sum of two* terms
(`FORWARD_UNIQUE_PRO_RULING.md` §5: "lowering with `g₁` adds only terms involving
`∂ₜg₁ = −2Ric₁`"):

`∂ₜA₀₃ = −2 Ric₁((∇¹−∇²)(Y,X), Z) + g₁((∂ₜ(∇¹−∇²))(Y,X), Z)`.

## Main definitions

* `bilin12At A` — the `(1,2)` tensor of a continuous bilinear vector-valued map, the
  `CovariantDerivative.difference`-free generalisation of `connectionDifferenceTensorAt`.
* `lowerBilin q A` — the `(0,3)` tensor `(X, Y, Z) ↦ q(A(Y, X), Z)` obtained by lowering
  the upper index of `A` against an **arbitrary** `(0,2)` fiber tensor `q` (not only a
  metric: the reaction term lowers with `Ric₁`).
* `connDiffDot g₁ g₂ Adot t x` — the invariant speed of `A₀₃`, the sum above.
* `bilinOfComp b c` — the bilinear map with prescribed basis components; this is what turns
  K1's *component* right-hand side into the invariant `Adot`.

## Main results

* `connDiffLow_hasDerivAt` — the `hA`-shaped fact K3 consumes, from the two Ricci-flow
  equations plus the invariant speed of the connection difference.
* `connDiffVec_hasDerivAt` — the frame → invariant adapter: K1's componentwise
  Christoffel-difference derivatives give the vector-valued derivative of
  `(∇¹ − ∇²)(Y, X)` at every pair of tangent vectors.
* `connDiffLow_hasDerivAt_frame` — the two composed: the `hA` producer whose hypotheses
  are exactly K1-shaped (frame components) plus the Ricci-flow equation of the *carrier*
  `g₁` alone (the second flow's PDE is not needed: only `g₁` does the lowering).
* `coeff_bilinOfComp` — the frame coefficients of `bilinOfComp` are the prescribed
  components, so `hΓ` is discharged directly from K1's componentwise derivatives.
* `christoffelInFrame_sol` — the definitional `SolutionOn` → metric-family bridge for K1's
  Christoffel symbols.

## Relocation TODO

`bilin12At`/`lowerBilin` and the two basis-expansion lemmas are generic fiber algebra with
canonical homes in `Tensor/RSTensor/NablaOnTensors/ConnectionDifference.lean` and
`Tensor/RSTensor/Components.lean`.  They live here only because the brick protocol forbids
editing existing files; move them when a second consumer appears.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Lowering

variable {x : M}

/-- The `(1,2)` tensor determined by a continuous bilinear vector-valued map `A`: its value
on a covector `α` and vectors `(X, Y)` is `α (A Y X)`.  This is
`connectionDifferenceTensorAt` with the connection difference replaced by an arbitrary
bilinear map; the two agree definitionally. -/
def bilin12At
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α => connectionDifferenceOutput (I := I) A α
      map_add' := by
        intro α β
        apply ContinuousMultilinearMap.ext
        intro v
        rw [connectionDifferenceOutput_apply]
        change (α + β) (fun _ : Fin 1 => (A (v 1)) (v 0)) =
          connectionDifferenceOutput (I := I) A α v +
            connectionDifferenceOutput (I := I) A β v
        rw [connectionDifferenceOutput_apply, connectionDifferenceOutput_apply]
        rfl
      map_smul' := by
        intro c α
        apply ContinuousMultilinearMap.ext
        intro v
        rw [connectionDifferenceOutput_apply]
        change (c • α) (fun _ : Fin 1 => (A (v 1)) (v 0)) =
          c • connectionDifferenceOutput (I := I) A α v
        rw [connectionDifferenceOutput_apply]
        rfl }

@[simp]
theorem bilin12At_apply
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (v : Fin 2 -> TangentSpace I x) :
    bilin12At (I := I) A α v = α (fun _ : Fin 1 => (A (v 1)) (v 0)) := by
  change connectionDifferenceOutput (I := I) A α v = _
  rw [connectionDifferenceOutput_apply]

/-- Auxiliary lowering with the free slot in position `0`:
`w ↦ q (w 0, A (w 2) (w 1))`. -/
private def lowerBilinOut (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  ContinuousLinearMap.uncurryLeft (𝕜 := Real) (n := 2)
    (Ei := fun _ : Fin 3 => TangentSpace I x) (G := Real)
    (LinearMap.toContinuousLinearMap
      { toFun := fun W =>
          (bilin12At (I := I) A
              (ContinuousMultilinearMap.curryLeft
                (q : ContinuousMultilinearMap Real (fun _ : Fin 2 => TangentSpace I x) Real)
                W) :
            ContinuousMultilinearMap Real (fun _ : Fin 2 => TangentSpace I x) Real)
        map_add' := by
          intro W₁ W₂
          rw [map_add]
          exact (bilin12At (I := I) A).toCLM.map_add _ _
        map_smul' := by
          intro c W
          rw [map_smul]
          exact (bilin12At (I := I) A).toCLM.map_smul c _ })

private theorem lowerBilinOut_apply
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (w : Fin 3 -> TangentSpace I x) :
    lowerBilinOut (I := I) q A w =
      q (fun a : Fin 2 => if a = 0 then w 0 else (A (w 2)) (w 1)) := by
  have h : lowerBilinOut (I := I) q A w =
      bilin12At (I := I) A
        (ContinuousMultilinearMap.curryLeft
          (q : ContinuousMultilinearMap Real (fun _ : Fin 2 => TangentSpace I x) Real) (w 0))
        (Fin.tail w) := by
    rw [lowerBilinOut, ContinuousLinearMap.uncurryLeft_apply]
    exact rfl
  rw [h, bilin12At_apply, ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  funext a
  fin_cases a <;> simp [Fin.tail]

/-- Slot permutation moving the free (lowered) slot from position `0` to position `2`. -/
private def lowerStdPerm : Equiv.Perm (Fin 3) where
  toFun i := if i = 0 then 2 else if i = 1 then 0 else 1
  invFun i := if i = 0 then 1 else if i = 1 then 2 else 0
  left_inv i := by fin_cases i <;> simp
  right_inv i := by fin_cases i <;> simp

/-- **Lowering the upper index of a bilinear vector-valued map against a `(0,2)` tensor.**
`lowerBilin q A` is the `(0,3)` fiber tensor `(X, Y, Z) ↦ q (A Y X, Z)`.  Unlike
`Integral.L2.lowerAllUpperIndices`, the lowering tensor `q` is arbitrary: the moving-carrier
reaction term of `∂ₜA₀₃` lowers with `Ric₁`, not with a metric. -/
def lowerBilin (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  ContinuousMultilinearMap.domDomCongr lowerStdPerm
    (lowerBilinOut (I := I)
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1) q) A)

theorem lowerBilin_apply
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (v : Fin 3 -> TangentSpace I x) :
    lowerBilin (I := I) q A v =
      q (fun a : Fin 2 => if a = 0 then (A (v 1)) (v 0) else v 2) := by
  have h : lowerBilin (I := I) q A v =
      lowerBilinOut (I := I)
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1) q) A
        (fun i : Fin 3 => v (lowerStdPerm i)) := rfl
  rw [h, lowerBilinOut_apply]
  change ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1) q _ = _
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext a
  fin_cases a <;> simp [lowerStdPerm]

end Lowering

section Expansion

variable {x : M}

/-- Expansion of a `(0,2)` fiber tensor in its **first** slot along a finite basis of the
tangent space. -/
theorem tensor02_expand {ι : Type*} [Fintype ι]
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (b : Module.Basis ι Real (TangentSpace I x)) (W Z : TangentSpace I x) :
    q (fun a : Fin 2 => if a = 0 then W else Z) =
      ∑ k, b.repr W k * q (fun a : Fin 2 => if a = 0 then b k else Z) := by
  classical
  set m : Fin 2 -> TangentSpace I x := fun a => if a = 0 then W else Z with hm
  have hupd : ∀ W' : TangentSpace I x,
      Function.update m 0 W' = (fun a : Fin 2 => if a = 0 then W' else Z) := by
    intro W'
    funext a
    fin_cases a <;> simp [hm]
  have hW : (∑ k, b.repr W k • b k) = W := b.sum_repr W
  calc q (fun a : Fin 2 => if a = 0 then W else Z)
      = q (Function.update m 0 (∑ k, b.repr W k • b k)) := by rw [hupd, hW]
    _ = ∑ k, q (Function.update m 0 (b.repr W k • b k)) :=
        q.toMultilinearMap.map_update_sum Finset.univ 0 (fun k => b.repr W k • b k) m
    _ = ∑ k, b.repr W k * q (fun a : Fin 2 => if a = 0 then b k else Z) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [q.map_update_smul, hupd, smul_eq_mul]

/-- Expansion of a continuous bilinear vector-valued map along a finite basis. -/
theorem bilin_expand {ι : Type*} [Fintype ι]
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (b : Module.Basis ι Real (TangentSpace I x)) (X Y : TangentSpace I x) :
    (A Y) X = ∑ j, ∑ i, (b.repr Y j * b.repr X i) • (A (b j)) (b i) := by
  classical
  have hY : (∑ j, b.repr Y j • b j) = Y := b.sum_repr Y
  have hX : (∑ i, b.repr X i • b i) = X := b.sum_repr X
  have step1 : (A Y) X = ∑ j, b.repr Y j • ((A (b j)) X) := by
    conv_lhs => rw [← hY]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply]
  have step2 : ∀ j : ι, (A (b j)) X = ∑ i, b.repr X i • (A (b j)) (b i) := by
    intro j
    conv_lhs => rw [← hX]
    simp only [map_sum, map_smul]
  rw [step1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [step2 j, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]

end Expansion

section Speed

/-- **The invariant speed of the connection-difference carrier `A₀₃`.**

`connDiffDot g₁ g₂ Adot t x` is the `(0,3)` fiber tensor

`(X, Y, Z) ↦ −2 Ric₁((∇¹−∇²)(Y, X), Z) + g₁(t)(Adot x Y X, Z)`,

where `Adot x` is the invariant speed of the `(1,2)` connection-difference tensor
`∇¹ − ∇²` at `x` (produced from K1's frame components by `connDiffVec_hasDerivAt`).
The first summand is the moving-carrier reaction created by `∂ₜg₁ = −2Ric₁`. -/
def connDiffDot (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : (x : M) →
      TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (t : Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  (-2 : Real) •
      lowerBilin (I := I) (metricRicciAt (I := I) (g₁ t) x)
        (CovariantDerivative.difference (metricCov (I := I) (g₁ t))
          (metricCov (I := I) (g₂ t)) x) +
    lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x) (Adot x)

theorem connDiffDot_apply (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : (x : M) →
      TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (t : Real) (x : M) (v : Fin 3 -> TangentSpace I x) :
    connDiffDot (I := I) g₁ g₂ Adot t x v =
      (-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then
            CovariantDerivative.difference (metricCov (I := I) (g₁ t))
              (metricCov (I := I) (g₂ t)) x (v 1) (v 0) else v 2) +
        (g₁ t).inner x ((Adot x (v 1)) (v 0)) (v 2) := by
  have hadd :
      connDiffDot (I := I) g₁ g₂ Adot t x v =
        ((-2 : Real) •
            lowerBilin (I := I) (metricRicciAt (I := I) (g₁ t) x)
              (CovariantDerivative.difference (metricCov (I := I) (g₁ t))
                (metricCov (I := I) (g₂ t)) x)) v +
          lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x) (Adot x) v :=
    Tensor0SSpace.add_apply (I := I) 3 x _ _ v
  have hsmul :
      ((-2 : Real) •
          lowerBilin (I := I) (metricRicciAt (I := I) (g₁ t) x)
            (CovariantDerivative.difference (metricCov (I := I) (g₁ t))
              (metricCov (I := I) (g₂ t)) x)) v =
        (-2 : Real) •
          lowerBilin (I := I) (metricRicciAt (I := I) (g₁ t) x)
            (CovariantDerivative.difference (metricCov (I := I) (g₁ t))
              (metricCov (I := I) (g₂ t)) x) v :=
    Tensor0SSpace.smul_apply (I := I) 3 x (-2 : Real) _ v
  rw [hadd, hsmul, lowerBilin_apply, lowerBilin_apply, smul_eq_mul,
    metricTensorField_apply]
  simp

end Speed

section Adapter

variable {x : M}

/-- **K1C-a, invariant core.**  If the carrier `g₁` solves the Ricci-flow equation at `x`
and the `(1,2)` connection difference `∇¹ − ∇²` has invariant time derivative `Adot x`,
then the lowered carrier `A₀₃` has time derivative `connDiffDot`.  This is exactly the
`hA` hypothesis of `forwardUniqueEnergy_hasDerivAt`. -/
theorem connDiffLow_hasDerivAt
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : (x : M) →
      TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    {t : Real}
    (hPDE₁ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hA : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real =>
          CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x Y X)
        ((Adot x Y) X) t)
    (v : Fin 3 -> TangentSpace I x) :
    HasDerivAt (fun r : Real => connDiffLowAt (I := I) (g₁ r) (g₂ r) x v)
      (connDiffDot (I := I) g₁ g₂ Adot t x v) t := by
  classical
  set b : Module.Basis
      (Fin (Module.finrank Real (TangentSpace I x))) Real (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x) with hb
  set F : Real → TangentSpace I x := fun r =>
    CovariantDerivative.difference (metricCov (I := I) (g₁ r))
      (metricCov (I := I) (g₂ r)) x (v 1) (v 0) with hF
  set Fdot : TangentSpace I x := (Adot x (v 1)) (v 0) with hFdot
  have hFderiv : HasDerivAt F Fdot t := hA (v 0) (v 1)
  -- componentwise derivative of the moving vector
  have hcomp : ∀ k, HasDerivAt (fun r : Real => b.repr (F r) k) (b.repr Fdot k) t := by
    intro k
    have hL : HasDerivAt (fun r : Real =>
        (LinearMap.toContinuousLinearMap (b.coord k)) (F r))
        ((LinearMap.toContinuousLinearMap (b.coord k)) Fdot) t :=
      (LinearMap.toContinuousLinearMap (b.coord k)).hasFDerivAt.comp_hasDerivAt t hFderiv
    simpa using hL
  -- derivative of the moving metric components
  have hmet : ∀ k, HasDerivAt
      (fun r : Real => (g₁ r).inner x (b k) (v 2))
      ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
        (fun a : Fin 2 => if a = 0 then b k else v 2)) t := fun k => hPDE₁ (b k) (v 2)
  -- the integrand as a finite sum of products
  have hsum : ∀ r : Real,
      connDiffLowAt (I := I) (g₁ r) (g₂ r) x v =
        ∑ k, b.repr (F r) k * (g₁ r).inner x (b k) (v 2) := by
    intro r
    rw [connDiffLowAt_apply]
    have h1 : (g₁ r).inner x (F r) (v 2) =
        metricTensorField (I := I) (g₁ r) x
          (fun a : Fin 2 => if a = 0 then F r else v 2) := by
      rw [metricTensorField_apply]; simp
    have h2 : ∀ k : Fin (Module.finrank Real (TangentSpace I x)),
        metricTensorField (I := I) (g₁ r) x
            (fun a : Fin 2 => if a = 0 then b k else v 2) =
          (g₁ r).inner x (b k) (v 2) := by
      intro k; rw [metricTensorField_apply]; simp
    rw [show
        (g₁ r).inner x
            (CovariantDerivative.difference (metricCov (I := I) (g₁ r))
              (metricCov (I := I) (g₂ r)) x (v 1) (v 0)) (v 2) =
          (g₁ r).inner x (F r) (v 2) from rfl,
      h1, tensor02_expand (I := I) (metricTensorField (I := I) (g₁ r) x) b (F r) (v 2)]
    exact Finset.sum_congr rfl fun k _ => by rw [h2 k]
  have hderiv : HasDerivAt (fun r : Real => ∑ k, b.repr (F r) k * (g₁ r).inner x (b k) (v 2))
      (∑ k, (b.repr Fdot k * (g₁ t).inner x (b k) (v 2) +
        b.repr (F t) k * ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then b k else v 2)))) t :=
    HasDerivAt.fun_sum fun k _ => (hcomp k).mul (hmet k)
  have hval :
      (∑ k, (b.repr Fdot k * (g₁ t).inner x (b k) (v 2) +
        b.repr (F t) k * ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then b k else v 2)))) =
        connDiffDot (I := I) g₁ g₂ Adot t x v := by
    rw [Finset.sum_add_distrib, connDiffDot_apply]
    have hg : (∑ k, b.repr Fdot k * (g₁ t).inner x (b k) (v 2)) =
        (g₁ t).inner x Fdot (v 2) := by
      have h1 : ∀ k : Fin (Module.finrank Real (TangentSpace I x)),
          (g₁ t).inner x (b k) (v 2) =
            metricTensorField (I := I) (g₁ t) x
              (fun a : Fin 2 => if a = 0 then b k else v 2) := by
        intro k; rw [metricTensorField_apply]; simp
      have h2 : (g₁ t).inner x Fdot (v 2) =
          metricTensorField (I := I) (g₁ t) x
            (fun a : Fin 2 => if a = 0 then Fdot else v 2) := by
        rw [metricTensorField_apply]; simp
      rw [h2, tensor02_expand (I := I) (metricTensorField (I := I) (g₁ t) x) b Fdot (v 2)]
      exact Finset.sum_congr rfl fun k _ => by rw [h1 k]
    have hr : (∑ k, b.repr (F t) k * ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then b k else v 2))) =
        (-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then F t else v 2) := by
      rw [tensor02_expand (I := I) (metricRicciAt (I := I) (g₁ t) x) b (F t) (v 2),
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hg, hr]
    ring
  have := hderiv.congr_deriv hval
  simpa only [hsum] using this

end Adapter

section Frame

variable {Idx : Type*} [Fintype Idx] {u : Set M} {x : M}

/-- **K1C-a, frame producer.**  K1 differentiates the frame components of `Γ¹ − Γ²`; this
turns those scalar facts into the invariant, vector-valued time derivative of the `(1,2)`
connection difference at *every* pair of tangent vectors.  The hypothesis says exactly that
the frame components of the supplied bilinear speed `Adot x` are the K1 derivatives. -/
theorem connDiffVec_hasDerivAt
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u) (hx : x ∈ u) {t : Real}
    (Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    (hΓ : ∀ i j k : Idx,
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k)
        (hframe.coeff k x ((Adot x (frame j x)) (frame i x))) t)
    (X Y : TangentSpace I x) :
    HasDerivAt
      (fun r : Real =>
        CovariantDerivative.difference (metricCov (I := I) (g₁ r))
          (metricCov (I := I) (g₂ r)) x Y X)
      ((Adot x Y) X) t := by
  classical
  set b : Module.Basis Idx Real (TangentSpace I x) := hframe.toBasisAt hx with hbdef
  have hbcoe : ∀ i : Idx, b i = frame i x := fun i =>
    IsLocalFrameOn.toBasisAt_coe hframe hx i
  have hcoeff : ∀ (k : Idx) (w : TangentSpace I x),
      hframe.coeff k x w = b.repr w k := by
    intro k w
    simp [IsLocalFrameOn.coeff, hx, hbdef, Module.Basis.coord_apply]
  have hfr : ∀ j : Idx, MDifferentiableAt I I.tangent (T% (frame j)) x := fun j =>
    (hframe.contMDiffAt hu hx j).mdifferentiableAt (by simp)
  -- the componentwise K1 fact, read in the frame basis
  have hbasis : ∀ i j k : Idx,
      HasDerivAt
        (fun r : Real =>
          b.repr (CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x (b j) (b i)) k)
        (b.repr ((Adot x (b j)) (b i)) k) t := by
    intro i j k
    have hdiff : ∀ r : Real,
        CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x (b j) (b i) =
          (metricCov (I := I) (g₁ r) (frame j) x) (frame i x) -
            (metricCov (I := I) (g₂ r) (frame j) x) (frame i x) := by
      intro r
      have h := IsCovariantDerivativeOn.difference_apply
        (metricCov (I := I) (g₁ r)).isCovariantDerivativeOnUniv
        (metricCov (I := I) (g₂ r)).isCovariantDerivativeOnUniv
        (x := x) (Set.mem_univ x) (σ := fun y => frame j y) (hfr j)
      have h' : CovariantDerivative.difference (metricCov (I := I) (g₁ r))
          (metricCov (I := I) (g₂ r)) x (frame j x) =
            metricCov (I := I) (g₁ r) (frame j) x -
              metricCov (I := I) (g₂ r) (frame j) x := by
        simpa [CovariantDerivative.difference] using h
      rw [hbcoe j, hbcoe i, h']
      rfl
    have hfun : (fun r : Real =>
        b.repr (CovariantDerivative.difference (metricCov (I := I) (g₁ r))
          (metricCov (I := I) (g₂ r)) x (b j) (b i)) k) =
        fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k := by
      funext r
      rw [hdiff r, ← hcoeff k]
      simp only [DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame_eval]
      exact map_sub (hframe.coeff k x) _ _
    have hval : b.repr ((Adot x (b j)) (b i)) k =
        hframe.coeff k x ((Adot x (frame j x)) (frame i x)) := by
      rw [hcoeff k, hbcoe i, hbcoe j]
    rw [hfun, hval]
    exact hΓ i j k
  -- vector-valued derivative at basis vectors
  have hvec : ∀ i j : Idx,
      HasDerivAt
        (fun r : Real =>
          CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x (b j) (b i))
        ((Adot x (b j)) (b i)) t := by
    intro i j
    have hsum : ∀ r : Real,
        CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x (b j) (b i) =
          ∑ k, b.repr (CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x (b j) (b i)) k • b k := fun r =>
      (b.sum_repr _).symm
    have htgt : ((Adot x (b j)) (b i)) =
        ∑ k, b.repr ((Adot x (b j)) (b i)) k • b k := (b.sum_repr _).symm
    rw [htgt]
    have := HasDerivAt.fun_sum (u := (Finset.univ : Finset Idx))
      (fun k (_ : k ∈ (Finset.univ : Finset Idx)) => (hbasis i j k).smul_const (b k))
    simpa only [← hsum] using this
  -- bilinear expansion to arbitrary vectors
  have hexp : ∀ r : Real,
      CovariantDerivative.difference (metricCov (I := I) (g₁ r))
          (metricCov (I := I) (g₂ r)) x Y X =
        ∑ j, ∑ i, (b.repr Y j * b.repr X i) •
          (CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x (b j)) (b i) := fun r =>
    bilin_expand (I := I) _ b X Y
  have htgt : ((Adot x Y) X) =
      ∑ j, ∑ i, (b.repr Y j * b.repr X i) • (Adot x (b j)) (b i) :=
    bilin_expand (I := I) (Adot x) b X Y
  rw [htgt]
  have hstep : HasDerivAt
      (fun r : Real =>
        ∑ j, ∑ i, (b.repr Y j * b.repr X i) •
          (CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x (b j)) (b i))
      (∑ j, ∑ i, (b.repr Y j * b.repr X i) • (Adot x (b j)) (b i)) t :=
    HasDerivAt.fun_sum fun j _ =>
      HasDerivAt.fun_sum fun i _ => (hvec i j).const_smul _
  simpa only [← hexp] using hstep

/-- **K1C-a.**  The `hA` hypothesis of `forwardUniqueEnergy_hasDerivAt`, produced from
K1-shaped inputs: the frame-component derivatives of the Christoffel difference (the
conclusion of `christoffelEvolutionDiffInFrameOn`, realised by the invariant bilinear speed
`Adot`) together with the Ricci-flow equation for the carrier `g₁`. -/
theorem connDiffLow_hasDerivAt_frame
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u) (hx : x ∈ u) {t : Real}
    (Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    (hPDE₁ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hΓ : ∀ i j k : Idx,
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k)
        (hframe.coeff k x ((Adot x (frame j x)) (frame i x))) t)
    (v : Fin 3 -> TangentSpace I x) :
    HasDerivAt (fun r : Real => connDiffLowAt (I := I) (g₁ r) (g₂ r) x v)
      (connDiffDot (I := I) g₁ g₂ Adot t x v) t :=
  connDiffLow_hasDerivAt (I := I) g₁ g₂ Adot hPDE₁
    (fun X Y => connDiffVec_hasDerivAt (I := I) g₁ g₂ frame hframe hu hx Adot hΓ X Y) v

/-- The continuous bilinear vector-valued map with prescribed components in a basis:
`bilinOfComp b c (b j) (b i) = ∑ k, c i j k • b k`.  This is what turns K1's *component*
right-hand side `christoffelEvolutionRHSInFrame gInv₁ nablaRic₁ − christoffelEvolutionRHSInFrame
gInv₂ nablaRic₂` into the invariant speed `Adot` that `connDiffDot` consumes. -/
def bilinOfComp (b : Module.Basis Idx Real (TangentSpace I x))
    (c : Idx -> Idx -> Idx -> Real) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    (b.constr Real fun j =>
      LinearMap.toContinuousLinearMap (b.constr Real fun i => ∑ k, c i j k • b k))

@[simp]
theorem bilinOfComp_basis (b : Module.Basis Idx Real (TangentSpace I x))
    (c : Idx -> Idx -> Idx -> Real) (i j : Idx) :
    (bilinOfComp (I := I) b c (b j)) (b i) = ∑ k, c i j k • b k := by
  have h : bilinOfComp (I := I) b c (b j) =
      LinearMap.toContinuousLinearMap (b.constr Real fun i => ∑ k, c i j k • b k) := by
    change (b.constr Real fun j' =>
      LinearMap.toContinuousLinearMap (b.constr Real fun i => ∑ k, c i j' k • b k)) (b j) = _
    rw [Module.Basis.constr_basis]
  rw [h]
  change (b.constr Real fun i' => ∑ k, c i' j k • b k) (b i) = _
  rw [Module.Basis.constr_basis]

/-- The frame coefficients of `bilinOfComp` are the prescribed components: this discharges
the `hΓ` hypothesis of `connDiffVec_hasDerivAt`/`connDiffLow_hasDerivAt_frame` directly from
K1's componentwise derivative facts. -/
theorem coeff_bilinOfComp (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u) (hx : x ∈ u)
    (c : Idx -> Idx -> Idx -> Real) (i j k : Idx) :
    hframe.coeff k x
        ((bilinOfComp (I := I) (hframe.toBasisAt hx) c (frame j x)) (frame i x)) =
      c i j k := by
  classical
  set b : Module.Basis Idx Real (TangentSpace I x) := hframe.toBasisAt hx with hbdef
  have hbcoe : ∀ l : Idx, b l = frame l x := fun l =>
    IsLocalFrameOn.toBasisAt_coe hframe hx l
  have hcoeff : ∀ (l : Idx) (w : TangentSpace I x),
      hframe.coeff l x w = b.repr w l := by
    intro l w
    simp [IsLocalFrameOn.coeff, hx, hbdef, Module.Basis.coord_apply]
  rw [← hbcoe i, ← hbcoe j, hcoeff k, bilinOfComp_basis]
  simp [Finsupp.single_apply]

end Frame

section SolutionBridge

variable {Idx : Type*} {u : Set M}

/-- K1 is stated for `SolutionOn` pairs, this file for metric families.  The bridge is
definitional: a `SolutionFamily`'s connection at time `s` *is* the Levi-Civita connection
`metricCov` of its time-`s` metric. -/
theorem christoffelInFrame_sol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (s : Real) (x : M) (i j k : Idx) :
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S.family.connection s) frame hframe x i j k =
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (metricCov (I := I) (S.base.metric s)) frame hframe x i j k := rfl

end SolutionBridge

end DifferentialGeometry.PDE.RicciFlow

end
