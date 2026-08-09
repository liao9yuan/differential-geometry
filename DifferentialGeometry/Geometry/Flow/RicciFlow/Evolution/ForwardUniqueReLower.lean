import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRmBridge
import DifferentialGeometry.Tensor.RSTensor.NablaDomDomCongr
import DifferentialGeometry.Tensor.RSTensor.ContractionLeibniz

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option backward.isDefEq.respectTransparency false

/-!
# The re-lowering operator and its covariant Leibniz defect (Route-K brick K2.6c)

`Evolution/ForwardUniqueRmBridge.lean` identified the R4 carrier mismatch as a concrete
operator (`mixLow_eq_rm04`): the `g₁`-lowered Riemann tensor of `g₂` is the own-lowered
`Rm04₂` with its **last slot precomposed by** `Φ = g₂♯ ∘ g₁♭` (`sharpFlat`).  This file
builds that re-lowering as a field operator and computes its first-order covariant
Leibniz defect.

## The representation

The `(0,s)` stack carries no covariant derivative of a mixed `(1,1)` field, so `Φ` cannot
be differentiated directly.  Instead the last-slot precomposition is realized as a
`g₂`-trace of a tensor product,

```
reLower g₁ g₂ T = tr_{g₂} ((T ⊗ g₁) · reLowerPerm),
```

where `reLowerPerm` moves `T`'s last slot and `g₁`'s first slot to the front (the two slots
`metricTraceFirstTwoField` contracts) and keeps `T₀ … T_{s-1}, (g₁)₁` in order.  This is a
smooth field by construction, and `reLower_apply` checks it against the intended semantics
(`Function.update`-form last-slot precomposition by `sharpFlat`), with `reLower_rm04`
the `mixLow_eq_rm04` instance.

## The defect

Differentiating the three layers — `nabla_metricTraceFirstTwo0S` through the trace,
`totalNabla0SFun_domDomCongr` through the reindexing, `nabla0SFun_product_eval` through the
product — gives

```
∇²(reLower T) − reLower(∇²T) = reLowerPair g₂ T (∇²g₁),
```

with `reLowerPair` the same trace-of-product construction with `g₁` replaced by an arbitrary
`(0,3)` field.  By `nabla2_metric1` (`∇²g₁ = −lapDiffFlux g₁ g₂ g₁`) the right-hand side is
**algebraic** in the connection-difference flux and `T`: no derivative of `T` beyond the one
displayed and no derivative of the difference carrier appears.

## The payoff

Instantiating `lapComm_eq_div_flux` with `L = reLowerOp` turns the abstract defect carriers
of the R4 organization into explicit ones:

```
Δ₂(reLower T) − reLower(Δ₂ T) = div₂(reLowerPair g₂ T (∇²g₁)) + tr_{g₂}(reLowerPair g₂ (∇²T) (∇²g₁)).
```

Both carriers are algebraic in `(A₀₃-flux, T, ∇²T)`.  Norm bounds are out of scope here;
the `lapDiffFlux_eval`/`fluxNormSq_le` pattern of `ForwardUniqueRmBounds.lean` covers them.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-! ## The re-lowering slot permutation -/

section Perm

/-- **Slot permutation for the re-lowering operator.**  On `Fin (s+3)` it sends
`k ↦ k+2` for `k < s`, `s ↦ 0`, `s+1 ↦ 1` and fixes `s+2`: it moves the last slot of `T`
and the first slot of `g₁` in `T ⊗ g₁` to the two leading positions contracted by
`metricTraceFirstTwoField`, leaving `T₀ … T_{s-1}, (g₁)₁` in order. -/
def reLowerPerm (s : ℕ) : Equiv.Perm (Fin (s + 1 + 2)) :=
  Equiv.ofLeftInverseOfCardLE (le_refl _)
    (fun k : Fin (s + 1 + 2) =>
      if h : (k : ℕ) < s then ⟨(k : ℕ) + 2, by omega⟩
      else if (k : ℕ) = s then ⟨0, by omega⟩
      else if (k : ℕ) = s + 1 then ⟨1, by omega⟩
      else k)
    (fun l : Fin (s + 1 + 2) =>
      if (l : ℕ) = 0 then ⟨s, by omega⟩
      else if (l : ℕ) = 1 then ⟨s + 1, by omega⟩
      else if h : (l : ℕ) < s + 2 then ⟨(l : ℕ) - 2, by omega⟩
      else l)
    (by
      intro k
      have hk : (k : ℕ) < s + 1 + 2 := k.isLt
      refine Fin.ext ?_
      dsimp only
      split_ifs <;> simp_all <;> omega)

theorem reLowerPerm_val (s : ℕ) (k : Fin (s + 1 + 2)) :
    ((reLowerPerm s k : Fin (s + 1 + 2)) : ℕ) =
      if (k : ℕ) < s then (k : ℕ) + 2
      else if (k : ℕ) = s then 0 else if (k : ℕ) = s + 1 then 1 else (k : ℕ) := by
  change ((if h : (k : ℕ) < s then (⟨(k : ℕ) + 2, by omega⟩ : Fin (s + 1 + 2))
      else if (k : ℕ) = s then ⟨0, by omega⟩
      else if (k : ℕ) = s + 1 then ⟨1, by omega⟩ else k : Fin (s + 1 + 2)) : ℕ) = _
  split_ifs <;> rfl

/-- The first `s+1` slots of the permuted product tuple: the tail with its **last** entry
replaced by the first trace vector. -/
theorem reLowerPerm_first {s : ℕ} {x : M} (a b : TangentSpace I x)
    (tail : Fin (s + 1) -> TangentSpace I x) (k : Fin (s + 1)) :
    metricTraceInput (I := I) a b tail (reLowerPerm s (Fin.castAdd 2 k)) =
      Function.update tail (Fin.last s) a k := by
  classical
  have hk : (k : ℕ) < s + 1 := k.isLt
  have hcast : ((Fin.castAdd 2 k : Fin (s + 1 + 2)) : ℕ) = (k : ℕ) := rfl
  rw [metricTraceInput_apply]
  by_cases h1 : (k : ℕ) < s
  · have hv : ((reLowerPerm s (Fin.castAdd 2 k) : Fin (s + 1 + 2)) : ℕ) = (k : ℕ) + 2 := by
      rw [reLowerPerm_val, hcast, if_pos h1]
    have hne : k ≠ Fin.last s := by
      intro hcon
      rw [hcon] at h1
      simp at h1
    simp only [hv, Function.update_of_ne hne]
    rw [dif_neg (by omega : ¬((k : ℕ) + 2 = 0)), dif_neg (by omega : ¬((k : ℕ) + 2 = 1))]
    exact congrArg tail (Fin.ext (by simp))
  · have hks : (k : ℕ) = s := by omega
    have hv : ((reLowerPerm s (Fin.castAdd 2 k) : Fin (s + 1 + 2)) : ℕ) = 0 := by
      rw [reLowerPerm_val, hcast, if_neg h1, if_pos hks]
    have hlast : k = Fin.last s := Fin.ext (by simp [hks])
    simp only [hv]
    rw [dif_pos (trivial : True), hlast, Function.update_self]

/-- Slot `s+1` of the permuted product tuple (the first slot of the second factor) is the
**second** trace vector. -/
theorem reLowerPerm_snd0 {s : ℕ} {x : M} (a b : TangentSpace I x)
    (tail : Fin (s + 1) -> TangentSpace I x) :
    metricTraceInput (I := I) a b tail (reLowerPerm s (Fin.natAdd (s + 1) (0 : Fin 2))) = b := by
  have hcast : ((Fin.natAdd (s + 1) (0 : Fin 2) : Fin (s + 1 + 2)) : ℕ) = s + 1 := by
    simp [Fin.natAdd]
  have hv : ((reLowerPerm s (Fin.natAdd (s + 1) (0 : Fin 2)) : Fin (s + 1 + 2)) : ℕ) = 1 := by
    rw [reLowerPerm_val, hcast, if_neg (by omega), if_neg (by omega), if_pos rfl]
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬((1 : ℕ) = 0)), dif_pos (trivial : True)]

/-- Slot `s+2` of the permuted product tuple (the second slot of the second factor) is the
**last** entry of the tail. -/
theorem reLowerPerm_snd1 {s : ℕ} {x : M} (a b : TangentSpace I x)
    (tail : Fin (s + 1) -> TangentSpace I x) :
    metricTraceInput (I := I) a b tail (reLowerPerm s (Fin.natAdd (s + 1) (1 : Fin 2))) =
      tail (Fin.last s) := by
  have hcast : ((Fin.natAdd (s + 1) (1 : Fin 2) : Fin (s + 1 + 2)) : ℕ) = s + 2 := by
    simp [Fin.natAdd]
  have hv : ((reLowerPerm s (Fin.natAdd (s + 1) (1 : Fin 2)) : Fin (s + 1 + 2)) : ℕ) = s + 2 := by
    rw [reLowerPerm_val, hcast, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬(s + 2 = 0)), dif_neg (by omega : ¬(s + 2 = 1))]
  exact congrArg tail (Fin.ext (by simp))

end Perm

/-! ## The re-lowering operator -/

section ReLower

/-- **General-basis evaluation of the first-two metric trace.**  Basis-free companion of
`metricTraceFirstTwoField_eq_sum`, which is tied to the centred coordinate frame. -/
theorem traceField_eq_sum {s : ℕ} (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x)) (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwoField (I := I) (M := M) g A x tail =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * A x (metricTraceInput (I := I) (basis i) (basis j) tail) := by
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv (A x) tail]
  rfl

/-- Exchange of two nested pairs of finite sums. -/
private theorem sum_comm4 {Idx : Type*} [Fintype Idx] (F : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, F a b i j) =
      ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx, F a b i j := by
  classical
  calc (∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, F a b i j)
      = ∑ a : Idx, ∑ i : Idx, ∑ b : Idx, ∑ j : Idx, F a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i : Idx, ∑ a : Idx, ∑ b : Idx, ∑ j : Idx, F a b i j := Finset.sum_comm
    _ = ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ b : Idx, F a b i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx, F a b i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- Expansion of one slot of a covariant tensor along a finite basis. -/
private theorem slot_expand {s : ℕ} {Idx : Type*} [Fintype Idx] {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (m : Fin s -> TangentSpace I x) (i : Fin s) (c : Idx -> Real)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    A (Function.update m i (∑ p : Idx, c p • basis p)) =
      ∑ p : Idx, c p * A (Function.update m i (basis p)) := by
  classical
  calc A (Function.update m i (∑ p : Idx, c p • basis p))
      = ∑ p : Idx, A (Function.update m i (c p • basis p)) :=
        A.toMultilinearMap.map_update_sum Finset.univ i (fun p => c p • basis p) m
    _ = ∑ p : Idx, c p * A (Function.update m i (basis p)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Tensor0SSpace.map_update_smul, smul_eq_mul]

/-- **The re-lowering operator on `(0,s+1)` fields.**  `reLower g₁ g₂ T` precomposes the
**last** slot of `T` with the endomorphism `Φ = g₂♯ ∘ g₁♭` of `sharpFlat`.  It is realized
as the `g₂`-trace of the permuted product `T ⊗ g₁` (see `reLowerPerm`), which makes it a
smooth field with no mixed-variance object anywhere in the construction. -/
def reLower (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  metricTraceFirstTwoField (I := I) (M := M) (s := s + 1) g₂
    (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (∞ : WithTop ℕ∞) (reLowerPerm s)
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 2)
        T (metricTensorField (I := I) g₁)))

/-- **Basis evaluation of the re-lowering.**  The trace-of-product representation, read off
in an arbitrary basis: the first trace index feeds `T`'s last slot, the second is paired by
`g₁` against the last input vector. -/
theorem reLower_eval (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x)) (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g₂ x basis gInv)
    (tail : Fin (s + 1) -> TangentSpace I x) :
    reLower (I := I) g₁ g₂ T x tail =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * (T x (Function.update tail (Fin.last s) (basis i)) *
          g₁.inner x (basis j) (tail (Fin.last s))) := by
  classical
  rw [reLower, traceField_eq_sum (I := I) g₂ _ basis gInv hinv tail]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  change (ContinuousMultilinearMap.domDomCongr (reLowerPerm s)
      ((MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 2)
        T (metricTensorField (I := I) g₁)) x)) _ = _
  rw [Tensor0SSpace.domDomCongr_apply]
  change (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 2)
      T (metricTensorField (I := I) g₁)) x
      (fun p => metricTraceInput (I := I) (basis i) (basis j) tail (reLowerPerm s p)) = _
  rw [tensor0SField_product_apply, metricTensorField_apply]
  congr 1
  · exact congrArg (T x) (funext fun k => reLowerPerm_first (I := I) (basis i) (basis j) tail k)
  · change g₁.inner x
        (metricTraceInput (I := I) (basis i) (basis j) tail
          (reLowerPerm s (Fin.natAdd (s + 1) (0 : Fin 2))))
        (metricTraceInput (I := I) (basis i) (basis j) tail
          (reLowerPerm s (Fin.natAdd (s + 1) (1 : Fin 2)))) = _
    rw [reLowerPerm_snd0 (I := I) (basis i) (basis j) tail,
      reLowerPerm_snd1 (I := I) (basis i) (basis j) tail]

/-- `sharpFlat` written through the `raiseAt` basis formula of `ForwardUniqueRmBridge`. -/
theorem sharpFlat_eq_raise (g₁ g₂ : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x)) (V : TangentSpace I x) :
    sharpFlat (I := I) g₁ g₂ x V =
      raiseAt (I := I) g₂ x basis (fun l : Idx => g₁.inner x V (basis l)) := by
  have hflat : ∀ l : Idx,
      g₂.inner x (sharpFlat (I := I) g₁ g₂ x V) (basis l) = g₁.inner x V (basis l) := by
    intro l
    have h2 : tangentFlatEquiv_gen (I := I) g₂ x (sharpFlat (I := I) g₁ g₂ x V) =
        tangentFlatEquiv_gen (I := I) g₁ x V := by
      change tangentFlatEquiv_gen (I := I) g₂ x
        ((tangentFlatEquiv_gen (I := I) g₂ x).symm
          ((tangentFlatEquiv_gen (I := I) g₁ x) V)) = _
      exact (tangentFlatEquiv_gen (I := I) g₂ x).apply_symm_apply _
    rw [← tangentFlatEquiv_apply_gen (I := I) g₂ x, h2,
      tangentFlatEquiv_apply_gen (I := I) g₁ x]
  rw [show (fun l : Idx => g₁.inner x V (basis l)) =
      fun l : Idx => g₂.inner x (sharpFlat (I := I) g₁ g₂ x V) (basis l) from
    (funext fun l => (hflat l).symm)]
  exact (raiseAt_lower (I := I) g₂ x basis (sharpFlat (I := I) g₁ g₂ x V)).symm

/-- **The semantic pin (deliverable 1).**  The trace-of-product construction *is* the
last-slot precomposition by `Φ = g₂♯ ∘ g₁♭`. -/
theorem reLower_apply (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (x : M) (tail : Fin (s + 1) -> TangentSpace I x) :
    reLower (I := I) g₁ g₂ T x tail =
      T x (Function.update tail (Fin.last s)
        (sharpFlat (I := I) g₁ g₂ x (tail (Fin.last s)))) := by
  classical
  set basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x) with hbasis
  set gInv := basisInvMetric (I := I) g₂ x basis with hgInv
  have hinv : MetricInverseInBasis_gen (I := I) (M := M) g₂ x basis gInv :=
    basisInvMetric_real (I := I) g₂ x basis
  rw [reLower_eval (I := I) g₁ g₂ T basis gInv hinv tail,
    sharpFlat_eq_raise (I := I) g₁ g₂ basis (tail (Fin.last s)), raiseAt_eq,
    slot_expand (I := I) (T x) tail (Fin.last s)
      (fun p => ∑ l, gInv p l * g₁.inner x (tail (Fin.last s)) (basis l)) basis]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [g₁.symm x (basis l) (tail (Fin.last s))]
  ring

/-- **The `mixLow_eq_rm04` instance (deliverable 1, checked against the pinned semantics).**
Re-lowering the own-`g₂`-lowered curvature gives the `g₁`-lowered Riemann tensor of `g₂` —
exactly the carrier of the R4 mismatch. -/
theorem reLower_rm04 (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) (hRm : Rm2 x = metricRm04At (I := I) g₂ x)
    (X Y Z W : TangentSpace I x) :
    reLower (I := I) g₁ g₂ Rm2 x (vec4 (I := I) X Y Z W) =
      g₁.inner x (riemannOp (metricCov (I := I) g₂) x X Y Z) W := by
  classical
  have hlast : (vec4 (I := I) X Y Z W) (Fin.last 3) = W := by
    simp [vec4]
  have hupd : Function.update (vec4 (I := I) X Y Z W) (Fin.last 3)
      (sharpFlat (I := I) g₁ g₂ x W) =
      vec4 (I := I) X Y Z (sharpFlat (I := I) g₁ g₂ x W) := by
    funext i
    fin_cases i <;> simp [vec4, Function.update]
  rw [reLower_apply (I := I) g₁ g₂ Rm2 x, hlast, hupd, hRm]
  exact mixLow_eq_rm04 (I := I) g₁ g₂ x X Y Z W

end ReLower

/-! ## The defect carrier -/

section Pair

/-- **Slot permutation for the re-lowering defect carrier.**  On `Fin (s+4)` it sends
`k ↦ k+3` for `k < s`, `s ↦ 0`, `s+1 ↦ 2`, `s+2 ↦ 1` and fixes `s+3`: in `T ⊗ K` (with `K`
a `(0,3)` field whose slot `0` is a derivative slot) it moves `T`'s last slot and `K`'s
middle slot to the two leading positions contracted by `metricTraceFirstTwoField`. -/
def reLowerPerm2 (s : ℕ) : Equiv.Perm (Fin (s + 1 + 3)) :=
  Equiv.ofLeftInverseOfCardLE (le_refl _)
    (fun k : Fin (s + 1 + 3) =>
      if h : (k : ℕ) < s then ⟨(k : ℕ) + 3, by omega⟩
      else if (k : ℕ) = s then ⟨0, by omega⟩
      else if (k : ℕ) = s + 1 then ⟨2, by omega⟩
      else if (k : ℕ) = s + 2 then ⟨1, by omega⟩
      else k)
    (fun l : Fin (s + 1 + 3) =>
      if (l : ℕ) = 0 then ⟨s, by omega⟩
      else if (l : ℕ) = 1 then ⟨s + 2, by omega⟩
      else if (l : ℕ) = 2 then ⟨s + 1, by omega⟩
      else if h : (l : ℕ) < s + 3 then ⟨(l : ℕ) - 3, by omega⟩
      else l)
    (by
      intro k
      have hk : (k : ℕ) < s + 1 + 3 := k.isLt
      refine Fin.ext ?_
      dsimp only
      split_ifs <;> simp_all <;> omega)

theorem reLowerPerm2_val (s : ℕ) (k : Fin (s + 1 + 3)) :
    ((reLowerPerm2 s k : Fin (s + 1 + 3)) : ℕ) =
      if (k : ℕ) < s then (k : ℕ) + 3
      else if (k : ℕ) = s then 0
      else if (k : ℕ) = s + 1 then 2
      else if (k : ℕ) = s + 2 then 1 else (k : ℕ) := by
  change ((if h : (k : ℕ) < s then (⟨(k : ℕ) + 3, by omega⟩ : Fin (s + 1 + 3))
      else if (k : ℕ) = s then ⟨0, by omega⟩
      else if (k : ℕ) = s + 1 then ⟨2, by omega⟩
      else if (k : ℕ) = s + 2 then ⟨1, by omega⟩ else k : Fin (s + 1 + 3)) : ℕ) = _
  split_ifs <;> rfl

/-- The first `s+1` slots of the permuted `T ⊗ K` tuple. -/
theorem reLowerPerm2_first {s : ℕ} {x : M} (a b : TangentSpace I x)
    (u : Fin (s + 2) -> TangentSpace I x) (k : Fin (s + 1)) :
    metricTraceInput (I := I) a b u (reLowerPerm2 s (Fin.castAdd 3 k)) =
      Function.update (Fin.tail u) (Fin.last s) a k := by
  classical
  have hk : (k : ℕ) < s + 1 := k.isLt
  have hcast : ((Fin.castAdd 3 k : Fin (s + 1 + 3)) : ℕ) = (k : ℕ) := rfl
  rw [metricTraceInput_apply]
  by_cases h1 : (k : ℕ) < s
  · have hv : ((reLowerPerm2 s (Fin.castAdd 3 k) : Fin (s + 1 + 3)) : ℕ) = (k : ℕ) + 3 := by
      rw [reLowerPerm2_val, hcast, if_pos h1]
    have hne : k ≠ Fin.last s := by
      intro hcon
      rw [hcon] at h1
      simp at h1
    simp only [hv, Function.update_of_ne hne]
    rw [dif_neg (by omega : ¬((k : ℕ) + 3 = 0)), dif_neg (by omega : ¬((k : ℕ) + 3 = 1))]
    exact congrArg u (Fin.ext (by simp))
  · have hks : (k : ℕ) = s := by omega
    have hv : ((reLowerPerm2 s (Fin.castAdd 3 k) : Fin (s + 1 + 3)) : ℕ) = 0 := by
      rw [reLowerPerm2_val, hcast, if_neg h1, if_pos hks]
    have hlast : k = Fin.last s := Fin.ext (by simp [hks])
    simp only [hv]
    rw [dif_pos (trivial : True), hlast, Function.update_self]

/-- Slot `s+1` of the permuted `T ⊗ K` tuple is `K`'s derivative slot input. -/
theorem reLowerPerm2_snd0 {s : ℕ} {x : M} (a b : TangentSpace I x)
    (u : Fin (s + 2) -> TangentSpace I x) :
    metricTraceInput (I := I) a b u (reLowerPerm2 s (Fin.natAdd (s + 1) (0 : Fin 3))) = u 0 := by
  have hcast : ((Fin.natAdd (s + 1) (0 : Fin 3) : Fin (s + 1 + 3)) : ℕ) = s + 1 := by
    simp [Fin.natAdd]
  have hv : ((reLowerPerm2 s (Fin.natAdd (s + 1) (0 : Fin 3)) : Fin (s + 1 + 3)) : ℕ) = 2 := by
    rw [reLowerPerm2_val, hcast, if_neg (by omega), if_neg (by omega), if_pos rfl]
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬((2 : ℕ) = 0)), dif_neg (by omega : ¬((2 : ℕ) = 1))]
  exact congrArg u (Fin.ext (by simp))

/-- Slot `s+2` of the permuted `T ⊗ K` tuple is the **second** trace vector. -/
theorem reLowerPerm2_snd1 {s : ℕ} {x : M} (a b : TangentSpace I x)
    (u : Fin (s + 2) -> TangentSpace I x) :
    metricTraceInput (I := I) a b u (reLowerPerm2 s (Fin.natAdd (s + 1) (1 : Fin 3))) = b := by
  have hcast : ((Fin.natAdd (s + 1) (1 : Fin 3) : Fin (s + 1 + 3)) : ℕ) = s + 2 := by
    simp [Fin.natAdd]
  have hv : ((reLowerPerm2 s (Fin.natAdd (s + 1) (1 : Fin 3)) : Fin (s + 1 + 3)) : ℕ) = 1 := by
    rw [reLowerPerm2_val, hcast, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos rfl]
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬((1 : ℕ) = 0)), dif_pos (trivial : True)]

/-- Slot `s+3` of the permuted `T ⊗ K` tuple is the **last** input vector. -/
theorem reLowerPerm2_snd2 {s : ℕ} {x : M} (a b : TangentSpace I x)
    (u : Fin (s + 2) -> TangentSpace I x) :
    metricTraceInput (I := I) a b u (reLowerPerm2 s (Fin.natAdd (s + 1) (2 : Fin 3))) =
      u (Fin.last (s + 1)) := by
  have hcast : ((Fin.natAdd (s + 1) (2 : Fin 3) : Fin (s + 1 + 3)) : ℕ) = s + 3 := by
    simp [Fin.natAdd]
  have hv : ((reLowerPerm2 s (Fin.natAdd (s + 1) (2 : Fin 3)) : Fin (s + 1 + 3)) : ℕ) = s + 3 := by
    rw [reLowerPerm2_val, hcast, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬(s + 3 = 0)), dif_neg (by omega : ¬(s + 3 = 1))]
  exact congrArg u (Fin.ext (by simp))

/-- **The defect carrier.**  `reLowerPair g₂ T K` is the bilinear `g₂`-contraction of a
`(0,s+1)` field `T` with a `(0,3)` field `K`, pairing `T`'s last slot against `K`'s middle
slot; `K`'s first slot becomes the leading (derivative) slot of the result and `K`'s last
slot becomes its trailing slot.  With `K = ∇²g₁` this is exactly the Leibniz defect of
`reLower` (`nabla_reLower`). -/
def reLowerPair (g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (K : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2) :=
  metricTraceFirstTwoField (I := I) (M := M) (s := s + 2) g₂
    (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (∞ : WithTop ℕ∞) (reLowerPerm2 s)
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K))

/-- Basis evaluation of the defect carrier. -/
theorem reLowerPair_eval (g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (K : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x)) (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g₂ x basis gInv)
    (u : Fin (s + 2) -> TangentSpace I x) :
    reLowerPair (I := I) g₂ T K x u =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * (T x (Function.update (Fin.tail u) (Fin.last s) (basis i)) *
          K x (vec3 (I := I) (u 0) (basis j) (u (Fin.last (s + 1))))) := by
  classical
  rw [reLowerPair, traceField_eq_sum (I := I) g₂ _ basis gInv hinv u]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  change (ContinuousMultilinearMap.domDomCongr (reLowerPerm2 s)
      ((MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K) x)) _ = _
  rw [Tensor0SSpace.domDomCongr_apply]
  change (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K) x
      (fun p => metricTraceInput (I := I) (basis i) (basis j) u (reLowerPerm2 s p)) = _
  rw [tensor0SField_product_apply]
  congr 1
  · exact congrArg (T x) (funext fun k => reLowerPerm2_first (I := I) (basis i) (basis j) u k)
  · refine congrArg (K x) (funext fun p => ?_)
    change metricTraceInput (I := I) (basis i) (basis j) u
        (reLowerPerm2 s (Fin.natAdd (s + 1) p)) = _
    fin_cases p
    · change metricTraceInput (I := I) (basis i) (basis j) u
          (reLowerPerm2 s (Fin.natAdd (s + 1) (0 : Fin 3))) =
        vec3 (I := I) (u 0) (basis j) (u (Fin.last (s + 1))) (0 : Fin 3)
      rw [reLowerPerm2_snd0 (I := I) (basis i) (basis j) u]
      simp [vec3]
    · change metricTraceInput (I := I) (basis i) (basis j) u
          (reLowerPerm2 s (Fin.natAdd (s + 1) (1 : Fin 3))) =
        vec3 (I := I) (u 0) (basis j) (u (Fin.last (s + 1))) (1 : Fin 3)
      rw [reLowerPerm2_snd1 (I := I) (basis i) (basis j) u]
      simp [vec3]
    · change metricTraceInput (I := I) (basis i) (basis j) u
          (reLowerPerm2 s (Fin.natAdd (s + 1) (2 : Fin 3))) =
        vec3 (I := I) (u 0) (basis j) (u (Fin.last (s + 1))) (2 : Fin 3)
      rw [reLowerPerm2_snd2 (I := I) (basis i) (basis j) u]
      simp [vec3]

end Pair

/-! ## The covariant Leibniz defect -/

section Defect

/-- Unfolding lemma for `reLower` (the trace-of-product representation). -/
theorem reLower_eq_trace (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    reLower (I := I) g₁ g₂ T =
      metricTraceFirstTwoField (I := I) (M := M) (s := s + 1) g₂
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) (reLowerPerm s)
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 2)
            T (metricTensorField (I := I) g₁))) := rfl

/-- The Levi-Civita connection of a smooth metric is `C¹`-locally smooth (the hypothesis
shape `nabla_metricTraceFirstTwo0S` consumes). -/
private theorem metricCov_one (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (metricCov (I := I) g) (1 : WithTop ℕ∞) := by
  simpa [metricCov] using
    (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) g)

/-- **Evaluated tensor-product Leibniz rule for the canonical total covariant derivative.**
Arbitrary-slot form of `nabla0SFun_product_eval`, obtained by realizing the direction and
the slots as values of smooth sections. -/
theorem nablaProd_eval {s q : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1))
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov A nablaA)
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) q cov B nablaB)
    {x : M} (X : TangentSpace I x) (w : Fin (s + q) -> TangentSpace I x) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + q) cov
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B) x
        (Fin.cons X w) =
      nablaA x (Fin.cons X (fun a : Fin s => w (Fin.castAdd q a))) *
          B x (fun a : Fin q => w (Fin.natAdd s a)) +
        A x (fun a : Fin s => w (Fin.castAdd q a)) *
          nablaB x (Fin.cons X (fun a : Fin q => w (Fin.natAdd s a))) := by
  classical
  let Xsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x X).choose
  have hXsec : Xsec x = X :=
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x X).choose_spec
  let V : Fin (s + q) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a => (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (w a)).choose
  have hV : ∀ a : Fin (s + q), V a x = w a := fun a =>
    (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (w a)).choose_spec
  have h1 := totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (s + q) cov Xsec
    (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B) x
    (fun a : Fin (s + q) => V a x)
  have h2 := nabla0SFun_product_eval (I := I) cov A B nablaA nablaB hA hB Xsec V x
  simp only [hV, hXsec] at h1 h2
  rw [h1, h2]

/-- Replacing the last slot of a `Fin.cons` tuple. -/
private theorem update_cons_last {s : ℕ} {x : M} (X : TangentSpace I x)
    (tail : Fin (s + 1) -> TangentSpace I x) (v : TangentSpace I x) :
    Function.update (Fin.cons X tail : Fin (s + 1 + 1) -> TangentSpace I x)
        (Fin.last (s + 1)) v =
      Fin.cons X (Function.update tail (Fin.last s) v) := by
  classical
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · have h0 : (0 : Fin (s + 1 + 1)) ≠ Fin.last (s + 1) := by
      rw [Ne, Fin.ext_iff]
      simp
    rw [Function.update_of_ne h0, Fin.cons_zero, Fin.cons_zero]
  · rw [Fin.cons_succ]
    by_cases hj : j = Fin.last s
    · subst hj
      rw [Fin.succ_last, Function.update_self, Function.update_self]
    · have hne : j.succ ≠ Fin.last (s + 1) := by
        rw [← Fin.succ_last]
        exact fun hc => hj (Fin.succ_injective _ hc)
      rw [Function.update_of_ne hne, Function.update_of_ne hj, Fin.cons_succ]

/-- The last entry of a `Fin.cons` tuple. -/
private theorem cons_last {s : ℕ} {x : M} (X : TangentSpace I x)
    (tail : Fin (s + 1) -> TangentSpace I x) :
    (Fin.cons X tail : Fin (s + 1 + 1) -> TangentSpace I x) (Fin.last (s + 1)) =
      tail (Fin.last s) := by
  rw [← Fin.succ_last, Fin.cons_succ]

/-- Recognizing a `Fin.cons` of a `Fin 2` tuple as a `vec3`. -/
private theorem cons2_vec3 {x : M} (X Y Z : TangentSpace I x)
    (v : Fin 2 -> TangentSpace I x) (h0 : v 0 = Y) (h1 : v 1 = Z) :
    (Fin.cons X v : Fin 3 -> TangentSpace I x) = vec3 (I := I) X Y Z := by
  funext p
  fin_cases p
  · change (Fin.cons X v : Fin 3 -> TangentSpace I x) (0 : Fin 3) = vec3 (I := I) X Y Z (0 : Fin 3)
    rw [Fin.cons_zero]
    simp [vec3]
  · change (Fin.cons X v : Fin 3 -> TangentSpace I x) (1 : Fin 3) = vec3 (I := I) X Y Z (1 : Fin 3)
    rw [show (1 : Fin 3) = (0 : Fin 2).succ from rfl, Fin.cons_succ, h0]
    simp [vec3]
  · change (Fin.cons X v : Fin 3 -> TangentSpace I x) (2 : Fin 3) = vec3 (I := I) X Y Z (2 : Fin 3)
    rw [show (2 : Fin 3) = (1 : Fin 2).succ from rfl, Fin.cons_succ, h1]
    simp [vec3]

/-- **The first-order covariant Leibniz defect of the re-lowering, pointwise.** -/
theorem nabla_reLower_eval (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    {x : M} (X : TangentSpace I x) (tail : Fin (s + 1) -> TangentSpace I x) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1)
        (metricCov (I := I) g₂) (reLower (I := I) g₁ g₂ T) x (Fin.cons X tail) =
      reLower (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) x (Fin.cons X tail) +
        reLowerPair (I := I) g₂ T
          (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) x (Fin.cons X tail) := by
  classical
  set basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x) with hbasis
  set gInv := basisInvMetric (I := I) g₂ x basis with hgInv
  have hinv : MetricInverseInBasis_gen (I := I) (M := M) g₂ x basis gInv :=
    basisInvMetric_real (I := I) g₂ x basis
  have hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen
      (I := I) (metricCov (I := I) g₂) g₂ :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) g₂
  have hrT : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (metricCov (I := I) g₂) T (metricNabla0S (I := I) g₂ T) :=
    totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (metricCov (I := I) g₂) T _
  have hrG : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (metricCov (I := I) g₂) (metricTensorField (I := I) g₁)
      (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) :=
    totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (metricCov (I := I) g₂) (metricTensorField (I := I) g₁) _
  rw [reLower_eq_trace,
    nabla_metricTraceFirstTwo0S (I := I) (M := M) (metricCov (I := I) g₂)
      (metricCov_one (I := I) g₂) g₂ hmc
      (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞) (reLowerPerm s)
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 2)
          T (metricTensorField (I := I) g₁)))
      basis gInv hinv X tail,
    reLower_eval (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) basis gInv hinv (Fin.cons X tail),
    reLowerPair_eval (I := I) g₂ T
      (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) basis gInv hinv
      (Fin.cons X tail),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_add]
  congr 1
  -- the per-index Leibniz identity
  rw [totalNabla0SFun_domDomCongr (I := I) (metricCov (I := I) g₂) (reLowerPerm s)
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 2)
        T (metricTensorField (I := I) g₁)) x,
    Tensor0SSpace.domDomCongr_apply]
  have harg : (fun p : Fin (s + 1 + 2 + 1) =>
        (Fin.cons X (metricTraceInput (I := I) (basis i) (basis j) tail) :
          Fin (s + 1 + 2 + 1) -> TangentSpace I x)
          (frontExtendEquiv (reLowerPerm s) p)) =
      (Fin.cons X (fun p : Fin (s + 1 + 2) =>
        metricTraceInput (I := I) (basis i) (basis j) tail (reLowerPerm s p)) :
          Fin (s + 1 + 2 + 1) -> TangentSpace I x) := by
    funext p
    rw [cons_apply_frontExtendEquiv]
    rfl
  rw [harg, nablaProd_eval (I := I) (metricCov (I := I) g₂) T (metricTensorField (I := I) g₁)
    (metricNabla0S (I := I) g₂ T)
    (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) hrT hrG X
    (fun p : Fin (s + 1 + 2) =>
      metricTraceInput (I := I) (basis i) (basis j) tail (reLowerPerm s p))]
  have hfirst : (fun a : Fin (s + 1) =>
        metricTraceInput (I := I) (basis i) (basis j) tail
          (reLowerPerm s (Fin.castAdd 2 a))) =
      Function.update tail (Fin.last s) (basis i) :=
    funext fun a => reLowerPerm_first (I := I) (basis i) (basis j) tail a
  have hg0 : metricTraceInput (I := I) (basis i) (basis j) tail
      (reLowerPerm s (Fin.natAdd (s + 1) (0 : Fin 2))) = basis j :=
    reLowerPerm_snd0 (I := I) (basis i) (basis j) tail
  have hg1 : metricTraceInput (I := I) (basis i) (basis j) tail
      (reLowerPerm s (Fin.natAdd (s + 1) (1 : Fin 2))) = tail (Fin.last s) :=
    reLowerPerm_snd1 (I := I) (basis i) (basis j) tail
  rw [hfirst, metricTensorField_apply, hg0, hg1,
    cons2_vec3 (I := I) X (basis j) (tail (Fin.last s))
      (fun a : Fin 2 => metricTraceInput (I := I) (basis i) (basis j) tail
        (reLowerPerm s (Fin.natAdd (s + 1) a))) hg0 hg1,
    update_cons_last (I := I) X tail (basis i), cons_last (I := I) X tail,
    Fin.tail_cons, Fin.cons_zero]

/-- **Deliverable 2: the covariant Leibniz defect of the re-lowering.**

`∇²` passes through `reLower` up to the algebraic pairing of `T` with `∇²g₁`:

```
∇²(reLower T) = reLower(∇²T) + reLowerPair g₂ T (∇²g₁).
```

The defect carries **no** derivative of `T` beyond the one already displayed and no
derivative of the re-lowering endomorphism: it is bilinear in `T` and `∇²g₁`. -/
theorem nabla_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    metricNabla0S (I := I) g₂ (reLower (I := I) g₁ g₂ T) =
      reLower (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) +
        reLowerPair (I := I) g₂ T
          (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) := by
  classical
  have h1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (metricCov (I := I) g₂) (reLower (I := I) g₁ g₂ T)
      (metricNabla0S (I := I) g₂ (reLower (I := I) g₁ g₂ T)) :=
    totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (metricCov (I := I) g₂) (reLower (I := I) g₁ g₂ T) _
  have h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (metricCov (I := I) g₂) (reLower (I := I) g₁ g₂ T)
      (reLower (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) +
        reLowerPair (I := I) g₂ T
          (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) := by
    intro Y x slots
    have hsplit :
        (reLower (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) +
            reLowerPair (I := I) g₂ T
              (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) x
            (Fin.cons (Y x) slots) =
          reLower (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) x (Fin.cons (Y x) slots) +
            reLowerPair (I := I) g₂ T
              (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) x
              (Fin.cons (Y x) slots) := rfl
    rw [hsplit, ← nabla_reLower_eval (I := I) g₁ g₂ T (Y x) slots]
    exact totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (metricCov (I := I) g₂) Y (reLower (I := I) g₁ g₂ T) x slots
  exact totalNabla0SRealizes_unique h1 h2

/-- **The defect is `A₀₃`-algebraic.**  Rewriting `∇²g₁` through `nabla2_metric1`
(`∇²g₁ = −lapDiffFlux g₁ g₂ g₁`) exhibits the Leibniz defect as an algebraic expression in
the connection-difference flux and `T`. -/
theorem nabla_reLower_flux (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    metricNabla0S (I := I) g₂ (reLower (I := I) g₁ g₂ T) =
      reLower (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) +
        reLowerPair (I := I) g₂ T
          (-lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁)) := by
  rw [nabla_reLower (I := I) g₁ g₂ T, nabla2_metric1 (I := I) g₁ g₂]

/-- Equal metrics: the re-lowering is the identity, so its Leibniz defect vanishes. -/
theorem reLowerPair_self (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    reLowerPair (I := I) g T
        (metricNabla0S (I := I) g (metricTensorField (I := I) g)) = 0 := by
  classical
  refine DFunLike.ext _ _ fun x => ?_
  refine ContinuousMultilinearMap.ext fun u => ?_
  set basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x) with hbasis
  rw [reLowerPair_eval (I := I) g T _ basis (basisInvMetric (I := I) g x basis)
    (basisInvMetric_real (I := I) g x basis) u]
  have hz : metricNabla0S (I := I) g (metricTensorField (I := I) g) x = 0 := by
    rw [metricNabla0S_self (I := I) g]
    rfl
  simp [hz]

end Defect

/-! ## The `[reLower, Δ₂]` commutator in divergence form -/

section Payoff

/-- **The rank-indexed re-lowering operator**, the shape `lapCommFlux` / `lapCommRem` /
`lapComm_eq_div_flux` consume.  A scalar has no slot to re-lower, so the operator is the
identity in rank `0`. -/
def reLowerOp (g₁ g₂ : SmoothRiemannianMetric I M) :
    ∀ k : ℕ, Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k
  | 0 => id
  | (_ + 1) => fun T => reLower (I := I) g₁ g₂ T

@[simp] theorem reLowerOp_succ (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    reLowerOp (I := I) g₁ g₂ (k + 1) T = reLower (I := I) g₁ g₂ T := rfl

/-- **The commutator flux is the algebraic defect carrier.**  The abstract
`lapCommFlux` of `ForwardUniqueRmBridge.lean`, instantiated at `L = reLowerOp`, is exactly
`reLowerPair g₂ T (∇²g₁)` — bilinear in `T` and `∇²g₁`, hence `A₀₃`-algebraic by
`nabla2_metric1`. -/
theorem lapCommFlux_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    lapCommFlux (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T =
      reLowerPair (I := I) g₂ T
        (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) := by
  rw [lapCommFlux, reLowerOp_succ, reLowerOp_succ, nabla_reLower]
  abel

/-- **The `[reLower, Δ₂]` commutator in divergence form** (first half of deliverable 3).
The flux carrier is explicit and algebraic; the remainder is identified in
`lapCommRem_reLower`. -/
theorem lapComm_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    roughLap0SField (I := I) g₂ (reLower (I := I) g₁ g₂ T) -
        reLower (I := I) g₁ g₂ (roughLap0SField (I := I) g₂ T) =
      covDiv0SField (I := I) g₂
          (reLowerPair (I := I) g₂ T
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) +
        lapCommRem (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T := by
  have h := lapComm_eq_div_flux (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T
  rw [lapCommFlux_reLower (I := I) g₁ g₂ T] at h
  simpa using h

/-- The last entry of a trace-input tuple. -/
private theorem traceInput_last {k : ℕ} {x : M} (a b : TangentSpace I x)
    (tail : Fin (k + 1) -> TangentSpace I x) :
    metricTraceInput (I := I) a b tail (Fin.last (k + 2)) = tail (Fin.last k) := by
  have hv : ((Fin.last (k + 2) : Fin (k + 1 + 2)) : ℕ) = k + 2 := rfl
  rw [metricTraceInput_apply]
  simp only [hv]
  rw [dif_neg (by omega : ¬(k + 2 = 0)), dif_neg (by omega : ¬(k + 2 = 1))]
  exact congrArg tail (Fin.ext (by simp))

/-- Replacing the last entry of a trace-input tuple is replacing the last entry of its
tail: the trace pair and the re-lowered slot never interfere. -/
private theorem traceInput_update_last {k : ℕ} {x : M} (a b : TangentSpace I x)
    (tail : Fin (k + 1) -> TangentSpace I x) (v : TangentSpace I x) :
    Function.update (metricTraceInput (I := I) a b tail) (Fin.last (k + 2)) v =
      metricTraceInput (I := I) a b (Function.update tail (Fin.last k) v) := by
  classical
  funext p
  have hp : (p : ℕ) < k + 1 + 2 := p.isLt
  by_cases hlast : p = Fin.last (k + 2)
  · subst hlast
    rw [Function.update_self, traceInput_last, Function.update_self]
  · have hpv : (p : ℕ) ≠ k + 2 := fun hc => hlast (Fin.ext (by rw [hc]; rfl))
    rw [Function.update_of_ne hlast, metricTraceInput_apply, metricTraceInput_apply]
    split_ifs with h0 h1
    · rfl
    · rfl
    · have hne : (⟨(p : ℕ) - 2, by omega⟩ : Fin (k + 1)) ≠ Fin.last k := by
        intro hc
        have hval : (p : ℕ) - 2 = k := congrArg Fin.val hc
        omega
      exact (Function.update_of_ne hne v tail).symm

/-- **The re-lowering commutes with the first-two metric trace.**  `reLower` acts on the
*last* slot and the trace contracts the *first two*, so the two operations are independent;
the proof is the exchange of the two basis double sums. -/
theorem trace_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 2 + 1)) :
    metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂ (reLower (I := I) g₁ g₂ A) =
      reLower (I := I) g₁ g₂
        (metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂ A) := by
  classical
  refine DFunLike.ext _ _ fun x => ?_
  refine ContinuousMultilinearMap.ext fun tail => ?_
  set basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x) with hbasis
  set gInv := basisInvMetric (I := I) g₂ x basis with hgInv
  have hinv : MetricInverseInBasis_gen (I := I) (M := M) g₂ x basis gInv :=
    basisInvMetric_real (I := I) g₂ x basis
  rw [traceField_eq_sum (I := I) g₂ (reLower (I := I) g₁ g₂ A) basis gInv hinv tail,
    reLower_eval (I := I) g₁ g₂
      (metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂ A) basis gInv hinv tail]
  have hL : ∀ a b : Fin (Module.finrank Real (TangentSpace I x)),
      gInv a b * (reLower (I := I) g₁ g₂ A) x
          (metricTraceInput (I := I) (basis a) (basis b) tail) =
        ∑ i, ∑ j, gInv a b * gInv i j *
          (A x (metricTraceInput (I := I) (basis a) (basis b)
              (Function.update tail (Fin.last k) (basis i))) *
            g₁.inner x (basis j) (tail (Fin.last k))) := by
    intro a b
    rw [reLower_eval (I := I) g₁ g₂ A basis gInv hinv
      (metricTraceInput (I := I) (basis a) (basis b) tail), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [traceInput_update_last, traceInput_last]
    ring
  have hR : ∀ i j : Fin (Module.finrank Real (TangentSpace I x)),
      gInv i j * ((metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂ A) x
            (Function.update tail (Fin.last k) (basis i)) *
          g₁.inner x (basis j) (tail (Fin.last k))) =
        ∑ a, ∑ b, gInv a b * gInv i j *
          (A x (metricTraceInput (I := I) (basis a) (basis b)
              (Function.update tail (Fin.last k) (basis i))) *
            g₁.inner x (basis j) (tail (Fin.last k))) := by
    intro i j
    rw [traceField_eq_sum (I := I) g₂ A basis gInv hinv
      (Function.update tail (Fin.last k) (basis i)), Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp only [hL, hR]
  exact sum_comm4 _

/-- **The commutator remainder is the traced algebraic defect carrier.**  The abstract
`lapCommRem` of `ForwardUniqueRmBridge.lean`, instantiated at `L = reLowerOp`, is the
`g₂`-trace of `reLowerPair g₂ (∇²T) (∇²g₁)`: algebraic in `∇²T` and `∇²g₁`. -/
theorem lapCommRem_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    lapCommRem (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T =
      metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
        (reLowerPair (I := I) g₂ (metricNabla0S (I := I) g₂ T)
          (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) := by
  rw [lapCommRem, reLowerOp_succ, reLowerOp_succ, covDiv0SField, covDiv0SField,
    nabla_reLower, metricTraceFirstTwoField_add, trace_reLower]
  abel

/-- **Deliverable 3: the concrete divergence-form `[reLower, Δ₂]` commutator.**

```
Δ₂(reLower T) − reLower(Δ₂ T) = div₂(reLowerPair g₂ T ∇²g₁) + tr_{g₂}(reLowerPair g₂ (∇²T) ∇²g₁),
```

with **both** carriers algebraic in `(∇²g₁, T, ∇²T)`; `nabla2_metric1` turns `∇²g₁` into
`−lapDiffFlux g₁ g₂ g₁`, i.e. into the `A₀₃` connection-difference flux
(`lapComm_reLower_flux`).  This retires the abstract defect carriers of the R4
organization. -/
theorem lapComm_reLower_eq (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    roughLap0SField (I := I) g₂ (reLower (I := I) g₁ g₂ T) -
        reLower (I := I) g₁ g₂ (roughLap0SField (I := I) g₂ T) =
      covDiv0SField (I := I) g₂
          (reLowerPair (I := I) g₂ T
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) +
        metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
          (reLowerPair (I := I) g₂ (metricNabla0S (I := I) g₂ T)
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) := by
  rw [lapComm_reLower (I := I) g₁ g₂ T, lapCommRem_reLower (I := I) g₁ g₂ T]

/-- The same commutator with both carriers written through the connection-difference flux
`A₀₃` (`nabla2_metric1`). -/
theorem lapComm_reLower_flux (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    roughLap0SField (I := I) g₂ (reLower (I := I) g₁ g₂ T) -
        reLower (I := I) g₁ g₂ (roughLap0SField (I := I) g₂ T) =
      covDiv0SField (I := I) g₂
          (reLowerPair (I := I) g₂ T
            (-lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁))) +
        metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
          (reLowerPair (I := I) g₂ (metricNabla0S (I := I) g₂ T)
            (-lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁))) := by
  rw [lapComm_reLower_eq (I := I) g₁ g₂ T, nabla2_metric1 (I := I) g₁ g₂]

end Payoff

end DifferentialGeometry.PDE.RicciFlow

end
