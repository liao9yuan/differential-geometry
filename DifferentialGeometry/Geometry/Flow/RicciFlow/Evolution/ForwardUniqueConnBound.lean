import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueConnDot
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRatePro
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Components
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Scaling

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option backward.isDefEq.respectTransparency false

/-!
# The pointwise bound on the speed of `A₀₃` (Route-K brick K1C-b)

`Evolution/ForwardUniqueConnDot.lean` (K1C-a) produces the invariant speed of the
connection-difference carrier,

`∂ₜA₀₃ = connDiffDot g₁ g₂ Adot t x
       = −2 · lowerBilin (Ric₁) (∇¹−∇²) + lowerBilin (g₁) (Adot x)`,

and `Evolution/ForwardUniqueEnergy.lean` (K3) consumes it inside the first variation of the
Kotschwar energy.  Closing the energy inequality needs `|∂ₜA₀₃|²_{g₁}` bounded by the three
difference carriers plus `|∇¹S₀₄|²`.  This file supplies

* the **named `∇¹S₀₄` carrier** (`nablaRmDiff`, `nablaRmDiffSq`) that the ruling's right-hand
  side refers to, built from `metricNabla0S g₁` and a supplied `(0,4)` field realising
  `rmDiffLowAt` — the same "supplied field + realisation equation" pattern that
  `Evolution/ForwardUniqueRmDiff.lean` uses for `Rm₂`;
* the **lowering-contraction bound** `lowerBilin_normSq_le`, which measures the lowering of a
  bilinear vector-valued map against an *arbitrary* `(0,2)` tensor by the lowering against the
  metric itself, with sharp constant `1`;
* the **reaction half of the ruling's estimate** (`connDiffDot_le_speed`), fully proved, and
  the capstone `connDiffDot_normSq_le` in the ruling's shape, which consumes the one remaining
  frontier `connSpeedLow_normSq_le`.

## The lowering-contraction bound

`lowerBilin_normSq_le` is a single statement discharging *both* gaps (2) and (3) of the K1C-b
classification of `ForwardUniqueConnDot.md`: instead of proving separately that lowering with
`g` is a fibre isometry and that a general `(0,2)` lowering is contractive, it compares the two
lowerings directly,

`|lowerBilin q A|²_g ≤ |q|²_g · |lowerBilin g A|²_g`,

so neither a mixed-variance fibre norm nor `RSLoweringNorm.lowerAllSpace` (whose producer
carries the model-space `[InnerProductSpace ℝ E]` taint) ever enters.  At `q = Ric₁` and
`A = ∇¹ − ∇²` the right-hand factor *is* `connDiffSq`, by `connDiffLow_eq_lower`.

## Hamilton's `∂ₜΓ` and the remaining frontier

`connSpeedLow_normSq_le` — the bound on the second summand `|g₁(Adot ·, ·)|²` — carries the
file's single `sorry`.  Its content is Hamilton's `∂ₜΓ = −g^{-1}(∇Ric + ∇Ric − ∇Ric)` formula
for each flow followed by the contracted-trace rewriting `∇Ric = tr_g(∇Rm)`.

An earlier version of the statement was **false** (it took only `hA` and the two Ricci-flow
equations, which do not determine `Adot`: recovering `∂ₜΓ` from `∂ₜg` needs joint `(t, y)`
regularity).  Ruling R8 repaired it by adding the honest K1 input `hΓ` in
`ChristoffelEvolutionEquationInFrameOn` currency plus two zeroth-order background norms; the
counterexample is the permanent record in `ForwardUniqueConnBound.md`, and
`connSpeedRHS_self` is its machine-checked half.

The repaired statement's **Layer A is proved**: `coeff_adot_eq` pins the frame coefficients of
`Adot` from `hΓ` by uniqueness of derivatives, `lower_raise_cancel` strips the inverse metric
from each flow's Hamilton term, and `connSpeedLow_eq` splits the lowering into
`g₁(Γ̇₁·,·) − g₂(Γ̇₂·,·) − h₀₂(Γ̇₂·,·)`.  What is left inside the `sorry`, after
`normSq0S_sub_le`, is two norm reductions — the contracted trace and the `Φ`-defect — both
detailed in the `connSpeedLow_normSq_le` docstring.  Nothing outside this file consumes the
frontier or its capstone.  The displayed dimensional constant is provisional: the *shape* of
the right-hand side, not the constant, is the interface.
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
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Frame

/-- **A `g`-orthonormal basis of the tangent fibre at a point.**  Local restatement of the
recipe used by `Evolution/ForwardUniqueRmBounds.lean` (whose version is `private`): the fibre
inner-product core of `g` at `x` feeds `stdOrthonormalBasis`. -/
private theorem exists_onFrame (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ b : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
        (TangentSpace I x),
      ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : Real) else 0 := by
  classical
  let D := (tangentMetricData_gen (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  refine ⟨ob.toBasis, ?_⟩
  intro i j
  have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
    MetricFiberData.toCore_inner D (ob i) (ob j)
  change g.inner x (ob.toBasis i) (ob.toBasis j) = if i = j then (1 : Real) else 0
  rw [← TangentMetricData_gen.inner_eq_gen
    (tangentMetricData_gen (I := I) g x) (ob.toBasis i) (ob.toBasis j)]
  change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
  rw [← hinner]
  exact ob.inner_eq_ite i j

/-- The identity inverse-metric witness attached to a `g`-orthonormal basis. -/
private theorem onFrame_inv {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (b : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : Real) else 0) :
    MetricInverseInBasis_gen (I := I) g x b (identityInvMetric (Idx := Idx)) := by
  intro i j
  constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]

/-- In a `g`-orthonormal basis the coordinates of a tangent vector are its `g`-inner products
with the basis vectors. -/
private theorem repr_inner {Idx : Type*} [Finite Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (b : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : Real) else 0)
    (v : TangentSpace I x) (k : Idx) :
    b.repr v k = g.inner x v (b k) := by
  classical
  haveI : Fintype Idx := Fintype.ofFinite Idx
  have hval : g.inner x v (b k) =
      metricTensorField (I := I) g x (fun a : Fin 2 => if a = 0 then v else b k) := by
    rw [metricTensorField_apply]; simp
  rw [hval, tensor02_expand (I := I) (metricTensorField (I := I) g x) b v (b k)]
  have hbb : ∀ l : Idx,
      metricTensorField (I := I) g x (fun a : Fin 2 => if a = 0 then b l else b k) =
        (if l = k then (1 : Real) else 0) := by
    intro l
    rw [metricTensorField_apply]
    simpa using hON l k
  simp only [hbb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Frame

section SlotSums

/-- Reindexing of a `2`-slot index map as a pair. -/
private def slotEq2 {Idx : Type*} : (Fin 2 -> Idx) ≃ Idx × Idx where
  toFun s := (s 0, s 1)
  invFun p := fun a => if a = 0 then p.1 else p.2
  left_inv := by intro s; funext a; fin_cases a <;> simp
  right_inv := by intro p; simp

/-- Reindexing of a `3`-slot index map as a triple. -/
private def slotEq3 {Idx : Type*} : (Fin 3 -> Idx) ≃ Idx × Idx × Idx where
  toFun s := (s 0, s 1, s 2)
  invFun p := fun a => if a = 0 then p.1 else if a = 1 then p.2.1 else p.2.2
  left_inv := by intro s; funext a; fin_cases a <;> simp
  right_inv := by intro p; simp

/-- A sum over `2`-slot index maps is a double sum. -/
private theorem sumSlots2 {Idx : Type*} [Fintype Idx] (F : (Fin 2 -> Idx) -> Real) :
    ∑ s : Fin 2 -> Idx, F s =
      ∑ i : Idx, ∑ j : Idx, F (fun a : Fin 2 => if a = 0 then i else j) := by
  classical
  have h := Equiv.sum_comp (slotEq2 (Idx := Idx)) (fun p => F (slotEq2.symm p))
  simp only [Equiv.symm_apply_apply] at h
  rw [h, Fintype.sum_prod_type]
  rfl

/-- A sum over `3`-slot index maps is a triple sum. -/
private theorem sumSlots3 {Idx : Type*} [Fintype Idx] (F : (Fin 3 -> Idx) -> Real) :
    ∑ s : Fin 3 -> Idx, F s =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx,
        F (fun a : Fin 3 => if a = 0 then i else if a = 1 then j else k) := by
  classical
  have h := Equiv.sum_comp (slotEq3 (Idx := Idx)) (fun p => F (slotEq3.symm p))
  simp only [Equiv.symm_apply_apply] at h
  rw [h, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

end SlotSums

section Contraction

/-- **`A₀₃` is the `g₁`-lowering of the connection difference.**  This identifies the carrier
of `Evolution/ForwardUniqueFields.lean` with the reference object of `lowerBilin_normSq_le`,
so that `connDiffSq` is literally the right-hand factor there. -/
theorem connDiffLow_eq_lower (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    connDiffLowAt (I := I) g₁ g₂ x =
      lowerBilin (I := I) (metricTensorField (I := I) g₁ x)
        (CovariantDerivative.difference (metricCov (I := I) g₁)
          (metricCov (I := I) g₂) x) := by
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [connDiffLowAt_apply, lowerBilin_apply, metricTensorField_apply]
  simp

/-- The basis components of a lowered bilinear map. -/
private theorem comp_lowerBilin {Idx : Type*} [Fintype Idx] {x : M}
    (b : Module.Basis Idx Real (TangentSpace I x))
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (i j k : Idx) :
    component0S (I := I) b (lowerBilin (I := I) q A)
        (fun a : Fin 3 => if a = 0 then i else if a = 1 then j else k) =
      q (fun a : Fin 2 => if a = 0 then (A (b j)) (b i) else b k) := by
  classical
  rw [component0S_apply, lowerBilin_apply]
  congr 1

/-- **The lowering-contraction bound.**  Lowering the upper index of a bilinear vector-valued
map `A` against an arbitrary `(0,2)` fibre tensor `q` costs exactly the fibre norm of `q`,
measured against the lowering by the metric itself:

`|lowerBilin q A|²_g ≤ |q|²_g · |lowerBilin g A|²_g`.

The constant is sharp.  In a `g`-orthonormal frame the components of `lowerBilin g A` are the
coordinates of the vectors `A(e_j) e_i`, those of `lowerBilin q A` are their contractions
against the component matrix of `q`, and the estimate is the discrete Cauchy--Schwarz
inequality summed over the three slots. -/
theorem lowerBilin_normSq_le (g : SmoothRiemannianMetric I M) (x : M)
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    normSq0S (I := I) g x 3 (lowerBilin (I := I) q A) ≤
      normSq0S (I := I) g x 2 q *
        normSq0S (I := I) g x 3
          (lowerBilin (I := I) (metricTensorField (I := I) g x) A) := by
  classical
  obtain ⟨b, hON⟩ := exists_onFrame (I := I) g x
  have hinv := onFrame_inv (I := I) g b hON
  -- (A) the fibre norm of `q` as a double sum of its components
  have hq : normSq0S (I := I) g x 2 q =
      ∑ l : Fin (Module.finrank Real (TangentSpace I x)),
        ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
          (q (fun a : Fin 2 => if a = 0 then b l else b k)) ^ 2 := by
    rw [normSq0S_identity_eq_sum_sq (I := I) g x 2 b hinv, sumSlots2]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [component0S_apply]
    congr 1
    funext a
    by_cases ha : a = 0 <;> simp [ha]
  -- (B) the fibre norm of the metric lowering as a triple sum of coordinates
  have href : normSq0S (I := I) g x 3
      (lowerBilin (I := I) (metricTensorField (I := I) g x) A) =
      ∑ i : Fin (Module.finrank Real (TangentSpace I x)),
        ∑ j : Fin (Module.finrank Real (TangentSpace I x)),
          ∑ l : Fin (Module.finrank Real (TangentSpace I x)),
            (b.repr ((A (b j)) (b i)) l) ^ 2 := by
    rw [normSq0S_identity_eq_sum_sq (I := I) g x 3 b hinv, sumSlots3]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => ?_
    congr 1
    rw [comp_lowerBilin (I := I) b _ A i j l, metricTensorField_apply,
      repr_inner (I := I) g b hON]
    simp
  -- (C) the fibre norm of the `q` lowering as a triple sum of contractions
  have hlow : normSq0S (I := I) g x 3 (lowerBilin (I := I) q A) =
      ∑ i : Fin (Module.finrank Real (TangentSpace I x)),
        ∑ j : Fin (Module.finrank Real (TangentSpace I x)),
          ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
            (∑ l : Fin (Module.finrank Real (TangentSpace I x)),
              b.repr ((A (b j)) (b i)) l *
                q (fun a : Fin 2 => if a = 0 then b l else b k)) ^ 2 := by
    rw [normSq0S_identity_eq_sum_sq (I := I) g x 3 b hinv, sumSlots3]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [comp_lowerBilin (I := I) b q A i j k,
      tensor02_expand (I := I) q b ((A (b j)) (b i)) (b k)]
  -- the estimate, slot by slot
  rw [hlow, hq, href, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hstep : ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
        (∑ l : Fin (Module.finrank Real (TangentSpace I x)),
          b.repr ((A (b j)) (b i)) l *
            q (fun a : Fin 2 => if a = 0 then b l else b k)) ^ 2 ≤
      ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
        ((∑ l : Fin (Module.finrank Real (TangentSpace I x)),
            (b.repr ((A (b j)) (b i)) l) ^ 2) *
          ∑ l : Fin (Module.finrank Real (TangentSpace I x)),
            (q (fun a : Fin 2 => if a = 0 then b l else b k)) ^ 2) :=
    Finset.sum_le_sum fun k _ =>
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun l => b.repr ((A (b j)) (b i)) l)
        (fun l => q (fun a : Fin 2 => if a = 0 then b l else b k))
  refine hstep.trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_comm]
  ring

end Contraction

section Carrier

/-- **The `S₀₄` realisation predicate.**  A `(0,4)` field realises the curvature-difference
carrier `rmDiffLowAt` of `Evolution/ForwardUniqueFields.lean`.  Following the pattern of
`Evolution/ForwardUniqueRmDiff.lean`, the field is supplied and its pointwise value is pinned
by an equation, rather than being constructed here: the smoothness of `x ↦ rmDiffLowAt g₁ g₂ x`
is the producer's business, not this file's. -/
def IsRmDiffField (g₁ g₂ : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) : Prop :=
  ∀ x : M, S x = rmDiffLowAt (I := I) g₁ g₂ x

/-- **`∇¹S₀₄`**: the `g₁`-covariant derivative of the curvature-difference carrier, a `(0,5)`
field whose new derivative slot is slot `0`. -/
def nablaRmDiff (g₁ : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5 :=
  metricNabla0S (I := I) g₁ S

/-- **`|∇¹S₀₄|²_{g₁}`** at a point: the fourth integrand of the ruling's right-hand side. -/
def nablaRmDiffSq (g₁ : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M) : Real :=
  normSq0S (I := I) g₁ x 5 (nablaRmDiff (I := I) g₁ S x)

theorem nablaRmDiffSq_nonneg (g₁ : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M) :
    0 ≤ nablaRmDiffSq (I := I) g₁ S x :=
  normSq0S_nonneg (I := I) g₁ x 5 _

/-- Equal metrics make the `∇¹S₀₄` integrand vanish: the carrier is a genuine difference. -/
theorem nablaRmDiffSq_self (g : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (hS : IsRmDiffField (I := I) g g S) (x : M) :
    nablaRmDiffSq (I := I) g S x = 0 := by
  have hzero : S = 0 := by
    refine DFunLike.ext _ _ fun y => ?_
    rw [hS y, rmDiffLowAt_self]
    rfl
  have hn : metricNabla0S (I := I) g S = 0 := by
    rw [hzero]
    simpa using metricNabla0S_smul (I := I) (s := 4) g (0 : Real) 0
  have hfield : nablaRmDiff (I := I) g S = 0 := hn
  have hz : nablaRmDiff (I := I) g S x = 0 := by rw [hfield]; rfl
  change normSq0S (I := I) g x 5 (nablaRmDiff (I := I) g S x) = 0
  rw [hz]
  simpa using normSq0S_smul (I := I) g (0 : Real)
    (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)

end Carrier

section NablaRicci

/-- **Splitting of the `∇Ric`-difference.**  The object that Hamilton's `∂ₜΓ` formula feeds
into the speed of `A₀₃` is `∇¹Ric₁ − ∇²Ric₂`; it splits into a single `g₁`-derivative of the
*Ricci difference* plus the Kotschwar flux of the background `Ric₂`,

`∇¹Ric₁ − ∇²Ric₂ = ∇¹(Ric₁ − Ric₂) + (∇¹ − ∇²)Ric₂`,

with no derivative of the metric difference anywhere.  Stated for arbitrary `(0,2)` fields, so
it also covers the `Ric`-realisation-free uses. -/
theorem nablaRicDiff_split (g₁ g₂ : SmoothRiemannianMetric I M)
    (Ric₁ Ric₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2) :
    metricNabla0S (I := I) g₁ Ric₁ - metricNabla0S (I := I) g₂ Ric₂ =
      metricNabla0S (I := I) g₁ (Ric₁ - Ric₂) + lapDiffFlux (I := I) g₁ g₂ Ric₂ := by
  rw [metricNabla0S_sub, lapDiffFlux]
  abel

/-- **The background half of the `∇Ric`-difference bound.**  The flux summand of
`nablaRicDiff_split` is `O(|A₀₃|²·|Ric₂|²)` — zeroth order in the background's derivatives —
by the existing `fluxNormSq_le`.  Only the `∇¹(Ric₁ − Ric₂)` summand is left for the
contracted-trace step, which is what `connSpeedLow_normSq_le` still owes. -/
theorem nablaRicDiff_le (g₁ g₂ : SmoothRiemannianMetric I M)
    (Ric₁ Ric₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2) (x : M) :
    normSq0S (I := I) g₁ x 3
        ((metricNabla0S (I := I) g₁ Ric₁ - metricNabla0S (I := I) g₂ Ric₂) x) ≤
      2 * normSq0S (I := I) g₁ x 3 (metricNabla0S (I := I) g₁ (Ric₁ - Ric₂) x) +
        8 * (Module.finrank Real E : Real) ^ 3 * connDiffSq (I := I) g₁ g₂ x *
          normSq0S (I := I) g₁ x 2 (Ric₂ x) := by
  have hpt : (metricNabla0S (I := I) g₁ Ric₁ - metricNabla0S (I := I) g₂ Ric₂) x =
      metricNabla0S (I := I) g₁ (Ric₁ - Ric₂) x + lapDiffFlux (I := I) g₁ g₂ Ric₂ x := by
    rw [nablaRicDiff_split (I := I) g₁ g₂ Ric₁ Ric₂]; rfl
  rw [hpt]
  refine le_trans (normSq0S_add_le (I := I) g₁ x 3 _ _) ?_
  have hflux : normSq0S (I := I) g₁ x 3 (lapDiffFlux (I := I) g₁ g₂ Ric₂ x) ≤
      4 * (Module.finrank Real E : Real) ^ 3 * connDiffSq (I := I) g₁ g₂ x *
        normSq0S (I := I) g₁ x 2 (Ric₂ x) := by
    refine (fluxNormSq_le (I := I) (s := 2) g₁ g₂ Ric₂ x).trans_eq ?_
    norm_num
  linarith

end NablaRicci

section Hamilton

variable {Idx : Type*} [Fintype Idx] {u : Set M} {x : M}

/-- **Uniqueness of the derivative pins the frame coefficients of a supplied invariant speed.**
`hA` says the supplied `Adot x` *is* the time derivative of the connection-difference curve;
`hΓ` says that same curve's frame components have derivative `c`.  Since a real-valued curve
has at most one derivative, the frame coefficients of `Adot x` are `c`.

This is the converse direction of `ForwardUniqueConnDot.connDiffVec_hasDerivAt` (which turns
component derivatives into the invariant one), and it is what lets K1's Hamilton right-hand
side reach an invariant statement about `Adot`. -/
theorem coeff_adot_eq
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u) (hx : x ∈ u) {t : Real}
    (Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    (hA : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real =>
          CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x Y X)
        ((Adot x Y) X) t)
    (c : Idx -> Idx -> Idx -> Real)
    (hΓ : ∀ i j k : Idx,
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k)
        (c i j k) t)
    (i j k : Idx) :
    hframe.coeff k x ((Adot x (frame j x)) (frame i x)) = c i j k := by
  classical
  set b : Module.Basis Idx Real (TangentSpace I x) := hframe.toBasisAt hx with hbdef
  have hbcoe : ∀ l : Idx, b l = frame l x := fun l =>
    IsLocalFrameOn.toBasisAt_coe hframe hx l
  have hcoeff : ∀ (l : Idx) (w : TangentSpace I x),
      hframe.coeff l x w = b.repr w l := by
    intro l w
    simp [IsLocalFrameOn.coeff, hx, hbdef, Module.Basis.coord_apply]
  have hfr : ∀ l : Idx, MDifferentiableAt I I.tangent (T% (frame l)) x := fun l =>
    (hframe.contMDiffAt hu hx l).mdifferentiableAt (by simp)
  -- the connection-difference curve, read through the frame
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
  -- the supplied speed, read through the same coordinate functional
  have hL : HasDerivAt
      (fun r : Real =>
        b.repr (CovariantDerivative.difference (metricCov (I := I) (g₁ r))
          (metricCov (I := I) (g₂ r)) x (b j) (b i)) k)
      (b.repr ((Adot x (b j)) (b i)) k) t := by
    have h := (LinearMap.toContinuousLinearMap
      (b.coord k)).hasFDerivAt.comp_hasDerivAt t (hA (b i) (b j))
    simpa using h
  rw [hfun] at hL
  have huniq := hL.unique (hΓ i j k)
  rw [hcoeff k, ← hbcoe i, ← hbcoe j]
  exact huniq

/-- **Lowering with a metric cancels that metric's inverse-metric raising.**  This is the
structural core of the flow-1 half of K1C-b: `christoffelEvolutionRHSInFrame` raises the
lowered Hamilton right-hand side with `g`'s inverse components, and pairing the result back
against `g` returns the lowered right-hand side unchanged — no inverse metric survives.  Stated
for an arbitrary lowered family `L`, so it applies verbatim to either flow. -/
theorem lower_raise_cancel [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (b : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x b gInv)
    (L : Idx -> Real) (k : Idx) :
    ∑ m : Idx, (∑ l : Idx, gInv m l * L l) * g.inner x (b m) (b k) = L k := by
  classical
  have hrow : ∀ m : Idx, (∑ l : Idx, gInv m l * L l) * g.inner x (b m) (b k) =
      ∑ l : Idx, g.inner x (b k) (b m) * gInv m l * L l := by
    intro m
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [g.symm x (b m) (b k)]
    ring
  rw [Finset.sum_congr rfl fun m _ => hrow m, Finset.sum_comm]
  have hcol : ∀ l : Idx,
      (∑ m : Idx, g.inner x (b k) (b m) * gInv m l * L l) =
        (if k = l then (1 : Real) else 0) * L l := by
    intro l
    rw [← Finset.sum_mul]
    exact congrArg (fun r : Real => r * L l) (hinv k l).2
  rw [Finset.sum_congr rfl fun l _ => hcol l]
  simp

/-- Basis components of a lowered bilinear map, expanded in the lowering slot. -/
private theorem lowerBilin_basis
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (b : Module.Basis Idx Real (TangentSpace I x)) (v : Fin 3 -> Idx) :
    lowerBilin (I := I) q A (fun a : Fin 3 => b (v a)) =
      ∑ m : Idx, b.repr ((A (b (v 1))) (b (v 0))) m *
        q (fun a : Fin 2 => if a = 0 then b m else b (v 2)) := by
  rw [lowerBilin_apply, tensor02_expand (I := I) q b _ (b (v 2))]

/-- The basis coordinates of `bilinOfComp` are the prescribed components. -/
private theorem repr_bilinOfComp
    (b : Module.Basis Idx Real (TangentSpace I x))
    (c : Idx -> Idx -> Idx -> Real) (i j m : Idx) :
    b.repr ((bilinOfComp (I := I) b c (b j)) (b i)) m = c i j m := by
  classical
  rw [bilinOfComp_basis]
  simp [Finsupp.single_apply]

/-- **The splitting of the lowered invariant speed (K1C-b, Layer A).**
The `g₁`-lowering of the supplied speed `Adot x` splits into the two flows' own-lowered
Hamilton right-hand sides plus a single `h₀₂`-defect:

`g₁(Adot ·, ·) = g₁(Γ̇₁ ·, ·) − g₂(Γ̇₂ ·, ·) − h₀₂(Γ̇₂ ·, ·)`,

where `Γ̇ₐ` is the bilinear map whose frame components are K1's `christoffelEvolutionRHSInFrame`.
Only the `h₀₂`-defect couples the two flows' metrics; each Hamilton term is lowered by *its
own* metric, so `lower_raise_cancel` strips the inverse metric from both.  This is the identity
that makes the Hamilton input `hΓ` bite: `Adot` is pinned by `coeff_adot_eq`. -/
theorem connSpeedLow_eq
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u) (hx : x ∈ u) {t : Real}
    (Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    (hA : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real =>
          CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x Y X)
        ((Adot x Y) X) t)
    (c₁ c₂ : Idx -> Idx -> Idx -> Real)
    (hΓ : ∀ i j k : Idx,
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k)
        (c₁ i j k - c₂ i j k) t) :
    lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x) (Adot x) =
      lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x)
          (bilinOfComp (I := I) (hframe.toBasisAt hx) c₁) -
        lowerBilin (I := I) (metricTensorField (I := I) (g₂ t) x)
          (bilinOfComp (I := I) (hframe.toBasisAt hx) c₂) -
        lowerBilin (I := I) (metricDiffAt (I := I) (g₁ t) (g₂ t) x)
          (bilinOfComp (I := I) (hframe.toBasisAt hx) c₂) := by
  classical
  set b : Module.Basis Idx Real (TangentSpace I x) := hframe.toBasisAt hx with hbdef
  have hbcoe : ∀ l : Idx, b l = frame l x := fun l =>
    IsLocalFrameOn.toBasisAt_coe hframe hx l
  have hcoeff : ∀ (l : Idx) (w : TangentSpace I x),
      hframe.coeff l x w = b.repr w l := by
    intro l w
    simp [IsLocalFrameOn.coeff, hx, hbdef, Module.Basis.coord_apply]
  -- the coordinates of the supplied speed, pinned by uniqueness of derivatives
  have hrepr : ∀ i j m : Idx,
      b.repr ((Adot x (b j)) (b i)) m = c₁ i j m - c₂ i j m := by
    intro i j m
    have h := coeff_adot_eq (I := I) g₁ g₂ frame hframe hu hx Adot hA
      (fun i' j' k' => c₁ i' j' k' - c₂ i' j' k') hΓ i j m
    rw [hcoeff m, ← hbcoe i, ← hbcoe j] at h
    exact h
  refine tensor0SSpace_ext (𝕜 := Real) 3 x fun w => ?_
  set L : ContinuousMultilinearMap Real (fun _ : Fin 3 => TangentSpace I x) Real :=
    lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x) (Adot x) with hLdef
  set R : ContinuousMultilinearMap Real (fun _ : Fin 3 => TangentSpace I x) Real :=
    lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x)
        (bilinOfComp (I := I) b c₁) -
      lowerBilin (I := I) (metricTensorField (I := I) (g₂ t) x)
        (bilinOfComp (I := I) b c₂) -
      lowerBilin (I := I) (metricDiffAt (I := I) (g₁ t) (g₂ t) x)
        (bilinOfComp (I := I) b c₂) with hRdef
  suffices h : L.toMultilinearMap = R.toMultilinearMap by
    exact congrArg
      (fun T : MultilinearMap Real (fun _ : Fin 3 => TangentSpace I x) Real => T w) h
  refine Module.Basis.ext_multilinear (e := fun _ : Fin 3 => b) ?_
  intro v
  change L (fun a : Fin 3 => b (v a)) = R (fun a : Fin 3 => b (v a))
  have hRval : R (fun a : Fin 3 => b (v a)) =
      lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x)
          (bilinOfComp (I := I) b c₁) (fun a : Fin 3 => b (v a)) -
        lowerBilin (I := I) (metricTensorField (I := I) (g₂ t) x)
          (bilinOfComp (I := I) b c₂) (fun a : Fin 3 => b (v a)) -
        lowerBilin (I := I) (metricDiffAt (I := I) (g₁ t) (g₂ t) x)
          (bilinOfComp (I := I) b c₂) (fun a : Fin 3 => b (v a)) := by
    rw [hRdef]
    rw [Tensor0SSpace.sub_apply (I := I) 3 x _ _ (fun a : Fin 3 => b (v a)),
      Tensor0SSpace.sub_apply (I := I) 3 x _ _ (fun a : Fin 3 => b (v a))]
  rw [hLdef, hRval, lowerBilin_basis (I := I) _ _ b v, lowerBilin_basis (I := I) _ _ b v,
    lowerBilin_basis (I := I) _ _ b v, lowerBilin_basis (I := I) _ _ b v,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hrepr (v 0) (v 1) m, repr_bilinOfComp (I := I) b c₁, repr_bilinOfComp (I := I) b c₂,
    metricTensorField_apply, metricTensorField_apply, metricDiffAt_apply]
  simp only []
  ring

end Hamilton

section MainBound

/-- Two-term expansion for a difference of `(0,s)` fibre tensors. -/
private theorem normSq0S_sub_le (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    normSq0S (I := I) g x s (A - B) ≤
      2 * normSq0S (I := I) g x s A + 2 * normSq0S (I := I) g x s B := by
  have hAB : A - B = A + (-1 : Real) • B := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  rw [hAB]
  refine (normSq0S_add_le (I := I) g x s A _).trans ?_
  rw [normSq0S_smul]
  norm_num

/-- **The reaction half of K1C-b.**  The moving-carrier reaction term of `∂ₜA₀₃` is controlled
by the background Ricci norm times the connection-difference carrier itself; the remaining
summand is the lowered speed of the connection difference, which `connSpeedLow_normSq_le`
handles.  `Λric` is a named background bound, in the hypothesis style of
`Evolution/ForwardUniqueRmBounds.lean`. -/
theorem connDiffDot_le_speed
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    (t : Real) (x : M) {Λric : Real}
    (hΛric : normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x) ≤ Λric) :
    normSq0S (I := I) (g₁ t) x 3 (connDiffDot (I := I) g₁ g₂ Adot t x) ≤
      8 * Λric * connDiffSq (I := I) (g₁ t) (g₂ t) x +
        2 * normSq0S (I := I) (g₁ t) x 3
          (lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x) (Adot x)) := by
  have hdef : connDiffDot (I := I) g₁ g₂ Adot t x =
      (-2 : Real) • lowerBilin (I := I) (metricRicciAt (I := I) (g₁ t) x)
          (CovariantDerivative.difference (metricCov (I := I) (g₁ t))
            (metricCov (I := I) (g₂ t)) x) +
        lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x) (Adot x) := rfl
  rw [hdef]
  refine le_trans (normSq0S_add_le (I := I) (g₁ t) x 3 _ _) ?_
  have hsmul : normSq0S (I := I) (g₁ t) x 3
      ((-2 : Real) • lowerBilin (I := I) (metricRicciAt (I := I) (g₁ t) x)
        (CovariantDerivative.difference (metricCov (I := I) (g₁ t))
          (metricCov (I := I) (g₂ t)) x)) =
      4 * normSq0S (I := I) (g₁ t) x 3
        (lowerBilin (I := I) (metricRicciAt (I := I) (g₁ t) x)
          (CovariantDerivative.difference (metricCov (I := I) (g₁ t))
            (metricCov (I := I) (g₂ t)) x)) := by
    rw [normSq0S_smul]; norm_num
  rw [hsmul]
  have hreact : normSq0S (I := I) (g₁ t) x 3
      (lowerBilin (I := I) (metricRicciAt (I := I) (g₁ t) x)
        (CovariantDerivative.difference (metricCov (I := I) (g₁ t))
          (metricCov (I := I) (g₂ t)) x)) ≤
      Λric * connDiffSq (I := I) (g₁ t) (g₂ t) x := by
    refine le_trans (lowerBilin_normSq_le (I := I) (g₁ t) x _ _) ?_
    rw [connDiffSq_def, connDiffLow_eq_lower]
    exact mul_le_mul_of_nonneg_right hΛric (normSq0S_nonneg (I := I) (g₁ t) x 3 _)
  linarith

/-- **Degenerate-case collapse of the K1C-b right-hand side.**  When the two metrics agree at
time `t`, every carrier on the right of `connSpeedLow_normSq_le` vanishes, so that right-hand
side is `0` — for *every* value of the background bounds `Λ`, `B₁`, `B₂`.  Companion of
`nablaRmDiffSq_self`, and the formal half of the counterexample recorded in the
`connSpeedLow_normSq_le` docstring. -/
theorem connSpeedRHS_self (g₁ g₂ : Real → SmoothRiemannianMetric I M) {t : Real} (x : M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (hS : IsRmDiffField (I := I) (g₁ t) (g₂ t) S)
    (hg : g₁ t = g₂ t) (Λ B₁ B₂ : Real) :
    9 * (Module.finrank Real E : Real) ^ 6 *
        (nablaRmDiffSq (I := I) (g₁ t) S x +
          (1 + Λ) ^ 2 * (B₁ + B₂) *
            (metricDiffSq (I := I) (g₁ t) (g₂ t) x +
              connDiffSq (I := I) (g₁ t) (g₂ t) x)) = 0 := by
  have hzero : ∀ s : Nat,
      normSq0S (I := I) (g₂ t) x s
          (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) = 0 :=
    fun s => ((tensor0SMetricData (I := I) (g₂ t) x s).inner_self_eq_zero_iff 0).2 rfl
  rw [hg] at hS ⊢
  rw [nablaRmDiffSq_self (I := I) (g₂ t) S hS x, metricDiffSq_def, connDiffSq_def,
    metricDiffAt_self, connDiffLowAt_self, hzero, hzero]
  ring

/-- **K1C-b: the bound on the lowered invariant speed of the connection difference.**

`|g₁(∂ₜ(∇¹−∇²)·, ·)|²_{g₁} ≤ C(n)·(|∇¹S₀₄|² + (1+Λ)²(B₁+B₂+B₃+B₄)(|h₀₂|² + |A₀₃|²))`.

**Repaired interface (ruling R8).**  An earlier version of this statement took only `hA`,
`hRF₁`, `hRF₂` and was *false*: those do not determine `Adot`, because recovering `∂ₜΓ` from
`∂ₜg` interchanges `∂ₜ` with a spatial derivative and so needs joint `(t, y)` regularity.  The
counterexample and the full analysis are the permanent record in `ForwardUniqueConnBound.md`;
`connSpeedRHS_self` above is its machine-checked half.  The repair adds the honest K1 input
`hΓ` — the conclusion of `ChristoffelEvolutionEquationInFrameOn`, discharged from a solution
pair by `christoffelEvolution_of_solution` — with `hA` kept as the realisation link, plus the
two zeroth-order background norms `B₃ ≥ |Ric₂|²` and `B₄ ≥ |Rm₂|²`.

**Status: one `sorry`, on a strictly reduced goal.**  Layer A is *proved* and is on the proof
path: `coeff_adot_eq` pins the frame coefficients of `Adot` by uniqueness of derivatives, and
`connSpeedLow_eq` splits the lowering into `g₁(Γ̇₁·,·) − g₂(Γ̇₂·,·) − h₀₂(Γ̇₂·,·)`, each Hamilton
term lowered by *its own* metric.  After `normSq0S_sub_le` two norm reductions remain:

* **the contracted trace.**  `lower_raise_cancel` strips the inverse metric from each Hamilton
  term, so `g₁(Γ̇₁·,·) − g₂(Γ̇₂·,·)` is the permutation sum `−T − T∘(0 1) + T∘(0↦2,1↦0,2↦1)` of
  `T = ∇¹Ric₁ − ∇²Ric₂`; `normSq0S_domDomCongr` makes each summand isometric, `nablaRicDiff_le`
  (green above) splits off `8n³·|A₀₃|²·|Ric₂|²` (this is what `B₃` is for), and
  `∇¹(Ric₁ − Ric₂) = tr_{g₁}(∇¹S₀₄)` follows from `ricciDiff_eq_trace`
  (`Evolution/ForwardUniqueRatePro.lean`) plus `nabla_metricTraceFirstTwo0S` /
  `traceNablaShuffle` — pure `∇`-past-trace commutation, *not* second Bianchi — and
  `traceNormSq_le`.  Note `ricciDiff_eq_trace` has **no residual `h₀₂` term** (both flows are
  lowered *and* traced with `g₁`), so `B₄` is not consumed on this route.
* **the `Φ`-defect.**  `lowerBilin_normSq_le` (green above) gives
  `|h₀₂(Γ̇₂·,·)|² ≤ |h₀₂|²·|g₁(Γ̇₂·,·)|²`, and `|g₁(Γ̇₂·,·)|²_{g₁} ≤ Λ²·|g₂(Γ̇₂·,·)|²_{g₁}`: in a
  `g₁`-orthonormal frame this is `|g₂^♯ω|²_{g₁} ≤ Λ|g₂^♯ω|²_{g₂} = Λ|ω|²_{g₂^{-1}} ≤ Λ²|ω|²_{g₁^{-1}}`,
  so the *one-sided* `hΛ` suffices, at cost `Λ²`.  The missing API is a slot-precomposition
  norm bound; `Tensor0SRiemannian/Comparison.lean` (`normSq0S_upper_le_of_equiv`,
  `normSq0S_le_of_metric_equiv`) is the layer it belongs in.

The displayed constant `100 n⁶` is provisional and generous; resize it when the two reductions
land. -/
theorem connSpeedLow_normSq_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    {t : Real} {x : M}
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u) (hx : x ∈ u)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (hS : IsRmDiffField (I := I) (g₁ t) (g₂ t) S)
    (Ric₁ Ric₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hRic₁ : ∀ y : M, Ric₁ y = metricRicciAt (I := I) (g₁ t) y)
    (hRic₂ : ∀ y : M, Ric₂ y = metricRicciAt (I := I) (g₂ t) y)
    (Rm₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (hRm₂ : ∀ y : M, Rm₂ y =
      DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
        (I := I) (g₁ t) (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)) y)
    (gInv₁ gInv₂ : Real ->
      DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (hgInv₁ : MetricInverseInBasis_gen (I := I) (g₁ t) x (hframe.toBasisAt hx)
      (fun i j : Idx => gInv₁ t x i j))
    (hgInv₂ : MetricInverseInBasis_gen (I := I) (g₂ t) x (hframe.toBasisAt hx)
      (fun i j : Idx => gInv₂ t x i j))
    (nablaRic₁ nablaRic₂ : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hNR₁ : ∀ d a b : Idx, nablaRic₁ t x d a b =
      component0S (I := I) (hframe.toBasisAt hx)
        (metricNabla0S (I := I) (g₁ t) Ric₁ x)
        (fun s : Fin 3 => if s = 0 then d else if s = 1 then a else b))
    (hNR₂ : ∀ d a b : Idx, nablaRic₂ t x d a b =
      component0S (I := I) (hframe.toBasisAt hx)
        (metricNabla0S (I := I) (g₂ t) Ric₂ x)
        (fun s : Fin 3 => if s = 0 then d else if s = 1 then a else b))
    (hΓ : ∀ i j k : Idx,
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k)
        (christoffelEvolutionRHSInFrame (M := M) gInv₁ nablaRic₁ t x i j k -
          christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ t x i j k) t)
    (hA : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real =>
          CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x Y X)
        ((Adot x Y) X) t)
    (hRF₁ : ∀ (y : M) (X Y : TangentSpace I y),
      HasDerivAt (fun r : Real => (g₁ r).inner y X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) y
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hRF₂ : ∀ (y : M) (X Y : TangentSpace I y),
      HasDerivAt (fun r : Real => (g₂ r).inner y X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₂ t) y
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    {Λ B₁ B₂ B₃ B₄ : Real} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v : TangentSpace I x, (g₁ t).inner x v v ≤ Λ * (g₂ t).inner x v v)
    (hB₁ : normSq0S (I := I) (g₁ t) x 3 (metricNabla0S (I := I) (g₂ t) Ric₂ x) ≤ B₁)
    (hB₂ : normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₂ t) Rm₂ x) ≤ B₂)
    (hB₃ : normSq0S (I := I) (g₁ t) x 2 (Ric₂ x) ≤ B₃)
    (hB₄ : normSq0S (I := I) (g₁ t) x 4 (Rm₂ x) ≤ B₄) :
    normSq0S (I := I) (g₁ t) x 3
        (lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x) (Adot x)) ≤
      100 * (Module.finrank Real E : Real) ^ 6 *
        (nablaRmDiffSq (I := I) (g₁ t) S x +
          (1 + Λ) ^ 2 * (B₁ + B₂ + B₃ + B₄) *
            (metricDiffSq (I := I) (g₁ t) (g₂ t) x +
              connDiffSq (I := I) (g₁ t) (g₂ t) x)) := by
  -- Layer A: Hamilton's `∂ₜΓ` reaches `Adot` and splits off the single `h₀₂`-defect.
  rw [connSpeedLow_eq (I := I) g₁ g₂ frame hframe hu hx Adot hA
    (fun i j k => christoffelEvolutionRHSInFrame (M := M) gInv₁ nablaRic₁ t x i j k)
    (fun i j k => christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ t x i j k) hΓ]
  refine le_trans (normSq0S_sub_le (I := I) (g₁ t) x 3 _ _) ?_
  -- Remaining: the two norm reductions (contracted trace; `Φ`-defect).  See the docstring.
  sorry

/-- **K1C-b, the ruling's bound on `|∂ₜA₀₃|²`.**  The speed of the connection-difference
carrier is controlled pointwise by the three difference carriers and the `∇¹S₀₄` integrand,
with all background norms (`Λric`, `Λ`, `B₁`, `B₂`) as named hypothesis arguments.  This is the
statement `forwardUniqueRate_le` is meant to consume; it is proved from `connDiffDot_le_speed`
(green) and `connSpeedLow_normSq_le`, and carries the same repaired (ruling R8) input list —
the K1 Hamilton input `hΓ` and the four named background norms.  It therefore inherits the one
`sorry` of `connSpeedLow_normSq_le`; downstream wiring (`adotLe`) absorbs `B₃`/`B₄` into the
slab constants. -/
theorem connDiffDot_normSq_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    {t : Real} {x : M}
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u) (hx : x ∈ u)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (hS : IsRmDiffField (I := I) (g₁ t) (g₂ t) S)
    (Ric₁ Ric₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hRic₁ : ∀ y : M, Ric₁ y = metricRicciAt (I := I) (g₁ t) y)
    (hRic₂ : ∀ y : M, Ric₂ y = metricRicciAt (I := I) (g₂ t) y)
    (Rm₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (hRm₂ : ∀ y : M, Rm₂ y =
      DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
        (I := I) (g₁ t) (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)) y)
    (gInv₁ gInv₂ : Real ->
      DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (hgInv₁ : MetricInverseInBasis_gen (I := I) (g₁ t) x (hframe.toBasisAt hx)
      (fun i j : Idx => gInv₁ t x i j))
    (hgInv₂ : MetricInverseInBasis_gen (I := I) (g₂ t) x (hframe.toBasisAt hx)
      (fun i j : Idx => gInv₂ t x i j))
    (nablaRic₁ nablaRic₂ : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hNR₁ : ∀ d a b : Idx, nablaRic₁ t x d a b =
      component0S (I := I) (hframe.toBasisAt hx)
        (metricNabla0S (I := I) (g₁ t) Ric₁ x)
        (fun s : Fin 3 => if s = 0 then d else if s = 1 then a else b))
    (hNR₂ : ∀ d a b : Idx, nablaRic₂ t x d a b =
      component0S (I := I) (hframe.toBasisAt hx)
        (metricNabla0S (I := I) (g₂ t) Ric₂ x)
        (fun s : Fin 3 => if s = 0 then d else if s = 1 then a else b))
    (hΓ : ∀ i j k : Idx,
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k)
        (christoffelEvolutionRHSInFrame (M := M) gInv₁ nablaRic₁ t x i j k -
          christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ t x i j k) t)
    (hA : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real =>
          CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x Y X)
        ((Adot x Y) X) t)
    (hRF₁ : ∀ (y : M) (X Y : TangentSpace I y),
      HasDerivAt (fun r : Real => (g₁ r).inner y X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) y
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hRF₂ : ∀ (y : M) (X Y : TangentSpace I y),
      HasDerivAt (fun r : Real => (g₂ r).inner y X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₂ t) y
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    {Λric Λ B₁ B₂ B₃ B₄ : Real}
    (hΛric : normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x) ≤ Λric)
    (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v : TangentSpace I x, (g₁ t).inner x v v ≤ Λ * (g₂ t).inner x v v)
    (hB₁ : normSq0S (I := I) (g₁ t) x 3 (metricNabla0S (I := I) (g₂ t) Ric₂ x) ≤ B₁)
    (hB₂ : normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₂ t) Rm₂ x) ≤ B₂)
    (hB₃ : normSq0S (I := I) (g₁ t) x 2 (Ric₂ x) ≤ B₃)
    (hB₄ : normSq0S (I := I) (g₁ t) x 4 (Rm₂ x) ≤ B₄) :
    normSq0S (I := I) (g₁ t) x 3 (connDiffDot (I := I) g₁ g₂ Adot t x) ≤
      8 * Λric * connDiffSq (I := I) (g₁ t) (g₂ t) x +
        2 * (100 * (Module.finrank Real E : Real) ^ 6 *
          (nablaRmDiffSq (I := I) (g₁ t) S x +
            (1 + Λ) ^ 2 * (B₁ + B₂ + B₃ + B₄) *
              (metricDiffSq (I := I) (g₁ t) (g₂ t) x +
                connDiffSq (I := I) (g₁ t) (g₂ t) x))) := by
  refine le_trans (connDiffDot_le_speed (I := I) g₁ g₂ Adot t x hΛric) ?_
  have h := connSpeedLow_normSq_le (I := I) g₁ g₂ Adot frame hframe hu hx S hS
    Ric₁ Ric₂ hRic₁ hRic₂ Rm₂ hRm₂ gInv₁ gInv₂ hgInv₁ hgInv₂ nablaRic₁ nablaRic₂
    hNR₁ hNR₂ hΓ hA hRF₁ hRF₂ hΛ0 hΛ hB₁ hB₂ hB₃ hB₄
  linarith

end MainBound

end DifferentialGeometry.PDE.RicciFlow

end
