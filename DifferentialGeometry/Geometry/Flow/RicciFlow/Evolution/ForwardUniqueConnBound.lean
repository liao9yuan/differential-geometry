import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueConnDot
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRmBounds
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

## The remaining frontier

`connSpeedLow_normSq_le` — the bound on the second summand `|g₁(Adot ·, ·)|²` — is stated with
its honest inputs (the derivative characterisation of `Adot`, the two Ricci-flow equations, the
`S₀₄` realisation, one-sided metric comparison, two named background norms) and is left with an
explicit `sorry`.  Its content is Hamilton's `∂ₜΓ = −g^{-1}(∇Ric + ∇Ric − ∇Ric)` formula for
each flow followed by the contracted-trace rewriting `∇Ric = tr_g(∇Rm)`, which converts the
`∇Ric`-difference into `tr_{g₁}(∇¹S₀₄)` plus `A₀₃`- and `h₀₂`-times-background terms.  The
displayed dimensional constant is provisional: the *shape* of the right-hand side, not the
constant, is the interface.
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

section MainBound

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

/-- **FRONTIER — the remaining half of K1C-b (`sorry`).**

The lowered invariant speed of the connection difference is controlled by the `∇¹S₀₄` carrier
together with the two zeroth-order carriers times background norms:

`|g₁(∂ₜ(∇¹−∇²)·, ·)|²_{g₁} ≤ C(n)·(|∇¹S₀₄|² + (1+Λ)²(B₁+B₂)(|h₀₂|² + |A₀₃|²))`.

All hypotheses are honest inputs, not restatements of the conclusion: `hA` is the derivative
characterisation of `Adot` already used by `connDiffLow_hasDerivAt`, `hRF₁`/`hRF₂` are the two
Ricci-flow equations, `hS`/`hRic₂`/`hRm₂` pin the supplied background and carrier fields, `hΛ`
is the one-sided metric comparison and `hB₁`/`hB₂` are the two named background norms.

**Missing content, classified.**  This is *missing groundwork/API*, not a mathematical
obstruction: (i) Hamilton's `∂ₜΓ^k_{ij} = −g^{kl}(∇_iR_{jl} + ∇_jR_{il} − ∇_lR_{ij})` is not yet
available as an invariant statement about `CovariantDerivative.difference` on this stack — only
its frame-component form (`Evolution/Connection/Christoffel.lean`) is; (ii) the contracted-trace
rewriting `∇Ric = tr_g(∇Rm)` — pure trace-and-`∇` commutation via `nabla_metricTraceFirstTwo0S`
and `traceNablaShuffle`, *not* second Bianchi (`curvSecondBianchi`,
`Geometry/Curvature/Bianchi.lean`, is proved but is needed only for the divergence form, which
this route avoids) — still needs the slot permutation carrying the trace pair to slots `1,3`.
The splitting `∇¹Ric₁ − ∇²Ric₂ = ∇¹(Ric₁ − Ric₂) + (∇¹−∇²)Ric₂` and the bound on its second
summand are already green here (`nablaRicDiff_split`, `nablaRicDiff_le`), so what is genuinely
left is (i) plus the contracted trace `∇¹(Ric₁ − Ric₂) = tr_{g₁}(∇¹S₀₄) + O(|h₀₂|+|A₀₃|)·bg`.
The displayed constant is provisional. -/
theorem connSpeedLow_normSq_le
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    {t : Real} (x : M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (hS : IsRmDiffField (I := I) (g₁ t) (g₂ t) S)
    (Ric₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hRic₂ : ∀ y : M, Ric₂ y = metricRicciAt (I := I) (g₂ t) y)
    (Rm₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (hRm₂ : ∀ y : M, Rm₂ y =
      DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
        (I := I) (g₁ t) (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)) y)
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
    {Λ B₁ B₂ : Real} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v : TangentSpace I x, (g₁ t).inner x v v ≤ Λ * (g₂ t).inner x v v)
    (hB₁ : normSq0S (I := I) (g₁ t) x 3 (metricNabla0S (I := I) (g₂ t) Ric₂ x) ≤ B₁)
    (hB₂ : normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₂ t) Rm₂ x) ≤ B₂) :
    normSq0S (I := I) (g₁ t) x 3
        (lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x) (Adot x)) ≤
      9 * (Module.finrank Real E : Real) ^ 6 *
        (nablaRmDiffSq (I := I) (g₁ t) S x +
          (1 + Λ) ^ 2 * (B₁ + B₂) *
            (metricDiffSq (I := I) (g₁ t) (g₂ t) x +
              connDiffSq (I := I) (g₁ t) (g₂ t) x)) := by
  sorry

/-- **K1C-b, the ruling's bound on `|∂ₜA₀₃|²`.**  The speed of the connection-difference
carrier is controlled pointwise by the three difference carriers and the `∇¹S₀₄` integrand,
with all background norms (`Λric`, `Λ`, `B₁`, `B₂`) as named hypothesis arguments.  This is the
statement `forwardUniqueRate_le` consumes; it is proved from `connDiffDot_le_speed` (green) and
`connSpeedLow_normSq_le` (the remaining frontier). -/
theorem connDiffDot_normSq_le
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    {t : Real} (x : M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (hS : IsRmDiffField (I := I) (g₁ t) (g₂ t) S)
    (Ric₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hRic₂ : ∀ y : M, Ric₂ y = metricRicciAt (I := I) (g₂ t) y)
    (Rm₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (hRm₂ : ∀ y : M, Rm₂ y =
      DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
        (I := I) (g₁ t) (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)) y)
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
    {Λric Λ B₁ B₂ : Real}
    (hΛric : normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x) ≤ Λric)
    (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v : TangentSpace I x, (g₁ t).inner x v v ≤ Λ * (g₂ t).inner x v v)
    (hB₁ : normSq0S (I := I) (g₁ t) x 3 (metricNabla0S (I := I) (g₂ t) Ric₂ x) ≤ B₁)
    (hB₂ : normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₂ t) Rm₂ x) ≤ B₂) :
    normSq0S (I := I) (g₁ t) x 3 (connDiffDot (I := I) g₁ g₂ Adot t x) ≤
      8 * Λric * connDiffSq (I := I) (g₁ t) (g₂ t) x +
        2 * (9 * (Module.finrank Real E : Real) ^ 6 *
          (nablaRmDiffSq (I := I) (g₁ t) S x +
            (1 + Λ) ^ 2 * (B₁ + B₂) *
              (metricDiffSq (I := I) (g₁ t) (g₂ t) x +
                connDiffSq (I := I) (g₁ t) (g₂ t) x))) := by
  refine le_trans (connDiffDot_le_speed (I := I) g₁ g₂ Adot t x hΛric) ?_
  have h := connSpeedLow_normSq_le (I := I) g₁ g₂ Adot x S hS Ric₂ hRic₂ Rm₂ hRm₂
    hA hRF₁ hRF₂ hΛ0 hΛ hB₁ hB₂
  linarith

end MainBound

end DifferentialGeometry.PDE.RicciFlow

end
