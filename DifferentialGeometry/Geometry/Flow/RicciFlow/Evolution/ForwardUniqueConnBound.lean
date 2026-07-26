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
* the **reaction half of the ruling's estimate** (`connDiffDot_le_speed`) and the capstone
  `connDiffDot_normSq_le` in the ruling's shape, proved from `connSpeedLow_normSq_le`.

Everything in this file is proved; there is no `sorry`.

## The lowering-contraction bound

`lowerBilin_normSq_le` is a single statement discharging *both* gaps (2) and (3) of the K1C-b
classification of `ForwardUniqueConnDot.md`: instead of proving separately that lowering with
`g` is a fibre isometry and that a general `(0,2)` lowering is contractive, it compares the two
lowerings directly,

`|lowerBilin q A|²_g ≤ |q|²_g · |lowerBilin g A|²_g`,

so neither a mixed-variance fibre norm nor `RSLoweringNorm.lowerAllSpace` (whose producer
carries the model-space `[InnerProductSpace ℝ E]` taint) ever enters.  At `q = Ric₁` and
`A = ∇¹ − ∇²` the right-hand factor *is* `connDiffSq`, by `connDiffLow_eq_lower`.

## Hamilton's `∂ₜΓ`

`connSpeedLow_normSq_le` — the bound on the second summand `|g₁(Adot ·, ·)|²` — is Hamilton's
`∂ₜΓ = −g^{-1}(∇Ric + ∇Ric − ∇Ric)` formula for each flow followed by the contracted-trace
rewriting `∇Ric = tr_g(∇Rm)`.

An earlier version of the statement was **false** (it took only `hA` and the two Ricci-flow
equations, which do not determine `Adot`: recovering `∂ₜΓ` from `∂ₜg` needs joint `(t, y)`
regularity).  Ruling R8 repaired it by adding the honest K1 input `hΓ` in
`ChristoffelEvolutionEquationInFrameOn` currency plus a zeroth-order background norm; the
counterexample is the permanent record in `ForwardUniqueConnBound.md`, and
`connSpeedRHS_self` is its machine-checked half.

The proof runs in three layers.  **Layer A**: `coeff_adot_eq` pins the frame coefficients of
`Adot` from `hΓ` by uniqueness of derivatives, `lower_raise_cancel` strips the inverse metric
from each flow's Hamilton term, and `connSpeedLow_eq` splits the lowering into
`g₁(Γ̇₁·,·) − g₂(Γ̇₂·,·) − h₀₂(Γ̇₂·,·)`.  **The Hamilton half**: `lowerHam_eq_perm` /
`hamSum_normSq_le` reduce each flow's term to a slot combination of its own `∇Ric`, and
`nablaRicDiff_trace_le` converts the surviving `∇¹(Ric₁ − Ric₂)` into `|∇¹S₀₄|²` by commuting
`∇` past the metric trace (which is why the two endpoints carry `[I.Boundaryless]`).  **The
`Φ`-defect half**: `lowerBilin_normSq_le` and `lowerBilin_metric_le`, the latter from the
*one-sided* `hΛ`.  Nothing outside this file consumes either endpoint.  The displayed
dimensional constant `200(n⁶+1)` is what the route as written yields; the *shape* of the
right-hand side, not the constant, is the interface.
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

/-- **Slot reindexing is a fibre isometry.**  Rank-uniform form of `normSq0S_domDomCongr`,
obtained by feeding it a `g`-orthonormal frame (whose inverse metric is the identity), so that
callers never have to produce a basis themselves. -/
private theorem normSq0S_reindex (g : SmoothRiemannianMetric I M) {x : M} {s s' : ℕ}
    (e : Fin s ≃ Fin s')
    (N : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    normSq0S (I := I) g x s' (N.domDomCongr e) = normSq0S (I := I) g x s N := by
  classical
  obtain ⟨b, hON⟩ := exists_onFrame (I := I) g x
  exact normSq0S_domDomCongr (I := I) g x b (onFrame_inv (I := I) g b hON) e N

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
by the existing `fluxNormSq_le`.  The remaining `∇¹(Ric₁ − Ric₂)` summand is handled by the
contracted-trace step `nablaRicDiff_trace_le`. -/
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

section TraceCommute

/-- **`∇` passes through the first-two metric trace**, for the Levi-Civita connection of `g`:

`∇(tr_g A) = tr_g (∇A ∘ traceNablaShuffle)`.

This is the field-level `nablaRealizes_metricTraceFirstTwo` transported onto the canonical
`metricNabla0S` by realizer uniqueness; the slot shuffle carries the new derivative slot past
the traced pair.  It holds because `∇g = 0`, and is *not* second Bianchi.

Relocation TODO: the canonical home is `Tensor/RSTensor/MetricTrace/NablaTraceGen.lean`, next
to `nablaRealizes_metricTraceFirstTwo`; it lives here only because that shared file must not be
edited mid-campaign. -/
private theorem nabla_trace_field [I.Boundaryless] {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2)) :
    metricNabla0S (I := I) g
        (DifferentialGeometry.Integral.Connection.metricTraceFirstTwoField
          (I := I) (M := M) g A) =
      DifferentialGeometry.Integral.Connection.metricTraceFirstTwoField (I := I) (M := M) g
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞)
          (DifferentialGeometry.Integral.Connection.traceNablaShuffle s)
          (metricNabla0S (I := I) g A)) := by
  have hcov1 :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) g
  have hmc :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) g
  exact totalNabla0SRealizes_unique
    (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
      (metricCov (I := I) g)
      (DifferentialGeometry.Integral.Connection.metricTraceFirstTwoField
        (I := I) (M := M) g A) _)
    (DifferentialGeometry.Integral.Connection.nablaRealizes_metricTraceFirstTwo
      (I := I) (M := M) (metricCov (I := I) g) hcov1 g hmc A (metricNabla0S (I := I) g A)
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2)
        (metricCov (I := I) g) A _))

/-- The dimensional cost of tracing a shuffled `(0,s+3)` field: `traceNormSq_le` at rank
`s+1`, with the shuffle absorbed by the fibre isometry `normSq0S_domDomCongr`. -/
private theorem traceShuffle_normSq_le {s : ℕ}
    (g : SmoothRiemannianMetric I M) (x : M)
    (N : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2 + 1)) :
    normSq0S (I := I) g x (s + 1)
        (DifferentialGeometry.Integral.Connection.metricTraceFirstTwoField (I := I) (M := M) g
          (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞)
            (DifferentialGeometry.Integral.Connection.traceNablaShuffle s) N) x) ≤
      (Module.finrank Real E : Real) ^ (s + 2 + 1) *
        normSq0S (I := I) g x (s + 2 + 1) (N x) := by
  have hle : normSq0S (I := I) g x (s + 1)
        (DifferentialGeometry.Integral.Connection.metricTraceFirstTwoField (I := I) (M := M) g
          (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞)
            (DifferentialGeometry.Integral.Connection.traceNablaShuffle s) N) x) ≤
      (Module.finrank Real E : Real) ^ (s + 2 + 1) *
        normSq0S (I := I) g x (s + 2 + 1)
          ((MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞)
            (DifferentialGeometry.Integral.Connection.traceNablaShuffle s) N) x) :=
    traceNormSq_le (I := I) (s := s + 1) g x
      ((MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞)
        (DifferentialGeometry.Integral.Connection.traceNablaShuffle s) N) x)
  have hiso : normSq0S (I := I) g x (s + 2 + 1)
        ((MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞)
          (DifferentialGeometry.Integral.Connection.traceNablaShuffle s) N) x) =
      normSq0S (I := I) g x (s + 2 + 1) (N x) :=
    normSq0S_reindex (I := I) g _ (N x)
  rwa [hiso] at hle

/-- **`|∇ tr_g (A∘e)|²_g ≤ n^{s+3}·|∇A|²_g`** for any slot permutation `e`: `∇` commutes with
the trace (`nabla_trace_field`), reindexings are fibre isometries, and the trace itself costs
`traceNormSq_le`. -/
private theorem nablaTracePerm_normSq_le [I.Boundaryless] {s : ℕ}
    (g : SmoothRiemannianMetric I M) (e : Equiv.Perm (Fin (s + 2)))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2)) (x : M) :
    normSq0S (I := I) g x (s + 1)
        (metricNabla0S (I := I) g
          (DifferentialGeometry.Integral.Connection.metricTraceFirstTwoField (I := I) (M := M) g
            (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞) e A)) x) ≤
      (Module.finrank Real E : Real) ^ (s + 2 + 1) *
        normSq0S (I := I) g x (s + 2 + 1) (metricNabla0S (I := I) g A x) := by
  have hna : metricNabla0S (I := I) g
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) e A) x =
      ContinuousMultilinearMap.domDomCongr (frontExtendEquiv e)
        (metricNabla0S (I := I) g A x) :=
    totalNabla0SFun_domDomCongr (I := I) (metricCov (I := I) g) e A x
  have hiso : normSq0S (I := I) g x (s + 2 + 1)
        (metricNabla0S (I := I) g
          (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞) e A) x) =
      normSq0S (I := I) g x (s + 2 + 1) (metricNabla0S (I := I) g A x) := by
    rw [hna]
    exact normSq0S_reindex (I := I) g _ (metricNabla0S (I := I) g A x)
  rw [nabla_trace_field (I := I) g
    (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (∞ : WithTop ℕ∞) e A)]
  refine le_trans (traceShuffle_normSq_le (I := I) g x
    (metricNabla0S (I := I) g
      (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞) e A))) ?_
  exact le_of_eq (by rw [hiso])

/-- **The contracted trace: `|∇¹(Ric₁ − Ric₂)|²_{g₁} ≤ n⁵·|∇¹S₀₄|²_{g₁}`.**

`ricciDiff_eq_trace` (`Evolution/ForwardUniqueRatePro.lean`) identifies the Ricci difference
with the `g₁`-trace of the reindexed Kotschwar carrier — both flows lowered *and* traced with
`g₁`, so there is no residual `h₀₂` term — and that identity upgrades from points to bundled
fields by `DFunLike.ext`.  Differentiating it commutes `∇¹` past the trace, which costs only
the dimensional factor `n⁵ = n^{3+2}` of `traceNormSq_le`.  This is the analytic content that
`connSpeedLow_normSq_le` consumes; it needs `[I.Boundaryless]`, inherited from
`nabla_metricTraceFirstTwo0S`. -/
theorem nablaRicDiff_trace_le [I.Boundaryless]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (hS : IsRmDiffField (I := I) g₁ g₂ S)
    (Ric₁ Ric₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hRic₁ : ∀ y : M, Ric₁ y = metricRicciAt (I := I) g₁ y)
    (hRic₂ : ∀ y : M, Ric₂ y = metricRicciAt (I := I) g₂ y)
    (x : M) :
    normSq0S (I := I) g₁ x 3 (metricNabla0S (I := I) g₁ (Ric₁ - Ric₂) x) ≤
      (Module.finrank Real E : Real) ^ 5 * nablaRmDiffSq (I := I) g₁ S x := by
  have hfield : Ric₁ - Ric₂ =
      DifferentialGeometry.Integral.Connection.metricTraceFirstTwoField (I := I) (M := M) g₁
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) rm04TraceSlots S) := by
    refine DFunLike.ext _ _ fun y => ?_
    have hsub : (Ric₁ - Ric₂) y = Ric₁ y - Ric₂ y := rfl
    rw [hsub, hRic₁ y, hRic₂ y, ricciDiff_eq_trace (I := I) g₁ g₂ y, ← hS y]
    rfl
  rw [hfield]
  exact nablaTracePerm_normSq_le (I := I) (s := 2) g₁ rm04TraceSlots S x

end TraceCommute

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

/-- **The own-metric lowering of K1's raised Hamilton right-hand side is the lowered one.**
Combining `lower_raise_cancel` with `bilinOfComp_basis`: the frame components of `g(Γ̇ ·, ·)`,
where `Γ̇` carries K1's components `∑ₗ gInv^{ml}·L_{ijl}`, are exactly `L_{ijk}` — no inverse
metric survives. -/
theorem lowerHamRHS_comp [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (b : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x b gInv)
    (L : Idx -> Idx -> Idx -> Real) (i j k : Idx) :
    component0S (I := I) b
        (lowerBilin (I := I) (metricTensorField (I := I) g x)
          (bilinOfComp (I := I) b (fun i' j' m => ∑ l : Idx, gInv m l * L i' j' l)))
        (fun s : Fin 3 => if s = 0 then i else if s = 1 then j else k) =
      L i j k := by
  classical
  rw [comp_lowerBilin (I := I) b _ (bilinOfComp (I := I) b
      (fun i' j' m => ∑ l : Idx, gInv m l * L i' j' l)) i j k,
    tensor02_expand (I := I) (metricTensorField (I := I) g x) b _ (b k)]
  have hterm : ∀ m : Idx,
      b.repr ((bilinOfComp (I := I) b
          (fun i' j' m' => ∑ l : Idx, gInv m' l * L i' j' l) (b j)) (b i)) m *
        metricTensorField (I := I) g x (fun a : Fin 2 => if a = 0 then b m else b k) =
      (∑ l : Idx, gInv m l * L i j l) * g.inner x (b m) (b k) := by
    intro m
    have hg : metricTensorField (I := I) g x
        (fun a : Fin 2 => if a = 0 then b m else b k) = g.inner x (b m) (b k) := by
      rw [metricTensorField_apply]; simp
    rw [repr_bilinOfComp (I := I) b
      (fun i' j' m' => ∑ l : Idx, gInv m' l * L i' j' l) i j m, hg]
  rw [Finset.sum_congr rfl fun m _ => hterm m]
  exact lower_raise_cancel (I := I) g b gInv hinv (fun l => L i j l) k

/-- Slot permutation `(i, j, k) ↦ (k, i, j)` of `Fin 3`: the third summand of Hamilton's
lowered right-hand side reads `∇_k Ric_{ij}`. -/
private def hamPerm : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide
  right_inv := by decide

/-- **Hamilton's three-term slot combination** of a `(0,3)` tensor `N` (thought of as `∇Ric`
with the derivative slot first):

`hamSum N = −N − N∘(0 1) + N∘(i,j,k ↦ k,i,j)`.

Naming the combination is what keeps the `Tensor0SSpace` module instances in play: written
inline, the `domDomCongr` summands elaborate as bare `ContinuousMultilinearMap`s and the `+`
fails to resolve. -/
def perm3 (e : Equiv.Perm (Fin 3))
    (N : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  N.domDomCongr e

@[simp] theorem perm3_apply (e : Equiv.Perm (Fin 3))
    (N : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (v : Fin 3 -> TangentSpace I x) :
    perm3 (I := I) e N v = N (fun a : Fin 3 => v (e a)) :=
  Tensor0SSpace.domDomCongr_apply (I := I) e N v

theorem normSq0S_perm3 (g : SmoothRiemannianMetric I M) (e : Equiv.Perm (Fin 3))
    (N : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    normSq0S (I := I) g x 3 (perm3 (I := I) e N) = normSq0S (I := I) g x 3 N :=
  normSq0S_reindex (I := I) g e N

def hamSum (N : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  (-1 : Real) • N + (-1 : Real) • perm3 (I := I) (Equiv.swap (0 : Fin 3) 1) N +
    perm3 (I := I) hamPerm N

/-- **Hamilton's lowered right-hand side is the slot combination `hamSum` of `∇Ric`.**  With
`N` the `(0,3)` tensor of `∇Ric` (derivative slot first), `g(Γ̇ ·, ·) = hamSum N`, so the whole
flow-`a` half of K1C-b is a three-term slot combination of a *single* tensor — which is what
makes its fibre norm computable by `normSq0S_domDomCongr`. -/
theorem lowerHam_eq_perm [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (b : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x b gInv)
    (N : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (nr : Idx -> Idx -> Idx -> Real)
    (hnr : ∀ d a c : Idx, nr d a c =
      component0S (I := I) b N
        (fun s : Fin 3 => if s = 0 then d else if s = 1 then a else c)) :
    lowerBilin (I := I) (metricTensorField (I := I) g x)
        (bilinOfComp (I := I) b (fun i j m =>
          ∑ l : Idx, gInv m l * (-nr i j l - nr j i l + nr l i j))) =
      hamSum (I := I) N := by
  classical
  refine tensor0SSpace_ext (𝕜 := Real) 3 x fun w => ?_
  set LHS : ContinuousMultilinearMap Real (fun _ : Fin 3 => TangentSpace I x) Real :=
    lowerBilin (I := I) (metricTensorField (I := I) g x)
      (bilinOfComp (I := I) b (fun i j m =>
        ∑ l : Idx, gInv m l * (-nr i j l - nr j i l + nr l i j))) with hLdef
  set RHS : ContinuousMultilinearMap Real (fun _ : Fin 3 => TangentSpace I x) Real :=
    hamSum (I := I) N with hRdef
  suffices h : LHS.toMultilinearMap = RHS.toMultilinearMap by
    exact congrArg
      (fun T : MultilinearMap Real (fun _ : Fin 3 => TangentSpace I x) Real => T w) h
  refine Module.Basis.ext_multilinear (e := fun _ : Fin 3 => b) ?_
  intro v
  change LHS (fun a : Fin 3 => b (v a)) = RHS (fun a : Fin 3 => b (v a))
  have hLval : LHS (fun a : Fin 3 => b (v a)) =
      -nr (v 0) (v 1) (v 2) - nr (v 1) (v 0) (v 2) + nr (v 2) (v 0) (v 1) := by
    rw [hLdef]
    have h := lowerHamRHS_comp (I := I) g b gInv hinv
      (fun i j l => -nr i j l - nr j i l + nr l i j) (v 0) (v 1) (v 2)
    rw [component0S_apply] at h
    have hslots : (fun a : Fin 3 =>
        b ((fun s : Fin 3 => if s = 0 then v 0 else if s = 1 then v 1 else v 2) a)) =
        fun a : Fin 3 => b (v a) := by
      funext a; fin_cases a <;> simp
    rw [hslots] at h
    exact h
  have hRval : RHS (fun a : Fin 3 => b (v a)) =
      -(N (fun a : Fin 3 => b (v a))) -
        N (fun a : Fin 3 => b (v (Equiv.swap (0 : Fin 3) 1 a))) +
        N (fun a : Fin 3 => b (v (hamPerm a))) := by
    rw [hRdef, hamSum,
      Tensor0SSpace.add_apply (I := I) 3 x _ _ (fun a : Fin 3 => b (v a)),
      Tensor0SSpace.add_apply (I := I) 3 x _ _ (fun a : Fin 3 => b (v a)),
      Tensor0SSpace.smul_apply (I := I) 3 x (-1 : Real) N (fun a : Fin 3 => b (v a)),
      Tensor0SSpace.smul_apply (I := I) 3 x (-1 : Real) _ (fun a : Fin 3 => b (v a))]
    simp only [perm3_apply, smul_eq_mul]
    ring
  rw [hLval, hRval]
  have hcomp : ∀ d a c : Idx, nr d a c =
      N (fun s : Fin 3 => b ((fun s' : Fin 3 =>
        if s' = 0 then d else if s' = 1 then a else c) s)) := by
    intro d a c
    rw [hnr d a c, component0S_apply]
  have h0 : N (fun a : Fin 3 => b (v a)) = nr (v 0) (v 1) (v 2) := by
    rw [hcomp (v 0) (v 1) (v 2)]
    congr 1
    funext a; fin_cases a <;> simp
  have h1 : N (fun a : Fin 3 => b (v (Equiv.swap (0 : Fin 3) 1 a))) =
      nr (v 1) (v 0) (v 2) := by
    rw [hcomp (v 1) (v 0) (v 2)]
    congr 1
    funext a; fin_cases a <;> simp [Equiv.swap_apply_def]
  have h2 : N (fun a : Fin 3 => b (v (hamPerm a))) = nr (v 2) (v 0) (v 1) := by
    rw [hcomp (v 2) (v 0) (v 1)]
    congr 1
    funext a; fin_cases a <;> simp [hamPerm]
  rw [h0, h1, h2]

/-- Slot reindexing is additive, hence so is `hamSum`. -/
theorem perm3_sub (e : Equiv.Perm (Fin 3))
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    perm3 (I := I) e (A - B) = perm3 (I := I) e A - perm3 (I := I) e B :=
  domDomCongr_sub (I := I) e A B

/-- `hamSum` is additive: the two flows' Hamilton terms subtract before the slot combination. -/
theorem hamSum_sub (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    hamSum (I := I) A - hamSum (I := I) B = hamSum (I := I) (A - B) := by
  rw [hamSum, hamSum, hamSum, perm3_sub, perm3_sub]
  module

/-- **The fibre norm of Hamilton's slot combination.**  Three slot-isometric summands, so
`|hamSum N|² ≤ 10·|N|²` by two applications of the `‖a+b‖² ≤ 2‖a‖²+2‖b‖²` kit. -/
theorem hamSum_normSq_le (g : SmoothRiemannianMetric I M)
    (N : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    normSq0S (I := I) g x 3 (hamSum (I := I) N) ≤ 10 * normSq0S (I := I) g x 3 N := by
  have hp1 : normSq0S (I := I) g x 3 (perm3 (I := I) (Equiv.swap (0 : Fin 3) 1) N) =
      normSq0S (I := I) g x 3 N := normSq0S_perm3 (I := I) g _ N
  have hp2 : normSq0S (I := I) g x 3 (perm3 (I := I) hamPerm N) =
      normSq0S (I := I) g x 3 N := normSq0S_perm3 (I := I) g _ N
  have hs1 : normSq0S (I := I) g x 3 ((-1 : Real) • N) = normSq0S (I := I) g x 3 N := by
    rw [normSq0S_smul]; norm_num
  have hs2 : normSq0S (I := I) g x 3
      ((-1 : Real) • perm3 (I := I) (Equiv.swap (0 : Fin 3) 1) N) =
      normSq0S (I := I) g x 3 N := by
    rw [normSq0S_smul, hp1]; norm_num
  have hinner := normSq0S_add_le (I := I) g x 3 ((-1 : Real) • N)
    ((-1 : Real) • perm3 (I := I) (Equiv.swap (0 : Fin 3) 1) N)
  have houter := normSq0S_add_le (I := I) g x 3
    ((-1 : Real) • N + (-1 : Real) • perm3 (I := I) (Equiv.swap (0 : Fin 3) 1) N)
    (perm3 (I := I) hamPerm N)
  rw [hamSum]
  rw [hs1, hs2] at hinner
  linarith [houter, hinner, hp2]

end Hamilton

section MetricCompare

/-- **One-sided metric comparison for a `g₂`-pairing measured in `g₁`.**  If `g₁ ≤ Λ·g₂` then,
in a `g₁`-orthonormal frame, the `g₁`-coordinate energy of a vector is controlled by its
`g₂`-pairings at cost `Λ²`:

`Σₖ g₁(v, eₖ)² ≤ Λ² Σₖ g₂(v, eₖ)²`.

Mechanism: `Σₖ g₁(v, eₖ)² = |v|²_{g₁}` (Parseval), `g₂(v,v)² ≤ |v|²_{g₁}·Σₖ g₂(v, eₖ)²`
(Cauchy–Schwarz on the `g₁`-coordinates) and `|v|²_{g₁} ≤ Λ·g₂(v,v)` (the hypothesis).  Only
the *one-sided* comparison is used. -/
private theorem inner_le_sum_sq {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g₁ g₂ : SmoothRiemannianMetric I M) {x : M}
    (b : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g₁.inner x (b i) (b j) = if i = j then (1 : Real) else 0)
    {Λ : Real} (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    (v : TangentSpace I x) :
    ∑ k : Idx, (g₁.inner x v (b k)) ^ 2 ≤ Λ ^ 2 * ∑ k : Idx, (g₂.inner x v (b k)) ^ 2 := by
  classical
  have hrepr : ∀ k : Idx, b.repr v k = g₁.inner x v (b k) :=
    fun k => repr_inner (I := I) g₁ b hON v k
  -- expansion of any `g`-pairing along the `g₁`-orthonormal coordinates of `v`
  have hpar : ∀ g : SmoothRiemannianMetric I M,
      g.inner x v v = ∑ k : Idx, g₁.inner x v (b k) * g.inner x v (b k) := by
    intro g
    have hv : g.inner x v v =
        metricTensorField (I := I) g x (fun a : Fin 2 => if a = 0 then v else v) := by
      rw [metricTensorField_apply]; simp
    rw [hv, tensor02_expand (I := I) (metricTensorField (I := I) g x) b v v]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hval : metricTensorField (I := I) g x
        (fun a : Fin 2 => if a = 0 then b k else v) = g.inner x (b k) v := by
      rw [metricTensorField_apply]; simp
    rw [hval, g.symm x (b k) v, hrepr k]
  set N : Real := ∑ k : Idx, (g₁.inner x v (b k)) ^ 2 with hNdef
  set Q : Real := ∑ k : Idx, (g₂.inner x v (b k)) ^ 2 with hQdef
  have hN : g₁.inner x v v = N := by
    rw [hpar g₁, hNdef]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hNnn : 0 ≤ N := by rw [hNdef]; positivity
  have hQnn : 0 ≤ Q := by rw [hQdef]; positivity
  have hCS : (g₂.inner x v v) ^ 2 ≤ N * Q := by
    rw [hpar g₂]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun k => g₁.inner x v (b k)) (fun k => g₂.inner x v (b k))
  have hsq : N ^ 2 ≤ Λ ^ 2 * (g₂.inner x v v) ^ 2 := by
    have h := hΛ v
    rw [hN] at h
    nlinarith [mul_self_le_mul_self hNnn h]
  rcases eq_or_lt_of_le hNnn with hN0 | hNpos
  · rw [← hN0]; positivity
  · nlinarith [hsq, hCS, hNpos, sq_nonneg Λ, hQnn]

/-- **The `Φ`-defect bound: raising with `g₂` but measuring in `g₁` costs `Λ²`.**
For any bilinear vector-valued map `A`,

`|g₁(A ·, ·)|²_{g₁} ≤ Λ² · |g₂(A ·, ·)|²_{g₁}`,

under the *one-sided* comparison `g₁ ≤ Λ·g₂`.  This is what makes K1C-b's flow-2 half usable:
`Γ̇₂` is raised with `g₂`'s inverse but has to be measured in `g₁`, and the operator carrying it
across is `Φ = g₂^♯ ∘ g₁^♭`.

**Relocation TODO** — nothing here is Ricci-flow-specific; this is a general fibre-metric
comparison.  Its canonical home is `Tensor/RSTensor/Tensor0SRiemannian/Comparison.lean`, next to
`normSq0S_upper_le_of_equiv`.  It lives here only to avoid editing that shared file mid-campaign
(planner ruling R9(b)). -/
theorem lowerBilin_metric_le (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    {Λ : Real} (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    normSq0S (I := I) g₁ x 3 (lowerBilin (I := I) (metricTensorField (I := I) g₁ x) A) ≤
      Λ ^ 2 * normSq0S (I := I) g₁ x 3
        (lowerBilin (I := I) (metricTensorField (I := I) g₂ x) A) := by
  classical
  obtain ⟨b, hON⟩ := exists_onFrame (I := I) g₁ x
  have hinv := onFrame_inv (I := I) g₁ b hON
  have hexp : ∀ q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x,
      normSq0S (I := I) g₁ x 3 (lowerBilin (I := I) q A) =
        ∑ i : Fin (Module.finrank Real (TangentSpace I x)),
          ∑ j : Fin (Module.finrank Real (TangentSpace I x)),
            ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
              (q (fun a : Fin 2 => if a = 0 then (A (b j)) (b i) else b k)) ^ 2 := by
    intro q
    rw [normSq0S_identity_eq_sum_sq (I := I) g₁ x 3 b hinv, sumSlots3]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [comp_lowerBilin (I := I) b q A i j k]
  have hcomp : ∀ (g : SmoothRiemannianMetric I M) (w : TangentSpace I x)
      (k : Fin (Module.finrank Real (TangentSpace I x))),
      metricTensorField (I := I) g x (fun a : Fin 2 => if a = 0 then w else b k) =
        g.inner x w (b k) := by
    intro g w k
    rw [metricTensorField_apply]; simp
  rw [hexp, hexp, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [hcomp]
  exact inner_le_sum_sq (I := I) g₁ g₂ b hON hΛ ((A (b j)) (b i))

end MetricCompare

section MainBound

/-- **The K1C-b constant bookkeeping, as pure real arithmetic.**  Isolating it from the tensor
expressions keeps `nlinarith` away from the (very large) geometric atoms — inlined, the defeq
checks on those atoms time out.  `E1`/`E2` are the two halves of the split, `X`/`D`/`R2` the
`∇Ric` chain and `L1`/`L2` the `Φ`-defect chain. -/
private theorem connSpeed_arith
    {n P Hm Ac Λ B₁ B₃ E1 E2 X D R2 L1 L2 : Real}
    (hn : 0 ≤ n) (hP : 0 ≤ P) (hHm : 0 ≤ Hm) (hAc : 0 ≤ Ac)
    (hB₁ : 0 ≤ B₁) (hB₃ : 0 ≤ B₃) (hΛ0 : 0 ≤ Λ)
    (hE1 : E1 ≤ 10 * X) (hX : X ≤ 2 * D + 8 * n ^ 3 * Ac * R2)
    (hD : D ≤ n ^ 5 * P) (hR2B : R2 ≤ B₃)
    (hE2 : E2 ≤ Hm * L1) (hL1 : L1 ≤ Λ ^ 2 * L2) (hL2B : L2 ≤ 10 * B₁)
    (hp5 : n ^ 5 ≤ n ^ 6 + 1) (hp3 : n ^ 3 ≤ n ^ 6 + 1) :
    2 * E1 + 2 * E2 ≤
      200 * (n ^ 6 + 1) *
        (P + (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac)) := by
  have hKnn : (0 : Real) ≤ n ^ 6 + 1 := by positivity
  have hK1 : (1 : Real) ≤ n ^ 6 + 1 := by have := pow_nonneg hn 6; linarith
  have hSBnn : (0 : Real) ≤ B₁ + B₃ := by linarith
  have hWnn : (0 : Real) ≤ Hm + Ac := by linarith
  have hQ1 : (1 : Real) ≤ (1 + Λ) ^ 2 := by nlinarith [sq_nonneg Λ]
  have hQnn : (0 : Real) ≤ (1 + Λ) ^ 2 := sq_nonneg _
  -- the common right-hand factor
  have hQ'nn : (0 : Real) ≤ (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac) :=
    mul_nonneg (mul_nonneg hQnn hSBnn) hWnn
  -- the two carrier-monotonicity products
  have hprod1 : Ac * B₃ ≤ (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac) := by
    have h1 : Ac * B₃ ≤ (Hm + Ac) * (B₁ + B₃) :=
      mul_le_mul (by linarith) (by linarith) hB₃ hWnn
    have h2 : (Hm + Ac) * (B₁ + B₃) ≤
        (1 + Λ) ^ 2 * ((Hm + Ac) * (B₁ + B₃)) :=
      le_mul_of_one_le_left (mul_nonneg hWnn hSBnn) hQ1
    have h3 : (1 + Λ) ^ 2 * ((Hm + Ac) * (B₁ + B₃)) =
        (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac) := by ring
    linarith [h3 ▸ h2]
  have hprod2 : Λ ^ 2 * (B₁ * Hm) ≤ (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac) := by
    have hΛ2 : Λ ^ 2 ≤ (1 + Λ) ^ 2 := by nlinarith
    have h1 : B₁ * Hm ≤ (B₁ + B₃) * (Hm + Ac) :=
      mul_le_mul (by linarith) (by linarith) hHm hSBnn
    have h2 : Λ ^ 2 * (B₁ * Hm) ≤ Λ ^ 2 * ((B₁ + B₃) * (Hm + Ac)) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg Λ)
    have h3 : Λ ^ 2 * ((B₁ + B₃) * (Hm + Ac)) ≤
        (1 + Λ) ^ 2 * ((B₁ + B₃) * (Hm + Ac)) :=
      mul_le_mul_of_nonneg_right hΛ2 (mul_nonneg hSBnn hWnn)
    have h4 : (1 + Λ) ^ 2 * ((B₁ + B₃) * (Hm + Ac)) =
        (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac) := by ring
    linarith [h4 ▸ h3]
  -- half one
  have hfl : 8 * n ^ 3 * Ac * R2 ≤ 8 * n ^ 3 * Ac * B₃ :=
    mul_le_mul_of_nonneg_left hR2B (by positivity)
  have hb1 : E1 ≤ 20 * (n ^ 5 * P) + 80 * (n ^ 3 * (Ac * B₃)) := by linarith
  -- half two
  have hb2 : E2 ≤ 10 * (Λ ^ 2 * (B₁ * Hm)) := by
    have hc1 : Λ ^ 2 * L2 ≤ Λ ^ 2 * (10 * B₁) := mul_le_mul_of_nonneg_left hL2B (sq_nonneg Λ)
    have hc2 : Hm * L1 ≤ Hm * (Λ ^ 2 * (10 * B₁)) :=
      mul_le_mul_of_nonneg_left (le_trans hL1 hc1) hHm
    linarith
  -- the three dimensional comparisons
  have hac : (0 : Real) ≤ Ac * B₃ := mul_nonneg hAc hB₃
  have hs1 : 40 * (n ^ 5 * P) ≤ 200 * ((n ^ 6 + 1) * P) := by
    have h1 : n ^ 5 * P ≤ (n ^ 6 + 1) * P := mul_le_mul_of_nonneg_right hp5 hP
    have h2 : (0 : Real) ≤ (n ^ 6 + 1) * P := mul_nonneg hKnn hP
    linarith
  have hs2 : 160 * (n ^ 3 * (Ac * B₃)) ≤
      160 * ((n ^ 6 + 1) * ((1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac))) := by
    have h1 : n ^ 3 * (Ac * B₃) ≤ (n ^ 6 + 1) * (Ac * B₃) :=
      mul_le_mul_of_nonneg_right hp3 hac
    have h2 : (n ^ 6 + 1) * (Ac * B₃) ≤
        (n ^ 6 + 1) * ((1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac)) :=
      mul_le_mul_of_nonneg_left hprod1 hKnn
    linarith
  have hs3 : 20 * (Λ ^ 2 * (B₁ * Hm)) ≤
      40 * ((n ^ 6 + 1) * ((1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac))) := by
    have h1 : Λ ^ 2 * (B₁ * Hm) ≤ (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac) := hprod2
    have h2 : (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac) ≤
        (n ^ 6 + 1) * ((1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac)) :=
      le_mul_of_one_le_left hQ'nn hK1
    have h3 : (0 : Real) ≤ (n ^ 6 + 1) * ((1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac)) :=
      mul_nonneg hKnn hQ'nn
    linarith
  have hexp : 200 * (n ^ 6 + 1) *
        (P + (1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac)) =
      200 * ((n ^ 6 + 1) * P) +
        200 * ((n ^ 6 + 1) * ((1 + Λ) ^ 2 * (B₁ + B₃) * (Hm + Ac))) := by ring
  rw [hexp]
  linarith

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
side is `0` — for *every* value of the background bounds `Λ`, `B₁`, `B₃`.  Companion of
`nablaRmDiffSq_self`, and the formal half of the counterexample recorded in the
`connSpeedLow_normSq_le` docstring. -/
theorem connSpeedRHS_self (g₁ g₂ : Real → SmoothRiemannianMetric I M) {t : Real} (x : M)
    (S : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (hS : IsRmDiffField (I := I) (g₁ t) (g₂ t) S)
    (hg : g₁ t = g₂ t) (Λ B₁ B₃ : Real) :
    200 * ((Module.finrank Real E : Real) ^ 6 + 1) *
        (nablaRmDiffSq (I := I) (g₁ t) S x +
          (1 + Λ) ^ 2 * (B₁ + B₃) *
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

`|g₁(∂ₜ(∇¹−∇²)·, ·)|²_{g₁} ≤ 200(n⁶+1)·(|∇¹S₀₄|² + (1+Λ)²(B₁+B₃)(|h₀₂|² + |A₀₃|²))`.

**Repaired interface (ruling R8).**  An earlier version of this statement took only `hA` and
the two Ricci-flow equations and was *false*: those do not determine `Adot`, because recovering
`∂ₜΓ` from `∂ₜg` interchanges `∂ₜ` with a spatial derivative and so needs joint `(t, y)`
regularity.  The counterexample and the full analysis are the permanent record in
`ForwardUniqueConnBound.md`; `connSpeedRHS_self` above is its machine-checked half.  The repair
adds the honest K1 input `hΓ` — the conclusion of `ChristoffelEvolutionEquationInFrameOn`,
discharged from a solution pair by `christoffelEvolution_of_solution` — with `hA` kept as the
realisation link, plus the zeroth-order background norm `B₃ ≥ |Ric₂|²`.

**Proved, in three layers.**

* **Layer A** — `coeff_adot_eq` pins the frame coefficients of `Adot` by uniqueness of
  derivatives against `hΓ`, and `connSpeedLow_eq` splits the lowering into
  `g₁(Γ̇₁·,·) − g₂(Γ̇₂·,·) − h₀₂(Γ̇₂·,·)`, each Hamilton term lowered by *its own* metric.
* **the Hamilton half** — `lower_raise_cancel` strips the inverse metric from each Hamilton
  term, `lowerHam_eq_perm` identifies it with `hamSum (∇Ric)`, `hamSum_sub` subtracts the two
  flows before the slot combination and `hamSum_normSq_le` costs a factor `10`
  (`normSq0S_perm3` makes each slot summand isometric).  `nablaRicDiff_le` then splits off
  `8n³·|A₀₃|²·|Ric₂|²` — this is what `B₃` is for — and `nablaRicDiff_trace_le` converts the
  surviving `∇¹(Ric₁ − Ric₂)` into `n⁵·|∇¹S₀₄|²`.  That last step is where `[I.Boundaryless]`
  enters: it commutes `∇` past the metric trace, which is pure metric compatibility and *not*
  second Bianchi.
* **the `Φ`-defect half** — `lowerBilin_normSq_le` gives `|h₀₂(Γ̇₂·,·)|² ≤ |h₀₂|²·|g₁(Γ̇₂·,·)|²`
  and `lowerBilin_metric_le` gives `|g₁(Γ̇₂·,·)|²_{g₁} ≤ Λ²·|g₂(Γ̇₂·,·)|²_{g₁}` from the
  *one-sided* `hΛ`.

`connSpeed_arith` does the constant bookkeeping as pure real arithmetic, so that `nlinarith`
never meets the (very large) tensor atoms.  The input list is exactly what the proof consumes
(ruling R9(c)): the two Ricci-flow equations, `Rm₂` and the background norms `B₂ ≥ |∇²Rm₂|²`,
`B₄ ≥ |Rm₂|²` were dropped, since Hamilton's formula reaches `Adot` through `hΓ` alone and the
trace step produces no `Rm₂` term.  The constant `200(n⁶+1)` is what the route yields; the
`+1` removes the `finrank = 0` case split at no mathematical cost. -/
theorem connSpeedLow_normSq_le [I.Boundaryless]
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
    {Λ B₁ B₃ : Real} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v : TangentSpace I x, (g₁ t).inner x v v ≤ Λ * (g₂ t).inner x v v)
    (hB₁ : normSq0S (I := I) (g₁ t) x 3 (metricNabla0S (I := I) (g₂ t) Ric₂ x) ≤ B₁)
    (hB₃ : normSq0S (I := I) (g₁ t) x 2 (Ric₂ x) ≤ B₃) :
    normSq0S (I := I) (g₁ t) x 3
        (lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x) (Adot x)) ≤
      200 * ((Module.finrank Real E : Real) ^ 6 + 1) *
        (nablaRmDiffSq (I := I) (g₁ t) S x +
          (1 + Λ) ^ 2 * (B₁ + B₃) *
            (metricDiffSq (I := I) (g₁ t) (g₂ t) x +
              connDiffSq (I := I) (g₁ t) (g₂ t) x)) := by
  classical
  -- Layer A: Hamilton's `∂ₜΓ` reaches `Adot` and splits off the single `h₀₂`-defect.
  rw [connSpeedLow_eq (I := I) g₁ g₂ frame hframe hu hx Adot hA
    (fun i j k => christoffelEvolutionRHSInFrame (M := M) gInv₁ nablaRic₁ t x i j k)
    (fun i j k => christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ t x i j k) hΓ]
  refine le_trans (normSq0S_sub_le (I := I) (g₁ t) x 3 _ _) ?_
  -- each flow's Hamilton term is `hamSum` of that flow's `∇Ric`
  have hT₁ : lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x)
      (bilinOfComp (I := I) (hframe.toBasisAt hx)
        (fun i j k => christoffelEvolutionRHSInFrame (M := M) gInv₁ nablaRic₁ t x i j k)) =
      hamSum (I := I) (metricNabla0S (I := I) (g₁ t) Ric₁ x) :=
    lowerHam_eq_perm (I := I) (g₁ t) (hframe.toBasisAt hx) (fun i j => gInv₁ t x i j) hgInv₁
      (metricNabla0S (I := I) (g₁ t) Ric₁ x) (fun d a c => nablaRic₁ t x d a c) hNR₁
  have hT₂ : lowerBilin (I := I) (metricTensorField (I := I) (g₂ t) x)
      (bilinOfComp (I := I) (hframe.toBasisAt hx)
        (fun i j k => christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ t x i j k)) =
      hamSum (I := I) (metricNabla0S (I := I) (g₂ t) Ric₂ x) :=
    lowerHam_eq_perm (I := I) (g₂ t) (hframe.toBasisAt hx) (fun i j => gInv₂ t x i j) hgInv₂
      (metricNabla0S (I := I) (g₂ t) Ric₂ x) (fun d a c => nablaRic₂ t x d a c) hNR₂
  rw [hT₁, hT₂, hamSum_sub]
  -- ## the `T₁ − T₂` half
  have hham := hamSum_normSq_le (I := I) (g₁ t)
    (metricNabla0S (I := I) (g₁ t) Ric₁ x - metricNabla0S (I := I) (g₂ t) Ric₂ x)
  have hpt : metricNabla0S (I := I) (g₁ t) Ric₁ x - metricNabla0S (I := I) (g₂ t) Ric₂ x =
      (metricNabla0S (I := I) (g₁ t) Ric₁ - metricNabla0S (I := I) (g₂ t) Ric₂) x := rfl
  rw [hpt] at hham
  have hsplit := nablaRicDiff_le (I := I) (g₁ t) (g₂ t) Ric₁ Ric₂ x
  -- ## the `Φ`-defect half
  have hd1 := lowerBilin_normSq_le (I := I) (g₁ t) x
    (metricDiffAt (I := I) (g₁ t) (g₂ t) x)
    (bilinOfComp (I := I) (hframe.toBasisAt hx)
      (fun i j k => christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ t x i j k))
  have hd2 := lowerBilin_metric_le (I := I) (g₁ t) (g₂ t) x hΛ
    (bilinOfComp (I := I) (hframe.toBasisAt hx)
      (fun i j k => christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ t x i j k))
  have hd3 : normSq0S (I := I) (g₁ t) x 3
      (lowerBilin (I := I) (metricTensorField (I := I) (g₂ t) x)
        (bilinOfComp (I := I) (hframe.toBasisAt hx)
          (fun i j k => christoffelEvolutionRHSInFrame (M := M) gInv₂ nablaRic₂ t x i j k)))
      ≤ 10 * B₁ := by
    rw [hT₂]
    exact le_trans (hamSum_normSq_le (I := I) (g₁ t) _) (by linarith)
  rw [← metricDiffSq_def (I := I) (g₁ t) (g₂ t) x] at hd1
  -- ## the contracted trace
  have htrace := nablaRicDiff_trace_le (I := I) (g₁ t) (g₂ t) S hS Ric₁ Ric₂ hRic₁ hRic₂ x
  -- ## nonnegativity bookkeeping
  have hnnn : (0 : Real) ≤ (Module.finrank Real E : Real) := by positivity
  have hpow : ∀ a : ℕ, a ≤ 6 →
      (Module.finrank Real E : Real) ^ a ≤ (Module.finrank Real E : Real) ^ 6 + 1 := by
    intro a ha
    rcases Nat.eq_zero_or_pos (Module.finrank Real E) with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero]
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · rw [ha0]; norm_num
      · rw [zero_pow (by omega : a ≠ 0)]; norm_num
    · have hn1 : (1 : Real) ≤ (Module.finrank Real E : Real) := by exact_mod_cast hpos
      have := pow_le_pow_right₀ hn1 ha
      linarith
  exact connSpeed_arith hnnn (nablaRmDiffSq_nonneg (I := I) (g₁ t) S x)
    (normSq0S_nonneg (I := I) (g₁ t) x 2 _) (normSq0S_nonneg (I := I) (g₁ t) x 3 _)
    (le_trans (normSq0S_nonneg (I := I) (g₁ t) x 3 _) hB₁)
    (le_trans (normSq0S_nonneg (I := I) (g₁ t) x 2 _) hB₃) hΛ0
    hham hsplit htrace hB₃ hd1 hd2 hd3 (hpow 5 (by norm_num)) (hpow 3 (by norm_num))

/-- **K1C-b, the ruling's bound on `|∂ₜA₀₃|²`.**  The speed of the connection-difference
carrier is controlled pointwise by the three difference carriers and the `∇¹S₀₄` integrand,
with the background norms (`Λric ≥ |Ric₁|²`, `Λ` for `g₁ ≤ Λg₂`, `B₁ ≥ |∇²Ric₂|²`,
`B₃ ≥ |Ric₂|²`) as named hypothesis arguments.  This is the statement `forwardUniqueRate_le` is
meant to consume; it is proved from `connDiffDot_le_speed` and `connSpeedLow_normSq_le` and
carries the latter's input list — the K1 Hamilton input `hΓ` and the two background norms —
together with its `[I.Boundaryless]`.  Downstream wiring (`adotLe`) absorbs `B₃` into the slab
constants. -/
theorem connDiffDot_normSq_le [I.Boundaryless]
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
    {Λric Λ B₁ B₃ : Real}
    (hΛric : normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x) ≤ Λric)
    (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v : TangentSpace I x, (g₁ t).inner x v v ≤ Λ * (g₂ t).inner x v v)
    (hB₁ : normSq0S (I := I) (g₁ t) x 3 (metricNabla0S (I := I) (g₂ t) Ric₂ x) ≤ B₁)
    (hB₃ : normSq0S (I := I) (g₁ t) x 2 (Ric₂ x) ≤ B₃) :
    normSq0S (I := I) (g₁ t) x 3 (connDiffDot (I := I) g₁ g₂ Adot t x) ≤
      8 * Λric * connDiffSq (I := I) (g₁ t) (g₂ t) x +
        2 * (200 * ((Module.finrank Real E : Real) ^ 6 + 1) *
          (nablaRmDiffSq (I := I) (g₁ t) S x +
            (1 + Λ) ^ 2 * (B₁ + B₃) *
              (metricDiffSq (I := I) (g₁ t) (g₂ t) x +
                connDiffSq (I := I) (g₁ t) (g₂ t) x))) := by
  refine le_trans (connDiffDot_le_speed (I := I) g₁ g₂ Adot t x hΛric) ?_
  have h := connSpeedLow_normSq_le (I := I) g₁ g₂ Adot frame hframe hu hx S hS
    Ric₁ Ric₂ hRic₁ hRic₂ gInv₁ gInv₂ hgInv₁ hgInv₂ nablaRic₁ nablaRic₂
    hNR₁ hNR₂ hΓ hA hΛ0 hΛ hB₁ hB₃
  linarith

end MainBound

end DifferentialGeometry.PDE.RicciFlow

end
