import DifferentialGeometry.Synthetic.Operator.Hessian
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Laplacian Operator
-/

open BigOperators
open SyntheticTensor

section LaplacianHelpers

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

end LaplacianHelpers

section Laplacian

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Laplacian of a function defined as the metric trace of its Hessian tensor form. -/
noncomputable def laplacian
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V) 
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (u : R) : R :=
  (metric_trace met atr (0 : Fin 2) (0 : Fin 1)
    (hessianForm emb met atr conn ha hl conn_add_left conn_smul_left u)) ![] ![]

/-- Δ(f+g) = Δf + Δg -/
lemma laplacian_add
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V) 
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (f g : R) :
    laplacian emb met atr conn ha hl conn_add_left conn_smul_left (f + g) =
    laplacian emb met atr conn ha hl conn_add_left conn_smul_left f +
    laplacian emb met atr conn ha hl conn_add_left conn_smul_left g := by
  simp only [laplacian, hessianForm_add, metric_trace_add, MultilinearMap.add_apply]

/-- Δ(f-g) = Δf - Δg -/
lemma laplacian_sub
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V) 
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (f g : R) :
    laplacian emb met atr conn ha hl conn_add_left conn_smul_left (f - g) =
    laplacian emb met atr conn ha hl conn_add_left conn_smul_left f -
    laplacian emb met atr conn ha hl conn_add_left conn_smul_left g := by
  have hsub : f - g = f + (-1) * g := by ring
  rw [hsub, laplacian_add]
  have hc : ∀ X : V, action emb X (-1 : R) = 0 := by
    intro X; rw [show (-1 : R) = -1 from rfl, action_neg_right, action_one]; ring
  have hz : laplacian emb met atr conn ha hl conn_add_left conn_smul_left ((-1) * g) =
      (-1) * laplacian emb met atr conn ha hl conn_add_left conn_smul_left g := by
    simp only [laplacian, hessianForm_smul emb met atr conn ha hl conn_add_left conn_smul_left (-1) g hc,
               metric_trace_smul, MultilinearMap.smul_apply, smul_eq_mul]
  rw [hz]; ring

/-- Δ(c*f) = c * Δf for spatial constant c -/
lemma laplacian_smul
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V) 
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (c f : R) (hc : ∀ X : V, action emb X c = 0) :
    laplacian emb met atr conn ha hl conn_add_left conn_smul_left (c * f) =
    c * laplacian emb met atr conn ha hl conn_add_left conn_smul_left f := by
  simp only [laplacian, hessianForm_smul emb met atr conn ha hl conn_add_left conn_smul_left c f hc,
             metric_trace_smul, MultilinearMap.smul_apply, smul_eq_mul]

/-- Second covariant derivative of tensors. -/
noncomputable def SecondCovDerivTensor
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    {r s : ℕ} (T : TensorData R V r s) (X Y : V) : TensorData R V r s :=
  let nXY_T := genericCovDeriv emb conn ha hl (conn X Y) T
  let nY_T := genericCovDeriv emb conn ha hl Y T
  let nX_nY_T := genericCovDeriv emb conn ha hl X nY_T
  nX_nY_T + (-1 : R) • nXY_T

/-- Bochner product rule for the rough Laplacian of a tensor norm.

For a time-slice tensor `T`, this is the abstract scalar identity
`Delta |T|^2 = 2 <roughDelta T, T> + 2 |nabla T|^2`.

The current synthetic Laplacian file has scalar linearity and second covariant
derivatives, but not yet the full tensor-inner-product expansion. This named
property is the reusable D target; concrete tensor-calculus proofs should
discharge it here rather than threading an anonymous `h_lap_component` through
Ricci-flow files. -/
def TensorNormLaplacianProductRule
    (lapNormSq roughLapInner covDerivNormSq : R) : Prop :=
  lapNormSq = 2 * roughLapInner + 2 * covDerivNormSq

/-- Consume the named tensor-norm Bochner product rule. -/
theorem tensor_norm_laplacian_eq_of_product_rule
    (lapNormSq roughLapInner covDerivNormSq : R)
    (h : TensorNormLaplacianProductRule lapNormSq roughLapInner covDerivNormSq) :
    lapNormSq = 2 * roughLapInner + 2 * covDerivNormSq :=
  h

/-- Coordinate Bochner reduction for the rough Laplacian of a tensor norm.

This is the finite-frame form of the standard computation

`Delta |T|^2 = 2 <roughDelta T, T> + 2 |nabla T|^2`.

The proof assumes the realization has already identified the three scalar
quantities with their coordinate traces:

* `lapNormSq` is the trace of the second derivative of the component norm,
  expanded by the scalar product rule;
* `roughLapInner` is the trace of `(roughDelta T)` paired with `T`;
* `covDerivNormSq` is the trace of the squared first covariant derivative.

Once those identifications are in this coordinate shape, the Bochner identity
is just distributivity over finite sums. -/
theorem tensorNormLaplacianProductRule_of_coordinate_bochner_sum
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (lapNormSq roughLapInner covDerivNormSq : R)
    (second first : κ -> ι -> R) (component : ι -> R)
    (h_lap : lapNormSq =
      ∑ a : κ, ∑ I : ι,
        (2 * second a I * component I + 2 * first a I * first a I))
    (h_rough : roughLapInner =
      ∑ a : κ, ∑ I : ι, second a I * component I)
    (h_cov : covDerivNormSq =
      ∑ a : κ, ∑ I : ι, first a I * first a I) :
    TensorNormLaplacianProductRule lapNormSq roughLapInner covDerivNormSq := by
  unfold TensorNormLaplacianProductRule
  rw [h_lap, h_rough, h_cov]
  have hrough :
      (∑ a : κ, ∑ I : ι, 2 * (second a I * component I)) =
        2 * (∑ a : κ, ∑ I : ι, second a I * component I) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  have hcov :
      (∑ a : κ, ∑ I : ι, 2 * (first a I * first a I)) =
        2 * (∑ a : κ, ∑ I : ι, first a I * first a I) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  rw [← hrough, ← hcov]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I _
  ring

end Laplacian
