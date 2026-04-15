import DifferentialGeometry.Synthetic.Operator.Gradient
import DifferentialGeometry.Synthetic.Operator.Laplacian
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Spatial Constants
-/

open SyntheticTensor

section SpatialConstant

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- A scalar c is spatially constant if X(c) = 0 for all vector fields X. -/
def IsSpatialConstant (emb : DerivationEmbedding k R V) (c : R) : Prop :=
  ∀ X : V, action emb X c = 0

lemma grad_zero_of_const
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V) 
    (c : R) (hc : IsSpatialConstant emb c) :
    grad emb met c = 0 := by
  apply met.eq_of_forall_g_eq; intro X
  change met.g (grad emb met c) X = met.g 0 X
  rw [g_grad]
  have h0 : met.g (0 : V) X = 0 := by
    have := met.g_smul_left 0 (0 : V) X; simp only [zero_smul, zero_mul] at this; exact this
  rw [h0]; exact hc X

lemma grad_smul_const
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V) 
    (c f : R) (hc : IsSpatialConstant emb c) :
    grad emb met (c * f) = c • grad emb met f := by
  apply met.eq_of_forall_g_eq; intro X
  change met.g (grad emb met (c * f)) X = met.g (c • grad emb met f) X
  rw [g_grad, met.g_smul_left, g_grad, action_smul_right, hc X, zero_mul, zero_add]

/-- Δc = 0 for spatial constant c. -/
lemma laplacian_zero_of_const
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V) 
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (c : R) (hc : IsSpatialConstant emb c) :
    laplacian emb met atr conn ha hl conn_add_left conn_smul_left c = 0 := by
  -- grad c = 0, so hessianForm c = lower_index(cov_diff(0)) = lower_index(0) = 0
  -- Then metric_trace(0) = 0.
  have h_grad_c : grad emb met c = 0 := grad_zero_of_const emb met c hc
  -- laplacian 0 = 0 (by linearity)
  have h_lap_0 : laplacian emb met atr conn ha hl conn_add_left conn_smul_left 0 = 0 := by
    have h_sub := laplacian_sub emb met atr conn ha hl conn_add_left conn_smul_left 0 0
    simp only [sub_self] at h_sub; exact h_sub
  -- laplacian c depends only on grad c, so laplacian c = laplacian 0 when grad c = grad 0 = 0
  -- More precisely: hessianForm c uses grad c, which is 0.
  -- grad 0 = 0 as well (0 is spatially constant).
  have hc0 : IsSpatialConstant emb (0 : R) := fun X => action_zero_right emb X
  have h_grad_0 : grad emb met 0 = 0 := grad_zero_of_const emb met 0 hc0
  -- hessianForm u depends on grad u through covariant_differential(grad u)
  -- If grad c = 0 = grad 0, then hessianForm c = hessianForm 0 definitionally? No, not directly.
  -- But: laplacian c = metric_trace(lower_index(cov_diff(grad c)))
  -- = metric_trace(lower_index(cov_diff(0))) since grad c = 0
  -- = metric_trace(lower_index(cov_diff(grad 0))) since grad 0 = 0
  -- = laplacian 0 = 0
  change (metric_trace met atr (0 : Fin 2) (0 : Fin 1)
    (hessianForm emb met atr conn ha hl conn_add_left conn_smul_left c)) ![] ![] = 0
  rw [show hessianForm emb met atr conn ha hl conn_add_left conn_smul_left c =
      hessianForm emb met atr conn ha hl conn_add_left conn_smul_left 0 from by
    simp only [hessianForm, h_grad_c, h_grad_0]]
  exact h_lap_0

/-- Δ(c*f) = c * Δf for spatial constant c. -/
lemma laplacian_const_smul
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V) 
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (c f : R) (hc : IsSpatialConstant emb c) :
    laplacian emb met atr conn ha hl conn_add_left conn_smul_left (c * f) =
    c * laplacian emb met atr conn ha hl conn_add_left conn_smul_left f :=
  laplacian_smul emb met atr conn ha hl conn_add_left conn_smul_left c f hc

end SpatialConstant
