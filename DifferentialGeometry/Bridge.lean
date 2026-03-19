import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Geometry.Connection

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Bridge: Connecting Analytic and Synthetic Geometry
-/

namespace DifferentialGeometry.Bridge

open AbstractDerivationAction

variable (R : Type) [CommRing R]
variable (V : Type) [AddCommGroup V] [Module R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V]

/--
General tensor calculus.
`r` is contravariant rank, `s` is covariant rank.
-/
class AbstractTensorCalculus (metric : AbstractMetricTensor R V) (conn : AbstractLeviCivitaConnection metric) where
  /-- Generic graded tensor type (r: contravariant, s: covariant) -/
  AbstractTensor : ℕ → ℕ → Type

  add {r s : ℕ} : AbstractTensor r s → AbstractTensor r s → AbstractTensor r s
  smul {r s : ℕ} : R → AbstractTensor r s → AbstractTensor r s
  tensor_prod {r1 s1 r2 s2 : ℕ} : AbstractTensor r1 s1 → AbstractTensor r2 s2 → AbstractTensor (r1 + r2) (s1 + s2)

  -- Embedding
  fromScalar : R → AbstractTensor 0 0
  fromVector : V → AbstractTensor 1 0

  -- Covariant Derivative
  nabla_tensor {r s : ℕ} : V → AbstractTensor r s → AbstractTensor r s

  /-- Interior product (contraction with a tangent vector) -/
  interior_product {s : ℕ} : AbstractTensor 0 (s + 1) → V → AbstractTensor 0 s

  /-- Covariant contraction (feeding a vector into a mixed tensor) -/
  contract_covariant {r s : ℕ} : AbstractTensor r (s + 1) → V → AbstractTensor r s

  /-- General contraction between one contravariant and one covariant slot -/
  contract {r s : ℕ} : AbstractTensor (r + 1) (s + 1) → AbstractTensor r s

  /-- Metric trace: contracting two covariant indices using the metric tensor -/
  metric_contract {r s : ℕ} : AbstractTensor r (s + 2) → AbstractTensor r s

  --  Axioms:

  -- 1. Linearity:
  contract_add {r s : ℕ} : ∀ T1 T2 : AbstractTensor (r + 1) (s + 1), contract (add T1 T2) = add (contract T1) (contract T2)
  contract_smul {r s : ℕ} : ∀ (f : R) (T : AbstractTensor (r + 1) (s + 1)), contract (smul f T) = smul f (contract T)

  nabla_tensor_add {r s : ℕ} : ∀ X (T1 T2 : AbstractTensor r s), nabla_tensor X (add T1 T2) = add (nabla_tensor X T1) (nabla_tensor X T2)

  nabla_tensor_add_left {r s : ℕ} : ∀ X Y (T : AbstractTensor r s), nabla_tensor (X + Y) T = add (nabla_tensor X T) (nabla_tensor Y T)
  nabla_tensor_smul_left {r s : ℕ} : ∀ (f : R) X (T : AbstractTensor r s), nabla_tensor (f • X) T = smul f (nabla_tensor X T)

  -- 2. Leibniz Rule: $\nabla_X(T_1 \otimes T_2) = (\nabla_X T_1) \otimes T_2 + T_1 \otimes (\nabla_X T_2)$
  leibniz_rule {r1 s1 r2 s2 : ℕ} : ∀ X (T1 : AbstractTensor r1 s1) (T2 : AbstractTensor r2 s2),
    nabla_tensor X (tensor_prod T1 T2) = add (tensor_prod (nabla_tensor X T1) T2) (tensor_prod T1 (nabla_tensor X T2))

  -- 3. Commutativity: $\text{contract}(\nabla_X T) = \nabla_X (\text{contract} T)$
  commutativity {r s : ℕ} : ∀ X (T : AbstractTensor (r + 1) (s + 1)), contract (nabla_tensor X T) = nabla_tensor X (contract T)

  -- 4. Base Cases: $\nabla_X (\text{fromScalar } f)$ = directional derivative; $\nabla_X (\text{fromVector } Y)$ = native connection
  base_scalar : ∀ X (f : R), nabla_tensor X (fromScalar f) = fromScalar (action X f)
  base_vector : ∀ X Y, nabla_tensor X (fromVector Y) = fromVector (conn.nabla X Y)

/-
  The proof to the previous class can be here.
-/

noncomputable instance mockTensorCalculus {metric : AbstractMetricTensor R V} {conn : AbstractLeviCivitaConnection metric} : AbstractTensorCalculus R V metric conn := sorry

end DifferentialGeometry.Bridge
