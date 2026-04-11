import DifferentialGeometry.VectorField
import DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Geometry.Connection
import Mathlib.LinearAlgebra.Multilinear.Curry

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open DifferentialGeometry
open TensorAlgebra
open AbstractDerivationAction

variable {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V]
variable [TensorAlgebra R V] [AbstractDerivationAction R V]



/--
Layer 2: Affine Tensor Calculus
Extends an affine connection to the entire tensor algebra by defining a universal covariant derivative operator.
-/
class AffineTensorCalculus (conn : AbstractAffineConnection R V) where
  /-- The universal covariant derivative operator acting on any (r,s) tensor -/
  nabla_tensor (X : V) {r s : ℕ} : AbstractTensor R V r s → AbstractTensor R V r s

  /-- Axiom 1: Degenerates to directional derivative on scalars (0-0 tensors) -/
  nabla_scalar : ∀ (X : V) (f : R),
    nabla_tensor X (TensorAlgebra.fromData (scalarToData f)) = TensorAlgebra.fromData (scalarToData (action X f))

  /-- Axiom 2: Degenerates to the affine connection on vector fields (1-0 tensors) -/
  nabla_vector : ∀ (X Y : V),
    nabla_tensor X (TensorAlgebra.fromData (vectorToData Y)) = TensorAlgebra.fromData (vectorToData (conn.nabla X Y))

  /-- Axiom 3: Leibniz Rule for Tensor Products -/
  nabla_tensor_prod : ∀ (X : V) {r1 s1 r2 s2 : ℕ} (T1 : AbstractTensor R V r1 s1) (T2 : AbstractTensor R V r2 s2),
    nabla_tensor X (TensorAlgebra.tensor_prod T1 T2) =
      TensorAlgebra.add (TensorAlgebra.tensor_prod (nabla_tensor X T1) T2) (TensorAlgebra.tensor_prod T1 (nabla_tensor X T2))

  /-- Axiom 4: Commutes with intrinsic contraction -/
  nabla_contract : ∀ (X : V) {r s : ℕ} (T : AbstractTensor R V (r + 1) (s + 1)),
    nabla_tensor X (TensorAlgebra.contract T) = TensorAlgebra.contract (nabla_tensor X T)

  /-- Axiom 5: Linearity over R addition -/
  nabla_add : ∀ (X : V) {r s : ℕ} (T1 T2 : AbstractTensor R V r s),
    nabla_tensor X (TensorAlgebra.add T1 T2) = TensorAlgebra.add (nabla_tensor X T1) (nabla_tensor X T2)

  /-- Axiom 6: Extended Leibniz Rule for scalar multiplication -/
  nabla_smul : ∀ (X : V) (c : R) {r s : ℕ} (T : AbstractTensor R V r s),
    nabla_tensor X (TensorAlgebra.smul c T) =
      TensorAlgebra.add (TensorAlgebra.smul (action X c) T) (TensorAlgebra.smul c (nabla_tensor X T))

  /-- Axiom 7: Additivity in the direction argument.
  ∇_{X+Y} T = ∇_X T + ∇_Y T. The covariant derivative is R-linear in the
  differentiation direction. In local coordinates this is immediate from
  (X+Y)^μ Γ^λ_μν = X^μ Γ^λ_μν + Y^μ Γ^λ_μν. -/
  nabla_add_left : ∀ (X Y : V) {r s : ℕ} (T : AbstractTensor R V r s),
    nabla_tensor (X + Y) T = TensorAlgebra.add (nabla_tensor X T) (nabla_tensor Y T)

  /-- Axiom 8: C∞-linearity in the direction argument.
  ∇_{fX} T = f · ∇_X T. The covariant derivative scales linearly with the
  direction vector field. In local coordinates: (fX)^μ = f X^μ, so
  (fX)^μ (∂_μ T + Γ·T) = f · X^μ (∂_μ T + Γ·T). -/
  nabla_smul_left : ∀ (c : R) (X : V) {r s : ℕ} (T : AbstractTensor R V r s),
    nabla_tensor (c • X) T = TensorAlgebra.smul c (nabla_tensor X T)

  /-- Axiom 9: Commutes with covariant index permutations.
  ∇_X (swap_{ij} T) = swap_{ij} (∇_X T). Index permutations are purely
  algebraic and commute with the covariant derivative. -/
  nabla_swap_covariant : ∀ (X : V) {r s : ℕ} (i j : Fin s) (T : AbstractTensor R V r s),
    nabla_tensor X (TensorAlgebra.swap_covariant i j T) = TensorAlgebra.swap_covariant i j (nabla_tensor X T)

  /-- Axiom 10: Commutes with contravariant index permutations.
  ∇_X (swap_{ij} T) = swap_{ij} (∇_X T). -/
  nabla_swap_contravariant : ∀ (X : V) {r s : ℕ} (i j : Fin r) (T : AbstractTensor R V r s),
    nabla_tensor X (TensorAlgebra.swap_contravariant i j T) = TensorAlgebra.swap_contravariant i j (nabla_tensor X T)

  /-- Axiom 11: ∇_X δ = 0. The Kronecker delta is covariantly constant because
  its components are 0 or 1 in every coordinate system. -/
  nabla_delta : ∀ (X : V), nabla_tensor X TensorAlgebra.delta_tensor = 0


-- ============================================================
-- Total Covariant Derivative (rank-increasing ∇)
-- ============================================================

variable (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn]

/-- The curried nabla map: for each vs : Fin s → V, produce the linear map
X ↦ toData(∇_X T) vs. Linearity in X uses Axiom 7/8 (nabla_add_left/smul_left);
multilinearity in vs uses the existing MultilinearMap structure of toData. -/
private noncomputable def nabla_curried {r s : ℕ} (T : AbstractTensor R V r s) :
    MultilinearMap R (fun _ : Fin s => V)
      (V →ₗ[R] MultilinearMap R (fun _ : Fin r => (V →ₗ[R] R)) R) where
  toFun vs :=
    { toFun := fun X => TensorAlgebra.toData (AffineTensorCalculus.nabla_tensor conn X T) vs
      map_add' := fun X Y => by
        have h := AffineTensorCalculus.nabla_add_left (conn := conn) X Y T
        change TensorAlgebra.toData (AffineTensorCalculus.nabla_tensor conn (X + Y) T) vs = _
        rw [h, TensorAlgebra.toData_add]; rfl
      map_smul' := fun c X => by
        have h := AffineTensorCalculus.nabla_smul_left (conn := conn) c X T
        change TensorAlgebra.toData (AffineTensorCalculus.nabla_tensor conn (c • X) T) vs = _
        rw [h, TensorAlgebra.toData_smul]; rfl }
  map_update_add' := fun m i x y => by
    ext X : 1
    exact MultilinearMap.map_update_add (TensorAlgebra.toData (AffineTensorCalculus.nabla_tensor conn X T)) m i x y
  map_update_smul' := fun m i c x => by
    ext X : 1
    exact MultilinearMap.map_update_smul (TensorAlgebra.toData (AffineTensorCalculus.nabla_tensor conn X T)) m i c x

/-- Total covariant derivative: ∇T packs X ↦ ∇_X T into an (r, s+1) tensor.
The LAST covariant slot (index `Fin.last s`) encodes the differentiation direction.

Constructed via `MultilinearMap.uncurryRight` applied to `nabla_curried`,
which avoids manual multilinearity proofs for the combined argument space.
Axiom 7 (`nabla_add_left`) and Axiom 8 (`nabla_smul_left`) provide the
R-linearity in the direction slot; the tensor evaluation slots inherit their
multilinearity from the existing `TensorData` structure. -/
noncomputable def total_nabla {r s : ℕ} (T : AbstractTensor R V r s) :
    AbstractTensor R V r (s + 1) :=
  TensorAlgebra.fromData (nabla_curried conn T).uncurryRight

/-- Evaluation of `total_nabla`: the last covariant slot is the differentiation direction.
  tensor_eval (total_nabla conn T) (Fin.snoc vs X) αs = tensor_eval (∇_X T) vs αs -/
lemma total_nabla_eval {r s : ℕ} (T : AbstractTensor R V r s)
    (vs : Fin s → V) (X : V) (αs : Fin r → (V →ₗ[R] R)) :
    tensor_eval (total_nabla conn T) (Fin.snoc vs X) αs =
    tensor_eval (AffineTensorCalculus.nabla_tensor conn X T) vs αs := by
  simp only [tensor_eval, total_nabla, TensorAlgebra.toData_fromData,
    MultilinearMap.uncurryRight_apply, Fin.init_snoc, Fin.snoc_last, nabla_curried]
  rfl
