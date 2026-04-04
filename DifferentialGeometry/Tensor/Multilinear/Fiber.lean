/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.RingTheory.TensorProduct.Finite
/-!
# Fiber-level results for the continuous multilinear map bundle

This file establishes that the bundle topology on each fiber
`Bundle.continuousMultilinearMap 𝕜 s F E x` agrees with the norm topology on
`ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜`, and derives topological and
algebraic instances from this fact.

These results hold for any vector bundle `E` with normed fibers, not just the
tangent bundle. The key tool is a continuous linear equivalence from the bundle fiber
to the model fiber, constructed from the trivialization at each point.

## Main Definitions

* `Bundle.continuousMultilinearMap.continuousLinearEquivAt`: the CLE from the bundle fiber
  at `x` to the model fiber, built from the trivialization at `x`.

## Main Results

* `Bundle.continuousMultilinearMap.topology_eq`: the bundle and norm topologies agree.
* Derived instances: `NormedAddCommGroup`, `NormedSpace`, `T2Space`,
  `IsTopologicalAddGroup`, `ContinuousSMul`, `FiniteDimensional` on fibers.
* `Bundle.continuousMultilinearMap.finrank_eq`: dimension is `(finrank 𝕜 F) ^ s`.

## Tags

multilinear map, vector bundle, fiber topology, continuous linear equivalence
-/

noncomputable section

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {s : ℕ}

/-- `Bundle.continuousMultilinearMap` fibers inherit the `FunLike` coercion from
`ContinuousMultilinearMap`, enabling direct function application. -/
instance instFunLike (s : ℕ) (x : B) :
    FunLike (Bundle.continuousMultilinearMap 𝕜 s F E x) (Fin s → E x) 𝕜 :=
  ContinuousMultilinearMap.funLike

/-!
## Topology equivalence

The bundle topology on `Bundle.continuousMultilinearMap 𝕜 s F E x` is defined as
`induced (pretriv ∘ mk') product_topology`. We show this equals the norm topology on
`ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜` by factoring through a
homeomorphism to the model fiber.
-/

/-- The bundle and norm topologies on a `Bundle.continuousMultilinearMap` fiber agree.
The bundle topology is induced from the pretrivialization (a continuous linear equivalence
to the model fiber), and this coincides with the norm topology since the composition map
is a homeomorphism. -/
theorem topology_eq (s : ℕ) (x : B) :
    (inferInstance : TopologicalSpace (Bundle.continuousMultilinearMap 𝕜 s F E x)) =
    (inferInstanceAs (TopologicalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜))) := by
  change instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x = _
  simp only [instTopologicalSpaceContinuousMultilinearMap]
  -- Step 1: Factor pretriv ∘ mk' = Prod.mk x ∘ g where g is the fiber map
  set e := trivializationAt F E x
  set g := ContinuousMultilinearMap.compContinuousLinearMapL
    (E₁ := fun _ : Fin s => E x) (E := fun _ : Fin s => F) (G := 𝕜)
    (fun _ => e.symmL 𝕜 x) with hg_def
  have hfactor : (↑(Pretrivialization.continuousMultilinearMap 𝕜 s e) ∘
      TotalSpace.mk' _ x) = Prod.mk x ∘ g := by funext; rfl
  -- Step 2: Decompose via induced_compose and isInducing_prodMkRight
  rw [hfactor, ← induced_compose, (isInducing_prodMkRight x).eq_induced.symm]
  -- Goal: induced g τ_norm = τ_norm
  -- Step 3: g is a homeomorphism (continuous with continuous inverse), hence inducing
  set g' := ContinuousMultilinearMap.compContinuousLinearMapL
    (E₁ := fun _ : Fin s => F) (E := fun _ : Fin s => E x) (G := 𝕜)
    (fun _ => e.continuousLinearMapAt 𝕜 x) with hg'_def
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F E x
  have hleft : Function.LeftInverse g' g := by
    intro L; ext v; dsimp [g, g']
    congr 1; funext i; exact e.symmₗ_linearMapAt hx (v i)
  have hright : Function.RightInverse g' g := by
    intro M; ext v; dsimp [g, g']
    congr 1; funext i; exact e.linearMapAt_symmₗ hx (v i)
  exact (Homeomorph.mk ⟨g, g', hleft, hright⟩
    g.continuous g'.continuous).isInducing.eq_induced.symm

/-!
## Normed instances
-/

/-- The fiber `Bundle.continuousMultilinearMap 𝕜 s F E x` is a normed additive commutative
group, using the norm topology which agrees with the bundle topology. -/
instance instNormedAddCommGroup (s : ℕ) (x : B) :
    NormedAddCommGroup (Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  inferInstanceAs (NormedAddCommGroup
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜))

/-- The fiber `Bundle.continuousMultilinearMap 𝕜 s F E x` is a normed `𝕜`-module. -/
instance instNormedSpace (s : ℕ) (x : B) :
    NormedSpace 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  inferInstanceAs (NormedSpace 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜))

/-!
## Topological instances derived from the topology equality
-/

instance instT2Space (s : ℕ) (x : B) :
    T2Space (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  rw [show instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
        ContinuousMultilinearMap.instTopologicalSpace from topology_eq s x]
  infer_instance

instance instIsTopologicalAddGroup (s : ℕ) (x : B) :
    @IsTopologicalAddGroup (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance _ := by
  rw [topology_eq s x]
  infer_instance

instance instContinuousSMul (s : ℕ) (x : B) :
    @ContinuousSMul 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) _ _ inferInstance := by
  rw [topology_eq s x]
  infer_instance

instance instContinuousAdd (s : ℕ) (x : B) :
    @ContinuousAdd (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance _ :=
  @IsTopologicalAddGroup.toContinuousAdd _ inferInstance _ (instIsTopologicalAddGroup s x)

/-!
## Continuous linear equivalence to the model fiber
-/

/-- The continuous linear equivalence from the multilinear bundle fiber at `x` to the model
fiber `ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜`, constructed from the
trivialization at `x`. The forward map precomposes with `e.symmL`, and the inverse
precomposes with `e.continuousLinearMapAt`. -/
def continuousLinearEquivAt (s : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x ≃L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 where
  toFun := ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ => (trivializationAt F E x).symmL 𝕜 x)
  invFun := ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ => (trivializationAt F E x).continuousLinearMapAt 𝕜 x)
  left_inv L := ContinuousMultilinearMap.ext fun v => by
    dsimp [ContinuousMultilinearMap.compContinuousLinearMapL]
    congr 1; funext i
    exact (trivializationAt F E x).symmₗ_linearMapAt
      (mem_baseSet_trivializationAt F E x) (v i)
  right_inv M := ContinuousMultilinearMap.ext fun v => by
    dsimp [ContinuousMultilinearMap.compContinuousLinearMapL]
    congr 1; funext i
    exact (trivializationAt F E x).linearMapAt_symmₗ
      (mem_baseSet_trivializationAt F E x) (v i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    change @Continuous (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x)
      ContinuousMultilinearMap.instTopologicalSpace _
    rw [show instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
      ContinuousMultilinearMap.instTopologicalSpace from topology_eq s x]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => (trivializationAt F E x).symmL 𝕜 x)).continuous
  continuous_invFun := by
    change @Continuous (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 s F E x)
      ContinuousMultilinearMap.instTopologicalSpace
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x) _
    rw [show instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
      ContinuousMultilinearMap.instTopologicalSpace from topology_eq s x]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => (trivializationAt F E x).continuousLinearMapAt 𝕜 x)).continuous

/-!
## Extensionality
-/

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E] in
@[ext]
theorem ext {s : ℕ} {x : B}
    {T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 s F E x}
    (h : ∀ m, T₁ m = T₂ m) : T₁ = T₂ :=
  ContinuousMultilinearMap.ext h

/-!
## Coercion to model fiber

The continuous linear equivalence `continuousLinearEquivAt` identifies each fiber with
the model fiber. We package this as `toModel` (forward direction) and `ofModel`
(its inverse), together with linearity, continuity, and invertibility lemmas.
-/

/-- Coerce a multilinear bundle fiber element to the model fiber via the trivialization CLE. -/
def toModel {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
  continuousLinearEquivAt (F := F) (E := E) s x T

/-- `toModel` as a bundled `ContinuousLinearMap`. -/
def toModelL (s : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
  (continuousLinearEquivAt (F := F) (E := E) s x).toContinuousLinearMap

/-- Construct a multilinear bundle fiber element from a model fiber element. -/
def ofModel {s : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    Bundle.continuousMultilinearMap 𝕜 s F E x :=
  (continuousLinearEquivAt (F := F) (E := E) s x).symm f

@[simp]
theorem toModelL_apply {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModelL (F := F) (E := E) s x T = toModel T := rfl

@[simp]
theorem toModel_add {s : ℕ} {x : B}
    (T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (T₁ + T₂) =
      toModel T₁ + toModel T₂ :=
  map_add (continuousLinearEquivAt (F := F) (E := E) s x) T₁ T₂

@[simp]
theorem toModel_smul {s : ℕ} {x : B}
    (c : 𝕜) (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (c • T) = c • toModel T :=
  map_smul (continuousLinearEquivAt (F := F) (E := E) s x) c T

@[simp]
theorem toModel_zero {s : ℕ} {x : B} :
    toModel (F := F) (E := E)
      (0 : Bundle.continuousMultilinearMap 𝕜 s F E x) = 0 :=
  map_zero (continuousLinearEquivAt (F := F) (E := E) s x)

@[simp]
theorem toModel_neg {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (-T) = -toModel T :=
  map_neg (continuousLinearEquivAt (F := F) (E := E) s x) T

@[simp]
theorem toModel_sub {s : ℕ} {x : B}
    (T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (T₁ - T₂) =
      toModel T₁ - toModel T₂ :=
  map_sub (continuousLinearEquivAt (F := F) (E := E) s x) T₁ T₂

@[simp]
theorem ofModel_toModel {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ofModel (F := F) (E := E) (toModel T) = T :=
  (continuousLinearEquivAt (F := F) (E := E) s x).symm_apply_apply T

@[simp]
theorem toModel_ofModel {s : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    toModel (F := F) (E := E) (ofModel (x := x) f) = f :=
  (continuousLinearEquivAt (F := F) (E := E) s x).apply_symm_apply f

theorem toModel_continuous {s : ℕ} {x : B} :
    Continuous
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T) :=
  (continuousLinearEquivAt (F := F) (E := E) s x).continuous_toFun

theorem toModel_injective {s : ℕ} {x : B} :
    Function.Injective
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T) :=
  (continuousLinearEquivAt (F := F) (E := E) s x).injective

theorem toModel_surjective {s : ℕ} {x : B} :
    Function.Surjective
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T) :=
  (continuousLinearEquivAt (F := F) (E := E) s x).surjective

theorem toModel_bijective {s : ℕ} {x : B} :
    Function.Bijective
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T) :=
  (continuousLinearEquivAt (F := F) (E := E) s x).bijective

/-!
## Finite-dimensionality and rank
-/

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

noncomputable instance instFiniteDimensional (s : ℕ) (x : B) :
    FiniteDimensional 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  exact (continuousLinearEquivAt (F := F) (E := E) s x).symm.toLinearEquiv.finiteDimensional

@[simp]
theorem finrank_eq (s : ℕ) (x : B) :
    Module.finrank 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) =
    (Module.finrank 𝕜 F) ^ s := by
  rw [(continuousLinearEquivAt (F := F) (E := E) s x).toLinearEquiv.finrank_eq,
      finrank_continuousMultilinearMap s]

/-!
## Tensor product of multilinear bundle fibers

The pointwise tensor product of an `s`-multilinear and a `q`-multilinear bundle fiber element
yields an `(s+q)`-multilinear element by concatenating inputs. The construction works by
mapping to the model fiber via `toModel`, forming the product there using
`smulRight`/`uncurrySum`/`domDomCongr`, and mapping back via `ofModel`.
-/

/-- The pointwise tensor product of two multilinear bundle fiber elements,
yielding an `(s+q)`-multilinear map by concatenating their inputs. -/
noncomputable def product_fun {s q : ℕ} {x : B}
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x)
    (β : Bundle.continuousMultilinearMap 𝕜 q F E x) :
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x :=
  ofModel (F := F) (E := E)
    ((toModel (F := F) (E := E) α |>.smulRight
      (toModel (F := F) (E := E) β)).uncurrySum.domDomCongr finSumFinEquiv)

scoped infixl:70 " ⊗ₘ " => product_fun

/-- The tensor product of multilinear bundle fiber elements is bilinear. -/
noncomputable def product_bilinear (s q : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x →ₗ[𝕜]
    Bundle.continuousMultilinearMap 𝕜 q F E x →ₗ[𝕜]
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x :=
  LinearMap.mk₂ 𝕜 product_fun
    (fun α₁ α₂ β => by
      apply toModel_injective (F := F) (E := E)
      simp only [product_fun, toModel_add, toModel_ofModel]
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 ContinuousMultilinearMap.add_apply,
                 ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring)
    (fun c α β => by
      apply toModel_injective (F := F) (E := E)
      simp only [product_fun, toModel_smul, toModel_ofModel]
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring)
    (fun α β₁ β₂ => by
      apply toModel_injective (F := F) (E := E)
      simp only [product_fun, toModel_add, toModel_ofModel]
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 ContinuousMultilinearMap.add_apply,
                 ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring)
    (fun c α β => by
      apply toModel_injective (F := F) (E := E)
      simp only [product_fun, toModel_smul, toModel_ofModel]
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring)

/-- The tensor product map lifted to the abstract tensor product via the universal property. -/
noncomputable def fromTensor (s q : ℕ) (x : B) :
    TensorProduct 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x) →ₗ[𝕜]
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x :=
  TensorProduct.lift (product_bilinear (F := F) (E := E) s q x)

/-- Linear equivalence between the `(s+q)`-multilinear bundle fiber and the tensor product
of the `s`- and `q`-multilinear bundle fibers, obtained by dimension counting. -/
noncomputable def equiv (s q : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x ≃ₗ[𝕜]
    TensorProduct 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x) := by
  haveI := instFiniteDimensional (𝕜 := 𝕜) (F := F) (E := E) s x
  haveI := instFiniteDimensional (𝕜 := 𝕜) (F := F) (E := E) q x
  haveI := instFiniteDimensional (𝕜 := 𝕜) (F := F) (E := E) (s + q) x
  haveI : Module.Free 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) := inferInstance
  haveI : Module.Free 𝕜 (Bundle.continuousMultilinearMap 𝕜 q F E x) := inferInstance
  haveI : FiniteDimensional 𝕜 (TensorProduct 𝕜
      (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x)) :=
    Module.Finite.tensorProduct 𝕜 _ _
  exact LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_tensorProduct,
        finrank_eq (𝕜 := 𝕜) (F := F) (E := E) s x,
        finrank_eq (𝕜 := 𝕜) (F := F) (E := E) q x,
        finrank_eq (𝕜 := 𝕜) (F := F) (E := E) (s + q) x, pow_add])

end Bundle.continuousMultilinearMap

end
