import DifferentialGeometry.Synthetic.Realization.Embedding
import DifferentialGeometry.Synthetic.Realization.Connection
import DifferentialGeometry.Integral.L2.Basic
import DifferentialGeometry.Integral.Measure.Properties
import Mathlib.Topology.Algebra.Support
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Compactly-supported smooth scalars and tangent sections

This file packages two `ℝ`-submodules of smooth data on a smooth manifold:

* `compactlySupportedSmoothFunctions I M` — the scalar-valued smooth functions
  `C^∞⟮I, M; ℝ⟯` whose underlying `M → ℝ` map has compact support;
* `compactlySupportedSmoothTangentSections I M` — the smooth tangent sections
  `Cₛ^∞⟮I; E, TangentSpace I⟯` whose underlying map has compact support.

The closure properties under pointwise addition and real scalar multiplication
follow from the standard `HasCompactSupport` closure lemmas. We further record:

* pointwise multiplication closure for scalars, both symmetric
  (`_mul_mem`) and one-sided (`_mul_mem_left`, `_mul_mem_right`);
* closure under the directional derivative
  `vectorFieldActionSmooth I M X f`, in both variable arguments;
* closure of the concrete Levi-Civita-style connection
  `concreteConn I M cov X Y` in the vector-field argument.

All results take hypotheses in the minimal form consistent with the conventions
of `Integral/Integration/Basic.lean`.
-/

noncomputable section

open Manifold Set Filter Bundle CovariantDerivative
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Submodule of compactly-supported smooth scalar functions -/

/-- The `ℝ`-submodule of smooth scalar functions `C^∞⟮I, M; ℝ⟯` whose underlying
`M → ℝ` map has compact support. Closed under pointwise addition and scalar
multiplication by the `HasCompactSupport` closure lemmas. -/
def compactlySupportedSmoothFunctions
    (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    Submodule ℝ C^∞⟮I, M; ℝ⟯ where
  carrier := { f : C^∞⟮I, M; ℝ⟯ | HasCompactSupport (f : M → ℝ) }
  zero_mem' := by
    change HasCompactSupport ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    simpa [ContMDiffMap.coe_zero] using
      (HasCompactSupport.zero : HasCompactSupport (0 : M → ℝ))
  add_mem' := by
    intro f f' hf hf'
    change HasCompactSupport ((f + f' : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    simpa [ContMDiffMap.coe_add] using hf.add hf'
  smul_mem' := by
    intro c f hf
    change HasCompactSupport ((c • f : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    -- Coerce the scalar multiple to the pointwise one and apply `smul_left`.
    have h : ((c • f : C^∞⟮I, M; ℝ⟯) : M → ℝ) = (fun _ : M => c) • (f : M → ℝ) := by
      ext x
      simp [ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [h]
    exact hf.smul_left

@[simp]
lemma mem_compactlySupportedSmoothFunctions
    {f : C^∞⟮I, M; ℝ⟯} :
    f ∈ compactlySupportedSmoothFunctions I M ↔ HasCompactSupport (f : M → ℝ) := Iff.rfl

/-! ## Submodule of compactly-supported smooth tangent sections -/

/-- The `ℝ`-submodule of smooth tangent sections whose underlying map to the
model space has compact support. Closed under pointwise addition and
scalar multiplication. -/
def compactlySupportedSmoothTangentSections
    (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    Submodule ℝ Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  carrier :=
    { X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ |
        HasCompactSupport (fun x : M => (X x : E)) }
  zero_mem' := by
    change HasCompactSupport
      (fun x : M => ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E))
    have h : (fun x : M =>
        ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E)) = (fun _ : M => (0 : E)) := by
      funext x
      change ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E) = (0 : E)
      rfl
    rw [h]
    exact HasCompactSupport.zero
  add_mem' := by
    intro X Y hX hY
    change HasCompactSupport
      (fun x : M =>
        (((X + Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) x : E))
    have h : (fun x : M =>
        (((X + Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) x : E)) =
        (fun x : M => (X x : E)) + (fun x : M => (Y x : E)) := by
      funext x
      change ((X + Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E) =
        ((X x : E) + (Y x : E))
      simp [ContMDiffSection.coe_add, Pi.add_apply]
    rw [h]
    exact hX.add hY
  smul_mem' := by
    intro c X hX
    change HasCompactSupport
      (fun x : M =>
        (((c • X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) x : E))
    have h : (fun x : M =>
        (((c • X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) x : E)) =
        (fun _ : M => c) • (fun x : M => (X x : E)) := by
      funext x
      change ((c • X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E) =
        c • (X x : E)
      simp [ContMDiffSection.coe_smul, Pi.smul_apply]
    rw [h]
    exact hX.smul_left

@[simp]
lemma mem_compactlySupportedSmoothTangentSections
    {X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯} :
    X ∈ compactlySupportedSmoothTangentSections I M ↔
      HasCompactSupport (fun x : M => (X x : E)) := Iff.rfl

/-! ## Pointwise multiplication closure for scalars -/

/-- Pointwise multiplication preserves compact support on the left: if `f` is
compactly supported, so is `f * f'` for any smooth `f'`. -/
theorem compactlySupportedSmoothFunctions_mul_mem_left
    {f : C^∞⟮I, M; ℝ⟯} (hf : f ∈ compactlySupportedSmoothFunctions I M)
    (f' : C^∞⟮I, M; ℝ⟯) :
    f * f' ∈ compactlySupportedSmoothFunctions I M := by
  change HasCompactSupport ((f * f' : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  have h : ((f * f' : C^∞⟮I, M; ℝ⟯) : M → ℝ) = (f : M → ℝ) * (f' : M → ℝ) := by
    ext x
    simp [ContMDiffMap.coe_mul, Pi.mul_apply]
  rw [h]
  exact hf.mul_right

/-- Pointwise multiplication preserves compact support on the right: if `f'` is
compactly supported, so is `f * f'` for any smooth `f`. -/
theorem compactlySupportedSmoothFunctions_mul_mem_right
    (f : C^∞⟮I, M; ℝ⟯) {f' : C^∞⟮I, M; ℝ⟯}
    (hf' : f' ∈ compactlySupportedSmoothFunctions I M) :
    f * f' ∈ compactlySupportedSmoothFunctions I M := by
  change HasCompactSupport ((f * f' : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  have h : ((f * f' : C^∞⟮I, M; ℝ⟯) : M → ℝ) = (f : M → ℝ) * (f' : M → ℝ) := by
    ext x
    simp [ContMDiffMap.coe_mul, Pi.mul_apply]
  rw [h]
  exact hf'.mul_left

/-- Pointwise multiplication is closed within the compactly-supported submodule:
the product of two compactly-supported smooth scalars is again compactly
supported. -/
theorem compactlySupportedSmoothFunctions_mul_mem
    {f f' : C^∞⟮I, M; ℝ⟯}
    (hf : f ∈ compactlySupportedSmoothFunctions I M)
    (_hf' : f' ∈ compactlySupportedSmoothFunctions I M) :
    f * f' ∈ compactlySupportedSmoothFunctions I M :=
  compactlySupportedSmoothFunctions_mul_mem_left hf f'

/-! ## Directional-derivative closure

The directional derivative `vectorFieldActionSmooth I M X f`, constructed in
`Synthetic/Realization/Embedding.lean`, sends a smooth tangent section `X` and a
smooth scalar `f` to the smooth scalar `X(f)`, whose value at a point `x` is the
continuous-linear-map image of `X x` under the exterior derivative of `f` at
`x`. Two support arguments follow directly from this pointwise formula. -/

section DirectionalDerivative

variable [T2Space M] [SigmaCompactSpace M]

/-- Auxiliary: the pointwise value of `vectorFieldAction` at a point `x` where
the vector field vanishes is zero, since the exterior derivative at `x` is a
continuous linear map. -/
private lemma vectorFieldAction_eq_zero_of_vectorField_eq_zero
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : C^∞⟮I, M; ℝ⟯)
    {x : M} (hx : X x = 0) :
    vectorFieldAction I M X f x = 0 := by
  simp [vectorFieldAction, hx]

/-- If the vector field `X` is compactly supported, then the directional
derivative `X(f)` is compactly supported for every smooth scalar `f`. -/
theorem compactlySupportedSmoothTangentSections_action_mem
    {X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hX : X ∈ compactlySupportedSmoothTangentSections I M)
    (f : C^∞⟮I, M; ℝ⟯) :
    vectorFieldActionSmooth I M X f ∈ compactlySupportedSmoothFunctions I M := by
  change HasCompactSupport
    ((vectorFieldActionSmooth I M X f : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  -- The coercion is the underlying `vectorFieldAction I M X f`.
  have hcoe :
      ((vectorFieldActionSmooth I M X f : C^∞⟮I, M; ℝ⟯) : M → ℝ) =
        vectorFieldAction I M X f := rfl
  rw [hcoe]
  -- `support (X f) ⊆ support (fun x => (X x : E))`: if `X x = 0` then `X(f)(x) = 0`.
  refine HasCompactSupport.mono (f := fun x : M => (X x : E)) hX ?_
  intro x hx
  -- `x ∈ support (vectorFieldAction I M X f)` means `vectorFieldAction I M X f x ≠ 0`.
  -- We must show `x ∈ support (fun x => (X x : E))`, i.e. `X x ≠ 0`.
  by_contra hXx
  apply hx
  have : X x = 0 := by
    -- `hXx : ¬ (X x : E) ≠ 0`, i.e. `(X x : E) = 0`.
    simpa using hXx
  exact vectorFieldAction_eq_zero_of_vectorField_eq_zero X f this

/-- If the scalar `f` is compactly supported, then the directional derivative
`X(f)` is compactly supported for every smooth vector field `X`. -/
theorem compactlySupportedSmoothFunctions_action_of_smooth_section
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : C^∞⟮I, M; ℝ⟯}
    (hf : f ∈ compactlySupportedSmoothFunctions I M) :
    vectorFieldActionSmooth I M X f ∈ compactlySupportedSmoothFunctions I M := by
  change HasCompactSupport
    ((vectorFieldActionSmooth I M X f : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  have hcoe :
      ((vectorFieldActionSmooth I M X f : C^∞⟮I, M; ℝ⟯) : M → ℝ) =
        vectorFieldAction I M X f := rfl
  rw [hcoe]
  -- `support (X f) ⊆ tsupport f`: if `f =ᶠ 0` near `x`, then `mfderiv f x = 0`,
  -- so `X(f)(x) = extDerivFun f x (X x) = 0`.
  refine HasCompactSupport.mono' (f := (f : M → ℝ)) hf ?_
  intro x hx
  -- `hx : x ∈ support (vectorFieldAction I M X f)`.
  -- Goal: `x ∈ tsupport (f : M → ℝ)`.
  by_contra hxnot
  apply hx
  -- `hxnot : x ∉ tsupport f` gives `f =ᶠ 0` near `x`.
  have hfEq : (f : M → ℝ) =ᶠ[𝓝 x] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hxnot
  -- Deduce that `mfderiv f x = 0`.
  have hmfd : mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x = mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => (0 : ℝ)) x :=
    hfEq.mfderiv_eq
  -- Reduce to the claim via the definition of `vectorFieldAction`.
  have : extDerivFun (I := I) (f : M → ℝ) x (X x) = 0 := by
    have hmfd_zero : mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x = 0 := by
      rw [hmfd]
      exact mfderiv_const
    simp [extDerivFun, hmfd_zero]
  simpa [vectorFieldAction] using this

end DirectionalDerivative

/-! ## Levi-Civita-style connection closure

For a bundled covariant derivative `cov` of class `C^∞` on the tangent bundle,
the concrete connection `concreteConn I M cov X Y` evaluates at a point `x` to
`cov Y x (X x)`. Compact support of `X` (resp. `Y`) implies compact support of
the resulting smooth section, via pointwise continuous-linear-map zero (resp.
locality of `cov`). -/

section CovariantDerivativeClosure

variable [T2Space M] [SigmaCompactSpace M]

/-- If the vector field `X` is compactly supported, then `∇_X Y = concreteConn
  cov X Y` is a compactly-supported smooth section for every smooth `Y`. -/
theorem compactlySupportedSmoothTangentSections_conn_mem_of_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    {X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hX : X ∈ compactlySupportedSmoothTangentSections I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov X Y ∈ compactlySupportedSmoothTangentSections I M := by
  change HasCompactSupport
    (fun x : M => ((concreteConn I M cov X Y) x : E))
  -- `support (∇_X Y) ⊆ support X`: if `X x = 0` then `(cov Y x) (X x) = 0`.
  refine HasCompactSupport.mono (f := fun x : M => (X x : E)) hX ?_
  intro x hx
  -- `hx : x ∈ support (fun x => (concreteConn X Y) x)`: `concreteConn X Y x ≠ 0`.
  -- Goal: `X x ≠ 0`.
  by_contra hXx
  apply hx
  have hXx' : X x = 0 := by simpa using hXx
  -- `concreteConn cov X Y x = cov Y x (X x) = cov Y x 0 = 0`.
  change ((concreteConn I M cov X Y) x : E) = 0
  have : (concreteConn I M cov X Y) x = 0 := by
    simp [concreteConn_apply, hXx']
  simpa using this

/-- If the vector field `Y` is compactly supported, then `∇_X Y = concreteConn
  cov X Y` is a compactly-supported smooth section for every smooth `X`.

The argument uses locality of a covariant derivative: if `Y` vanishes on an open
neighborhood of `x`, then `cov Y x = cov 0 x = 0`. -/
theorem compactlySupportedSmoothTangentSections_conn_mem_of_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hY : Y ∈ compactlySupportedSmoothTangentSections I M) :
    concreteConn I M cov X Y ∈ compactlySupportedSmoothTangentSections I M := by
  change HasCompactSupport
    (fun x : M => ((concreteConn I M cov X Y) x : E))
  -- `support (∇_X Y) ⊆ tsupport Y`: if `Y =ᶠ 0` near `x` then `cov Y x = 0`.
  refine HasCompactSupport.mono' (f := fun x : M => (Y x : E)) hY ?_
  intro x hx
  -- `hx : x ∈ support (fun x => (concreteConn X Y) x)`.
  -- Goal: `x ∈ tsupport (fun x => (Y x : E))`.
  by_contra hxnot
  apply hx
  -- From `hxnot` we get that `fun x => (Y x : E)` vanishes eventually near `x`.
  have hY_eq_E : (fun x : M => (Y x : E)) =ᶠ[𝓝 x] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hxnot
  have hY_eq_dep : (fun x : M => Y x) =ᶠ[𝓝 x]
      (fun x : M => (0 : TangentSpace I x)) := by
    filter_upwards [hY_eq_E] with y hy
    -- `hy : (fun x => (Y x : E)) y = 0 y`, i.e. `(Y y : E) = 0`.
    -- This is definitionally `Y y = 0` because `TangentSpace I y = E`.
    have : (Y y : E) = (0 : E) := by simpa using hy
    exact this
  -- Apply `CovariantDerivative.zero`: `cov 0 = 0`.
  have hY_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun x : M => (TotalSpace.mk' E x (Y x) : TangentBundle I M)) x :=
    Y.mdifferentiableAt
  have hzero_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun x : M => (TotalSpace.mk' E x
        (0 : (TangentSpace I : M → Type _) x) : TangentBundle I M)) x :=
    mdifferentiableAt_zeroSection (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I)
  have huniv : (Set.univ : Set M) ∈ 𝓝 x := Filter.univ_mem
  have hcov_eq :
      (cov.toFun (fun x : M => Y x)) x =
        (cov.toFun (fun x : M => (0 : (TangentSpace I : M → Type _) x))) x :=
    cov.isCovariantDerivativeOn.congr_of_eventuallyEq hY_diff hzero_diff huniv hY_eq_dep
  -- `cov 0 = 0` pointwise.
  have hcov_zero :
      (cov.toFun (fun x : M => (0 : (TangentSpace I : M → Type _) x))) x = 0 := by
    -- `cov.zero : cov 0 = 0` where `0` on the LHS is `Pi.instZero`, the pointwise-zero section.
    have h0 : cov.toFun (fun x : M => (0 : (TangentSpace I : M → Type _) x)) =
        fun x : M => (0 : TangentSpace I x →L[ℝ] TangentSpace I x) :=
      cov.zero
    -- Evaluate at `x`.
    exact congrArg (fun φ => φ x) h0
  -- Combine: `cov Y x = 0`, hence `concreteConn X Y x = cov Y x (X x) = 0`.
  change ((concreteConn I M cov X Y) x : E) = 0
  have hcov_Y_zero : (cov.toFun (fun x : M => Y x)) x = 0 := hcov_eq.trans hcov_zero
  have : (concreteConn I M cov X Y) x = 0 := by
    change (cov.toFun (fun x : M => Y x)) x (X x) = 0
    rw [hcov_Y_zero]
    simp
  simpa using this

end CovariantDerivativeClosure

/-! ## Density of compactly-supported smooth scalar functions in `L^p`

On a smooth finite-dimensional σ-compact Hausdorff boundaryless manifold `M`
equipped with a smooth Riemannian metric `g`, the image of
`compactlySupportedSmoothFunctions I M` under the natural map to
`Lp ℝ p (riemannianVolumeMeasure g)` is dense for every `p ∈ [1, ∞)`.

The proof proceeds by the classical two-step ladder:

1. continuous compactly-supported functions are dense in `L^p` on a regular
   locally-finite Radon measure over a σ-compact (weakly) locally-compact
   Hausdorff `R1` space (Mathlib's
   `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`);
2. smooth compactly-supported functions uniformly approximate continuous
   compactly-supported functions with nested support
   (Mathlib's `Continuous.exists_contMDiff_approx`); the uniform bound, together
   with the finite measure of the common compact support, controls the `L^p`
   distance directly.

The natural map is implemented via `MemLp.toLp` applied to the underlying
`M → ℝ` coercion of each `C^∞⟮I, M; ℝ⟯`. The membership lemma
`compactlySupportedSmoothFunctions_memLp` packages memebership in `L^p`, based
on `Continuous.memLp_of_hasCompactSupport` plus local finiteness of the
Riemannian volume measure on compacts.  -/

section LpDensity

open MeasureTheory
open scoped ENNReal

-- Borel structures on `E` and `M`, matching the ones installed in
-- `Integral/Integration/Basic.lean` and the `Measure/` files.
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure

/-- A smooth function with compact support is in `L^p` for every `p` with respect
to the Riemannian volume measure. Consequence of local finiteness of the
Riemannian volume measure on compacts together with continuity (smoothness
implies continuity). -/
theorem compactlySupportedSmoothFunctions_memLp
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {p : ℝ≥0∞}
    {f : C^∞⟮I, M; ℝ⟯} (hf : f ∈ compactlySupportedSmoothFunctions I M) :
    MeasureTheory.MemLp ((f : M → ℝ)) p
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  -- `hf` says that the underlying `M → ℝ` map is compactly supported; `f` is
  -- continuous because it is smooth.
  have hcont : Continuous (f : M → ℝ) := f.contMDiff.continuous
  have hsup : HasCompactSupport ((f : M → ℝ)) := hf
  exact hcont.memLp_of_hasCompactSupport (μ := riemannianVolumeMeasure (I := I) (M := M) g) hsup

/-- Any continuous compactly-supported `φ : M → ℝ` can be uniformly approximated by
a smooth compactly-supported map whose support is contained in `tsupport φ`. The
precision of the uniform approximation is controlled by any positive real `δ`. -/
private lemma exists_contMDiff_uniform_approx_sub_compact_support
    [T2Space M] [SigmaCompactSpace M]
    {φ : M → ℝ} (hφ : Continuous φ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : C^∞⟮I, M; ℝ⟯,
      (∀ x : M, |(g : M → ℝ) x - φ x| < δ) ∧
        Function.support (g : M → ℝ) ⊆ Function.support φ := by
  have hε_cont : Continuous (fun _ : M => δ) := continuous_const
  have hε_pos : ∀ x : M, 0 < (fun _ : M => δ) x := fun _ => hδ
  -- `Continuous.exists_contMDiff_approx` gives a `C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯`
  -- approximator with pointwise control by `δ` and support contained in
  -- `support φ`. Since `𝓘(ℝ, ℝ) = modelWithCornersSelf ℝ ℝ`, the output
  -- unifies with `C^∞⟮I, M; ℝ⟯`.
  obtain ⟨g, g_approx, g_supp⟩ :=
    hφ.exists_contMDiff_approx (F := ℝ) I (⊤ : ℕ∞) hε_cont hε_pos
  refine ⟨g, ?_, g_supp⟩
  intro x
  have := g_approx x
  simpa [Real.dist_eq] using this

/-- `eLpNorm` of a continuous function bounded by `δ` and supported on a set of
finite measure `K`, with bound `μ K ^ (1/p) * δ`. This is the key analytic
building block of the density result: the `L^p` norm of the difference between a
continuous compactly-supported function and its smooth uniform approximation is
controlled by the uniform bound times the `(1/p)`-power of the measure of the
common compact support. -/
private lemma eLpNorm_le_of_bound_and_support_le_measure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {p : ℝ≥0∞}
    {h : M → ℝ} (_h_meas : AEStronglyMeasurable h
      (riemannianVolumeMeasure (I := I) (M := M) g))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h_bound : ∀ x : M, ‖h x‖ ≤ δ)
    {K : Set M} (hK : IsCompact K)
    (h_supp : ∀ x : M, x ∉ K → h x = 0) :
    eLpNorm h p (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (riemannianVolumeMeasure (I := I) (M := M) g K) ^ (p.toReal⁻¹) *
        ENNReal.ofReal δ := by
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  -- Write `h = K.indicator h` since `h` vanishes off `K`.
  have h_eq : h = K.indicator h := by
    ext x
    by_cases hx : x ∈ K
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, h_supp x hx]
  rw [h_eq]
  -- Bound `‖K.indicator h x‖ ≤ K.indicator (fun _ => δ) x` pointwise.
  have hpt : ∀ x : M,
      ‖K.indicator h x‖ ≤ ‖K.indicator (fun _ : M => δ) x‖ := by
    intro x
    by_cases hx : x ∈ K
    · have hnonneg : (0 : ℝ) ≤ δ := hδ
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
        show ‖(δ : ℝ)‖ = δ from by rw [Real.norm_eq_abs]; exact abs_of_nonneg hnonneg]
      exact h_bound x
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  -- Reduce to the indicator bound.
  have h1 : eLpNorm (K.indicator h) p μ ≤
      eLpNorm (K.indicator (fun _ : M => δ)) p μ :=
    eLpNorm_mono hpt
  -- Bound `eLpNorm (K.indicator const) p μ ≤ δ · μ K ^ (1/p)`.
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have h2 : eLpNorm (K.indicator (fun _ : M => δ)) p μ ≤
      ‖(δ : ℝ)‖ₑ * μ K ^ (p.toReal⁻¹) := by
    have := eLpNorm_indicator_const_le (μ := μ) (s := K) (c := δ) p
    -- `eLpNorm_indicator_const_le` returns the bound using `‖c‖ₑ`.
    simpa [one_div] using this
  -- `‖δ‖ₑ = ENNReal.ofReal δ` for `δ ≥ 0`.
  have hδ_enorm : ‖(δ : ℝ)‖ₑ = ENNReal.ofReal δ := by
    rw [Real.enorm_eq_ofReal hδ]
  calc
    eLpNorm (K.indicator h) p μ ≤ eLpNorm (K.indicator (fun _ : M => δ)) p μ := h1
    _ ≤ ‖(δ : ℝ)‖ₑ * μ K ^ (p.toReal⁻¹) := h2
    _ = ENNReal.ofReal δ * μ K ^ (p.toReal⁻¹) := by rw [hδ_enorm]
    _ = μ K ^ (p.toReal⁻¹) * ENNReal.ofReal δ := by rw [mul_comm]

/-- Approximation of a continuous compactly-supported `φ : M → ℝ` by a smooth
compactly-supported function in `eLpNorm`. The smooth approximator has its
support contained in `tsupport φ`, so it is itself compactly supported. -/
private lemma exists_smoothCompactSupport_eLpNorm_sub_le_of_continuous
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {φ : M → ℝ} (hφ_cont : Continuous φ) (hφ_supp : HasCompactSupport φ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ f : C^∞⟮I, M; ℝ⟯,
      f ∈ compactlySupportedSmoothFunctions I M ∧
        eLpNorm (φ - (f : M → ℝ)) p
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ ε := by
  classical
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  set K : Set M := tsupport φ with hK_def
  have hK_compact : IsCompact K := hφ_supp
  have hμK_lt : μ K < ⊤ := hK_compact.measure_lt_top
  have hμK_ne : μ K ≠ ⊤ := hμK_lt.ne
  -- Bound `μ K ^ (1/p)`.
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
  have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp'
  have hμK_pow_ne : μ K ^ (p.toReal⁻¹) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr (le_of_lt hp_toReal_pos)) hμK_ne
  set factor : ℝ≥0∞ := μ K ^ (p.toReal⁻¹) with hfactor_def
  have hfactor_ne_top : factor ≠ ⊤ := hμK_pow_ne
  -- Choose `δ : ℝ` so small that `factor * ENNReal.ofReal δ ≤ ε`.
  -- The explicit choice works because `factor < ⊤` and `ε ≠ 0`.
  have hchoice :
      ∃ δ : ℝ, 0 < δ ∧ factor * ENNReal.ofReal δ ≤ ε := by
    -- If `factor = 0`, any positive `δ` works (since `0 * _ = 0 ≤ ε`).
    by_cases hfactor_zero : factor = 0
    · exact ⟨1, zero_lt_one, by
        rw [hfactor_zero, zero_mul]
        exact zero_le _⟩
    -- Otherwise, `0 < factor < ⊤`.
    have hfactor_pos : 0 < factor := by
      exact lt_of_le_of_ne (zero_le _) (Ne.symm hfactor_zero)
    -- Case on whether `ε = ⊤`.
    by_cases hε_top : ε = ⊤
    · refine ⟨1, zero_lt_one, ?_⟩
      rw [hε_top]; exact le_top
    · -- `ε < ⊤` and `factor < ⊤`.
      have hε_lt : ε < ⊤ := lt_top_iff_ne_top.mpr hε_top
      have hε_toReal_pos : 0 < ε.toReal := by
        rw [ENNReal.toReal_pos_iff]
        exact ⟨lt_of_le_of_ne (zero_le _) (Ne.symm hε), hε_lt⟩
      have hfactor_toReal_pos : 0 < factor.toReal := by
        rw [ENNReal.toReal_pos_iff]
        exact ⟨hfactor_pos, lt_top_iff_ne_top.mpr hfactor_ne_top⟩
      -- Pick δ = ε.toReal / (2 * factor.toReal).
      set δ : ℝ := ε.toReal / (2 * factor.toReal) with hδ_eq
      have hδ_pos : 0 < δ := by positivity
      refine ⟨δ, hδ_pos, ?_⟩
      -- Need: factor * ENNReal.ofReal δ ≤ ε.
      have hmul :
          factor * ENNReal.ofReal δ =
            ENNReal.ofReal (factor.toReal * δ) := by
        conv_lhs => rw [← ENNReal.ofReal_toReal hfactor_ne_top]
        rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      rw [hmul]
      -- And `factor.toReal * δ = ε.toReal / 2 ≤ ε.toReal`.
      have hprod : factor.toReal * δ = ε.toReal / 2 := by
        rw [hδ_eq]
        field_simp
      rw [hprod]
      have h1 : ENNReal.ofReal (ε.toReal / 2) ≤ ENNReal.ofReal ε.toReal := by
        refine ENNReal.ofReal_le_ofReal ?_
        linarith
      calc ENNReal.ofReal (ε.toReal / 2)
          ≤ ENNReal.ofReal ε.toReal := h1
        _ = ε := ENNReal.ofReal_toReal hε_top
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hchoice
  -- Now apply the uniform approximation result.
  obtain ⟨f, hf_approx, hf_supp_le⟩ :=
    exists_contMDiff_uniform_approx_sub_compact_support (I := I) (M := M)
      hφ_cont hδ_pos
  -- Set `h := φ - (f : M → ℝ)`. Want: `eLpNorm h p μ ≤ ε`.
  set h : M → ℝ := φ - (f : M → ℝ) with hh_def
  -- Pointwise bound `|h x| ≤ δ`.
  have h_bound : ∀ x : M, ‖h x‖ ≤ δ := by
    intro x
    have := hf_approx x
    -- `|f x - φ x| < δ` implies `|φ x - f x| < δ`.
    rw [Real.norm_eq_abs]
    change |φ x - (f : M → ℝ) x| ≤ δ
    have habs : |(f : M → ℝ) x - φ x| = |φ x - (f : M → ℝ) x| := abs_sub_comm _ _
    linarith [this, habs.symm.le]
  -- Support of `h` is contained in `K = tsupport φ`.
  have h_supp : ∀ x : M, x ∉ K → h x = 0 := by
    intro x hx
    -- `x ∉ tsupport φ` implies `x ∉ support φ`, so `φ x = 0`.
    have hφx : φ x = 0 := by
      by_contra hne
      exact hx (subset_tsupport φ hne)
    -- Also `support f ⊆ support φ`, so `x ∉ support φ` implies `x ∉ support f`,
    -- i.e. `f x = 0`.
    have hfx : (f : M → ℝ) x = 0 := by
      by_contra hne
      have : x ∈ Function.support ((f : M → ℝ)) := hne
      have : x ∈ Function.support φ := hf_supp_le this
      exact this hφx
    simp [h, hφx, hfx]
  -- Measurability of `h = φ - (f : M → ℝ)` (strong, as both are continuous).
  have h_meas : AEStronglyMeasurable h μ := by
    apply Continuous.aestronglyMeasurable
    exact hφ_cont.sub f.contMDiff.continuous
  -- Apply the eLpNorm estimator.
  have h_estimate := eLpNorm_le_of_bound_and_support_le_measure (I := I) (M := M) g
    (p := p) (h := h) h_meas (le_of_lt hδ_pos) h_bound hK_compact h_supp
  -- Combine with `factor * ENNReal.ofReal δ ≤ ε`.
  have hμK_eq : μ K ^ (p.toReal⁻¹) = factor := rfl
  refine ⟨f, ?_, ?_⟩
  · -- Membership: `tsupport f ⊆ tsupport φ` is compact.
    change HasCompactSupport ((f : M → ℝ))
    refine HasCompactSupport.mono' (f := φ) hφ_supp ?_
    intro x hx
    -- `hx : x ∈ support (f : M → ℝ)`. Goal: `x ∈ tsupport φ`.
    have : x ∈ Function.support φ := hf_supp_le hx
    exact subset_tsupport φ this
  · calc
      eLpNorm h p μ ≤ μ K ^ (p.toReal⁻¹) * ENNReal.ofReal δ := h_estimate
      _ = factor * ENNReal.ofReal δ := by rw [hμK_eq]
      _ ≤ ε := hδ_bound

/-- Density of compactly-supported smooth scalar functions in `L^p`, stated in
the form: for every `u ∈ Lp ℝ p μ` and every `ε > 0`, there exists `f : C^∞⟮I,
M; ℝ⟯` with compact support such that the `L^p` distance between `u` and the
`L^p` class of `f` is less than `ε`. Here `μ` is the Riemannian volume measure
of the smooth Riemannian metric `g`. -/
theorem compactlySupportedSmoothFunctions_denseRange_in_Lp
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    ∀ (u : MeasureTheory.Lp ℝ p (riemannianVolumeMeasure (I := I) (M := M) g))
      {ε : ℝ} (_hε : 0 < ε),
    ∃ (f : C^∞⟮I, M; ℝ⟯) (hmem : f ∈ compactlySupportedSmoothFunctions I M),
      ‖u - (compactlySupportedSmoothFunctions_memLp (I := I) (M := M) g hmem).toLp
        (f : M → ℝ)‖ < ε := by
  intro u ε hε
  classical
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  haveI : IsLocallyFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
  haveI : (riemannianVolumeMeasure (I := I) (M := M) g).Regular :=
    riemannianVolumeMeasure_regular (I := I) (M := M) g
  haveI : LocallyCompactSpace M := locallyCompactSpace_of_chartedSpace E H I M
  -- We aim for `eLpNorm (u - fLp) ≤ ENNReal.ofReal (ε/2)` and then
  -- conclude `‖u - fLp‖ ≤ ε/2 < ε` in the real-valued norm.
  let μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  have hμ_def : μ = riemannianVolumeMeasure (I := I) (M := M) g := rfl
  have hε2_pos : 0 < ε / 2 := by linarith
  have hε4_pos : 0 < ε / 4 := by linarith
  have hε4_enn_ne : ENNReal.ofReal (ε / 4) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hε4_pos
  have hu_mem : MemLp ((u : M → ℝ)) p μ := Lp.memLp u
  -- Step 1: continuous compactly-supported approximator within ε/4.
  obtain ⟨φ, φ_supp, φ_approx, φ_cont, _φ_mem⟩ :=
    hu_mem.exists_hasCompactSupport_eLpNorm_sub_le (μ := μ) hp' hε4_enn_ne
  -- Step 2: smooth compactly-supported approximator of φ within ε/4.
  obtain ⟨f, hf_mem, f_approx⟩ :=
    exists_smoothCompactSupport_eLpNorm_sub_le_of_continuous
      (I := I) (M := M) g hp hp' φ_cont φ_supp hε4_enn_ne
  refine ⟨f, hf_mem, ?_⟩
  -- Identify `(f : M → ℝ)` and `(fLp : M → ℝ)` a.e.
  set fLp := (compactlySupportedSmoothFunctions_memLp (I := I) (M := M) g hf_mem).toLp
      ((f : M → ℝ))
  -- `fLp.1 =ᵐ[μ] f`.
  have h_fLp_eq : (fLp : M → ℝ) =ᵐ[μ] ((f : M → ℝ)) :=
    MemLp.coeFn_toLp _
  -- `(u - fLp : Lp ℝ p μ) : M → ℝ =ᵐ[μ] (u : M → ℝ) - (fLp : M → ℝ)`.
  have h_sub_coe : ((u - fLp : Lp ℝ p μ) : M → ℝ) =ᵐ[μ]
      (u : M → ℝ) - (fLp : M → ℝ) := Lp.coeFn_sub u fLp
  -- Hence `(u - fLp : Lp ℝ p μ) : M → ℝ =ᵐ[μ] (u : M → ℝ) - (f : M → ℝ)`.
  have h_sub_eq_ae : ((u - fLp : Lp ℝ p μ) : M → ℝ) =ᵐ[μ]
      (u : M → ℝ) - (f : M → ℝ) := by
    filter_upwards [h_sub_coe, h_fLp_eq] with x hsub hf
    rw [hsub]; simp [hf]
  have heLp_eq : eLpNorm ((u - fLp : Lp ℝ p μ) : M → ℝ) p μ =
      eLpNorm ((u : M → ℝ) - (f : M → ℝ)) p μ :=
    eLpNorm_congr_ae h_sub_eq_ae
  -- Triangle inequality: `eLpNorm (u - f) ≤ eLpNorm (u - φ) + eLpNorm (φ - f)`.
  have h_u_minus_φ_aem : AEStronglyMeasurable ((u : M → ℝ) - φ) μ :=
    hu_mem.1.sub φ_cont.aestronglyMeasurable
  have h_φ_minus_f_aem : AEStronglyMeasurable (φ - (f : M → ℝ)) μ :=
    φ_cont.aestronglyMeasurable.sub f.contMDiff.continuous.aestronglyMeasurable
  have htri_raw := eLpNorm_add_le (p := p) (μ := μ)
    h_u_minus_φ_aem h_φ_minus_f_aem hp
  have h_sum_eq : ((u : M → ℝ) - φ) + (φ - (f : M → ℝ)) =
      (u : M → ℝ) - (f : M → ℝ) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have htri : eLpNorm ((u : M → ℝ) - (f : M → ℝ)) p μ ≤
      eLpNorm ((u : M → ℝ) - φ) p μ + eLpNorm (φ - (f : M → ℝ)) p μ := by
    rw [← h_sum_eq]; exact htri_raw
  -- Combine bounds.
  have hsum_bound : eLpNorm ((u : M → ℝ) - (f : M → ℝ)) p μ ≤
      ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
    htri.trans (add_le_add φ_approx f_approx)
  have h_ofReal_add : ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) =
      ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_add (le_of_lt hε4_pos) (le_of_lt hε4_pos)]
    ring_nf
  have hsum_bound' : eLpNorm ((u : M → ℝ) - (f : M → ℝ)) p μ ≤
      ENNReal.ofReal (ε / 2) := hsum_bound.trans_eq h_ofReal_add
  have h_fLp_bound : eLpNorm ((u - fLp : Lp ℝ p μ) : M → ℝ) p μ ≤
      ENNReal.ofReal (ε / 2) := by
    rw [heLp_eq]; exact hsum_bound'
  -- Translate to `‖u - fLp‖ ≤ ε / 2`.
  have hnorm_def : ‖u - fLp‖ = (eLpNorm (⇑(u - fLp)) p μ).toReal := Lp.norm_def _
  have h_ofReal_ne_top : ENNReal.ofReal (ε / 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_toReal_bound : (eLpNorm ((u - fLp : Lp ℝ p μ) : M → ℝ) p μ).toReal ≤ ε / 2 := by
    have := ENNReal.toReal_mono h_ofReal_ne_top h_fLp_bound
    calc (eLpNorm ((u - fLp : Lp ℝ p μ) : M → ℝ) p μ).toReal
        ≤ (ENNReal.ofReal (ε / 2)).toReal := this
      _ = ε / 2 := ENNReal.toReal_ofReal (le_of_lt hε2_pos)
  calc ‖u - fLp‖ = (eLpNorm ((u - fLp : Lp ℝ p μ) : M → ℝ) p μ).toReal := hnorm_def
    _ ≤ ε / 2 := h_toReal_bound
    _ < ε := by linarith

/-- `Dense`-image formulation of the density result: the range of the canonical
map `compactlySupportedSmoothFunctions I M → Lp ℝ p μ` has dense image. -/
theorem compactlySupportedSmoothFunctions_dense_image_in_Lp
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (hp' : p ≠ ⊤) :
    Dense (Set.range
      (fun f : compactlySupportedSmoothFunctions I M =>
        ((compactlySupportedSmoothFunctions_memLp (I := I) (M := M) (p := p) g f.2).toLp
          ((f : C^∞⟮I, M; ℝ⟯) : M → ℝ) :
            MeasureTheory.Lp ℝ p (riemannianVolumeMeasure (I := I) (M := M) g)))) := by
  rw [Metric.dense_iff]
  intro u r hr
  -- `‖u - fLp‖ < r` is the existence statement.
  obtain ⟨f, hf_mem, hbound⟩ :=
    compactlySupportedSmoothFunctions_denseRange_in_Lp (I := I) (M := M)
      g hp.out hp' u hr
  refine ⟨
    (compactlySupportedSmoothFunctions_memLp (I := I) (M := M) (p := p) g hf_mem).toLp
      ((f : C^∞⟮I, M; ℝ⟯) : M → ℝ),
    ?_, ?_⟩
  · -- In the open ball of center `u` and radius `r`, via distance = norm of diff.
    rw [Metric.mem_ball, dist_comm]
    have hdist : dist u ((compactlySupportedSmoothFunctions_memLp
        (I := I) (M := M) (p := p) g hf_mem).toLp
      ((f : C^∞⟮I, M; ℝ⟯) : M → ℝ)) = ‖u - _‖ := dist_eq_norm u _
    rw [hdist]; exact hbound
  · exact ⟨⟨f, hf_mem⟩, rfl⟩

end LpDensity

end L2
end Integral
end DifferentialGeometry

end
