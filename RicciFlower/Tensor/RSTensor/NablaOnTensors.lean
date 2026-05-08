import RicciFlower.Tensor.RSTensor.LieDerivative
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# Covariant Derivative on Realized Mixed Tensors

This file contains the realized counterpart of the earlier fixed-vector-space
tensor-derivative layer.  It starts from
mathlib's bundled `CovariantDerivative` on the tangent bundle, extracts the
local chart connection endomorphism `Γ_X`, and feeds it into the model formula
for `(r,s)` tensor fields.

The Lie derivative file owns the shared slot-correction algebra.  This file
owns the interpretation of that algebra as a covariant derivative.
-/

namespace TensorLieDeriv

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section ModelCovariantDerivative

/-- Pointwise model formula for the covariant derivative of a covariant tensor.

The input `dα_X` is the first-order derivative of the tensor components in the
direction `X`, while `ΓX` is the connection endomorphism acting on each input
slot. -/
def covariantDeriv_tensor0SModelAt (s : ℕ)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  dα_X - lieDeriv_correction s ΓX α

omit [CompleteSpace 𝕜] in
@[simp] lemma covariantDeriv_tensor0SModelAt_apply (s : ℕ)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α =
      dα_X - lieDeriv_correction s ΓX α := by
  rfl

/-- Model-space covariant derivative of a covariant tensor field.

This is the chart-level formula
`∇_X α = Dα(X) - Σᵢ α(..., Γ_X -, ...)`. -/
def covariantDeriv_tensor0SModel (s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s
    (fderiv 𝕜 α x (X x)) (ΓX x) (α x)

/-- Within-set variant of `covariantDeriv_tensor0SModel`. -/
def covariantDeriv_tensor0SModelWithin (s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (u : Set E) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s
    (fderivWithin 𝕜 α u x (X x)) (ΓX x) (α x)

/-- Pointwise model formula for the covariant derivative of a mixed `(r,s)` tensor.

In the `Hom((0,r),(0,s))` model the connection acts on output covariant slots
with a minus sign and on input covariant slots with a plus sign. For `r = 1`,
`s = 0`, this recovers the usual `D Y(X) + Γ_X Y` vector-field formula under
the vector-as-`Hom(V*, 𝕜)` identification. -/
def covariantDeriv_tensorRSModelAt (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E) :
    TensorRSModel r s 𝕜 E :=
  dT_X
    - (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s ΓX).comp T
    + T.comp (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r ΓX)

@[simp] theorem covariantDeriv_tensorRSModelAt_apply (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E) :
    covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s dT_X ΓX T =
      dT_X
        - (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s ΓX).comp T
        + T.comp (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r ΓX) := by
  rfl

/-- Model-space covariant derivative of a mixed `(r,s)` tensor field. -/
def covariantDeriv_tensorRSModel (r s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (T : E → TensorRSModel r s 𝕜 E) (x : E) :
    TensorRSModel r s 𝕜 E :=
  covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s
    (fderiv 𝕜 T x (X x)) (ΓX x) (T x)

/-- Within-set variant of `covariantDeriv_tensorRSModel`. -/
def covariantDeriv_tensorRSModelWithin (r s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (T : E → TensorRSModel r s 𝕜 E) (u : Set E) (x : E) :
    TensorRSModel r s 𝕜 E :=
  covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s
    (fderivWithin 𝕜 T u x (X x)) (ΓX x) (T x)

/- Reusable slot-correction Leibniz rule for the covariant tensor product.

This is the same algebra proved for Lie derivatives; the only semantic change
is that `ΓX` is read as the connection endomorphism in the `X` direction. -/
omit [CompleteSpace 𝕜] in
lemma covariantSlotCorrection_modelProduct (s q : ℕ) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (β : Tensor0SModel (𝕜 := 𝕜) (E := E) q) :
    lieDeriv_correction (s + q) ΓX
        (Bundle.continuousMultilinearMap.modelProduct s q α β) =
      Bundle.continuousMultilinearMap.modelProduct s q
          (lieDeriv_correction s ΓX α) β +
        Bundle.continuousMultilinearMap.modelProduct s q
          α (lieDeriv_correction q ΓX β) :=
  lieDeriv_correction_modelProduct (𝕜 := 𝕜) (E := E) s q ΓX α β

end ModelCovariantDerivative

section TangentCovariantDerivative

variable [IsManifold I 1 M]

/-- The base tangent-vector covariant derivative, with mathlib's argument order exposed.

`covariantDeriv_vectorField cov X Y x` is `(∇_X Y)(x)`, implemented as
`cov Y x (X x)`. -/
def covariantDeriv_vectorField
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y : (x : M) → TangentSpace I x) (x : M) :
    TangentSpace I x :=
  cov Y x (X x)

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp] lemma covariantDeriv_vectorField_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y : (x : M) → TangentSpace I x) (x : M) :
    covariantDeriv_vectorField (I := I) cov X Y x = cov Y x (X x) := by
  rfl

/-- The tangent field whose coordinates in the tangent-bundle trivialization centered at `x₀`
are the constant vector `v`. -/
noncomputable def tangentConstInChart (x₀ : M) (v : E) (p : M) :
    TangentSpace I p :=
  (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp] lemma tangentConstInChart_apply (x₀ : M) (v : E) (p : M) :
    tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v p =
      (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v := by
  rfl

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
lemma tangentConstInChart_add (x₀ : M) (v w : E) :
    (tangentConstInChart x₀ (v + w) : (p : M) → TangentSpace I p) =
      (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) +
        tangentConstInChart x₀ w := by
  funext p
  change (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p (v + w) =
    (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v +
      (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p w
  exact map_add _ _ _

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
lemma tangentConstInChart_smul (x₀ : M) (a : 𝕜) (v : E) :
    (tangentConstInChart x₀ (a • v) : (p : M) → TangentSpace I p) =
      a • (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) := by
  funext p
  change (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p (a • v) =
    a • (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v
  exact map_smul _ _ _

section ConnectionEndomorphism

variable [IsManifold I 2 M]

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
lemma mdifferentiableAt_tangentConstInChart_of_mem
    {x₀ p : M} (v : E)
    (hp : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    MDiffAt (T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p := by
  let e := trivializationAt E (TangentSpace I) x₀
  refine (e.mdifferentiableAt_section_iff I
    (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) hp).mpr ?_
  have hconst :
      (fun y : M =>
        (e ((T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) y)).2) =ᶠ[𝓝 p]
          fun _ : M => v := by
    filter_upwards [e.open_baseSet.mem_nhds hp] with y hy
    have hcoe : ⇑(e.linearMapAt 𝕜 y) = fun z => (e ⟨y, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := 𝕜) hy
    simpa [Bundle.Trivialization.continuousLinearMapAt_apply, hcoe] using
      (e.continuousLinearMapAt_symmL (R := 𝕜) hy v)
  exact hconst.mdifferentiableAt_iff.mpr mdifferentiableAt_const

/-- Local connection endomorphism in a chart, extracted from a mathlib covariant derivative.

At a chart point `y`, with `p = (extChartAt I x₀).symm y`, this is the model-space
endomorphism
`v ↦ trivialize_x₀ ((∇_X tangentConstInChart(x₀,v)) p)`.
It is set to zero off the chart target. -/
noncomputable def connectionEndomorphismInChart
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : (x : M) → TangentSpace I x) (x₀ : M) (y : E) :
    E →L[𝕜] E := by
  classical
  let e := trivializationAt E (TangentSpace I) x₀
  let p := (extChartAt I x₀).symm y
  refine LinearMap.toContinuousLinearMap ?_
  refine
    { toFun := fun v =>
        if y ∈ (extChartAt I x₀).target then
          e.continuousLinearMapAt 𝕜 p
            ((cov (tangentConstInChart x₀ v) p) (X p))
        else
          0
      map_add' := ?_
      map_smul' := ?_ }
  · intro v w
    by_cases hy : y ∈ (extChartAt I x₀).target
    · have hp_source : p ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
      have hp_base : p ∈ e.baseSet := by
        simpa [e, p, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
      have hv : MDiffAt
          (T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p :=
        mdifferentiableAt_tangentConstInChart_of_mem
          (x₀ := x₀) (p := p) v hp_base
      have hw : MDiffAt
          (T% (tangentConstInChart x₀ w : (p : M) → TangentSpace I p)) p :=
        mdifferentiableAt_tangentConstInChart_of_mem
          (x₀ := x₀) (p := p) w hp_base
      have hsection :
          (tangentConstInChart x₀ (v + w) : (p : M) → TangentSpace I p) =
            (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) +
              tangentConstInChart x₀ w :=
        tangentConstInChart_add x₀ v w
      have hcov :
          cov ((tangentConstInChart x₀ v : (p : M) → TangentSpace I p) +
              tangentConstInChart x₀ w) p =
            cov (tangentConstInChart x₀ v) p +
              cov (tangentConstInChart x₀ w) p :=
        cov.isCovariantDerivativeOnUniv.add hv hw
      rw [if_pos hy, if_pos hy, if_pos hy]
      rw [hsection, hcov]
      simp [map_add]
    · rw [if_neg hy, if_neg hy, if_neg hy]
      simp
  · intro a v
    by_cases hy : y ∈ (extChartAt I x₀).target
    · have hp_source : p ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
      have hp_base : p ∈ e.baseSet := by
        simpa [e, p, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
      have hv : MDiffAt
          (T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p :=
        mdifferentiableAt_tangentConstInChart_of_mem
          (x₀ := x₀) (p := p) v hp_base
      have hsection :
          (tangentConstInChart x₀ (a • v) : (p : M) → TangentSpace I p) =
            a • (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) :=
        tangentConstInChart_smul x₀ a v
      have hcov :
          cov (a • (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p =
            a • cov (tangentConstInChart x₀ v) p :=
        cov.isCovariantDerivativeOnUniv.smul_const a hv
      rw [if_pos hy, if_pos hy]
      rw [hsection, hcov]
      simp [map_smul]
    · rw [if_neg hy, if_neg hy]
      simp

@[simp] lemma connectionEndomorphismInChart_apply_of_mem
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : (x : M) → TangentSpace I x) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (v : E) :
    connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀ y v =
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜
        ((extChartAt I x₀).symm y)
        ((cov (tangentConstInChart x₀ v)
          ((extChartAt I x₀).symm y))
          (X ((extChartAt I x₀).symm y))) := by
  classical
  change (if y ∈ (extChartAt I x₀).target then
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜
        ((extChartAt I x₀).symm y)
        ((cov (tangentConstInChart x₀ v) ((extChartAt I x₀).symm y))
          (X ((extChartAt I x₀).symm y)))
    else 0) =
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜
        ((extChartAt I x₀).symm y)
        ((cov (tangentConstInChart x₀ v) ((extChartAt I x₀).symm y))
          (X ((extChartAt I x₀).symm y)))
  rw [if_pos hy]

@[simp] lemma connectionEndomorphismInChart_apply_of_notMem
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : (x : M) → TangentSpace I x) (x₀ : M) {y : E}
    (hy : y ∉ (extChartAt I x₀).target) (v : E) :
    connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀ y v = 0 := by
  classical
  change (if y ∈ (extChartAt I x₀).target then
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜
        ((extChartAt I x₀).symm y)
        ((cov (tangentConstInChart x₀ v) ((extChartAt I x₀).symm y))
          (X ((extChartAt I x₀).symm y)))
    else 0) = 0
  rw [if_neg hy]

end ConnectionEndomorphism

end TangentCovariantDerivative

section SmoothVectorFieldRSNabla

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

/-- Pointwise covariant derivative of a covariant `(0,s)` tensor field in a chosen chart,
with the local connection endomorphism supplied explicitly.

This is the covariant-tensor analogue of `mcovariantDeriv_tensorRSWithin`. It uses the
model formula `D_X alpha - correction_Gamma alpha` and then transports the result back
to the tensor fiber at `x0`. -/
noncomputable def mcovariantDeriv_tensor0SWithin (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (u : Set M) (x₀ : M) : Tensor0SSpace s I x₀ := by
  let X' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I)
  let α' : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
    fun y => tensor0SSpace_continuousLinearEquiv (I := I) s
      ((extChartAt I x₀).symm y) (α.toFun ((extChartAt I x₀).symm y))
  exact (tensor0SSpace_continuousLinearEquiv (I := I) s x₀).symm
    (covariantDeriv_tensor0SModelWithin s X' ΓX α'
      ((extChartAt I x₀).symm ⁻¹' u ∩ range I)
      (extChartAt I x₀ x₀))

/-- Pointwise covariant derivative of a covariant `(0,s)` tensor field in a chosen chart,
with supplied local connection endomorphism. -/
noncomputable def mcovariantDeriv_tensor0S (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (x₀ : M) : Tensor0SSpace s I x₀ :=
  mcovariantDeriv_tensor0SWithin (n := n) s X ΓX α univ x₀

/-- Pointwise covariant derivative of an `(r,s)` tensor field in a chosen chart,
with the local connection endomorphism supplied explicitly.

This mirrors `mlieDeriv_tensorRSWithin`, but the model formula uses a supplied
`ΓX : E → E →L[𝕜] E` instead of `fderivWithin X'`. For a genuine connection,
`ΓX y` should be the chart representative of `v ↦ ∇_X(constant v)` at the
model point `y`. The wrappers below use `connectionEndomorphismInChart` to extract
this endomorphism from a mathlib `CovariantDerivative`. -/
noncomputable def mcovariantDeriv_tensorRSWithin (r s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (u : Set M) (x₀ : M) : TensorRSSpace r s I x₀ := by
  let X' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I)
  let T' : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
    fun y => tensorRSSpace_continuousLinearEquiv (I := I) r s
      ((extChartAt I x₀).symm y) (T.toFun ((extChartAt I x₀).symm y))
  exact (tensorRSSpace_continuousLinearEquiv (I := I) r s x₀).symm
    (covariantDeriv_tensorRSModelWithin r s X' ΓX T'
      ((extChartAt I x₀).symm ⁻¹' u ∩ range I)
      (extChartAt I x₀ x₀))

/-- Pointwise covariant derivative of an `(r,s)` tensor field in a chosen chart,
with supplied local connection endomorphism. -/
noncomputable def mcovariantDeriv_tensorRS (r s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (x₀ : M) : TensorRSSpace r s I x₀ :=
  mcovariantDeriv_tensorRSWithin (n := n) r s X ΓX T univ x₀

section ExtractedConnection

variable [IsManifold I 2 M]

/-- Pointwise covariant derivative of a covariant `(0,s)` tensor field in a chosen chart,
extracting the local connection endomorphism from a mathlib `CovariantDerivative`. -/
noncomputable def mcovariantDeriv_tensor0SWithinFromConnection (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (u : Set M) (x₀ : M) : Tensor0SSpace s I x₀ :=
  mcovariantDeriv_tensor0SWithin (n := n) s X
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀) α u x₀

/-- Pointwise covariant derivative of a covariant `(0,s)` tensor field in a chosen chart,
extracting the local connection endomorphism from a mathlib `CovariantDerivative`. -/
noncomputable def mcovariantDeriv_tensor0SFromConnection (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (x₀ : M) : Tensor0SSpace s I x₀ :=
  mcovariantDeriv_tensor0SWithinFromConnection (n := n) s cov X α univ x₀

/-- Pointwise covariant derivative of an `(r,s)` tensor field in a chosen chart, extracting
the local connection endomorphism from a mathlib `CovariantDerivative`. -/
noncomputable def mcovariantDeriv_tensorRSWithinFromConnection (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (u : Set M) (x₀ : M) : TensorRSSpace r s I x₀ :=
  mcovariantDeriv_tensorRSWithin (n := n) r s X
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀) T u x₀

/-- Pointwise covariant derivative of an `(r,s)` tensor field in a chosen chart, extracting
the local connection endomorphism from a mathlib `CovariantDerivative`. -/
noncomputable def mcovariantDeriv_tensorRSFromConnection (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (x₀ : M) : TensorRSSpace r s I x₀ :=
  mcovariantDeriv_tensorRSWithinFromConnection (n := n) r s cov X T univ x₀

end ExtractedConnection

end SmoothVectorFieldRSNabla

end

end TensorLieDeriv

namespace Tensor0SBundle

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Function TensorLieDeriv
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [CompleteSpace 𝕜]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (⊤ : WithTop ℕ∞) M]
variable [IsManifold I ((⊤ : WithTop ℕ∞) + 1) M]

/-- Raw pointwise covariant derivative of a covariant tensor field along a smooth vector
field, using a realized connection. The bundled section version is `nabla0S`. -/
noncomputable def nabla0SFun (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s)
    (x : M) : Tensor0SSpace s I x :=
  TensorLieDeriv.mcovariantDeriv_tensor0SFromConnection
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (⊤ : WithTop ℕ∞)) s cov X α x

/-- Raw pointwise covariant derivative of a mixed tensor field along a smooth vector
field, using a realized connection. The bundled section version is `nablaRS`. -/
noncomputable def nablaRSFun (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) r s)
    (x : M) : TensorRSSpace r s I x :=
  TensorLieDeriv.mcovariantDeriv_tensorRSFromConnection
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (⊤ : WithTop ℕ∞)) r s cov X T x

@[simp] theorem nabla0SFun_apply (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s)
    (x : M) :
    nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α x =
      TensorLieDeriv.mcovariantDeriv_tensor0SFromConnection
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (⊤ : WithTop ℕ∞)) s cov X α x := rfl

@[simp] theorem nablaRSFun_apply (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) r s)
    (x : M) :
    nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T x =
      TensorLieDeriv.mcovariantDeriv_tensorRSFromConnection
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (⊤ : WithTop ℕ∞)) r s cov X T x := rfl

/-- Regularity predicate for the raw covariant derivative of a covariant tensor field.

This is kept explicit so `nabla0S` never hides the analytic smoothness proof. -/
abbrev Nabla0SRegular (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s) : Prop :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel s 𝕜 E)) (⊤ : WithTop ℕ∞)
    (fun x : M =>
      (⟨x, nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x⟩ :
        TotalSpace (Tensor0SModel s 𝕜 E) (fun x : M => Tensor0SSpace s I x)))

/-- Regularity predicate for the raw covariant derivative of a mixed tensor field.

This is kept explicit so `nablaRS` never hides the analytic smoothness proof. -/
abbrev NablaRSRegular (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) r s) : Prop :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ContMDiff I (I.prod 𝓘(𝕜, TensorRSModel r s 𝕜 E)) (⊤ : WithTop ℕ∞)
    (fun x : M =>
      (⟨x, nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x⟩ :
        TotalSpace (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x)))

/-- Bundled covariant derivative of a covariant tensor field. The smoothness proof is an
explicit argument; use `nabla0S_reg` once the analytic regularity bridge is available. -/
noncomputable def nabla0S (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s)
    (hreg : Nabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ⟨nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α, hreg⟩

/-- Bundled covariant derivative of a mixed tensor field. The smoothness proof is an
explicit argument; use `nablaRS_reg` once the analytic regularity bridge is available. -/
noncomputable def nablaRS (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) r s)
    (hreg : NablaRSRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) r s :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ⟨nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T, hreg⟩

@[simp] theorem nabla0S_apply (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s)
    (hreg : Nabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α)
    (x : M) :
    nabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α hreg x =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α x := rfl

@[simp] theorem nablaRS_apply (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) r s)
    (hreg : NablaRSRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T)
    (x : M) :
    nablaRS (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T hreg x =
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T x := rfl

/-- Smoothness target for covariant tensor derivatives.

Expected proof: trivialize the tensor bundle, unfold `nabla0SFun`, use the chart formula
for `mcovariantDeriv_tensor0SFromConnection`, and combine smoothness of the connection
endomorphism with the model-space derivative/correction smoothness lemmas. -/
theorem nabla0S_reg (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s) :
    Nabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α := by
  sorry

/-- Smoothness target for mixed tensor derivatives.

Expected proof: trivialize the Hom tensor bundle, unfold `nablaRSFun`, use the chart formula
for `mcovariantDeriv_tensorRSFromConnection`, and combine smoothness of the connection
endomorphism with the model-space derivative/correction smoothness lemmas. -/
theorem nablaRS_reg (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) r s) :
    NablaRSRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T := by
  sorry

end

end Tensor0SBundle
