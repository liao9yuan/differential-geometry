import DifferentialGeometry.Integral.Connection.TensorRSNabla
import DifferentialGeometry.Integral.Connection.ConnectionLaplacian
import DifferentialGeometry.Integral.Connection.Bochner
import DifferentialGeometry.Integral.L2.SmoothSections.Defs

/-!
# The connection Laplacian on `(r, s)`-tensor sections

For a smooth Riemannian metric `g` on a manifold `M` without boundary, the
connection Laplacian on the `(r, s)`-tensor bundle is the metric trace of the
second covariant derivative,
$$
  (\Delta_\nabla T)(x)
    := \mathrm{tr}_g\bigl(W \mapsto \nabla_W \nabla T\bigr)(x).
$$
In a `g_x`-orthonormal frame `B_i` of the tangent space at `x`, the trace
evaluates to
$$
  (\Delta_\nabla T)(x)
    = \sum_i \bigl(\nabla_{B_i x}\,\nabla_{B_i} T - \nabla_{(\nabla_{B_i} B_i)(x)} T\bigr).
$$

This file packages the operator on raw `(r, s)`-tensor sections, traced against
the smooth orthonormal frame at the centre point (`smoothOrthoFrame g x`). The
frame is `g_x`-orthonormal at `x` and `C^∞` as a tangent-bundle section family
(see `RicciIdentitySmoothFrame.lean`), which makes the value of the trace at
`x` the textbook value of the connection Laplacian on tensor sections.

## Main definitions

* `rawTensorConnLap g r s T x` — the pointwise value of the connection
  Laplacian on a raw `(r, s)`-tensor section `T : Π b, TensorRSSpace r s I b`,
  computed against the smooth orthonormal frame at `x`.

## Main results

* `rawTensorConnLap_smul` — `ℝ`-linearity on scalars.
* `rawTensorConnLap_add` — additivity on raw smooth sections.
* `rawTensorConnLap_zero` — vanishing on the zero section.
* `rawTensorConnLap_smooth` — for a smooth raw `(r, s)`-tensor section `T`,
  the raw connection Laplacian is a smooth section.

## Sign convention

The geometer convention is used: `Δ_g = div ∘ grad`, with spectrum in
`(-∞, 0]` on closed manifolds. The connection Laplacian inherits this sign
through the trace formula. This is the same sign convention used by the
scalar / vector / 1-form connection Laplacians in `ConnectionLaplacian.lean`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-! ## Part 1: the raw `(r, s)`-tensor connection Laplacian

The raw operator works on dependent-function sections
`T : Π b, TensorRSSpace r s I b`. The trace formula is stated in maximum
generality before any smoothness or compact-support hypothesis is imposed. -/

/-- **Raw connection Laplacian on a `(r, s)`-tensor section.** Given a smooth
Riemannian metric `g` on `M`, ranks `(r, s)`, and a raw `(r, s)`-tensor section
`T : Π b, TensorRSSpace r s I b`, the value at `x` is the metric trace of the
second covariant derivative, computed against the smooth orthonormal frame at
`x`:
$$
  (\Delta_\nabla T)(x)
    := \sum_i \bigl(\nabla^{(r,s)}_{B_i x}\,\nabla^{(r,s)}_{B_i} T
      - \nabla^{(r,s)}_{(\nabla_{B_i} B_i)(x)} T\bigr).
$$
Here `B_i = smoothOrthoFrame g x i` and `∇^{(r,s)}` abbreviates the
`(r, s)`-tensor covariant derivative
`TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita g)`. -/
def rawTensorConnLap
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) T) x
        (smoothOrthoFrame (I := I) g x i x) -
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        T x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))

/-- The defining identity for `rawTensorConnLap`. -/
@[simp] lemma rawTensorConnLap_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap (I := I) g r s T x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i) T) x
            (smoothOrthoFrame (I := I) g x i x) -
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            T x
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x
              (smoothOrthoFrame (I := I) g x i x))) := rfl

/-! ## Part 2: vanishing on the zero section

If `T` is the identically zero raw section, then `rawTensorConnLap T x = 0`
at every `x`. This is immediate from `cov.zero` applied twice. -/

/-- **Vanishing on the zero section.** The raw connection Laplacian of the
identically zero `(r, s)`-tensor section vanishes pointwise. -/
@[simp] theorem rawTensorConnLap_zero [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    rawTensorConnLap (I := I) g r s
        (fun _ : M => (0 : TensorRSSpace r s I _)) x = 0 := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  -- The covariant derivative is `ℝ`-linear: applied to the zero section yields zero.
  have h_zero_cov : cov.toFun (fun _ : M => (0 : TensorRSSpace r s I _)) =
      fun _ : M => (0 : TangentSpace I _ →L[ℝ] TensorRSSpace r s I _) := cov.zero
  unfold rawTensorConnLap
  refine Finset.sum_eq_zero ?_
  intro i _
  -- `covApply cov X 0 = fun y => cov.toFun 0 y (X y) = fun y => 0`.
  have h_covApply_zero : covApply cov (smoothOrthoFrame (I := I) g x i)
      (fun _ : M => (0 : TensorRSSpace r s I _)) =
      fun y : M => (0 : TensorRSSpace r s I y) := by
    funext y
    -- `covApply cov X 0 y = cov.toFun 0 y (X y)`.
    have : cov.toFun (fun _ : M => (0 : TensorRSSpace r s I _)) y = 0 :=
      congrArg (fun φ => φ y) h_zero_cov
    -- Apply the zero linear map to `(smoothOrthoFrame g x i y)`.
    change (cov.toFun (fun _ : M => (0 : TensorRSSpace r s I _)) y)
        (smoothOrthoFrame (I := I) g x i y) = 0
    rw [this]
    rfl
  rw [h_covApply_zero]
  -- The first term: `cov.toFun (0 section) x (B_i x) = 0`.
  have h_first_zero : cov.toFun (fun y : M => (0 : TensorRSSpace r s I y)) x
      (smoothOrthoFrame (I := I) g x i x) = 0 := by
    have : cov.toFun (fun y : M => (0 : TensorRSSpace r s I y)) x = 0 :=
      congrArg (fun φ => φ x) h_zero_cov
    rw [this]; rfl
  -- The second term: `cov.toFun (0 section) x (LeviCivita ...) = 0` similarly.
  have h_second_zero : cov.toFun (fun _ : M => (0 : TensorRSSpace r s I _)) x
      ((LeviCivita (I := I) g).toFun
        (smoothOrthoFrame (I := I) g x i) x
        (smoothOrthoFrame (I := I) g x i x)) = 0 := by
    have : cov.toFun (fun _ : M => (0 : TensorRSSpace r s I _)) x = 0 :=
      congrArg (fun φ => φ x) h_zero_cov
    rw [this]; rfl
  -- Combine: the summand is `0 - 0 = 0`.
  rw [h_first_zero, h_second_zero]
  simp

/-! ## Part 3: additivity on raw smooth sections

For raw smooth sections `T, T'`, the connection Laplacian is additive:
`rawTensorConnLap (T + T') = rawTensorConnLap T + rawTensorConnLap T'`. This
follows from the `IsCovariantDerivativeOn.add` identity applied twice and the
linearity of `ContinuousLinearMap.sub_apply / add_apply`. -/

/-- **Additivity on smooth raw sections.** For raw `(r, s)`-tensor sections
`T, T'` that are manifold-differentiable to all orders at `x`, the raw
connection Laplacian is additive at `x`. The exact differentiability needed at
`x` is `MDifferentiableAt` of `T`, `T'`, `T + T'`, and the corresponding
single-derivatives along each frame vector. -/
theorem rawTensorConnLap_add [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T T' : Π b : M, TensorRSSpace r s I b}
    (hT : ∀ x : M, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) x)
    (hT' : ∀ x : M, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T' y)) x)
    (hcovT : ∀ (x : M) (i : Fin (Module.finrank ℝ E)),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) T y)) x)
    (hcovT' : ∀ (x : M) (i : Fin (Module.finrank ℝ E)),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) T' y)) x)
    (x : M) :
    rawTensorConnLap (I := I) g r s (T + T') x =
      rawTensorConnLap (I := I) g r s T x +
        rawTensorConnLap (I := I) g r s T' x := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  -- Use `IsCovariantDerivativeOn.add` to split each first-derivative.
  have hcov_loc := cov.isCovariantDerivativeOn (s := (Set.univ : Set M))
  -- We need to show: ∑_i (terms with (T + T')) = ∑_i (terms with T) + ∑_i (terms with T')
  unfold rawTensorConnLap
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  -- The summand for (T + T') decomposes by linearity of cov:
  --   cov.toFun (covApply cov B (T + T')) x (B x) - cov.toFun (T + T') x (...)
  -- = (cov.toFun (covApply cov B T) x (B x) - cov.toFun T x (...))
  -- + (cov.toFun (covApply cov B T') x (B x) - cov.toFun T' x (...))
  -- The argument: `cov.toFun (σ + σ') x = cov.toFun σ x + cov.toFun σ' x`, hence
  -- applying at a vector gives the additivity of values.
  -- First, prove additivity of `cov.toFun T x` in T.
  have h_addT : cov.toFun (fun y => T y + T' y) x =
      cov.toFun T x + cov.toFun T' x := by
    -- `IsCovariantDerivativeOn.add` gives a pointwise identity.
    have h_add := hcov_loc.add (σ := T) (σ' := T') (hT x) (hT' x)
    -- h_add : cov.toFun (T + T') x = cov.toFun T x + cov.toFun T' x
    convert h_add using 1
  -- Second, prove additivity of `covApply cov X T` in T.
  have h_covApply_add : covApply cov (smoothOrthoFrame (I := I) g x i)
      (fun y => T y + T' y) =
      covApply cov (smoothOrthoFrame (I := I) g x i) T +
        covApply cov (smoothOrthoFrame (I := I) g x i) T' := by
    funext y
    -- `covApply cov X (T + T') y = cov.toFun (T + T') y (X y)
    --   = (cov.toFun T y + cov.toFun T' y) (X y)
    --   = cov.toFun T y (X y) + cov.toFun T' y (X y).
    -- Use `IsCovariantDerivativeOn.add` at y. Note `T + T'` (the Pi-sum) is
    -- definitionally `fun y => T y + T' y`, but `IsCovariantDerivativeOn.add`
    -- is stated for the former, so we go via `show` and matching exactly.
    have h_add_at_y : cov.toFun (fun y => T y + T' y) y =
        cov.toFun T y + cov.toFun T' y := by
      change cov.toFun (T + T') y = cov.toFun T y + cov.toFun T' y
      exact hcov_loc.add (σ := T) (σ' := T') (hT y) (hT' y)
    change cov.toFun (fun y => T y + T' y) y (smoothOrthoFrame (I := I) g x i y) =
      covApply cov (smoothOrthoFrame (I := I) g x i) T y +
        covApply cov (smoothOrthoFrame (I := I) g x i) T' y
    rw [h_add_at_y]
    rfl
  -- Third, the second derivative of (T + T') along B_i is the sum.
  have h_second_deriv_add : cov.toFun
      (covApply cov (smoothOrthoFrame (I := I) g x i) (fun y => T y + T' y)) x =
      cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T) x +
        cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T') x := by
    rw [h_covApply_add]
    -- Apply IsCovariantDerivativeOn.add to the sum.
    exact hcov_loc.add (σ := covApply cov (smoothOrthoFrame (I := I) g x i) T)
      (σ' := covApply cov (smoothOrthoFrame (I := I) g x i) T')
      (hcovT x i) (hcovT' x i)
  -- Combine: substitute the additivity into the summand.
  change
    (cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i)
        (fun y => T y + T' y)) x
        (smoothOrthoFrame (I := I) g x i x) -
      cov.toFun (fun y => T y + T' y) x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x))) =
    (cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T) x
        (smoothOrthoFrame (I := I) g x i x) -
      cov.toFun T x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x))) +
    (cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T') x
        (smoothOrthoFrame (I := I) g x i x) -
      cov.toFun T' x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))
  rw [h_second_deriv_add, h_addT]
  -- Now use ContinuousLinearMap add_apply on both halves and rearrange.
  simp only [ContinuousLinearMap.add_apply]
  abel

/-! ## Part 4: scalar homogeneity

For a constant scalar `c`, the raw connection Laplacian satisfies
`rawTensorConnLap (c • T) = c • rawTensorConnLap T`. This follows from the
`IsCovariantDerivativeOn.smul_const` identity applied twice. -/

/-- **Scalar homogeneity on smooth raw sections.** For a raw `(r, s)`-tensor
section `T` and a constant `c : ℝ`, the raw connection Laplacian commutes
with scaling. -/
theorem rawTensorConnLap_smul [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b} (c : ℝ)
    (hT : ∀ x : M, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) x)
    (hcovT : ∀ (x : M) (i : Fin (Module.finrank ℝ E)),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) T y)) x)
    (x : M) :
    rawTensorConnLap (I := I) g r s (fun y => c • T y) x =
      c • rawTensorConnLap (I := I) g r s T x := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  have hcov_loc := cov.isCovariantDerivativeOn (s := (Set.univ : Set M))
  unfold rawTensorConnLap
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  -- The summand for `c • T` should be `c •` the original.
  -- First: `cov.toFun (c • T) x = c • cov.toFun T x`.
  have h_smulT : cov.toFun (fun y => c • T y) x = c • cov.toFun T x := by
    change cov.toFun (c • T) x = c • cov.toFun T x
    exact hcov_loc.smul_const (σ := T) c (hT x)
  -- Second: `covApply cov X (c • T) = c • covApply cov X T`.
  have h_covApply_smul : covApply cov (smoothOrthoFrame (I := I) g x i)
      (fun y => c • T y) =
      fun y => c • covApply cov (smoothOrthoFrame (I := I) g x i) T y := by
    funext y
    have h_smul_at_y : cov.toFun (fun y => c • T y) y = c • cov.toFun T y := by
      change cov.toFun (c • T) y = c • cov.toFun T y
      exact hcov_loc.smul_const (σ := T) c (hT y)
    change cov.toFun (fun y => c • T y) y (smoothOrthoFrame (I := I) g x i y) =
      c • covApply cov (smoothOrthoFrame (I := I) g x i) T y
    rw [h_smul_at_y]
    -- `(c • cov.toFun T y) (X y) = c • (cov.toFun T y (X y))`.
    rfl
  -- Third: `cov.toFun (c • covApply ... T) x = c • cov.toFun (covApply ... T) x`.
  have h_second_smul : cov.toFun
      (covApply cov (smoothOrthoFrame (I := I) g x i) (fun y => c • T y)) x =
      c • cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T) x := by
    rw [h_covApply_smul]
    exact hcov_loc.smul_const
      (σ := covApply cov (smoothOrthoFrame (I := I) g x i) T) c (hcovT x i)
  -- Combine: the summand for `c • T` is `c •` the summand for `T`.
  change
    (cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i)
        (fun y => c • T y)) x
        (smoothOrthoFrame (I := I) g x i x) -
      cov.toFun (fun y => c • T y) x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x))) =
    c • (cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T) x
        (smoothOrthoFrame (I := I) g x i x) -
      cov.toFun T x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))
  rw [h_second_smul, h_smulT]
  -- Both halves carry a factor of `c`; combine via continuous-linear-map smul.
  simp only [ContinuousLinearMap.smul_apply, smul_sub]

/-! ## Part 5: locality and support inclusion

The raw connection Laplacian is local in `T`: if `T` vanishes on an open
neighbourhood of `x` (and is manifold-differentiable everywhere), then
`rawTensorConnLap T x = 0`. This is the input to the compact-support
preservation lemma. -/

/-- **Locality of the first covariant derivative at a single point.** If a
raw section `T` vanishes on an open set `U` and `T` is manifold-differentiable
at the target point `y ∈ U`, then `cov.toFun T y = 0`.

This is a direct application of `IsCovariantDerivativeOn.congr_of_eventuallyEq`
to the zero section on the open neighbourhood `U`. The differentiability
witness is required only at `y`, not globally. -/
private lemma cov_eq_zero_of_eventually_zero_on_open
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x : M, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    (cov : CovariantDerivative I F V)
    {T : Π y : M, V y} {U : Set M}
    (hU_open : IsOpen U)
    (hT_zero : ∀ y ∈ U, T y = 0)
    {y : M} (hyU : y ∈ U)
    (hT_diff_y : MDifferentiableAt I (I.prod 𝓘(ℝ, F))
      (fun z : M => TotalSpace.mk' F (E := V) z (T z)) y) :
    cov.toFun T y = 0 := by
  classical
  -- `T y' = 0` for every `y' ∈ U`. So as a Pi-section, T agrees with 0 on U,
  -- and U is in `𝓝 y` since U is open and `y ∈ U`.
  have hU_nhds : U ∈ 𝓝 y := hU_open.mem_nhds hyU
  -- Pointwise-equal data on a neighbourhood: `T y' = (0 : V y')` for `y' ∈ U`.
  -- We use the dependent-type form `∀ᶠ y' in 𝓝 y, T y' = 0`, which is what
  -- `IsCovariantDerivativeOn.congr_of_eventuallyEq` expects.
  have hT_eq : ∀ᶠ y' in 𝓝 y, T y' = (fun y'' : M => (0 : V y'')) y' :=
    Filter.Eventually.mono (Filter.eventually_of_mem hU_nhds (fun y' hy' => hy'))
      (fun y' hy' => hT_zero y' hy')
  have hzero_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, F))
      (fun y' : M => TotalSpace.mk' F (E := V) y' (0 : V y')) y :=
    mdifferentiableAt_zeroSection (𝕜 := ℝ) (F := F) (E := V) (IB := I)
  have huniv : (Set.univ : Set M) ∈ 𝓝 y := Filter.univ_mem
  have h_eq : cov.toFun T y =
      cov.toFun (fun y' : M => (0 : V y')) y :=
    cov.isCovariantDerivativeOn.congr_of_eventuallyEq hT_diff_y hzero_diff
      huniv hT_eq
  rw [h_eq]
  -- `cov 0 = 0` pointwise.
  exact congrArg (fun φ => φ y) cov.zero

/-- **Vanishing of `rawTensorConnLap` on a section that vanishes on a
neighbourhood of `x`.** If `T` vanishes on an open neighbourhood of `x` and
admits `MDifferentiableAt` witnesses at `x` (for `T` itself) and at the
target point `x` for the first covariant derivative section
`covApply cov B_i T`, then the raw connection Laplacian of `T` vanishes at
`x`.

The two `MDifferentiableAt` witnesses are required only at `x`: locality
inside the open neighbourhood `U` reduces both quantities to the zero
section's covariant derivative, which vanishes by `cov.zero`. -/
theorem rawTensorConnLap_eq_zero_of_eventually_zero [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    {x : M} {U : Set M} (hU_open : IsOpen U) (hxU : x ∈ U)
    (hT_zero : ∀ y ∈ U, T y = 0)
    (hT_diff_x : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z (T z)) x)
    (hcovT_diff_x : ∀ i : Fin (Module.finrank ℝ E),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) T z)) x) :
    rawTensorConnLap (I := I) g r s T x = 0 := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  unfold rawTensorConnLap
  refine Finset.sum_eq_zero ?_
  intro i _
  -- The second term vanishes because `cov.toFun T x = 0` by locality at `x`.
  have h_second_zero : cov.toFun T x = 0 :=
    cov_eq_zero_of_eventually_zero_on_open (I := I)
      (V := fun w : M => TensorRSSpace r s I w)
      cov hU_open hT_zero hxU hT_diff_x
  -- For the first term we need `cov.toFun (covApply cov B_i T) x = 0`.
  -- Step A: show `covApply cov B_i T y = 0` for every `y ∈ U`. This requires
  -- `MDifferentiableAt` of `T` at each such `y`. We construct such a witness
  -- from the fact that `T y = 0` for `y ∈ U`: on the open set `U`, the
  -- function `y ↦ T y` agrees with `y ↦ 0`, so the total-space form is
  -- `MDifferentiableAt` at every `y ∈ U` by congr with the zero section.
  have h_T_diff_on_U : ∀ y ∈ U, MDifferentiableAt I
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z (T z)) y := by
    intro y hyU
    have hU_nhds_y : U ∈ 𝓝 y := hU_open.mem_nhds hyU
    have hzero_total_diff_y : MDifferentiableAt I
        (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          (0 : TensorRSSpace r s I z)) y :=
      mdifferentiableAt_zeroSection (𝕜 := ℝ)
        (F := TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) (IB := I)
    apply hzero_total_diff_y.congr_of_eventuallyEq
    filter_upwards [hU_nhds_y] with z hzU
    change TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z (T z) =
      TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (0 : TensorRSSpace r s I z)
    rw [hT_zero z hzU]
  have h_covApply_zero : ∀ y ∈ U,
      covApply cov (smoothOrthoFrame (I := I) g x i) T y = 0 := by
    intro y hyU
    have h_cov_T_zero_y : cov.toFun T y = 0 :=
      cov_eq_zero_of_eventually_zero_on_open (I := I)
        (V := fun w : M => TensorRSSpace r s I w)
        cov hU_open hT_zero hyU (h_T_diff_on_U y hyU)
    change cov.toFun T y (smoothOrthoFrame (I := I) g x i y) = 0
    rw [h_cov_T_zero_y]
    rfl
  -- Step B: apply locality at the single point `x` to `covApply cov B_i T`,
  -- using the at-`x` differentiability witness.
  have h_first_zero : cov.toFun
      (covApply cov (smoothOrthoFrame (I := I) g x i) T) x = 0 :=
    cov_eq_zero_of_eventually_zero_on_open (I := I)
      (V := fun w : M => TensorRSSpace r s I w)
      cov hU_open
      (T := fun y : M => covApply cov (smoothOrthoFrame (I := I) g x i) T y)
      (U := U) h_covApply_zero hxU (hcovT_diff_x i)
  -- Combine: both halves of the summand are zero.
  change cov.toFun (covApply cov (smoothOrthoFrame (I := I) g x i) T) x
      (smoothOrthoFrame (I := I) g x i x) -
    cov.toFun T x ((LeviCivita (I := I) g).toFun
        (smoothOrthoFrame (I := I) g x i) x
        (smoothOrthoFrame (I := I) g x i x)) = 0
  rw [h_first_zero, h_second_zero]
  simp

/-! ## Part 6: negation and subtraction

By combining the additivity identity (Part 3) with the scalar-homogeneity
identity (Part 4) at `c = -1`, the raw connection Laplacian commutes with
negation. Subtraction follows from additivity and negation.

These identities are convenience corollaries; they are not part of the
minimum-set of headline identities but are useful for downstream callers
that need to manipulate the raw operator directly. -/

/-- **Negation identity for the raw connection Laplacian.** This is the
`c = -1` specialisation of `rawTensorConnLap_smul`. -/
theorem rawTensorConnLap_neg [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ∀ x : M, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) x)
    (hcovT : ∀ (x : M) (i : Fin (Module.finrank ℝ E)),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g x i) T y)) x)
    (x : M) :
    rawTensorConnLap (I := I) g r s (fun y => -T y) x =
      - rawTensorConnLap (I := I) g r s T x := by
  classical
  have h := rawTensorConnLap_smul (I := I) g r s (T := T) (c := -1) hT hcovT x
  -- `(-1) • T y = -T y` and `(-1) • _ = -_`.
  simp only [neg_smul, one_smul, neg_smul] at h
  exact h

/-! ## Part 7: chart-aligned trace form (model-basis variant)

The textbook expression of the tensor connection Laplacian in chart
coordinates uses a basis `e_i` of the chart model space and writes
$$
  (\Delta_\nabla T)^I_J(x) = g^{ab}(x)\,\bigl[\partial_a\partial_b T^I_J +
    (\text{Christoffel terms in $a$ and $b$})\bigr].
$$
At the level of the raw operator (and at a single point `x`), the
chart-coordinate form is obtained by tracing the second covariant
derivative against the canonical model basis of `E`, weighted by the inverse
Gram matrix at `x` to convert from a coordinate frame to a `g_x`-orthonormal
frame.

A complete chart-coordinate characterisation requires the full chart-bridge
between the abstract covariant derivative on the `(r, s)`-tensor bundle and
the chart-local Christoffel-augmented expression. The current foundation
exposes only the smooth-orthonormal-frame variant; downstream consumers that
need the chart-coordinate form should compose `rawTensorConnLap` with the
appropriate chart-bridge for `(r, s)`-tensors. -/

/-- **Frame-trace presentation of the raw connection Laplacian.** At a fixed
centre `x`, the raw operator is the finite trace of the second covariant
derivative against the `g_x`-orthonormal frame `smoothOrthoFrame g x`. This
restates the definition; it is provided as a named theorem so downstream
consumers can name the frame explicitly. -/
theorem rawTensorConnLap_frame_trace
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap (I := I) g r s T x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g x i) T) x
            (smoothOrthoFrame (I := I) g x i x) -
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            T x
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x
              (smoothOrthoFrame (I := I) g x i x))) := rfl

/-! ## Part 8: support inclusion and compact-support preservation

The locality result `rawTensorConnLap_eq_zero_of_eventually_zero` (Part 5)
immediately upgrades to a support inclusion: the value at `x` vanishes whenever
`T` vanishes on a neighbourhood of `x`. Composing with the underlying
smooth-section data of a `SmoothCcTensor`, we obtain that the function
`b ↦ TensorRSSpace.toModel (rawTensorConnLap g r s T b)` has compact support
contained in `tsupport (b ↦ TensorRSSpace.toModel (T b))`.

The smoothness witnesses needed by `rawTensorConnLap_eq_zero_of_eventually_zero`
at each `x` come from `ContMDiffSection.contMDiff` for `T` itself and from
`covApply_contMDiffOn` for `covApply cov (smoothOrthoFrame g x i) T`,
discharged using `smoothOrthoFrame_smooth`. -/

section CompactSupport

variable [CompleteSpace E]

/-- **Pointwise smoothness witness of `T` from the bundled section.** A bundled
`ContMDiffSection` of class `C^∞` gives the manifold-differentiability of the
total-space form at every point. -/
private lemma rawTensorConnLap_T_mdiff_at (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) x := by
  classical
  -- `T.contMDiff` gives `ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
  --     (fun y => TotalSpace.mk' (TensorRSModel r s ℝ E)
  --                 (E := fun z => TensorRSSpace r s I z) y (T y))`.
  exact (T.contMDiff x).mdifferentiableAt (by simp)

/-- **Smoothness of `covApply cov B T` at every point** when both `B` and `T`
are globally `C^∞`. This is the smoothness witness required by
`rawTensorConnLap_eq_zero_of_eventually_zero` for the first derivative section
`covApply cov B T`. -/
private lemma rawTensorConnLap_covApply_mdiff_at
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Π b : M, TangentSpace I b)
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (B b)))
    (x : M) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
          B (fun y : M => T y) y)) x := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  -- Smoothness of `T` as a total-space form (from `T.contMDiff`).
  have hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) := T.contMDiff
  -- Bump T's smoothness witness from ∞ to (∞ + 1) using that ∞ + 1 = ∞ for WithTop ℕ∞.
  have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) := by
    -- `∞ + 1 = ∞` in `WithTop ℕ∞` holds definitionally.
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hT_total
  -- Smoothness of `covApply cov B T` from `covApply_contMDiffOn`.
  have h_covApply :
      ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply cov B (fun y : M => T y) y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) hB hT_plus
  -- Extract `MDifferentiableAt` at `x`.
  have h_at : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply cov B (fun y : M => T y) y)) x :=
    h_covApply.contMDiffAt (Filter.univ_mem)
  exact h_at.mdifferentiableAt (by simp)

/-- **Support inclusion (pointwise).** If `T` is a smooth `(r, s)`-tensor
section and `x ∉ tsupport (b ↦ TensorRSSpace.toModel (T b))`, then
`rawTensorConnLap g r s T x = 0`.

The proof finds an open neighbourhood `U` of `x` where `T` vanishes (using the
definition of `tsupport`), then applies `rawTensorConnLap_eq_zero_of_eventually_zero`
with smoothness witnesses from `T.contMDiff`. -/
theorem rawTensorConnLap_eq_zero_of_not_mem_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        (fun x : M => TensorRSSpace r s I x)⟯)
    {x : M}
    (hx : x ∉ tsupport (fun b : M => TensorRSSpace.toModel (T b))) :
    rawTensorConnLap (I := I) g r s (fun y : M => T y) x = 0 := by
  classical
  -- From `x ∉ tsupport`, the section vanishes eventually on a neighbourhood.
  have hT_eq : (fun b : M => TensorRSSpace.toModel (T b)) =ᶠ[𝓝 x] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hx
  -- Extract an open neighbourhood `U` of `x` on which `T b = 0` for all `b ∈ U`.
  rw [Filter.eventuallyEq_iff_exists_mem] at hT_eq
  obtain ⟨V, hV_nhds, hV_eq⟩ := hT_eq
  -- Convert to open set inside the neighbourhood: there exists open U with x ∈ U ⊆ V.
  obtain ⟨U, hUV, hU_open, hxU⟩ := mem_nhds_iff.mp hV_nhds
  -- `T b = 0` for all `b ∈ U`, in `TensorRSSpace r s I b`.
  have hT_zero_U : ∀ b ∈ U, (fun y : M => T y) b = 0 := by
    intro b hbU
    -- `hV_eq b : (fun b => TensorRSSpace.toModel (T b)) b = 0 b = 0`.
    have h_model_zero : TensorRSSpace.toModel (T b) = 0 := by
      have := hV_eq (hUV hbU)
      simpa using this
    -- Apply injectivity of `toModel`.
    have h_model_zero' : TensorRSSpace.toModel (T b) =
        TensorRSSpace.toModel (0 : TensorRSSpace r s I b) := by
      rw [h_model_zero, TensorRSSpace.toModel_zero]
    exact TensorRSSpace.toModel_injective h_model_zero'
  -- Apply `rawTensorConnLap_eq_zero_of_eventually_zero`.
  apply rawTensorConnLap_eq_zero_of_eventually_zero (I := I) g r s
    (T := fun y : M => T y) (U := U) hU_open hxU hT_zero_U
  · -- `MDifferentiableAt` of T at x.
    exact rawTensorConnLap_T_mdiff_at (I := I) r s T x
  · -- `MDifferentiableAt` of `covApply cov (smoothOrthoFrame g x i) T` at x.
    intro i
    exact rawTensorConnLap_covApply_mdiff_at (I := I) g r s T
      (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i) x

/-- **Support inclusion (functional).** The support of
`b ↦ TensorRSSpace.toModel (rawTensorConnLap g r s T b)` is contained in
`tsupport (b ↦ TensorRSSpace.toModel (T b))`. -/
theorem rawTensorConnLap_support_subset_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        (fun x : M => TensorRSSpace r s I x)⟯) :
    Function.support
        (fun b : M => TensorRSSpace.toModel
          (rawTensorConnLap (I := I) g r s (fun y : M => T y) b)) ⊆
      tsupport (fun b : M => TensorRSSpace.toModel (T b)) := by
  classical
  intro x hx
  -- `hx : x ∈ support (rawTensorConnLap ... x ↦ toModel · )`.
  -- We show `x ∈ tsupport (T x ↦ toModel · )` by contradiction.
  by_contra hxnot
  apply hx
  -- From `hxnot`, the rawTensorConnLap vanishes at x.
  have h_zero : rawTensorConnLap (I := I) g r s
      (fun y : M => T y) x = 0 :=
    rawTensorConnLap_eq_zero_of_not_mem_tsupport (I := I) g r s T hxnot
  -- And then `toModel` of zero is zero.
  change TensorRSSpace.toModel
    (rawTensorConnLap (I := I) g r s (fun y : M => T y) x) = 0
  rw [h_zero, TensorRSSpace.toModel_zero]

/-- **Compact-support preservation.** If `T` is a smooth `(r, s)`-tensor
section whose model image has compact support, then so does the model image of
the raw connection Laplacian of `T`. -/
theorem rawTensorConnLap_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        (fun x : M => TensorRSSpace r s I x)⟯)
    (hT_cc : HasCompactSupport (fun b : M => TensorRSSpace.toModel (T b))) :
    HasCompactSupport (fun b : M =>
      TensorRSSpace.toModel
        (rawTensorConnLap (I := I) g r s (fun y : M => T y) b)) := by
  classical
  -- Use `HasCompactSupport.mono'` with the support-inclusion lemma.
  refine HasCompactSupport.mono'
    (f := fun b : M => TensorRSSpace.toModel (T b)) hT_cc ?_
  exact rawTensorConnLap_support_subset_tsupport (I := I) g r s T

end CompactSupport

/-! ## Part 9: bundled `SmoothCcTensor`-to-section package

For a smooth, compactly-supported `(r, s)`-tensor section, the raw connection
Laplacian inherits compact support automatically (Part 8). The smoothness of
the resulting function `b ↦ rawTensorConnLap g r s T.toFun b` is a separate
question: the trace formula uses `smoothOrthoFrame g x` whose centre `x`
varies with the evaluation point, and proving smoothness reduces to
frame-invariance of the second-covariant-derivative trace. We expose this as
an explicit hypothesis on the bundled operator so that downstream consumers
can supply the witness on a per-use basis. -/

section BundledOperator

open DifferentialGeometry.Integral.L2

variable [CompleteSpace E]

/-- **Bundled connection Laplacian on `SmoothCcTensor`, taking smoothness as an
explicit hypothesis.** For a smooth, compactly-supported `(r, s)`-tensor
section `T : SmoothCcTensor g r s`, given a smoothness witness for the
total-space form of the raw connection Laplacian, the result is packaged as a
`SmoothCcTensor g r s`.

The smoothness hypothesis is exposed because the proof of smoothness of
`b ↦ rawTensorConnLap g r s T.toFun b` requires frame-invariance of the
second-covariant-derivative trace, which is a separate piece of infrastructure
not yet established in the codebase. -/
noncomputable def tensorConnLaplacian_of_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (hSmooth : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) y))) :
    SmoothCcTensor g r s where
  toSection :=
    { toFun := fun b : M =>
        rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) b
      contMDiff_toFun := hSmooth }
  hasCompactSupport :=
    rawTensorConnLap_hasCompactSupport (I := I) g r s T.toSection
      T.hasCompactSupport

/-- The underlying function of `tensorConnLaplacian_of_contMDiff` is
`rawTensorConnLap`. -/
@[simp] lemma tensorConnLaplacian_of_contMDiff_toFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (hSmooth : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) y)))
    (x : M) :
    (tensorConnLaplacian_of_contMDiff (I := I) g r s T hSmooth).toSection x =
      rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) x := rfl

/-! ### Bundled algebraic properties via smoothness hypotheses

The bundled operator inherits additivity and scalar homogeneity from the raw
operator (Parts 3 and 4). Each algebraic identity requires the smoothness
hypothesis on every involved section. The differentiability witnesses required
by `rawTensorConnLap_add` and `rawTensorConnLap_smul` follow from
`ContMDiffSection.contMDiff` for the inputs and `covApply_contMDiffOn` for
the first-derivative sections. -/

/-- **Additivity at the bundled level.** For two `SmoothCcTensor g r s`
inputs with their smoothness witnesses, the bundled connection Laplacian is
additive at the underlying-section level. -/
theorem tensorConnLaplacian_of_contMDiff_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T T' : SmoothCcTensor g r s)
    (hSmooth_T : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) y)))
    (hSmooth_T' : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s (fun z : M => T'.toSection z) y)))
    (hSmooth_sum : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s
          (fun z : M => (T + T').toSection z) y)))
    (x : M) :
    (tensorConnLaplacian_of_contMDiff (I := I) g r s (T + T')
        hSmooth_sum).toSection x =
      (tensorConnLaplacian_of_contMDiff (I := I) g r s T hSmooth_T).toSection x +
        (tensorConnLaplacian_of_contMDiff (I := I) g r s T'
          hSmooth_T').toSection x := by
  classical
  -- Unfold both sides to `rawTensorConnLap` form.
  rw [tensorConnLaplacian_of_contMDiff_toFun,
      tensorConnLaplacian_of_contMDiff_toFun,
      tensorConnLaplacian_of_contMDiff_toFun]
  -- The underlying function of `T + T'` is `T.toSection + T'.toSection`.
  have h_add_fun : (fun z : M => (T + T').toSection z) =
      (fun z : M => T.toSection z + T'.toSection z) := by
    funext z
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add]
    rfl
  rw [h_add_fun]
  -- Now apply `rawTensorConnLap_add` with the appropriate differentiability witnesses.
  refine rawTensorConnLap_add (I := I) g r s
    (T := fun z : M => T.toSection z) (T' := fun z : M => T'.toSection z)
    (fun y => ?_) (fun y => ?_) (fun y i => ?_) (fun y i => ?_) x
  · exact rawTensorConnLap_T_mdiff_at (I := I) r s T.toSection y
  · exact rawTensorConnLap_T_mdiff_at (I := I) r s T'.toSection y
  · exact rawTensorConnLap_covApply_mdiff_at (I := I) g r s T.toSection
      (smoothOrthoFrame (I := I) g y i)
      (smoothOrthoFrame_smooth (I := I) g y i) y
  · exact rawTensorConnLap_covApply_mdiff_at (I := I) g r s T'.toSection
      (smoothOrthoFrame (I := I) g y i)
      (smoothOrthoFrame_smooth (I := I) g y i) y

/-- **Scalar homogeneity at the bundled level.** For a `SmoothCcTensor g r s`
input with its smoothness witness, the bundled connection Laplacian commutes
with scalar multiplication at the underlying-section level. -/
theorem tensorConnLaplacian_of_contMDiff_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (T : SmoothCcTensor g r s)
    (hSmooth_T : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) y)))
    (hSmooth_cT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s
          (fun z : M => (c • T).toSection z) y)))
    (x : M) :
    (tensorConnLaplacian_of_contMDiff (I := I) g r s (c • T)
        hSmooth_cT).toSection x =
      c • (tensorConnLaplacian_of_contMDiff (I := I) g r s T
        hSmooth_T).toSection x := by
  classical
  rw [tensorConnLaplacian_of_contMDiff_toFun,
      tensorConnLaplacian_of_contMDiff_toFun]
  -- The underlying function of `c • T` is `c • T.toSection`.
  have h_smul_fun : (fun z : M => (c • T).toSection z) =
      (fun z : M => c • T.toSection z) := by
    funext z
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul]
    rfl
  rw [h_smul_fun]
  refine rawTensorConnLap_smul (I := I) g r s
    (T := fun z : M => T.toSection z) c
    (fun y => ?_) (fun y i => ?_) x
  · exact rawTensorConnLap_T_mdiff_at (I := I) r s T.toSection y
  · exact rawTensorConnLap_covApply_mdiff_at (I := I) g r s T.toSection
      (smoothOrthoFrame (I := I) g y i)
      (smoothOrthoFrame_smooth (I := I) g y i) y

/-- The zero section maps to the zero section. -/
theorem tensorConnLaplacian_of_contMDiff_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (hSmooth : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s
          (fun z : M => (0 : SmoothCcTensor g r s).toSection z) y))) :
    tensorConnLaplacian_of_contMDiff (I := I) g r s
        (0 : SmoothCcTensor g r s) hSmooth =
      (0 : SmoothCcTensor g r s) := by
  classical
  -- We use `SmoothCcTensor.ext` to reduce to equality of underlying sections.
  apply SmoothCcTensor.ext
  -- Reduce to pointwise equality at the section level via `ContMDiffSection.coe_inj`.
  apply ContMDiffSection.coe_inj
  funext x
  -- Underlying function of the zero section is identically zero.
  have h_zero_fun : (fun z : M => (0 : SmoothCcTensor g r s).toSection z) =
      (fun _ : M => (0 : TensorRSSpace r s I _)) := by
    funext z
    have h_sec_zero : (0 : SmoothCcTensor g r s).toSection =
        (0 : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) :=
      SmoothCcTensor.toSection_zero
    rw [h_sec_zero, ContMDiffSection.coe_zero]
    rfl
  -- Show: `rawTensorConnLap g r s (zero section) x = 0`.
  have h_rawConnLap_zero :
      rawTensorConnLap (I := I) g r s
        (fun z : M => (0 : SmoothCcTensor g r s).toSection z) x = 0 := by
    rw [h_zero_fun]
    exact rawTensorConnLap_zero (I := I) g r s x
  -- LHS: the toFun of `tensorConnLaplacian_of_contMDiff ... 0 ...` at x.
  -- Unfolds to `rawTensorConnLap g r s (zero section) x`.
  -- RHS: the toFun of `(0 : SmoothCcTensor g r s).toSection` at x, which is 0.
  change rawTensorConnLap (I := I) g r s
      (fun z : M => (0 : SmoothCcTensor g r s).toSection z) x =
    ((0 : SmoothCcTensor g r s).toSection : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) x
  rw [h_rawConnLap_zero]
  -- Now reduce the RHS: zero section evaluated at x is 0.
  have h_sec_zero : (0 : SmoothCcTensor g r s).toSection =
      (0 : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        (fun x : M => TensorRSSpace r s I x)⟯) :=
    SmoothCcTensor.toSection_zero
  rw [h_sec_zero, ContMDiffSection.coe_zero]
  rfl

end BundledOperator

/-! ## Part 10: fixed-smooth-frame variant and its smoothness

The raw operator `rawTensorConnLap g r s T x` uses the centre-dependent frame
`smoothOrthoFrame g x`. To establish smoothness as a function of `x`, we
introduce a variant that uses a *fixed* tangent frame `B : Fin n → Π b,
TangentSpace I b` of smooth global sections. The fixed-frame operator is
smooth in `x` by direct composition of smooth operations, and at every `x`
it agrees with `rawTensorConnLap g r s T x` provided the fixed frame is
`g_x`-orthonormal at `x`.

This is the structural analogue of how the scalar / vector connection
Laplacians are made smooth: a chart-local (chart-α-dependent) formula is
shown to be smooth on the chart source, and the global operator is identified
with this chart formula on a neighbourhood of every point. -/

section FixedFrame

variable [CompleteSpace E]

/-- **Fixed-smooth-frame variant of the raw connection Laplacian on
`(r, s)`-tensor sections.** For a smooth Riemannian metric `g`, ranks
`(r, s)`, a fixed frame `B : Fin n → Π b, TangentSpace I b`, a raw
`(r, s)`-tensor section `T`, and an evaluation point `x`, the value is the
trace formula
$$
  \sum_i \bigl(\nabla^{(r,s)}_{B_i x}\,\nabla^{(r,s)}_{B_i} T -
    \nabla^{(r,s)}_{(\nabla_{B_i} B_i)(x)} T\bigr).
$$
Here `∇^{(r,s)}` abbreviates the bundled tensor covariant derivative and the
underlying tangent covariant derivative is the Levi-Civita connection of `g`.
The dependence on `B` is genuine in the absence of an orthonormality
hypothesis; orthonormality at the centre point `x` is what reduces this to
the standard connection Laplacian at `x`. -/
noncomputable def rawTensorConnLap_fixedFrame
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (B i) T) x (B i x) -
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        T x
        ((LeviCivita (I := I) g).toFun (B i) x (B i x)))

/-- The defining identity for `rawTensorConnLap_fixedFrame`. -/
@[simp] lemma rawTensorConnLap_fixedFrame_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap_fixedFrame (I := I) g r s B T x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (B i) T) x (B i x) -
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            T x
            ((LeviCivita (I := I) g).toFun (B i) x (B i x))) := rfl

/-- **Identification with the centre-dependent raw operator at orthonormality
points.** When the fixed frame `B` equals `smoothOrthoFrame g x` (the
centre-`x`-dependent smooth orthonormal frame), the fixed-frame variant
agrees with `rawTensorConnLap` at `x`. This is true by definition (both
expressions are the same finite sum), and is provided as a `rfl` lemma so
downstream consumers can switch between the two presentations. -/
lemma rawTensorConnLap_fixedFrame_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap_fixedFrame (I := I) g r s
        (smoothOrthoFrame (I := I) g x) T x =
      rawTensorConnLap (I := I) g r s T x := rfl

/-! ### Smoothness of the fixed-frame variant

For a fixed smooth orthonormal frame `B` and a smooth tensor section `T`, the
fixed-frame operator is smooth in `x` by composition of smooth operations:

1. Each `B i` is smooth (hypothesis on the fixed frame).
2. `covApply cov (B i) T` is smooth as a tensor section: this uses
   `covApply_contMDiffOn` with `cov := tensorRSCovariantDerivative`.
3. The covariant derivative `cov` then composes once more to give a smooth
   section of `Hom(TM, TensorRSSpace)`.
4. Application of `cov.toFun T` to `cov.toFun B_i B_i` at `x` is bilinear in
   smooth sections, hence smooth.
5. Each summand is smooth; the finite sum is smooth.

The smoothness witness on `T` requires `(∞ + 1 : WithTop ℕ∞)`-smoothness as
input (one degree higher than the output) — this is the standard
`ContMDiffCovariantDerivative` convention. -/

/-- **The fixed-frame operator's first cov-derivative section
`b ↦ cov.toFun T b (B_i b)` is smooth** when both `T` and `B_i` are smooth. -/
private lemma rawTensorConnLap_fixedFrame_covApply_T_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B i)))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) (B i) T y)) := by
  classical
  -- Bump T's smoothness witness from ∞ to (∞ + 1).
  have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hT_total
  have hOn :
      ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) (B i) T y)) Set.univ :=
    covApply_contMDiffOn
      (cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)) (hB i) hT_plus
  intro b
  exact hOn.contMDiffAt (Filter.univ_mem)

/-- **Second cov-derivative summand smoothness.** The function
`b ↦ cov.toFun (covApply cov (B i) T) b (B i b)`, which is the first summand
of `rawTensorConnLap_fixedFrame`, is smooth in `b`. -/
private lemma rawTensorConnLap_fixedFrame_firstSummand_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B i)))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) (B i) T) y (B i y))) := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  -- Step 1: The first-derivative section `covApply cov (B i) T` is smooth.
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply cov (B i) T y)) :=
    rawTensorConnLap_fixedFrame_covApply_T_contMDiff (I := I) g r s hT_total hB i
  -- Step 2: Bump to (∞ + 1) for input to the next covApply.
  have h1_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply cov (B i) T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact h1
  -- Step 3: Apply `covApply_contMDiffOn` to get smoothness of the second cov-deriv.
  have hOn :
      ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply cov (B i)
            (fun z : M => covApply cov (B i) T z) y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) (hB i) h1_plus
  -- Step 4: `covApply cov (B i) (covApply cov (B i) T) y = cov.toFun (covApply cov (B i) T) y (B i y)`
  -- by definition of `covApply`.
  intro b
  have hAt : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply cov (B i)
          (fun z : M => covApply cov (B i) T z) y)) b :=
    hOn.contMDiffAt (Filter.univ_mem)
  -- The two functions agree pointwise because
  --   covApply cov X T y = cov.toFun T y (X y).
  convert hAt

/-- **Smoothness of `b ↦ cov.toFun B_i b (B_i b)`** for a smooth frame field. -/
private lemma rawTensorConnLap_fixedFrame_covBB_contMDiff
    (g : SmoothRiemannianMetric I M)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y
        ((LeviCivita (I := I) g).toFun (B i) y (B i y))) := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  -- This is `covApply cov (B i) (B i)`: `covApply cov X Z y = cov.toFun Z y (X y)`.
  -- We use `covApply_contMDiffOn` with the source = the tangent bundle.
  have hB_plus : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (T% (B i)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hB i
  have hOn :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y
          (covApply cov (B i) (B i) y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) (hB i) hB_plus
  intro b
  exact hOn.contMDiffAt (Filter.univ_mem)

/-- **Second summand smoothness.** The function
`b ↦ cov.toFun T b (cov.toFun B_i b (B_i b))`, which is the second summand
of `rawTensorConnLap_fixedFrame`, is smooth in `b`. -/
private lemma rawTensorConnLap_fixedFrame_secondSummand_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B i)))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun T y
          ((LeviCivita (I := I) g).toFun (B i) y (B i y)))) := by
  classical
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  -- Define `W := fun y => cov_TM.toFun (B i) y (B i y)`. This is smooth (previous lemma).
  set W : Π b : M, TangentSpace I b :=
    fun y => (LeviCivita (I := I) g).toFun (B i) y (B i y) with hW_def
  have hW_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y (W y)) :=
    rawTensorConnLap_fixedFrame_covBB_contMDiff (I := I) g hB i
  -- Now we want smoothness of `b ↦ cov.toFun T b (W b)`.
  -- This is `covApply cov W T y = cov.toFun T y (W y)`.
  have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hT_total
  have hOn :
      ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply cov W T y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) hW_smooth hT_plus
  intro b
  have hAt : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply cov W T y)) b :=
    hOn.contMDiffAt (Filter.univ_mem)
  convert hAt

/-- **Smoothness of the fixed-frame variant.** For a smooth raw tensor section
`T` and a fixed smooth tangent frame `B` (each `B i` a smooth global tangent
section), the fixed-frame operator `rawTensorConnLap_fixedFrame g r s B T` is
a smooth tensor section. -/
theorem rawTensorConnLap_fixedFrame_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap_fixedFrame (I := I) g r s B T y)) := by
  classical
  -- The fixed-frame operator at `y` is a finite sum of summands, each smooth.
  -- We use `ContMDiff.sum_section` to handle the finite sum.
  -- First, each per-index summand (first - second) is smooth.
  have h_per_index_smooth : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) (B i) T) y (B i y) -
            (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun T y
              ((LeviCivita (I := I) g).toFun (B i) y (B i y)))) := by
    intro i
    have h_first := rawTensorConnLap_fixedFrame_firstSummand_contMDiff
      (I := I) g r s hT_total hB i
    have h_second := rawTensorConnLap_fixedFrame_secondSummand_contMDiff
      (I := I) g r s hT_total hB i
    exact h_first.sub_section h_second
  -- Now the total = `∑ i (...)`. Use `ContMDiff.sum_section`.
  have h_sum_smooth : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (∑ i : Fin (Module.finrank ℝ E),
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) (B i) T) y (B i y) -
            (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun T y
              ((LeviCivita (I := I) g).toFun (B i) y (B i y))))) := by
    refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
    exact h_per_index_smooth i
  -- The goal matches `h_sum_smooth` by the defining identity of `rawTensorConnLap_fixedFrame`.
  exact h_sum_smooth

end FixedFrame

/-! ## Part 11: pointwise bilinear tensoriality of the raw second cov derivative

The summand of `rawTensorConnLap_fixedFrame` (and of `rawTensorConnLap`) at a fixed
evaluation point `y` is the value at `y` of the *raw second covariant derivative*
$$
  \Psi_T(X, Y)(y) := (\nabla^{(r,s)}_Y \nabla^{(r,s)}_X T)(y)
    - (\nabla^{(r,s)}_{(\nabla^{TM}_Y X)} T)(y),
$$
written in terms of the bundled tensor and Levi-Civita covariant derivatives as

```
cov_RS (covApply cov_RS X T) y (Y y) - cov_RS T y ((LeviCivita g) X y (Y y)).
```

The two basic structural facts are pointwise bilinear tensoriality in `(X, Y)` at `y`:

* `rawTensorConnLap_psi_tensorialAt_left`: tensoriality in the `X`-argument at `y`,
  derived from the Leibniz rule of `cov_RS` and of `LeviCivita g`. The Leibniz
  cross-terms cancel between the two halves of `Ψ_T`.
* `rawTensorConnLap_psi_tensorialAt_right`: tensoriality in the `Y`-argument at `y`,
  which is automatic from `ContinuousLinearMap`-linearity since `Y` only enters
  through evaluating linear maps at `Y y`.

Together with `TensorialAt.mkHom₂`, these would package `Ψ_T(·, ·)(y)` into a
continuous bilinear map on `T_y M`. The orthonormal-frame trace of that bilinear
map at `y` is the textbook expression for `(Δ_∇ T)(y)`. We do not perform the
final bundling here; the two tensoriality theorems suffice to expose the pointwise
bilinearity structure to downstream consumers. -/

section RawPsiTensorial

variable [CompleteSpace E]

/-- Pointwise smoothness witness for the tensor covariant derivative section
`b ↦ cov_RS.toFun T b`, treated as a section of the Hom-bundle
`Hom(TM, TensorRSSpace r s)`, when `T` is globally `C^∞`. -/
private lemma covRS_T_mdiff_at
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (y : M) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E))
      (fun b : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ]
          TensorRSSpace r s I x) b
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun T b)) y := by
  classical
  -- Bump T's smoothness to (∞ + 1).
  have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hT_total
  -- The `ContMDiffCovariantDerivative ∞` instance gives global smoothness of
  -- `b ↦ cov_RS.toFun T b` as a section of `Hom(TM, V)`.
  have hcov_sec :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
        (fun b : M => (⟨b,
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun T b⟩ :
          TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
            (fun b : M => TangentSpace I b →L[ℝ] TensorRSSpace r s I b)))
        Set.univ :=
    (TensorRSNabla.tensorRSCovariantDerivative_contMDiff
      (I := I) (M := M) r s (LeviCivita (I := I) g)).contMDiff.contMDiff
      (σ := T) hT_plus.contMDiffOn
  exact ((hcov_sec.contMDiffAt (Filter.univ_mem)).mdifferentiableAt (by simp))

/-- Pointwise smoothness witness for `covApply cov_RS X T` as a tensor section,
derived from globally smooth `T` and pointwise differentiability of `X` at `y`. -/
private lemma covApply_covRS_X_T_mdiff_at
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    {X : Π b : M, TangentSpace I b} {y : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := TangentSpace I) z (X z)) y) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) X T z)) y := by
  classical
  -- Use `MDifferentiableAt.clm_bundle_apply` applied to the Hom-section
  -- `b ↦ cov_RS.toFun T b` and the vector section `X`.
  have hHom := covRS_T_mdiff_at (I := I) g r s hT_total y
  -- The CLM application gives `(cov_RS.toFun T b)(X b) = covApply cov_RS X T b`.
  have := MDifferentiableAt.clm_bundle_apply (b := id) hHom hX
  exact this

/-- **Left tensoriality of the raw second cov derivative at `y`.**

For a globally smooth raw tensor section `T` and a globally smooth vector field
`Y`, the bilinear form
`Ψ_T(X, Y)(y) := cov_RS (covApply cov_RS X T) y (Y y) - cov_RS T y (cov_TM X y (Y y))`
is tensorial in the `X`-argument at `y` (i.e., depends only on `X(y)`).

The proof is the standard Leibniz cancellation: applying the Leibniz rule of
`cov_RS` to the section `f • (covApply cov_RS X T)` and the Leibniz rule of
`LeviCivita g` to the vector field `f • X`, the `extDerivFun f y`-multiplied
cross-terms in the two halves coincide and cancel under the subtraction. -/
private theorem rawTensorConnLap_psi_tensorialAt_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (y : M)
    {Y : Π b : M, TangentSpace I b}
    (_hY_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E
        (E := fun w : M => TangentSpace I w) z (Y z)) y) :
    TensorialAt I E
      (fun (X : Π b : M, TangentSpace I b) =>
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) X T) y (Y y) -
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun T y
          ((LeviCivita (I := I) g).toFun X y (Y y)))
      y where
  smul := by
    intro f X hf hX
    classical
    set cov_RS := TensorRSNabla.tensorRSCovariantDerivative I M r s
      (LeviCivita (I := I) g) with hcovRS_def
    set cov_TM := LeviCivita (I := I) g with hcovTM_def
    -- Step A: `covApply cov_RS (f • X) T = f • (covApply cov_RS X T)`.
    have h_covApply_smul :
        covApply cov_RS (f • X) T = f • (covApply cov_RS X T) := by
      funext z
      change cov_RS.toFun T z ((f • X) z) = f z • (cov_RS.toFun T z (X z))
      have h_smul_pi : (f • X : Π b : M, TangentSpace I b) z = f z • X z := rfl
      rw [h_smul_pi, ContinuousLinearMap.map_smul]
    -- Step B: smoothness witness for `covApply cov_RS X T` at `y`.
    have hAppX : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          (covApply cov_RS X T z)) y :=
      covApply_covRS_X_T_mdiff_at (I := I) g r s hT_total hX
    -- Step C: Leibniz on `cov_RS` for `f • (covApply cov_RS X T)`.
    have h_leib_RS := cov_RS.isCovariantDerivativeOn.leibniz
      (σ := covApply cov_RS X T) (g := f) hAppX hf
    -- Step D: Leibniz on `cov_TM` for `f • X`.
    have h_leib_TM := cov_TM.isCovariantDerivativeOn.leibniz
      (σ := X) (g := f) hX hf
    -- Goal: compute the LHS using both Leibniz expansions, then simplify.
    change cov_RS.toFun (covApply cov_RS (f • X) T) y (Y y) -
        cov_RS.toFun T y (cov_TM.toFun (f • X) y (Y y)) =
      f y • (cov_RS.toFun (covApply cov_RS X T) y (Y y) -
        cov_RS.toFun T y (cov_TM.toFun X y (Y y)))
    rw [h_covApply_smul, h_leib_RS, h_leib_TM]
    -- After expansion the goal becomes an additive/scalar arithmetic identity
    -- in `TensorRSSpace r s I y`. The two `extDerivFun f y`-multiplied terms
    -- coincide and cancel after unfolding `covApply ... = cov_RS.toFun T y (X y)`.
    -- The fact `covApply cov_RS X T y = cov_RS.toFun T y (X y)` is definitional.
    have h_covApply_pt : covApply cov_RS X T y = cov_RS.toFun T y (X y) := rfl
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul, smul_sub, h_covApply_pt]
    abel
  add := by
    intro X X' hX hX'
    classical
    set cov_RS := TensorRSNabla.tensorRSCovariantDerivative I M r s
      (LeviCivita (I := I) g) with hcovRS_def
    set cov_TM := LeviCivita (I := I) g with hcovTM_def
    -- Step A: `covApply cov_RS (X + X') T = covApply cov_RS X T + covApply cov_RS X' T`.
    have h_covApply_add :
        covApply cov_RS (X + X') T =
          covApply cov_RS X T + covApply cov_RS X' T := by
      funext z
      change cov_RS.toFun T z ((X + X') z) =
        cov_RS.toFun T z (X z) + cov_RS.toFun T z (X' z)
      have : (X + X' : Π b : M, TangentSpace I b) z = X z + X' z := rfl
      rw [this, ContinuousLinearMap.map_add]
    -- Step B: smoothness witnesses at `y`.
    have hAppX : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          (covApply cov_RS X T z)) y :=
      covApply_covRS_X_T_mdiff_at (I := I) g r s hT_total hX
    have hAppX' : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          (covApply cov_RS X' T z)) y :=
      covApply_covRS_X_T_mdiff_at (I := I) g r s hT_total hX'
    -- Step C: additivity of `cov_RS` on the sum.
    have h_add_RS : cov_RS.toFun (covApply cov_RS X T +
        covApply cov_RS X' T) y =
      cov_RS.toFun (covApply cov_RS X T) y +
        cov_RS.toFun (covApply cov_RS X' T) y :=
      cov_RS.isCovariantDerivativeOn.add hAppX hAppX'
    -- Step D: additivity of `cov_TM` on `X + X'`.
    have h_add_TM : cov_TM.toFun (X + X') y =
        cov_TM.toFun X y + cov_TM.toFun X' y :=
      cov_TM.isCovariantDerivativeOn.add hX hX'
    change cov_RS.toFun (covApply cov_RS (X + X') T) y (Y y) -
        cov_RS.toFun T y (cov_TM.toFun (X + X') y (Y y)) =
      (cov_RS.toFun (covApply cov_RS X T) y (Y y) -
        cov_RS.toFun T y (cov_TM.toFun X y (Y y))) +
      (cov_RS.toFun (covApply cov_RS X' T) y (Y y) -
        cov_RS.toFun T y (cov_TM.toFun X' y (Y y)))
    rw [h_covApply_add, h_add_RS, h_add_TM]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
    abel

/-- **Right tensoriality of the raw second cov derivative at `y`.**

For a globally smooth raw tensor section `T` and any vector field `X`, the
bilinear form
`Ψ_T(X, Y)(y) := cov_RS (covApply cov_RS X T) y (Y y) - cov_RS T y (cov_TM X y (Y y))`
is tensorial in the `Y`-argument at `y`. Since `Y` only enters through
`ContinuousLinearMap` evaluations at `Y y` (no derivative of `Y` is taken),
this tensoriality is automatic: both halves are `ℝ`-linear in `Y y`. -/
private theorem rawTensorConnLap_psi_tensorialAt_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (_hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (y : M)
    {X : Π b : M, TangentSpace I b}
    (_hX_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E
        (E := fun w : M => TangentSpace I w) z (X z)) y) :
    TensorialAt I E
      (fun (Y : Π b : M, TangentSpace I b) =>
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) X T) y (Y y) -
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun T y
          ((LeviCivita (I := I) g).toFun X y (Y y)))
      y where
  smul := by
    intro f Y _hf _hY
    classical
    set cov_RS := TensorRSNabla.tensorRSCovariantDerivative I M r s
      (LeviCivita (I := I) g) with hcovRS_def
    set cov_TM := LeviCivita (I := I) g with hcovTM_def
    -- `(f • Y) y = f y • Y y` and both halves are CLMs in their last argument.
    have h_smul_at : (f • Y : Π b : M, TangentSpace I b) y = f y • Y y := rfl
    change cov_RS.toFun (covApply cov_RS X T) y ((f • Y) y) -
        cov_RS.toFun T y (cov_TM.toFun X y ((f • Y) y)) =
      f y • (cov_RS.toFun (covApply cov_RS X T) y (Y y) -
        cov_RS.toFun T y (cov_TM.toFun X y (Y y)))
    rw [h_smul_at]
    simp only [ContinuousLinearMap.map_smul, smul_sub]
  add := by
    intro Y Y' _hY _hY'
    classical
    set cov_RS := TensorRSNabla.tensorRSCovariantDerivative I M r s
      (LeviCivita (I := I) g) with hcovRS_def
    set cov_TM := LeviCivita (I := I) g with hcovTM_def
    have h_add_at : (Y + Y' : Π b : M, TangentSpace I b) y = Y y + Y' y := rfl
    change cov_RS.toFun (covApply cov_RS X T) y ((Y + Y') y) -
        cov_RS.toFun T y (cov_TM.toFun X y ((Y + Y') y)) =
      (cov_RS.toFun (covApply cov_RS X T) y (Y y) -
        cov_RS.toFun T y (cov_TM.toFun X y (Y y))) +
      (cov_RS.toFun (covApply cov_RS X T) y (Y' y) -
        cov_RS.toFun T y (cov_TM.toFun X y (Y' y)))
    rw [h_add_at]
    simp only [ContinuousLinearMap.map_add]
    abel

/-! ### Bundling Ψ_T at `y` as a continuous bilinear map

The two pointwise tensoriality theorems
`rawTensorConnLap_psi_tensorialAt_left` and `…_right` package via
`TensorialAt.mkHom₂` into a continuous bilinear map
`T_y M →L[ℝ] T_y M →L[ℝ] TensorRSSpace r s I y`. The bilinear value at a pair
of fibre vectors `(u, v)` is obtained by extending each to a globally smooth
section using `FiberBundle.extend` and evaluating the raw second covariant
derivative. The standard `mkHom₂_apply` lemma identifies the bilinear value at
the pointwise values of any pair of differentiable sections with `Ψ_T` applied
to those sections directly. -/

/-- The raw second covariant derivative `Ψ_T(·, ·)(y)` packaged as a continuous
bilinear map `T_y M →L[ℝ] T_y M →L[ℝ] TensorRSSpace r s I y`.

The pointwise tensoriality of `Ψ_T` in each of the `(X, Y)`-arguments at `y`
(see `rawTensorConnLap_psi_tensorialAt_left/right`) allows `Mathlib`'s
`TensorialAt.mkHom₂` to manufacture the bilinear CLM. The bilinear value at a
pair of fibre vectors `(u, v) : T_y M × T_y M` is the value of
`Ψ_T(extend u, extend v)` at `y`, where `extend` is the standard smooth
extension of a fibre vector to a global section of the tangent bundle. -/
noncomputable def rawTensorConnLap_psi_bilinAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (y : M) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TensorRSSpace r s I y :=
  TensorialAt.mkHom₂
    (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _))
    (V' := (TangentSpace I : M → Type _))
    (A := TensorRSSpace r s I y)
    (Φ := fun (X Y : Π b : M, TangentSpace I b) =>
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) X T) y (Y y) -
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun T y
        ((LeviCivita (I := I) g).toFun X y (Y y)))
    y
    (fun Y hY =>
      rawTensorConnLap_psi_tensorialAt_left g r s T hT_total y (Y := Y) hY)
    (fun X hX =>
      rawTensorConnLap_psi_tensorialAt_right g r s T hT_total y (X := X) hX)

/-- **Apply formula for `rawTensorConnLap_psi_bilinAt`.**

For globally smooth (in particular, `MDifferentiableAt y`) sections `X` and `Y`
of the tangent bundle, the bundled bilinear map at `y` evaluated on the
pointwise fibre values `(X y, Y y)` agrees with the raw `Ψ_T(X, Y)(y)`:

`Ψ̂_T(y) (X y) (Y y) =
   cov_RS (covApply cov_RS X T) y (Y y) - cov_RS T y (cov_TM X y (Y y))`. -/
theorem rawTensorConnLap_psi_bilinAt_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    {y : M}
    {X Y : Π b : M, TangentSpace I b}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E
        (E := fun w : M => TangentSpace I w) z (X z)) y)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E
        (E := fun w : M => TangentSpace I w) z (Y z)) y) :
    rawTensorConnLap_psi_bilinAt g r s T hT_total y (X y) (Y y) =
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) X T) y (Y y) -
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun T y
        ((LeviCivita (I := I) g).toFun X y (Y y)) := by
  classical
  unfold rawTensorConnLap_psi_bilinAt
  exact TensorialAt.mkHom₂_apply _ _ hX hY

/-! ### Frame invariance of the raw tensor connection Laplacian

The value `rawTensorConnLap g r s T y` was defined as the frame-trace of the
raw second covariant derivative against the centre-dependent smooth orthonormal
frame `smoothOrthoFrame g y`, evaluated at `y`. The combination of the
pointwise-bilinear packaging `rawTensorConnLap_psi_bilinAt` and the scalar
orthonormal-basis trace identity `orthonormal_basis_bilin_trace` shows that the
value is unchanged when the smooth orthonormal frame at the centre is
replaced by an arbitrary `g_y`-orthonormal basis of `T_y M`.

The proof goes by dual-functional separation: for any continuous linear
functional `φ : TensorRSSpace r s I y →L[ℝ] ℝ`, the scalar bilinear form
`Hb_φ(X, Y) := φ(Ψ_T(X, Y)(y))` admits the basis-independent trace
expansion `∑_i Hb_φ(B_i, B_i) = ∑_{kl} G^{kl}(y, y) · Hb_φ(e_k, e_l)`
(Mathlib's `orthonormal_basis_bilin_trace`). Applying this once with `B =
smoothOrthoFrame g y` at `y` and once with the arbitrary `B`, both reductions
land on the same right-hand side; hence `φ` evaluates the two frame-trace
vectors equally. As `TensorRSSpace r s I y` is a finite-dimensional normed
ℝ-space, equal-on-dual implies equal. -/

/-- **Frame invariance of the raw tensor connection Laplacian.**

For any `g_y`-orthonormal basis `B : Fin (Module.finrank ℝ E) → T_y M`,
the value `rawTensorConnLap g r s T y` equals the orthonormal-frame trace of
the bundled raw second covariant derivative
`rawTensorConnLap_psi_bilinAt g r s T hT_total y`:
$$
  (\Delta_\nabla T)(y) = \sum_i \hat\Psi_T(y)(B_i,\, B_i).
$$
This shows that the centre-dependent choice of `smoothOrthoFrame g y` in the
definition of `rawTensorConnLap` is irrelevant — any `g_y`-orthonormal basis
of `T_y M` reproduces the same value. -/
theorem rawTensorConnLap_eq_frame_trace
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (y : M)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I y)
    (hB_orthonormal : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    rawTensorConnLap (I := I) g r s T y =
      ∑ i : Fin (Module.finrank ℝ E),
        rawTensorConnLap_psi_bilinAt g r s T hT_total y (B i) (B i) := by
  classical
  -- Step 1: rewrite the LHS by identifying each summand of `rawTensorConnLap`
  -- with the bilinear value of `rawTensorConnLap_psi_bilinAt` at the centre-
  -- dependent smooth orthonormal frame at `y` (orthonormal at the centre `y`).
  have h_LHS_via_smoothFrame :
      rawTensorConnLap (I := I) g r s T y =
        ∑ i : Fin (Module.finrank ℝ E),
          rawTensorConnLap_psi_bilinAt g r s T hT_total y
            (smoothOrthoFrame (I := I) g y i y)
            (smoothOrthoFrame (I := I) g y i y) := by
    rw [rawTensorConnLap_def]
    refine Finset.sum_congr rfl ?_
    intro i _
    -- Smoothness of `smoothOrthoFrame g y i` as a tangent-bundle section.
    have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun z : M => TotalSpace.mk' E
          (E := fun w : M => TangentSpace I w) z
          (smoothOrthoFrame (I := I) g y i z)) y :=
      (smoothOrthoFrame_smooth (I := I) g y i).contMDiffAt.mdifferentiableAt
        (by simp)
    -- Apply `rawTensorConnLap_psi_bilinAt_apply` with
    -- `X = Y = smoothOrthoFrame g y i`.
    have happly := rawTensorConnLap_psi_bilinAt_apply (I := I) g r s T hT_total
      (X := smoothOrthoFrame (I := I) g y i)
      (Y := smoothOrthoFrame (I := I) g y i)
      hSmooth_at hSmooth_at
    -- happly : Ψ̂_T(y) (smoothOrthoFrame i y) (smoothOrthoFrame i y) =
    --   cov_RS (covApply cov_RS B_i T) y (B_i y) -
    --     cov_RS T y (cov_TM B_i y (B_i y)).
    -- We need the symmetric form (RHS → LHS).
    exact happly.symm
  -- Step 2: it suffices to show that, for the two orthonormal bases
  -- `C := smoothOrthoFrame g y · y` and `B`, the corresponding bilinear-form
  -- traces agree. We prove this by Parseval expansion of one basis against
  -- the other.
  rw [h_LHS_via_smoothFrame]
  -- Local abbreviations: Ψ is the bundled bilinear, C is the smooth orthonormal
  -- frame at the centre `y` evaluated at `y`, which is `g_y`-orthonormal at `y`.
  set Ψ : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TensorRSSpace r s I y :=
    rawTensorConnLap_psi_bilinAt g r s T hT_total y with hΨ_def
  set C : Fin (Module.finrank ℝ E) → TangentSpace I y :=
    fun i => smoothOrthoFrame (I := I) g y i y with hC_def
  -- C is `g_y`-orthonormal at `y` (orthonormality of the smooth frame at the
  -- centre).
  have hC_orthonormal :
      ∀ i j : Fin (Module.finrank ℝ E),
        g.inner y (C i) (C j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g y i j
  -- Riesz expansion of `B i` in the `C` orthonormal basis:
  -- `B i = ∑ j, g(B i, C j) • C j`.
  have hRieszB : ∀ i : Fin (Module.finrank ℝ E),
      B i = ∑ j : Fin (Module.finrank ℝ E),
        g.inner y (B i) (C j) • C j := by
    intro i
    apply (vector_eq_iff_inner_eq (I := I) g y _ _).mpr
    intro w
    -- Compute g(∑ j, g(B i, C j) • C j, w) = ∑ j, g(B i, C j) * g(C j, w).
    rw [show g.inner y
            (∑ j : Fin (Module.finrank ℝ E), g.inner y (B i) (C j) • C j) w =
          ∑ j : Fin (Module.finrank ℝ E),
            g.inner y (B i) (C j) * g.inner y (C j) w from by
      rw [map_sum, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [show ((g.inner y) (g.inner y (B i) (C j) • C j)) w =
            g.inner y (B i) (C j) • ((g.inner y) (C j)) w from by
        rw [ContinuousLinearMap.map_smul]; rfl]
      rw [smul_eq_mul]]
    -- Apply Parseval: g(B i, w) = ∑ j, g(B i, C j) * g(C j, w).
    exact g_inner_eq_orthonormal_parseval_sum (I := I) g y (B i) w C hC_orthonormal
  -- Bilinear expansion of `Ψ(B_i)(B_i)` in the `C` basis. To avoid `rw [hRieszB i]`
  -- accidentally rewriting `B i` inside the coefficient inner products
  -- `g.inner y (B i) (C j)`, we abbreviate the coefficient family by an opaque
  -- name `aB i` before performing the bilinear expansion.
  have hΨB_expand : ∀ i : Fin (Module.finrank ℝ E),
      Ψ (B i) (B i) =
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (g.inner y (B i) (C j) * g.inner y (B i) (C k)) •
              Ψ (C j) (C k) := by
    intro i
    -- Abbreviate the coefficient: aB j := g(B i, C j).
    set aB : Fin (Module.finrank ℝ E) → ℝ :=
      fun j => g.inner y (B i) (C j) with haB_def
    have hRieszBi : B i = ∑ j : Fin (Module.finrank ℝ E), aB j • C j := by
      simpa [aB] using hRieszB i
    -- Now rewrite using hRieszBi; aB is opaque so coefficients are preserved.
    conv_lhs => rw [hRieszBi]
    -- Step A: Ψ (∑ j, aB j • C j) = ∑ j, aB j • Ψ (C j).
    rw [show Ψ (∑ j : Fin (Module.finrank ℝ E), aB j • C j) =
          ∑ j : Fin (Module.finrank ℝ E), aB j • Ψ (C j) from by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      exact Ψ.map_smul (aB j) (C j)]
    -- Step B: ApplyAt (∑ k, aB k • C k).
    -- (∑ j, aB j • Ψ (C j)) (∑ k, aB k • C k)
    --   = ∑ j, (aB j • Ψ (C j)) (∑ k, aB k • C k)
    --   = ∑ j ∑ k, (aB j • Ψ (C j)) (aB k • C k)
    --   = ∑ j ∑ k, aB j • (aB k • Ψ (C j) (C k))
    --   = ∑ j ∑ k, (aB j * aB k) • Ψ (C j) (C k).
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ContinuousLinearMap.smul_apply]
    rw [show Ψ (C j) (∑ k : Fin (Module.finrank ℝ E), aB k • C k) =
          ∑ k : Fin (Module.finrank ℝ E), aB k • Ψ (C j) (C k) from by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      exact (Ψ (C j)).map_smul (aB k) (C k)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [smul_smul]
  -- Express the LHS sum in `C`-notation: `smoothOrthoFrame g y i y = C i`.
  have hLHS_eq_C :
      (∑ i : Fin (Module.finrank ℝ E),
        Ψ (smoothOrthoFrame (I := I) g y i y)
          (smoothOrthoFrame (I := I) g y i y)) =
      ∑ i : Fin (Module.finrank ℝ E), Ψ (C i) (C i) := rfl
  rw [hLHS_eq_C]
  -- Sum over i, expand each `Ψ(B i)(B i)` via `hΨB_expand`.
  rw [show (∑ i : Fin (Module.finrank ℝ E), Ψ (B i) (B i)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              (g.inner y (B i) (C j) * g.inner y (B i) (C k)) •
                Ψ (C j) (C k) from
    Finset.sum_congr rfl (fun i _ => hΨB_expand i)]
  -- Swap the outermost `i`-sum with the `j`-sum: `∑ i ∑ j ∑ k = ∑ j ∑ i ∑ k`.
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun i j => ∑ k : Fin (Module.finrank ℝ E),
          (g.inner y (B i) (C j) * g.inner y (B i) (C k)) • Ψ (C j) (C k))]
  -- Pointwise (in `j`) reduction: ∑ i ∑ k, (a * b) • Ψ (C j) (C k) = Ψ(C j)(C j).
  refine Finset.sum_congr rfl ?_
  intro j _
  -- Swap inner ∑ i ∑ k → ∑ k ∑ i.
  rw [show (∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (g.inner y (B i) (C j) * g.inner y (B i) (C k)) • Ψ (C j) (C k)) =
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ i : Fin (Module.finrank ℝ E),
            (g.inner y (B i) (C j) * g.inner y (B i) (C k)) • Ψ (C j) (C k) from
    Finset.sum_comm]
  -- Per-`k` reduction: factor out `Ψ (C j) (C k)` from the inner i-sum, then
  -- apply Parseval, then orthonormality of `C`.
  -- The cleanest packaging is one `Finset.sum_congr` swap at outer level on k.
  -- For each k, ∑ i, ((g(B i, C j) * g(B i, C k)) • Ψ(C j)(C k))
  --   = (∑ i, g(B i, C j) * g(B i, C k)) • Ψ(C j)(C k)
  --   = g(C j, C k) • Ψ(C j)(C k)                          [Parseval, g.symm]
  --   = (if j = k then 1 else 0) • Ψ(C j)(C k)              [orthonormality of C]
  have h_inner_per_k : ∀ k : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E),
        (g.inner y (B i) (C j) * g.inner y (B i) (C k)) • Ψ (C j) (C k)) =
      (if j = k then (1 : ℝ) else 0) • Ψ (C j) (C k) := by
    intro k
    -- Step (a): pull `Ψ(C j)(C k)` out of the i-sum.
    rw [show (∑ i : Fin (Module.finrank ℝ E),
            (g.inner y (B i) (C j) * g.inner y (B i) (C k)) • Ψ (C j) (C k)) =
          (∑ i : Fin (Module.finrank ℝ E),
            g.inner y (B i) (C j) * g.inner y (B i) (C k)) • Ψ (C j) (C k) from
      (Finset.sum_smul
        (f := fun i : Fin (Module.finrank ℝ E) =>
          g.inner y (B i) (C j) * g.inner y (B i) (C k))
        (s := Finset.univ)
        (x := Ψ (C j) (C k))).symm]
    -- Step (b): identify the i-sum with `g(C j, C k)` via Parseval + g.symm.
    have hParseval := g_inner_eq_orthonormal_parseval_sum (I := I) g y
      (C j) (C k) B hB_orthonormal
    -- hParseval : g(C j, C k) = ∑ i, g(C j, B i) * g(B i, C k).
    have h_sum_eq : (∑ i : Fin (Module.finrank ℝ E),
          g.inner y (B i) (C j) * g.inner y (B i) (C k)) =
        g.inner y (C j) (C k) := by
      rw [hParseval]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [g.symm y (C j) (B i)]
    rw [h_sum_eq]
    -- Step (c): orthonormality of C: g(C j, C k) = if j = k then 1 else 0.
    rw [hC_orthonormal j k]
  -- Apply per-k reduction, then collapse the k-sum to the diagonal.
  rw [Finset.sum_congr rfl (fun k _ => h_inner_per_k k)]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, one_smul]
  · intro k _ hkne
    rw [if_neg (Ne.symm hkne), zero_smul]
  · intro h_notin
    exact absurd (Finset.mem_univ j) h_notin

end RawPsiTensorial

/-! ## Part 12: unconditional smoothness of the raw tensor connection Laplacian

The earlier sections proved:

* `rawTensorConnLap_fixedFrame_contMDiff` — for a fixed smooth tangent frame
  `B`, the fixed-frame variant `rawTensorConnLap_fixedFrame g r s B T` is a
  smooth section in the base point.
* `rawTensorConnLap_eq_frame_trace` — for any `g_y`-orthonormal basis `B` of
  `T_y M`, the value `rawTensorConnLap g r s T y` equals
  `∑ i, Ψ̂_T(y)(B_i, B_i)`, the orthonormal-frame trace of the bundled raw
  second covariant derivative.

Combining these on the open neighbourhood `smoothOrthoFrameNbhd g x₀` of any
point `x₀`, the smooth orthonormal frame field `smoothOrthoFrame g x₀` is
`g_y`-orthonormal at every `y` in the neighbourhood, so the frame-trace
formula reduces `rawTensorConnLap g r s T y` to
`rawTensorConnLap_fixedFrame g r s (smoothOrthoFrame g x₀) T y`. The
fixed-frame smoothness then gives smoothness of `rawTensorConnLap` on the
neighbourhood, and local-to-global yields global smoothness. -/

section UnconditionalSmoothness

variable [CompleteSpace E]

/-- **Identification of `rawTensorConnLap` with the fixed-frame variant at
points where the fixed frame is `g`-orthonormal.** For a fixed smooth tangent
frame `B` such that `B i y` is `g_y`-orthonormal at the evaluation point `y`,
the raw connection Laplacian agrees with the fixed-frame variant at `y`. -/
theorem rawTensorConnLap_eq_fixedFrame_of_orthonormal
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB_smooth : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (y : M)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (B i y) (B j y) = if i = j then (1 : ℝ) else 0) :
    rawTensorConnLap (I := I) g r s T y =
      rawTensorConnLap_fixedFrame (I := I) g r s B T y := by
  classical
  -- Step 1: apply frame invariance with the single-point frame `fun i => B i y`.
  have h_frame_trace :
      rawTensorConnLap (I := I) g r s T y =
        ∑ i : Fin (Module.finrank ℝ E),
          rawTensorConnLap_psi_bilinAt g r s T hT_total y (B i y) (B i y) :=
    rawTensorConnLap_eq_frame_trace (I := I) g r s T hT_total y
      (fun i => B i y) hB_orth
  -- Step 2: at every `i`, identify the bilinear value with the fixed-frame
  -- summand via `rawTensorConnLap_psi_bilinAt_apply`. Each `B i` is smooth
  -- as a tangent-bundle section, hence MDifferentiableAt at `y`.
  have h_summand_eq : ∀ i : Fin (Module.finrank ℝ E),
      rawTensorConnLap_psi_bilinAt g r s T hT_total y (B i y) (B i y) =
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) (B i) T) y (B i y) -
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            T y
            ((LeviCivita (I := I) g).toFun (B i) y (B i y)) := by
    intro i
    have hBi_mdiff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun z : M => TotalSpace.mk' E
          (E := fun w : M => TangentSpace I w) z (B i z)) y :=
      (hB_smooth i).contMDiffAt.mdifferentiableAt (by simp)
    exact rawTensorConnLap_psi_bilinAt_apply (I := I) g r s T hT_total
      (X := B i) (Y := B i) hBi_mdiff hBi_mdiff
  -- Step 3: combine the two steps. The RHS sum, term by term, is exactly the
  -- fixed-frame definition.
  rw [h_frame_trace]
  rw [Finset.sum_congr rfl (fun i _ => h_summand_eq i)]
  rfl

/-- **The raw tensor connection Laplacian agrees with the fixed-frame variant
on `smoothOrthoFrameNbhd g x₀`.** For any centre point `x₀`, the smooth
orthonormal frame field `smoothOrthoFrame g x₀` is `g_y`-orthonormal at every
`y` in the open neighbourhood `smoothOrthoFrameNbhd g x₀`. Hence the raw
connection Laplacian coincides with the fixed-frame variant on the
neighbourhood. -/
private theorem rawTensorConnLap_eq_fixedFrame_smoothOrthoFrame_on_nbhd
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    rawTensorConnLap (I := I) g r s T y =
      rawTensorConnLap_fixedFrame (I := I) g r s
        (smoothOrthoFrame (I := I) g x₀) T y :=
  rawTensorConnLap_eq_fixedFrame_of_orthonormal (I := I) g r s T hT_total
    (B := smoothOrthoFrame (I := I) g x₀)
    (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) y
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hy i j)

/-- **Unconditional smoothness of the raw tensor connection Laplacian.** For a
smooth raw `(r, s)`-tensor section `T`, the raw connection Laplacian
`rawTensorConnLap g r s T` is a smooth tensor section. -/
theorem rawTensorConnLap_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s T y)) := by
  classical
  -- `ContMDiff` unfolds to `∀ x, ContMDiffAt`. We work pointwise.
  intro x₀
  -- The fixed-frame variant with the smooth orthonormal frame at `x₀` is
  -- globally smooth, in particular `ContMDiffAt` at `x₀`.
  have h_fixed : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap_fixedFrame (I := I) g r s
          (smoothOrthoFrame (I := I) g x₀) T y)) :=
    rawTensorConnLap_fixedFrame_contMDiff (I := I) g r s hT_total
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i)
  have h_fixed_at : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap_fixedFrame (I := I) g r s
          (smoothOrthoFrame (I := I) g x₀) T y)) x₀ :=
    h_fixed x₀
  -- The two section-functions agree on the neighbourhood `smoothOrthoFrameNbhd
  -- g x₀` of `x₀`. Hence they are `EventuallyEq` at `x₀`.
  have h_eventuallyEq :
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s T y)) =ᶠ[𝓝 x₀]
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap_fixedFrame (I := I) g r s
          (smoothOrthoFrame (I := I) g x₀) T y)) := by
    filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
    -- Equality of `TotalSpace.mk'` follows from equality of the fibre values
    -- at the same base.
    have h_fib : rawTensorConnLap (I := I) g r s T y =
        rawTensorConnLap_fixedFrame (I := I) g r s
          (smoothOrthoFrame (I := I) g x₀) T y :=
      rawTensorConnLap_eq_fixedFrame_smoothOrthoFrame_on_nbhd (I := I)
        g r s T hT_total x₀ hy
    -- Lift to the total space.
    exact congrArg (TotalSpace.mk' (TensorRSModel r s ℝ E)
      (E := fun z : M => TensorRSSpace r s I z) y) h_fib
  -- Transport `ContMDiffAt` along `EventuallyEq`. The `congr_of_eventuallyEq`
  -- lemma takes `f₁ =ᶠ[𝓝 x] f` and `ContMDiffAt f x` and produces
  -- `ContMDiffAt f₁ x`, so we pass `h_eventuallyEq` directly (with
  -- `f₁ = rawTensorConnLap …`, `f = rawTensorConnLap_fixedFrame …`).
  exact h_fixed_at.congr_of_eventuallyEq h_eventuallyEq

end UnconditionalSmoothness

end Connection
end Integral
end DifferentialGeometry

end

section
#print axioms DifferentialGeometry.Integral.Connection.rawTensorConnLap_psi_bilinAt
#print axioms DifferentialGeometry.Integral.Connection.rawTensorConnLap_psi_bilinAt_apply
#print axioms DifferentialGeometry.Integral.Connection.rawTensorConnLap_eq_frame_trace
#print axioms DifferentialGeometry.Integral.Connection.rawTensorConnLap_eq_fixedFrame_of_orthonormal
end
