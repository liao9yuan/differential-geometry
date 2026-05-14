import RicciFlower.Realized.CurvatureTensor
import RicciFlower.Tensor.RSTensor.Tensor0SRiemannian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Rough Laplacian Preparation

This file provides the basis-level metric trace interface used by the scalar
and one-form Bochner layer.  It intentionally does not claim that the traced
object is already the intrinsic rough Laplacian tensor operation; that bridge is
recorded as an explicit realization predicate.
-/

namespace RicciFlower
namespace Realized

noncomputable section

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Insert two distinguished tangent vectors into the first two slots of a
covariant tensor input, leaving the remaining `s` slots to `tail`. -/
def metricTraceInput {x : M} {s : ℕ}
    (X Y : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    Fin (s + 2) -> TangentSpace I x :=
  Fin.cases X (Fin.cases Y tail)

/-- The metric as a pointwise covariant two-tensor. -/
def metricTensor0S (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  (((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm.toContinuousLinearMap).comp
    (g.inner x)).uncurryLeft

@[simp]
theorem metricTensor0S_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 -> TangentSpace I x) :
    metricTensor0S (I := I) g x v = g.inner x (v 0) (v 1) := by
  simp [metricTensor0S, Fin.tail]

/-- Intrinsic metric trace of a covariant two-tensor, expressed as the metric
inner product with the metric tensor itself.  The metric tensor is placed in
the first argument so the existing direct `(0,2)` coordinate theorem rewrites
to the usual `g^{ij} B_{ij}` without needing a separate inverse-symmetry
lemma. -/
def metricTracePair0SAt (g : SmoothRiemannianMetric I M)
    {x : M}
    (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Real :=
  inner0S (I := I) g x 2 (metricTensor0S (I := I) g x) B

/-- Construction frontier for freezing all but the first two slots of a
covariant tensor.  This is mathematically just partial evaluation of a
continuous multilinear map; the remaining work is bundled-continuity
bookkeeping. -/
theorem exists_freezeFirstTwo0S {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    ∃ B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x,
      ∀ X Y : TangentSpace I x,
        B (vec2 (I := I) X Y) = T (metricTraceInput (I := I) X Y tail) := by
  -- Frontier: bundle partial evaluation of a continuous multilinear map.
  sorry

/-- Freeze all but the first two slots of a covariant tensor. -/
def freezeFirstTwo0S {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  Classical.choose (exists_freezeFirstTwo0S (I := I) T tail)

@[simp]
theorem freezeFirstTwo0S_apply {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) (X Y : TangentSpace I x) :
    freezeFirstTwo0S (I := I) T tail (vec2 (I := I) X Y) =
      T (metricTraceInput (I := I) X Y tail) := by
  exact Classical.choose_spec (exists_freezeFirstTwo0S (I := I) T tail) X Y

/-- Construction frontier for freezing the first slot of a `(0,3)` tensor and
leaving the last two slots variable. -/
theorem exists_freezeLastTwo0S3 {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) :
    ∃ B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x,
      ∀ X Z : TangentSpace I x,
        B (vec2 (I := I) X Z) = T (vec3 (I := I) Y X Z) := by
  -- Frontier: bundle partial evaluation of a continuous multilinear map.
  sorry

/-- Freeze the first slot of a `(0,3)` tensor and trace the last two slots. -/
def freezeLastTwo0S3 {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  Classical.choose (exists_freezeLastTwo0S3 (I := I) T Y)

@[simp]
theorem freezeLastTwo0S3_apply {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y X Z : TangentSpace I x) :
    freezeLastTwo0S3 (I := I) T Y (vec2 (I := I) X Z) =
      T (vec3 (I := I) Y X Z) := by
  exact Classical.choose_spec (exists_freezeLastTwo0S3 (I := I) T Y) X Z

/-- Intrinsic metric trace of the first two covariant slots. -/
def metricTraceFirstTwo0SAt (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) : Real :=
  metricTracePair0SAt (I := I) g (freezeFirstTwo0S (I := I) T tail)

/-- Intrinsic metric trace of the last two slots of a `(0,3)` tensor after
freezing the first slot. -/
def metricTraceLastTwo0SAt3 (g : SmoothRiemannianMetric I M)
    {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) : Real :=
  metricTracePair0SAt (I := I) g (freezeLastTwo0S3 (I := I) T Y)

/-- Basis-level metric trace of the first two covariant slots of a `(0,s+2)`
tensor. This is the coordinate-side preparation interface for the rough
Laplacian. -/
def metricTrace0S2InBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    gInv i j * T (metricTraceInput (I := I) (basis i) (basis j) tail)

/-- Coordinate formula for the intrinsic trace of a `(0,2)` tensor. -/
theorem metricTracePair0SAt_eq_sum_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    metricTracePair0SAt (I := I) g B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * B (vec2 (I := I) (basis i) (basis j)) := by
  -- Frontier: finite-sum contraction of `inner0S_two_eq_coord_direct`
  -- with the metric tensor.
  sorry

/-- Coordinate formula for the intrinsic trace of the first two slots. -/
theorem metricTraceFirstTwo0SAt_eq_sum_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g T tail =
      metricTrace0S2InBasis (I := I) basis gInv T tail := by
  rw [metricTraceFirstTwo0SAt, metricTracePair0SAt_eq_sum_basis
    (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp

/-- Coordinate formula for the intrinsic trace of the last two slots of a
`(0,3)` tensor after freezing the first slot. -/
theorem metricTraceLastTwo0SAt3_eq_sum_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) :
    metricTraceLastTwo0SAt3 (I := I) g T Y =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * T (vec3 (I := I) Y (basis i) (basis j)) := by
  rw [metricTraceLastTwo0SAt3, metricTracePair0SAt_eq_sum_basis
    (I := I) g basis gInv hinv]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp

/-- A coordinate trace sum computes the intrinsic first-two-slot trace. -/
theorem metricTrace0S2InBasis_eq_metricTrace
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTrace0S2InBasis (I := I) basis gInv T tail =
      metricTraceFirstTwo0SAt (I := I) g T tail :=
  (metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv T tail).symm

/-- Basis independence of the first-two-slot coordinate trace. -/
theorem metricTrace0S2InBasis_eq_metricTrace0S2InBasis
    (g : SmoothRiemannianMetric I M)
    {Idx₁ Idx₂ : Type*} [Fintype Idx₁] [DecidableEq Idx₁]
    [Fintype Idx₂] [DecidableEq Idx₂]
    {x : M}
    (basis₁ : Module.Basis Idx₁ Real (TangentSpace I x))
    (gInv₁ : Idx₁ -> Idx₁ -> Real)
    (hinv₁ : MetricInverseInBasis (I := I) g x basis₁ gInv₁)
    (basis₂ : Module.Basis Idx₂ Real (TangentSpace I x))
    (gInv₂ : Idx₂ -> Idx₂ -> Real)
    (hinv₂ : MetricInverseInBasis (I := I) g x basis₂ gInv₂)
    {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTrace0S2InBasis (I := I) basis₁ gInv₁ T tail =
      metricTrace0S2InBasis (I := I) basis₂ gInv₂ T tail := by
  rw [metricTrace0S2InBasis_eq_metricTrace (I := I) g basis₁ gInv₁ hinv₁ T tail,
    metricTrace0S2InBasis_eq_metricTrace (I := I) g basis₂ gInv₂ hinv₂ T tail]

/-- Basis-level rough Laplacian value of a covariant tensor, represented as the
metric trace of a supplied second covariant derivative tensor. -/
def roughLap0SAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) : Real :=
  metricTrace0S2InBasis (I := I) basis gInv nabla2A tail

/-- One-form specialization of the basis-level rough Laplacian interface. -/
def roughLap1FormAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (Y : TangentSpace I x) : Real :=
  roughLap0SAt (I := I) basis gInv (s := 1) nabla2α (fun _ : Fin 1 => Y)

/-- Basis-level realization predicate saying that a supplied rough Laplacian
tensor is the coordinate metric trace of a supplied second covariant derivative
tensor. This is a compatibility interface; the primary predicate below is
basis-free. -/
def RoughLap0SRealizesMetricTraceInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) : Prop :=
  ∀ tail : Fin s -> TangentSpace I x,
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail

theorem roughLap0SAt_eq_of_realizes
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (h : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv roughA nabla2A)
    (tail : Fin s -> TangentSpace I x) :
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail :=
  h tail

theorem roughLap1FormAt_eq_of_realizes
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv (s := 1) roughα nabla2α)
    (Y : TangentSpace I x) :
    roughα (fun _ : Fin 1 => Y) =
      roughLap1FormAt (I := I) basis gInv nabla2α Y :=
  h (fun _ : Fin 1 => Y)

/-!
## Intrinsic-facing realization predicates

The primary rough-Laplacian interface is now basis-free: a supplied tensor
realizes a metric trace when it agrees with `metricTraceFirstTwo0SAt`.  Basis
and inverse-metric components appear only in coordinate wrappers below.
-/

/-- A supplied `(0,s)` tensor realizes the metric trace of a supplied
`(0,s+2)` tensor. -/
def metric_trace_0s
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (traceT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x) : Prop :=
  ∀ tail : Fin s -> TangentSpace I x,
    traceT tail = metricTraceFirstTwo0SAt (I := I) g T tail

/-- Primary basis-free rough Laplacian realization for covariant tensors. -/
def RoughLap0SRealizesMetricTrace
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) : Prop :=
  metric_trace_0s (I := I) g nabla2A roughA

/-- Intrinsic-facing rough Laplacian realization for covariant tensors. -/
def rough_lap_0s
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x) : Prop :=
  RoughLap0SRealizesMetricTrace (I := I) g roughA nabla2A

/-- One-form specialization of the intrinsic-facing rough Laplacian interface. -/
def rough_lap_one_form
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 x) : Prop :=
  rough_lap_0s (I := I) g (s := 1) nabla2α roughα

theorem metric_trace_0s_apply_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (traceT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x)
    (htrace : metric_trace_0s (I := I) g T traceT)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (tail : Fin s -> TangentSpace I x) :
    traceT tail = metricTrace0S2InBasis (I := I) basis gInv T tail :=
  by
    rw [htrace tail]
    exact (metricTrace0S2InBasis_eq_metricTrace (I := I) g basis gInv hinv T tail).symm

theorem rough_lap_0s_apply_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x)
    (hrough : rough_lap_0s (I := I) g nabla2A roughA)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (tail : Fin s -> TangentSpace I x) :
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail :=
  by
    simpa [rough_lap_0s, roughLap0SAt] using
      metric_trace_0s_apply_basis (I := I) g basis gInv nabla2A roughA hrough hinv tail

theorem rough_lap_one_form_apply_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 x)
    (hrough : rough_lap_one_form (I := I) g nabla2α roughα)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Y : TangentSpace I x) :
    roughα (fun _ : Fin 1 => Y) =
      roughLap1FormAt (I := I) basis gInv nabla2α Y :=
  by
    simpa [rough_lap_one_form, rough_lap_0s, roughLap1FormAt, roughLap0SAt] using
      rough_lap_0s_apply_basis (I := I) g basis gInv nabla2α roughα hrough hinv
        (fun _ : Fin 1 => Y)

/-- Basis-level realization extracted from the intrinsic one-form rough
Laplacian interface. -/
theorem rough_lap_one_form_realizes_metric_trace
    (g : SmoothRiemannianMetric I M)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 x)
    (hrough : rough_lap_one_form (I := I) g nabla2α roughα)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv) :
    RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv
      (s := 1) roughα nabla2α := by
  intro tail
  simpa [rough_lap_one_form, rough_lap_0s, roughLap0SAt] using
    rough_lap_0s_apply_basis (I := I) g basis gInv nabla2α roughα hrough hinv tail

end

end Realized
end RicciFlower
