import RicciFlower.RoughLaplacian
import RicciFlower.Coordinates.NablaComponents.TensorRS
import RicciFlower.Tensor.RSTensor.Components
import RicciFlower.Tensor.RSTensor.CotangentRiemannian
import RicciFlower.Tensor.RSTensor.MetricCompatibility
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Connection.OneJet
import RicciFlower.Tensor.Multilinear.BundleSmoothEval
import RicciFlower.Operators.HessianTrace

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Metric traces of mixed tensors

This file contains the small intrinsic metric-trace adapters needed to turn a
connection-variation tensor `A : T*M ⊗ T*M ⊗ TM` into the one-form
`V ↦ tr_g ((X,Y) ↦ g(A(X,Y), V))`.
-/

namespace RicciFlower
namespace Realized

noncomputable section

open Bundle Tensor0SBundle Filter
open RicciFlower.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Linear trace functional on the one upper slot of a `(1,2)` tensor after
lowering that slot by a supplied covector. -/
private def connTraceEvalLin
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x →ₗ[Real]
      Real where
  toFun β :=
    metricTrace0S2InBasis (I := I)
      (Coordinates.coordinateFrameAt_toBasis (I := I) x)
      (fun k l : Coordinates.CoordinateIdx (𝕜 := Real) E =>
        Coordinates.inverseMetricFlatModelInChart_component (I := I) g x k l
          (extChartAt I x x))
      (A β) Fin.elim0
  map_add' β γ := by
    simp only [metricTrace0S2InBasis, map_add, ContinuousMultilinearMap.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring_nf
  map_smul' c β := by
    simp only [metricTrace0S2InBasis, map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [mul_left_comm]

/-- Pointwise one-form obtained by metric-tracing a `(1,2)` tensor:
`V ↦ tr_g ((X,Y) ↦ g(A(X,Y), V))`. -/
def connTraceOneFormAt
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  dualToCotangent (I := I)
    ((connTraceEvalLin (I := I) g A).comp
      ((dualToCotangentLinear (I := I)).comp (tangentFlatLinear (I := I) g x)))

@[simp] theorem connTraceOneFormAt_apply
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x)
    (V : TangentSpace I x) :
    cotangentToDual (I := I) (connTraceOneFormAt (I := I) g A) V =
      metricTraceFirstTwo0STensor (I := I) g
        (A (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) V)))
        Fin.elim0 := by
  unfold connTraceOneFormAt connTraceEvalLin
  rw [cotangentToDual_dualToCotangent]
  rw [metricTraceFirstTwo0STensor_apply]
  exact metricTrace0S2InBasis_eq_metricTrace (I := I) g
    (Coordinates.coordinateFrameAt_toBasis (I := I) x)
    (fun k l : Coordinates.CoordinateIdx (𝕜 := Real) E =>
      Coordinates.inverseMetricFlatModelInChart_component (I := I) g x k l
        (extChartAt I x x))
    (Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x)
    (A (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) V))) Fin.elim0

/-- Basis-coordinate formula for the pointwise connection-trace one-form. -/
theorem connTraceOneFormAt_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (q : Idx) :
    cotangentToDual (I := I) (connTraceOneFormAt (I := I) g A) (basis q) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (A (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) (basis q))))
            (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0) := by
  rw [connTraceOneFormAt_apply]
  rw [metricTraceFirstTwo0STensor_apply]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  rfl

/-- Pointwise tangent vector obtained by raising the metric trace one-form. -/
def connTraceAt
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x) :
    TangentSpace I x :=
  cotangentSharp (I := I) g x (connTraceOneFormAt (I := I) g A)

@[simp] theorem connTraceAt_eq
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x) :
    connTraceAt (I := I) g A =
      cotangentSharp (I := I) g x (connTraceOneFormAt (I := I) g A) := by
  rfl

/-- Basis-coordinate reconstruction of the raised trace vector. -/
theorem connTraceAt_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv) :
    connTraceAt (I := I) g A =
      ∑ p : Idx,
        (∑ q : Idx,
          gInv p q *
            (∑ i : Idx, ∑ j : Idx,
              gInv i j *
                (A (dualToCotangent (I := I)
                    ((tangentFlatLinear (I := I) g x) (basis q))))
                  (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0))) •
          basis p := by
  rw [connTraceAt_eq]
  rw [cotangentSharp_eq_sum_inv (I := I) g x basis gInv hinv]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [connTraceOneFormAt_coord (I := I) g A basis gInv hinv q]

private theorem sumFinOne {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 1 → Idx) → α) :
    (∑ r : Fin 1 → Idx, F r) =
      ∑ r : Idx, F (fun _ : Fin 1 => r) := by
  classical
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) Idx)
    F (fun r : Idx => F (fun _ : Fin 1 => r))]
  intro r
  congr 1
  funext a
  simpa [Equiv.funUnique] using congrArg r (Subsingleton.elim a (0 : Fin 1))

private theorem traceFlat_apply_sum
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (q i j : Idx) :
    (A (dualToCotangent (I := I)
        ((tangentFlatLinear (I := I) g x) (basis q))))
      (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0) =
      ∑ r : Idx,
        g.inner x (basis q) (basis r) *
          componentRS (I := I) basis A
            (fun _ : Fin 1 => r)
            (fun a : Fin 2 => if a = 0 then i else j) := by
  have h := componentRS_apply_input_eq_sum (I := I) basis A
    (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) (basis q)))
    (fun a : Fin 2 => if a = 0 then i else j)
  have hslots :
      metricTraceInput (I := I) (basis i) (basis j) Fin.elim0 =
        (fun a : Fin 2 => if a = 0 then basis i else basis j) := by
    funext a
    fin_cases a <;> rfl
  calc
    (A (dualToCotangent (I := I)
        ((tangentFlatLinear (I := I) g x) (basis q))))
      (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0) =
        ∑ r : Fin 1 → Idx,
          (dualToCotangent (I := I)
            ((tangentFlatLinear (I := I) g x) (basis q)))
              (fun a : Fin 1 => basis (r a)) *
            componentRS (I := I) basis A r
              (fun a : Fin 2 => if a = 0 then i else j) := by
          rw [hslots]
          simpa [component0S_apply] using h
    _ =
      ∑ r : Idx,
        g.inner x (basis q) (basis r) *
          componentRS (I := I) basis A
            (fun _ : Fin 1 => r)
            (fun a : Fin 2 => if a = 0 then i else j) := by
        rw [sumFinOne]
        simp [dualToCotangent_apply, tangentFlatLinear_apply]

private theorem sumFourComm
    {ι κ η μ α : Type*} [Fintype ι] [Fintype κ] [Fintype η] [Fintype μ]
    [AddCommMonoid α]
    (F : ι → κ → η → μ → α) :
    (∑ a : ι, ∑ b : κ, ∑ c : η, ∑ d : μ, F a b c d) =
      ∑ b : κ, ∑ c : η, ∑ d : μ, ∑ a : ι, F a b c d := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]

private theorem traceAlg
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gInv G : Idx → Idx → Real)
    (C : Idx → Idx → Idx → Real)
    (hInv : ∀ a b : Idx, (∑ q : Idx, gInv a q * G q b) =
      (if a = b then 1 else 0))
    (p : Idx) :
    (∑ q : Idx,
      gInv p q *
        (∑ i : Idx, ∑ j : Idx,
          gInv i j * (∑ r : Idx, G q r * C r i j))) =
      ∑ i : Idx, ∑ j : Idx, gInv i j * C p i j := by
  classical
  calc
    (∑ q : Idx,
      gInv p q *
        (∑ i : Idx, ∑ j : Idx,
          gInv i j * (∑ r : Idx, G q r * C r i j))) =
      ∑ q : Idx,
        ∑ i : Idx,
          ∑ j : Idx,
            ∑ r : Idx,
              gInv p q * (gInv i j * (G q r * C r i j)) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        calc
          gInv p q * (gInv i j * (∑ r : Idx, G q r * C r i j)) =
              (gInv p q * gInv i j) *
                (∑ r : Idx, G q r * C r i j) := by ring
          _ = ∑ r : Idx,
              (gInv p q * gInv i j) * (G q r * C r i j) := by
            rw [Finset.mul_sum]
          _ = ∑ r : Idx,
              gInv p q * (gInv i j * (G q r * C r i j)) := by
            apply Finset.sum_congr rfl
            intro r _
            ring
      _ =
      ∑ i : Idx,
        ∑ j : Idx,
          ∑ r : Idx,
            ∑ q : Idx,
              gInv p q * (gInv i j * (G q r * C r i j)) := by
        exact sumFourComm
          (fun q i j r => gInv p q * (gInv i j * (G q r * C r i j)))
      _ =
      ∑ i : Idx,
        ∑ j : Idx,
          ∑ r : Idx,
            (∑ q : Idx, gInv p q * G q r) *
              (gInv i j * C r i j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro r _
        calc
          ∑ q : Idx, gInv p q * (gInv i j * (G q r * C r i j)) =
              ∑ q : Idx, (gInv p q * G q r) * (gInv i j * C r i j) := by
            apply Finset.sum_congr rfl
            intro q _
            ring
          _ = (∑ q : Idx, gInv p q * G q r) *
              (gInv i j * C r i j) := by
            rw [Finset.sum_mul]
      _ =
      ∑ i : Idx,
        ∑ j : Idx,
          ∑ r : Idx,
            (if p = r then 1 else 0) *
              (gInv i j * C r i j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro r _
        rw [hInv p r]
      _ = ∑ i : Idx, ∑ j : Idx, gInv i j * C p i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_eq_single p]
        · simp
        · intro r _ hr
          have hpr : p ≠ r := fun h => hr h.symm
          simp [hpr]
        · intro hp
          exact False.elim (hp (Finset.mem_univ _))

/-- Coefficient form of `connTraceAt`: after raising the traced one-form, the
`p`-th coordinate is the inverse-metric trace of the `(1,2)` tensor components
with upper index `p`. -/
theorem connTraceCoeff
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (A : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (p : Idx) :
    basis.repr (connTraceAt (I := I) g A) p =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          componentRS (I := I) basis A
            (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) := by
  classical
  let coeff : Idx → Real := fun p0 =>
    ∑ q : Idx,
      gInv p0 q *
        (∑ i : Idx, ∑ j : Idx,
          gInv i j *
            (A (dualToCotangent (I := I)
                ((tangentFlatLinear (I := I) g x) (basis q))))
              (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0))
  have hvec :
      connTraceAt (I := I) g A =
        ∑ p0 : Idx, coeff p0 • basis p0 := by
    simpa [coeff] using connTraceAt_coord (I := I) g A basis gInv hinv
  have hcoeff :
      basis.repr (connTraceAt (I := I) g A) p = coeff p := by
    rw [hvec]
    rw [map_sum]
    simp only [map_smul, Module.Basis.repr_self]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    change (∑ c : Idx, Finsupp.single c (coeff c)) p = coeff p
    rw [Finsupp.finset_sum_apply
      (S := Finset.univ)
      (f := fun c : Idx => (Finsupp.single c (coeff c) : Idx →₀ Real))
      (a := p)]
    calc
      (∑ c : Idx, (Finsupp.single c (coeff c) : Idx →₀ Real) p) =
          (Finsupp.single p (coeff p) : Idx →₀ Real) p := by
        refine Finset.sum_eq_single
          (s := Finset.univ)
          (f := fun c : Idx => (Finsupp.single c (coeff c) : Idx →₀ Real) p)
          (a := p) ?_ ?_
        · intro b _ hb
          simpa using
            (Finsupp.single_eq_of_ne hb.symm :
              (Finsupp.single b (coeff b) : Idx →₀ Real) p = 0)
        · intro hp
          exact False.elim (hp (Finset.mem_univ _))
      _ = coeff p := by
        rw [Finsupp.single_eq_same]
  rw [hcoeff]
  dsimp [coeff]
  simp_rw [traceFlat_apply_sum (I := I) g A basis]
  exact traceAlg gInv (fun q r => g.inner x (basis q) (basis r))
    (fun r i j =>
      componentRS (I := I) basis A
        (fun _ : Fin 1 => r)
        (fun q : Fin 2 => if q = 0 then i else j))
    (fun a b => (hinv a b).1) p

private theorem gInvComp_contMDiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        inverseMetricFlatModelInChart_component (I := I) g x₀ i j
          (extChartAt I x₀ y)) x₀ := by
  haveI : CompleteSpace E := FiniteDimensional.complete Real E
  let f : E → Real :=
    inverseMetricFlatModelInChart_component (I := I) g x₀ i j
  have hf :
      ContDiffWithinAt Real ∞ f (Set.range I) (extChartAt I x₀ x₀) :=
    inverseMetricFlatModelInChart_component_contDiffWithinAt (I := I) g x₀ i j
  have hchart :
      ContMDiffWithinAt I 𝓘(Real, E) ∞ (extChartAt I x₀)
        (extChartAt I x₀).source x₀ :=
    (contMDiffAt_extChartAt (I := I) (x := x₀)).contMDiffWithinAt
  have hcomp :
      ContMDiffWithinAt I 𝓘(Real, Real) ∞ (f ∘ extChartAt I x₀)
        (extChartAt I x₀).source x₀ := by
    exact hf.comp_contMDiffWithinAt hchart (by
      intro y hy
      exact extChartAt_target_subset_range x₀ ((extChartAt I x₀).map_source hy))
  have hcompAt :
      ContMDiffAt I 𝓘(Real, Real) ∞ (f ∘ extChartAt I x₀) x₀ :=
    hcomp.contMDiffAt ((isOpen_extChartAt_source (I := I) x₀).mem_nhds
      (mem_extChartAt_source (I := I) x₀))
  simpa [f, Function.comp_def] using hcompAt

/-- Local coordinate expansion of the intrinsic trace of a smooth covariant
two-tensor field. -/
private theorem trace02_eventually
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M) :
    (fun y : M => metricTracePair0SAt (I := I) g (A y)) =ᶠ[nhds x₀]
      fun y : M =>
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ y) *
              A y
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y) := by
  classical
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with y hy
  let basis := coordinateFrameAt_basis (I := I) x₀ hy
  let gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x₀ i j
        (extChartAt I x₀ y)
  have htrace :=
    metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv
      (gInvBasisAt (I := I) g x₀ hy) (A y)
  calc
    metricTracePair0SAt (I := I) g (A y) =
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            gInv i j * A y (vec2 (I := I) (basis i) (basis j)) := htrace
    _ =
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ y) *
              A y
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      apply congrArg
      funext q
      fin_cases q <;>
        simp [basis, coordinateFrameAt_basis_apply, Curvature.vec2]

/-- The metric trace of a smooth covariant two-tensor field is smooth. -/
theorem trace02_smooth
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun x : M => metricTracePair0SAt (I := I) g (A x)) := by
  classical
  intro x₀
  have hRhs :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                  (extChartAt I x₀ y) *
                A y
        (fun q : Fin 2 =>
          coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y))
        x₀ := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    exact (gInvComp_contMDiffAt (I := I) g x₀ i j).mul
      (Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
        (𝕜 := Real) (I := I) (M := M) A x₀
        (fun q : Fin 2 => if q = 0 then i else j))
  exact hRhs.congr_of_eventuallyEq (trace02_eventually (I := I) g A x₀)

theorem connTraceCoeff_eventually
    (g : SmoothRiemannianMetric I M)
    (A : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (x₀ : M) (p : CoordinateIdx (𝕜 := Real) E) :
    (fun y : M =>
        (coordinateFrameAt_isLocalFrame (I := I) x₀).coeff p y
          (connTraceAt (I := I) g (A y))) =ᶠ[nhds x₀]
      fun y : M =>
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ y) *
              (A y
                (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                  (I := I) (M := M) 1 x₀
                  ((continuousMultilinearMap_basis
                    (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                    (fun _ : Fin 1 => p)) y))
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y) := by
  classical
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with y hy
  let basis := coordinateFrameAt_basis (I := I) x₀ hy
  let gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x₀ i j
        (extChartAt I x₀ y)
  have hcoeff :=
    connTraceCoeff (I := I) g (A y) basis gInv
      (gInvBasisAt (I := I) g x₀ hy) p
  calc
    (coordinateFrameAt_isLocalFrame (I := I) x₀).coeff p y
        (connTraceAt (I := I) g (A y))
        =
          basis.repr (connTraceAt (I := I) g (A y)) p := by
            simp [basis, coordinateFrameAt_basis, IsLocalFrameOn.coeff, hy]
    _ =
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            gInv i j *
              componentRS (I := I) basis (A y)
                (fun _ : Fin 1 => p)
                (fun q : Fin 2 => if q = 0 then i else j) := hcoeff
    _ =
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ y) *
              (A y
                (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                  (I := I) (M := M) 1 x₀
                  ((continuousMultilinearMap_basis
                    (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                    (fun _ : Fin 1 => p)) y))
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          have hconst :=
            constInChart_basisTensor0S_coordFrame (𝕜 := Real) (I := I)
              (M := M) (r := 1) x₀ hy (fun _ : Fin 1 => p)
          simp [basis, componentRS_apply, coordinateFrameAt_basis_apply,
            hconst]

private theorem connTraceCoeff_contMDiffAt
    (g : SmoothRiemannianMetric I M)
    (A : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (x₀ : M) (p : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        (coordinateFrameAt_isLocalFrame (I := I) x₀).coeff p y
          (connTraceAt (I := I) g (A y))) x₀ := by
  classical
  have hRhs :
      ContMDiffAt I 𝓘(Real, Real) ∞
        (fun y : M =>
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                  (extChartAt I x₀ y) *
                (A y
                  (Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
                    (I := I) (M := M) 1 x₀
                    ((continuousMultilinearMap_basis
                      (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
                      (fun _ : Fin 1 => p)) y))
                  (fun q : Fin 2 =>
                    coordinateFrameAt (I := I) x₀ (if q = 0 then i else j) y))
        x₀ := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    exact (gInvComp_contMDiffAt (I := I) g x₀ i j).mul
      (tensorRS_eval_constInChart_coordinateFrame_contMDiffAt
        (𝕜 := Real) (I := I) (M := M) A x₀
        (fun _ : Fin 1 => p)
        (fun q : Fin 2 => if q = 0 then i else j))
  exact hRhs.congr_of_eventuallyEq
    (connTraceCoeff_eventually (I := I) g A x₀ p)

/-- Smooth tangent section obtained by metric-tracing a smooth `(1,2)` tensor. -/
def connTraceField
    (g : SmoothRiemannianMetric I M)
    (A : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) := by
  refine ⟨fun x : M => connTraceAt (I := I) g (A x), ?_⟩
  intro x₀
  exact (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt_of_coeff
    (fun p => connTraceCoeff_contMDiffAt (I := I) g A x₀ p)
    ((coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀))

@[simp] theorem connTraceField_apply
    (g : SmoothRiemannianMetric I M)
    (A : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) :
    connTraceField (I := I) g A x = connTraceAt (I := I) g (A x) := rfl

/-- Coordinate-frame coefficient formula for the bundled metric trace field. -/
theorem connTraceField_coord
    (g : SmoothRiemannianMetric I M)
    (A : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (p : CoordinateIdx (𝕜 := Real) E) :
    (coordinateFrameAt_isLocalFrame (I := I) x₀).coeff p x
        (connTraceField (I := I) g A x) =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x₀ i j
              (extChartAt I x₀ x) *
            componentRS (I := I) (coordinateFrameAt_basis (I := I) x₀ hx)
              (A x) (fun _ : Fin 1 => p)
              (fun q : Fin 2 => if q = 0 then i else j) := by
  classical
  let basis := coordinateFrameAt_basis (I := I) x₀ hx
  let gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x₀ i j
        (extChartAt I x₀ x)
  have hcoeff :=
    connTraceCoeff (I := I) g (A x) basis gInv
      (gInvBasisAt (I := I) g x₀ hx) p
  calc
    (coordinateFrameAt_isLocalFrame (I := I) x₀).coeff p x
        (connTraceField (I := I) g A x)
        =
          basis.repr (connTraceAt (I := I) g (A x)) p := by
            simp [basis, coordinateFrameAt_basis, IsLocalFrameOn.coeff, hx]
    _ =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInv i j *
            componentRS (I := I) basis (A x) (fun _ : Fin 1 => p)
              (fun q : Fin 2 => if q = 0 then i else j) := hcoeff
    _ =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x₀ i j
              (extChartAt I x₀ x) *
            componentRS (I := I) (coordinateFrameAt_basis (I := I) x₀ hx)
              (A x) (fun _ : Fin 1 => p)
              (fun q : Fin 2 => if q = 0 then i else j) := rfl

private theorem metricField_eq0S
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.metricTensorField (I := I) g x =
      metricTensor0S (I := I) g x := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply Tensor0SBundle.ext0S_basis (I := I) basis
  intro slots
  simp [Tensor0SBundle.component0S_apply]

private theorem finCons_vec2_eq_vec3 {x : M}
    (X Y Z : TangentSpace I x) :
    Fin.cons X (vec2 (I := I) Y Z) = vec3 (I := I) X Y Z := by
  funext a
  fin_cases a <;> rfl

private theorem tensor0S_update_zero {s : ℕ} {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s -> TangentSpace I x) (a : Fin s) :
    A (Function.update slots a 0) = 0 := by
  exact A.map_coord_zero a (by simp)

private def trace04Slots
    (i j : CoordinateIdx (𝕜 := Real) E)
    (tail : Fin 2 -> CoordinateIdx (𝕜 := Real) E) :
    Fin 4 -> CoordinateIdx (𝕜 := Real) E
  | ⟨0, _⟩ => i
  | ⟨1, _⟩ => j
  | ⟨2, _⟩ => tail 0
  | ⟨3, _⟩ => tail 1

private theorem trace04Slots_apply {x₀ y : M}
    (i j : CoordinateIdx (𝕜 := Real) E)
    (tail : Fin 2 -> CoordinateIdx (𝕜 := Real) E) :
    metricTraceInput (I := I)
        (coordinateFrameAt (I := I) x₀ i y)
        (coordinateFrameAt (I := I) x₀ j y)
        (fun q : Fin 2 => coordinateFrameAt (I := I) x₀ (tail q) y) =
      fun q : Fin 4 =>
        coordinateFrameAt (I := I) x₀ (trace04Slots i j tail q) y := by
  funext q
  fin_cases q <;> rfl

private theorem trace04Event
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x₀ : M) (tail : Fin 2 -> CoordinateIdx (𝕜 := Real) E) :
    (fun y : M =>
        metricTraceFirstTwo0STensor (I := I) g (A y)
          (fun q : Fin 2 =>
            coordinateFrameAt (I := I) x₀ (tail q) y)) =ᶠ[nhds x₀]
      fun y : M =>
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ y) *
              A y
                (fun q : Fin 4 =>
                  coordinateFrameAt (I := I) x₀ (trace04Slots i j tail q) y) := by
  classical
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with y hy
  let basis := coordinateFrameAt_basis (I := I) x₀ hy
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x₀ i j
        (extChartAt I x₀ y)
  have htrace :=
    metricTraceFirstTwo0STensor_apply (I := I) g (A y)
      (fun q : Fin 2 => coordinateFrameAt (I := I) x₀ (tail q) y)
  have hsum :=
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv
      (gInvBasisAt (I := I) g x₀ hy) (A y)
      (fun q : Fin 2 => coordinateFrameAt (I := I) x₀ (tail q) y)
  calc
    metricTraceFirstTwo0STensor (I := I) g (A y)
        (fun q : Fin 2 =>
          coordinateFrameAt (I := I) x₀ (tail q) y)
        =
      metricTraceFirstTwo0SAt (I := I) g (A y)
        (fun q : Fin 2 =>
          coordinateFrameAt (I := I) x₀ (tail q) y) := htrace
    _ =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInv i j *
            (A y)
              (metricTraceInput (I := I) (basis i) (basis j)
                (fun q : Fin 2 =>
                  coordinateFrameAt (I := I) x₀ (tail q) y)) := hsum
    _ =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x₀ i j
              (extChartAt I x₀ y) *
            A y
              (fun q : Fin 4 =>
                coordinateFrameAt (I := I) x₀ (trace04Slots i j tail q) y) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        simpa [basis, coordinateFrameAt_basis_apply] using
          congrArg (fun slots => A y slots)
            (trace04Slots_apply (I := I) (x₀ := x₀) (y := y) i j tail)

private theorem trace04Coeff
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x₀ : M) (tail : Fin 2 -> CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun y : M =>
        metricTraceFirstTwo0STensor (I := I) g (A y)
          (fun q : Fin 2 =>
            coordinateFrameAt (I := I) x₀ (tail q) y)) x₀ := by
  classical
  have hRhs :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                  (extChartAt I x₀ y) *
                A y
                  (fun q : Fin 4 =>
                    coordinateFrameAt (I := I) x₀ (trace04Slots i j tail q) y))
        x₀ := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    exact (gInvComp_contMDiffAt (I := I) g x₀ i j).mul
      (Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
        (𝕜 := Real) (I := I) (M := M) A x₀
        (trace04Slots i j tail))
  exact hRhs.congr_of_eventuallyEq
    (trace04Event (I := I) g A x₀ tail)

set_option backward.isDefEq.respectTransparency false in
/-- Smooth `(0,2)` field obtained by tracing the first two slots of a smooth
`(0,4)` tensor field. -/
def trace04Field
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := by
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 2
  let F : (p : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 p :=
    fun p : M => metricTraceFirstTwo0STensor (I := I) g (A p)
  refine ⟨F, ?_⟩
  let d := Module.finrank Real E
  let b : Module.Basis (Fin d) Real E := Module.finBasis Real E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  have hcoeff := trace04Coeff (I := I) g A x₀ σ
  refine hcoeff.congr_of_eventuallyEq ?_
  let e := coordinateTrivializationAt (𝕜 := Real) (I := I) x₀
  have hx₀ : x₀ ∈ coordinateFrameSet (𝕜 := Real) (I := I) x₀ :=
    coordinateFrameAt_mem (𝕜 := Real) (I := I) x₀
  filter_upwards [(coordinateFrameSet_open (𝕜 := Real) (I := I) x₀).mem_nhds hx₀]
    with y hy
  rw [continuousMultilinearMap_basis_repr]
  change ((trivializationAt (Tensor0SModel 2 Real E)
      (Bundle.continuousMultilinearMap Real 2 E
        (TangentSpace I : M -> Type _)) x₀
      ⟨y, F y⟩).2)
      (fun a : Fin 2 => b (σ a)) =
    metricTraceFirstTwo0STensor (I := I) g (A y)
      (fun q : Fin 2 => coordinateFrameAt (I := I) x₀ (σ q) y)
  change (F y).compContinuousLinearMap
      (fun _ : Fin 2 =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real y)
      (fun a : Fin 2 => b (σ a)) =
    metricTraceFirstTwo0STensor (I := I) g (A y)
      (fun q : Fin 2 => coordinateFrameAt (I := I) x₀ (σ q) y)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr
  funext q
  change
    (coordinateTrivializationAt (𝕜 := Real) (I := I) x₀).symmL Real y
        (b (σ q)) =
      coordinateFrameAt (I := I) x₀ (σ q) y
  change e.symmL Real y (b (σ q)) = e.localFrame b (σ q) y
  rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
    (e := e) (b := b) (i := σ q) hy]
  rfl

@[simp] theorem trace04Field_apply
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) :
    trace04Field (I := I) (M := M) g A x =
      metricTraceFirstTwo0STensor (I := I) g (A x) := by
  rfl

private theorem metricTraceInput_vec2_eq_vec4 {x : M}
    (X Y Z U : TangentSpace I x) :
    metricTraceInput (I := I) X Y (vec2 (I := I) Z U) =
      vec4 (I := I) X Y Z U := by
  funext a
  fin_cases a <;> rfl

private def freezeTail04Slots
    (x₀ : M) (σ : Fin 2 -> CoordinateIdx (𝕜 := Real) E)
    (Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    Fin 4 -> (y : M) -> TangentSpace I y
  | ⟨0, _⟩ => coordinateFrameAt (I := I) x₀ (σ 0)
  | ⟨1, _⟩ => coordinateFrameAt (I := I) x₀ (σ 1)
  | ⟨2, _⟩ => fun y => Y y
  | ⟨3, _⟩ => fun y => Z y

private theorem freezeTail04Slots_vec4
    (x₀ y : M) (σ : Fin 2 -> CoordinateIdx (𝕜 := Real) E)
    (Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    (fun q : Fin 4 => freezeTail04Slots (I := I) x₀ σ Y Z q y) =
      vec4 (I := I)
        (coordinateFrameAt (I := I) x₀ (σ 0) y)
        (coordinateFrameAt (I := I) x₀ (σ 1) y)
        (Y y) (Z y) := by
  funext q
  fin_cases q <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- Freeze the last two slots of a smooth `(0,4)` tensor field against two
smooth tangent sections, leaving a smooth `(0,2)` tensor field in the first two
slots. -/
noncomputable def freezeTail04Field
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := by
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 2
  let F : (p : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 p :=
    fun p : M => freezeFirstTwo0S (I := I) (A p)
      (vec2 (I := I) (Y p) (Z p))
  refine ⟨F, ?_⟩
  let d := Module.finrank Real E
  let b : Module.Basis (Fin d) Real E := Module.finBasis Real E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  have hcoeff :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          A y (fun q : Fin 4 => freezeTail04Slots (I := I) x₀ σ Y Z q y))
        x₀ := by
    let v : Fin 4 -> (y : M) -> TangentSpace I y :=
      fun q y => freezeTail04Slots (I := I) x₀ σ Y Z q y
    have hv : ∀ q : Fin 4,
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun y : M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) y (v q y)) x₀ := by
      intro q
      fin_cases q
      · exact (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀)
          (coordinateFrameAt_mem (I := I) x₀) (σ 0)
      · exact (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀)
          (coordinateFrameAt_mem (I := I) x₀) (σ 1)
      · exact Y.contMDiff x₀
      · exact Z.contMDiff x₀
    have hA := TensorMultilinear.contMDiffAt_section_apply
      (𝕜 := Real) (I := I) (M := M) (n := 4)
      (T := fun y : M => A y) (A.contMDiff x₀) v hv
    simpa [v, Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
      using hA
  refine hcoeff.congr_of_eventuallyEq ?_
  let e := coordinateTrivializationAt (𝕜 := Real) (I := I) x₀
  have hx₀ : x₀ ∈ coordinateFrameSet (𝕜 := Real) (I := I) x₀ :=
    coordinateFrameAt_mem (𝕜 := Real) (I := I) x₀
  filter_upwards [(coordinateFrameSet_open (𝕜 := Real) (I := I) x₀).mem_nhds hx₀]
    with y hy
  rw [continuousMultilinearMap_basis_repr]
  change ((trivializationAt (Tensor0SModel 2 Real E)
      (Bundle.continuousMultilinearMap Real 2 E
        (TangentSpace I : M -> Type _)) x₀
      ⟨y, F y⟩).2)
      (fun a : Fin 2 => b (σ a)) =
    A y (fun q : Fin 4 => freezeTail04Slots (I := I) x₀ σ Y Z q y)
  change (F y).compContinuousLinearMap
      (fun _ : Fin 2 =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real y)
      (fun a : Fin 2 => b (σ a)) =
    A y (fun q : Fin 4 => freezeTail04Slots (I := I) x₀ σ Y Z q y)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hslot :
      (fun a : Fin 2 =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real y
          (b (σ a))) =
        vec2 (I := I)
          (coordinateFrameAt (I := I) x₀ (σ 0) y)
          (coordinateFrameAt (I := I) x₀ (σ 1) y) := by
    funext q
    fin_cases q
    · change
        (coordinateTrivializationAt (𝕜 := Real) (I := I) x₀).symmL Real y
            (b (σ 0)) =
          coordinateFrameAt (I := I) x₀ (σ 0) y
      change e.symmL Real y (b (σ 0)) = e.localFrame b (σ 0) y
      rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
        (e := e) (b := b) (i := σ 0) hy]
      rfl
    · change
        (coordinateTrivializationAt (𝕜 := Real) (I := I) x₀).symmL Real y
            (b (σ 1)) =
          coordinateFrameAt (I := I) x₀ (σ 1) y
      change e.symmL Real y (b (σ 1)) = e.localFrame b (σ 1) y
      rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
        (e := e) (b := b) (i := σ 1) hy]
      rfl
  rw [hslot]
  rw [freezeFirstTwo0S_apply]
  rw [metricTraceInput_vec2_eq_vec4]
  rw [freezeTail04Slots_vec4]

@[simp] theorem freezeTail04Field_apply
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    freezeTail04Field (I := I) (M := M) A Y Z x =
      freezeFirstTwo0S (I := I) (A x) (vec2 (I := I) (Y x) (Z x)) := by
  rfl

/-- Metric-compatible covariant differentiation commutes with the metric trace
of a smooth `(0,2)` tensor, in the concrete basis form used by the contracted
Bianchi interface. -/
theorem nablaTrace02
    [T2Space M] [CompleteSpace E] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) g x basis gInv)
    (X : TangentSpace I x) :
    let traceA : M -> Real := fun y => metricTracePair0SAt (I := I) g (A y)
    let nablaA :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov A x
    let dTrace := differential1FormFun (I := I) traceA x
    dTrace (fun _ : Fin 1 => X) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * nablaA (vec3 (I := I) X (basis i) (basis j)) := by
  classical
  let traceA : M -> Real := fun y => metricTracePair0SAt (I := I) g (A y)
  let nablaA :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov A x
  let dTrace := differential1FormFun (I := I) traceA x
  let Xsec : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x X).choose
  have hXsec : Xsec x = X :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x X).choose_spec
  have hinner :=
    inner0S_two_nabla (I := I) cov g hmc
      (Tensor0SBundle.metricTensorField (I := I) g) A Xsec x
  have hmetric :
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov Xsec
        (Tensor0SBundle.metricTensorField (I := I) g) x = 0 :=
    Tensor0SBundle.nabla_metric_zero (I := I) cov g hmc Xsec x
  have htrace :
      extDerivFun (I := I) traceA x (Xsec x) =
        metricTracePair0SAt (I := I) g
          (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov Xsec A x) := by
    have hfun :
        traceA =
          fun y : M =>
            inner0S (I := I) g y 2
              (Tensor0SBundle.metricTensorField (I := I) g y) (A y) := by
      funext y
      simp [traceA, metricTracePair0SAt, metricField_eq0S]
    have hzero :
        inner0S (I := I) g x 2
          (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
          (A x) = 0 := by
      change (((tensor0SMetricData (I := I) g x 2).flat)
          (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x))
          (A x) = 0
      have hflat :
          (tensor0SMetricData (I := I) g x 2).flat
            (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 x) = 0 := by
        exact LinearMap.map_zero
          ((tensor0SMetricData (I := I) g x 2).flat.toLinearMap :
            Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 x →ₗ[Real]
            Module.Dual Real
              (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                2 x))
      rw [hflat]
      rfl
    rw [hfun]
    rw [hinner, hmetric]
    rw [hzero]
    simp [metricTracePair0SAt, metricField_eq0S]
  have hnabla :
      ∀ i j : Idx,
        nablaA (vec3 (I := I) X (basis i) (basis j)) =
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov Xsec A x (vec2 (I := I) (basis i) (basis j)) := by
    intro i j
    have h :=
      totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov Xsec A x
        (vec2 (I := I) (basis i) (basis j))
    simpa [nablaA, hXsec, finCons_vec2_eq_vec3 (I := I)] using h
  calc
    dTrace (fun _ : Fin 1 => X)
        = extDerivFun (I := I) traceA x X := by
            simp [dTrace, differential1FormFun_apply_eq_extDerivFun]
    _ = extDerivFun (I := I) traceA x (Xsec x) := by
            rw [hXsec]
    _ = metricTracePair0SAt (I := I) g
          (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov Xsec A x) := htrace
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j *
            nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 cov Xsec A x (vec2 (I := I) (basis i) (basis j)) := by
            exact metricTracePair0SAt_eq_sum_basis
              (I := I) g basis gInv hinv
              (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
                2 cov Xsec A x)
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j * nablaA (vec3 (I := I) X (basis i) (basis j)) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rw [hnabla i j]

private theorem tailFreezeNabla
    [T2Space M] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M}
    (hYzero : ((cov (fun p : M => Y p) x) (X x)) = 0)
    (hZzero : ((cov (fun p : M => Z p) x) (X x)) = 0)
    (U V : TangentSpace I x) :
    let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2 :=
      freezeTail04Field (I := I) (M := M) A Y Z
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B x (vec3 (I := I) (X x) U V) =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov A x (Fin.cons (X x) (vec4 (I := I) U V (Y x) (Z x))) := by
  classical
  let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    freezeTail04Field (I := I) (M := M) A Y Z
  obtain ⟨Usec, hUsec, hUcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x U
  obtain ⟨Vsec, hVsec, hVcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x V
  let V2 : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)
    | ⟨0, _⟩ => Usec
    | ⟨1, _⟩ => Vsec
  let V4 : Fin 4 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)
    | ⟨0, _⟩ => Usec
    | ⟨1, _⟩ => Vsec
    | ⟨2, _⟩ => Y
    | ⟨3, _⟩ => Z
  have hBtot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov X B x (vec2 (I := I) U V)
  have hAtot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 cov X A x
      (vec4 (I := I) U V (Y x) (Z x))
  have hBeval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V2 B x
  have hAeval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V4 A x
  have hderiv :
      extDerivFun (I := I)
          (fun p : M => B p (fun a : Fin 2 => V2 a p)) x (X x) =
        extDerivFun (I := I)
          (fun p : M => A p (fun a : Fin 4 => V4 a p)) x (X x) := by
    have hfun :
        (fun p : M => B p (fun a : Fin 2 => V2 a p)) =
          fun p : M => A p (fun a : Fin 4 => V4 a p) := by
      funext p
      have hV2p :
          (fun a : Fin 2 => V2 a p) =
            vec2 (I := I) (Usec p) (Vsec p) := by
        funext a
        fin_cases a <;> rfl
      have hV4p :
          (fun a : Fin 4 => V4 a p) =
            vec4 (I := I) (Usec p) (Vsec p) (Y p) (Z p) := by
        funext a
        fin_cases a <;> rfl
      rw [hV2p, hV4p]
      simp [B, metricTraceInput_vec2_eq_vec4]
    rw [hfun]
  have hBcorr :
      (∑ a : Fin 2,
        B x
          (Function.update (fun b : Fin 2 => V2 b x) a
            ((cov (fun p : M => V2 a p) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_two]
    simp [V2, hUcov X, hVcov X, tensor0S_update_zero]
  have hAcorr :
      (∑ a : Fin 4,
        A x
          (Function.update (fun b : Fin 4 => V4 b x) a
            ((cov (fun p : M => V4 a p) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_four]
    simp [V4, hUcov X, hVcov X, hYzero, hZzero, tensor0S_update_zero]
  calc
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B x (vec3 (I := I) (X x) U V)
        =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov X B x (vec2 (I := I) U V) := by
        simpa [finCons_vec2_eq_vec3 (I := I), hUsec, hVsec] using hBtot
    _ =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov X A x (vec4 (I := I) U V (Y x) (Z x)) := by
        have hV2x :
            (fun a : Fin 2 => V2 a x) = vec2 (I := I) U V := by
          funext a
          fin_cases a <;> simp [V2, hUsec, hVsec, Curvature.vec2]
        have hV4x :
            (fun a : Fin 4 => V4 a x) =
              vec4 (I := I) U V (Y x) (Z x) := by
          funext a
          fin_cases a <;> simp [V4, hUsec, hVsec, Curvature.vec4]
        rw [← hV2x, ← hV4x]
        rw [hBeval, hAeval, hderiv, hBcorr, hAcorr]
    _ =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov A x (Fin.cons (X x) (vec4 (I := I) U V (Y x) (Z x))) := by
        simpa [hUsec, hVsec] using hAtot.symm

/-- Metric-compatible covariant differentiation commutes with tracing the
first two covariant slots of a smooth `(0,4)` tensor field. -/
theorem nablaTrace04
    [T2Space M] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (g : SmoothRiemannianMetric I M)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) g x basis gInv)
    (X Y Z : TangentSpace I x) :
    let traceA := trace04Field (I := I) (M := M) g A
    let nablaA :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov A x
    let nablaTraceA :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov traceA x
    nablaTraceA (vec3 (I := I) X Y Z) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * nablaA (Fin.cons X (vec4 (I := I) (basis i) (basis j) Y Z)) := by
  classical
  let traceA := trace04Field (I := I) (M := M) g A
  let nablaA :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 cov A x
  let nablaTraceA :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov traceA x
  obtain ⟨Xsec, hXsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x X
  obtain ⟨Ysec, hYsec, hYcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x Y
  obtain ⟨Zsec, hZsec, hZcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x Z
  let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    freezeTail04Field (I := I) (M := M) A Ysec Zsec
  let traceB : M -> Real := fun y => metricTracePair0SAt (I := I) g (B y)
  let dTraceB := differential1FormFun (I := I) traceB x
  let V2 : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)
    | ⟨0, _⟩ => Ysec
    | ⟨1, _⟩ => Zsec
  have htot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov Xsec traceA x (vec2 (I := I) Y Z)
  have heval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov Xsec V2 traceA x
  have hfun :
      (fun p : M => traceA p (fun a : Fin 2 => V2 a p)) = traceB := by
    funext p
    have hV2p :
        (fun a : Fin 2 => V2 a p) = vec2 (I := I) (Ysec p) (Zsec p) := by
      funext a
      fin_cases a <;> rfl
    rw [hV2p]
    simp [traceA, traceB, B, metricTraceFirstTwo0SAt]
  have hcorr :
      (∑ a : Fin 2,
        traceA x
          (Function.update (fun b : Fin 2 => V2 b x) a
            ((cov (fun p : M => V2 a p) x) (Xsec x)))) = 0 := by
    rw [Fin.sum_univ_two]
    simp [traceA, V2, hYcov Xsec, hZcov Xsec, tensor0S_update_zero]
  have hleft :
      nablaTraceA (vec3 (I := I) X Y Z) =
        dTraceB (fun _ : Fin 1 => X) := by
    calc
      nablaTraceA (vec3 (I := I) X Y Z)
          =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov Xsec traceA x (vec2 (I := I) Y Z) := by
          simpa [nablaTraceA, hXsec, finCons_vec2_eq_vec3 (I := I)] using htot
      _ = extDerivFun (I := I) traceB x (Xsec x) := by
          have hV2x :
              (fun a : Fin 2 => V2 a x) = vec2 (I := I) Y Z := by
            funext a
            fin_cases a <;> simp [V2, hYsec, hZsec, Curvature.vec2]
          rw [← hV2x]
          rw [heval, hcorr]
          rw [hfun]
          ring
      _ = dTraceB (fun _ : Fin 1 => X) := by
          simp [dTraceB, differential1FormFun_apply_eq_extDerivFun, hXsec]
  have htrace02 :
      dTraceB (fun _ : Fin 1 => X) =
        ∑ i : Idx, ∑ j : Idx,
          gInv i j *
            (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 cov B x) (vec3 (I := I) X (basis i) (basis j)) := by
    simpa [B, traceB, dTraceB] using
      nablaTrace02 (I := I) (M := M) cov g hmc B basis gInv hinv X
  dsimp
  rw [hleft, htrace02]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hfreeze :=
    tailFreezeNabla (I := I) (M := M) cov hcov A Xsec Ysec Zsec
      (hYcov Xsec) (hZcov Xsec) (basis i) (basis j)
  simpa [B, nablaA, hXsec, hYsec, hZsec] using hfreeze

end

end Realized
end RicciFlower
