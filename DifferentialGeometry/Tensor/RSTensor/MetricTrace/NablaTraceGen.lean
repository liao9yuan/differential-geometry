import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Higher
import DifferentialGeometry.Tensor.RSTensor.NablaDomDomCongr

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# General-rank metric-trace / covariant-derivative commutation (formalism A)

This file generalises the fixed-rank `nablaTrace02` / `nablaTrace04`
(`MetricTrace/NablaTrace02.lean`, `MetricTrace/Higher.lean`) to the
**general-rank** metric trace of the first two slots,
`metricTraceFirstTwo0S : (0, s+2) → (0, s)`, needed for the rough Laplacian of
`∇ᵏRm` in the all-`k` BBS `StarSum2` route
(`Geometry/Flow/RicciFlow/Evolution/BBSAllKBundledRoute.md`).

The pointwise tail-freeze `freezeFirstTwo0S` (`Geometry/Operator/RoughLaplacian.lean`)
is already rank-uniform; the only missing piece is the **smooth-field** wrapper.
`freezeTailField` is the rank-`s` generalisation of `freezeTail04Field`
(`MetricTrace/NablaTrace02.lean`): freeze the last `s` slots of a smooth
`(0, s+2)` field against `s` smooth sections, leaving the first two free as a
smooth `(0, 2)` field.  Its output is always `(0, 2)`, so the bundle-trivialisation
part of the smoothness proof is identical to the `s = 2` case; only the input slot
tuple `Fin (s+2)` generalises.
-/

namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle Tensor0SBundle Filter
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The `Fin (s+2)` slot tuple for freezing the last `s` slots: the two free slots
carry the coordinate-frame fields `σ 0, σ 1`, the last `s` carry the frozen
sections `Y`.  This is `metricTraceInput` with the trace pair as the coordinate
frame and the tail as `Y`. -/
private def freezeTailSlots {s : ℕ}
    (x₀ : M) (σ : Fin 2 → CoordinateIdx (𝕜 := Real) E)
    (Y : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Fin (s + 2) → (y : M) → TangentSpace I y :=
  fun q y => metricTraceInput (I := I)
    (coordinateFrameAt (I := I) x₀ (σ 0) y)
    (coordinateFrameAt (I := I) x₀ (σ 1) y)
    (fun b : Fin s => Y b y) q

set_option backward.isDefEq.respectTransparency false in
/-- **Freeze the last `s` slots of a smooth `(0, s+2)` tensor field** against `s`
smooth tangent sections, leaving a smooth `(0, 2)` tensor field in the first two
slots.  Rank-`s` generalisation of `freezeTail04Field`. -/
noncomputable def freezeTailField {s : ℕ}
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (Y : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := by
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 2
  let F : (p : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 p :=
    fun p : M => freezeFirstTwo0S (I := I) (A p) (fun b : Fin s => Y b p)
  refine ⟨F, ?_⟩
  let d := Module.finrank Real E
  let b : Module.Basis (Fin d) Real E := Module.finBasis Real E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  have hcoeff :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          A y (fun q : Fin (s + 2) => freezeTailSlots (I := I) x₀ σ Y q y))
        x₀ := by
    let v : Fin (s + 2) → (y : M) → TangentSpace I y :=
      fun q y => freezeTailSlots (I := I) x₀ σ Y q y
    have hv : ∀ q : Fin (s + 2),
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun y : M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) y (v q y)) x₀ := by
      intro q
      refine Fin.cases ?_ (fun i => ?_) q
      · -- slot 0: the first free slot, coordinate frame `σ 0`
        have hframe :
            ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
              (fun y : M =>
                TotalSpace.mk' E (E := fun x : M => TangentSpace I x) y
                  (coordinateFrameAt (I := I) x₀ (σ 0) y)) x₀ :=
          (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
            (coordinateFrameSet_open (I := I) x₀)
            (coordinateFrameAt_mem (I := I) x₀) (σ 0)
        refine hframe.congr_of_eventuallyEq ?_
        filter_upwards with y
        simp [v, freezeTailSlots, metricTraceInput]
      · refine Fin.cases ?_ (fun c => ?_) i
        · -- slot 1: the second free slot, coordinate frame `σ 1`
          have hframe :
              ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
                (fun y : M =>
                  TotalSpace.mk' E (E := fun x : M => TangentSpace I x) y
                    (coordinateFrameAt (I := I) x₀ (σ 1) y)) x₀ :=
            (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
              (coordinateFrameSet_open (I := I) x₀)
              (coordinateFrameAt_mem (I := I) x₀) (σ 1)
          refine hframe.congr_of_eventuallyEq ?_
          filter_upwards with y
          simp only [v, freezeTailSlots, metricTraceInput, Fin.cases_succ,
            Fin.cases_zero]
        · -- slot `succ (succ c)`: the frozen section `Y c`
          have hYc := (Y c).contMDiff x₀
          refine hYc.congr_of_eventuallyEq ?_
          filter_upwards with y
          simp [v, freezeTailSlots, metricTraceInput]
    have hA := TensorMultilinear.contMDiffAt_section_apply_gen
      (𝕜 := Real) (I := I) (M := M) (n := s + 2)
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
        (TangentSpace I : M → Type _)) x₀
      ⟨y, F y⟩).2)
      (fun a : Fin 2 => b (σ a)) =
    A y (fun q : Fin (s + 2) => freezeTailSlots (I := I) x₀ σ Y q y)
  change (F y).compContinuousLinearMap
      (fun _ : Fin 2 =>
        (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL Real y)
      (fun a : Fin 2 => b (σ a)) =
    A y (fun q : Fin (s + 2) => freezeTailSlots (I := I) x₀ σ Y q y)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hslot :
      (fun a : Fin 2 =>
        (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL Real y
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
  rfl

@[simp] theorem freezeTailField_apply {s : ℕ}
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (Y : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    freezeTailField (I := I) (M := M) A Y x =
      freezeFirstTwo0S (I := I) (A x) (fun b : Fin s => Y b x) := by
  rfl

/-- **The covariant derivative of the tail-frozen field equals `∇A` on the
assembled slots.**  Rank-`s` generalisation of `tailFreezeNabla` (`Higher.lean`):
for tail sections `Y` parallel-at-`x` along `X`, the total covariant derivative of
`freezeTailField A Y` along `X`, evaluated on the two free slots `(U, V)`, equals
`∇A` on the new derivative slot `X` followed by `(U, V)` and the frozen tail. -/
private theorem tailFreezeNablaGen {s : ℕ}
    [T2Space M] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Y : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    {x : M}
    (hYzero : ∀ b : Fin s, ((cov (fun p : M => Y b p) x) (X x)) = 0)
    (U V : TangentSpace I x) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov (freezeTailField (I := I) (M := M) A Y) x (vec3 (I := I) (X x) U V) =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) cov A x
        (Fin.cons (X x) (metricTraceInput (I := I) U V (fun b : Fin s => Y b x))) := by
  classical
  set B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := freezeTailField (I := I) (M := M) A Y with hBdef
  obtain ⟨Usec, hUsec, hUcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x U
  obtain ⟨Vsec, hVsec, hVcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x V
  let V2 : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)
    | ⟨0, _⟩ => Usec
    | ⟨1, _⟩ => Vsec
  let Vfull : Fin (s + 2) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    Fin.cons Usec (Fin.cons Vsec Y)
  have hVfullp : ∀ p : M,
      (fun q : Fin (s + 2) => Vfull q p) =
        metricTraceInput (I := I) (Usec p) (Vsec p) (fun b : Fin s => Y b p) := by
    intro p
    funext q
    refine Fin.cases ?_ (fun i => ?_) q
    · rfl
    · refine Fin.cases ?_ (fun c => ?_) i <;> rfl
  have hBtot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov X B x (vec2 (I := I) U V)
  have hAtot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (s + 2) cov X A x
      (metricTraceInput (I := I) U V (fun b : Fin s => Y b x))
  have hBeval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V2 B x
  have hAeval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X Vfull A x
  have hderiv :
      extDerivFun (I := I)
          (fun p : M => B p (fun a : Fin 2 => V2 a p)) x (X x) =
        extDerivFun (I := I)
          (fun p : M => A p (fun a : Fin (s + 2) => Vfull a p)) x (X x) := by
    have hfun :
        (fun p : M => B p (fun a : Fin 2 => V2 a p)) =
          fun p : M => A p (fun a : Fin (s + 2) => Vfull a p) := by
      funext p
      have hV2p :
          (fun a : Fin 2 => V2 a p) = vec2 (I := I) (Usec p) (Vsec p) := by
        funext a
        fin_cases a <;> rfl
      rw [hV2p, hVfullp p, hBdef, freezeTailField_apply, freezeFirstTwo0S_apply]
    rw [hfun]
  have hBcorr :
      (∑ a : Fin 2,
        B x
          (Function.update (fun b : Fin 2 => V2 b x) a
            ((cov (fun p : M => V2 a p) x) (X x)))) = 0 := by
    rw [Fin.sum_univ_two]
    simp [V2, hUcov X, hVcov X, metricTrace_tensor0S_update_zero]
  have hAcorr :
      (∑ a : Fin (s + 2),
        A x
          (Function.update (fun b : Fin (s + 2) => Vfull b x) a
            ((cov (fun p : M => Vfull a p) x) (X x)))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    have hz : (cov (fun p : M => Vfull a p) x) (X x) = 0 := by
      refine Fin.cases ?_ (fun i => ?_) a
      · simpa only [Vfull, Fin.cons_zero] using hUcov X
      · refine Fin.cases ?_ (fun c => ?_) i
        · simpa only [Vfull, Fin.cons_succ, Fin.cons_zero] using hVcov X
        · simpa only [Vfull, Fin.cons_succ] using hYzero c
    rw [hz]
    simp [metricTrace_tensor0S_update_zero]
  calc
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov B x (vec3 (I := I) (X x) U V)
        =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov X B x (vec2 (I := I) U V) := by
        simpa [metricTrace_finCons_vec2_eq_vec3 (I := I), hUsec, hVsec] using hBtot
    _ =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) cov X A x
        (metricTraceInput (I := I) U V (fun b : Fin s => Y b x)) := by
        have hV2x :
            (fun a : Fin 2 => V2 a x) = vec2 (I := I) U V := by
          funext a
          fin_cases a <;> simp [V2, hUsec, hVsec, DifferentialGeometry.Integral.Connection.vec2]
        have hVfullx :
            (fun a : Fin (s + 2) => Vfull a x) =
              metricTraceInput (I := I) U V (fun b : Fin s => Y b x) := by
          rw [hVfullp x, hUsec, hVsec]
        rw [← hV2x, ← hVfullx]
        rw [hBeval, hAeval, hderiv, hBcorr, hAcorr]
    _ =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) cov A x
        (Fin.cons (X x)
          (metricTraceInput (I := I) U V (fun b : Fin s => Y b x))) :=
        hAtot.symm

/-! ## The general-rank metric-trace field `metricTraceFirstTwoField` -/

/-- The `Fin (s+2)` coordinate-index tuple for the first-two metric trace: `i, j`
in the two trace slots, `σ` in the `s`-slot tail. -/
private def traceFirstTwoIdx {s : ℕ}
    (i j : CoordinateIdx (𝕜 := Real) E)
    (σ : Fin s -> CoordinateIdx (𝕜 := Real) E) :
    Fin (s + 2) -> CoordinateIdx (𝕜 := Real) E :=
  Fin.cons i (Fin.cons j σ)

private theorem metricTraceInput_coordFrame {s : ℕ} (x₀ y : M)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (σ : Fin s -> CoordinateIdx (𝕜 := Real) E) :
    metricTraceInput (I := I) (coordinateFrameAt (I := I) x₀ i y)
        (coordinateFrameAt (I := I) x₀ j y)
        (fun c : Fin s => coordinateFrameAt (I := I) x₀ (σ c) y) =
      fun q : Fin (s + 2) =>
        coordinateFrameAt (I := I) x₀ (traceFirstTwoIdx i j σ q) y := by
  funext q
  refine Fin.cases ?_ (fun c => ?_) q
  · rfl
  · refine Fin.cases ?_ (fun d => ?_) c <;> rfl

private theorem metricTraceFirstTwoEvent {s : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (x₀ : M) (σ : Fin s -> CoordinateIdx (𝕜 := Real) E) :
    (fun y : M =>
        metricTraceFirstTwo0STensor (I := I) g (A y)
          (fun c : Fin s => coordinateFrameAt (I := I) x₀ (σ c) y)) =ᶠ[nhds x₀]
      fun y : M =>
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ y) *
              A y (fun q : Fin (s + 2) =>
                coordinateFrameAt (I := I) x₀ (traceFirstTwoIdx i j σ q) y) := by
  classical
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with y hy
  let basis := coordinateFrameAt_basis (I := I) x₀ hy
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x₀ i j
        (extChartAt I x₀ y)
  rw [metricTraceFirstTwo0STensor_apply (I := I) g (A y)
    (fun c : Fin s => coordinateFrameAt (I := I) x₀ (σ c) y)]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv
    (gInvBasisAt (I := I) g x₀ hy) (A y)
    (fun c : Fin s => coordinateFrameAt (I := I) x₀ (σ c) y)]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simpa [basis, coordinateFrameAt_basis_apply] using
    congrArg (fun slots => A y slots)
      (metricTraceInput_coordFrame (I := I) x₀ y i j σ)

private theorem metricTraceFirstTwoCoeff {s : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (x₀ : M) (σ : Fin s -> CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun y : M =>
        metricTraceFirstTwo0STensor (I := I) g (A y)
          (fun c : Fin s => coordinateFrameAt (I := I) x₀ (σ c) y)) x₀ := by
  classical
  have hRhs :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                  (extChartAt I x₀ y) *
                A y
                  (fun q : Fin (s + 2) =>
                    coordinateFrameAt (I := I) x₀ (traceFirstTwoIdx i j σ q) y))
        x₀ := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    exact (gInvComp_contMDiffAt (I := I) g x₀ i j).mul
      (DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
        (𝕜 := Real) (I := I) (M := M) A x₀ (traceFirstTwoIdx i j σ))
  exact hRhs.congr_of_eventuallyEq
    (metricTraceFirstTwoEvent (I := I) g A x₀ σ)

set_option backward.isDefEq.respectTransparency false in
/-- **Smooth `(0,s)` field obtained by the metric trace of the first two slots of a
smooth `(0, s+2)` tensor field.**  Rank-`s` generalisation of `trace04Field`
(`Trace04.lean`), tracing slots `0, 1` directly (no `domDomCongr`). -/
def metricTraceFirstTwoField {s : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s := by
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) s
  let F : (p : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s p :=
    fun p : M => metricTraceFirstTwo0STensor (I := I) g (A p)
  refine ⟨F, ?_⟩
  let d := Module.finrank Real E
  let b : Module.Basis (Fin d) Real E := Module.finBasis Real E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  have hcoeff := metricTraceFirstTwoCoeff (I := I) g A x₀ σ
  refine hcoeff.congr_of_eventuallyEq ?_
  let e := coordinateTrivializationAt (𝕜 := Real) (I := I) x₀
  have hx₀ : x₀ ∈ coordinateFrameSet (𝕜 := Real) (I := I) x₀ :=
    coordinateFrameAt_mem (𝕜 := Real) (I := I) x₀
  filter_upwards [(coordinateFrameSet_open (𝕜 := Real) (I := I) x₀).mem_nhds hx₀]
    with y hy
  rw [continuousMultilinearMap_basis_repr]
  change ((trivializationAt (Tensor0SModel s Real E)
      (Bundle.continuousMultilinearMap Real s E
        (TangentSpace I : M -> Type _)) x₀
      ⟨y, F y⟩).2)
      (fun a : Fin s => b (σ a)) =
    metricTraceFirstTwo0STensor (I := I) g (A y)
      (fun q : Fin s => coordinateFrameAt (I := I) x₀ (σ q) y)
  change (F y).compContinuousLinearMap
      (fun _ : Fin s =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real y)
      (fun a : Fin s => b (σ a)) =
    metricTraceFirstTwo0STensor (I := I) g (A y)
      (fun q : Fin s => coordinateFrameAt (I := I) x₀ (σ q) y)
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

@[simp] theorem metricTraceFirstTwoField_apply {s : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (x : M) :
    metricTraceFirstTwoField (I := I) (M := M) g A x =
      metricTraceFirstTwo0STensor (I := I) g (A x) := by
  rfl

/-- The first-two metric trace of a `(0, s+2)` tensor equals the scalar pair trace
of the tail-frozen `(0,2)` tensor.  Both expand to `Σᵢⱼ gⁱʲ T(eᵢ, eⱼ, tail)`. -/
private theorem metricTraceFirstTwo0STensor_eq_pair_freeze {s : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) (x : M)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0STensor (I := I) g T tail =
      metricTracePair0SAt (I := I) g (freezeFirstTwo0S (I := I) T tail) := by
  classical
  let basis := coordinateFrameAt_toBasis (I := I) x
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x i j (extChartAt I x x)
  have hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv := by
    simpa [basis, gInv] using
      (inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x)
  rw [metricTraceFirstTwo0STensor_apply (I := I) g T tail]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv T tail]
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv
    (freezeFirstTwo0S (I := I) T tail)]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [freezeFirstTwo0S_apply]

/-- **The general-rank metric-trace / covariant-derivative commutation (formalism A).**
For a smooth `(0, s+2)` tensor field `A`, covariant differentiation along `X`
commutes with the first-two metric trace, with the new derivative slot prepended
and the trace pair shifted to slots `1, 2`:

`∇(metricTraceFirstTwoField g A)(X :: tail)
  = Σᵢⱼ gⁱʲ · ∇A (X :: eᵢ :: eⱼ :: tail)`.

The trace itself commutes with `∇` cleanly (no curvature term); the curvature
correction appears only later, when comparing this slot-shifted trace to the
standard rough-Laplacian trace.  Rank-`s` generalisation of `nablaTrace04`,
assembled from `freezeTailField`, `tailFreezeNablaGen`, `metricTraceFirstTwoField`,
and the scalar `nablaTrace02`. -/
theorem nabla_metricTraceFirstTwo0S {s : ℕ}
    [T2Space M] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv)
    (X : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov (metricTraceFirstTwoField (I := I) (M := M) g A) x (Fin.cons X tail) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (s + 2) cov A x
            (Fin.cons X (metricTraceInput (I := I) (basis i) (basis j) tail)) := by
  classical
  obtain ⟨Xsec, hXsec⟩ :=
    ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x X
  choose Vtail hVtailx hVtailcov using fun b : Fin s =>
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x (tail b)
  let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := freezeTailField (I := I) (M := M) A Vtail
  let traceB : M -> Real := fun y => metricTracePair0SAt (I := I) g (B y)
  have htot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov Xsec (metricTraceFirstTwoField (I := I) (M := M) g A) x
      (fun b : Fin s => tail b)
  have heval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov Xsec Vtail
      (metricTraceFirstTwoField (I := I) (M := M) g A) x
  have hfun :
      (fun p : M =>
          metricTraceFirstTwoField (I := I) (M := M) g A p
            (fun a : Fin s => Vtail a p)) = traceB := by
    funext p
    simp only [traceB, B, metricTraceFirstTwoField_apply, freezeTailField_apply]
    rw [metricTraceFirstTwo0STensor_eq_pair_freeze (I := I) g p (A p)
      (fun a : Fin s => Vtail a p)]
  have hcorr :
      (∑ a : Fin s,
        metricTraceFirstTwoField (I := I) (M := M) g A x
          (Function.update (fun b : Fin s => Vtail b x) a
            ((cov (fun p : M => Vtail a p) x) (Xsec x)))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    rw [hVtailcov a Xsec]
    simp [metricTrace_tensor0S_update_zero]
  have hVtailx_fun : (fun a : Fin s => Vtail a x) = fun b : Fin s => tail b := by
    funext a; exact hVtailx a
  have hleft :
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov (metricTraceFirstTwoField (I := I) (M := M) g A) x (Fin.cons X tail) =
        differential1FormFun (I := I) traceB x (fun _ : Fin 1 => X) := by
    have hconsX : Fin.cons (Xsec x) (fun b : Fin s => tail b) =
        (Fin.cons X tail : Fin (s + 1) -> TangentSpace I x) := by
      rw [hXsec]
    calc
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov (metricTraceFirstTwoField (I := I) (M := M) g A) x (Fin.cons X tail)
          =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov Xsec (metricTraceFirstTwoField (I := I) (M := M) g A) x
          (fun b : Fin s => tail b) := by
          rw [← hconsX]; exact htot
      _ = extDerivFun (I := I) traceB x (Xsec x) := by
          rw [← hVtailx_fun, heval, hcorr, hfun, sub_zero]
      _ = differential1FormFun (I := I) traceB x (fun _ : Fin 1 => X) := by
          simp [differential1FormFun_apply_eq_extDerivFun, hXsec]
  have htrace02 :
      differential1FormFun (I := I) traceB x (fun _ : Fin 1 => X) =
        ∑ i : Idx, ∑ j : Idx,
          gInv i j *
            totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 cov B x (vec3 (I := I) X (basis i) (basis j)) := by
    simpa [traceB] using
      nablaTrace02 (I := I) (M := M) cov g hmc B basis gInv hinv X
  rw [hleft, htrace02]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hfreeze :=
    tailFreezeNablaGen (I := I) (M := M) cov hcov A Xsec Vtail
      (fun b => hVtailcov b Xsec) (basis i) (basis j)
  rw [← hXsec, show tail = (fun b : Fin s => Vtail b x) from (funext hVtailx).symm]
  exact hfreeze

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise coordinate formula for the first-two metric trace field, with the
canonical centred chart inverse metric. -/
theorem metricTraceFirstTwoField_eq_sum {s : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (x : M) (tail : Fin s -> TangentSpace I x) :
    (metricTraceFirstTwoField (I := I) (M := M) g A) x tail =
      metricTrace0S2InBasis (I := I)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x)
        (fun k l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
          DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
            (I := I) g x k l (extChartAt I x x))
        (A x) tail := by
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x)
      (fun k l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
        DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
          (I := I) g x k l (extChartAt I x x))
      (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) g x)
      (A x) tail]

set_option backward.isDefEq.respectTransparency false in
/-- **The first-two metric trace field is additive.** -/
theorem metricTraceFirstTwoField_add {s : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2)) :
    metricTraceFirstTwoField (I := I) (M := M) g (A + B)
      = metricTraceFirstTwoField (I := I) (M := M) g A
        + metricTraceFirstTwoField (I := I) (M := M) g B := by
  classical
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
  refine DFunLike.ext _ _ fun x => ?_
  refine ContinuousMultilinearMap.ext fun tail => ?_
  have hsplit :
      ((metricTraceFirstTwoField (I := I) (M := M) g A
          + metricTraceFirstTwoField (I := I) (M := M) g B) x) tail
        = (metricTraceFirstTwoField (I := I) (M := M) g A x) tail
          + (metricTraceFirstTwoField (I := I) (M := M) g B x) tail := rfl
  rw [hsplit, metricTraceFirstTwoField_eq_sum, metricTraceFirstTwoField_eq_sum,
    metricTraceFirstTwoField_eq_sum]
  have hAB : (A + B) x = A x + B x := rfl
  rw [hAB]
  unfold metricTrace0S2InBasis
  simp only [ContinuousMultilinearMap.add_apply, mul_add, Finset.sum_add_distrib]

set_option backward.isDefEq.respectTransparency false in
/-- **The first-two metric trace field is homogeneous.** -/
theorem metricTraceFirstTwoField_smul {s : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) (c : Real)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2)) :
    metricTraceFirstTwoField (I := I) (M := M) g (c • A)
      = c • metricTraceFirstTwoField (I := I) (M := M) g A := by
  classical
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
  refine DFunLike.ext _ _ fun x => ?_
  refine ContinuousMultilinearMap.ext fun tail => ?_
  have hsplit :
      ((c • metricTraceFirstTwoField (I := I) (M := M) g A) x) tail
        = c * (metricTraceFirstTwoField (I := I) (M := M) g A x) tail := rfl
  rw [hsplit, metricTraceFirstTwoField_eq_sum, metricTraceFirstTwoField_eq_sum]
  have hcA : (c • A) x = c • A x := rfl
  rw [hcA]
  unfold metricTrace0S2InBasis
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

set_option backward.isDefEq.respectTransparency false in
/-- **The first-two metric trace commutes with tail reindexing**: tracing the two
leading slots of `A · (frontExtendEquiv (frontExtendEquiv e))` (which fixes those two
slots and permutes the tail by `e`) is the `e`-reindexing of the trace of `A`. -/
theorem metricTraceFirstTwoField_domDomCongr_gen {s s' : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M)
    (e : Fin (s + 2) ≃ Fin (s' + 2)) (e' : Fin s ≃ Fin s')
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (hcompat : forall (x : M) (X Y : TangentSpace I x)
        (tail : Fin s' -> TangentSpace I x),
      metricTraceInput (I := I) X Y tail ∘ e = metricTraceInput (I := I) X Y (tail ∘ e')) :
    metricTraceFirstTwoField (I := I) (M := M) g
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) e A)
      = MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) e'
          (metricTraceFirstTwoField (I := I) (M := M) g A) := by
  classical
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s'
  refine DFunLike.ext _ _ fun x => ?_
  refine ContinuousMultilinearMap.ext fun tail => ?_
  have hrhs :
      ((MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) e'
          (metricTraceFirstTwoField (I := I) (M := M) g A)) x) tail
        = ((metricTraceFirstTwoField (I := I) (M := M) g A) x) (tail ∘ e') := by
    rw [MultilinearSection.domDomCongr_apply,
      ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  have hL := metricTraceFirstTwoField_eq_sum (I := I) (M := M) g
    (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (∞ : WithTop ℕ∞) e A) x tail
  have hR := metricTraceFirstTwoField_eq_sum (I := I) (M := M) g A x (tail ∘ e')
  rw [hL, hrhs, hR]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [MultilinearSection.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg (A x) (hcompat x _ _ tail)

/-- **First-two metric trace commutes with tail reindexing** (the `frontExtendEquiv²`
case): tracing the two leading slots of `A · frontExt(frontExt e)` is the `e`-reindex of
the trace of `A`.  Special case of `_gen`. -/
theorem metricTraceFirstTwoField_domDomCongr {s s' : ℕ}
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) (e : Fin s ≃ Fin s')
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2)) :
    metricTraceFirstTwoField (I := I) (M := M) g
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞)
          (Tensor0SBundle.frontExtendEquiv (Tensor0SBundle.frontExtendEquiv e)) A)
      = MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) e
          (metricTraceFirstTwoField (I := I) (M := M) g A) := by
  refine metricTraceFirstTwoField_domDomCongr_gen (I := I) (M := M) g
    (Tensor0SBundle.frontExtendEquiv (Tensor0SBundle.frontExtendEquiv e)) e A ?_
  intro x X Y tail
  funext q
  refine Fin.cases ?_ (fun q1 => ?_) q
  · simp only [Function.comp_apply, Tensor0SBundle.frontExtendEquiv_zero, metricTraceInput,
      Fin.cases_zero]
  · refine Fin.cases ?_ (fun r => ?_) q1
    · simp only [Function.comp_apply, Tensor0SBundle.frontExtendEquiv_succ,
        Tensor0SBundle.frontExtendEquiv_zero, metricTraceInput, Fin.cases_succ, Fin.cases_zero]
    · simp only [Function.comp_apply, Tensor0SBundle.frontExtendEquiv_succ,
        metricTraceInput, Fin.cases_succ]

end

end DifferentialGeometry.Integral.Connection
