import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRmBounds
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricCongr
import DifferentialGeometry.Tensor.RSTensor.NormSqProduct

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The Ricci-trace slot bridge for the forward-uniqueness rate estimate

`Evolution/ForwardUniqueRateLe.lean` proves the Kotschwar rate bound
`rate ≤ K·E − D`.  Its sub-lemma `ricciDiffSq_le` consumes the Ricci difference as a
`g₁`-trace of a `(0,4)` representative,

`htr : metricRicciAt g₁ x − metricRicciAt g₂ x = metricTraceFirstTwo0STensor g₁ V`,

with `metricTraceFirstTwo0STensor` contracting the **first two** slots.  The tree only had
this identity in *component* form (`ricciFromRm13_comp_eq_rm04_trace`), and with the trace
pair on `Rm₀₄` slots `0` and `3` rather than `0` and `1`.  This file supplies the missing
tensor-level producer and moves the trace pair into place.

## Main results

* `rm04TraceSlots` — the slot permutation `(0,1,2,3) ↦ (0,2,3,1)` of `Fin 4` that carries the
  `Rm₀₄` trace pair `(0,3)` onto the leading pair `(0,1)`.
* `ricci_eq_trace_rm04` — **the tensor-level Ricci trace identity**: for any `(1,3)` Riemann
  tensor and any `g`-lowering of it, `Ric = tr_g` of the reindexed `(0,4)` tensor.  This is
  the invariant form of `ricciFromRm13_comp_eq_rm04_trace`, whose `Rm04LowersRm13At` gate is
  discharged canonically by `riemannCurvature04At_eq_lower_riemannCurvatureAt`.
* `metricRicci_eq_trace` — the canonical metric specialisation.
* `ricciDiff_eq_trace` — the difference form, **verbatim the shape `ricciDiffSq_le`'s `htr`
  consumes**, with the Kotschwar carrier `S₀₄ = rmDiffLowAt g₁ g₂ x` as the representative.
* `normSq_ricciTraceRep` — the companion norm identity `|V|²_{g₁} = rmDiffSq g₁ g₂ x`, so
  `ricciDiffSq_le`'s second input `hV` holds with background coefficient `B = 0`.

Both flows are traced with the **same** metric `g₁`: `rmDiffLowAt` lowers `Rm¹` and `Rm²`
with `g₁`, and a pure contraction is recovered from any lowering by tracing back with the
metric that lowered it.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section TraceSlots

/-- The slot permutation carrying the `Rm₀₄` Ricci-trace pair into the leading pair.

With the standard convention `Rm₀₄(X,Y,Z,W) = ⟨R(X,Y)Z, W⟩`, the Ricci trace contracts
slots `0` and `3` (`Ric_{ij} = g^{ak} Rm₀₄(e_a, e_i, e_j, e_k)`), whereas
`metricTraceFirstTwo0STensor` contracts slots `0` and `1`.  Reindexing a `(0,4)` tensor by
this permutation sends the input tuple `(a, k, i, j)` to `(a, i, j, k)`, so the two
conventions agree. -/
def rm04TraceSlots : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv := by decide
  right_inv := by decide

/-- Evaluating the reindexed `(0,4)` tensor on a first-two-slot trace input. -/
private theorem traceInput_domDomCongr {x : M}
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (X Y : TangentSpace I x) (tail : Fin 2 -> TangentSpace I x) :
    (ContinuousMultilinearMap.domDomCongr rm04TraceSlots Rm04)
        (metricTraceInput (I := I) X Y tail) =
      Rm04 (vec4 (I := I) X (tail 0) (tail 1) Y) := by
  have h :
      (ContinuousMultilinearMap.domDomCongr rm04TraceSlots Rm04)
          (metricTraceInput (I := I) X Y tail) =
        Rm04 (fun m => metricTraceInput (I := I) X Y tail (rm04TraceSlots m)) := rfl
  rw [h]
  congr 1
  funext m
  fin_cases m <;> rfl

/-- Slot reindexing commutes with subtraction of `(0,s)` fiber tensors. -/
theorem domDomCongr_sub {x : M} {s s' : Nat} (e : Fin s ≃ Fin s')
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    ContinuousMultilinearMap.domDomCongr e (A - B) =
      ContinuousMultilinearMap.domDomCongr e A -
        ContinuousMultilinearMap.domDomCongr e B := by
  refine tensor0SSpace_ext (𝕜 := Real) s' x fun v => ?_
  have hD := Tensor0SSpace.sub_apply (I := I) s' x
    (ContinuousMultilinearMap.domDomCongr e A)
    (ContinuousMultilinearMap.domDomCongr e B) v
  have hE := Tensor0SSpace.sub_apply (I := I) s x A B (fun i => v (e i))
  calc (ContinuousMultilinearMap.domDomCongr e (A - B)) v
      = (A - B) (fun i => v (e i)) := rfl
    _ = A (fun i => v (e i)) - B (fun i => v (e i)) := hE
    _ = (ContinuousMultilinearMap.domDomCongr e A) v -
        (ContinuousMultilinearMap.domDomCongr e B) v := rfl
    _ = (ContinuousMultilinearMap.domDomCongr e A -
        ContinuousMultilinearMap.domDomCongr e B) v := hD.symm

end TraceSlots

section RicciTrace

/-- **The tensor-level Ricci trace identity.**  If `Rm04` is the `g`-lowering of a `(1,3)`
tensor `Rm13`, then the Ricci tensor obtained by tracing `Rm13` is the `g`-trace of the first
two slots of `Rm04` after moving its trace pair `(0,3)` into leading position:

`ricciFromRm13At Rm13 = metricTraceFirstTwo0STensor g (domDomCongr rm04TraceSlots Rm04)`.

This is the invariant form of the component identity `ricciFromRm13_comp_eq_rm04_trace`; the
`Rm04LowersRm13At` gate is discharged canonically by
`riemannCurvature04At_eq_lower_riemannCurvatureAt`. -/
theorem ricci_eq_trace_rm04 (g : SmoothRiemannianMetric I M) {x : M}
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x Rm13 Rm04) :
    ricciFromRm13At (I := I) (M := M) Rm13 =
      metricTraceFirstTwo0STensor (I := I) g
        (ContinuousMultilinearMap.domDomCongr rm04TraceSlots Rm04) := by
  classical
  set basis := Module.finBasis Real (TangentSpace I x) with hbasisdef
  set gInv := basisInvMetric (I := I) g x basis with hgInvdef
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv :=
    basisInvMetric_real (I := I) g x basis
  refine tensor0SSpace_ext (𝕜 := Real) 2 x fun u => ?_
  set L : ContinuousMultilinearMap Real (fun _ : Fin 2 => TangentSpace I x) Real :=
    ricciFromRm13At (I := I) (M := M) Rm13 with hLdef
  set R : ContinuousMultilinearMap Real (fun _ : Fin 2 => TangentSpace I x) Real :=
    metricTraceFirstTwo0STensor (I := I) g
      (ContinuousMultilinearMap.domDomCongr rm04TraceSlots Rm04) with hRdef
  suffices h : L.toMultilinearMap = R.toMultilinearMap by
    exact congrArg
      (fun T : MultilinearMap Real (fun _ : Fin 2 => TangentSpace I x) Real => T u) h
  refine Module.Basis.ext_multilinear (e := fun _ : Fin 2 => basis) ?_
  intro v
  change L (fun i => basis (v i)) = R (fun i => basis (v i))
  have hL : L (fun i => basis (v i)) =
      ricciCompAt (I := I) basis (ricciFromRm13At (I := I) (M := M) Rm13) (v 0) (v 1) := by
    rw [ricciCompAt_apply, hLdef]
    congr 1
    funext a
    fin_cases a <;> rfl
  have hR : R (fun i => basis (v i)) =
      ∑ a : Fin (Module.finrank Real (TangentSpace I x)),
        ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
          gInv a k * rm04CompAt (I := I) basis Rm04 a (v 0) (v 1) k := by
    rw [hRdef]
    change metricTraceFirstTwo0STensor (I := I) g
      (ContinuousMultilinearMap.domDomCongr rm04TraceSlots Rm04)
        (fun i => basis (v i)) = _
    rw [metricTraceFirstTwo0STensor_apply,
      ← metricTrace0S2InBasis_eq_metricTrace (I := I) g basis gInv hinv]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [rm04CompAt_apply]
    exact traceInput_domDomCongr (I := I) Rm04 (basis a) (basis k) (fun i => basis (v i))
  rw [hL, hR,
    ricciFromRm13_comp_eq_rm04_trace (I := I) g basis gInv hinv Rm13 Rm04 hLower]

/-- **Canonical metric form of the Ricci trace identity.**  The Ricci tensor of `g` is the
`g`-trace of its own reindexed `(0,4)` Riemann tensor. -/
theorem metricRicci_eq_trace (g : SmoothRiemannianMetric I M) (x : M) :
    metricRicciAt (I := I) g x =
      metricTraceFirstTwo0STensor (I := I) g
        (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
          (metricRm04At (I := I) g x)) :=
  ricci_eq_trace_rm04 (I := I) g (metricRm13At (I := I) g x) (metricRm04At (I := I) g x)
    (fun X Y Z W =>
      CovariantDerivative.riemannCurvature04At_eq_lower_riemannCurvatureAt
        (I := I) g (metricCov (I := I) g) (metricCov_smooth (I := I) g) X Y Z W)

/-- The Ricci tensor of a *second* metric, read as a `g₁`-trace: the `(1,3)` Riemann tensor
of `∇²` is lowered with `g₁` and traced back with `g₁`.  A pure contraction is recovered from
any lowering by tracing with the metric that lowered it, so this is again `Ric₂`. -/
theorem metricRicci_eq_trace_cross (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    metricRicciAt (I := I) g₂ x =
      metricTraceFirstTwo0STensor (I := I) g₁
        (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
          (CovariantDerivative.riemannCurvature04At (I := I) g₁
            (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x)) :=
  ricci_eq_trace_rm04 (I := I) g₁ (metricRm13At (I := I) g₂ x) _
    (fun X Y Z W =>
      CovariantDerivative.riemannCurvature04At_eq_lower_riemannCurvatureAt
        (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) X Y Z W)

/-- Subtractivity of the intrinsic first-two-slot metric trace. -/
private theorem trace_sub (g : SmoothRiemannianMetric I M) {x : M} {s : Nat}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x) :
    metricTraceFirstTwo0STensor (I := I) g A -
        metricTraceFirstTwo0STensor (I := I) g B =
      metricTraceFirstTwo0STensor (I := I) g (A - B) := by
  classical
  set basis := Module.finBasis Real (TangentSpace I x) with hbasisdef
  set gInv := basisInvMetric (I := I) g x basis with hgInvdef
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv :=
    basisInvMetric_real (I := I) g x basis
  refine tensor0SSpace_ext (𝕜 := Real) s x fun tail => ?_
  have key : ∀ T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x,
      metricTraceFirstTwo0SAt (I := I) g T tail =
        ∑ a : Fin (Module.finrank Real (TangentSpace I x)),
          ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
            gInv a k * T (metricTraceInput (I := I) (basis a) (basis k) tail) := by
    intro T
    rw [← metricTrace0S2InBasis_eq_metricTrace (I := I) g basis gInv hinv]
    rfl
  have hsub := Tensor0SSpace.sub_apply (I := I) s x
    (metricTraceFirstTwo0STensor (I := I) g A)
    (metricTraceFirstTwo0STensor (I := I) g B) tail
  calc (metricTraceFirstTwo0STensor (I := I) g A -
          metricTraceFirstTwo0STensor (I := I) g B) tail
      = metricTraceFirstTwo0STensor (I := I) g A tail -
        metricTraceFirstTwo0STensor (I := I) g B tail := hsub
    _ = (∑ a : Fin (Module.finrank Real (TangentSpace I x)),
            ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
              gInv a k * A (metricTraceInput (I := I) (basis a) (basis k) tail)) -
          ∑ a : Fin (Module.finrank Real (TangentSpace I x)),
            ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
              gInv a k * B (metricTraceInput (I := I) (basis a) (basis k) tail) := by
        rw [metricTraceFirstTwo0STensor_apply, metricTraceFirstTwo0STensor_apply,
          key A, key B]
    _ = ∑ a : Fin (Module.finrank Real (TangentSpace I x)),
          ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
            gInv a k * (A - B) (metricTraceInput (I := I) (basis a) (basis k) tail) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hAB := Tensor0SSpace.sub_apply (I := I) (s + 2) x A B
          (metricTraceInput (I := I) (basis a) (basis k) tail)
        calc gInv a k * A (metricTraceInput (I := I) (basis a) (basis k) tail) -
              gInv a k * B (metricTraceInput (I := I) (basis a) (basis k) tail)
            = gInv a k * (A (metricTraceInput (I := I) (basis a) (basis k) tail) -
                B (metricTraceInput (I := I) (basis a) (basis k) tail)) := by ring
          _ = gInv a k * (A - B) (metricTraceInput (I := I) (basis a) (basis k) tail) :=
              congrArg (fun r : Real => gInv a k * r) hAB.symm
    _ = metricTraceFirstTwo0STensor (I := I) g (A - B) tail := by
        rw [metricTraceFirstTwo0STensor_apply, key (A - B)]

/-- **The Ricci-difference trace producer, in `ricciDiffSq_le`'s `htr` shape.**  The
difference of the two canonical Ricci tensors is the `g₁`-trace of the reindexed Kotschwar
curvature carrier `S₀₄ = rmDiffLowAt g₁ g₂ x`:

`Ric₁ − Ric₂ = tr_{g₁} (domDomCongr rm04TraceSlots (rmDiffLowAt g₁ g₂ x))`.

There is no residual `h₀₂` term: both flows are lowered *and* traced with `g₁`. -/
theorem ricciDiff_eq_trace (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x =
      metricTraceFirstTwo0STensor (I := I) g₁
        (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
          (rmDiffLowAt (I := I) g₁ g₂ x)) := by
  have h₁ := metricRicci_eq_trace (I := I) g₁ x
  have h₂ := metricRicci_eq_trace_cross (I := I) g₁ g₂ x
  have h₃ := domDomCongr_sub (I := I) (x := x) rm04TraceSlots
    (metricRm04At (I := I) g₁ x)
    (CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
      (metricCov_smooth (I := I) g₂) x)
  have h₄ := trace_sub (I := I) (s := 2) g₁
    (ContinuousMultilinearMap.domDomCongr rm04TraceSlots (metricRm04At (I := I) g₁ x))
    (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
      (CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
        (metricCov_smooth (I := I) g₂) x))
  calc metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x
      = metricTraceFirstTwo0STensor (I := I) g₁
            (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
              (metricRm04At (I := I) g₁ x)) -
          metricTraceFirstTwo0STensor (I := I) g₁
            (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
              (CovariantDerivative.riemannCurvature04At (I := I) g₁
                (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x)) := by
        rw [h₁, h₂]
    _ = metricTraceFirstTwo0STensor (I := I) g₁
          (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
              (metricRm04At (I := I) g₁ x) -
            ContinuousMultilinearMap.domDomCongr rm04TraceSlots
              (CovariantDerivative.riemannCurvature04At (I := I) g₁
                (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x)) := h₄
    _ = metricTraceFirstTwo0STensor (I := I) g₁
          (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
            (rmDiffLowAt (I := I) g₁ g₂ x)) :=
        congrArg (metricTraceFirstTwo0STensor (I := I) g₁) h₃.symm

end RicciTrace

section TraceNorm

/-- A `g`-orthonormal basis of the tangent fibre at a point.  (Local copy; the lane already
carries private copies in `ForwardUniqueRmBounds.lean` and `ForwardUniqueConnBound.lean` —
the campaign-end dedup is to promote one public pair to
`Tensor/RSTensor/Tensor0SRiemannian/`.) -/
private theorem exists_onFrame (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ b : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
        (TangentSpace I x),
      ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : Real) else 0 := by
  classical
  let D := (tangentMetricData_gen (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  refine ⟨ob.toBasis, ?_⟩
  intro i j
  have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
    MetricFiberData.toCore_inner D (ob i) (ob j)
  change g.inner x (ob.toBasis i) (ob.toBasis j) = if i = j then (1 : Real) else 0
  rw [← TangentMetricData_gen.inner_eq_gen
    (tangentMetricData_gen (I := I) g x) (ob.toBasis i) (ob.toBasis j)]
  change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
  rw [← hinner]
  exact ob.inner_eq_ite i j

/-- The identity inverse-metric witness attached to a `g`-orthonormal basis. -/
private theorem onFrame_inv {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0) :
    MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)) := by
  intro i j
  constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]

/-- **The trace representative has exactly the curvature-difference density as its norm.**
Slot reindexing is a fibre isometry, so `ricciDiffSq_le`'s norm input `hV` holds with
background coefficient `B = 0`. -/
theorem normSq_ricciTraceRep (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    normSq0S (I := I) g₁ x 4
        (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
          (rmDiffLowAt (I := I) g₁ g₂ x)) =
      rmDiffSq (I := I) g₁ g₂ x := by
  classical
  obtain ⟨basis, hON⟩ := exists_onFrame (I := I) g₁ x
  rw [rmDiffSq_def]
  exact normSq0S_domDomCongr (I := I) g₁ x basis (onFrame_inv (I := I) g₁ basis hON)
    rm04TraceSlots (rmDiffLowAt (I := I) g₁ g₂ x)

end TraceNorm

end DifferentialGeometry.PDE.RicciFlow

end
