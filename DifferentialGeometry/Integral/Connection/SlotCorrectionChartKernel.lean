import DifferentialGeometry.Integral.Connection.SlotCorrectionChartCompFormula
import DifferentialGeometry.Integral.Connection.LeviCivitaChartSmooth
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartLeviCivitaParallelCLMOpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SlotUniformBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SlotChartSourceContMDiff
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.GoodSetMeasure

/-!
# Kernel factorisation, chart-pulled smoothness, and uniform bounds for the
chart-`α`-trivialised input / output Christoffel slot corrections

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, ranks
`r s : ℕ`, a smooth tangent vector field `B`, and a slot index
`k : Fin r` (input) or `l : Fin s` (output), the chart-`α`-trivialised
input / output slot corrections of an `(r, s)`-tensor section `T` factor on
the chart source as

  `(triv α).cLMA b (chartTensorRSInputSlotCorrection r s g α T B b k)
      = (inputSlotChartKernel g r s α B k b) ((triv α).cLMA b (T b))`

(and the analogous identity for the output slot), where the kernel CLM
`inputSlotChartKernel g r s α B k b : TensorRSModel r s ℝ E →L[ℝ]
TensorRSModel r s ℝ E` (and its output sibling) depends only on `g`, `α`,
`B`, the slot index, and the base point `b` — not on `T`. The kernel is
chart-pulled `C^∞` on the chart-`α` Levi-Civita good set and admits uniform
operator-norm and Fréchet-derivative bounds on the intersection of the POU
tsupport with the good set.

## Strategy

The kernel is realised as composition with a model-side slot-conjugated CLM
family `slotInputConjCLM` (resp. `slotOutputConjCLM`) of type
`Fin r → (E →L[ℝ] E)`. The conjugation is by `chartJ α b ∘ · ∘ chartJinv α b`
of the Levi-Civita parallel CLM at slot `k` (resp. `l`) and identity at
every other slot. The composite `chartJ α b ∘ chartLeviCivitaParallelCLM g α b B
∘ chartJinv α b` is exactly the hom-bundle trivialisation image of
`chartLeviCivitaParallelCLM` at `b`, which agrees with
`christoffelCorrectionCLM g α B b` on the chart source — and the latter is
chart-source `C^∞` by `christoffelCorrectionCLM_contMDiffOn_chartSource`.

The uniform op-norm bound on the conjugation reduces to the existing
chart-`α`-trivialisation and Levi-Civita parallel CLM op-norm bounds on the
POU tsupport. The uniform Fréchet-derivative bound is obtained from the
chart-source smoothness via continuity of `fderiv` on the chart-target image
of the (open) chart-`α` Levi-Civita good set.

## Main declarations

* `slotInputConjCLM` / `slotOutputConjCLM` — the per-slot conjugation CLM
  families on `E →L[ℝ] E`.
* `inputSlotChartKernel` / `outputSlotChartKernel` — the bundled kernel CLMs.
* `chartTensorRSInputSlotCorrection_chart_kernel_factorization` /
  `chartTensorRSOutputSlotCorrection_chart_kernel_factorization` — the
  kernel factorisation identities.
* `inputSlotChartKernel_contDiffAt_chart_pulled` /
  `outputSlotChartKernel_contDiffAt_chart_pulled` — chart-pulled `C^∞`
  smoothness on the chart-`α` Levi-Civita good set.
* `inputSlotChartKernel_opNorm_uniform_on_pouTsupport` /
  `outputSlotChartKernel_opNorm_uniform_on_pouTsupport` — uniform op-norm
  bounds on the intersection of the POU tsupport with the good set.
* `inputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport` /
  `outputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport` — uniform
  Fréchet-derivative op-norm bounds on the same set.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## The per-slot conjugation CLM family

For each input slot `i : Fin r` (or output slot `j : Fin s`) we define a
`E →L[ℝ] E` factor: at the substituted slot it is the chart-`α`-conjugate of
the Levi-Civita parallel CLM, and at every other slot it is the identity.

The conjugate `chartJ α b ∘L Φ ∘L chartJinv α b` is the model-side image of
`Φ : E →L[ℝ] E` (using the definitional identification `TangentSpace I b = E`)
under the chart-`(α, b)`-twist of `Φ` viewed at the diagonal hom-fibre. The
substituted-slot case below specialises to `Φ := chartLeviCivitaParallelCLM
g α b B`. -/

/-- The per-input-slot conjugation CLM: the chart-`α`-conjugate of the
Levi-Civita parallel CLM at slot `k`, the identity at every other slot. -/
def slotInputConjCLM (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M)
    (i : Fin r) : E →L[ℝ] E :=
  if i = k then
    (chartJ (I := I) (M := M) α b).comp
      ((chartLeviCivitaParallelCLM (I := I) g α b B).comp
        (chartJinv (I := I) (M := M) α b))
  else
    ContinuousLinearMap.id ℝ E

/-- The per-output-slot conjugation CLM: the chart-`α`-conjugate of the
Levi-Civita parallel CLM at slot `l`, the identity at every other slot. -/
def slotOutputConjCLM (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M)
    (j : Fin s) : E →L[ℝ] E :=
  if j = l then
    (chartJ (I := I) (M := M) α b).comp
      ((chartLeviCivitaParallelCLM (I := I) g α b B).comp
        (chartJinv (I := I) (M := M) α b))
  else
    ContinuousLinearMap.id ℝ E

@[simp] lemma slotInputConjCLM_self (g : SmoothRiemannianMetric I M) (r : ℕ)
    (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    slotInputConjCLM (I := I) g r α B k b k =
      (chartJ (I := I) (M := M) α b).comp
        ((chartLeviCivitaParallelCLM (I := I) g α b B).comp
          (chartJinv (I := I) (M := M) α b)) := by
  unfold slotInputConjCLM
  simp

@[simp] lemma slotInputConjCLM_other (g : SmoothRiemannianMetric I M) (r : ℕ)
    (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M)
    {i : Fin r} (h : i ≠ k) :
    slotInputConjCLM (I := I) g r α B k b i = ContinuousLinearMap.id ℝ E := by
  unfold slotInputConjCLM
  simp [h]

@[simp] lemma slotOutputConjCLM_self (g : SmoothRiemannianMetric I M) (s : ℕ)
    (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    slotOutputConjCLM (I := I) g s α B l b l =
      (chartJ (I := I) (M := M) α b).comp
        ((chartLeviCivitaParallelCLM (I := I) g α b B).comp
          (chartJinv (I := I) (M := M) α b)) := by
  unfold slotOutputConjCLM
  simp

@[simp] lemma slotOutputConjCLM_other (g : SmoothRiemannianMetric I M) (s : ℕ)
    (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M)
    {j : Fin s} (h : j ≠ l) :
    slotOutputConjCLM (I := I) g s α B l b j = ContinuousLinearMap.id ℝ E := by
  unfold slotOutputConjCLM
  simp [h]

/-! ## The kernel CLMs

The kernel sends `S : TensorRSModel r s ℝ E = Tensor0SModel r ℝ E →L[ℝ]
Tensor0SModel s ℝ E` to the slot-corrected form of `S`. The input kernel
post-precomposes on the input side; the output kernel left-postcomposes on
the output side. Both use `ContinuousMultilinearMap.compContinuousLinearMapL`
applied to the slot-conjugation family. -/

/-- The model-side precomposition CLM induced by the input-slot
conjugation family. -/
def inputSlotPrecompCLM (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel r ℝ E :=
  ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (E := fun _ : Fin r => E) (F := ℝ)
    (slotInputConjCLM (I := I) g r α B k b)

/-- The model-side postcomposition CLM induced by the output-slot
conjugation family. -/
def outputSlotPostcompCLM (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    Tensor0SModel s ℝ E →L[ℝ] Tensor0SModel s ℝ E :=
  ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (E := fun _ : Fin s => E) (F := ℝ)
    (slotOutputConjCLM (I := I) g s α B l b)

/-- **The input-slot kernel CLM.** Acts on a chart-α-trivialised `(r, s)`-
tensor model element by right-composing with `inputSlotPrecompCLM`. -/
def inputSlotChartKernel (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
      (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) :=
  (ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel r ℝ E) (Tensor0SModel s ℝ E)).flip
    (inputSlotPrecompCLM (I := I) g r α B k b)

/-- **The output-slot kernel CLM.** Acts on a chart-α-trivialised `(r, s)`-
tensor model element by left-composing with `outputSlotPostcompCLM`. -/
def outputSlotChartKernel (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
      (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) :=
  (ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel s ℝ E) (Tensor0SModel s ℝ E))
    (outputSlotPostcompCLM (I := I) g s α B l b)

@[simp] lemma inputSlotChartKernel_apply (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M)
    (S : Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) :
    inputSlotChartKernel (I := I) g r s α B k b S =
      S.comp (inputSlotPrecompCLM (I := I) g r α B k b) := rfl

@[simp] lemma outputSlotChartKernel_apply (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M)
    (S : Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) :
    outputSlotChartKernel (I := I) g r s α B l b S =
      (outputSlotPostcompCLM (I := I) g s α B l b).comp S := rfl

/-! ## Factorisation identities

We show that the chart-`α`-trivialised slot correction equals the kernel
applied to the chart-`α`-trivialised tensor section value `T b`. -/

/-- Identity relating the slot-conjugated precomposition on the model side
to the bundle-side slot-substitution after composing with `chartJ` on input.

For `b` in the chart-`α` source and `α' : Tensor0SModel r ℝ E`, the
`(α'.compCLM slotInputConjCLM)`-composition with `chartJ` on the input side
equals `tensorSlotSubstCLM r b (tangentSlotCLM r k chartLeviCivitaParallelCLM)`
applied to `α'.compCLM chartJ`. The key step is the identity
`(chartJ ∘ Ψ_k ∘ chartJinv) ∘ chartJ = chartJ ∘ Ψ_k` on the chart base set,
which uses `chartJinv ∘ chartJ = id`. -/
private lemma slotInputConjCLM_compCLM_compCLM_chartJ
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (k : Fin r)
    (α' : Tensor0SModel r ℝ E) :
    (α'.compContinuousLinearMap
        (slotInputConjCLM (I := I) g r α B k b)).compContinuousLinearMap
      (fun _ : Fin r => chartJ (I := I) (M := M) α b) =
    α'.compContinuousLinearMap
      (fun i : Fin r => (chartJ (I := I) (M := M) α b).comp
        (tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b B) i)) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  -- Reduce: it suffices to show the two slot families agree pointwise after
  -- composition with chartJ. Both sides equal `α'.compCLM (per-slot families)`,
  -- and we identify the slot families.
  -- Family 1: `fun i => slotInputConjCLM ... i ∘ chartJ`.
  -- Family 2: `fun i => chartJ ∘ tangentSlotCLM ... i`.
  -- These are equal CLMs E →L E for each i (on baseSet) by the per-slot identity.
  have hfamily :
      (fun i : Fin r => (slotInputConjCLM (I := I) g r α B k b i).comp
          (chartJ (I := I) (M := M) α b)) =
      (fun i : Fin r => (chartJ (I := I) (M := M) α b).comp
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b B) i)) := by
    funext i
    by_cases hik : i = k
    · subst hik
      rw [slotInputConjCLM_self, tangentSlotCLM_self]
      -- LHS: (chartJ ∘ Φ ∘ chartJinv) ∘ chartJ = chartJ ∘ Φ ∘ (chartJinv ∘ chartJ) = chartJ ∘ Φ.
      -- RHS: chartJ ∘ Φ.
      refine ContinuousLinearMap.ext ?_
      intro x
      -- Both sides definitionally `chartJ (Φ (chartJinv (chartJ x)))` and `chartJ (Φ x)`.
      -- chartJinv (chartJ x) = x on baseSet.
      change chartJ (I := I) (M := M) α b
          ((chartLeviCivitaParallelCLM (I := I) g α b B)
            (chartJinv (I := I) (M := M) α b
              (chartJ (I := I) (M := M) α b x))) =
        chartJ (I := I) (M := M) α b
          ((chartLeviCivitaParallelCLM (I := I) g α b B) x)
      rw [chartJinv_chartJ_self (I := I) (M := M) α hb_base]
    · rw [slotInputConjCLM_other (I := I) g r α B k b hik,
        tangentSlotCLM_other (I := I) r k _ hik]
      -- LHS: id ∘ chartJ = chartJ; RHS: chartJ ∘ id = chartJ.
      refine ContinuousLinearMap.ext ?_
      intro x
      change chartJ (I := I) (M := M) α b x = chartJ (I := I) (M := M) α b x
      rfl
  -- Now use `compContinuousLinearMap_compContinuousLinearMap`-style: the LHS is
  -- `(α'.compCLM slotInputConjCLM).compCLM (fun _ => chartJ)`. Combine the two
  -- precompositions into a single compCLM with the composed family.
  refine ContinuousMultilinearMap.ext ?_
  intro v
  -- Establish the per-tuple equality directly: evaluate both sides as α' on
  -- the composed family applied pointwise to v.
  have h_lhs_eq :
      (((α'.compContinuousLinearMap
            (slotInputConjCLM (I := I) g r α B k b)).compContinuousLinearMap
          (fun _ : Fin r => chartJ (I := I) (M := M) α b)) v : ℝ) =
      α' (fun i : Fin r =>
        (slotInputConjCLM (I := I) g r α B k b i) (chartJ (I := I) (M := M) α b (v i))) := by
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- Direct route: both sides equal `α' (fun i => chartJ ((tangentSlotCLM ... i)(v i)))`
  -- by the per-slot equality. We derive the slot-equality first.
  rw [h_lhs_eq]
  -- Goal: α' (fun i => slotInputConjCLM ... i (chartJ (v i))) = compCLM α' (...) v
  -- Use that compCLM equals α' applied to the composed family at v.
  have hfam_at_v : (fun i : Fin r =>
      (slotInputConjCLM (I := I) g r α B k b i) (chartJ (I := I) (M := M) α b (v i))) =
      (fun i : Fin r => (chartJ (I := I) (M := M) α b)
        ((tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b B) i) (v i))) := by
    funext i
    have hi := congrFun hfamily i
    have h_at_v := congrArg (fun (T : E →L[ℝ] E) => T (v i)) hi
    simp only [ContinuousLinearMap.comp_apply] at h_at_v
    exact h_at_v
  rw [hfam_at_v]
  -- Goal: α' (chartJ ∘ tangentSlotCLM ... applied to v) = compCLM α' (...) v
  -- This is `compCLM_apply.symm`.
  exact (ContinuousMultilinearMap.compContinuousLinearMap_apply _ _ _).symm

/-- Identity relating the slot-conjugated postcomposition on the model side
to the bundle-side slot-substitution after composing with `chartJinv` on
output. For `b` in the chart source and the output kernel,
`chartJinv ∘ (chartJ ∘ Ψ_l ∘ chartJinv) = Ψ_l ∘ chartJinv` on the base set,
which is the per-slot ingredient for the postcomposition identity. -/
private lemma slotOutputConjCLM_compose_chartJinv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (l : Fin s)
    (m : Fin s → E) (j : Fin s) :
    chartJinv (I := I) (M := M) α b
        (slotOutputConjCLM (I := I) g s α B l b j (m j)) =
      tangentSlotCLM (I := I) s l
          (chartLeviCivitaParallelCLM (I := I) g α b B) j
          (chartJinv (I := I) (M := M) α b (m j)) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  by_cases hjl : j = l
  · subst hjl
    rw [slotOutputConjCLM_self, tangentSlotCLM_self]
    -- LHS = chartJinv (chartJ (chartLeviCivitaParallelCLM (chartJinv (m j))))
    -- RHS = chartLeviCivitaParallelCLM (chartJinv (m j))
    -- Unfold the `comp` action: chartJ.comp(parallel.comp(chartJinv)) applied to m_j
    -- equals chartJ(parallel(chartJinv(m_j))).
    change chartJinv (I := I) (M := M) α b
        (chartJ (I := I) (M := M) α b
          ((chartLeviCivitaParallelCLM (I := I) g α b B)
            (chartJinv (I := I) (M := M) α b (m j)))) = _
    rw [chartJinv_chartJ_self (I := I) (M := M) α hb_base]
  · rw [slotOutputConjCLM_other (I := I) g s α B l b hjl,
      tangentSlotCLM_other (I := I) s l _ hjl]
    rw [ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply]

/-! ### Headline factorisation: input slot -/

/-- **Kernel factorisation of the chart-`α`-trivialised input-slot
Christoffel correction.**

For `b` in the chart-`α` source, the chart-`α`-trivialised input-slot
Christoffel correction at `b` equals the input-slot kernel applied to the
chart-`α`-trivialisation of `T b`. -/
theorem chartTensorRSInputSlotCorrection_chart_kernel_factorization
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (k : Fin r) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k) =
    (inputSlotChartKernel (I := I) g r s α B k b)
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (T b)) := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro α'
  refine ContinuousMultilinearMap.ext ?_
  intro w
  have hLHS_bridge :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
      r s α hb (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)
  have hRHS_bridge :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
      r s α hb (T b)
  -- Compute both sides at `(α', w)` to a common normal form.
  have hLHS_eval :
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)
        α' w : ℝ) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (α'.compContinuousLinearMap
            (fun i : Fin r => (chartJ (I := I) (M := M) α b).comp
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b B) i))))
        (fun j : Fin s => chartJinv (I := I) (M := M) α b (w j)) := by
    rw [hLHS_bridge, chartRSTwistInv_apply]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have h_apply := chartTensorRSInputSlotCorrection_apply (I := I) r s g α T B b k
      (α'.compContinuousLinearMap
        (fun _ : Fin r => chartJ (I := I) (M := M) α b))
      (fun j : Fin s => chartJinv (I := I) (M := M) α b (w j))
    have hsubst :
        (tensorSlotSubstCLM (I := I) r b
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B))
            (α'.compContinuousLinearMap
              (fun _ : Fin r => chartJ (I := I) (M := M) α b))
          : Tensor0SSpace r I b) =
        α'.compContinuousLinearMap
          (fun i : Fin r => (chartJ (I := I) (M := M) α b).comp
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B) i)) := by
      refine ContinuousMultilinearMap.ext ?_
      intro v
      rw [tensorSlotSubstCLM_apply (I := I) r b
        (tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b B))
        (α'.compContinuousLinearMap
          (fun _ : Fin r => chartJ (I := I) (M := M) α b)) v]
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
      rfl
    rw [hsubst] at h_apply
    exact h_apply
  -- Step 2: compute the RHS.
  have hRHS_eval :
      ((inputSlotChartKernel (I := I) g r s α B k b)
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (T b)) α' w : ℝ) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (α'.compContinuousLinearMap
            (fun i : Fin r => (chartJ (I := I) (M := M) α b).comp
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b B) i))))
        (fun j : Fin s => chartJinv (I := I) (M := M) α b (w j)) := by
    rw [inputSlotChartKernel_apply, ContinuousLinearMap.comp_apply,
      hRHS_bridge, chartRSTwistInv_apply]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have hkey :=
      slotInputConjCLM_compCLM_compCLM_chartJ (I := I) (M := M) g r α B hb k α'
    have h_unfold_precomp :
        ((inputSlotPrecompCLM (I := I) g r α B k b) α').compContinuousLinearMap
          (fun _ : Fin r => chartJ (I := I) (M := M) α b) =
        α'.compContinuousLinearMap
          (fun i : Fin r => (chartJ (I := I) (M := M) α b).comp
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B) i)) := by
      unfold inputSlotPrecompCLM
      rw [ContinuousMultilinearMap.compContinuousLinearMapL_apply]
      exact hkey
    rw [h_unfold_precomp]
    rfl
  exact hLHS_eval.trans hRHS_eval.symm

/-! ### Headline factorisation: output slot -/

/-- **Kernel factorisation of the chart-`α`-trivialised output-slot
Christoffel correction.**

For `b` in the chart-`α` source, the chart-`α`-trivialised output-slot
Christoffel correction at `b` equals the output-slot kernel applied to the
chart-`α`-trivialisation of `T b`. -/
theorem chartTensorRSOutputSlotCorrection_chart_kernel_factorization
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (l : Fin s) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l) =
    (outputSlotChartKernel (I := I) g r s α B l b)
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (T b)) := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro α'
  refine ContinuousMultilinearMap.ext ?_
  intro m
  have hLHS_bridge :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
      r s α hb (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)
  have hRHS_bridge :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
      r s α hb (T b)
  -- Step 1: compute LHS = (T b)(α'.compCLM chartJ) (fun j => Ψ_l j (chartJinv (m j))).
  have hLHS_eval :
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)
        α' m : ℝ) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (α'.compContinuousLinearMap
            (fun _ : Fin r => chartJ (I := I) (M := M) α b)))
        (fun j : Fin s =>
          tangentSlotCLM (I := I) s l
            (chartLeviCivitaParallelCLM (I := I) g α b B) j
            (chartJinv (I := I) (M := M) α b (m j))) := by
    rw [hLHS_bridge, chartRSTwistInv_apply]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    -- (toModel OSC) at function level = OSC = (substCLM Ψ_l).comp(T b).
    -- ((substCLM Ψ_l).comp(T b)) (α'.compCLM chartJ) = substCLM Ψ_l ((T b)(α'.compCLM chartJ)).
    -- Then evaluate at (chartJinv ∘ m) gives the formula.
    exact chartTensorRSOutputSlotCorrection_apply (I := I) r s g α T B b l
      (α'.compContinuousLinearMap
        (fun _ : Fin r => chartJ (I := I) (M := M) α b))
      (fun j : Fin s => chartJinv (I := I) (M := M) α b (m j))
  -- Step 2: compute RHS to the same expression.
  have hRHS_eval :
      ((outputSlotChartKernel (I := I) g r s α B l b)
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (T b)) α' m : ℝ) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (α'.compContinuousLinearMap
            (fun _ : Fin r => chartJ (I := I) (M := M) α b)))
        (fun j : Fin s =>
          tangentSlotCLM (I := I) s l
            (chartLeviCivitaParallelCLM (I := I) g α b B) j
            (chartJinv (I := I) (M := M) α b (m j))) := by
    rw [outputSlotChartKernel_apply]
    rw [ContinuousLinearMap.comp_apply]
    rw [hRHS_bridge]
    -- outputSlotPostcompCLM = compCLML (slotOutputConjCLM) applied to RHS-CMM.
    unfold outputSlotPostcompCLM
    rw [ContinuousMultilinearMap.compContinuousLinearMapL_apply]
    -- Now: ((chartRSTwistInv (toModel T b) α').compCLM slotOutputConjCLM) m.
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [chartRSTwistInv_apply]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    -- Now: (toModel T b)(α'.compCLM chartJ) (fun j => chartJinv (slotOutputConjCLM j (m j))).
    congr 1
    funext j
    exact slotOutputConjCLM_compose_chartJinv (I := I) (M := M) g s α B hb l m j
  exact hLHS_eval.trans hRHS_eval.symm

/-! ## Chart-pulled smoothness of the kernels

The kernel is a CLM-valued function of `b`. To express its smoothness in the
form requested by downstream consumers, we work with the chart-pulled
representation `y : E ↦ inputSlotChartKernel ... (symm y)`, evaluated at
`extChartAt I α b`, and show it is `ContDiffAt ℝ ∞` on the chart-α
Levi-Civita good set image.

The strategy: the kernel is built from the slot-conjugation CLM via
continuous-linear operations (`compContinuousLinearMapL`, `compL`,
`compL.flip`). Each of these is a continuous map of CLMs and preserves
smoothness. The base smoothness ingredient is the chart-pulled smoothness
of `b ↦ slotInputConjCLM g r α B k b i` for each `i : Fin r` (and the
analogous output-side variant).

For `i ≠ k` the conjugation is the constant `id_E`, hence trivially smooth.
For `i = k` the conjugation is the hom-bundle-trivialised image of
`chartLeviCivitaParallelCLM g α b B`, which by
`chartLeviCivitaParallelCLM_trivImage_eq_christoffelCorrectionCLM` agrees on
the chart source with `christoffelCorrectionCLM g α B b`, which is
chart-source `ContMDiffOn ∞` by `christoffelCorrectionCLM_contMDiffOn_chartSource`. -/

/-! ### The conjugation = christoffelCorrectionCLM identity on the chart source -/

/-- On the chart-`α` source, the chart-`α`-conjugation
`chartJ α b ∘L chartLeviCivitaParallelCLM g α b X ∘L chartJinv α b` agrees
with `christoffelCorrectionCLM g α X b`. -/
private lemma chartLCConj_eq_christoffelCorrectionCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) :
    (chartJ (I := I) (M := M) α b).comp
        ((chartLeviCivitaParallelCLM (I := I) g α b X).comp
          (chartJinv (I := I) (M := M) α b)) =
      christoffelCorrectionCLM (I := I) g α X b := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  refine ContinuousLinearMap.ext ?_
  intro w
  -- LHS: ((chartJ).comp((parallel).comp(chartJinv))) w
  -- Step 1: unfold the outer `.comp`.
  rw [ContinuousLinearMap.comp_apply]
  -- Goal: chartJ ((parallel).comp(chartJinv) w) = christoffelCorrectionCLM g α X b w
  -- Step 2: unfold the inner `.comp` by switching to a definitionally-equal form.
  change chartJ (I := I) (M := M) α b
      ((chartLeviCivitaParallelCLM (I := I) g α b X)
        (chartJinv (I := I) (M := M) α b w)) = _
  -- Use the parallel CLM evaluation formula.
  rw [chartLeviCivitaParallelCLM_apply (I := I) g α b X
    (chartJinv (I := I) (M := M) α b w)]
  -- LHS now: chartJ (trivFromE (christoffelCorrection ...)).
  -- chartJ α b = trivToE α b definitionally; use `trivToE_trivFromE` to collapse.
  change trivToE (I := I) α b
      (trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b
          (trivToE (I := I) α b (X b))
          (chartJinv (I := I) (M := M) α b w))) = _
  rw [trivToE_trivFromE (I := I) α hb_base]
  -- Identify with christoffelCorrectionCLM.
  exact christoffelCorrection_eq_christoffelCorrectionCLM (I := I) g α X hb_base w

/-! ### Chart-pulled smoothness of the slot-conjugation CLM family -/

/-- Chart-pulled smoothness of the chart-`α`-conjugation
`chartJ α (symm y) ∘L chartLeviCivitaParallelCLM g α (symm y) B ∘L chartJinv α (symm y)`
on the chart-target image of the chart-`α` Levi-Civita good set. -/
private lemma chartLCConj_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : M =>
        (chartJ (I := I) (M := M) α b).comp
          ((chartLeviCivitaParallelCLM (I := I) g α b B.toFun).comp
            (chartJinv (I := I) (M := M) α b)))
      ((chartAt H α).source) := by
  classical
  -- Use the public `christoffelCorrectionCLM_contMDiffOn` (on the good set,
  -- which equals the chart source under [I.Boundaryless]).
  have hB_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := fun y : M => TangentSpace I y) x (B.toFun x)) := B.contMDiff
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := hB_total.contMDiffOn
  have hχ_good : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (christoffelCorrectionCLM (I := I) g α B.toFun)
      (chartLeviCivitaGoodSet (I := I) α) :=
    christoffelCorrectionCLM_contMDiffOn (I := I) g α hB_on
  have h_good_eq_source :
      chartLeviCivitaGoodSet (I := I) α = (chartAt H α).source := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α,
      extChartAt_source_eq_chartAt_source (I := I)]
  have hχ : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (christoffelCorrectionCLM (I := I) g α B.toFun)
      ((chartAt H α).source) := by
    rw [← h_good_eq_source]; exact hχ_good
  refine hχ.congr ?_
  intro b hb
  exact chartLCConj_eq_christoffelCorrectionCLM (I := I) (M := M) g α B.toFun hb

/-! ### Chart-target smoothness via extChartAt symm -/

/-- The chart-target image of the chart-`α` Levi-Civita good set is open. -/
private lemma goodSet_image_isOpen (α : M) :
    IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
  chartLeviCivitaGoodSet_image_isOpen (I := I) α

/-- The chart-`α` Levi-Civita good set is contained in the chart source. -/
private lemma goodSet_subset_chartSource (α : M) :
    chartLeviCivitaGoodSet (I := I) α ⊆ (chartAt H α).source := by
  intro b hb
  have h_eq :=
    chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
  rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)] at hb
  exact hb

/-- For `b` in the chart-`α` Levi-Civita good set, `extChartAt I α b` lies in
the chart-target image of the good set. -/
private lemma extChartAt_mem_goodSet_image (α : M) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    extChartAt I α b ∈ (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
  ⟨b, hb, rfl⟩

/-- Chart-pulled smoothness (in the `y : E` chart variable) of the chart-`α`
conjugation `chartJ ∘ parallel ∘ chartJinv` evaluated at `(symm y)`, on the
chart-target image of the chart-`α` Levi-Civita good set. -/
private lemma chartLCConj_chart_pulled_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContDiffOn ℝ ∞
      (fun y : E =>
        (chartJ (I := I) (M := M) α ((extChartAt I α).symm y)).comp
          ((chartLeviCivitaParallelCLM (I := I) g α
              ((extChartAt I α).symm y) B.toFun).comp
            (chartJinv (I := I) (M := M) α ((extChartAt I α).symm y))))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  -- We have ContMDiffOn on chart-source. Compose with extChartAt.symm and
  -- transfer to ContDiffOn on the chart-target image using the standard
  -- chartE_pullback pattern (see `chartE_pullback_contDiffOn_goodSet`).
  have hcm := chartLCConj_contMDiffOn_chartSource (I := I) (M := M) g α B
  -- Strategy: pointwise. For each y in the image, write y = extChartAt I α b
  -- for some b ∈ goodSet, then ContMDiff at b composed with smoothness of
  -- extChartAt.symm at φ b gives ContDiff at y.
  set hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  intro y hy
  rcases hy with ⟨x, hxS, rfl⟩
  have hx_src : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hxS
  -- ContMDiffAt the M-function at x.
  set F : M → E →L[ℝ] E := fun b : M =>
    (chartJ (I := I) (M := M) α b).comp
      ((chartLeviCivitaParallelCLM (I := I) g α b B.toFun).comp
        (chartJinv (I := I) (M := M) α b)) with hF_def
  have hF_at : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ F x := by
    have hopen_src : IsOpen (chartAt H α).source :=
      (chartAt H α).open_source
    exact hcm.contMDiffAt (hopen_src.mem_nhds hx_src)
  -- ContMDiffAt of extChartAt.symm at φ x.
  set φ := extChartAt I α
  have hxφ_src : x ∈ φ.source := by rw [extChartAt_source]; exact hx_src
  have hxφ_tgt : φ x ∈ φ.target := φ.map_source hxφ_src
  have hxφ_inv : φ.symm (φ x) = x := φ.left_inv hxφ_src
  have hsymm_on : ContMDiffOn 𝓘(ℝ, E) I (∞ : WithTop ℕ∞) φ.symm φ.target :=
    contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x := α)
  have hsymm_at : ContMDiffWithinAt 𝓘(ℝ, E) I (∞ : WithTop ℕ∞)
      φ.symm φ.target (φ x) := hsymm_on (φ x) hxφ_tgt
  have hF_at' : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ F (φ.symm (φ x)) := by
    rw [hxφ_inv]; exact hF_at
  have hcomp_at : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (F ∘ φ.symm) φ.target (φ x) :=
    hF_at'.comp_contMDiffWithinAt (φ x) hsymm_at
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hcomp_at
  refine hcomp_at.mono ?_
  intro z hz
  rcases hz with ⟨x', hx'_good, rfl⟩
  exact interior_subset
    (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx'_good)

/-- Wrapper. Chart-pulled smoothness (as a `ContDiffAt`) of the chart-`α`
conjugation, at a point in the chart-`α` Levi-Civita good set. -/
private lemma chartLCConj_chart_pulled_contDiffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞
      (fun y : E =>
        (chartJ (I := I) (M := M) α ((extChartAt I α).symm y)).comp
          ((chartLeviCivitaParallelCLM (I := I) g α
              ((extChartAt I α).symm y) B.toFun).comp
            (chartJinv (I := I) (M := M) α ((extChartAt I α).symm y))))
      (extChartAt I α b) := by
  classical
  have hOpen := goodSet_image_isOpen (I := I) (M := M) α
  have hmem : extChartAt I α b ∈
      (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    extChartAt_mem_goodSet_image (I := I) (M := M) α hb
  exact (chartLCConj_chart_pulled_contDiffOn (I := I) (M := M) g α B).contDiffAt
    (hOpen.mem_nhds hmem)

/-! ### Chart-pulled smoothness of the slot-conjugation family -/

/-- Chart-pulled `ContDiffAt` smoothness of each slot of the input slot
conjugation family at a chart-good-set point. -/
private lemma slotInputConjCLM_chart_pulled_contDiffAt
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (i : Fin r) :
    ContDiffAt ℝ ∞
      (fun y : E =>
        slotInputConjCLM (I := I) g r α B.toFun k
          ((extChartAt I α).symm y) i)
      (extChartAt I α b) := by
  classical
  by_cases hik : i = k
  · subst hik
    -- slotInputConjCLM ... i (= k after subst) = chartJ ∘ parallelCLM ∘ chartJinv (smooth).
    have heq : (fun y : E =>
        slotInputConjCLM (I := I) g r α B.toFun i ((extChartAt I α).symm y) i) =
      (fun y : E =>
        (chartJ (I := I) (M := M) α ((extChartAt I α).symm y)).comp
          ((chartLeviCivitaParallelCLM (I := I) g α
              ((extChartAt I α).symm y) B.toFun).comp
            (chartJinv (I := I) (M := M) α ((extChartAt I α).symm y)))) := by
      funext y
      exact slotInputConjCLM_self (I := I) g r α B.toFun i ((extChartAt I α).symm y)
    rw [heq]
    exact chartLCConj_chart_pulled_contDiffAt (I := I) (M := M) g α B hb
  · -- slotInputConjCLM ... i = id_E (constant).
    have heq : (fun y : E =>
        slotInputConjCLM (I := I) g r α B.toFun k ((extChartAt I α).symm y) i) =
      (fun _ : E => ContinuousLinearMap.id ℝ E) := by
      funext y
      exact slotInputConjCLM_other (I := I) g r α B.toFun k _ hik
    rw [heq]
    exact contDiffAt_const

/-- Chart-pulled `ContDiffAt` smoothness of each slot of the output slot
conjugation family at a chart-good-set point. -/
private lemma slotOutputConjCLM_chart_pulled_contDiffAt
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (j : Fin s) :
    ContDiffAt ℝ ∞
      (fun y : E =>
        slotOutputConjCLM (I := I) g s α B.toFun l
          ((extChartAt I α).symm y) j)
      (extChartAt I α b) := by
  classical
  by_cases hjl : j = l
  · subst hjl
    have heq : (fun y : E =>
        slotOutputConjCLM (I := I) g s α B.toFun j ((extChartAt I α).symm y) j) =
      (fun y : E =>
        (chartJ (I := I) (M := M) α ((extChartAt I α).symm y)).comp
          ((chartLeviCivitaParallelCLM (I := I) g α
              ((extChartAt I α).symm y) B.toFun).comp
            (chartJinv (I := I) (M := M) α ((extChartAt I α).symm y)))) := by
      funext y
      exact slotOutputConjCLM_self (I := I) g s α B.toFun j ((extChartAt I α).symm y)
    rw [heq]
    exact chartLCConj_chart_pulled_contDiffAt (I := I) (M := M) g α B hb
  · have heq : (fun y : E =>
        slotOutputConjCLM (I := I) g s α B.toFun l ((extChartAt I α).symm y) j) =
      (fun _ : E => ContinuousLinearMap.id ℝ E) := by
      funext y
      exact slotOutputConjCLM_other (I := I) g s α B.toFun l _ hjl
    rw [heq]
    exact contDiffAt_const

/-! ### Smoothness of `compContinuousLinearMapL` of a smooth family

`compContinuousLinearMapL` is a continuous linear (hence smooth) functional
in the `f` argument; we use this to lift smoothness of each slot factor to
smoothness of the entire `compContinuousLinearMapL`-bundle. -/

/-- Smoothness of the chart-pulled `inputSlotPrecompCLM` at a good-set point. -/
private lemma inputSlotPrecompCLM_chart_pulled_contDiffAt
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞
      (fun y : E =>
        inputSlotPrecompCLM (I := I) g r α B.toFun k
          ((extChartAt I α).symm y))
      (extChartAt I α b) := by
  classical
  -- The map `Φ ↦ compContinuousLinearMapL Φ` is the underlying function of
  -- the continuous multilinear map `compContinuousLinearMapContinuousMultilinear`.
  -- Smoothness follows by composing the smoothness of each slot via
  -- the CMM-as-function smoothness.
  set hmulti : ContinuousMultilinearMap ℝ (fun _ : Fin r => E →L[ℝ] E)
      ((ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      ℝ (fun _ : Fin r => E) (fun _ : Fin r => E) ℝ with hmulti_def
  -- Smoothness of the pi-bundle of slot factors.
  have hpi : ContDiffAt ℝ ∞
      (fun y : E =>
        fun i : Fin r => slotInputConjCLM (I := I) g r α B.toFun k
          ((extChartAt I α).symm y) i)
      (extChartAt I α b) := by
    refine contDiffAt_pi.mpr ?_
    intro i
    exact slotInputConjCLM_chart_pulled_contDiffAt (I := I) (M := M)
      g r α B k hb i
  -- Continuous multilinear map composed with smooth pi-tuple is smooth.
  have hcomposed :=
    (hmulti.contDiff (𝕜 := ℝ)).contDiffAt.comp (x := extChartAt I α b) hpi
  -- `hcomposed` is smooth function `y ↦ hmulti (slot family)`.
  -- The applied form of `compContinuousLinearMapContinuousMultilinear ... f`
  -- is `compContinuousLinearMapL f` by the simp lemma generated by
  -- `@[simps! apply_apply]`. Establish this once and rewrite.
  have h_eval :
      ∀ y : E,
        (hmulti
            (fun i : Fin r => slotInputConjCLM (I := I) g r α B.toFun k
              ((extChartAt I α).symm y) i)
          : ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →L[ℝ]
              ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) =
        inputSlotPrecompCLM (I := I) g r α B.toFun k
          ((extChartAt I α).symm y) := by
    intro y
    -- Both sides are CLMs `CMM ... → CMM ...`. Apply ext.
    refine ContinuousLinearMap.ext ?_
    intro w
    -- LHS = (compCLMContMultilinear ... slotConjFamily) w
    --     = (compCLML slotConjFamily) w
    --     = w.compCLM slotConjFamily
    -- RHS = inputSlotPrecompCLM (symm y) (w)
    --     = compCLML (slotInputConjCLM ... (symm y)) w
    --     = w.compCLM slotConjFamily
    -- Both are definitionally equal.
    rfl
  refine hcomposed.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  exact h_eval y

/-- Smoothness of the chart-pulled `outputSlotPostcompCLM` at a good-set point. -/
private lemma outputSlotPostcompCLM_chart_pulled_contDiffAt
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞
      (fun y : E =>
        outputSlotPostcompCLM (I := I) g s α B.toFun l
          ((extChartAt I α).symm y))
      (extChartAt I α b) := by
  classical
  set hmulti : ContinuousMultilinearMap ℝ (fun _ : Fin s => E →L[ℝ] E)
      ((ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      ℝ (fun _ : Fin s => E) (fun _ : Fin s => E) ℝ with hmulti_def
  have hpi : ContDiffAt ℝ ∞
      (fun y : E =>
        fun j : Fin s => slotOutputConjCLM (I := I) g s α B.toFun l
          ((extChartAt I α).symm y) j)
      (extChartAt I α b) := by
    refine contDiffAt_pi.mpr ?_
    intro j
    exact slotOutputConjCLM_chart_pulled_contDiffAt (I := I) (M := M)
      g s α B l hb j
  have hcomposed :=
    (hmulti.contDiff (𝕜 := ℝ)).contDiffAt.comp (x := extChartAt I α b) hpi
  have h_eval :
      ∀ y : E,
        (hmulti
            (fun j : Fin s => slotOutputConjCLM (I := I) g s α B.toFun l
              ((extChartAt I α).symm y) j)
          : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ →L[ℝ]
              ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
        outputSlotPostcompCLM (I := I) g s α B.toFun l
          ((extChartAt I α).symm y) := by
    intro y
    refine ContinuousLinearMap.ext ?_
    intro w
    rfl
  refine hcomposed.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  exact h_eval y

/-! ### Headlines: chart-pulled smoothness of the kernels -/

/-- **Chart-pulled smoothness of the input-slot kernel.**

The chart-pulled input-slot kernel `y ↦ inputSlotChartKernel g r s α B k
((extChartAt I α).symm y)` is `ContDiffAt ℝ ∞` at `extChartAt I α b` for any
`b` in the chart-`α` Levi-Civita good set. -/
theorem inputSlotChartKernel_contDiffAt_chart_pulled
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (k : Fin r) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y))
      (extChartAt I α b) := by
  classical
  -- The smoothness of the kernel does not depend on the locality hypothesis;
  -- it follows from the local smoothness of the chart-Jacobian-conjugated
  -- parallel CLM on the chart source. We retain `h_atlas` in the signature
  -- for API uniformity with the uniform-bound headlines below.
  let _ := h_atlas
  -- inputSlotChartKernel = (compL).flip (inputSlotPrecompCLM).
  -- This is a continuous linear map applied to inputSlotPrecompCLM.
  -- Smoothness of compL_flip ∘ inputSlotPrecompCLM follows.
  have h_precomp := inputSlotPrecompCLM_chart_pulled_contDiffAt
    (I := I) (M := M) g r α B k hb
  -- Apply the continuous linear map `(compL).flip` (smooth) to h_precomp.
  set L : (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel r ℝ E) →L[ℝ]
      ((Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
        (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)) :=
    (ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel r ℝ E) (Tensor0SModel s ℝ E)).flip with hL_def
  have hL_smooth : ContDiff ℝ ∞ (L : _ → _) := L.contDiff
  have hcomposed := hL_smooth.contDiffAt.comp (x := extChartAt I α b) h_precomp
  refine hcomposed.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  rfl

/-- **Chart-pulled smoothness of the output-slot kernel.**

The chart-pulled output-slot kernel `y ↦ outputSlotChartKernel g r s α B l
((extChartAt I α).symm y)` is `ContDiffAt ℝ ∞` at `extChartAt I α b` for any
`b` in the chart-`α` Levi-Civita good set. -/
theorem outputSlotChartKernel_contDiffAt_chart_pulled
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (l : Fin s) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y))
      (extChartAt I α b) := by
  classical
  let _ := h_atlas
  have h_postcomp := outputSlotPostcompCLM_chart_pulled_contDiffAt
    (I := I) (M := M) g s α B l hb
  set L : (Tensor0SModel s ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
      ((Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
        (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)) :=
    ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel s ℝ E) (Tensor0SModel s ℝ E) with hL_def
  have hL_smooth : ContDiff ℝ ∞ (L : _ → _) := L.contDiff
  have hcomposed := hL_smooth.contDiffAt.comp (x := extChartAt I α b) h_postcomp
  refine hcomposed.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  rfl

/-! ## Uniform op-norm bounds on `tsupport ∩ goodSet`

The op-norm of `inputSlotChartKernel ... b` is bounded by the op-norm of
`inputSlotPrecompCLM ... b`, which in turn is bounded by `∏ ‖slotInputConjCLM
... b i‖ ≤ (max ‖chartJ‖^2 · ‖chartLeviCivitaParallelCLM‖) ^ 1 · 1^(r-1) =
‖chartJ‖^2 · ‖chartLeviCivitaParallelCLM‖`. Each of the three factors admits
a uniform bound on the POU tsupport. -/

/-! ### Op-norm of the conjugation -/

/-- Op-norm bound on the chart-`α`-conjugation
`chartJ α b ∘L chartLeviCivitaParallelCLM g α b X ∘L chartJinv α b`. -/
private lemma chartLCConj_opNorm_le (g : SmoothRiemannianMetric I M) (α b : M)
    (X : Π b' : M, TangentSpace I b') :
    ‖(chartJ (I := I) (M := M) α b).comp
        ((chartLeviCivitaParallelCLM (I := I) g α b X).comp
          (chartJinv (I := I) (M := M) α b))‖ ≤
      ‖chartJ (I := I) (M := M) α b‖ *
        (‖chartLeviCivitaParallelCLM (I := I) g α b X‖ *
          ‖chartJinv (I := I) (M := M) α b‖) := by
  refine ContinuousLinearMap.opNorm_comp_le _ _ |>.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact ContinuousLinearMap.opNorm_comp_le _ _

/-- Pointwise per-slot op-norm bound on `slotInputConjCLM`. -/
private lemma slotInputConjCLM_opNorm_le (g : SmoothRiemannianMetric I M)
    (r : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M)
    (i : Fin r) :
    ‖slotInputConjCLM (I := I) g r α B k b i‖ ≤
      max 1
        (‖chartJ (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartJinv (I := I) (M := M) α b‖)) := by
  classical
  by_cases hik : i = k
  · subst hik
    rw [slotInputConjCLM_self]
    refine le_trans (chartLCConj_opNorm_le (I := I) (M := M) g α b B) ?_
    exact le_max_right _ _
  · rw [slotInputConjCLM_other (I := I) g r α B k b hik]
    refine ContinuousLinearMap.norm_id_le.trans ?_
    exact le_max_left _ _

/-- Pointwise per-slot op-norm bound on `slotOutputConjCLM`. -/
private lemma slotOutputConjCLM_opNorm_le (g : SmoothRiemannianMetric I M)
    (s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M)
    (j : Fin s) :
    ‖slotOutputConjCLM (I := I) g s α B l b j‖ ≤
      max 1
        (‖chartJ (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartJinv (I := I) (M := M) α b‖)) := by
  classical
  by_cases hjl : j = l
  · subst hjl
    rw [slotOutputConjCLM_self]
    refine le_trans (chartLCConj_opNorm_le (I := I) (M := M) g α b B) ?_
    exact le_max_right _ _
  · rw [slotOutputConjCLM_other (I := I) g s α B l b hjl]
    refine ContinuousLinearMap.norm_id_le.trans ?_
    exact le_max_left _ _

/-- Op-norm bound on the product of per-slot input conjugation factors. -/
private lemma slotInputConjCLM_prod_opNorm_le (g : SmoothRiemannianMetric I M)
    (r : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    (∏ i : Fin r, ‖slotInputConjCLM (I := I) g r α B k b i‖) ≤
      (max 1
        (‖chartJ (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartJinv (I := I) (M := M) α b‖))) ^ r := by
  classical
  set M_b : ℝ := max 1
    (‖chartJ (I := I) (M := M) α b‖ *
      (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
        ‖chartJinv (I := I) (M := M) α b‖)) with hM_def
  have h_pow : M_b ^ r = ∏ _i : Fin r, M_b := by
    rw [Finset.prod_const]; simp
  rw [h_pow]
  refine Finset.prod_le_prod ?_ ?_
  · intro i _; exact norm_nonneg _
  · intro i _; exact slotInputConjCLM_opNorm_le (I := I) (M := M) g r α B k b i

/-- Op-norm bound on the product of per-slot output conjugation factors. -/
private lemma slotOutputConjCLM_prod_opNorm_le (g : SmoothRiemannianMetric I M)
    (s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    (∏ j : Fin s, ‖slotOutputConjCLM (I := I) g s α B l b j‖) ≤
      (max 1
        (‖chartJ (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartJinv (I := I) (M := M) α b‖))) ^ s := by
  classical
  set M_b : ℝ := max 1
    (‖chartJ (I := I) (M := M) α b‖ *
      (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
        ‖chartJinv (I := I) (M := M) α b‖)) with hM_def
  have h_pow : M_b ^ s = ∏ _j : Fin s, M_b := by
    rw [Finset.prod_const]; simp
  rw [h_pow]
  refine Finset.prod_le_prod ?_ ?_
  · intro j _; exact norm_nonneg _
  · intro j _; exact slotOutputConjCLM_opNorm_le (I := I) (M := M) g s α B l b j

/-- Op-norm bound on the `inputSlotPrecompCLM`. -/
private lemma inputSlotPrecompCLM_opNorm_le (g : SmoothRiemannianMetric I M)
    (r : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    ‖inputSlotPrecompCLM (I := I) g r α B k b‖ ≤
      (max 1
        (‖chartJ (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartJinv (I := I) (M := M) α b‖))) ^ r := by
  classical
  unfold inputSlotPrecompCLM
  refine le_trans
    (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
      (𝕜 := ℝ) (E := fun _ : Fin r => E) ℝ _) ?_
  exact slotInputConjCLM_prod_opNorm_le (I := I) (M := M) g r α B k b

/-- Op-norm bound on the `outputSlotPostcompCLM`. -/
private lemma outputSlotPostcompCLM_opNorm_le (g : SmoothRiemannianMetric I M)
    (s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    ‖outputSlotPostcompCLM (I := I) g s α B l b‖ ≤
      (max 1
        (‖chartJ (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartJinv (I := I) (M := M) α b‖))) ^ s := by
  classical
  unfold outputSlotPostcompCLM
  refine le_trans
    (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
      (𝕜 := ℝ) (E := fun _ : Fin s => E) ℝ _) ?_
  exact slotOutputConjCLM_prod_opNorm_le (I := I) (M := M) g s α B l b

/-! ### Op-norm of the kernel CLMs -/

/-- Op-norm bound on `inputSlotChartKernel`. -/
private lemma inputSlotChartKernel_opNorm_le (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    ‖inputSlotChartKernel (I := I) g r s α B k b‖ ≤
      ‖inputSlotPrecompCLM (I := I) g r α B k b‖ := by
  classical
  unfold inputSlotChartKernel
  -- ‖compL.flip P‖ ≤ ‖compL.flip‖ * ‖P‖ ≤ ‖compL‖ * ‖P‖ ≤ 1 * ‖P‖ = ‖P‖.
  refine le_trans ((ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
    (Tensor0SModel r ℝ E) (Tensor0SModel s ℝ E)).flip.le_opNorm _) ?_
  rw [ContinuousLinearMap.opNorm_flip]
  have h_le := ContinuousLinearMap.norm_compL_le (𝕜 := ℝ)
    (E := Tensor0SModel r ℝ E) (Fₗ := Tensor0SModel r ℝ E)
    (Gₗ := Tensor0SModel s ℝ E)
  have h_nn : 0 ≤ ‖inputSlotPrecompCLM (I := I) g r α B k b‖ := norm_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_right h_le h_nn) ?_
  rw [one_mul]

/-- Op-norm bound on `outputSlotChartKernel`. -/
private lemma outputSlotChartKernel_opNorm_le (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    ‖outputSlotChartKernel (I := I) g r s α B l b‖ ≤
      ‖outputSlotPostcompCLM (I := I) g s α B l b‖ := by
  classical
  unfold outputSlotChartKernel
  -- ‖compL Q‖ ≤ ‖compL‖ * ‖Q‖ ≤ 1 * ‖Q‖ = ‖Q‖.
  refine le_trans ((ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
    (Tensor0SModel s ℝ E) (Tensor0SModel s ℝ E)).le_opNorm _) ?_
  have h_le := ContinuousLinearMap.norm_compL_le (𝕜 := ℝ)
    (E := Tensor0SModel r ℝ E) (Fₗ := Tensor0SModel s ℝ E)
    (Gₗ := Tensor0SModel s ℝ E)
  have h_nn : 0 ≤ ‖outputSlotPostcompCLM (I := I) g s α B l b‖ := norm_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_right h_le h_nn) ?_
  rw [one_mul]

/-! ### Uniform bound on `M_b`

`M_b b := max 1 (‖chartJ α b‖ · ‖parallelCLM g α b B‖ · ‖chartJinv α b‖)`.
On the POU tsupport (a compact subset of the chart source), each factor
admits a uniform bound by the existing infrastructure. -/

/-- Uniform bound on `M_b` on the POU tsupport. -/
private lemma chartLCConj_M_bound_on_pouTsupport
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ M_max : ℝ, 0 ≤ M_max ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        max 1
          (‖chartJ (I := I) (M := M) α b‖ *
            (‖chartLeviCivitaParallelCLM (I := I) g α b B.toFun‖ *
              ‖chartJinv (I := I) (M := M) α b‖)) ≤ M_max := by
  classical
  set K : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_def
  have hK_compact : IsCompact K := pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  obtain ⟨C_J, hCJ_pos, hCJ_bound⟩ :=
    chartJ_opNorm_isBounded_on_compact (I := I) (M := M) h_atlas α hK_compact hK_sub
  have hCJ_nn : 0 ≤ C_J := le_of_lt hCJ_pos
  obtain ⟨C_Jinv, hCJinv_pos, hCJinv_bound⟩ :=
    chartJinv_opNorm_isBounded_on_compact (I := I) (M := M)
      h_atlas α hK_compact hK_sub
  have hCJinv_nn : 0 ≤ C_Jinv := le_of_lt hCJinv_pos
  obtain ⟨C_P, hCP_nn, hCP_bound⟩ :=
    chartLeviCivitaParallelCLM_general_X_opNorm_isBounded_on_pouTsupport
      (I := I) (M := M) h_atlas g α
  -- Uniform bound on `‖B b‖` over K via chartJinv op-norm and continuity of
  -- the chart-trivialised representation `chartE_section_repr α B b`.
  obtain ⟨C_B, hCB_nn, hCB_bound⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K,
      ‖B.toFun b‖ ≤ C := by
    have hsection_cm : ContMDiffOn I (𝓘(ℝ, E)) ∞
        (chartE_section_repr (I := I) α B.toFun) (chartAt H α).source := by
      have hsmooth_total :
          ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
            (fun x : M => TotalSpace.mk' E
              (E := fun y : M => TangentSpace I y) x (B.toFun x)) :=
        B.contMDiff
      have hbase : (trivializationAt E (TangentSpace I) α).baseSet =
          (chartAt H α).source :=
        TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α
      have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
        (e := trivializationAt E (TangentSpace I) α)).mp
          hsmooth_total.contMDiffOn
      rw [hbase] at hrewrite
      refine ContMDiffOn.congr hrewrite ?_
      intro x hx
      have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [hbase]; exact hx
      change (trivializationAt E (TangentSpace I) α).linearMapAt ℝ x
        (B.toFun x) = _
      rw [Bundle.Trivialization.linearMapAt_apply, if_pos hx_base]
    have hcont_on : ContinuousOn
        (fun b : M => ‖chartE_section_repr (I := I) α B.toFun b‖) K :=
      (continuous_norm.comp_continuousOn hsection_cm.continuousOn).mono hK_sub
    rcases hK_compact.bddAbove_image hcont_on with ⟨MB, hMB⟩
    refine ⟨C_Jinv * max MB 0, mul_nonneg hCJinv_nn (le_max_right _ _), ?_⟩
    intro b hb
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
      exact hK_sub hb
    have h_inv :
        (trivFromE (I := I) α b)
            (chartE_section_repr (I := I) α B.toFun b) = B.toFun b :=
      trivFromE_trivToE (I := I) α (x := b) hb_base (B.toFun b)
    have h_op : ‖B.toFun b‖ ≤ ‖trivFromE (I := I) α b‖ *
        ‖chartE_section_repr (I := I) α B.toFun b‖ := by
      have h := (trivFromE (I := I) α b).le_opNorm
        (chartE_section_repr (I := I) α B.toFun b)
      rwa [h_inv] at h
    have h_repr_le :
        ‖chartE_section_repr (I := I) α B.toFun b‖ ≤ max MB 0 :=
      (hMB ⟨b, hb, rfl⟩).trans (le_max_left _ _)
    have hJinv_b : ‖trivFromE (I := I) α b‖ ≤ C_Jinv := hCJinv_bound b hb
    have h_repr_nn : 0 ≤ ‖chartE_section_repr (I := I) α B.toFun b‖ :=
      norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hJinv_b h_repr_nn,
      mul_le_mul_of_nonneg_left h_repr_le hCJinv_nn]
  -- Construct M_max := max 1 (C_J * (C_P * C_B * C_Jinv)).
  refine ⟨max 1 (C_J * (C_P * C_B * C_Jinv)),
    le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro b hb
  have h_CJ : ‖chartJ (I := I) (M := M) α b‖ ≤ C_J := hCJ_bound b hb
  have h_CJinv : ‖chartJinv (I := I) (M := M) α b‖ ≤ C_Jinv := hCJinv_bound b hb
  have h_CP : ‖chartLeviCivitaParallelCLM (I := I) g α b B.toFun‖ ≤
      C_P * ‖B.toFun b‖ := hCP_bound (b := b) hb B.toFun
  have h_CB : ‖B.toFun b‖ ≤ C_B := hCB_bound b hb
  have h_CJ_nn : 0 ≤ ‖chartJ (I := I) (M := M) α b‖ := norm_nonneg _
  have h_CJinv_nn : 0 ≤ ‖chartJinv (I := I) (M := M) α b‖ := norm_nonneg _
  have h_CP_nn' : 0 ≤ ‖chartLeviCivitaParallelCLM (I := I) g α b B.toFun‖ :=
    norm_nonneg _
  have h_Bnn : 0 ≤ ‖B.toFun b‖ := norm_nonneg _
  have h_full :
      ‖chartJ (I := I) (M := M) α b‖ *
        (‖chartLeviCivitaParallelCLM (I := I) g α b B.toFun‖ *
          ‖chartJinv (I := I) (M := M) α b‖) ≤
      C_J * (C_P * C_B * C_Jinv) := by
    have h1 : ‖chartLeviCivitaParallelCLM (I := I) g α b B.toFun‖ ≤ C_P * C_B :=
      h_CP.trans (mul_le_mul_of_nonneg_left h_CB hCP_nn)
    have h2 :
        ‖chartLeviCivitaParallelCLM (I := I) g α b B.toFun‖ *
          ‖chartJinv (I := I) (M := M) α b‖ ≤ C_P * C_B * C_Jinv := by
      have ha := mul_le_mul_of_nonneg_right h1 h_CJinv_nn
      have hb := mul_le_mul_of_nonneg_left h_CJinv (mul_nonneg hCP_nn hCB_nn)
      linarith
    have h3 :
        ‖chartJ (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B.toFun‖ *
            ‖chartJinv (I := I) (M := M) α b‖) ≤
          C_J * (C_P * C_B * C_Jinv) := by
      have ha := mul_le_mul_of_nonneg_right h_CJ (mul_nonneg h_CP_nn' h_CJinv_nn)
      have hb := mul_le_mul_of_nonneg_left h2 hCJ_nn
      linarith
    exact h3
  refine max_le ?_ ?_
  · exact le_max_left _ _
  · exact h_full.trans (le_max_right _ _)

/-! ### Headline uniform op-norm bound: input slot kernel -/

/-- **Uniform operator-norm bound for the chart-pulled input-slot kernel on
the intersection of the POU tsupport with the chart-`α` Levi-Civita good
set.** -/
theorem inputSlotChartKernel_opNorm_uniform_on_pouTsupport
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖inputSlotChartKernel (I := I) g r s α B.toFun k b‖ ≤ K := by
  classical
  obtain ⟨M_max, hM_max_nn, hM_max_bound⟩ :=
    chartLCConj_M_bound_on_pouTsupport (I := I) (M := M) h_atlas g α B
  refine ⟨M_max ^ r, by positivity, ?_⟩
  intro b hb
  have hb1 := hb.1
  have h_bound :
      max 1
        (‖chartJ (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B.toFun‖ *
            ‖chartJinv (I := I) (M := M) α b‖)) ≤ M_max :=
    hM_max_bound hb1
  have h_pow_le :
      (max 1
        (‖chartJ (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B.toFun‖ *
            ‖chartJinv (I := I) (M := M) α b‖))) ^ r ≤ M_max ^ r := by
    refine pow_le_pow_left₀ ?_ h_bound r
    exact le_trans zero_le_one (le_max_left _ _)
  have h_chain1 := inputSlotChartKernel_opNorm_le (I := I) (M := M)
    g r s α B.toFun k b
  have h_chain2 := inputSlotPrecompCLM_opNorm_le (I := I) (M := M)
    g r α B.toFun k b
  exact le_trans (le_trans h_chain1 h_chain2) h_pow_le

/-- **Uniform operator-norm bound for the chart-pulled output-slot kernel on
the intersection of the POU tsupport with the chart-`α` Levi-Civita good
set.** -/
theorem outputSlotChartKernel_opNorm_uniform_on_pouTsupport
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖outputSlotChartKernel (I := I) g r s α B.toFun l b‖ ≤ K := by
  classical
  obtain ⟨M_max, hM_max_nn, hM_max_bound⟩ :=
    chartLCConj_M_bound_on_pouTsupport (I := I) (M := M) h_atlas g α B
  refine ⟨M_max ^ s, by positivity, ?_⟩
  intro b hb
  have hb1 := hb.1
  have h_bound :
      max 1
        (‖chartJ (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B.toFun‖ *
            ‖chartJinv (I := I) (M := M) α b‖)) ≤ M_max :=
    hM_max_bound hb1
  have h_pow_le :
      (max 1
        (‖chartJ (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B.toFun‖ *
            ‖chartJinv (I := I) (M := M) α b‖))) ^ s ≤ M_max ^ s := by
    refine pow_le_pow_left₀ ?_ h_bound s
    exact le_trans zero_le_one (le_max_left _ _)
  have h_chain1 := outputSlotChartKernel_opNorm_le (I := I) (M := M)
    g r s α B.toFun l b
  have h_chain2 := outputSlotPostcompCLM_opNorm_le (I := I) (M := M)
    g s α B.toFun l b
  exact le_trans (le_trans h_chain1 h_chain2) h_pow_le

/-! ## Uniform fderiv bounds on `tsupport ∩ goodSet`

The chart-pulled kernel is `ContDiffOn ℝ ∞` on the open chart-target image
of the chart-`α` Levi-Civita good set. Hence its Fréchet-derivative is
continuous on that open set, and uniformly bounded on the closed compact
image of the POU tsupport ∩ good set. -/

/-- Chart-pulled `ContDiffOn` smoothness of `inputSlotChartKernel`. (Auxiliary
form, used to derive the uniform fderiv bound.) -/
private lemma inputSlotChartKernel_chart_pulled_contDiffOn_aux
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r) :
    ContDiffOn ℝ ∞
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  -- inputSlotChartKernel = (compL).flip (inputSlotPrecompCLM), so smooth
  -- chart-pulled follows from smoothness of inputSlotPrecompCLM chart-pulled.
  set L : (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel r ℝ E) →L[ℝ]
      ((Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
        (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)) :=
    (ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel r ℝ E) (Tensor0SModel s ℝ E)).flip with hL_def
  have hL_smooth : ContDiff ℝ ∞ (L : _ → _) := L.contDiff
  intro y hy
  obtain ⟨b, hb_good, hyb⟩ := hy
  subst hyb
  have h_precomp_at := inputSlotPrecompCLM_chart_pulled_contDiffAt
    (I := I) (M := M) g r α B k hb_good
  have hcomposed := hL_smooth.contDiffAt.comp (x := extChartAt I α b) h_precomp_at
  have h_at : ContDiffAt ℝ ∞
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y))
      (extChartAt I α b) := by
    refine hcomposed.congr_of_eventuallyEq ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    rfl
  exact h_at.contDiffWithinAt

/-- Chart-pulled `ContDiffOn` smoothness of `outputSlotChartKernel`. (Auxiliary
form, used to derive the uniform fderiv bound.) -/
private lemma outputSlotChartKernel_chart_pulled_contDiffOn_aux
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s) :
    ContDiffOn ℝ ∞
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  set L : (Tensor0SModel s ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
      ((Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
        (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)) :=
    ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel s ℝ E) (Tensor0SModel s ℝ E) with hL_def
  have hL_smooth : ContDiff ℝ ∞ (L : _ → _) := L.contDiff
  intro y hy
  obtain ⟨b, hb_good, hyb⟩ := hy
  subst hyb
  have h_postcomp_at := outputSlotPostcompCLM_chart_pulled_contDiffAt
    (I := I) (M := M) g s α B l hb_good
  have hcomposed := hL_smooth.contDiffAt.comp (x := extChartAt I α b) h_postcomp_at
  have h_at : ContDiffAt ℝ ∞
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y))
      (extChartAt I α b) := by
    refine hcomposed.congr_of_eventuallyEq ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    rfl
  exact h_at.contDiffWithinAt

/-! ### Continuity of the chart-pulled fderiv on the open good-set image -/

private lemma inputSlotChartKernel_fderiv_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r) :
    ContinuousOn
      (fun y : E => ‖fderiv ℝ
        (fun y' : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y')) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hcd := inputSlotChartKernel_chart_pulled_contDiffOn_aux (I := I) (M := M)
    g r s α B k
  have hOpen := goodSet_image_isOpen (I := I) (M := M) α
  have hfd_cd : ContDiffOn ℝ ∞
      (fderiv ℝ (fun y' : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y')))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
    have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
    exact hcd.fderiv_of_isOpen hOpen h_le
  exact continuous_norm.comp_continuousOn hfd_cd.continuousOn

private lemma outputSlotChartKernel_fderiv_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s) :
    ContinuousOn
      (fun y : E => ‖fderiv ℝ
        (fun y' : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y')) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hcd := outputSlotChartKernel_chart_pulled_contDiffOn_aux (I := I) (M := M)
    g r s α B l
  have hOpen := goodSet_image_isOpen (I := I) (M := M) α
  have hfd_cd : ContDiffOn ℝ ∞
      (fderiv ℝ (fun y' : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y')))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
    have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
    exact hcd.fderiv_of_isOpen hOpen h_le
  exact continuous_norm.comp_continuousOn hfd_cd.continuousOn

/-! ### Uniform fderiv bound on POU tsupport ∩ goodSet -/

/-- **Uniform Fréchet-derivative op-norm bound for the chart-pulled
input-slot kernel.** -/
theorem inputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖fderiv ℝ
            (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                            ((extChartAt I α).symm y))
            (extChartAt I α b)‖ ≤ K := by
  classical
  -- The fderiv bound follows from continuity of fderiv on the open good-set
  -- image. We retain `h_atlas` in the signature for API uniformity.
  let _ := h_atlas
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  -- Continuity on the open image; restrict via continuous extChartAt.
  have hcont := inputSlotChartKernel_fderiv_continuousOn (I := I) (M := M)
    g r s α B k
  -- Map K_set into the good-set image via extChartAt.
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α := by
    intro b hb
    have h_eq :=
      chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
    rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
    exact hK_sub hb
  have hmaps : Set.MapsTo (extChartAt I α) K_set
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    fun b hb => ⟨b, hK_sub_good hb, rfl⟩
  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
  have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
    (hφ_cm.continuousOn).mono hK_sub
  have hcont_M : ContinuousOn (fun b : M =>
      ‖fderiv ℝ
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y)) (extChartAt I α b)‖) K_set :=
    hcont.comp hφ_cont hmaps
  obtain ⟨C, hC_mem⟩ := hK_compact.bddAbove_image hcont_M
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  have hb_K : b ∈ K_set := hb.1
  have h := hC_mem ⟨b, hb_K, rfl⟩
  exact le_trans h (le_max_left _ _)

/-- **Uniform Fréchet-derivative op-norm bound for the chart-pulled
output-slot kernel.** -/
theorem outputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖fderiv ℝ
            (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                            ((extChartAt I α).symm y))
            (extChartAt I α b)‖ ≤ K := by
  classical
  let _ := h_atlas
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hcont := outputSlotChartKernel_fderiv_continuousOn (I := I) (M := M)
    g r s α B l
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α := by
    intro b hb
    have h_eq :=
      chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
    rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
    exact hK_sub hb
  have hmaps : Set.MapsTo (extChartAt I α) K_set
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    fun b hb => ⟨b, hK_sub_good hb, rfl⟩
  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
  have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
    (hφ_cm.continuousOn).mono hK_sub
  have hcont_M : ContinuousOn (fun b : M =>
      ‖fderiv ℝ
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y)) (extChartAt I α b)‖) K_set :=
    hcont.comp hφ_cont hmaps
  obtain ⟨C, hC_mem⟩ := hK_compact.bddAbove_image hcont_M
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  have hb_K : b ∈ K_set := hb.1
  have h := hC_mem ⟨b, hb_K, rfl⟩
  exact le_trans h (le_max_left _ _)

end Connection
end Integral
end DifferentialGeometry

end
