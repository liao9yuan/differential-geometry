/-
Authors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.RSTensor.Field
import DifferentialGeometry.Tensor.RSTensor.Contract
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

set_option linter.style.longLine false

/-!
# Riemannian Metric on a Smooth Manifold

We define `RiemannianMetric` on a smooth manifold `M` as a `ContMDiffRiemannianMetric`
from Mathlib, specialized to the tangent bundle of `M`.

## Main Definitions

* `RiemannianMetric I n M` : a smooth Riemannian metric on `M`, i.e. a smoothly varying
  family of inner products on the tangent spaces of `M`.
* `RiemannianMetric.to02Tensor` : convert a Riemannian metric to a smooth (0,2)-tensor field.
-/

noncomputable section

open Bundle Manifold Tensor0SBundle

open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable (n : WithTop ℕ∞)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

/-- A Riemannian metric on a smooth manifold `M` is a `ContMDiffRiemannianMetric` on the
tangent bundle, i.e. a smoothly varying family of inner products on the tangent spaces. -/
abbrev RiemannianMetric := Bundle.ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)

section Aux
variable {I} {n} {M}

/-- The forward trivialization of the tangent bundle at `x₀`, viewed as a non-dependent
`(E →L[ℝ] E)`-valued function. -/
noncomputable def trivializationAt_clmAtFun (x₀ : M) : M → (E →L[ℝ] E) :=
  fun x => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x

set_option linter.unusedSectionVars false in
/-- The second component of the trivialization `e₀` is jointly smooth on the total space.
Since `(e₀ p).2 = clmAt(e₀, p.1) p.2`, this says `(b, v) ↦ clmAt(e₀, b) v` is `C^n`
as a map from the total space manifold to `E`. -/
lemma contMDiffOn_trivializationAt_snd {x₀ : M} :
    ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) n
      (fun p : TotalSpace E (TangentSpace I) =>
        (trivializationAt E (TangentSpace I) x₀ p).2)
      (trivializationAt E (TangentSpace I) x₀).source :=
  contMDiff_snd.comp_contMDiffOn (trivializationAt E (TangentSpace I) x₀).contMDiffOn

/-- For each `v : E`, the pointwise evaluation `b ↦ clmAt(e₀, b) v` is `C^n` on `baseSet`.
This follows from `contMDiffOn_trivializationAt_snd` (joint smoothness of
`(b, v) ↦ clmAt(e₀, b) v` on the total space) together with the fact that `clmAt(e₀, b)`
is linear in `v` for each `b`. -/
lemma contMDiffOn_trivializationAt_clmAt_apply {x₀ : M} (v : E) :
    ContMDiffOn I 𝓘(ℝ, E) n
      (fun x => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x v)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  sorry

/-- The forward trivialization `continuousLinearMapAt` of the tangent bundle at `x₀`
varies C^n-smoothly within the base set.
Uses `contMDiffOn_trivializationAt_clmAt_apply` (pointwise smoothness for each `v`)
and `contDiff_clm_apply_iff` (a CLM-valued function from a finite-dimensional space is C^n
iff all pointwise evaluations are). -/
theorem contMDiffWithinAt_trivializationAt_clmAt (n : WithTop ℕ∞) {x₀ : M} :
    ContMDiffWithinAt I 𝓘(ℝ, E →L[ℝ] E) n
      (trivializationAt_clmAtFun (I := I) (M := M) x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet x₀ := by
  sorry

end Aux

/-- Convert a Riemannian metric to a smooth (0,2)-tensor field. At each point `x`, the
inner product `g.inner x : TₓM →L[ℝ] TₓM →L[ℝ] ℝ` is uncurried into a continuous
bilinear form `TₓM × TₓM → ℝ`, i.e. a (0,2)-tensor. -/
def RiemannianMetric.to02Tensor {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    (g : RiemannianMetric I n M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (I := I) (M := M) (n := n) 2 := by
  unfold Tensor0SBundle.Tensor0SField
  letI := Tensor0SBundle.tensor0SBundle_topology
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  let eCLM := (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let uCLM := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let gI := Bundle.ContMDiffRiemannianMetric.inner g
  exact ⟨fun x => (eCLM.comp (gI x)).uncurryLeft, by
    haveI := Tensor0SBundle.tensor0SBundle_smooth
      (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := n) 2
    intro x₀; rw [contMDiffAt_section]
    have triv_2 : ∀ (x : M) (f : Tensor0SBundle.Tensor0SSpace 2 I x),
        (trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun x => Tensor0SBundle.Tensor0SSpace 2 I x) x₀ ⟨x, f⟩).2 = f := by
      intro x f; simp only [trivializationAt, FiberBundle.trivializationAt']; sorry
    simp_rw [triv_2]
    -- Extract trivialized smoothness and smooth coordinate changes.
    set e₀ := trivializationAt E (TangentSpace I) x₀
    have hTriv := (contMDiffAt_section (F := E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        (s := gI) (x₀ := x₀)).mp (g.contMDiff.contMDiffAt (x := x₀))
    let clmAtFun : M → (E →L[ℝ] E) := fun x => e₀.continuousLinearMapAt ℝ x
    have hClmAt : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) n clmAtFun x₀ :=
      (contMDiffWithinAt_trivializationAt_clmAt n).contMDiffAt
        (e₀.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) x₀))
    -- Build smooth R(x).comp(H(x)) that equals gI on baseSet.
    have hSmooth := (contMDiffAt_const.clm_apply hClmAt :
      ContMDiffAt I 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ) n
        (fun x => (ContinuousLinearMap.compL ℝ E E ℝ).flip (clmAtFun x)) x₀).clm_comp
      (hTriv.clm_comp hClmAt)
    let gIFun : M → (E →L[ℝ] E →L[ℝ] ℝ) := fun x => gI x
    suffices hgI : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) n gIFun x₀ by
      exact uCLM.contMDiffAt.comp x₀ (contMDiffAt_const.clm_comp hgI)
    apply hSmooth.congr_of_eventuallyEq
    filter_upwards
      [e₀.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) x₀)]
    intro x hx; dsimp only [gIFun, clmAtFun]
    -- Reduce to inCoordinates form, cancel symmL ∘ clmAt on both arguments.
    ext a b
    change (gI x) a b = ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
        (fun b => TangentSpace I b →L[ℝ] ℝ) x₀ x x₀ x (gI x)
        (e₀.continuousLinearMapAt ℝ x a) (e₀.continuousLinearMapAt ℝ x b)
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.coe_comp',
      Function.comp_apply, show trivializationAt E (TangentSpace I) x₀ = e₀ from rfl]
    rw [Trivialization.symmL_continuousLinearMapAt e₀ hx a]
    -- Unwrap the cotangent trivialization to expose and cancel the second symmL.
    have hx_cot : x ∈ (trivializationAt (E →L[ℝ] ℝ)
        (fun b => TangentSpace I b →L[ℝ] ℝ) x₀).baseSet := by
      rw [hom_trivializationAt_baseSet]
      exact ⟨hx, by simp [trivializationAt, FiberBundle.trivializationAt']⟩
    simp only [Trivialization.continuousLinearMapAt, Trivialization.linearMapAt,
      Pretrivialization.linearMapAt,
      dif_pos (show x ∈ (trivializationAt (E →L[ℝ] ℝ)
        (fun b => TangentSpace I b →L[ℝ] ℝ) x₀).toPretrivialization.baseSet from hx_cot),
      dif_pos (show x ∈ e₀.toPretrivialization.baseSet from hx),
      Pretrivialization.linearEquivAt]
    dsimp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
    show (gI x) a b = (trivializationAt ℝ (fun _ : M => ℝ) x₀).continuousLinearMapAt ℝ x
        ((gI x a) ((e₀.symmL ℝ x) ((e₀ ⟨x, b⟩).2)))
    rw [show (e₀.symmL ℝ x) ((e₀ ⟨x, b⟩).2) = b from
      Trivialization.symm_apply_apply_mk e₀ hx b]; simp⟩

end
