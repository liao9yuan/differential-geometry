import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AkMFold
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricFlatBasis

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Claim 1 geometric wiring (plan: `Claim1Wiring.md`)

Discharges the hypotheses of `claim1` (AkMFold.lean) on the actual geometry.
Canonical setting (design D2b): a tangent-bundle trivialization `e₀` with
`frame := e₀.localFrame basisE`, `u := e₀.baseSet`.

SIGN CONVENTION (`Claim1Wiring.md` §1b): `A_k = ∇_k − ∇_ref`, so the `A_k`
component array is `chr(g_k) − chr(gRef)` and the lowered-Koszul coefficients
are `(+½, +½, −½)`.

This file so far: **B2** (smoothness inputs `hchr`, `hframe`, `hA`).
TODO (B2 tail): `hg` = smoothness of `frameComp0S (metricTensorField g) frame`
via `TensorMultilinear.contMDiffAt_section_apply_gen` (the (0,s) eval engine
inside `tensorRS_eval_contMDiffAt`, `Tensor/RSTensor/LocalFrameRegularity.lean`)
once the `metricTensorField`-as-smooth-section producer is located.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-! ## B2: the smoothness inputs of `claim1` on a trivialization domain -/

/-- **B2 `hchr`**: the Levi-Civita Christoffel array of `g` in the trivialization
frame is `C^∞` on the trivialization domain (the `ContMDiffOn` form the component
towers consume).  Analytic content = `lc_christoffel_contMDiffAt`
(`LeviCivita/Smooth/MetricFlatBasis.lean`, the `localFrame_coeff` form); here we
bridge `IsLocalFrameOn.coeff` to `localFrame_coeff` on the trivialization domain. -/
theorem lcChrist_e_mdiffOn
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    (d i j : Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y : M => christoffelSymbolInFrame
        (leviCivitaConnectionOfMetric (I := I) g)
        (fun a y' => e₀.localFrame basisE a y')
        (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y d i j)
      e₀.baseSet := by
  intro y hy
  refine ((lc_christoffel_contMDiffAt (I := I) e₀ basisE g hy d i j).congr_of_eventuallyEq
    ?_).contMDiffWithinAt
  filter_upwards [e₀.open_baseSet.mem_nhds hy] with z hz
  have hbasis : (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hz =
      e₀.basisAt basisE hz := by
    ext j'
    simp [IsLocalFrameOn.toBasisAt, Bundle.Trivialization.localFrame,
      Bundle.Trivialization.basisAt, hz]
  simp [christoffelSymbolInFrame, IsLocalFrameOn.coeff, hz,
    Bundle.Trivialization.localFrame_coeff, hbasis]

/-- **B2 `hframe`**: the trivialization frame vectors are smooth sections on the
trivialization domain (the `TotalSpace.mk'` form the tower machinery consumes). -/
theorem frame_e_mdiffOn
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (basisE : Module.Basis Idx Real E) (d : Idx) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (e₀.localFrame basisE d y))
      e₀.baseSet :=
  (e₀.isLocalFrameOn_localFrame_baseSet I ∞ basisE).contMDiffOn d

/-- The `A_k = ∇_k − ∇_ref` component field in the trivialization frame, with the
contracted UPPER slot LAST (`m 2`), as the towers and `claim1` consume it:
`A(m) = Γ(g_k)^{m 2}_{m 0, m 1} − Γ(gRef)^{m 2}_{m 0, m 1}`. -/
def akCompField
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (gK gRef : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E) :
    M → (Fin (2 + 1) → Idx) → Real :=
  fun y m =>
    christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gK)
      (fun a y' => e₀.localFrame basisE a y')
      (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y (m 0) (m 1) (m 2) -
    christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
      (fun a y' => e₀.localFrame basisE a y')
      (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y (m 0) (m 1) (m 2)

/-- **B2 `hA`**: the `A_k` component field is `C^∞` on the trivialization domain
(difference of the two smooth Christoffel arrays). -/
theorem akCompField_mdiffOn
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (gK gRef : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    (k : Fin (2 + 1) → Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => akCompField (I := I) e₀ gK gRef basisE y k) e₀.baseSet := by
  exact (lcChrist_e_mdiffOn e₀ gK basisE (k 0) (k 1) (k 2)).sub
    (lcChrist_e_mdiffOn e₀ gRef basisE (k 0) (k 1) (k 2))

set_option backward.isDefEq.respectTransparency false in
/-- **B2 `hg`**: the metric component field in the trivialization frame is `C^∞` on the
trivialization domain (the smooth `(0,2)` section `metricTensorField g` evaluated on the
smooth frame slots, via the `(0,s)` evaluation engine). -/
theorem gCompField_mdiffOn
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    (k : Fin (1 + 1) → Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => frameComp0S (I := I) (metricTensorField (I := I) g)
        (fun a y' => e₀.localFrame basisE a y') y k) e₀.baseSet := by
  intro y hy
  have hT : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun x : M => Tensor0SSpace 2 I x) b (metricTensorField (I := I) g b)) y :=
    (metricTensorField (I := I) g).contMDiff.contMDiffAt
  have hv : ∀ i : Fin 2,
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b
          (e₀.localFrame basisE (k i) b)) y :=
    fun i => (frame_e_mdiffOn e₀ basisE (k i)).contMDiffAt (e₀.open_baseSet.mem_nhds hy)
  have h := TensorMultilinear.contMDiffAt_section_apply_gen
    (T := fun b : M => metricTensorField (I := I) g b) hT
    (v := fun (i : Fin 2) (b : M) => e₀.localFrame basisE (k i) b) hv
  exact h.contMDiffWithinAt

end DifferentialGeometry.PDE.RicciFlow
