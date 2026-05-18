import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.CanonicalTensorRepr
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.Hom

/-!
# The tensor transformation law for raw chart-frame components

For a closed Riemannian manifold `(M, g)` and fixed ranks `(r, s)`, the raw
chart-frame scalar component `tensorChartComponentRaw g r s S α P` of a smooth
compactly-supported `(r, s)`-tensor section `S` depends on the chart base point
`α`: it reads the section through the trivialisation of the `(r, s)`-tensor
bundle centred at `α`.

On the overlap of two chart sources, the raw component computed in the chart at
`α` is a finite linear combination of the raw components computed in the chart
at `γ`, with smooth coefficients. This file proves that transformation law.

## The mathematical content

The raw component is
`tensorChartComponentRaw g r s S α Idx Jdx x =
  tensorChartComponentProjection r s Idx Jdx (tensorTrivProj g r s S α x)`,
where `tensorTrivProj g r s S α x` is the image of the section value
`S.toSection x` under the fibre projection of the trivialisation centred at
`α`.

The two trivialisations centred at `γ` and `α` are related, on the overlap of
their base sets, by the bundle coordinate-change continuous linear map
`Trivialization.coordChangeL ℝ (triv γ) (triv α) x` — a continuous linear
isomorphism of the model fibre `TensorRSModel r s ℝ E`. Concretely

`tensorTrivProj g r s S α x =
  coordChangeL ℝ (triv γ) (triv α) x (tensorTrivProj g r s S γ x)`

on the chart overlap, because the inverse fibre projection of `triv γ`
recovers `S.toSection x` from `tensorTrivProj g r s S γ x`.

Expanding `tensorTrivProj g r s S γ x` in the chart-frame basis of
`TensorRSModel r s ℝ E` (`tensorRSModel_eq_sum_basis`) and using linearity of
both the coordinate-change map and the component projection yields the
transformation law. The coefficient indexed by a multi-index pair `Q` is the
`P₀`-component of the coordinate-change image of the `Q`-th chart-frame basis
element of `TensorRSModel r s ℝ E`; it is smooth on the chart overlap because
the bundle coordinate change is `C^∞` there (`contMDiffOn_coordChangeL`).

## Main results

* `tensorChartComponentRaw_chartTransition_decomp` — the transformation law:
  on the overlap of the chart sources at `γ` and `α`, the raw component in the
  chart at `α` is a finite linear combination, with coefficients smooth on the
  overlap, of the raw components in the chart at `γ`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M`

These are required only to keep the ambient instance environment consistent
with the imported files; they do not leak onto the public signature. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The `(r, s)`-tensor bundle of `M`

The mixed `(r, s)`-tensor bundle has model fibre `TensorRSModel r s ℝ E` and
fibre `TensorRSSpace r s I x` at `x : M`. Its fibre-bundle, vector-bundle and
`C^∞`-vector-bundle structures are the ones declared in `Tensor.RSTensor.Defs`.

The trivialisation at a base point `α : M` is
`trivializationAt (TensorRSModel r s ℝ E) (fun y : M => TensorRSSpace r s I y) α`.
It is a member of the trivialisation atlas, and — since the bundle is a vector
bundle — it is linear in the fibres, so the bundle coordinate-change map
`Trivialization.coordChangeL` between two such trivialisations is available. -/

/-- The trivialisation of the `(r, s)`-tensor bundle centred at `α : M`.

Declared `@[reducible]` so that instance synthesis sees through it to the
underlying `trivializationAt`, making the standard `MemTrivializationAtlas`
instance fire on `rsTriv`. -/
@[reducible] private def rsTriv (r s : ℕ) (α : M) :
    Trivialization (TensorRSModel r s ℝ E)
      (Bundle.TotalSpace.proj (F := TensorRSModel r s ℝ E)
        (E := fun y : M => TensorRSSpace r s I y)) :=
  trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) α

/-- The base set of the `(r, s)`-tensor bundle trivialisation at `α` is the
chart source at `α`. The `(r, s)`-tensor bundle is the hom-bundle of the
`(0, r)`- and `(0, s)`-tensor bundles, whose trivialisation base sets are both
the chart source; the hom-bundle base set is their intersection. -/
private lemma rsTriv_baseSet (r s : ℕ) (α : M) :
    (rsTriv (E := E) (I := I) (M := M) r s α).baseSet = (chartAt H α).source := by
  classical
  change ((trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) α).baseSet) =
    (chartAt H α).source
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
  rw [Set.inter_self]
  rfl

/-! ## The trivialisation projection identified through `tensorTrivProj`

`tensorTrivProj g r s S α x` is, by definition, the fibre projection of the
section value `S.toSection x` through the trivialisation centred at `α`. -/

/-- The fibre projection through the trivialisation centred at `α` recovers
`tensorTrivProj`. -/
private lemma tensorTrivProj_eq_clmAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (x : M) :
    tensorTrivProj (I := I) (M := M) g r s S α x =
      (rsTriv (E := E) (I := I) (M := M) r s α).continuousLinearMapAt ℝ x
        (S.toSection x) := rfl

/-! ## The bundle coordinate-change identity for the trivialisation projection

The fibre projections of two trivialisations are related, on the overlap of
their base sets, by the bundle coordinate-change continuous linear map. The
proof unfolds `Trivialization.coordChangeL` to the composition of the inverse
fibre projection of the first trivialisation with the fibre projection of the
second; the inverse fibre projection cancels against the fibre projection
inside `tensorTrivProj`. -/

/-- Applying the coordinate-change map of two trivialisations equals the
fibre projection of the second composed with the inverse fibre projection of
the first. This is the `(r, s)`-tensor-bundle analogue of the standard
tangent-bundle identity. -/
private lemma coordChangeL_apply_eq_clmAt_symmL
    (r s : ℕ) (γ α : M) {x : M}
    (hxγ : x ∈ (chartAt H γ).source) (hxα : x ∈ (chartAt H α).source)
    (w : TensorRSModel r s ℝ E) :
    ((rsTriv (E := E) (I := I) (M := M) r s γ).coordChangeL ℝ
        (rsTriv (E := E) (I := I) (M := M) r s α) x) w =
      (rsTriv (E := E) (I := I) (M := M) r s α).continuousLinearMapAt ℝ x
        ((rsTriv (E := E) (I := I) (M := M) r s γ).symmL ℝ x w) := by
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  letI : TopologicalSpace (TotalSpace (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y)) :=
    tensorRSBundle_topology r s
  letI : FiberBundle (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_fiber r s
  letI : VectorBundle ℝ (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_vector r s
  have hxγ' : x ∈ (rsTriv (E := E) (I := I) (M := M) r s γ).baseSet := by
    rw [rsTriv_baseSet]; exact hxγ
  have hxα' : x ∈ (rsTriv (E := E) (I := I) (M := M) r s α).baseSet := by
    rw [rsTriv_baseSet]; exact hxα
  rw [Bundle.Trivialization.coordChangeL_apply _ _ ⟨hxγ', hxα'⟩,
    Bundle.Trivialization.continuousLinearMapAt_apply,
    Bundle.Trivialization.coe_linearMapAt_of_mem _ hxα',
    Bundle.Trivialization.symmL_apply]

/-- **The trivialisation transformation law for `tensorTrivProj`.** On the
overlap of the chart sources at `γ` and `α`, the trivialisation projection
centred at `α` is the bundle coordinate-change image of the trivialisation
projection centred at `γ`. -/
private lemma tensorTrivProj_chartTransition
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (γ α : M) {x : M}
    (hxγ : x ∈ (chartAt H γ).source) (hxα : x ∈ (chartAt H α).source) :
    tensorTrivProj (I := I) (M := M) g r s S α x =
      ((rsTriv (E := E) (I := I) (M := M) r s γ).coordChangeL ℝ
          (rsTriv (E := E) (I := I) (M := M) r s α) x)
        (tensorTrivProj (I := I) (M := M) g r s S γ x) := by
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  letI : TopologicalSpace (TotalSpace (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y)) :=
    tensorRSBundle_topology r s
  letI : FiberBundle (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_fiber r s
  letI : VectorBundle ℝ (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_vector r s
  have hxγ' : x ∈ (rsTriv (E := E) (I := I) (M := M) r s γ).baseSet := by
    rw [rsTriv_baseSet]; exact hxγ
  -- The coordinate-change map of `tensorTrivProj … γ x` unfolds to the
  -- `α`-projection of the `γ`-inverse-projection of the `γ`-projection.
  rw [tensorTrivProj_eq_clmAt (I := I) (M := M) g r s S γ x,
    coordChangeL_apply_eq_clmAt_symmL (E := E) (I := I) (M := M) r s γ α
      hxγ hxα]
  -- The `γ`-inverse-projection cancels the `γ`-projection (centre membership).
  rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hxγ' (S.toSection x)]
  exact (tensorTrivProj_eq_clmAt (I := I) (M := M) g r s S α x)

/-! ## The smooth transition-coefficient family

For a fixed component multi-index `P₀` the transition coefficient indexed by a
multi-index pair `Q` is the `P₀`-component, in the chart-frame basis of
`TensorRSModel r s ℝ E`, of the coordinate-change image of the `Q`-th
chart-frame basis element. As `x` ranges over the chart overlap this is a
scalar function `M → ℝ`. -/

/-- The transition-coefficient function: the `P₀`-component of the bundle
coordinate-change image of the `Q`-th chart-frame basis element of
`TensorRSModel r s ℝ E`, as a scalar function of the base point. -/
private def transitionCoeff
    (r s : ℕ) (γ α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) (x : M) : ℝ :=
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  letI : TopologicalSpace (TotalSpace (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y)) :=
    tensorRSBundle_topology r s
  letI : FiberBundle (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_fiber r s
  letI : VectorBundle ℝ (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_vector r s
  tensorChartComponentProjection (E := E) r s P₀.1 P₀.2
    (((rsTriv (E := E) (I := I) (M := M) r s γ).coordChangeL ℝ
        (rsTriv (E := E) (I := I) (M := M) r s α) x)
      (tensorChartBasisElement (E := E) r s Q.1 Q.2))

/-! ### Smoothness of the bundle coordinate change on the chart overlap

The bundle coordinate change `x ↦ coordChangeL ℝ (triv γ) (triv α) x` is `C^∞`
on the intersection of the trivialisation base sets — i.e. on the chart
overlap — because the `(r, s)`-tensor bundle is a `C^∞` vector bundle. -/

/-- The bundle coordinate change of the `(r, s)`-tensor-bundle trivialisations
is `C^∞` on the chart overlap, as a map into the continuous linear
endomorphisms of the model fibre. -/
private lemma contMDiffOn_rsCoordChangeL (r s : ℕ) (γ α : M) :
    ContMDiffOn I (modelWithCornersSelf ℝ
        (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M =>
        ((rsTriv (E := E) (I := I) (M := M) r s γ).coordChangeL ℝ
          (rsTriv (E := E) (I := I) (M := M) r s α) x :
          TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E))
      ((chartAt H γ).source ∩ (chartAt H α).source) := by
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  letI : TopologicalSpace (TotalSpace (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y)) :=
    tensorRSBundle_topology r s
  letI : FiberBundle (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_fiber r s
  letI : VectorBundle ℝ (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_vector r s
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) I :=
    tensorRSBundle_smooth ∞ r s
  have h := contMDiffOn_coordChangeL (n := (∞ : WithTop ℕ∞)) (IB := I)
    (F := TensorRSModel r s ℝ E)
    (E := fun y : M => TensorRSSpace r s I y)
    (rsTriv (E := E) (I := I) (M := M) r s γ)
    (rsTriv (E := E) (I := I) (M := M) r s α)
  rwa [rsTriv_baseSet, rsTriv_baseSet] at h

/-- **Smoothness of the transition coefficient.** For each multi-index pair `Q`
the transition coefficient `transitionCoeff r s γ α P₀ Q` is `C^∞` on the
chart overlap. It is the composition of the smooth bundle coordinate change
with a constant chart-frame basis element and a constant component projection,
all `C^∞`. -/
private lemma contMDiffOn_transitionCoeff
    (r s : ℕ) (γ α : M) (P₀ Q : TensorCompIdx (E := E) r s) :
    ContMDiffOn I (modelWithCornersSelf ℝ ℝ) ∞
      (transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q)
      ((chartAt H γ).source ∩ (chartAt H α).source) := by
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  -- The coordinate change is `C^∞` as a map into endomorphisms of the model.
  have hcoord := contMDiffOn_rsCoordChangeL (E := E) (I := I) (M := M) r s γ α
  -- Apply it at the constant chart-frame basis element `Q`.
  have hcoord_app : ContMDiffOn I
      (modelWithCornersSelf ℝ (TensorRSModel r s ℝ E)) ∞
      (fun x : M =>
        ((rsTriv (E := E) (I := I) (M := M) r s γ).coordChangeL ℝ
          (rsTriv (E := E) (I := I) (M := M) r s α) x :
          TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
            (tensorChartBasisElement (E := E) r s Q.1 Q.2))
      ((chartAt H γ).source ∩ (chartAt H α).source) :=
    hcoord.clm_apply contMDiffOn_const
  -- Compose with the constant component-projection continuous linear map.
  have hproj : ContMDiff
      (modelWithCornersSelf ℝ (TensorRSModel r s ℝ E))
      (modelWithCornersSelf ℝ ℝ) ∞
      (tensorChartComponentProjection (E := E) r s P₀.1 P₀.2) :=
    (tensorChartComponentProjection (E := E) r s P₀.1 P₀.2).contMDiff
  exact hproj.comp_contMDiffOn hcoord_app

/-! ## The transformation law

The headline. On the chart overlap, the raw component in the chart at `α` is a
finite linear combination, with coefficients smooth on the overlap, of the raw
components in the chart at `γ`. -/

/-- **Tensor transformation law for raw chart-frame components.** For a smooth
compactly-supported `(r, s)`-tensor section `S`, two chart base points `γ` and
`α`, and a component multi-index `P₀`, there is a family of coefficient
functions `c Q`, each `C^∞` on the overlap of the chart sources at `γ` and
`α`, such that on that overlap the raw chart-frame component of `S` in the
chart at `α` equals the finite sum over component multi-indices `Q` of
`c Q · (raw component of S in the chart at γ)`.

The coefficients `c Q` are the components of the `(r, s)`-tensor-power
chart-transition Jacobian: each `c Q x` is the `P₀`-component, in the
chart-frame basis of the model fibre `TensorRSModel r s ℝ E`, of the bundle
coordinate-change image of the `Q`-th chart-frame basis element. Smoothness on
the overlap holds because the chart transition is a `C^∞` diffeomorphism there,
so the induced bundle coordinate change is `C^∞`. -/
theorem tensorChartComponentRaw_chartTransition_decomp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (γ α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    ∃ c : TensorCompIdx (E := E) r s → M → ℝ,
      (∀ Q, ContMDiffOn I (modelWithCornersSelf ℝ ℝ) ∞ (c Q)
        ((chartAt H γ).source ∩ (chartAt H α).source)) ∧
      ∀ x ∈ (chartAt H γ).source ∩ (chartAt H α).source,
        tensorChartComponentRaw (I := I) (M := M) g r s S α P₀.1 P₀.2 x =
          ∑ Q : TensorCompIdx (E := E) r s,
            c Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s S γ Q.1 Q.2 x := by
  classical
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  refine ⟨transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀, ?_, ?_⟩
  · -- Smoothness of every coefficient.
    intro Q
    exact contMDiffOn_transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q
  · -- The pointwise decomposition on the chart overlap.
    intro x hx
    obtain ⟨hxγ, hxα⟩ := hx
    -- The raw `α`-component is the projection of the `α`-trivialisation image.
    rw [tensorChartComponentRaw_def (I := I) (M := M) g r s S α P₀.1 P₀.2]
    -- The `α`-trivialisation image is the coordinate-change image of the
    -- `γ`-trivialisation image (bundle transformation law).
    rw [tensorTrivProj_chartTransition (E := E) (I := I) (M := M)
      g r s S γ α hxγ hxα]
    -- Abbreviate the bundle coordinate-change continuous linear equivalence.
    set L : TensorRSModel r s ℝ E ≃L[ℝ] TensorRSModel r s ℝ E :=
      (rsTriv (E := E) (I := I) (M := M) r s γ).coordChangeL ℝ
        (rsTriv (E := E) (I := I) (M := M) r s α) x with hL_def
    -- Expand the `γ`-trivialisation image in the chart-frame basis.
    have hsum := tensorRSModel_eq_sum_basis (E := E) r s
      (tensorTrivProj (I := I) (M := M) g r s S γ x)
    -- Rewrite the argument of `L` by the basis expansion, then push `L`
    -- and the projection through the finite double sum by linearity.
    conv_lhs => rw [hsum]
    -- The double sum over `(Idx, Jdx)` is reindexed as a single sum over the
    -- multi-index pair type `TensorCompIdx r s`.
    rw [show (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                tensorChartComponentProjection (E := E) r s Idx Jdx
                    (tensorTrivProj (I := I) (M := M) g r s S γ x) •
                  tensorChartBasisElement (E := E) r s Idx Jdx) =
          ∑ Q : TensorCompIdx (E := E) r s,
            tensorChartComponentProjection (E := E) r s Q.1 Q.2
                (tensorTrivProj (I := I) (M := M) g r s S γ x) •
              tensorChartBasisElement (E := E) r s Q.1 Q.2 from
      (Finset.sum_product'
        (s := (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))))
        (t := (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))))
        (f := fun Idx Jdx =>
          tensorChartComponentProjection (E := E) r s Idx Jdx
              (tensorTrivProj (I := I) (M := M) g r s S γ x) •
            tensorChartBasisElement (E := E) r s Idx Jdx)).symm]
    -- Push `L` (a continuous linear equivalence) through the finite sum, then
    -- push the component projection through, and identify each summand.
    rw [map_sum L, map_sum (tensorChartComponentProjection (E := E) r s P₀.1 P₀.2)]
    refine Finset.sum_congr rfl ?_
    intro Q _
    -- Push `L` and the projection through the scalar multiplication.
    rw [map_smul L, map_smul (tensorChartComponentProjection (E := E) r s P₀.1 P₀.2),
      smul_eq_mul]
    -- Identify the projection of the `L`-image of the `Q`-th basis element with
    -- the transition coefficient, and the scalar with the raw `γ`-component.
    rw [show tensorChartComponentProjection (E := E) r s P₀.1 P₀.2
            (L (tensorChartBasisElement (E := E) r s Q.1 Q.2)) =
          transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q x from by
        rw [hL_def]; rfl]
    rw [tensorChartComponentRaw_def (I := I) (M := M) g r s S γ Q.1 Q.2]
    ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
