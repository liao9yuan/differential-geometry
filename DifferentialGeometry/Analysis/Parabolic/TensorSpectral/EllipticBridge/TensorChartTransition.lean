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
def transitionCoeff
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
lemma contMDiffOn_transitionCoeff
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

/-- **Tensor transformation law for raw chart-frame components, with explicit
coefficients.** For a smooth compactly-supported `(r, s)`-tensor section `S`,
two chart base points `γ` and `α`, and a component multi-index `P₀`, on the
overlap of the chart sources at `γ` and `α` the raw chart-frame component of `S`
in the chart at `α` equals the finite sum over component multi-indices `Q` of
`transitionCoeff r s γ α P₀ Q · (raw component of S in the chart at γ)`.

This is the transformation law with the coefficient family pinned down to the
explicit smooth transition coefficient `transitionCoeff`. -/
theorem tensorChartComponentRaw_eq_transitionCoeff_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (γ α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    {x : M} (hx : x ∈ (chartAt H γ).source ∩ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s S α P₀.1 P₀.2 x =
      ∑ Q : TensorCompIdx (E := E) r s,
        transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q x *
          tensorChartComponentRaw (I := I) (M := M) g r s S γ Q.1 Q.2 x := by
  classical
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
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
  refine ⟨transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀, ?_, ?_⟩
  · -- Smoothness of every coefficient.
    intro Q
    exact contMDiffOn_transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q
  · -- The pointwise decomposition on the chart overlap.
    intro x hx
    exact tensorChartComponentRaw_eq_transitionCoeff_sum
      (E := E) (I := I) (M := M) g r s S γ α P₀ hx

/-! ## Uniform op-norm bound on `transitionCoeff` over POU tsupport overlaps

For closed Riemannian manifolds the chart-atlas partition of unity has finite
nonempty support: there is a designated finite set `chartAtlasPOU_finset` of
chart base points outside which the partition-of-unity weight vanishes
identically. Each weight has compact closed support (`tsupport`) contained in
the corresponding chart source.

Restricting the smooth (hence continuous) function `transitionCoeff r s γ α P₀ Q`
to the closed-in-`M` set
`tsupport (POU γ) ∩ tsupport (POU α) ⊆ (chartAt H γ).source ∩ (chartAt H α).source`
yields a continuous function on a compact set, hence bounded. The component
multi-index pair `(P₀, Q)` ranges over the finite type `TensorCompIdx r s`
squared, and `(γ, α)` ranges over the finite product
`chartAtlasPOU_finset × chartAtlasPOU_finset` (for pairs outside this product
the tsupport overlap is empty, so the bound is vacuous).

Taking the maximum over all these finite parameter choices produces a single
uniform constant `K ≥ 0` bounding `|transitionCoeff r s γ α P₀ Q b|` for every
`(γ, α, P₀, Q, b)` with `b` in the POU tsupport overlap. -/

section UniformBound

/-! ### A `transitionCoeff` overlap region is compact and chart-subordinate -/

/-- The intersection of two POU tsupports is a closed subset of the compact
manifold `M`, hence compact. -/
private lemma pouTsupport_inter_isCompact (γ α : M) :
    IsCompact
      (tsupport (fun x : M =>
          ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
        tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (pouTsupport_isCompact (I := I) (M := M) γ).inter_right
    (isClosed_tsupport _)

/-- The POU tsupport at `γ` is contained in the chart source at `γ`. -/
private lemma pouTsupport_subset_chartSource (γ : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H γ).source :=
  DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M γ

/-- The intersection of two POU tsupports is a subset of the chart-source
intersection that is the natural smoothness domain of `transitionCoeff`. -/
private lemma pouTsupport_inter_subset_chartSource_inter (γ α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H γ).source ∩ (chartAt H α).source := by
  intro x hx
  exact ⟨pouTsupport_subset_chartSource (I := I) (M := M) γ hx.1,
    pouTsupport_subset_chartSource (I := I) (M := M) α hx.2⟩

/-! ### Per-pair, per-`(P₀, Q)` bound from continuity on the compact overlap -/

/-- For each pair `(γ, α)` of chart base points and each component-index pair
`(P₀, Q)`, the absolute value of `transitionCoeff r s γ α P₀ Q` is bounded on
the (compact) POU tsupport intersection. The bound is non-negative. -/
private lemma exists_transitionCoeff_bound_on_pouTsupport_pair
    (r s : ℕ) (γ α : M) (P₀ Q : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        |transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q b| ≤ C := by
  classical
  -- Abbreviate the compact intersection.
  set K : Set M := tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_def
  -- Case split on whether `K` is empty.
  by_cases hK_empty : K = ∅
  · -- Empty case: any `C ≥ 0` works, take `C = 0`.
    refine ⟨0, le_refl 0, ?_⟩
    intro b hb
    rw [hK_empty] at hb
    exact absurd hb (Set.notMem_empty b)
  · -- Non-empty case: extract max on the compact set.
    have hK_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
    have hK_compact : IsCompact K :=
      pouTsupport_inter_isCompact (I := I) (M := M) γ α
    have hK_sub : K ⊆ (chartAt H γ).source ∩ (chartAt H α).source :=
      pouTsupport_inter_subset_chartSource_inter (I := I) (M := M) γ α
    -- `transitionCoeff r s γ α P₀ Q` is `ContinuousOn` on the chart-overlap.
    have h_cont_overlap : ContinuousOn
        (transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q)
        ((chartAt H γ).source ∩ (chartAt H α).source) :=
      (contMDiffOn_transitionCoeff (E := E) (I := I) (M := M)
        r s γ α P₀ Q).continuousOn
    -- Restrict to `K`.
    have h_cont_K : ContinuousOn
        (transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q) K :=
      h_cont_overlap.mono hK_sub
    -- Pass to `|·|`.
    have h_abs_cont_K : ContinuousOn
        (fun b => |transitionCoeff (E := E) (I := I) (M := M)
          r s γ α P₀ Q b|) K :=
      continuous_abs.comp_continuousOn h_cont_K
    -- Extract the maximizer.
    obtain ⟨b_max, _hb_max_mem, hb_max⟩ :=
      hK_compact.exists_isMaxOn hK_ne h_abs_cont_K
    set C₀ : ℝ := |transitionCoeff (E := E) (I := I) (M := M)
      r s γ α P₀ Q b_max| with hC₀_def
    have hC₀_nn : 0 ≤ C₀ := abs_nonneg _
    refine ⟨C₀, hC₀_nn, ?_⟩
    intro b hb
    exact hb_max hb

/-! ### Vanishing of `transitionCoeff` data outside `chartAtlasPOU_finset`

When `γ ∉ chartAtlasPOU_finset`, the partition-of-unity weight at `γ` is
identically zero, so its function support is empty and its tsupport (the
closure of an empty set) is empty. The tsupport intersection with any other
POU tsupport is then empty, so the bound predicate is vacuously satisfied. -/

private lemma chartAtlasPOU_tsupport_eq_empty_of_notMem_finset
    {γ : M} (hγ : γ ∉ chartAtlasPOU_finset (I := I) (M := M)) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = ∅ := by
  classical
  -- The function support is empty, since the function is identically zero.
  have h_supp_empty :
      Function.support (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = ∅ := by
    ext x
    simp only [Function.mem_support, ne_eq, Set.mem_empty_iff_false, iff_false,
      Decidable.not_not]
    exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_weight_zero_of_notMem
      (I := I) (M := M) hγ x
  -- The tsupport is the closure of the function support.
  unfold tsupport
  rw [h_supp_empty, closure_empty]

private lemma pouTsupport_inter_eq_empty_of_left_notMem_finset
    {γ : M} (hγ : γ ∉ chartAtlasPOU_finset (I := I) (M := M)) (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = ∅ := by
  rw [chartAtlasPOU_tsupport_eq_empty_of_notMem_finset
    (I := I) (M := M) hγ]
  exact Set.empty_inter _

private lemma pouTsupport_inter_eq_empty_of_right_notMem_finset
    (γ : M) {α : M} (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M)) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = ∅ := by
  rw [chartAtlasPOU_tsupport_eq_empty_of_notMem_finset
    (I := I) (M := M) hα]
  exact Set.inter_empty _

/-! ### Aggregation of the per-pair, per-`(P₀, Q)` bounds into a single
constant by finset induction

We package the bound as a plain existential: there exists a single `K : ℝ`
simultaneously bounding the absolute value of `transitionCoeff` over the
finite product of the quantified data, constructed inductively on the
chart-atlas POU finset using the per-`(γ, α)` joint bound. -/

/-- For a fixed pair `(γ, α)` and each component index `(P₀, Q)`, the per-pair
bound is a finite quantification on the (compact, hence bounded) POU-tsupport
intersection. Aggregating over the finite type `TensorCompIdx r s ×
TensorCompIdx r s` (handled by `Finset.induction_on` on the universe finset)
gives a single non-negative constant. -/
private lemma exists_transitionCoeff_bound_on_pouTsupport_joint_PQ
    (r s : ℕ) (γ α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ P₀ Q : TensorCompIdx (E := E) r s,
      ∀ b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        |transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q b| ≤ C := by
  classical
  -- Universal-over-`(P₀, Q)` form: induct on `Finset.univ`.
  -- The auxiliary claim: for a finset `T : Finset (TensorCompIdx × TensorCompIdx)`,
  -- there is a uniform `C` bounding all `(PQ ∈ T)` cases.
  suffices h_aux :
      ∀ T : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s),
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ PQ ∈ T,
          ∀ b ∈ tsupport (fun x : M =>
                ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
              tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
            |transitionCoeff (E := E) (I := I) (M := M)
              r s γ α PQ.1 PQ.2 b| ≤ C by
    obtain ⟨C, hC_nn, hC_le⟩ := h_aux
      (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
        TensorCompIdx (E := E) r s))
    refine ⟨C, hC_nn, ?_⟩
    intro P₀ Q b hb
    exact hC_le (P₀, Q) (Finset.mem_univ _) b hb
  -- Induction on `T`.
  intro T
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨0, le_refl 0, ?_⟩
    intro PQ hPQ
    exact absurd hPQ (Finset.notMem_empty _)
  | insert PQ T' _hPQ_notin ih =>
    obtain ⟨C_T, hC_T_nn, hC_T_le⟩ := ih
    obtain ⟨C_PQ, hC_PQ_nn, hC_PQ_le⟩ :=
      exists_transitionCoeff_bound_on_pouTsupport_pair
        (E := E) (I := I) (M := M) r s γ α PQ.1 PQ.2
    refine ⟨max C_T C_PQ, le_max_of_le_left hC_T_nn, ?_⟩
    intro QQ hQQ b hb
    rcases Finset.mem_insert.mp hQQ with heq | hin
    · -- `QQ = PQ`: use the new per-`(P₀, Q)` bound.
      subst heq
      exact le_trans (hC_PQ_le b hb) (le_max_right _ _)
    · -- `QQ ∈ T'`: use the inductive hypothesis.
      exact le_trans (hC_T_le QQ hin b hb) (le_max_left _ _)

/-- Existential form: there is a single non-negative constant `K` bounding
`|transitionCoeff r s γ α P₀ Q b|` simultaneously over all chart base points
`γ, α : M`, all component multi-indices `P₀, Q`, and all `b` in the POU
tsupport intersection at `(γ, α)`. Proved by induction on
`chartAtlasPOU_finset × chartAtlasPOU_finset`. -/
private lemma exists_transitionCoeff_uniform_bound_on_pouTsupport
    (r s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ γ α : M, ∀ P₀ Q : TensorCompIdx (E := E) r s, ∀ b : M,
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        |transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q b| ≤ K := by
  classical
  -- Auxiliary: induction on a finset `S` of chart-base-point pairs.
  suffices h_aux :
      ∀ S : Finset (M × M),
        ∃ K : ℝ, 0 ≤ K ∧
          ∀ γα ∈ S,
          ∀ P₀ Q : TensorCompIdx (E := E) r s, ∀ b : M,
            b ∈ tsupport (fun x : M =>
                ((chartAtlasPOU I M γα.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
              tsupport (fun x : M =>
                ((chartAtlasPOU I M γα.2 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
            |transitionCoeff (E := E) (I := I) (M := M)
              r s γα.1 γα.2 P₀ Q b| ≤ K by
    -- Take `S := chartAtlasPOU_finset × chartAtlasPOU_finset`.
    obtain ⟨K, hK_nn, hK_le⟩ := h_aux
      (chartAtlasPOU_finset (I := I) (M := M) ×ˢ
        chartAtlasPOU_finset (I := I) (M := M))
    refine ⟨K, hK_nn, ?_⟩
    intro γ α P₀ Q b hb
    -- Case split on the membership of `(γ, α)` in the product.
    by_cases hγ : γ ∈ chartAtlasPOU_finset (I := I) (M := M)
    · by_cases hα : α ∈ chartAtlasPOU_finset (I := I) (M := M)
      · -- Both in: apply `hK_le`.
        have hmem : (γ, α) ∈
            chartAtlasPOU_finset (I := I) (M := M) ×ˢ
              chartAtlasPOU_finset (I := I) (M := M) :=
          Finset.mem_product.mpr ⟨hγ, hα⟩
        exact hK_le (γ, α) hmem P₀ Q b hb
      · -- α not in: tsupport intersection is empty.
        have h_empty := pouTsupport_inter_eq_empty_of_right_notMem_finset
          (I := I) (M := M) γ hα
        rw [h_empty] at hb
        exact absurd hb (Set.notMem_empty b)
    · -- γ not in: tsupport intersection is empty.
      have h_empty := pouTsupport_inter_eq_empty_of_left_notMem_finset
        (I := I) (M := M) hγ α
      rw [h_empty] at hb
      exact absurd hb (Set.notMem_empty b)
  -- Induction on `S`.
  intro S
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨0, le_refl 0, ?_⟩
    intro γα hγα
    exact absurd hγα (Finset.notMem_empty _)
  | insert γα S' _hγα_notin ih =>
    obtain ⟨K_S, hK_S_nn, hK_S_le⟩ := ih
    obtain ⟨K_γα, hK_γα_nn, hK_γα_le⟩ :=
      exists_transitionCoeff_bound_on_pouTsupport_joint_PQ
        (E := E) (I := I) (M := M) r s γα.1 γα.2
    refine ⟨max K_S K_γα, le_max_of_le_left hK_S_nn, ?_⟩
    intro δβ hδβ P₀ Q b hb
    rcases Finset.mem_insert.mp hδβ with heq | hin
    · -- `δβ = γα`.
      subst heq
      exact le_trans (hK_γα_le P₀ Q b hb) (le_max_right _ _)
    · -- `δβ ∈ S'`.
      exact le_trans (hK_S_le δβ hin P₀ Q b hb) (le_max_left _ _)

/-- **Uniform op-norm bound on `transitionCoeff` over chart overlaps,
restricted to POU tsupport ranges.**

For a closed Riemannian manifold modelled on a finite-dimensional real
inner-product space, and fixed tensor ranks `(r, s)`, there exists a single
non-negative real constant `K` such that for every pair of chart base points
`γ, α : M`, every component multi-index pair `(P₀, Q) : TensorCompIdx r s ×
TensorCompIdx r s`, and every point `b : M` lying in the intersection of the
closed supports of the partition-of-unity weights `chartAtlasPOU γ` and
`chartAtlasPOU α`, the absolute value of `transitionCoeff r s γ α P₀ Q b` is
bounded by `K`.

The constant `K` depends only on the manifold, the metric-induced bundle
structure, and the ranks `(r, s)`. It does NOT depend on a chart-source
consistency hypothesis on the atlas, and it is uniform over all the
quantified data above.

For pairs `(γ, α)` outside the (finite) `chartAtlasPOU_finset` the relevant
POU tsupport intersection is empty (since the partition-of-unity weight at a
chart base point outside that finite set is identically zero), so the bound
is vacuously satisfied for those pairs; effectively the supremum is taken
over the finite product `chartAtlasPOU_finset × chartAtlasPOU_finset`. -/
theorem transitionCoeff_le_uniform_on_pouTsupport
    (r s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ γ α : M, ∀ P₀ Q : TensorCompIdx (E := E) r s, ∀ b : M,
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        |transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q b| ≤ K :=
  exists_transitionCoeff_uniform_bound_on_pouTsupport
    (E := E) (I := I) (M := M) r s

/-! ## Uniform op-norm bound on the chart-transition Fréchet derivative

The chart-transition map `extChartAt I α ∘ (extChartAt I γ).symm` is `C^∞` on
the open `E`-source `((extChartAt I γ).symm ≫ extChartAt I α).source`. Its
Fréchet derivative is therefore `ContinuousOn` on the same set, and its
operator norm is bounded on any compact subset.

For chart base points `γ, α` in the (finite) `chartAtlasPOU_finset` and points
`b : M` in `tsupport (POU γ) ∩ tsupport (POU α)`, the image
`extChartAt I γ '' (tsupport (POU γ) ∩ tsupport (POU α))` is a compact subset
of `((extChartAt I γ).symm ≫ extChartAt I α).source`. Taking the maximum of
the per-pair operator-norm bounds over the finite chart-pair product yields a
single uniform constant `K_jac ≥ 0`. For pairs outside the finite product the
POU tsupport intersection is empty, so the bound is vacuously satisfied. -/

/-- The `E`-source of the chart transition `(extChartAt I γ).symm ≫
extChartAt I α` is open in `E` for a boundaryless model. The source equals
`I '' ((chartAt H γ).symm ≫ₕ chartAt H α).source`, which under boundaryless
`I` (so `range I = univ`) equals `I.symm ⁻¹' ((chartAt H γ).symm ≫ₕ chartAt
H α).source`; the preimage is open by continuity of `I.symm` and openness of
the `OpenPartialHomeomorph` trans source. -/
private lemma isOpen_extCoordChange_source (γ α : M) :
    IsOpen (((extChartAt I γ).symm ≫ extChartAt I α).source) := by
  classical
  -- Rewrite the source via `ext_coord_change_source` and `I.image_eq`.
  rw [ext_coord_change_source (I := I) α γ, I.image_eq, I.range_eq_univ,
    Set.inter_univ]
  -- The remaining set is the preimage of an open set under continuous `I.symm`.
  exact ((chartAt H γ).symm ≫ₕ chartAt H α).open_source.preimage I.continuous_symm

/-- The image of `tsupport (POU γ) ∩ tsupport (POU α)` under `extChartAt I γ`
is compact in `E`. Continuous image (`extChartAt I γ` is continuous on
`(chartAt H γ).source`) of a compact set; the POU tsupport intersection is
compact and contained in `(chartAt H γ).source`. -/
private lemma pouTsupport_inter_image_extChartAt_isCompact (γ α : M) :
    IsCompact
      ((extChartAt I γ) '' (tsupport (fun x : M =>
          ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
        tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))) := by
  classical
  have hK_compact : IsCompact (tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    pouTsupport_inter_isCompact (I := I) (M := M) γ α
  have h_cont : ContinuousOn (extChartAt I γ) (chartAt H γ).source := by
    have h := continuousOn_extChartAt (I := I) γ
    rw [extChartAt_source (I := I)] at h
    exact h
  have hK_sub : tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H γ).source := fun x hx =>
    pouTsupport_subset_chartSource (I := I) (M := M) γ hx.1
  exact hK_compact.image_of_continuousOn (h_cont.mono hK_sub)

/-- For `b ∈ (chartAt H γ).source ∩ (chartAt H α).source`, the point
`extChartAt I γ b` lies in `((extChartAt I γ).symm ≫ extChartAt I α).source`.
This is the image identity `extend_image_source_inter` rewritten via
`I.extendCoordChange_source`. -/
private lemma extChartAt_mem_extCoordChange_source
    {γ α : M} {b : M}
    (hbγ : b ∈ (chartAt H γ).source) (hbα : b ∈ (chartAt H α).source) :
    extChartAt I γ b ∈ ((extChartAt I γ).symm ≫ extChartAt I α).source := by
  classical
  -- The image identity:
  -- (chartAt H γ).extend I '' ((chartAt H γ).source ∩ (chartAt H α).source)
  --   = (I.extendCoordChange (chartAt H γ) (chartAt H α)).source.
  have h_img := OpenPartialHomeomorph.extend_image_source_inter
    (I := I) (f := chartAt H γ) (f' := chartAt H α)
  -- The trans `(extChartAt I γ).symm ≫ extChartAt I α` is by definition
  -- `I.extendCoordChange (chartAt H γ) (chartAt H α)` (both unfold to
  -- `((chartAt H γ).extend I).symm ≫ (chartAt H α).extend I`).
  change extChartAt I γ b ∈ (I.extendCoordChange (chartAt H γ) (chartAt H α)).source
  rw [← h_img]
  exact ⟨b, ⟨hbγ, hbα⟩, rfl⟩

/-- The image of `tsupport (POU γ) ∩ tsupport (POU α)` under `extChartAt I γ`
is contained in `((extChartAt I γ).symm ≫ extChartAt I α).source`. -/
private lemma pouTsupport_inter_image_subset_extCoordChange_source
    (γ α : M) :
    (extChartAt I γ) '' (tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) ⊆
      ((extChartAt I γ).symm ≫ extChartAt I α).source := by
  classical
  rintro z ⟨b, hb, rfl⟩
  have hb_inter : b ∈ (chartAt H γ).source ∩ (chartAt H α).source :=
    pouTsupport_inter_subset_chartSource_inter (I := I) (M := M) γ α hb
  exact extChartAt_mem_extCoordChange_source
    (I := I) (M := M) hb_inter.1 hb_inter.2

/-! ### Per-pair bound: continuous Fréchet derivative on a compact image -/

/-- For each pair `(γ, α)` of chart base points, the operator norm of the
Fréchet derivative `fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm)` at the
point `extChartAt I γ b`, with `b` in the POU tsupport intersection, is
bounded by a non-negative constant `C_{γ,α}`. The argument: the chart
transition is `ContDiffOn ℝ ∞` on the open source, hence its Fréchet
derivative is `ContinuousOn`; the operator norm is continuous; the image of
the (compact) POU tsupport intersection under `extChartAt I γ` is compact
and contained in the open source; bounded continuous functions on compact
sets achieve their maxima. -/
private lemma exists_fderiv_chartTransition_bound_on_pouTsupport_pair
    (γ α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        ‖fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm)
            (extChartAt I γ b)‖ ≤ C := by
  classical
  -- The chart-transition source in `E`.
  set U : Set E := ((extChartAt I γ).symm ≫ extChartAt I α).source with hU_def
  have hU_open : IsOpen U :=
    isOpen_extCoordChange_source (I := I) (M := M) γ α
  -- Smoothness of the chart transition on `U`.
  have h_contDiff : ContDiffOn ℝ ∞
      (extChartAt I α ∘ (extChartAt I γ).symm) U :=
    contDiffOn_ext_coord_change (I := I) (n := ∞) α γ
  -- Continuity of `fderiv` on `U`.
  have h_one_le : (1 : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (by decide : (1 : ℕ∞) ≤ ⊤)
  have h_cont_fderiv : ContinuousOn
      (fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm)) U :=
    h_contDiff.continuousOn_fderiv_of_isOpen hU_open h_one_le
  -- Continuity of the operator norm composed with `fderiv` on `U`.
  have h_cont_norm : ContinuousOn
      (fun y : E => ‖fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm) y‖) U :=
    continuous_norm.comp_continuousOn h_cont_fderiv
  -- The image `K_E` of the POU tsupport intersection.
  set K_E : Set E := (extChartAt I γ) '' (tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) with hKE_def
  have hKE_compact : IsCompact K_E :=
    pouTsupport_inter_image_extChartAt_isCompact (I := I) (M := M) γ α
  have hKE_subset_U : K_E ⊆ U :=
    pouTsupport_inter_image_subset_extCoordChange_source (I := I) (M := M) γ α
  -- Case split on whether `K_E` is empty.
  by_cases hKE_empty : K_E = ∅
  · -- Empty case: every `C ≥ 0` works, take `C = 0`.
    refine ⟨0, le_refl 0, ?_⟩
    intro b hb
    -- Reach a contradiction: `extChartAt I γ b ∈ K_E = ∅`.
    have h_mem : extChartAt I γ b ∈ K_E := ⟨b, hb, rfl⟩
    rw [hKE_empty] at h_mem
    exact absurd h_mem (Set.notMem_empty _)
  · -- Non-empty case: take the maximum on `K_E`.
    have hKE_ne : K_E.Nonempty := Set.nonempty_iff_ne_empty.mpr hKE_empty
    have h_cont_norm_KE : ContinuousOn
        (fun y : E => ‖fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm) y‖)
        K_E := h_cont_norm.mono hKE_subset_U
    obtain ⟨y_max, _hy_mem, hy_max⟩ :=
      hKE_compact.exists_isMaxOn hKE_ne h_cont_norm_KE
    set C₀ : ℝ := ‖fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm) y_max‖
      with hC₀_def
    have hC₀_nn : 0 ≤ C₀ := norm_nonneg _
    refine ⟨C₀, hC₀_nn, ?_⟩
    intro b hb
    have h_mem : extChartAt I γ b ∈ K_E := ⟨b, hb, rfl⟩
    exact hy_max h_mem

/-! ### Aggregation: finset induction over `chartAtlasPOU_finset` pairs -/

/-- Existential form: there is a single non-negative constant `K_jac` bounding
`‖fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm) (extChartAt I γ b)‖`
simultaneously over all pairs `(γ, α)` of chart base points and all `b` in
the POU tsupport intersection at `(γ, α)`. Proved by induction on
`chartAtlasPOU_finset × chartAtlasPOU_finset`. -/
private lemma exists_fderiv_chartTransition_uniform_bound_on_pouTsupport :
    ∃ K_jac : ℝ, 0 ≤ K_jac ∧
      ∀ γ α : M, ∀ b : M,
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm)
            (extChartAt I γ b)‖ ≤ K_jac := by
  classical
  -- Auxiliary: induct on a finset `S` of chart-base-point pairs.
  suffices h_aux :
      ∀ S : Finset (M × M),
        ∃ K_jac : ℝ, 0 ≤ K_jac ∧
          ∀ γα ∈ S, ∀ b : M,
            b ∈ tsupport (fun x : M =>
                ((chartAtlasPOU I M γα.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
              tsupport (fun x : M =>
                ((chartAtlasPOU I M γα.2 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
            ‖fderiv ℝ (extChartAt I γα.2 ∘ (extChartAt I γα.1).symm)
                (extChartAt I γα.1 b)‖ ≤ K_jac by
    obtain ⟨K_jac, hK_nn, hK_le⟩ := h_aux
      (chartAtlasPOU_finset (I := I) (M := M) ×ˢ
        chartAtlasPOU_finset (I := I) (M := M))
    refine ⟨K_jac, hK_nn, ?_⟩
    intro γ α b hb
    by_cases hγ : γ ∈ chartAtlasPOU_finset (I := I) (M := M)
    · by_cases hα : α ∈ chartAtlasPOU_finset (I := I) (M := M)
      · have hmem : (γ, α) ∈
            chartAtlasPOU_finset (I := I) (M := M) ×ˢ
              chartAtlasPOU_finset (I := I) (M := M) :=
          Finset.mem_product.mpr ⟨hγ, hα⟩
        exact hK_le (γ, α) hmem b hb
      · have h_empty := pouTsupport_inter_eq_empty_of_right_notMem_finset
          (I := I) (M := M) γ hα
        rw [h_empty] at hb
        exact absurd hb (Set.notMem_empty b)
    · have h_empty := pouTsupport_inter_eq_empty_of_left_notMem_finset
        (I := I) (M := M) hγ α
      rw [h_empty] at hb
      exact absurd hb (Set.notMem_empty b)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨0, le_refl 0, ?_⟩
    intro γα hγα
    exact absurd hγα (Finset.notMem_empty _)
  | insert γα S' _hγα_notin ih =>
    obtain ⟨K_S, hK_S_nn, hK_S_le⟩ := ih
    obtain ⟨K_γα, hK_γα_nn, hK_γα_le⟩ :=
      exists_fderiv_chartTransition_bound_on_pouTsupport_pair
        (E := E) (I := I) (M := M) γα.1 γα.2
    refine ⟨max K_S K_γα, le_max_of_le_left hK_S_nn, ?_⟩
    intro δβ hδβ b hb
    rcases Finset.mem_insert.mp hδβ with heq | hin
    · subst heq
      exact le_trans (hK_γα_le b hb) (le_max_right _ _)
    · exact le_trans (hK_S_le δβ hin b hb) (le_max_left _ _)

/-- **Uniform op-norm bound on the chart-transition Fréchet derivative over
POU tsupport overlaps.**

For a closed Riemannian manifold modelled on a finite-dimensional real
inner-product space, there exists a single non-negative real constant
`K_jac` such that for every pair of chart base points `γ, α : M` and every
point `b : M` lying in the intersection of the closed supports of the
partition-of-unity weights `chartAtlasPOU γ` and `chartAtlasPOU α`, the
operator norm of the Fréchet derivative

  `fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm) (extChartAt I γ b)`

is bounded by `K_jac`. The constant `K_jac` depends only on the manifold.

For pairs `(γ, α)` outside the (finite) `chartAtlasPOU_finset` the relevant
POU tsupport intersection is empty (since the partition-of-unity weight at a
chart base point outside that finite set is identically zero), so the bound
is vacuously satisfied for those pairs; effectively the supremum is taken
over the finite product `chartAtlasPOU_finset × chartAtlasPOU_finset`.

Applying the theorem with `γ` and `α` swapped gives the analogous bound for
the inverse chart transition `extChartAt I γ ∘ (extChartAt I α).symm` at the
point `extChartAt I α b` (the POU tsupport intersection is symmetric in
`γ, α`). -/
theorem chartTransition_fderiv_le_uniform_on_pouTsupport :
    ∃ K_jac : ℝ, 0 ≤ K_jac ∧
      ∀ γ α : M, ∀ b : M,
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm)
            (extChartAt I γ b)‖ ≤ K_jac :=
  exists_fderiv_chartTransition_uniform_bound_on_pouTsupport
    (E := E) (I := I) (M := M)

end UniformBound

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

/-! ## Axiom audit -/

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.transitionCoeff_le_uniform_on_pouTsupport

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTransition_fderiv_le_uniform_on_pouTsupport
