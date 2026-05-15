import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.InducedMetric
import DifferentialGeometry.Geometry.Gradient
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Outward unit normal vector field on the boundary

Given a smooth Riemannian metric `g` on the tangent bundle of a smooth manifold
`M` modelled on `(E, H, I)` whose model with corners admits a smooth boundary
stratum (`[hI : HasSmoothBoundary E H I]`), this file constructs at each
boundary point `x : BoundaryManifold I M` a distinguished unit tangent vector

  `outwardNormal g x : TangentSpace I x.val`

with the following properties:

* It is `g`-orthogonal to every tangent vector of the boundary submanifold,
  i.e., to every vector in the image of the inclusion's differential
  `dincl x : boundaryE →L[ℝ] E`.
* It has unit `g`-length: `g.inner x.val (outwardNormal g x) (outwardNormal g x) = 1`.
* It points "outward" in the sense that, when read in the ambient chart at
  `x.val`, its `g`-inner product with the chart-coordinate "inward direction"
  is strictly negative.

## Construction

At a boundary point `x`, the inclusion's manifold derivative `dincl x` is a
continuous linear injection `boundaryE → E`. The image `range (dincl x)` is a
linear subspace of `E` of dimension `Module.finrank ℝ boundaryE`. Its
`g`-orthogonal complement in `E` is denoted `normalSubspace g x`; this is the
locus of `g`-perpendicular tangent vectors to the boundary.

To select the outward direction, we use the structural "inward direction"
field of `HasSmoothBoundary`, namely `hI.inwardCoordE : E`. For the canonical
`EuclideanHalfSpace n` model, this is the standard basis vector
`EuclideanSpace.single 0 1`. Codimension-one transversality of this direction
to the boundary tangent space is part of the typeclass data
(`HasSmoothBoundary.inwardCoordE_transverse`); the bundle-level corollary
`InwardCoordTransverse_of_HasSmoothBoundary` therefore needs no further
hypothesis.

The `g`-orthogonal projection of `-inwardCoord g x` onto the normal subspace
gives an unnormalised outward vector `outwardDir g x`, and `outwardNormal g x`
is its unit `g`-normalisation.

## Main definitions

* `inwardCoordE` — the chart-coordinate "inward direction" in `E`.
* `inwardCoord g x` — its chart-pull-back to `TangentSpace I x.val`.
* `normalSubspace g x` — the `g`-orthogonal complement of `range (dincl x)`.
* `outwardDir g x` — an unnormalised outward vector in `normalSubspace g x`.
* `outwardNormal g x` — the unit-`g`-length outward normal.

## Main results

* `outwardNormal_mem_normalSubspace` — `outwardNormal g x` lies in the
  `g`-orthogonal complement of the boundary tangent space.
* `outwardNormal_orthogonal_to_boundary` — `g`-orthogonality to all boundary
  tangent vectors.
* `outwardNormal_norm_one` — unit `g`-length.
* `outwardNormal_inner_inwardCoord_neg` — strict negativity of the
  `g`-inner product with the chart-coordinate inward direction.
* `InwardCoordTransverse_of_HasSmoothBoundary` — transversality is automatic
  from the typeclass; no separate hypothesis needed at use sites.
-/

noncomputable section

open Set Function Topology Bundle Manifold MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

/-! ## Chart-coordinate inward direction in `E`

The model-side "inward direction" is supplied as a structural field of
`HasSmoothBoundary`, together with the codimension-one transversality
condition `inwardCoordE_transverse`. For the canonical `EuclideanHalfSpace n`
instance, this is the standard basis vector `e_0 = EuclideanSpace.single 0 1`.
-/

/-- The chart-coordinate "inward direction" in the model normed space `E`,
read from the typeclass field `HasSmoothBoundary.inwardCoordE`. -/
abbrev inwardCoordE : E := hI.inwardCoordE

/-! ## Chart-local representation of the boundary inclusion

To bridge the model-level transversality assumption (`inwardCoordE_transverse`)
to the bundle-level version (`InwardCoordTransverse`), we re-derive the
chart-local computation `dincl x = fderiv ℝ Φ (chart-point of x)` here, using
public infrastructure from `BoundaryManifold` / `InducedMetric`. -/

/-- The chart-local representation of the boundary inclusion
`Φ := I ∘ inclH ∘ boundaryI.symm : boundaryE → E`. -/
private def PhiLocal (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I] :
    hI.boundaryE → E :=
  (I : H → E) ∘ hI.inclH ∘ hI.boundaryI.symm

private lemma PhiLocal_eq (I : ModelWithCorners ℝ E H)
    [hI : HasSmoothBoundary E H I] :
    PhiLocal I = (I : H → E) ∘ hI.inclH ∘ hI.boundaryI.symm := rfl

private lemma infty_ne_zero_withTopENat' : (∞ : WithTop ℕ∞) ≠ 0 := by
  intro h
  have h' : ((⊤ : ℕ∞) : WithTop ℕ∞) = ((0 : ℕ∞) : WithTop ℕ∞) := h
  exact ENat.top_ne_zero (WithTop.coe_eq_coe.mp h')

/-- Computation of the boundary inclusion's manifold derivative in coordinates.
In the boundary chart at `x` and ambient chart at `x.val`, the chart-local
representation is `PhiLocal`, so the manifold derivative agrees with the
Fréchet derivative of `PhiLocal` at the chart point of `x`. -/
private lemma dincl_eq_fderiv_PhiLocal (x : BoundaryManifold I M)
    [Nonempty hI.boundaryH] :
    (dincl x : hI.boundaryE →L[ℝ] E) =
      fderiv ℝ (PhiLocal I) (extChartAt hI.boundaryI x x) := by
  unfold dincl
  have h_diff : MDifferentiableAt hI.boundaryI I (boundaryInclusion I M) x :=
    (boundaryInclusion_contMDiff (I := I) (M := M)).mdifferentiableAt
      infty_ne_zero_withTopENat'
  rw [h_diff.mfderiv]
  have h_range : Set.range hI.boundaryI = Set.univ := hI.boundaryI.range_eq_univ
  rw [h_range, fderivWithin_univ]
  have h_chart_eq :
      chartAt hI.boundaryH x = BoundaryManifold.boundaryChart (I := I) x := by
    change BoundaryManifold.defaultBoundaryChart (I := I) x =
      BoundaryManifold.boundaryChart (I := I) x
    exact BoundaryManifold.defaultBoundaryChart_eq_boundaryChart (I := I) x
  have h_eq : (writtenInExtChartAt hI.boundaryI I x (boundaryInclusion I M))
      =ᶠ[𝓝 (extChartAt hI.boundaryI x x)] PhiLocal I := by
    have h_target_mem : (extChartAt hI.boundaryI x).target ∈
        𝓝 (extChartAt hI.boundaryI x x) :=
      extChartAt_target_mem_nhds (I := hI.boundaryI) (M := BoundaryManifold I M) x
    filter_upwards [h_target_mem] with e he
    have he_target_chart : hI.boundaryI.symm e ∈ (chartAt hI.boundaryH x).target := by
      rw [extChartAt_target] at he
      exact he.1
    rw [h_chart_eq] at he_target_chart
    have h_extChart_symm_val :
        (((extChartAt hI.boundaryI x).symm e : BoundaryManifold I M) : M) =
          (chartAt H (x : M)).symm (hI.inclH (hI.boundaryI.symm e)) := by
      change (((chartAt hI.boundaryH x).symm (hI.boundaryI.symm e) :
          BoundaryManifold I M) : M) = _
      rw [h_chart_eq]
      exact BoundaryManifold.boundaryChartInvFun_val_of_mem_target
        (I := I) x he_target_chart
    change writtenInExtChartAt hI.boundaryI I x (boundaryInclusion I M) e =
      PhiLocal I e
    unfold writtenInExtChartAt
    simp only [Function.comp_apply]
    change extChartAt I (boundaryInclusion I M x)
        (((extChartAt hI.boundaryI x).symm e : BoundaryManifold I M) : M) =
      PhiLocal I e
    rw [h_extChart_symm_val]
    change I (chartAt H (x : M) ((chartAt H (x : M)).symm
      (hI.inclH (hI.boundaryI.symm e)))) = PhiLocal I e
    rw [(chartAt H (x : M)).right_inv he_target_chart]
    rfl
  rw [Filter.EventuallyEq.fderiv_eq h_eq]

/-! ## The chart-pulled-back inward direction in the tangent space

The tangent space at `x.val ∈ M` is identified with `E` via the trivialisation
of the tangent bundle at `x.val`. The chart-pulled-back inward direction is
the image of `inwardCoordE : E` under this trivialisation. We use
`(trivializationAt E (TangentSpace I) x.val).symm x.val` to obtain a vector
in `TangentSpace I x.val`. -/

/-- The chart-pulled-back inward direction at a boundary point: the image of
the chart-coordinate inward direction under the (inverse) trivialisation of
the ambient tangent bundle at `x.val`. -/
def inwardCoord (x : BoundaryManifold I M) : TangentSpace I (x : M) :=
  (trivializationAt E (TangentSpace I) (x : M)).symm (x : M) hI.inwardCoordE

/-- At the basepoint, the inward-direction trivialisation is the identity:
`inwardCoord x = inwardCoordE` under the type alias `TangentSpace I (x : M) = E`.

The proof uses that the inverse trivialisation of the tangent bundle at the
basepoint is `mfderivWithin 𝓘(ℝ, E) I (extChartAt I _).symm (range I) _`, which
equals the identity by `mfderivWithin_range_extChartAt_symm`. -/
lemma inwardCoord_eq (x : BoundaryManifold I M) :
    inwardCoord (M := M) x = hI.inwardCoordE := by
  -- `inwardCoord x = symmL ℝ (x : M) inwardCoordE` (using `symmL_apply`).
  have h_symmL : inwardCoord (M := M) x =
      ((trivializationAt E (TangentSpace I) (x : M)).symmL ℝ (x : M)) hI.inwardCoordE := rfl
  rw [h_symmL,
      TangentBundle.symmL_trivializationAt
        (x₀ := (x : M)) (x := (x : M)) (mem_chart_source H _),
      mfderivWithin_range_extChartAt_symm]
  rfl

/-! ## The chart-localised inward direction (parameterised by a base boundary point)

The function `inwardCoord` uses, at each boundary point `x`, the trivialisation
of the tangent bundle at `x.val` itself. This makes the basepoint of the
trivialisation vary with `x`, which obstructs smooth dependence on `x`.

To recover smooth dependence we introduce `inwardCoordAt α₀ x`, which uses the
trivialisation centred at a *fixed* base point `α₀ : BoundaryManifold I M`.
This is the analogue of the "frame field" `chartBasisVecFiber` from
`Integral/Measure/ChartDensity.lean`: as a function of `x` (with `α₀` fixed),
it is the section of the ambient tangent bundle obtained by transporting
`inwardCoordE : E` through the inverse trivialisation of the ambient tangent
bundle centred at `α₀.val`.

For `x` in the trivialisation base set of `α₀.val`, this section is smooth
in `x` (the basepoint of the trivialisation is fixed). At the special case
`α₀ = x`, it reduces to the original `inwardCoord x`. -/

/-- The chart-localised inward direction parameterised by a fixed base
boundary point `α₀`: the image of `inwardCoordE : E` under the inverse
trivialisation of the ambient tangent bundle centred at `α₀.val`, evaluated
at `x.val`. -/
def inwardCoordAt (α₀ : BoundaryManifold I M) (x : BoundaryManifold I M) :
    TangentSpace I (x : M) :=
  (trivializationAt E (TangentSpace I) (α₀ : M)).symm (x : M) hI.inwardCoordE

/-- At `α₀ = x`, the parameterised version coincides with the original
`inwardCoord x`. -/
@[simp] lemma inwardCoordAt_self (x : BoundaryManifold I M) :
    inwardCoordAt (M := M) x x = inwardCoord (M := M) x := rfl

/-! ## The `g`-orthogonal complement of the boundary tangent space

For each boundary point `x`, the boundary tangent space `range (dincl x)` is a
linear subspace of `TangentSpace I x.val`. Its `g`-orthogonal complement
inside `TangentSpace I x.val` is `normalSubspace g x`, characterised as the
set of vectors `v` with `g.inner x.val v w = 0` for every `w ∈ range (dincl x)`.

Recall that `TangentSpace I x.val := E` is a type alias, so the underlying
type for the submodule is `E`. -/

/-- The `g`-orthogonal complement of the boundary tangent space, as a
submodule of `TangentSpace I x.val`. A vector `v` lies in this submodule iff
`g.inner x.val v (dincl x w) = 0` for every `w : boundaryE`. -/
def normalSubspace (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    Submodule ℝ (TangentSpace I (x : M)) where
  carrier := {v : TangentSpace I (x : M) | ∀ w : hI.boundaryE,
    g.inner (x : M) v (dincl (M := M) x w) = 0}
  zero_mem' := by
    intro w
    simp
  add_mem' := by
    intro v₁ v₂ h₁ h₂ w
    -- `g.inner x (v₁ + v₂) (dincl x w) = g.inner x v₁ (dincl x w) + g.inner x v₂ (dincl x w)`.
    rw [map_add, ContinuousLinearMap.add_apply, h₁ w, h₂ w, add_zero]
  smul_mem' := by
    intro c v hv w
    -- `g.inner x (c • v) (dincl x w) = c * g.inner x v (dincl x w)`.
    rw [map_smul, ContinuousLinearMap.smul_apply, hv w, smul_zero]

@[simp] lemma mem_normalSubspace_iff
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v : TangentSpace I (x : M)) :
    v ∈ normalSubspace (M := M) g x ↔
      ∀ w : hI.boundaryE, g.inner (x : M) v (dincl (M := M) x w) = 0 :=
  Iff.rfl

/-- A boundary tangent vector `dincl x w` is `g`-orthogonal to every vector in
`normalSubspace g x` (by definition). -/
lemma inner_normalSubspace_dincl
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    {v : TangentSpace I (x : M)} (hv : v ∈ normalSubspace (M := M) g x)
    (w : hI.boundaryE) :
    g.inner (x : M) v (dincl (M := M) x w) = 0 := hv w

/-- Symmetric form: a vector in the normal subspace, with the metric applied
to a boundary tangent vector first. -/
lemma inner_dincl_normalSubspace
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    {v : TangentSpace I (x : M)} (hv : v ∈ normalSubspace (M := M) g x)
    (w : hI.boundaryE) :
    g.inner (x : M) (dincl (M := M) x w) v = 0 := by
  rw [g.symm (x : M) _ v]; exact hv w

/-! ## The dual covector at a boundary point

We construct a covector on `TangentSpace I x.val` that vanishes on
`range (dincl x)`, by composing the boundary inclusion's differential with a
suitable linear functional. This is built from the inner product `g`,
restricted to the boundary tangent space and "subtracted off" from the
inward direction.

The basic idea: the linear functional `w ↦ g.inner x.val (inwardCoord g x) (dincl x w)`
is a linear map `boundaryE → ℝ`. Pulled back through `dincl x` (which is
`boundaryE`-into-`E`) it produces nothing useful directly. Instead we use the
inverse `induced metric` flat: for each `w : boundaryE`, the bilinear form
`(boundaryE × boundaryE) → ℝ` given by the induced metric is non-degenerate, so
the linear functional `w ↦ g.inner x.val (inwardCoord g x) (dincl x w)` is the
flat-image of a unique vector `boundaryComponentOfInwardCoord` in `boundaryE`.

We then form `tangentialPart := dincl x boundaryComponentOfInwardCoord` (in
`TangentSpace I x.val`) and define `outwardDir := tangentialPart - inwardCoord g x`.
This vector lies in `normalSubspace g x`: by construction, for every `w : boundaryE`,

  `g.inner x.val outwardDir (dincl x w)`
    `= g.inner x.val tangentialPart (dincl x w) - g.inner x.val (inwardCoord g x) (dincl x w)`
    `= inducedMetric (boundaryComponentOfInwardCoord) w - g.inner x.val (inwardCoord g x) (dincl x w)`
    `= 0`.

Furthermore, `outwardDir` has strictly negative `g`-inner product with
`inwardCoord g x`, provided `inwardCoord g x ∉ range (dincl x)` (which is
the geometric "transversality" condition).
-/

variable (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)

/-- The boundary linear functional induced by the inward direction:
`w ↦ g.inner x.val (inwardCoord g x) (dincl x w)`. This is a linear map from
`boundaryE` to `ℝ`. -/
def boundaryFunOfInward : hI.boundaryE →ₗ[ℝ] ℝ where
  toFun w := g.inner (x : M) (inwardCoord (M := M) x) (dincl (M := M) x w)
  map_add' u v := by
    -- `dincl x (u + v) = dincl x u + dincl x v` (CLM), then `g.inner x v` is a CLM, so map_add.
    rw [ContinuousLinearMap.map_add (dincl (M := M) x) u v]
    exact ContinuousLinearMap.map_add (g.inner (x : M) (inwardCoord (M := M) x)) _ _
  map_smul' c v := by
    -- `dincl x (c • v) = c • dincl x v`, then `g.inner x v` map_smul.
    rw [ContinuousLinearMap.map_smul (dincl (M := M) x) c v]
    exact ContinuousLinearMap.map_smul (g.inner (x : M) (inwardCoord (M := M) x)) _ _

@[simp] lemma boundaryFunOfInward_apply (w : hI.boundaryE) :
    boundaryFunOfInward (M := M) g x w =
      g.inner (x : M) (inwardCoord (M := M) x) (dincl (M := M) x w) := rfl

/-- The induced metric `inducedMetricInner g x` viewed as a continuous bilinear
form on `boundaryE`, in linear-map form. We unfold it through
`metricFlatLinear` of the boundary metric. -/
private def boundaryFlatLinear : hI.boundaryE →ₗ[ℝ] (hI.boundaryE →ₗ[ℝ] ℝ) where
  toFun u := (inducedMetricInner (M := M) g x u).toLinearMap
  map_add' u v := by
    ext w
    change inducedMetricInner (M := M) g x (u + v) w =
      inducedMetricInner (M := M) g x u w + inducedMetricInner (M := M) g x v w
    rw [map_add, ContinuousLinearMap.add_apply]
  map_smul' c v := by
    ext w
    change inducedMetricInner (M := M) g x (c • v) w =
      c • inducedMetricInner (M := M) g x v w
    rw [map_smul, ContinuousLinearMap.smul_apply]

@[simp] private lemma boundaryFlatLinear_apply (u v : hI.boundaryE) :
    boundaryFlatLinear (M := M) g x u v = inducedMetricInner (M := M) g x u v := rfl

/-- The boundary flat map is injective: the induced metric is positive-definite
on the boundary tangent space (already established in the induced metric
construction). -/
private lemma boundaryFlatLinear_injective :
    Function.Injective (boundaryFlatLinear (M := M) g x) := by
  intro u v hpoint
  -- From `boundaryFlatLinear u = boundaryFlatLinear v`, derive `u = v` using positive-definiteness.
  by_contra hne
  have huv_ne : u - v ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < inducedMetricInner (M := M) g x (u - v) (u - v) :=
    inducedMetricInner_pos (M := M) g x (u - v) huv_ne
  have hzero : ∀ z : hI.boundaryE, inducedMetricInner (M := M) g x (u - v) z = 0 := by
    intro z
    have h := congrArg (fun L : hI.boundaryE →ₗ[ℝ] ℝ => L z) hpoint
    simp only [boundaryFlatLinear_apply] at h
    have hsub : inducedMetricInner (M := M) g x (u - v) z =
        inducedMetricInner (M := M) g x u z - inducedMetricInner (M := M) g x v z := by
      rw [map_sub, ContinuousLinearMap.sub_apply]
    rw [hsub, sub_eq_zero]; exact h
  exact (lt_irrefl 0) (hzero (u - v) ▸ hpos)

/-- The boundary flat map's domain and codomain have equal finite dimension. -/
private lemma boundaryFlatLinear_finrank_eq :
    Module.finrank ℝ hI.boundaryE = Module.finrank ℝ (hI.boundaryE →ₗ[ℝ] ℝ) :=
  Subspace.dual_finrank_eq.symm

/-- The boundary flat linear equivalence
`boundaryE ≃ₗ[ℝ] (boundaryE →ₗ[ℝ] ℝ)` induced by the induced metric. -/
private def boundaryFlatMap : hI.boundaryE ≃ₗ[ℝ] (hI.boundaryE →ₗ[ℝ] ℝ) :=
  LinearMap.linearEquivOfInjective
    (boundaryFlatLinear (M := M) g x)
    (boundaryFlatLinear_injective (M := M) g x)
    (boundaryFlatLinear_finrank_eq (E := E) (H := H) (I := I))

@[simp] private lemma boundaryFlatMap_apply (u v : hI.boundaryE) :
    boundaryFlatMap (M := M) g x u v = inducedMetricInner (M := M) g x u v := rfl

/-- The defining identity for the boundary sharp: the unique `u : boundaryE`
such that the induced metric pairs `u` with every `w` to recover the value of
the given linear functional. -/
private lemma boundaryFlatMap_apply_symm
    (α : hI.boundaryE →ₗ[ℝ] ℝ) (w : hI.boundaryE) :
    inducedMetricInner (M := M) g x ((boundaryFlatMap (M := M) g x).symm α) w = α w := by
  have h := (boundaryFlatMap (M := M) g x).apply_symm_apply α
  have hh : boundaryFlatMap (M := M) g x ((boundaryFlatMap (M := M) g x).symm α) w = α w :=
    congrArg (fun L : hI.boundaryE →ₗ[ℝ] ℝ => L w) h
  rw [boundaryFlatMap_apply] at hh
  exact hh

/-- The unique boundary vector whose induced-metric pairing recovers the
boundary linear functional `boundaryFunOfInward`. -/
def boundaryComponentOfInward : hI.boundaryE :=
  (boundaryFlatMap (M := M) g x).symm (boundaryFunOfInward (M := M) g x)

/-- Defining identity for the boundary component of the inward direction:
the induced metric of `boundaryComponentOfInward` against any `w` equals
`g.inner x.val (inwardCoord g x) (dincl x w)`. -/
lemma inducedMetricInner_boundaryComponentOfInward (w : hI.boundaryE) :
    inducedMetricInner (M := M) g x (boundaryComponentOfInward (M := M) g x) w =
      g.inner (x : M) (inwardCoord (M := M) x) (dincl (M := M) x w) := by
  unfold boundaryComponentOfInward
  have := boundaryFlatMap_apply_symm (M := M) g x (boundaryFunOfInward (M := M) g x) w
  rw [this]
  rfl

/-- The "tangential part" of `inwardCoord g x`: the image of
`boundaryComponentOfInward` in `TangentSpace I x.val`, lying in
`range (dincl x)`. -/
def inwardTangentialPart : TangentSpace I (x : M) :=
  dincl (M := M) x (boundaryComponentOfInward (M := M) g x)

@[simp] lemma inwardTangentialPart_def :
    inwardTangentialPart (M := M) g x =
      dincl (M := M) x (boundaryComponentOfInward (M := M) g x) := rfl

/-- The unnormalised outward vector: `tangentialPart - inwardCoord`. By
construction, this lies in the `g`-orthogonal complement of `range (dincl x)`
(see `outwardDir_mem_normalSubspace`). -/
def outwardDir : TangentSpace I (x : M) :=
  inwardTangentialPart (M := M) g x - inwardCoord (M := M) x

@[simp] lemma outwardDir_def :
    outwardDir (M := M) g x =
      inwardTangentialPart (M := M) g x - inwardCoord (M := M) x := rfl

/-- The unnormalised outward vector lies in the `g`-orthogonal complement of
`range (dincl x)`, by the defining identity for the boundary component of
the inward direction. -/
theorem outwardDir_mem_normalSubspace :
    outwardDir (M := M) g x ∈ normalSubspace (M := M) g x := by
  intro w
  -- Goal: `g.inner x.val (tangentialPart - inwardCoord) (dincl x w) = 0`.
  rw [outwardDir_def]
  have hsub : g.inner (x : M)
        (inwardTangentialPart (M := M) g x - inwardCoord (M := M) x)
        (dincl (M := M) x w) =
      g.inner (x : M) (inwardTangentialPart (M := M) g x) (dincl (M := M) x w) -
      g.inner (x : M) (inwardCoord (M := M) x) (dincl (M := M) x w) := by
    rw [map_sub, ContinuousLinearMap.sub_apply]
  rw [hsub]
  -- The first term equals `inducedMetricInner ... w` by definition of induced metric.
  have h1 : g.inner (x : M) (inwardTangentialPart (M := M) g x) (dincl (M := M) x w) =
      inducedMetricInner (M := M) g x (boundaryComponentOfInward (M := M) g x) w := by
    rw [inducedMetricInner_apply, inwardTangentialPart_def]
  rw [h1]
  rw [inducedMetricInner_boundaryComponentOfInward (M := M) g x w]
  ring

/-- The `g`-inner product of `outwardDir` with `inwardCoord g x` is the
"deficit" between the squared `g`-norm of `inwardCoord` and the boundary-
projected component. This is non-positive, and we will show that under
suitable transversality it is strictly negative. -/
lemma g_inner_outwardDir_inwardCoord :
    g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x) =
      g.inner (x : M) (inwardTangentialPart (M := M) g x) (inwardCoord (M := M) x) -
      g.inner (x : M) (inwardCoord (M := M) x) (inwardCoord (M := M) x) := by
  rw [outwardDir_def, map_sub, ContinuousLinearMap.sub_apply]

/-- Symmetric form. -/
lemma g_inner_inwardCoord_outwardDir :
    g.inner (x : M) (inwardCoord (M := M) x) (outwardDir (M := M) g x) =
      g.inner (x : M) (inwardTangentialPart (M := M) g x) (inwardCoord (M := M) x) -
      g.inner (x : M) (inwardCoord (M := M) x) (inwardCoord (M := M) x) := by
  rw [g.symm (x : M) (inwardCoord (M := M) x) (outwardDir (M := M) g x)]
  exact g_inner_outwardDir_inwardCoord (M := M) g x

/-! ## The `g`-norm-squared identity for `outwardDir`

We need a closed-form expression for `g.inner x.val (outwardDir) (outwardDir)`
in terms of the inner products of `inwardCoord` and the tangential part. -/

/-- A direct calculation: `g(outwardDir, outwardDir) = g(inwardCoord, inwardCoord)
- g(tangentialPart, inwardCoord)`. We use that `outwardDir = tangentialPart -
inwardCoord` and the fact that `outwardDir ∈ normalSubspace`, so it is
`g`-orthogonal to `tangentialPart` (which lies in `range (dincl x)`). -/
lemma g_inner_outwardDir_outwardDir :
    g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) =
      g.inner (x : M) (inwardCoord (M := M) x) (inwardCoord (M := M) x) -
      g.inner (x : M) (inwardTangentialPart (M := M) g x) (inwardCoord (M := M) x) := by
  -- `g(outwardDir, outwardDir) = -g(outwardDir, inwardCoord)` since
  -- `outwardDir = tangentialPart - inwardCoord` and `g(outwardDir, tangentialPart) = 0`.
  have h_orth : g.inner (x : M) (outwardDir (M := M) g x)
      (inwardTangentialPart (M := M) g x) = 0 := by
    -- `tangentialPart = dincl x (boundaryComponentOfInward ...)` ∈ range (dincl x).
    have hmem : outwardDir (M := M) g x ∈ normalSubspace (M := M) g x :=
      outwardDir_mem_normalSubspace (M := M) g x
    rw [inwardTangentialPart_def]
    exact hmem (boundaryComponentOfInward (M := M) g x)
  -- Decompose the second factor: `outwardDir = tangentialPart - inwardCoord`,
  -- so `g(outwardDir, outwardDir) = g(outwardDir, tangentialPart) - g(outwardDir, inwardCoord)`.
  have hdecomp : g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) =
      g.inner (x : M) (outwardDir (M := M) g x) (inwardTangentialPart (M := M) g x) -
      g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x) := by
    -- The second `outwardDir g x` is definitionally `tangentialPart - inwardCoord`.
    -- `g.inner x v : E →L[ℝ] ℝ` is a CLM, so `map_sub` produces the result.
    change g.inner (x : M) (outwardDir (M := M) g x)
        (inwardTangentialPart (M := M) g x - inwardCoord (M := M) x) =
      g.inner (x : M) (outwardDir (M := M) g x) (inwardTangentialPart (M := M) g x) -
      g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x)
    exact ContinuousLinearMap.map_sub _ _ _
  rw [hdecomp, h_orth, zero_sub]
  -- Now: `-g(outwardDir, inwardCoord) = g(inwardCoord, inwardCoord) - g(tangentialPart, inwardCoord)`.
  rw [g_inner_outwardDir_inwardCoord (M := M) g x]
  ring

/-! ## Transversality and positivity

The key transversality condition is that `inwardCoord g x ∉ range (dincl x)`,
i.e., the chart-coordinate inward direction is not tangent to the boundary.
Under this condition, `outwardDir g x ≠ 0` and its `g`-norm is strictly
positive.

The transversality condition holds in particular when `Module.finrank ℝ E =
Module.finrank ℝ boundaryE + 1` (the canonical codimension-one setting): in
that case, `range (dincl x)` is a hyperplane and a generic vector (such as
`inwardCoordE`) is transverse to it.
-/

/-- **Transversality** (internal `def`): the chart-coordinate inward direction
is not in the image of the inclusion's differential. This is provided
automatically by the `HasSmoothBoundary` typeclass via
`InwardCoordTransverse_of_HasSmoothBoundary`; clients of the public API need
not supply it as a hypothesis. -/
def InwardCoordTransverse (x : BoundaryManifold I M) : Prop :=
  inwardCoord (M := M) x ∉ LinearMap.range (dincl (M := M) x).toLinearMap

/-- The chart-coordinate inward direction is transverse to the boundary at
every boundary point. This is the bundle-level instance of the model-level
codimension-one transversality field `HasSmoothBoundary.inwardCoordE_transverse`,
combined with the chart-local identification `dincl x = fderiv ℝ Φ (chart-point)`.
The hypothesis no longer needs to be supplied at every use site. -/
theorem InwardCoordTransverse_of_HasSmoothBoundary
    (x : BoundaryManifold I M) :
    InwardCoordTransverse (M := M) x := by
  by_cases hN : Nonempty hI.boundaryH
  · haveI := hN
    -- Goal: `inwardCoord x ∉ LinearMap.range (dincl x).toLinearMap`.
    -- `inwardCoord x = inwardCoordE` and
    -- `range (dincl x) = range (fderiv ℝ PhiLocal (extChartAt boundaryI x x))`.
    intro hmem
    have hmem' : inwardCoord (M := M) x ∈ Set.range (dincl (M := M) x) := by
      rcases hmem with ⟨w, hw⟩
      exact ⟨w, hw⟩
    rw [inwardCoord_eq, dincl_eq_fderiv_PhiLocal (I := I) (M := M) x] at hmem'
    -- Now `hmem' : hI.inwardCoordE ∈ Set.range (fderiv ℝ (PhiLocal I) ...)`.
    -- The typeclass field `inwardCoordE_transverse` says this is impossible.
    exact hI.inwardCoordE_transverse (extChartAt hI.boundaryI x x) hmem'
  · haveI : IsEmpty hI.boundaryH := not_nonempty_iff.mp hN
    haveI : IsEmpty (BoundaryManifold I M) :=
      BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
    exact (IsEmpty.false x).elim

/-- The outward unnormalised direction is non-zero. -/
theorem outwardDir_ne_zero :
    outwardDir (M := M) g x ≠ 0 := by
  intro h0
  -- If `outwardDir = 0`, then `inwardCoord = tangentialPart ∈ range (dincl x)`,
  -- contradicting transversality.
  have htr : InwardCoordTransverse (M := M) x :=
    InwardCoordTransverse_of_HasSmoothBoundary (M := M) x
  have h_eq : inwardCoord (M := M) x = inwardTangentialPart (M := M) g x := by
    have := h0
    rw [outwardDir_def, sub_eq_zero] at this
    exact this.symm
  apply htr
  rw [h_eq, inwardTangentialPart_def]
  exact ⟨boundaryComponentOfInward (M := M) g x, rfl⟩

/-- The `g`-norm-squared of `outwardDir` is strictly positive. -/
theorem g_inner_outwardDir_pos :
    0 < g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) :=
  g.pos (x : M) _ (outwardDir_ne_zero (M := M) g x)

/-- `outwardDir` has strictly negative `g`-inner product with
`inwardCoord g x`. -/
theorem g_inner_outwardDir_inwardCoord_neg :
    g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x) < 0 := by
  -- `g(outwardDir, inwardCoord) = -g(outwardDir, outwardDir) - g(tangentialPart, outwardDir).`
  -- More directly: `outwardDir = tangentialPart - inwardCoord`, so
  -- `g(outwardDir, inwardCoord) = g(tangentialPart, inwardCoord) - g(inwardCoord, inwardCoord)`.
  -- And `g(outwardDir, outwardDir) = g(inwardCoord, inwardCoord) - g(tangentialPart, inwardCoord)`,
  -- so `g(outwardDir, inwardCoord) = -g(outwardDir, outwardDir) < 0`.
  have hpos : 0 < g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) :=
    g_inner_outwardDir_pos (M := M) g x
  have h_id : g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x) =
      -g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) := by
    rw [g_inner_outwardDir_inwardCoord (M := M) g x,
        g_inner_outwardDir_outwardDir (M := M) g x]
    ring
  rw [h_id]
  linarith

/-! ## The unit-`g`-length outward normal

Under the transversality condition, we normalise `outwardDir` to obtain a
unit vector `outwardNormal`. -/

/-- The outward unit normal at a boundary point: the unit-`g`-length scaling
of `outwardDir`. The `0 < g(outwardDir, outwardDir)` discriminator is always
true (by `g_inner_outwardDir_pos`), but we keep the conditional form so that
the definition is total. -/
def outwardNormal : TangentSpace I (x : M) :=
  open scoped Classical in
  if _h : 0 < g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) then
    (Real.sqrt (g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x)))⁻¹ •
      outwardDir (M := M) g x
  else
    0

/-- The outward normal equals the unit-normalisation of `outwardDir`. -/
lemma outwardNormal_eq :
    outwardNormal (M := M) g x =
      (Real.sqrt (g.inner (x : M) (outwardDir (M := M) g x)
        (outwardDir (M := M) g x)))⁻¹ • outwardDir (M := M) g x := by
  unfold outwardNormal
  rw [dif_pos (g_inner_outwardDir_pos (M := M) g x)]

/-! ## Properties of the outward normal -/

/-- The outward normal lies in the normal subspace. -/
theorem outwardNormal_mem_normalSubspace :
    outwardNormal (M := M) g x ∈ normalSubspace (M := M) g x := by
  rw [outwardNormal_eq (M := M) g x]
  exact (normalSubspace (M := M) g x).smul_mem _
    (outwardDir_mem_normalSubspace (M := M) g x)

/-- The outward normal is `g`-orthogonal to every boundary tangent vector. -/
theorem outwardNormal_orthogonal_to_boundary (w : hI.boundaryE) :
    g.inner (x : M) (outwardNormal (M := M) g x) (dincl (M := M) x w) = 0 :=
  (outwardNormal_mem_normalSubspace (M := M) g x) w

/-- Symmetric form. -/
theorem inner_dincl_outwardNormal (w : hI.boundaryE) :
    g.inner (x : M) (dincl (M := M) x w) (outwardNormal (M := M) g x) = 0 := by
  rw [g.symm (x : M) _ (outwardNormal (M := M) g x)]
  exact outwardNormal_orthogonal_to_boundary (M := M) g x w

/-- The outward normal has unit `g`-length. -/
theorem outwardNormal_norm_one :
    g.inner (x : M) (outwardNormal (M := M) g x) (outwardNormal (M := M) g x) = 1 := by
  set q : ℝ := g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) with hq_def
  have hq_pos : 0 < q := g_inner_outwardDir_pos (M := M) g x
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hsq_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq_pos
  have hsq_ne : Real.sqrt q ≠ 0 := ne_of_gt hsq_pos
  have hsq_sq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq_pos.le
  rw [outwardNormal_eq (M := M) g x]
  -- Goal: `g.inner x ((sqrt q)⁻¹ • outwardDir) ((sqrt q)⁻¹ • outwardDir) = 1`.
  -- Step 1: extract `(sqrt q)⁻¹` from the first argument.
  have h1 : g.inner (x : M) ((Real.sqrt q)⁻¹ • outwardDir (M := M) g x)
          ((Real.sqrt q)⁻¹ • outwardDir (M := M) g x) =
      (Real.sqrt q)⁻¹ • (g.inner (x : M) (outwardDir (M := M) g x))
          ((Real.sqrt q)⁻¹ • outwardDir (M := M) g x) := by
    rw [show g.inner (x : M) ((Real.sqrt q)⁻¹ • outwardDir (M := M) g x) =
        (Real.sqrt q)⁻¹ • g.inner (x : M) (outwardDir (M := M) g x) from
          map_smul _ _ _]
    rfl
  rw [h1]
  -- Step 2: extract `(sqrt q)⁻¹` from the second argument.
  rw [show (g.inner (x : M) (outwardDir (M := M) g x))
        ((Real.sqrt q)⁻¹ • outwardDir (M := M) g x) =
      (Real.sqrt q)⁻¹ • g.inner (x : M) (outwardDir (M := M) g x)
        (outwardDir (M := M) g x) from
    ContinuousLinearMap.map_smul _ _ _]
  -- Step 3: simplify scalar multiplication.
  rw [show g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) = q from rfl]
  rw [smul_eq_mul, smul_eq_mul]
  -- Goal: `(sqrt q)⁻¹ * ((sqrt q)⁻¹ * q) = 1`.
  rw [show (Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) = q / (Real.sqrt q * Real.sqrt q) by
    field_simp]
  rw [hsq_sq]
  exact div_self hq_ne

/-- The outward normal points outward: its `g`-inner product with the
chart-coordinate inward direction `inwardCoord g x` is strictly negative. -/
theorem outwardNormal_inner_inwardCoord_neg :
    g.inner (x : M) (outwardNormal (M := M) g x) (inwardCoord (M := M) x) < 0 := by
  rw [outwardNormal_eq (M := M) g x]
  rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  -- Goal: `(sqrt q)⁻¹ * g(outwardDir, inwardCoord) < 0`.
  have hq_pos : 0 < g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) :=
    g_inner_outwardDir_pos (M := M) g x
  have hsq_pos : 0 < Real.sqrt
      (g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x)) :=
    Real.sqrt_pos.mpr hq_pos
  have hsq_inv_pos : 0 < (Real.sqrt
      (g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x)))⁻¹ :=
    inv_pos.mpr hsq_pos
  have hneg : g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x) < 0 :=
    g_inner_outwardDir_inwardCoord_neg (M := M) g x
  exact mul_neg_of_pos_of_neg hsq_inv_pos hneg

/-! ## Parameterised Gram–Schmidt construction with a fixed reference chart

The smoothness arguments for `outwardNormal` go through a parameterised
construction in which the reference inward direction is read in a *fixed*
trivialisation centred at a chosen base boundary point `α₀`. This decouples
the algebraic Gram–Schmidt step from the varying-basepoint trivialisation
used by `inwardCoord`, making smooth dependence on the variable point `x`
provable via the existing `chartBasisVec_contMDiffOn`-style infrastructure.

For each base point `α₀ : BoundaryManifold I M`:

* `inwardCoordAt α₀ x` is the image of `inwardCoordE : E` under the inverse
  trivialisation centred at `α₀.val`, evaluated at `x.val` (defined above).
* `boundaryFunOfInwardAt g α₀ x : boundaryE →ₗ[ℝ] ℝ` is the boundary linear
  functional `w ↦ g.inner x.val (inwardCoordAt α₀ x) (dincl x w)`.
* `boundaryComponentOfInwardAt g α₀ x : boundaryE` is the unique boundary
  vector whose induced-metric pairing recovers the boundary functional.
* `inwardTangentialPartAt g α₀ x : T_x M` is the inclusion-image of
  `boundaryComponentOfInwardAt g α₀ x`.
* `outwardDirAt g α₀ x : T_x M` is `inwardTangentialPartAt g α₀ x - inwardCoordAt α₀ x`.
* `outwardNormalAt g α₀ x : T_x M` is the unit-`g`-length scaling of
  `outwardDirAt g α₀ x`.

At `α₀ = x` each parameterised entity reduces to the original (basepoint-free)
version, so the parameterised construction subsumes the original. -/

/-- The boundary linear functional induced by `inwardCoordAt α₀ x`:
`w ↦ g.inner x.val (inwardCoordAt α₀ x) (dincl x w)`. -/
def boundaryFunOfInwardAt (g : SmoothRiemannianMetric I M)
    (α₀ x : BoundaryManifold I M) : hI.boundaryE →ₗ[ℝ] ℝ where
  toFun w := g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (dincl (M := M) x w)
  map_add' u v := by
    rw [ContinuousLinearMap.map_add (dincl (M := M) x) u v]
    exact ContinuousLinearMap.map_add
      (g.inner (x : M) (inwardCoordAt (M := M) α₀ x)) _ _
  map_smul' c v := by
    rw [ContinuousLinearMap.map_smul (dincl (M := M) x) c v]
    exact ContinuousLinearMap.map_smul
      (g.inner (x : M) (inwardCoordAt (M := M) α₀ x)) _ _

@[simp] lemma boundaryFunOfInwardAt_apply
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M)
    (w : hI.boundaryE) :
    boundaryFunOfInwardAt (M := M) g α₀ x w =
      g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (dincl (M := M) x w) := rfl

@[simp] lemma boundaryFunOfInwardAt_self
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    boundaryFunOfInwardAt (M := M) g x x = boundaryFunOfInward (M := M) g x := by
  ext w
  simp [boundaryFunOfInwardAt_apply, boundaryFunOfInward_apply,
    inwardCoordAt_self]

/-- The unique boundary vector whose induced-metric pairing recovers
`boundaryFunOfInwardAt α₀ x`. -/
def boundaryComponentOfInwardAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    hI.boundaryE :=
  (boundaryFlatMap (M := M) g x).symm (boundaryFunOfInwardAt (M := M) g α₀ x)

@[simp] lemma boundaryComponentOfInwardAt_self
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    boundaryComponentOfInwardAt (M := M) g x x =
      boundaryComponentOfInward (M := M) g x := by
  unfold boundaryComponentOfInwardAt boundaryComponentOfInward
  rw [boundaryFunOfInwardAt_self]

/-- Defining identity for the parameterised boundary component: induced metric
pairing recovers the boundary functional value. -/
lemma inducedMetricInner_boundaryComponentOfInwardAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M)
    (w : hI.boundaryE) :
    inducedMetricInner (M := M) g x (boundaryComponentOfInwardAt (M := M) g α₀ x) w =
      g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (dincl (M := M) x w) := by
  unfold boundaryComponentOfInwardAt
  have := boundaryFlatMap_apply_symm (M := M) g x
    (boundaryFunOfInwardAt (M := M) g α₀ x) w
  rw [this]
  rfl

/-- The "tangential part" of `inwardCoordAt α₀ x`: the image of
`boundaryComponentOfInwardAt α₀ x` in `T_x M`. -/
def inwardTangentialPartAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    TangentSpace I (x : M) :=
  dincl (M := M) x (boundaryComponentOfInwardAt (M := M) g α₀ x)

@[simp] lemma inwardTangentialPartAt_def
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    inwardTangentialPartAt (M := M) g α₀ x =
      dincl (M := M) x (boundaryComponentOfInwardAt (M := M) g α₀ x) := rfl

@[simp] lemma inwardTangentialPartAt_self
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    inwardTangentialPartAt (M := M) g x x = inwardTangentialPart (M := M) g x := by
  unfold inwardTangentialPartAt inwardTangentialPart
  rw [boundaryComponentOfInwardAt_self]

/-- The parameterised unnormalised outward direction:
`tangentialPart - inwardCoordAt α₀ x`. -/
def outwardDirAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    TangentSpace I (x : M) :=
  inwardTangentialPartAt (M := M) g α₀ x - inwardCoordAt (M := M) α₀ x

@[simp] lemma outwardDirAt_def
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    outwardDirAt (M := M) g α₀ x =
      inwardTangentialPartAt (M := M) g α₀ x - inwardCoordAt (M := M) α₀ x := rfl

@[simp] lemma outwardDirAt_self
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    outwardDirAt (M := M) g x x = outwardDir (M := M) g x := by
  unfold outwardDirAt outwardDir
  rw [inwardTangentialPartAt_self, inwardCoordAt_self]

/-- The parameterised unnormalised outward direction lies in the
`g`-orthogonal complement of `range (dincl x)`. -/
theorem outwardDirAt_mem_normalSubspace
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    outwardDirAt (M := M) g α₀ x ∈ normalSubspace (M := M) g x := by
  intro w
  rw [outwardDirAt_def]
  have hsub : g.inner (x : M)
        (inwardTangentialPartAt (M := M) g α₀ x - inwardCoordAt (M := M) α₀ x)
        (dincl (M := M) x w) =
      g.inner (x : M) (inwardTangentialPartAt (M := M) g α₀ x) (dincl (M := M) x w) -
      g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (dincl (M := M) x w) := by
    rw [map_sub, ContinuousLinearMap.sub_apply]
  rw [hsub]
  have h1 : g.inner (x : M) (inwardTangentialPartAt (M := M) g α₀ x) (dincl (M := M) x w) =
      inducedMetricInner (M := M) g x (boundaryComponentOfInwardAt (M := M) g α₀ x) w := by
    rw [inducedMetricInner_apply, inwardTangentialPartAt_def]
  rw [h1]
  rw [inducedMetricInner_boundaryComponentOfInwardAt (M := M) g α₀ x w]
  ring

/-- Parameterised analogue of `g_inner_outwardDir_inwardCoord`. -/
lemma g_inner_outwardDirAt_inwardCoordAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    g.inner (x : M) (outwardDirAt (M := M) g α₀ x) (inwardCoordAt (M := M) α₀ x) =
      g.inner (x : M) (inwardTangentialPartAt (M := M) g α₀ x)
        (inwardCoordAt (M := M) α₀ x) -
      g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (inwardCoordAt (M := M) α₀ x) := by
  rw [outwardDirAt_def, map_sub, ContinuousLinearMap.sub_apply]

/-- Parameterised analogue of `g_inner_outwardDir_outwardDir`. -/
lemma g_inner_outwardDirAt_outwardDirAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    g.inner (x : M) (outwardDirAt (M := M) g α₀ x) (outwardDirAt (M := M) g α₀ x) =
      g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (inwardCoordAt (M := M) α₀ x) -
      g.inner (x : M) (inwardTangentialPartAt (M := M) g α₀ x)
        (inwardCoordAt (M := M) α₀ x) := by
  have h_orth : g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
      (inwardTangentialPartAt (M := M) g α₀ x) = 0 := by
    have hmem : outwardDirAt (M := M) g α₀ x ∈ normalSubspace (M := M) g x :=
      outwardDirAt_mem_normalSubspace (M := M) g α₀ x
    rw [inwardTangentialPartAt_def]
    exact hmem (boundaryComponentOfInwardAt (M := M) g α₀ x)
  have hdecomp : g.inner (x : M)
        (outwardDirAt (M := M) g α₀ x) (outwardDirAt (M := M) g α₀ x) =
      g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (inwardTangentialPartAt (M := M) g α₀ x) -
      g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (inwardCoordAt (M := M) α₀ x) := by
    change g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (inwardTangentialPartAt (M := M) g α₀ x - inwardCoordAt (M := M) α₀ x) =
      g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (inwardTangentialPartAt (M := M) g α₀ x) -
      g.inner (x : M) (outwardDirAt (M := M) g α₀ x) (inwardCoordAt (M := M) α₀ x)
    exact ContinuousLinearMap.map_sub _ _ _
  rw [hdecomp, h_orth, zero_sub]
  rw [g_inner_outwardDirAt_inwardCoordAt (M := M) g α₀ x]
  ring

/-! ### Parameterised outward unit normal

The parameterised outward unit normal `outwardNormalAt g α₀ x` is the
unit-`g`-length scaling of `outwardDirAt g α₀ x`, when the squared-`g`-norm
is strictly positive (always the case on the chart base set of `α₀`,
established by continuity from the basepoint identity).
At `α₀ = x` the construction reduces to the original `outwardNormal x`. -/

/-- The parameterised outward unit normal: the unit-`g`-length scaling of
`outwardDirAt g α₀ x`. The `0 < g(outwardDirAt, outwardDirAt)` discriminator
is true on the chart base set of `α₀`, but we keep the conditional form so
that the definition is total. -/
def outwardNormalAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    TangentSpace I (x : M) :=
  open scoped Classical in
  if _h :
    0 < g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (outwardDirAt (M := M) g α₀ x) then
    (Real.sqrt (g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (outwardDirAt (M := M) g α₀ x)))⁻¹ • outwardDirAt (M := M) g α₀ x
  else 0

/-- At `α₀ = x`, the parameterised outward unit normal coincides with the
original `outwardNormal x`. -/
@[simp] lemma outwardNormalAt_self
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    outwardNormalAt (M := M) g x x = outwardNormal (M := M) g x := by
  unfold outwardNormalAt outwardNormal
  rw [outwardDirAt_self]


/-! ## Continuity and smoothness of the outward normal as a bundle section

We prove that the section
`x ↦ TotalSpace.mk' E (boundaryInclusion I M x) (outwardNormal g x)` of the
ambient tangent bundle, restricted along the boundary inclusion, is continuous
(and, under additional infrastructure, `C^∞`).

The continuity proof factors through:

* continuity of the chart-trivialised representation
  `b ↦ (e ⟨b.val, outwardNormal g b⟩).2 : E`, where `e := triv-amb at x₀.val`,
  via `Trivialization.contMDiffAt_iff` / continuity equivalents;
* continuity of `b ↦ outwardDir g b` (as a chart-trivialised function),
  obtained from continuity of `b ↦ dincl b (BC g b) - inwardCoord b`;
* continuity of `b ↦ BC g b` (boundary component of inward), via the
  Riesz inverse against a continuous covector;
* continuity of `q b := g.inner b.val (outwardDir g b) (outwardDir g b) > 0`,
  the positive scalar used in the unit-normalisation, leading to continuity of
  the unit-normaliser `(Real.sqrt q b)⁻¹`. -/

section Smoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ### Local helper: smoothness exponent arithmetic -/

private lemma infty_le_top_add' : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  have h_eq : (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) := by
    change ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = ((⊤ : ℕ∞) : WithTop ℕ∞)
    rfl
  rw [h_eq]

/-! ### Smoothness of the chart-trivialisation linear map of the ambient tangent
bundle, in `inTangentCoordinates` form

The chart-trivialisation linear map appears in two equivalent forms:

* the bundle form `b ↦ e.continuousLinearMapAt ℝ b : TangentSpace I b →L[ℝ] E`,
  whose codomain depends on `b` (via the type alias `TangentSpace I b = E`);
* the `inTangentCoordinates`-form
  `b ↦ inTangentCoordinates I 𝓘(ℝ, E) id (extChartAt I x₀)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀)) x₀ b : E →L[ℝ] E`,
  whose codomain is the fixed CLM type.

We work with the second form, which has constant codomain type and is therefore
suitable as a target type for `ContMDiff` statements without dependent-type
coercion issues. -/

/-- The chart-trivialisation linear map of the ambient tangent bundle, in
`inTangentCoordinates`-form. -/
private noncomputable def trivClmAtITC (x₀ : M) (b : M) : E →L[ℝ] E :=
  inTangentCoordinates I 𝓘(ℝ, E) id (extChartAt I x₀)
    (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀)) x₀ b

/-- Smoothness of the `inTangentCoordinates`-form of the chart-trivialisation
linear map at the basepoint. -/
private lemma trivClmAtITC_contMDiffAt
    (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (trivClmAtITC (I := I) x₀) x₀ := by
  have h_chart_at : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I x₀) x₀ := by
    refine (contMDiffOn_extChartAt (I := I) (n := ∞) (x := x₀)).contMDiffAt ?_
    exact (chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀)
  exact h_chart_at.mfderiv_const infty_le_top_add'

/-- Smoothness of the `inTangentCoordinates`-form along the boundary
inclusion. -/
private lemma trivClmAtITC_along_inclusion_contMDiffAt
    (x₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : BoundaryManifold I M => trivClmAtITC (I := I) (x₀ : M) (b : M)) x₀ := by
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) x₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  exact (trivClmAtITC_contMDiffAt (x₀ : M)).comp x₀ h_inclusion_at

/-- Pointwise relation: on the chart source, the `inTangentCoordinates`-form
applied to a constant inputs-from-`E` produces the chart-trivialisation
linear map applied to that input. (Pointwise in `b ∈ chart source`.) -/
private lemma trivClmAtITC_apply
    (x₀ : M) {b : M} (hb : b ∈ (chartAt H x₀).source) (v : E) :
    trivClmAtITC (I := I) x₀ b v =
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ b
        (((trivializationAt E (TangentSpace I) x₀).symmL ℝ b) v) := by
  -- Apply `inTangentCoordinates_eq_mfderiv_comp` and identify each factor.
  unfold trivClmAtITC
  have h_chart_E_src : (extChartAt I x₀) b ∈ (chartAt E ((extChartAt I x₀) x₀)).source := by
    simp
  have h_inT := inTangentCoordinates_eq_mfderiv_comp
    (I := I) (I' := 𝓘(ℝ, E)) (𝕜 := ℝ)
    (f := id) (g := extChartAt I x₀)
    (ϕ := mfderiv I 𝓘(ℝ, E) (extChartAt I x₀)) (x₀ := x₀) (x := b)
    (hx := hb) (hy := h_chart_E_src)
  rw [h_inT]
  have h_first : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) (extChartAt I x₀ x₀)) (extChartAt I x₀ b)
      = ContinuousLinearMap.id ℝ E := by
    have h_eq : extChartAt 𝓘(ℝ, E) (extChartAt I x₀ x₀) =ᶠ[𝓝 (extChartAt I x₀ b)]
        (id : E → E) := by
      filter_upwards with z; rfl
    rw [Filter.EventuallyEq.mfderiv_eq h_eq]
    exact mfderiv_id
  have h_third :
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (Set.range I) (extChartAt I x₀ b)
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ b :=
    (TangentBundle.symmL_trivializationAt hb).symm
  -- Reduce `id x₀` and `id b` to `x₀` and `b`.
  change ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
            (extChartAt 𝓘(ℝ, E) (extChartAt I x₀ x₀)) (extChartAt I x₀ b)).comp
          ((mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) b).comp
            (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (Set.range I)
              (extChartAt I x₀ b)))) v =
    ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ b)
      (((trivializationAt E (TangentSpace I) x₀).symmL ℝ b) v)
  rw [h_first, h_third]
  rw [show mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) b =
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ b from
    (TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I) hb).symm]
  rfl

/-! ### Smoothness of the chart-trivialised dincl-applied-to-section

For any smooth model-space-valued section `s : BoundaryManifold I M → boundaryE`,
the function `b ↦ clmAt b.val (dincl b (s b)) : E` (where `clmAt = (trivAmbAt
x₀.val).continuousLinearMapAt ℝ`) is smooth at `x₀`. The proof uses
`ContMDiffAt.mfderiv_apply`. -/

/-- The `inTangentCoordinates`-form of the dincl-applied-to-section, at a
fixed reference point `x₀ : BoundaryManifold I M`. -/
private noncomputable def dinclITC (x₀ : BoundaryManifold I M)
    (b : BoundaryManifold I M) (v : hI.boundaryE) : E :=
  inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
    (mfderiv hI.boundaryI I (boundaryInclusion I M)) x₀ b v

/-- Smoothness of `b ↦ dinclITC x₀ b (s b)` for any smooth section
`s : BoundaryManifold I M → boundaryE`. -/
private lemma dinclITC_apply_contMDiffAt
    {s : BoundaryManifold I M → hI.boundaryE} {x₀ : BoundaryManifold I M}
    (hs : ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE) ∞ s x₀) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
      (fun b : BoundaryManifold I M => dinclITC (M := M) x₀ b (s b)) x₀ := by
  -- Use `ContMDiffAt.mfderiv_apply` with `f := fun _ b => boundaryInclusion I M b`,
  -- `g := id`, `g₁ := id`, `g₂ := s`.
  unfold dinclITC
  -- Setting up the application.
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) x₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  -- The `mfderiv_apply` formulation needs `f : N → M_src → M_tgt`. We let `N = N' = boundaryManifold`.
  -- For `f n b' := boundaryInclusion I M b'` (constant in `n`).
  have h_f_uncurry : ContMDiffAt (hI.boundaryI.prod hI.boundaryI) I ∞
      (Function.uncurry (fun (_ : BoundaryManifold I M) (b' : BoundaryManifold I M) =>
        boundaryInclusion I M b'))
      (x₀, x₀) := by
    -- `Function.uncurry (fun _ b' => f b') = f ∘ Prod.snd`.
    -- Smoothness: `Prod.snd` smooth, `boundaryInclusion` smooth, composition smooth.
    have h_snd : ContMDiffAt (hI.boundaryI.prod hI.boundaryI) hI.boundaryI ∞
        (Prod.snd : BoundaryManifold I M × BoundaryManifold I M → BoundaryManifold I M)
        (x₀, x₀) := contMDiffAt_snd
    exact h_inclusion_at.comp (x₀, x₀) h_snd
  have h_g_at : ContMDiffAt hI.boundaryI hI.boundaryI ∞
      (id : BoundaryManifold I M → BoundaryManifold I M) x₀ := contMDiffAt_id
  have h_g₁_at : ContMDiffAt hI.boundaryI hI.boundaryI ∞
      (id : BoundaryManifold I M → BoundaryManifold I M) x₀ := contMDiffAt_id
  exact ContMDiffAt.mfderiv_apply
    (f := fun (_ : BoundaryManifold I M) (b : BoundaryManifold I M) => boundaryInclusion I M b)
    (g := id) (g₁ := id) (g₂ := s)
    h_f_uncurry h_g_at h_g₁_at hs infty_le_top_add'

/-- The `inTangentCoordinates`-form of `dincl b` evaluates as
`clmAt b.val ∘ dincl b ∘ symmL_bdy b`. We write this in pointwise form. -/
private lemma dinclITC_apply
    (x₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_amb : (b : M) ∈ (chartAt H (x₀ : M)).source)
    (hb_bdy : b ∈ (chartAt hI.boundaryH x₀).source) (v : hI.boundaryE) :
    dinclITC (M := M) x₀ b v =
      (trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ
        (b : M) (dincl (M := M) b
          (((trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) x₀).symmL ℝ b) v)) := by
  unfold dinclITC
  have h_inT := inTangentCoordinates_eq_mfderiv_comp
    (I := hI.boundaryI) (I' := I) (𝕜 := ℝ)
    (f := id) (g := boundaryInclusion I M)
    (ϕ := mfderiv hI.boundaryI I (boundaryInclusion I M)) (x₀ := x₀) (x := b)
    (hx := hb_bdy) (hy := hb_amb)
  rw [h_inT]
  -- Three factors:
  -- 1. mfderiv (extChartAt I (boundaryInclusion x₀)) (boundaryInclusion b) = clmAt b.val
  -- 2. mfderiv (boundaryInclusion) b = dincl b
  -- 3. mfderivWithin (range boundaryI) (extChartAt boundaryI x₀).symm (extChartAt boundaryI x₀ b)
  --    = symmL_bdy b
  have h_first : mfderiv I 𝓘(ℝ, E)
      (extChartAt I (boundaryInclusion I M x₀)) (boundaryInclusion I M b)
      = (trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M) :=
    (TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I) hb_amb).symm
  have h_third :
      mfderivWithin 𝓘(ℝ, hI.boundaryE) hI.boundaryI (extChartAt hI.boundaryI x₀).symm
        (Set.range hI.boundaryI) (extChartAt hI.boundaryI x₀ b)
      = (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ b :=
    (TangentBundle.symmL_trivializationAt hb_bdy).symm
  -- The middle factor: `mfderiv (boundaryInclusion I M) (id b) = mfderiv boundaryInclusion b = dincl b`.
  -- Note: `id b` here is from the inTangentCoordinates_eq_mfderiv_comp using `f = id`, but the
  -- `g x` in the formula is `boundaryInclusion x` (where `g := boundaryInclusion`).
  -- The middle factor is `mfderiv (f x) (g x) = mfderiv id ... wait, we have ϕ x = mfderiv (f x) (g x)`.
  -- Actually re-read: `inTangentCoord f g ϕ x₀ x = mfderiv (extChart at g x₀) (g x) ∘L ϕ x ∘L mfderivWithin (range I) (extChart at f x₀).symm`.
  -- With `f = id`, `g = boundaryInclusion`, `ϕ x = mfderiv boundaryInclusion x`:
  -- `= mfderiv (extChart at boundaryInclusion x₀) (boundaryInclusion x) ∘L mfderiv boundaryInclusion x ∘L mfderivWithin (range boundaryI) (extChartAt boundaryI x₀).symm (extChartAt boundaryI x₀ (id x))`.
  -- Simplifying: extChart at boundaryInclusion x₀ = extChartAt I (x₀.val); (extChartAt boundaryI x₀ (id x)) = extChartAt boundaryI x₀ x.
  -- The middle factor: `mfderiv (boundaryInclusion I M) b = dincl b`.
  -- `id x₀ = x₀` and `id b = b`.
  change ((mfderiv I 𝓘(ℝ, E) (extChartAt I (boundaryInclusion I M x₀))
          (boundaryInclusion I M b)).comp
        ((mfderiv hI.boundaryI I (boundaryInclusion I M) b).comp
          (mfderivWithin 𝓘(ℝ, hI.boundaryE) hI.boundaryI (extChartAt hI.boundaryI x₀).symm
            (Set.range hI.boundaryI) (extChartAt hI.boundaryI x₀ b)))) v =
      ((trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M))
        ((dincl (M := M) b) (((trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) x₀).symmL ℝ b) v))
  rw [h_first, h_third]
  rfl

/-! ### Smoothness of the chart-trivialised dincl-applied-to-section, continued

For the unnormalised outward direction `outwardDir g b = dincl b (BC g b) - inwardCoord b`,
we want continuity (and smoothness, when `BC g b` is smooth in `b`) of its chart
trivialisation in the ambient bundle. -/

/-- Smoothness of `b ↦ trivClmAtITC x₀.val b.val v(b) : E` for any smooth model-space
function `v : BoundaryManifold I M → E`, under the trivialisation at `x₀.val`. -/
private lemma trivClmAtITC_apply_contMDiffAt
    {x₀ : BoundaryManifold I M} {v : BoundaryManifold I M → E}
    (hv : ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞ v x₀) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
      (fun b : BoundaryManifold I M => trivClmAtITC (I := I) (x₀ : M) (b : M) (v b)) x₀ :=
  (trivClmAtITC_along_inclusion_contMDiffAt x₀).clm_apply hv

/-! ### Smoothness of the boundary chart-trivialisation linear map -/

/-- The boundary chart-trivialisation linear map, in `inTangentCoordinates`-form. -/
private noncomputable def trivClmAtITC_bdy (x₀ : BoundaryManifold I M)
    (b : BoundaryManifold I M) : hI.boundaryE →L[ℝ] hI.boundaryE :=
  inTangentCoordinates hI.boundaryI 𝓘(ℝ, hI.boundaryE) id (extChartAt hI.boundaryI x₀)
    (mfderiv hI.boundaryI 𝓘(ℝ, hI.boundaryE) (extChartAt hI.boundaryI x₀)) x₀ b

/-- Smoothness of the `inTangentCoordinates`-form of the boundary chart
trivialisation linear map. -/
private lemma trivClmAtITC_bdy_contMDiffAt
    (x₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] hI.boundaryE) ∞
      (trivClmAtITC_bdy (M := M) x₀) x₀ := by
  have h_chart_at : ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE) ∞
      (extChartAt hI.boundaryI x₀) x₀ := by
    refine (contMDiffOn_extChartAt (I := hI.boundaryI) (n := ∞) (x := x₀)).contMDiffAt ?_
    exact (chartAt hI.boundaryH x₀).open_source.mem_nhds (mem_chart_source _ _)
  exact h_chart_at.mfderiv_const infty_le_top_add'

/-- Pointwise relation: on the chart source of the boundary, the
`inTangentCoordinates`-form for the boundary applied to a constant input from
`boundaryE` produces the chart-trivialisation linear map applied to that input. -/
private lemma trivClmAtITC_bdy_apply
    (x₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb : b ∈ (chartAt hI.boundaryH x₀).source) (v : hI.boundaryE) :
    trivClmAtITC_bdy (M := M) x₀ b v =
      (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).continuousLinearMapAt ℝ b
        (((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ b) v) := by
  unfold trivClmAtITC_bdy
  have h_chart_E_src : (extChartAt hI.boundaryI x₀) b ∈
      (chartAt hI.boundaryE ((extChartAt hI.boundaryI x₀) x₀)).source := by simp
  have h_inT := inTangentCoordinates_eq_mfderiv_comp
    (I := hI.boundaryI) (I' := 𝓘(ℝ, hI.boundaryE)) (𝕜 := ℝ)
    (f := id) (g := extChartAt hI.boundaryI x₀)
    (ϕ := mfderiv hI.boundaryI 𝓘(ℝ, hI.boundaryE) (extChartAt hI.boundaryI x₀))
    (x₀ := x₀) (x := b)
    (hx := hb) (hy := h_chart_E_src)
  rw [h_inT]
  have h_first : mfderiv 𝓘(ℝ, hI.boundaryE) 𝓘(ℝ, hI.boundaryE)
      (extChartAt 𝓘(ℝ, hI.boundaryE) (extChartAt hI.boundaryI x₀ x₀))
      (extChartAt hI.boundaryI x₀ b) = ContinuousLinearMap.id ℝ hI.boundaryE := by
    have h_eq : extChartAt 𝓘(ℝ, hI.boundaryE)
        (extChartAt hI.boundaryI x₀ x₀) =ᶠ[𝓝 (extChartAt hI.boundaryI x₀ b)]
          (id : hI.boundaryE → hI.boundaryE) := by
      filter_upwards with z; rfl
    rw [Filter.EventuallyEq.mfderiv_eq h_eq]
    exact mfderiv_id
  have h_third :
      mfderivWithin 𝓘(ℝ, hI.boundaryE) hI.boundaryI (extChartAt hI.boundaryI x₀).symm
        (Set.range hI.boundaryI) (extChartAt hI.boundaryI x₀ b)
      = (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ b :=
    (TangentBundle.symmL_trivializationAt hb).symm
  change ((mfderiv 𝓘(ℝ, hI.boundaryE) 𝓘(ℝ, hI.boundaryE)
        (extChartAt 𝓘(ℝ, hI.boundaryE) (extChartAt hI.boundaryI x₀ x₀))
        (extChartAt hI.boundaryI x₀ b)).comp
      ((mfderiv hI.boundaryI 𝓘(ℝ, hI.boundaryE) (extChartAt hI.boundaryI x₀) b).comp
        (mfderivWithin 𝓘(ℝ, hI.boundaryE) hI.boundaryI (extChartAt hI.boundaryI x₀).symm
          (Set.range hI.boundaryI) (extChartAt hI.boundaryI x₀ b)))) v =
    ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).continuousLinearMapAt ℝ b)
      (((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ b) v)
  rw [h_first, h_third]
  rw [show mfderiv hI.boundaryI 𝓘(ℝ, hI.boundaryE) (extChartAt hI.boundaryI x₀) b =
      (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).continuousLinearMapAt ℝ b from
    (TangentBundle.continuousLinearMapAt_trivializationAt
      (𝕜 := ℝ) (I := hI.boundaryI) hb).symm]
  rfl

/-! ### Continuity / smoothness of the boundary metric flat as a CLM-valued function

Bundle-section smoothness `inducedMetricInner_contMDiff` already establishes
smoothness of `b ↦ inducedMetricInner g b` as a section of the bilinear-form
Hom-bundle on `BoundaryManifold I M`. We extract the chart-trivialised CLM-valued
form. -/

variable (g : Measure.SmoothRiemannianMetric I M)

/-- The chart-trivialised boundary metric flat, as a CLM-valued function
`BoundaryManifold I M → (boundaryE →L[ℝ] (boundaryE →L[ℝ] ℝ))`. -/
private noncomputable def boundaryFlatCharted
    (x₀ : BoundaryManifold I M) (b : BoundaryManifold I M) :
    hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ :=
  ((trivializationAt (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
      (fun y : BoundaryManifold I M =>
        TangentSpace hI.boundaryI y →L[ℝ] TangentSpace hI.boundaryI y →L[ℝ] ℝ) x₀)
    ⟨b, inducedMetricInner g b⟩).2

/-- Smoothness of the chart-trivialised boundary metric flat. -/
private lemma boundaryFlatCharted_contMDiffAt
    (x₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ) ∞
      (boundaryFlatCharted (M := M) g x₀) x₀ := by
  have h_section := inducedMetricInner_contMDiff (g := g)
  have h_x₀ : x₀ ∈ (trivializationAt (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
      (fun y : BoundaryManifold I M =>
        TangentSpace hI.boundaryI y →L[ℝ] TangentSpace hI.boundaryI y →L[ℝ] ℝ) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  exact ((trivializationAt _ _ x₀).contMDiffAt_section_iff h_x₀).mp
    h_section.contMDiffAt

/-! ### Boundary functional and its smoothness

`boundaryFunOfInward g b : boundaryE →ₗ[ℝ] ℝ` was defined as a `→ₗ[ℝ]` map; we
upgrade it to a continuous version `boundaryFunOfInwardCLM g b` for use with
the smoothness machinery. -/

/-- The continuous version of `boundaryFunOfInward`, viewed as a CLM. -/
private noncomputable def boundaryFunOfInwardCLM
    (b : BoundaryManifold I M) : hI.boundaryE →L[ℝ] ℝ :=
  (g.inner (b : M) (inwardCoord (M := M) b)).comp (dincl (M := M) b)

@[simp] private lemma boundaryFunOfInwardCLM_apply
    (b : BoundaryManifold I M) (w : hI.boundaryE) :
    boundaryFunOfInwardCLM (M := M) g b w =
      g.inner (b : M) (inwardCoord (M := M) b) (dincl (M := M) b w) := rfl

/-! ### Continuity of the outward normal as a section

The deliverable here: continuity of the section
`b ↦ TotalSpace.mk' E (boundaryInclusion I M b) (outwardNormal g b)`.

We use `FiberBundle.continuousAt_totalSpace` to reduce continuity of the section
to continuity of:

(a) `b ↦ (b : M)` (the proj-component) — direct from continuity of `boundaryInclusion`.

(b) `b ↦ (e_amb ⟨b.val, outwardNormal g b⟩).2 : E` (the chart-trivialised
fiber component, where `e_amb := triv-amb at x₀.val`) on a neighbourhood of `x₀`.

For (b), the strategy is to identify the chart-trivialised form on the chart
base set with continuous compositions of the chart trivialisations of the
boundary metric flat (from `inducedMetricInner_contMDiff`), the smooth
chart-trivialised dincl-section (from `dinclITC_apply_contMDiffAt`), and
arithmetic on the strictly-positive scalar `q b`. -/

/-- The boundary metric flat is invertible (as a CLM) at every boundary point.
This follows from positive-definiteness of `inducedMetricInner` (which gives
injectivity) combined with the equality of source and target finite dimensions. -/
private lemma inducedMetricInner_isInvertible
    (b : BoundaryManifold I M) :
    (inducedMetricInner (M := M) g b).IsInvertible := by
  -- Use `boundaryFlatLinear_injective` to derive a `LinearEquiv` and then a `CLE`.
  -- The CLM `inducedMetricInner g b` agrees with `boundaryFlatLinear g x` viewed as
  -- a `→ₗ[ℝ]`. The ContinuousLinearMap form is the same up to the natural inclusion.
  -- We extract a `≃L[ℝ]` from the linear equivalence in finite-dim, then witness
  -- invertibility by `ContinuousLinearMap.IsInvertible`.
  have h_inj : Function.Injective (inducedMetricInner (M := M) g b) := by
    intro u v huv
    -- From `huv : inducedMetricInner g b u = inducedMetricInner g b v`, derive `u = v`.
    -- Apply `huv` to any `w`, getting `inducedMetricInner g b u w = inducedMetricInner g b v w`,
    -- which by linearity gives `inducedMetricInner g b (u - v) w = 0` for all `w`.
    -- Setting `w = u - v` and using `inducedMetricInner_pos` gives `u = v`.
    by_contra hne
    have huv_ne : u - v ≠ 0 := sub_ne_zero.mpr hne
    have hpos : 0 < inducedMetricInner (M := M) g b (u - v) (u - v) :=
      inducedMetricInner_pos (M := M) g b (u - v) huv_ne
    have hzero : inducedMetricInner (M := M) g b (u - v) (u - v) = 0 := by
      have h1 : inducedMetricInner (M := M) g b (u - v) =
          inducedMetricInner (M := M) g b u - inducedMetricInner (M := M) g b v :=
        ContinuousLinearMap.map_sub _ _ _
      rw [h1, huv, sub_self]
      simp
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  -- From injectivity + finrank-equality, build the LinearEquiv, then CLE.
  -- The LinearEquiv is essentially `boundaryFlatLinear_injective`-style.
  -- Extract the underlying linear map: `(inducedMetricInner g b).toLinearMap`.
  let L : hI.boundaryE →ₗ[ℝ] (hI.boundaryE →L[ℝ] ℝ) := (inducedMetricInner g b).toLinearMap
  have hL_inj : Function.Injective L := h_inj
  -- The dimensions match.
  have hfinrank : Module.finrank ℝ hI.boundaryE =
      Module.finrank ℝ (hI.boundaryE →L[ℝ] ℝ) := by
    -- Continuous dual has same finrank as the algebraic dual in finite-dim, which equals dim of E.
    -- Mathlib: `LinearMap.finrank_dual_eq` for algebraic dual; for continuous dual, same.
    rw [show Module.finrank ℝ (hI.boundaryE →L[ℝ] ℝ) =
        Module.finrank ℝ (hI.boundaryE →ₗ[ℝ] ℝ) from ?_]
    · exact Subspace.dual_finrank_eq.symm
    · -- `(boundaryE →L[ℝ] ℝ) ≃ₗ[ℝ] (boundaryE →ₗ[ℝ] ℝ)` in finite-dim. Use this.
      exact (LinearEquiv.finrank_eq
        (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := hI.boundaryE) (F' := ℝ))).symm
  let L_equiv : hI.boundaryE ≃ₗ[ℝ] (hI.boundaryE →L[ℝ] ℝ) :=
    LinearMap.linearEquivOfInjective L hL_inj hfinrank
  -- Promote to a continuous linear equivalence (auto in finite-dim).
  let L_cle : hI.boundaryE ≃L[ℝ] (hI.boundaryE →L[ℝ] ℝ) := L_equiv.toContinuousLinearEquiv
  -- The underlying CLM of `L_cle` agrees with `inducedMetricInner g b`.
  have h_eq : (L_cle : hI.boundaryE →L[ℝ] (hI.boundaryE →L[ℝ] ℝ)) =
      inducedMetricInner (M := M) g b := by
    ext u
    -- Both apply to give `inducedMetricInner g b u`.
    rfl
  -- Therefore `inducedMetricInner g b` is invertible (witnessed by `L_cle`).
  exact ⟨L_cle, h_eq⟩


/-! ### Smoothness of the chart-trivialised boundary metric flat as a
constant-codomain CLM-valued function

We extract continuity of the chart-trivialised boundary metric flat
`b ↦ boundaryFlatCharted x₀ b : (boundaryE →L[ℝ] (boundaryE →L[ℝ] ℝ))`,
which is a smooth function with **constant codomain type**. -/

/-- Continuity of the chart-trivialised boundary metric flat. -/
private lemma boundaryFlatCharted_continuousAt
    (x₀ : BoundaryManifold I M) :
    ContinuousAt (boundaryFlatCharted (M := M) g x₀) x₀ :=
  (boundaryFlatCharted_contMDiffAt (M := M) g x₀).continuousAt

/-! ### Identification of the boundary metric flat at the basepoint

At the basepoint, the chart-trivialised boundary metric flat
`boundaryFlatCharted x₀ x₀` coincides with `inducedMetricInner g x₀` because
both factors of the chart-trivialisation reduce to the identity at the
basepoint (a standard property of `mfderivWithin_range_extChartAt_symm`). -/

/-- Helper: at the basepoint, the chart-trivialised boundary metric flat
agrees with the bundle value `inducedMetricInner g x₀`. -/
private lemma boundaryFlatCharted_basepoint
    (x₀ : BoundaryManifold I M) :
    boundaryFlatCharted (M := M) g x₀ x₀ = inducedMetricInner (M := M) g x₀ := by
  refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => ?_
  have hb_bdy : x₀ ∈ (trivializationAt hI.boundaryE
      (TangentSpace hI.boundaryI) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  -- Unfold `boundaryFlatCharted` to `hom_trivializationAt_apply`-form, then
  -- reduce via `inCoordinates_apply_eq₂` at the basepoint.
  change ((trivializationAt (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
          (fun y : BoundaryManifold I M =>
            TangentSpace hI.boundaryI y →L[ℝ]
            TangentSpace hI.boundaryI y →L[ℝ] ℝ) x₀)
        ⟨x₀, inducedMetricInner (M := M) g x₀⟩).2 u v =
      ((inducedMetricInner (M := M) g x₀) u) v
  rw [hom_trivializationAt_apply]
  -- Now LHS is `inCoordinates ... x₀ x₀ x₀ x₀ (inducedMetricInner g x₀) u v`.
  rw [inCoordinates_apply_eq₂ (𝕜 := ℝ) hb_bdy hb_bdy (Set.mem_univ _)]
  -- LHS now: `(triv-trivial-ℝ).linearMapAt ℝ x₀ (inducedMetricInner g x₀ (symm u) (symm v))`.
  change (trivializationAt ℝ (Bundle.Trivial (BoundaryManifold I M) ℝ) x₀).linearMapAt ℝ x₀ _ = _
  change (Bundle.Trivial.trivialization (BoundaryManifold I M) ℝ).linearMapAt ℝ x₀ _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization (𝕜 := ℝ)
    (B := BoundaryManifold I M) (F := ℝ) x₀]
  -- Now: `(inducedMetricInner g x₀) (symm x₀ u) (symm x₀ v) = (inducedMetricInner g x₀ u) v`.
  -- Uses `(triv-bdy at x₀).symm x₀ = id` (basepoint identity).
  have h_symmL_id : ∀ w : hI.boundaryE,
      ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ x₀) w = w := by
    intro w
    have hsymmL_eq :
        (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ x₀
          = mfderivWithin 𝓘(ℝ, hI.boundaryE) hI.boundaryI
              (extChartAt hI.boundaryI x₀).symm
              (Set.range hI.boundaryI) (extChartAt hI.boundaryI x₀ x₀) :=
      TangentBundle.symmL_trivializationAt hb_bdy
    rw [hsymmL_eq, mfderivWithin_range_extChartAt_symm]
    rfl
  -- Convert `.symm` form to `.symmL ℝ` form to apply `h_symmL_id`.
  -- `Trivialization.symmL_apply` says `⇑(symmL R e b) = symm e b` (CLM coercion = symm).
  have hcoe :
      ⇑((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ x₀)
        = (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symm x₀ :=
    Trivialization.symmL_apply _ _ _
  have hsymm1 : (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symm x₀ u
      = ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ x₀) u := by
    rw [hcoe]
  have hsymm2 : (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symm x₀ v
      = ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ x₀) v := by
    rw [hcoe]
  rw [hsymm1, hsymm2, h_symmL_id u, h_symmL_id v]
  rfl

/-! ### Operator-norm smoothness of the chart-trivialised inverse boundary
metric flat -/

/-- The chart-trivialised inverse boundary metric flat:
`b ↦ ContinuousLinearMap.inverse (boundaryFlatCharted x₀ b) :
   (boundaryE →L[ℝ] ℝ) →L[ℝ] boundaryE`. `C^∞` at the basepoint thanks to
operator-norm smoothness of inverse on invertibles. -/
private noncomputable def boundaryFlatChartedInv
    (x₀ : BoundaryManifold I M) (b : BoundaryManifold I M) :
    (hI.boundaryE →L[ℝ] ℝ) →L[ℝ] hI.boundaryE :=
  ContinuousLinearMap.inverse (boundaryFlatCharted (M := M) g x₀ b)

/-- The chart-trivialised inverse boundary metric flat is `C^∞` at the
basepoint. -/
private lemma boundaryFlatChartedInv_contMDiffAt
    (x₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, (hI.boundaryE →L[ℝ] ℝ) →L[ℝ] hI.boundaryE) ∞
      (boundaryFlatChartedInv (M := M) g x₀) x₀ := by
  have h_flat : ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ) ∞
      (boundaryFlatCharted (M := M) g x₀) x₀ :=
    boundaryFlatCharted_contMDiffAt (M := M) g x₀
  have h_inv : (boundaryFlatCharted (M := M) g x₀ x₀).IsInvertible := by
    rw [boundaryFlatCharted_basepoint (M := M) g x₀]
    exact inducedMetricInner_isInvertible (M := M) g x₀
  have h_inverse_smooth :
      ContDiffAt ℝ ∞ ContinuousLinearMap.inverse
        (boundaryFlatCharted (M := M) g x₀ x₀) :=
    h_inv.contDiffAt_map_inverse
  exact h_inverse_smooth.contMDiffAt.comp x₀ h_flat

/-! ### Smoothness of the chart-trivialised boundary functional `boundaryFunOfInward`

We chart-trivialise both factors of `boundaryFunOfInwardCLM g b = (g.inner b.val
(inwardCoord b)) ∘ (dincl b)`. The natural chart-trivialised form has type
`boundaryE →L[ℝ] ℝ` and is `b ↦ (boundaryFunOfInwardCLM g b) ∘ symmL_bdy b`,
where `symmL_bdy = (triv-bdy at x₀).symmL ℝ b`.

The smoothness of `b ↦ (boundaryFunOfInwardCLM g b) ∘ symmL_bdy b` will be
established by direct expansion: `(g.inner b.val v) ∘ dincl b ∘ symmL_bdy b`
where `v = inwardCoord b = inwardCoordE` (constant by `inwardCoord_eq`). The
factors are smooth via the chart-trivialisation lemmas. -/

/-- The chart-trivialised covector `boundaryFunOfInwardCharted x₀ b : boundaryE
→L[ℝ] ℝ`, defined as `(boundaryFunOfInwardCLM g b) ∘ (symmL_bdy x₀ b)`. -/
private noncomputable def boundaryFunOfInwardCharted
    (x₀ : BoundaryManifold I M) (b : BoundaryManifold I M) :
    hI.boundaryE →L[ℝ] ℝ :=
  (boundaryFunOfInwardCLM (M := M) g b).comp
    ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ b)

@[simp] private lemma boundaryFunOfInwardCharted_apply
    (x₀ : BoundaryManifold I M) (b : BoundaryManifold I M)
    (w : hI.boundaryE) :
    boundaryFunOfInwardCharted (M := M) g x₀ b w =
      g.inner (b : M) (inwardCoord (M := M) b)
        (dincl (M := M) b
          (((trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) x₀).symmL ℝ b) w)) := rfl

/-! ### Smooth chart-fixed inward direction `inwardCoordAt`

The parameterised inward direction `inwardCoordAt α₀ b` uses a *fixed*
ambient trivialisation centred at `α₀.val`. As a section of the ambient
tangent bundle, it is smooth on the chart base set. -/

/-- The section `b ↦ TotalSpace.mk' E (b : M) (inwardCoordAt α₀ b)` is smooth
on the chart base set of `α₀.val`. The proof mirrors
`Measure.chartBasisVec_contMDiffOn`, with the constant input `inwardCoordE`
in place of a basis vector. -/
private lemma inwardCoordAt_section_contMDiffOn
    (α₀ : BoundaryManifold I M) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M =>
        TotalSpace.mk' E y
          ((trivializationAt E (TangentSpace I) (α₀ : M)).symm y hI.inwardCoordE))
      (trivializationAt E (TangentSpace I) (α₀ : M)).baseSet := by
  -- Mirrors `chartBasisVec_contMDiffOn`: smooth section, with constant model-
  -- space input replacing the basis vector.
  have hiff :=
    ((trivializationAt E (TangentSpace I) (α₀ : M))).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞)
      (s := fun y : M => (trivializationAt E (TangentSpace I) (α₀ : M)).symm y
        hI.inwardCoordE)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun _ : M => hI.inwardCoordE)
      (trivializationAt E (TangentSpace I) (α₀ : M)).baseSet := contMDiffOn_const
  refine hconst.congr ?_
  intro y hy
  -- Round-trip identity: `(triv ⟨y, triv.symm y v⟩).2 = v` when `y ∈ baseSet`.
  have h := (trivializationAt E (TangentSpace I) (α₀ : M)).apply_mk_symm hy
    hI.inwardCoordE
  exact congrArg Prod.snd h

/-- Smoothness along the boundary inclusion: the inward direction
`inwardCoordAt α₀ b`, viewed as a function of `b : BoundaryManifold I M`, is
smooth at `α₀` as a totalspace-valued function. -/
private lemma inwardCoordAt_section_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (inwardCoordAt (M := M) α₀ b)) α₀ := by
  -- Use the section smoothness on `M`, composed with the smooth inclusion.
  have hα_in : (α₀ : M) ∈ (trivializationAt E (TangentSpace I) (α₀ : M)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (α₀ : M)
  have h_section_open :
      (trivializationAt E (TangentSpace I) (α₀ : M)).baseSet ∈ 𝓝 (α₀ : M) :=
    ((trivializationAt E (TangentSpace I) (α₀ : M)).open_baseSet).mem_nhds hα_in
  have h_section_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M =>
        TotalSpace.mk' E y
          ((trivializationAt E (TangentSpace I) (α₀ : M)).symm y hI.inwardCoordE))
      (α₀ : M) :=
    (inwardCoordAt_section_contMDiffOn (M := M) α₀).contMDiffAt h_section_open
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) α₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  exact h_section_at.comp α₀ h_inclusion_at

/-! ### Continuity of the chart-fixed inward direction

The parameterised inward direction `inwardCoordAt α₀ b` is continuous at `α₀`
as a totalspace-valued function. -/

private lemma inwardCoordAt_section_continuousAt
    (α₀ : BoundaryManifold I M) :
    ContinuousAt
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (inwardCoordAt (M := M) α₀ b)) α₀ :=
  (inwardCoordAt_section_contMDiffAt (M := M) α₀).continuousAt

/-! ### Continuity of the chart-trivialised second component of `inwardCoordAt`

The chart-trivialised second component (in the trivialisation at `α₀.val`) of
the section `b ↦ inwardCoordAt α₀ b` is the *constant* function with value
`inwardCoordE`. This is the round-trip identity. -/

private lemma chart_triv_second_inwardCoordAt
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb : (b : M) ∈ (trivializationAt E (TangentSpace I) (α₀ : M)).baseSet) :
    ((trivializationAt E (TangentSpace I) (α₀ : M))
        ⟨(b : M), inwardCoordAt (M := M) α₀ b⟩).2 = hI.inwardCoordE := by
  -- `inwardCoordAt α₀ b = (triv at α₀.val).symm b.val inwardCoordE`.
  -- `(triv ⟨b.val, triv.symm b.val v⟩).2 = v` when `b.val ∈ baseSet`.
  unfold inwardCoordAt
  have h := (trivializationAt E (TangentSpace I) (α₀ : M)).apply_mk_symm hb
    hI.inwardCoordE
  exact congrArg Prod.snd h

/-! ### Codimension-one helper: the `g`-normal subspace is one-dimensional

The normal subspace `normalSubspace g x` is the `g`-orthogonal complement of
`range (dincl x)`. Combined with the codim-1 typeclass field, this subspace
has dimension exactly `1`. This is the key fact used downstream to show the
unit outward normal is unique up to sign. -/

/-- The boundary tangent subspace at `x : BoundaryManifold I M`, expressed as
a submodule of `E` (the model space). The `dincl x` map is naturally typed
into `TangentSpace I (x : M) = E`, so we view its image as a submodule of `E`
via the type alias. -/
private noncomputable def tangentSpaceImage
    (x : BoundaryManifold I M) : Submodule ℝ E :=
  Submodule.map (dincl (M := M) x).toLinearMap ⊤

/-- The boundary tangent subspace has dimension equal to `finrank ℝ boundaryE`. -/
private lemma tangentSpaceImage_finrank
    (x : BoundaryManifold I M) [Nonempty hI.boundaryH] :
    Module.finrank ℝ (tangentSpaceImage (M := M) x) =
      Module.finrank ℝ hI.boundaryE := by
  have h_inj : Function.Injective (dincl (M := M) x) :=
    dincl_injective (I := I) (M := M) x
  have h_inj_lm : Function.Injective (dincl (M := M) x).toLinearMap := h_inj
  unfold tangentSpaceImage
  have h_equiv : (⊤ : Submodule ℝ hI.boundaryE) ≃ₗ[ℝ]
      Submodule.map (dincl (M := M) x).toLinearMap ⊤ :=
    Submodule.equivMapOfInjective (dincl (M := M) x).toLinearMap h_inj_lm ⊤
  have h_top_finrank : Module.finrank ℝ (⊤ : Submodule ℝ hI.boundaryE) =
      Module.finrank ℝ hI.boundaryE := finrank_top _ _
  rw [← h_top_finrank]
  exact (LinearEquiv.finrank_eq h_equiv).symm

/-! ### Dimension of the `g`-normal subspace via metric duality

The `g`-orthogonal complement of `range (dincl x)` is `normalSubspace g x`.
Using the codim-1 condition `finrank_boundaryE_succ` and the non-degeneracy
of `g.inner x` together with injectivity of `dincl x`, the dimension of
`normalSubspace g x` is exactly `1`.

The argument: the `g`-pullback covector map `v ↦ (w ↦ g.inner x v (dincl x w))`
is a linear map `E →ₗ[ℝ] (boundaryE →ₗ[ℝ] ℝ)`. Its kernel is
`normalSubspace g x`. By non-degeneracy and the codim-1 condition, its image
equals the whole `boundaryE →ₗ[ℝ] ℝ` (whose dimension equals `boundaryE`).
Rank-nullity then gives the dimension count.

The infrastructure below provides the kernel-identification piece. The
surjectivity argument requires combining the `g`-Riesz isomorphism with the
restriction along `dincl x`, and is left for future development. -/

/-- The `g`-pullback covector linear map: `v ↦ (w ↦ g.inner x v (dincl x w))`. -/
private noncomputable def metricPullback
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    TangentSpace I (x : M) →ₗ[ℝ] (hI.boundaryE →ₗ[ℝ] ℝ) where
  toFun v :=
    { toFun := fun w => g.inner (x : M) v (dincl (M := M) x w)
      map_add' := fun u v' => by
        rw [ContinuousLinearMap.map_add (dincl (M := M) x) u v']
        exact ContinuousLinearMap.map_add (g.inner (x : M) v) _ _
      map_smul' := fun c v' => by
        rw [ContinuousLinearMap.map_smul (dincl (M := M) x) c v']
        exact ContinuousLinearMap.map_smul (g.inner (x : M) v) _ _ }
  map_add' v₁ v₂ := by
    ext w
    change g.inner (x : M) (v₁ + v₂) (dincl (M := M) x w) =
      g.inner (x : M) v₁ (dincl (M := M) x w) +
      g.inner (x : M) v₂ (dincl (M := M) x w)
    rw [map_add, ContinuousLinearMap.add_apply]
  map_smul' c v := by
    ext w
    change g.inner (x : M) (c • v) (dincl (M := M) x w) =
      c • g.inner (x : M) v (dincl (M := M) x w)
    rw [map_smul, ContinuousLinearMap.smul_apply]

@[simp] private lemma metricPullback_apply
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v : TangentSpace I (x : M)) (w : hI.boundaryE) :
    metricPullback (M := M) g x v w =
      g.inner (x : M) v (dincl (M := M) x w) := rfl

/-- A vector `v` is in the kernel of `metricPullback g x` iff it is in
`normalSubspace g x`. -/
private lemma mem_ker_metricPullback_iff
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v : TangentSpace I (x : M)) :
    v ∈ LinearMap.ker (metricPullback (M := M) g x) ↔
      v ∈ normalSubspace (M := M) g x := by
  refine ⟨?_, ?_⟩
  · intro hv w
    have h := congrArg (fun L : hI.boundaryE →ₗ[ℝ] ℝ => L w) hv
    simp only [metricPullback_apply, LinearMap.zero_apply] at h
    exact h
  · intro hv
    apply LinearMap.ext
    intro w
    rw [metricPullback_apply, hv w]
    rfl

/-- The kernel of `metricPullback` as a `Submodule` equals `normalSubspace`. -/
private lemma ker_metricPullback_eq_normalSubspace
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    LinearMap.ker (metricPullback (M := M) g x) = normalSubspace (M := M) g x := by
  apply Submodule.ext
  intro v
  exact mem_ker_metricPullback_iff (M := M) g x v

/-! The `g`-pullback covector map is surjective onto `boundaryE →ₗ[ℝ] ℝ`. The
proof combines the `g`-Riesz isomorphism `(E →ₗ[ℝ] ℝ) ≃ E` (induced by the
non-degenerate metric) with the surjective restriction `(E →ₗ[ℝ] ℝ) →
(boundaryE →ₗ[ℝ] ℝ)` along the injective `dincl x`. The full assembly is
substantial; we leave it for future development. -/

/-! ## Smoothness of the parameterised outward normal `outwardNormalAt α₀`

We establish chart-α-local smoothness of the parameterised outward unit normal
`outwardNormalAt α₀ g b`, viewed as a section of the ambient tangent bundle
along the boundary inclusion. The headline result is `ContMDiffAt` at the
basepoint `α₀`.

Strategy. We construct chart-trivialised model-space-valued versions of the
boundary functional, the boundary component, the inward tangential part, and
the unnormalised outward direction. Their smoothness at `α₀` follows by
direct composition (using `boundaryFlatChartedInv_contMDiffAt`,
`dinclITC_apply_contMDiffAt`, and `clm_bundle_apply` on the smooth
inner-product section). We then identify the chart-trivialised forms with
the chart-trivialised second components of the bundle-valued quantities on
the chart base sets, and conclude smoothness of the bundle section at
`α₀` via `Trivialization.contMDiffAt_iff`. -/

variable (g : Measure.SmoothRiemannianMetric I M)

/-! ### The chart-trivialised boundary functional

We construct a CLM-valued chart-trivialised form of the boundary functional
`w ↦ g.inner b.val (inwardCoordAt α₀ b) (dincl b w)`. The smoothness at α₀
of the chart-trivialised form is established via `clm_bundle_apply` on the
smooth bilinear-form bundle `g.inner` and the smooth inward-direction section,
combined with the smoothness of the chart-conjugated `dincl`. -/

/-- The chart-trivialised boundary functional, defined as the composite of
the chart-trivialised inner-product covector with the chart-conjugated
boundary inclusion derivative `dinclITC α₀ b`. -/
private noncomputable def boundaryFunOfInwardAtChartedCLM
    (α₀ : BoundaryManifold I M) (b : BoundaryManifold I M) :
    hI.boundaryE →L[ℝ] ℝ :=
  ((trivializationAt (E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] ℝ) (α₀ : M))
    ⟨(b : M), g.inner (b : M) (inwardCoordAt (M := M) α₀ b)⟩).2.comp
    (inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
      (mfderiv hI.boundaryI I (boundaryInclusion I M)) α₀ b)

/-- Smoothness of the chart-trivialised boundary functional at `α₀`. -/
private lemma boundaryFunOfInwardAtChartedCLM_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] ℝ) ∞
      (boundaryFunOfInwardAtChartedCLM (M := M) g α₀) α₀ := by
  -- Smoothness via composition of the chart-trivialised inner-product covector
  -- with the chart-conjugated dincl (each of which is smooth at α₀).
  have h_inwardCoord_section : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (inwardCoordAt (M := M) α₀ b)) α₀ :=
    inwardCoordAt_section_contMDiffAt (M := M) α₀
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) α₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  have h_g_section : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y : M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M =>
            TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          y (g.inner y)) := g.contMDiff
  have h_g_at : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M =>
            TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          (b : M) (g.inner (b : M))) α₀ :=
    h_g_section.contMDiffAt.comp α₀ h_inclusion_at
  have h_inner_applied : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun y : M => TangentSpace I y →L[ℝ] ℝ)
          (b : M)
          (g.inner (b : M) (inwardCoordAt (M := M) α₀ b))) α₀ :=
    h_g_at.clm_bundle_apply h_inwardCoord_section
  -- Extract chart-trivialised second component as a smooth `E →L[ℝ] ℝ`-valued function.
  have h_α_smooth : ContMDiffAt hI.boundaryI 𝓘(ℝ, E →L[ℝ] ℝ) ∞
      (fun b : BoundaryManifold I M =>
        ((trivializationAt (E →L[ℝ] ℝ)
            (fun y : M => TangentSpace I y →L[ℝ] ℝ) (α₀ : M))
          ⟨(b : M),
            g.inner (b : M) (inwardCoordAt (M := M) α₀ b)⟩).2) α₀ := by
    rw [Bundle.contMDiffAt_totalSpace] at h_inner_applied
    exact h_inner_applied.2
  -- Smoothness of the chart-conjugated dincl.
  have h_dincl_clm : ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] E) ∞
      (fun b : BoundaryManifold I M =>
        inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
          (mfderiv hI.boundaryI I (boundaryInclusion I M)) α₀ b) α₀ :=
    h_inclusion_at.mfderiv_const infty_le_top_add'
  exact h_α_smooth.clm_comp h_dincl_clm

/-- Pointwise application of the chart-trivialised boundary functional, on
the chart base sets. -/
private lemma boundaryFunOfInwardAtChartedCLM_apply_of_mem
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_amb : (b : M) ∈ (chartAt H (α₀ : M)).source)
    (hb_bdy : b ∈ (chartAt hI.boundaryH α₀).source)
    (w : hI.boundaryE) :
    boundaryFunOfInwardAtChartedCLM (M := M) g α₀ b w =
      g.inner (b : M) (inwardCoordAt (M := M) α₀ b)
        (dincl (M := M) b
          (((trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w)) := by
  -- Unfold the definition and compute step-by-step.
  unfold boundaryFunOfInwardAtChartedCLM
  rw [ContinuousLinearMap.coe_comp', Function.comp_apply]
  -- LHS now: `((triv-Dual α₀.val) ⟨b.val, g.inner b.val (inwardCoordAt α₀ b)⟩).2 (dinclITC α₀ b w)`.
  have h_amb_baseSet : (b : M) ∈ (trivializationAt E (TangentSpace I) (α₀ : M)).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hb_amb
  -- Apply `hom_trivializationAt_apply` to expose `inCoordinates`.
  rw [hom_trivializationAt_apply]
  -- The output bundle here is `Bundle.Trivial M ℝ`, with trivialisation that's the trivial one.
  -- The trivial bundle's `continuousLinearMapAt` is the identity (`Bundle.Trivial.linearMapAt_trivialization`).
  -- We compute `inCoordinates` directly via its definition + the trivial-bundle simplification.
  have h_inC :
      (ContinuousLinearMap.inCoordinates E (TangentSpace I) ℝ (fun _ : M => ℝ)
        (α₀ : M) (b : M) (α₀ : M) (b : M)
        (g.inner (b : M) (inwardCoordAt (M := M) α₀ b)))
        (inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
          (mfderiv hI.boundaryI I (boundaryInclusion I M)) α₀ b w) =
        g.inner (b : M) (inwardCoordAt (M := M) α₀ b)
          (dincl (M := M) b
            (((trivializationAt hI.boundaryE
                (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w)) := by
    -- Unfold `inCoordinates` and simplify.
    rw [ContinuousLinearMap.inCoordinates]
    rw [ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.coe_comp', Function.comp_apply]
    -- For trivial bundle ℝ, the clmAt is the identity.
    have h_trivial_clmAt : ∀ x : ℝ,
        (trivializationAt ℝ (fun _ : M => ℝ) (α₀ : M)).continuousLinearMapAt ℝ (b : M) x = x := by
      intro x
      change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ (b : M) x = x
      rw [Bundle.Trivial.continuousLinearMapAt_trivialization (𝕜 := ℝ) (B := M) (F := ℝ) (b : M)]
      rfl
    rw [h_trivial_clmAt]
    -- Use the dinclITC formula in unfolded form. Show the inner expression equals
    -- the chart-conjugated form first by congruence, then close via round-trip.
    have h_dinclITC_val :
        inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
            (mfderiv hI.boundaryI I (boundaryInclusion I M)) α₀ b w =
          (trivializationAt E (TangentSpace I) (α₀ : M)).continuousLinearMapAt ℝ
            (b : M) (dincl (M := M) b
              (((trivializationAt hI.boundaryE
                  (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w)) := by
      have := dinclITC_apply (M := M) α₀ hb_amb hb_bdy w
      unfold dinclITC at this
      exact this
    rw [h_dinclITC_val]
    -- `(triv-amb α₀.val).symmL b.val ∘ continuousLinearMapAt b.val = id` (round-trip).
    have h_amb_round :
        (((trivializationAt E (TangentSpace I) (α₀ : M)).symmL ℝ (b : M))
            ((trivializationAt E (TangentSpace I) (α₀ : M)).continuousLinearMapAt ℝ
              (b : M)
              (dincl (M := M) b
                (((trivializationAt hI.boundaryE
                    (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w)))) =
          dincl (M := M) b
            (((trivializationAt hI.boundaryE
                (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w) :=
      (trivializationAt E (TangentSpace I) (α₀ : M)).symmL_continuousLinearMapAt
        (R := ℝ) h_amb_baseSet (dincl (M := M) b
          (((trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w))
    rw [h_amb_round]
  exact h_inC

/-! ### Chart-trivialised boundary metric flat: explicit formula

We need an explicit formula for the chart-trivialised boundary metric flat
`boundaryFlatCharted α₀ b u v` in terms of `inducedMetricInner g b` and the
chart-conjugation `(triv-bdy α₀).symm b`. -/

/-- On the chart base sets, the chart-trivialised boundary metric flat
agrees with the bundle inner product through chart-conjugation. -/
private lemma boundaryFlatCharted_apply_of_mem
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_bdy : b ∈ (trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) α₀).baseSet)
    (u v : hI.boundaryE) :
    boundaryFlatCharted (M := M) g α₀ b u v =
      inducedMetricInner (M := M) g b
        ((trivializationAt hI.boundaryE
            (TangentSpace hI.boundaryI) α₀).symm b u)
        ((trivializationAt hI.boundaryE
            (TangentSpace hI.boundaryI) α₀).symm b v) := by
  -- Direct calculation via `hom_trivializationAt_apply` + `inCoordinates_apply_eq₂` for the
  -- Hom-trivialisation of the bilinear-form bundle.
  unfold boundaryFlatCharted
  rw [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ (𝕜 := ℝ) hb_bdy hb_bdy (Set.mem_univ _)]
  change (trivializationAt ℝ (Bundle.Trivial (BoundaryManifold I M) ℝ) α₀).linearMapAt ℝ b _ = _
  change (Bundle.Trivial.trivialization (BoundaryManifold I M) ℝ).linearMapAt ℝ b _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization (𝕜 := ℝ) (B := BoundaryManifold I M) (F := ℝ) b]
  -- LHS now: `inducedMetricInner g b (symm_bdy α₀ b u) (symm_bdy α₀ b v)` modulo notation.
  rfl

/-! ### Invertibility of the chart-trivialised boundary metric flat

The chart-trivialised boundary metric flat `boundaryFlatCharted α₀ b` is
invertible at every `b` in the boundary chart base set, since the underlying
`inducedMetricInner g b` is invertible (`inducedMetricInner_isInvertible`)
and `(triv-bdy α₀).symm b` is a continuous linear isomorphism on the base
set. -/

/-- Invertibility of the chart-trivialised boundary metric flat on the chart
base set. -/
private lemma boundaryFlatCharted_isInvertible_of_mem
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_bdy : b ∈ (trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) α₀).baseSet) :
    (boundaryFlatCharted (M := M) g α₀ b).IsInvertible := by
  -- We construct an explicit CLE witnessing invertibility.
  -- The chart-trivialised flat factorises as
  --   `boundaryFlatCharted α₀ b u v = inducedMetricInner g b (symm_bdy α₀ b u) (symm_bdy α₀ b v)`.
  -- = `(inducedMetricInner g b ∘L symm_bdy α₀ b) u (symm_bdy α₀ b v)`
  -- = `((inducedMetricInner g b (symm_bdy α₀ b u)) ∘L symm_bdy α₀ b) v`
  -- = `(((inducedMetricInner g b ∘L symm_bdy α₀ b) ∘L precomp(symm_bdy α₀ b)) u) v`. (Roughly.)
  --
  -- Concretely: the underlying CLM is the composition
  --   `(precomp by symm_bdy α₀ b) ∘L (inducedMetricInner g b) ∘L (symm_bdy α₀ b)`.
  -- Each factor is a CLE on the chart base set (using `continuousLinearEquivAt`), so the
  -- composition is also a CLE.
  classical
  obtain ⟨L_cle, hL_eq⟩ := inducedMetricInner_isInvertible (M := M) g b
  -- L_cle : hI.boundaryE ≃L[ℝ] (hI.boundaryE →L[ℝ] ℝ).
  let T : hI.boundaryE ≃L[ℝ] hI.boundaryE :=
    (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearEquivAt ℝ b
      hb_bdy
  -- Compose: `φ := T.symm ∘L L_cle ∘L (T.arrowCongr (refl ℝ))` to get the chart-conjugated
  -- inner product as a CLE, then check it equals `boundaryFlatCharted α₀ b`.
  let φ : hI.boundaryE ≃L[ℝ] (hI.boundaryE →L[ℝ] ℝ) :=
    T.symm.trans (L_cle.trans (T.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)))
  refine ⟨φ, ?_⟩
  -- Show `(φ : boundaryE →L[ℝ] (boundaryE →L[ℝ] ℝ)) = boundaryFlatCharted α₀ b`.
  ext u v
  -- LHS: `(T.arrowCongr (refl ℝ) (L_cle (T.symm u))) v`.
  change ((T.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (L_cle (T.symm u))) v = _
  simp only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.refl_apply]
  -- LHS: `L_cle (T.symm u) (T.symm v)`. (`arrowCongr (refl ℝ)` sends `α ↦ α ∘L T.symm`.)
  -- Substitute `(L_cle : ...) = inducedMetricInner g b`.
  have h_eq_LCle : (L_cle : hI.boundaryE →L[ℝ] (hI.boundaryE →L[ℝ] ℝ)) =
      inducedMetricInner (M := M) g b := hL_eq
  have h_lhs : L_cle (T.symm u) (T.symm v) =
      inducedMetricInner (M := M) g b (T.symm u) (T.symm v) := by
    rw [show L_cle (T.symm u) (T.symm v) =
        (L_cle : hI.boundaryE →L[ℝ] (hI.boundaryE →L[ℝ] ℝ)) (T.symm u) (T.symm v) from rfl]
    rw [h_eq_LCle]
  rw [h_lhs]
  -- T.symm corresponds to symm_bdy α₀ b.
  have h_T_symm_u : (T.symm u : hI.boundaryE) =
      (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symm b u := rfl
  have h_T_symm_v : (T.symm v : hI.boundaryE) =
      (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symm b v := rfl
  rw [h_T_symm_u, h_T_symm_v]
  -- RHS: `boundaryFlatCharted α₀ b u v = inducedMetricInner g b (symm_bdy α₀ b u) (symm_bdy α₀ b v)`.
  rw [boundaryFlatCharted_apply_of_mem (M := M) g α₀ hb_bdy u v]

/-! ### Chart-trivialised boundary component of the inward direction -/

/-- The chart-trivialised boundary component of the inward direction. -/
private noncomputable def boundaryComponentOfInwardAtCharted
    (α₀ : BoundaryManifold I M) (b : BoundaryManifold I M) : hI.boundaryE :=
  (boundaryFlatChartedInv (M := M) g α₀ b)
    (boundaryFunOfInwardAtChartedCLM (M := M) g α₀ b)

/-- Smoothness of the chart-trivialised boundary component at `α₀`. -/
private lemma boundaryComponentOfInwardAtCharted_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE) ∞
      (boundaryComponentOfInwardAtCharted (M := M) g α₀) α₀ :=
  (boundaryFlatChartedInv_contMDiffAt (M := M) g α₀).clm_apply
    (boundaryFunOfInwardAtChartedCLM_contMDiffAt (M := M) g α₀)

/-! ### Identification of chart-trivialised boundary component with the bundle quantity

On the chart base sets, the chart-trivialised boundary component
`boundaryComponentOfInwardAtCharted α₀ g b` equals the chart-trivialisation
image of the bundle boundary component:
`(triv-bdy α₀).continuousLinearMapAt ℝ b (boundaryComponentOfInwardAt α₀ g b)`.

The proof uses uniqueness from invertibility of `boundaryFlatCharted α₀ b`. -/

/-- The defining identity for the bundle boundary component, recast in chart-
trivialised form: applying `boundaryFlatCharted α₀ b` to
`(triv-bdy α₀).continuousLinearMapAt ℝ b (boundaryComponentOfInwardAt α₀ g b)`
yields the chart-trivialised boundary functional. -/
private lemma boundaryFlatCharted_clmAt_bdy_BC_eq
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_amb : (b : M) ∈ (chartAt H (α₀ : M)).source)
    (hb_bdy : b ∈ (chartAt hI.boundaryH α₀).source) :
    boundaryFlatCharted (M := M) g α₀ b
      ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearMapAt
        ℝ b (boundaryComponentOfInwardAt (M := M) g α₀ b)) =
      boundaryFunOfInwardAtChartedCLM (M := M) g α₀ b := by
  refine ContinuousLinearMap.ext fun v => ?_
  -- Apply both sides to `v : boundaryE`.
  have hb_bdy_baseSet : b ∈ (trivializationAt hI.boundaryE
      (TangentSpace hI.boundaryI) α₀).baseSet := hb_bdy
  -- LHS: `boundaryFlatCharted α₀ b (clmAt_bdy α₀ b BC) v`.
  rw [boundaryFlatCharted_apply_of_mem (M := M) g α₀ hb_bdy_baseSet
    ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearMapAt
        ℝ b (boundaryComponentOfInwardAt (M := M) g α₀ b)) v]
  -- After rewrite: `inducedMetricInner g b (symm_bdy α₀ b (clmAt_bdy α₀ b BC)) (symm_bdy α₀ b v)`.
  -- Simplify the inner argument via round-trip: `symm_bdy α₀ b (clmAt_bdy α₀ b BC) = BC`.
  have h_round_BC :
      ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symm b
          ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearMapAt
            ℝ b (boundaryComponentOfInwardAt (M := M) g α₀ b))) =
        boundaryComponentOfInwardAt (M := M) g α₀ b := by
    have := (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symmL_continuousLinearMapAt
      (R := ℝ) hb_bdy_baseSet (boundaryComponentOfInwardAt (M := M) g α₀ b)
    simpa using this
  rw [h_round_BC]
  -- Now LHS: `inducedMetricInner g b BC (symm_bdy α₀ b v)`.
  -- Use the defining identity:
  --   `inducedMetricInner g b BC w = g.inner b.val (inwardCoordAt α₀ b) (dincl b w)`.
  rw [inducedMetricInner_boundaryComponentOfInwardAt (M := M) g α₀ b
    ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symm b v)]
  -- Now LHS: `g.inner b.val (inwardCoordAt α₀ b) (dincl b (symm_bdy α₀ b v))`.
  -- RHS via `boundaryFunOfInwardAtChartedCLM_apply_of_mem`:
  rw [boundaryFunOfInwardAtChartedCLM_apply_of_mem (M := M) g α₀ hb_amb hb_bdy v]
  -- Now both sides are: `g.inner b.val (inwardCoordAt α₀ b) (dincl b (symm_bdy α₀ b v))`.
  -- The `symm` and `symmL` coercions are equal.
  rfl

/-- The chart-trivialised boundary component agrees with the chart-image of
the bundle boundary component on the chart base sets. -/
private lemma boundaryComponentOfInwardAtCharted_eq
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_amb : (b : M) ∈ (chartAt H (α₀ : M)).source)
    (hb_bdy : b ∈ (chartAt hI.boundaryH α₀).source) :
    boundaryComponentOfInwardAtCharted (M := M) g α₀ b =
      (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearMapAt
        ℝ b (boundaryComponentOfInwardAt (M := M) g α₀ b) := by
  unfold boundaryComponentOfInwardAtCharted boundaryFlatChartedInv
  -- Use invertibility-based uniqueness: `inverse A (A x) = x` when A is invertible.
  have h_inv := boundaryFlatCharted_isInvertible_of_mem (M := M) g α₀ hb_bdy
  have h_eq := boundaryFlatCharted_clmAt_bdy_BC_eq (M := M) g α₀ hb_amb hb_bdy
  rw [← h_eq]
  exact (ContinuousLinearMap.IsInvertible.inverse_apply_eq h_inv).mpr rfl

/-! ### Chart-trivialised inward tangential part as a smooth `E`-valued function

The chart-trivialised second component of `inwardTangentialPartAt α₀ g b`,
defined as `dinclITC α₀ b (boundaryComponentOfInwardAtCharted α₀ g b)`, is
`C^∞` at `α₀` and equals
`(triv-amb at α₀.val).continuousLinearMapAt ℝ b.val (inwardTangentialPartAt α₀ g b)`
on the chart base sets. -/

/-- Smoothness of `b ↦ dinclITC α₀ b (boundaryComponentOfInwardAtCharted α₀ g b)` at `α₀`. -/
private lemma inwardTangentialPartAtCharted_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
      (fun b : BoundaryManifold I M =>
        dinclITC (M := M) α₀ b (boundaryComponentOfInwardAtCharted (M := M) g α₀ b)) α₀ :=
  dinclITC_apply_contMDiffAt (M := M)
    (boundaryComponentOfInwardAtCharted_contMDiffAt (M := M) g α₀)

/-- On the chart base sets, the chart-trivialised inward tangential part agrees with
the chart-trivialised second component of the bundle inward tangential part. -/
private lemma inwardTangentialPartAtCharted_eq
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_amb : (b : M) ∈ (chartAt H (α₀ : M)).source)
    (hb_bdy : b ∈ (chartAt hI.boundaryH α₀).source) :
    dinclITC (M := M) α₀ b (boundaryComponentOfInwardAtCharted (M := M) g α₀ b) =
      (trivializationAt E (TangentSpace I) (α₀ : M)).continuousLinearMapAt ℝ
        (b : M) (inwardTangentialPartAt (M := M) g α₀ b) := by
  -- LHS: `dinclITC α₀ b BCC = clmAt_amb α₀ b.val (dincl b (symmL_bdy α₀ b BCC))`.
  -- Substitute `BCC = clmAt_bdy α₀ b BCBundle`. Round-trip: `symmL_bdy ∘ clmAt_bdy = id`.
  -- LHS becomes: `clmAt_amb α₀ b.val (dincl b BCBundle) = clmAt_amb α₀ b.val (inwardTangentialPartAt α₀ g b)`.
  rw [dinclITC_apply (M := M) α₀ hb_amb hb_bdy]
  rw [boundaryComponentOfInwardAtCharted_eq (M := M) g α₀ hb_amb hb_bdy]
  -- After: `clmAt_amb α₀ b.val (dincl b (symmL_bdy α₀ b (clmAt_bdy α₀ b BC))) =
  --         clmAt_amb α₀ b.val (inwardTangentialPartAt α₀ g b)`.
  have hb_bdy_baseSet : b ∈ (trivializationAt hI.boundaryE
      (TangentSpace hI.boundaryI) α₀).baseSet := hb_bdy
  have h_round_bdy :
      (((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symmL ℝ b)
          ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearMapAt
            ℝ b (boundaryComponentOfInwardAt (M := M) g α₀ b))) =
        boundaryComponentOfInwardAt (M := M) g α₀ b := by
    have := (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symmL_continuousLinearMapAt
      (R := ℝ) hb_bdy_baseSet (boundaryComponentOfInwardAt (M := M) g α₀ b)
    simpa using this
  rw [h_round_bdy]
  rfl

/-! ### Smoothness of the bundle section `b ↦ ⟨b.val, outwardDirAt α₀ g b⟩` at α₀

Using the chart-trivialised quantities and `Trivialization.contMDiffAt_iff`,
we show smoothness of the bundle outward direction section at α₀. -/

/-- Smoothness of `b ↦ TotalSpace.mk' E b.val (outwardDirAt α₀ g b)` at `α₀`. -/
private lemma outwardDirAt_section_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (outwardDirAt (M := M) g α₀ b)) α₀ := by
  classical
  -- Use `Trivialization.contMDiffAt_iff` to reduce to chart-trivialised form.
  set T_amb := trivializationAt E (TangentSpace I) (α₀ : M) with hT_amb_def
  have hα_amb : (α₀ : M) ∈ T_amb.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (α₀ : M)
  refine (T_amb.contMDiffAt_iff (n := ∞)
    (f := fun b : BoundaryManifold I M =>
      TotalSpace.mk' E (b : M) (outwardDirAt (M := M) g α₀ b))
    (IM := hI.boundaryI) (x₀ := α₀) ?_).mpr ?_
  · change (TotalSpace.mk' E (α₀ : M)
      (outwardDirAt (M := M) g α₀ α₀)) ∈ T_amb.source
    rw [Trivialization.mem_source]
    change (α₀ : M) ∈ T_amb.baseSet
    simp only [hT_amb_def]
    exact FiberBundle.mem_baseSet_trivializationAt' (α₀ : M)
  refine ⟨?_, ?_⟩
  · -- proj-component is `boundaryInclusion`, smooth.
    convert (boundaryInclusion_contMDiff (I := I) (M := M)).contMDiffAt using 1
  · -- chart-trivialised second component:
    -- `(T_amb ⟨b.val, outwardDirAt α₀ g b⟩).2`
    -- = `T_amb.continuousLinearMapAt ℝ b.val (outwardDirAt α₀ g b)`
    -- = `T_amb.continuousLinearMapAt ℝ b.val (inwardTangentialPartAt α₀ g b - inwardCoordAt α₀ b)`
    -- = `(T_amb.continuousLinearMapAt ℝ b.val (inwardTangentialPartAt α₀ g b))
    --      - (T_amb.continuousLinearMapAt ℝ b.val (inwardCoordAt α₀ b))`
    -- = `(dinclITC α₀ b BCC) - inwardCoordE` (using identifications above).
    have h_inwardTangChart_at : ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
        (fun b : BoundaryManifold I M =>
          dinclITC (M := M) α₀ b (boundaryComponentOfInwardAtCharted (M := M) g α₀ b)) α₀ :=
      inwardTangentialPartAtCharted_contMDiffAt (M := M) g α₀
    have h_const : ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
        (fun _ : BoundaryManifold I M => hI.inwardCoordE) α₀ := contMDiffAt_const
    have h_sub : ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
        (fun b : BoundaryManifold I M =>
          dinclITC (M := M) α₀ b (boundaryComponentOfInwardAtCharted (M := M) g α₀ b) -
            hI.inwardCoordE) α₀ :=
      h_inwardTangChart_at.sub h_const
    refine h_sub.congr_of_eventuallyEq ?_
    -- Show eventually `(T_amb ⟨b.val, outwardDirAt α₀ g b⟩).2 = dinclITC α₀ b BCC - inwardCoordE`.
    have h_nhds_amb : ∀ᶠ b : BoundaryManifold I M in 𝓝 α₀,
        (b : M) ∈ (chartAt H (α₀ : M)).source := by
      have h_continuous : Continuous (fun b : BoundaryManifold I M => (b : M)) :=
        continuous_subtype_val
      exact h_continuous.continuousAt.preimage_mem_nhds
        ((chartAt H (α₀ : M)).open_source.mem_nhds (mem_chart_source H _))
    have h_nhds_bdy : ∀ᶠ b : BoundaryManifold I M in 𝓝 α₀,
        b ∈ (chartAt hI.boundaryH α₀).source :=
      (chartAt hI.boundaryH α₀).open_source.mem_nhds (mem_chart_source _ _)
    filter_upwards [h_nhds_amb, h_nhds_bdy] with b hb_amb hb_bdy
    -- Goal: `dinclITC α₀ b BCC - inwardCoordE = (T_amb ⟨b.val, outwardDirAt α₀ g b⟩).2`.
    have hb_amb_baseSet : (b : M) ∈ T_amb.baseSet := by
      simp only [hT_amb_def]
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact hb_amb
    -- Step 1: `(T_amb ⟨b.val, outwardDirAt α₀ g b⟩).2 = T_amb.continuousLinearMapAt ℝ b.val (outwardDirAt α₀ g b)`.
    rw [show (T_amb ⟨(b : M), outwardDirAt (M := M) g α₀ b⟩).2 =
        T_amb.continuousLinearMapAt ℝ (b : M) (outwardDirAt (M := M) g α₀ b) from ?_]
    swap
    · rw [Trivialization.continuousLinearMapAt_apply]
      rw [T_amb.coe_linearMapAt_of_mem hb_amb_baseSet]
    -- Step 2: `outwardDirAt α₀ g b = inwardTangentialPartAt α₀ g b - inwardCoordAt α₀ b`.
    rw [outwardDirAt_def, map_sub]
    -- LHS: `T_amb.continuousLinearMapAt ℝ b.val (inwardTangentialPartAt α₀ g b)
    --      - T_amb.continuousLinearMapAt ℝ b.val (inwardCoordAt α₀ b)`.
    -- = `(dinclITC α₀ b BCC) - inwardCoordE` (using identifications).
    rw [← inwardTangentialPartAtCharted_eq (M := M) g α₀ hb_amb hb_bdy]
    -- Now LHS: `dinclITC α₀ b BCC - clmAt_amb α₀ b.val (inwardCoordAt α₀ b)`.
    have h_inwardCoord_chartTriv :
        T_amb.continuousLinearMapAt ℝ (b : M) (inwardCoordAt (M := M) α₀ b) =
          hI.inwardCoordE := by
      rw [show T_amb.continuousLinearMapAt ℝ (b : M) (inwardCoordAt (M := M) α₀ b) =
          (T_amb ⟨(b : M), inwardCoordAt (M := M) α₀ b⟩).2 from ?_]
      · simp only [hT_amb_def]
        exact chart_triv_second_inwardCoordAt (M := M) α₀ hb_amb_baseSet
      · rw [Trivialization.continuousLinearMapAt_apply]
        rw [T_amb.coe_linearMapAt_of_mem hb_amb_baseSet]
    rw [h_inwardCoord_chartTriv]

/-! ### Smoothness of the squared `g`-norm of `outwardDirAt`

The function `b ↦ g.inner b.val (outwardDirAt α₀ g b) (outwardDirAt α₀ g b) : ℝ`
is `C^∞` at `α₀`. -/

/-- Smoothness of the squared `g`-norm of `outwardDirAt α₀ g b` at `α₀`. -/
private lemma outwardDirAt_norm_squared_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ) ∞
      (fun b : BoundaryManifold I M =>
        g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b)) α₀ := by
  classical
  have h_outwardDir_section : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (outwardDirAt (M := M) g α₀ b)) α₀ :=
    outwardDirAt_section_contMDiffAt (M := M) g α₀
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) α₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  have h_g_section : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y : M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M =>
            TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          y (g.inner y)) := g.contMDiff
  have h_g_at : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M =>
            TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          (b : M) (g.inner (b : M))) α₀ :=
    h_g_section.contMDiffAt.comp α₀ h_inclusion_at
  -- Apply `clm_bundle_apply₂` for the bilinear-form section evaluated at two smooth sections.
  have h_apply : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' ℝ (E := fun y : M => ℝ)
          (b : M)
          (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
            (outwardDirAt (M := M) g α₀ b))) α₀ :=
    h_g_at.clm_bundle_apply₂ h_outwardDir_section h_outwardDir_section
  rw [Bundle.contMDiffAt_totalSpace] at h_apply
  exact h_apply.2

/-! ### Positivity of the squared `g`-norm at the basepoint -/

/-- The squared `g`-norm of `outwardDirAt α₀ g α₀` is strictly positive. -/
private lemma outwardDirAt_norm_squared_pos_basepoint
    (α₀ : BoundaryManifold I M) :
    0 < g.inner (α₀ : M) (outwardDirAt (M := M) g α₀ α₀)
        (outwardDirAt (M := M) g α₀ α₀) := by
  rw [outwardDirAt_self (M := M) g α₀]
  exact g_inner_outwardDir_pos (M := M) g α₀

/-! ### Smoothness of the parameterised outward unit normal as a section

The outward unit normal `outwardNormalAt α₀ g b` equals
`(Real.sqrt (q b))⁻¹ • outwardDirAt α₀ g b` where `q b` is the squared
`g`-norm. Smoothness at `α₀` follows from smoothness of each factor:
`q` is smooth and positive at `α₀`, so its square root and reciprocal are
smooth at `α₀`; and `outwardDirAt` is smooth at `α₀` as a section. -/

/-- Smoothness of the parameterised outward unit normal section at `α₀`.

This is the chart-α-local smoothness result. The section
`b ↦ TotalSpace.mk' E b.val (outwardNormalAt α₀ g b)` is `C^∞` at `α₀`. -/
theorem outwardNormalAt_section_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (outwardNormalAt (M := M) g α₀ b)) α₀ := by
  classical
  -- The squared norm is smooth and strictly positive at α₀.
  have h_q_smooth : ContMDiffAt hI.boundaryI 𝓘(ℝ) ∞
      (fun b : BoundaryManifold I M =>
        g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b)) α₀ :=
    outwardDirAt_norm_squared_contMDiffAt (M := M) g α₀
  have h_q_pos_at : 0 < g.inner (α₀ : M) (outwardDirAt (M := M) g α₀ α₀)
      (outwardDirAt (M := M) g α₀ α₀) :=
    outwardDirAt_norm_squared_pos_basepoint (M := M) g α₀
  have h_q_ne : g.inner (α₀ : M) (outwardDirAt (M := M) g α₀ α₀)
      (outwardDirAt (M := M) g α₀ α₀) ≠ 0 := ne_of_gt h_q_pos_at
  -- `Real.sqrt (q b)` smooth at α₀ via `ContDiffAt.sqrt`.
  have h_q_sqrt_at : ContMDiffAt hI.boundaryI 𝓘(ℝ) ∞
      (fun b : BoundaryManifold I M =>
        Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b))) α₀ := by
    have h_sqrt_at : ContDiffAt ℝ ∞ Real.sqrt
        (g.inner (α₀ : M) (outwardDirAt (M := M) g α₀ α₀)
          (outwardDirAt (M := M) g α₀ α₀)) := Real.contDiffAt_sqrt h_q_ne
    exact h_sqrt_at.contMDiffAt.comp α₀ h_q_smooth
  have h_sqrt_pos : 0 < Real.sqrt (g.inner (α₀ : M)
      (outwardDirAt (M := M) g α₀ α₀)
      (outwardDirAt (M := M) g α₀ α₀)) := Real.sqrt_pos.mpr h_q_pos_at
  have h_sqrt_ne : Real.sqrt (g.inner (α₀ : M) (outwardDirAt (M := M) g α₀ α₀)
      (outwardDirAt (M := M) g α₀ α₀)) ≠ 0 := ne_of_gt h_sqrt_pos
  have h_sqrt_inv_at : ContMDiffAt hI.boundaryI 𝓘(ℝ) ∞
      (fun b : BoundaryManifold I M =>
        (Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b)))⁻¹) α₀ :=
    h_q_sqrt_at.inv₀ h_sqrt_ne
  have h_outwardDir_section : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (outwardDirAt (M := M) g α₀ b)) α₀ :=
    outwardDirAt_section_contMDiffAt (M := M) g α₀
  -- Use `Trivialization.contMDiffAt_iff` to reduce to chart-trivialised form, where we use
  -- `ContMDiffAt.smul`.
  set T_amb := trivializationAt E (TangentSpace I) (α₀ : M) with hT_amb_def
  have hα_amb : (α₀ : M) ∈ T_amb.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (α₀ : M)
  refine (T_amb.contMDiffAt_iff (n := ∞)
    (f := fun b : BoundaryManifold I M =>
      TotalSpace.mk' E (b : M) (outwardNormalAt (M := M) g α₀ b))
    (IM := hI.boundaryI) (x₀ := α₀) ?_).mpr ?_
  · change (TotalSpace.mk' E (α₀ : M)
      (outwardNormalAt (M := M) g α₀ α₀)) ∈ T_amb.source
    rw [Trivialization.mem_source]
    change (α₀ : M) ∈ T_amb.baseSet
    simp only [hT_amb_def]
    exact FiberBundle.mem_baseSet_trivializationAt' (α₀ : M)
  refine ⟨?_, ?_⟩
  · convert (boundaryInclusion_contMDiff (I := I) (M := M)).contMDiffAt using 1
  · -- Chart-trivialised second component is `(sqrt q)⁻¹ • clmAt b.val (outwardDirAt α₀ g b)`,
    -- which is smooth at α₀.
    have h_outwardDirCharted_at : ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
        (fun b : BoundaryManifold I M =>
          (T_amb ⟨(b : M), outwardDirAt (M := M) g α₀ b⟩).2) α₀ := by
      rw [Bundle.contMDiffAt_totalSpace] at h_outwardDir_section
      exact h_outwardDir_section.2
    have h_smul_smooth : ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
        (fun b : BoundaryManifold I M =>
          (Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
            (outwardDirAt (M := M) g α₀ b)))⁻¹ •
            (T_amb ⟨(b : M), outwardDirAt (M := M) g α₀ b⟩).2) α₀ :=
      h_sqrt_inv_at.smul h_outwardDirCharted_at
    refine h_smul_smooth.congr_of_eventuallyEq ?_
    -- On a positive-norm neighbourhood (open, contains α₀), the chart-trivialised second component
    -- of `outwardNormalAt α₀ g b` equals the smooth expression.
    have h_q_continuous : ContinuousAt
        (fun b : BoundaryManifold I M =>
          g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
            (outwardDirAt (M := M) g α₀ b)) α₀ := h_q_smooth.continuousAt
    have h_q_pos_nhds : ∀ᶠ b : BoundaryManifold I M in 𝓝 α₀,
        0 < g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b) := by
      filter_upwards [h_q_continuous (eventually_gt_nhds h_q_pos_at)] with b hb
      exact hb
    have h_nhds_amb : ∀ᶠ b : BoundaryManifold I M in 𝓝 α₀,
        (b : M) ∈ T_amb.baseSet := by
      have h_continuous : Continuous (fun b : BoundaryManifold I M => (b : M)) :=
        continuous_subtype_val
      exact h_continuous.continuousAt.preimage_mem_nhds (T_amb.open_baseSet.mem_nhds hα_amb)
    filter_upwards [h_q_pos_nhds, h_nhds_amb] with b hb_q_pos hb_amb_baseSet
    -- Goal: `(sqrt q b)⁻¹ • (T_amb ⟨b.val, outwardDirAt α₀ g b⟩).2
    --        = (T_amb ⟨b.val, outwardNormalAt α₀ g b⟩).2`.
    -- Use `outwardNormalAt α₀ g b = (sqrt q b)⁻¹ • outwardDirAt α₀ g b` (positivity).
    have h_norm_formula : outwardNormalAt (M := M) g α₀ b =
        (Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
            (outwardDirAt (M := M) g α₀ b)))⁻¹ • outwardDirAt (M := M) g α₀ b := by
      unfold outwardNormalAt
      rw [dif_pos hb_q_pos]
    -- LHS: `(sqrt q b)⁻¹ • (T_amb ⟨b.val, outwardDirAt α₀ g b⟩).2`.
    -- RHS: `(T_amb ⟨b.val, outwardNormalAt α₀ g b⟩).2 = (T_amb ⟨b.val, (sqrt q b)⁻¹ • outwardDirAt α₀ g b⟩).2`.
    -- = `T_amb.continuousLinearMapAt ℝ b.val ((sqrt q b)⁻¹ • outwardDirAt α₀ g b)
    --    = (sqrt q b)⁻¹ • T_amb.continuousLinearMapAt ℝ b.val (outwardDirAt α₀ g b)`
    -- = `(sqrt q b)⁻¹ • (T_amb ⟨b.val, outwardDirAt α₀ g b⟩).2`. (LHS.)
    rw [h_norm_formula]
    rw [show (T_amb ⟨(b : M), (Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b)))⁻¹ • outwardDirAt (M := M) g α₀ b⟩).2 =
        T_amb.continuousLinearMapAt ℝ (b : M)
          ((Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
            (outwardDirAt (M := M) g α₀ b)))⁻¹ • outwardDirAt (M := M) g α₀ b) from ?_]
    swap
    · rw [Trivialization.continuousLinearMapAt_apply]
      rw [T_amb.coe_linearMapAt_of_mem hb_amb_baseSet]
    rw [map_smul]
    rw [show (T_amb ⟨(b : M), outwardDirAt (M := M) g α₀ b⟩).2 =
        T_amb.continuousLinearMapAt ℝ (b : M) (outwardDirAt (M := M) g α₀ b) from ?_]
    · rw [Trivialization.continuousLinearMapAt_apply]
      rw [T_amb.coe_linearMapAt_of_mem hb_amb_baseSet]

/-! ### Chart-α-local smoothness: `ContMDiffOn` form

We deduce a `ContMDiffOn` form on the open subset of the boundary
trivialisation base set where the squared `g`-norm is strictly positive.
This subset is open (the squared norm is continuous, and the positivity
locus is open); it contains `α₀`.

Note: positivity of the squared norm on the *full* boundary trivialisation
base set requires identifying `inwardCoordAt α₀ b` with `inwardCoord b` (which
is always transverse), but in general the two differ for `b ≠ α₀`. We thus
state the `ContMDiffOn` result on the (smaller, open) positivity locus,
which contains `α₀`. -/

/-- The open positivity locus inside the boundary chart base set. This is the
(open) subset of points where `outwardDirAt α₀ g b` has strictly positive
squared `g`-norm. It is non-empty (contains `α₀`). -/
private def positivityLocus
    (α₀ : BoundaryManifold I M) : Set (BoundaryManifold I M) :=
  (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet ∩
    {b : BoundaryManifold I M |
      0 < g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
        (outwardDirAt (M := M) g α₀ b)}

/-! ## Dimension of the `g`-normal subspace and chart-invariance helpers

The boundary tangent subspace `range (dincl y)` has dimension `n-1`, and its
`g`-orthogonal complement `normalSubspace g y` therefore has dimension exactly
`1` in the ambient `n`-dimensional tangent space. The argument is:

* The metric pull-back covector map
  `metricPullback g y : T_y M →ₗ[ℝ] (boundaryE →ₗ[ℝ] ℝ)`
  has kernel equal to `normalSubspace g y`.
* It is *surjective* onto `boundaryE →ₗ[ℝ] ℝ`: for any covector `α` on the
  boundary, the boundary-level metric flat (`boundaryFlatMap`) provides a
  unique `u : boundaryE` with `inducedMetric(u, w) = α(w)`; setting
  `v := dincl y u : T_y M` gives `metricPullback g y v = α`.
* By rank-nullity, `dim ker = dim T_y M - dim image = n - (n-1) = 1`.

This is the key dimensional input to the chart-invariance argument for the
outward unit normal. -/

/-- The metric pull-back covector map is surjective: every linear functional
on `boundaryE` arises as `w ↦ g.inner y v (dincl y w)` for some `v ∈ T_y M`. -/
private lemma metricPullback_surjective
    (g : Measure.SmoothRiemannianMetric I M) (y : BoundaryManifold I M) :
    Function.Surjective (metricPullback (M := M) g y) := by
  intro α
  -- Given `α : boundaryE →ₗ[ℝ] ℝ`, set `u := boundaryFlatMap.symm α : boundaryE`,
  -- then `v := dincl y u : T_y M`.
  set u : hI.boundaryE := (boundaryFlatMap (M := M) g y).symm α with hu_def
  refine ⟨dincl (M := M) y u, ?_⟩
  -- Goal: `metricPullback g y (dincl y u) = α`.
  -- For each `w : boundaryE`, both sides give `g.inner y (dincl y u) (dincl y w)`.
  refine LinearMap.ext fun w => ?_
  -- `metricPullback g y v w = g.inner y v (dincl y w)`.
  rw [metricPullback_apply]
  -- Now LHS: `g.inner y (dincl y u) (dincl y w) = inducedMetricInner g y u w`.
  rw [show g.inner (y : M) (dincl (M := M) y u) (dincl (M := M) y w) =
        inducedMetricInner (M := M) g y u w from
        (inducedMetricInner_apply g y u w).symm]
  -- `inducedMetricInner g y u w = boundaryFlatMap g y u w = α w` by `boundaryFlatMap_apply_symm`.
  rw [show inducedMetricInner (M := M) g y u w = boundaryFlatMap (M := M) g y u w from rfl]
  -- `boundaryFlatMap _ ((boundaryFlatMap _ ).symm α) w = α w`.
  have h := (boundaryFlatMap (M := M) g y).apply_symm_apply α
  -- `h : boundaryFlatMap g y u = α` (where `u = (boundaryFlatMap g y).symm α`).
  exact congrArg (fun L : hI.boundaryE →ₗ[ℝ] ℝ => L w) h

/-- The kernel of the metric pull-back covector map has finrank `1`. -/
private lemma finrank_ker_metricPullback_eq_one
    (g : Measure.SmoothRiemannianMetric I M) (y : BoundaryManifold I M) :
    Module.finrank ℝ (LinearMap.ker (metricPullback (M := M) g y)) = 1 := by
  by_cases hN : Nonempty hI.boundaryH
  · haveI := hN
    -- By rank-nullity: `finrank (range f) + finrank (ker f) = finrank (source)`.
    -- Source: `T_y M = E`. Range: surjective onto `boundaryE →ₗ[ℝ] ℝ`, finrank = finrank boundaryE.
    -- finrank E = finrank boundaryE + 1 (codim-1).
    have h_rk_null :=
      LinearMap.finrank_range_add_finrank_ker (metricPullback (M := M) g y)
    -- Surjectivity gives `range f = ⊤`, hence `finrank (range f) = finrank (codomain)`.
    have h_surj : Function.Surjective (metricPullback (M := M) g y) :=
      metricPullback_surjective (M := M) g y
    have h_range_top : LinearMap.range (metricPullback (M := M) g y) = ⊤ :=
      LinearMap.range_eq_top.mpr h_surj
    -- `finrank (range f) = finrank (boundaryE →ₗ[ℝ] ℝ)` via `range = ⊤`.
    have h_finrank_range : Module.finrank ℝ
        (LinearMap.range (metricPullback (M := M) g y)) =
        Module.finrank ℝ (hI.boundaryE →ₗ[ℝ] ℝ) := by
      rw [h_range_top, finrank_top]
    -- `finrank (boundaryE →ₗ[ℝ] ℝ) = finrank boundaryE`.
    have h_dual : Module.finrank ℝ (hI.boundaryE →ₗ[ℝ] ℝ) =
        Module.finrank ℝ hI.boundaryE := Subspace.dual_finrank_eq
    -- `finrank (source) = finrank (TangentSpace I y) = finrank E`.
    have h_source : Module.finrank ℝ (TangentSpace I (y : M)) = Module.finrank ℝ E := rfl
    -- Codim-1 condition.
    have h_codim : Module.finrank ℝ hI.boundaryE + 1 = Module.finrank ℝ E :=
      hI.finrank_boundaryE_succ
    -- Assemble.
    rw [h_finrank_range, h_dual] at h_rk_null
    -- `h_rk_null : finrank boundaryE + finrank (ker f) = finrank E`.
    -- `h_codim : finrank boundaryE + 1 = finrank E`.
    -- Subtract: `finrank (ker f) = 1`.
    omega
  · haveI : IsEmpty hI.boundaryH := not_nonempty_iff.mp hN
    haveI : IsEmpty (BoundaryManifold I M) :=
      BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
    exact (IsEmpty.false y).elim

/-- **Block 1.** The `g`-orthogonal normal subspace at a boundary point is
exactly one-dimensional. -/
theorem normalSubspace_finrank_one
    (g : Measure.SmoothRiemannianMetric I M) (y : BoundaryManifold I M) :
    Module.finrank ℝ (normalSubspace (M := M) g y) = 1 := by
  rw [← ker_metricPullback_eq_normalSubspace (M := M) g y]
  exact finrank_ker_metricPullback_eq_one (M := M) g y

/-! ## Two unit vectors in a one-dimensional submodule are equal up to sign

In a 1-dimensional subspace `V` of an inner-product-equipped space `T_y M`,
two vectors with the same `g`-length-squared `1` differ at most by a sign. -/

/-- **Block 2.** Any two unit-`g`-length vectors in a 1-dimensional submodule
are equal or opposite. -/
private lemma unit_vectors_in_1dim_equal_or_opposite
    (g : Measure.SmoothRiemannianMetric I M) {y : BoundaryManifold I M}
    {V : Submodule ℝ (TangentSpace I (y : M))}
    (hV : Module.finrank ℝ V = 1)
    {v w : TangentSpace I (y : M)} (hv : v ∈ V) (hw : w ∈ V)
    (hv_unit : g.inner (y : M) v v = 1) (hw_unit : g.inner (y : M) w w = 1) :
    v = w ∨ v = -w := by
  classical
  -- Lift to subtype-elements and use `exists_smul_eq_of_finrank_eq_one`.
  let v' : V := ⟨v, hv⟩
  let w' : V := ⟨w, hw⟩
  -- `v` is non-zero (otherwise `g(v,v) = 0 ≠ 1`).
  have hv_ne : v ≠ 0 := by
    intro h0
    rw [h0] at hv_unit
    -- `g.inner y 0 0 = 0`.
    simp at hv_unit
  have hv'_ne : v' ≠ 0 := by
    intro h0
    apply hv_ne
    exact congrArg Subtype.val h0
  -- Get scalar c with `c • v' = w'`.
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_finrank_eq_one (K := ℝ) (V := V) hV hv'_ne w'
  -- Project to ambient: `c • v = w`.
  have hc_amb : c • v = w := by
    have := congrArg Subtype.val hc
    -- `Subtype.val (c • v') = c • v` and `Subtype.val w' = w`.
    simpa [v', w'] using this
  -- Compute `g(w, w) = c² · g(v, v)`. Since both equal 1, `c² = 1`, so `c = ±1`.
  have h_g_w_w : g.inner (y : M) w w = c * c * g.inner (y : M) v v := by
    -- `g.inner y (c • v) (c • v) = c * (g.inner y v (c • v))` (linearity in first slot)
    -- `= c * (c * g.inner y v v)` (linearity in second slot).
    rw [show w = c • v from hc_amb.symm]
    rw [show g.inner (y : M) (c • v) = c • (g.inner (y : M) v) from
          map_smul _ _ _]
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  have hc_sq : c * c = 1 := by
    rw [hv_unit, mul_one] at h_g_w_w
    rw [h_g_w_w] at hw_unit
    exact hw_unit
  -- From `c * c = 1`, we get `c = 1 ∨ c = -1`.
  have hc_eq : c = 1 ∨ c = -1 := by
    have hc_sq_one : c ^ 2 = 1 := by rw [sq]; exact hc_sq
    exact sq_eq_one_iff.mp hc_sq_one
  -- Case-split.
  rcases hc_eq with h_pos | h_neg
  · left
    rw [show w = c • v from hc_amb.symm, h_pos, one_smul]
  · right
    rw [show w = c • v from hc_amb.symm, h_neg, neg_one_smul, neg_neg]

/-! ## Parameterised transversality and the unnormalised outward direction

The unnormalised parameterised outward direction `outwardDirAt α y` vanishes
exactly when `inwardCoordAt α y ∈ range (dincl y)`. The forward direction is
direct from the construction (`outwardDirAt = inwardTangentialPartAt -
inwardCoordAt`); the reverse direction uses non-degeneracy of the induced
boundary metric to identify the unique boundary component of the inward
direction. -/

/-- The chart-α inward direction is in the boundary tangent space iff the
parameterised unnormalised outward direction vanishes. -/
private lemma outwardDirAt_eq_zero_iff_inwardCoordAt_mem_range
    (g : Measure.SmoothRiemannianMetric I M) (α y : BoundaryManifold I M) :
    outwardDirAt (M := M) g α y = 0 ↔
      inwardCoordAt (M := M) α y ∈ Set.range (dincl (M := M) y) := by
  refine ⟨?_, ?_⟩
  · -- Forward direction: `outwardDirAt = 0` implies `inwardCoordAt = inwardTangentialPart ∈ range`.
    intro h0
    rw [outwardDirAt_def, sub_eq_zero] at h0
    rw [← h0, inwardTangentialPartAt_def]
    exact ⟨boundaryComponentOfInwardAt (M := M) g α y, rfl⟩
  · -- Reverse direction: if `inwardCoordAt α y = dincl y u`, then by uniqueness
    -- `boundaryComponentOfInwardAt α y = u`, so `inwardTangentialPart = dincl y u = inwardCoordAt`,
    -- hence `outwardDirAt = 0`.
    rintro ⟨u, hu⟩
    -- Goal: `outwardDirAt α g y = 0`, i.e., `inwardTangentialPart - inwardCoordAt = 0`.
    rw [outwardDirAt_def, sub_eq_zero, inwardTangentialPartAt_def, ← hu]
    -- Goal: `dincl y (boundaryComponentOfInwardAt α g y) = dincl y u`.
    -- It suffices to show `boundaryComponentOfInwardAt α g y = u` via `dincl_injective`.
    apply congrArg (dincl (M := M) y)
    -- We use non-degeneracy: for all `w`, the induced metric pairing of
    -- `boundaryComponentOfInwardAt` with `w` agrees with that of `u` with `w`.
    -- Then `boundaryFlatMap` injectivity gives the equality.
    have h_pair : ∀ w : hI.boundaryE,
        inducedMetricInner (M := M) g y
          (boundaryComponentOfInwardAt (M := M) g α y) w =
        inducedMetricInner (M := M) g y u w := by
      intro w
      -- LHS: defining identity gives `g.inner y (inwardCoordAt α y) (dincl y w)`.
      rw [inducedMetricInner_boundaryComponentOfInwardAt (M := M) g α y w]
      -- RHS: `inducedMetricInner g y u w = g.inner y (dincl y u) (dincl y w)`.
      rw [inducedMetricInner_apply]
      -- Substitute `inwardCoordAt α y = dincl y u`.
      rw [hu]
    -- From pointwise pairing equality, conclude the boundary vectors are equal.
    -- Use the boundary metric flat injectivity (`boundaryFlatLinear_injective`).
    have h_lin_eq : boundaryFlatLinear (M := M) g y
        (boundaryComponentOfInwardAt (M := M) g α y) =
        boundaryFlatLinear (M := M) g y u := by
      refine LinearMap.ext fun w => ?_
      rw [boundaryFlatLinear_apply, boundaryFlatLinear_apply]
      exact h_pair w
    exact boundaryFlatLinear_injective (M := M) g y h_lin_eq

/-- The parameterised outward direction is non-zero when the chart-α inward
direction is transverse (not in the boundary tangent space). -/
private lemma outwardDirAt_ne_zero_of_transverse
    (g : Measure.SmoothRiemannianMetric I M) (α y : BoundaryManifold I M)
    (h_trans : inwardCoordAt (M := M) α y ∉ Set.range (dincl (M := M) y)) :
    outwardDirAt (M := M) g α y ≠ 0 := by
  intro h0
  exact h_trans
    ((outwardDirAt_eq_zero_iff_inwardCoordAt_mem_range (M := M) g α y).mp h0)

/-- Under transversality of the parameterised inward direction, the squared
`g`-norm of `outwardDirAt α y` is strictly positive. -/
private lemma g_inner_outwardDirAt_pos_of_transverse
    (g : Measure.SmoothRiemannianMetric I M) (α y : BoundaryManifold I M)
    (h_trans : inwardCoordAt (M := M) α y ∉ Set.range (dincl (M := M) y)) :
    0 < g.inner (y : M) (outwardDirAt (M := M) g α y)
        (outwardDirAt (M := M) g α y) :=
  g.pos (y : M) _ (outwardDirAt_ne_zero_of_transverse (M := M) g α y h_trans)

/-! ## Parameterised sign lemma and unit-`g`-length normalisation

Under transversality, the parameterised outward direction has strictly negative
`g`-inner product with the chart-α inward direction, and the unit-`g`-length
normalisation `outwardNormalAt α y` has likewise strictly negative `g`-inner
product with that direction. -/

/-- Parameterised sign lemma: under transversality, `outwardDirAt α y` has
strictly negative `g`-inner product with `inwardCoordAt α y`. -/
private lemma g_inner_outwardDirAt_inwardCoordAt_neg_of_transverse
    (g : Measure.SmoothRiemannianMetric I M) (α y : BoundaryManifold I M)
    (h_trans : inwardCoordAt (M := M) α y ∉ Set.range (dincl (M := M) y)) :
    g.inner (y : M) (outwardDirAt (M := M) g α y)
        (inwardCoordAt (M := M) α y) < 0 := by
  -- Adding `g_inner_outwardDirAt_inwardCoordAt` and `g_inner_outwardDirAt_outwardDirAt` cancels
  -- the cross term, giving the identity
  --   `g(outwardDirAt, inwardCoordAt) = - g(outwardDirAt, outwardDirAt)`.
  -- Positivity of the latter (`g_inner_outwardDirAt_pos_of_transverse`) yields the negative sign.
  have hpos : 0 < g.inner (y : M) (outwardDirAt (M := M) g α y)
        (outwardDirAt (M := M) g α y) :=
    g_inner_outwardDirAt_pos_of_transverse (M := M) g α y h_trans
  have h_id : g.inner (y : M) (outwardDirAt (M := M) g α y)
        (inwardCoordAt (M := M) α y) =
      -g.inner (y : M) (outwardDirAt (M := M) g α y)
        (outwardDirAt (M := M) g α y) := by
    rw [g_inner_outwardDirAt_inwardCoordAt (M := M) g α y,
        g_inner_outwardDirAt_outwardDirAt (M := M) g α y]
    ring
  rw [h_id]
  linarith

/-- Parameterised unit-`g`-length identity: under transversality, the
parameterised outward unit normal has unit `g`-length. -/
private lemma outwardNormalAt_norm_one_of_transverse
    (g : Measure.SmoothRiemannianMetric I M) (α y : BoundaryManifold I M)
    (h_trans : inwardCoordAt (M := M) α y ∉ Set.range (dincl (M := M) y)) :
    g.inner (y : M) (outwardNormalAt (M := M) g α y)
        (outwardNormalAt (M := M) g α y) = 1 := by
  set q : ℝ := g.inner (y : M) (outwardDirAt (M := M) g α y)
      (outwardDirAt (M := M) g α y) with hq_def
  have hq_pos : 0 < q :=
    g_inner_outwardDirAt_pos_of_transverse (M := M) g α y h_trans
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hsq_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq_pos
  have hsq_ne : Real.sqrt q ≠ 0 := ne_of_gt hsq_pos
  have hsq_sq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq_pos.le
  -- `outwardNormalAt α g y = (sqrt q)⁻¹ • outwardDirAt α g y`.
  have h_normal_eq : outwardNormalAt (M := M) g α y =
      (Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y := by
    unfold outwardNormalAt
    rw [dif_pos hq_pos]
  rw [h_normal_eq]
  -- Pull out the scalars from each argument.
  have h1 : g.inner (y : M) ((Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y)
          ((Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y) =
      (Real.sqrt q)⁻¹ • (g.inner (y : M) (outwardDirAt (M := M) g α y))
          ((Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y) := by
    rw [show g.inner (y : M) ((Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y) =
        (Real.sqrt q)⁻¹ • g.inner (y : M) (outwardDirAt (M := M) g α y) from
          map_smul _ _ _]
    rfl
  rw [h1]
  rw [show (g.inner (y : M) (outwardDirAt (M := M) g α y))
        ((Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y) =
      (Real.sqrt q)⁻¹ • g.inner (y : M) (outwardDirAt (M := M) g α y)
        (outwardDirAt (M := M) g α y) from
    ContinuousLinearMap.map_smul _ _ _]
  rw [show g.inner (y : M) (outwardDirAt (M := M) g α y)
        (outwardDirAt (M := M) g α y) = q from rfl]
  rw [smul_eq_mul, smul_eq_mul]
  rw [show (Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) = q / (Real.sqrt q * Real.sqrt q) by
    field_simp]
  rw [hsq_sq]
  exact div_self hq_ne

/-- Parameterised orthogonality: the parameterised outward unit normal lies in
the `g`-orthogonal normal subspace, i.e., it is `g`-orthogonal to every
boundary tangent vector at `y`. -/
private lemma outwardNormalAt_mem_normalSubspace
    (g : Measure.SmoothRiemannianMetric I M) (α y : BoundaryManifold I M) :
    outwardNormalAt (M := M) g α y ∈ normalSubspace (M := M) g y := by
  -- Goal: for all `w : boundaryE`, `g.inner y (outwardNormalAt α g y) (dincl y w) = 0`.
  -- `outwardNormalAt = (sqrt q)⁻¹ • outwardDirAt` (or `0` when `q ≤ 0`); both lie in `normalSubspace`.
  unfold outwardNormalAt
  classical
  by_cases h_pos : 0 < g.inner (y : M) (outwardDirAt (M := M) g α y)
      (outwardDirAt (M := M) g α y)
  · rw [dif_pos h_pos]
    exact (normalSubspace (M := M) g y).smul_mem _
      (outwardDirAt_mem_normalSubspace (M := M) g α y)
  · rw [dif_neg h_pos]
    exact (normalSubspace (M := M) g y).zero_mem

/-- Parameterised sign lemma for `outwardNormalAt`: under transversality, the
parameterised outward unit normal has strictly negative `g`-inner product
with the chart-α inward direction. -/
private lemma outwardNormalAt_inner_inwardCoordAt_neg_of_transverse
    (g : Measure.SmoothRiemannianMetric I M) (α y : BoundaryManifold I M)
    (h_trans : inwardCoordAt (M := M) α y ∉ Set.range (dincl (M := M) y)) :
    g.inner (y : M) (outwardNormalAt (M := M) g α y)
        (inwardCoordAt (M := M) α y) < 0 := by
  have hq_pos : 0 < g.inner (y : M) (outwardDirAt (M := M) g α y)
      (outwardDirAt (M := M) g α y) :=
    g_inner_outwardDirAt_pos_of_transverse (M := M) g α y h_trans
  -- `outwardNormalAt = (sqrt q)⁻¹ • outwardDirAt`.
  have h_normal_eq : outwardNormalAt (M := M) g α y =
      (Real.sqrt (g.inner (y : M) (outwardDirAt (M := M) g α y)
          (outwardDirAt (M := M) g α y)))⁻¹ • outwardDirAt (M := M) g α y := by
    unfold outwardNormalAt
    rw [dif_pos hq_pos]
  rw [h_normal_eq]
  rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  -- Goal: `(sqrt q)⁻¹ * g(outwardDirAt, inwardCoordAt) < 0`.
  have hsq_pos : 0 < Real.sqrt (g.inner (y : M) (outwardDirAt (M := M) g α y)
      (outwardDirAt (M := M) g α y)) := Real.sqrt_pos.mpr hq_pos
  have hsq_inv_pos : 0 < (Real.sqrt (g.inner (y : M) (outwardDirAt (M := M) g α y)
      (outwardDirAt (M := M) g α y)))⁻¹ := inv_pos.mpr hsq_pos
  have hneg : g.inner (y : M) (outwardDirAt (M := M) g α y)
      (inwardCoordAt (M := M) α y) < 0 :=
    g_inner_outwardDirAt_inwardCoordAt_neg_of_transverse (M := M) g α y h_trans
  exact mul_neg_of_pos_of_neg hsq_inv_pos hneg

/-! ## Chart-invariance of the outward unit normal under boundary orientation

If two chart base points `α₀, α₁` agree on the inward direction at `y` up to
a strictly positive scalar and a boundary-tangent correction, the outward
unit normal at `y` is independent of the chart.

The argument:

1. `normalSubspace g y` has dimension `1` (`normalSubspace_finrank_one`).
2. Both `outwardNormalAt α₀ g y` and `outwardNormalAt α₁ g y` lie in
   `normalSubspace g y`.
3. Under transversality of both, both have unit `g`-length, so by the
   "two unit vectors in a 1-dim subspace" lemma they are equal or opposite.
4. The orientation hypothesis fixes the sign: writing
   `inwardCoordAt α₀ y = c • inwardCoordAt α₁ y + dincl y w` with `c > 0`,
   the `g`-inner product of `outwardNormalAt α₁ g y` with
   `inwardCoordAt α₀ y` is a positive scalar times its `g`-inner product with
   `inwardCoordAt α₁ y` (negative), hence is itself negative. So the chart-α₀
   sign condition is matched by `outwardNormalAt α₁ g y`, forcing equality.
5. The non-transverse case (where both outward unit normals are `0` by
   definition) is handled separately, using the orientation hypothesis to
   transfer non-transversality between the two charts.
-/

/-- Under the orientation hypothesis, transversality of the parameterised
inward direction is independent of the chart base point. -/
private lemma inwardCoordAt_mem_range_iff_of_orientation
    (α₀ α₁ y : BoundaryManifold I M)
    (c : ℝ) (hc : 0 < c)
    (h_w : inwardCoordAt (M := M) α₀ y - c • inwardCoordAt (M := M) α₁ y ∈
        Set.range (dincl (M := M) y).toLinearMap) :
    inwardCoordAt (M := M) α₀ y ∈ Set.range (dincl (M := M) y) ↔
      inwardCoordAt (M := M) α₁ y ∈ Set.range (dincl (M := M) y) := by
  -- `Set.range (dincl y).toLinearMap = Set.range (dincl y)` (these agree on the underlying function).
  have h_range_eq : Set.range (dincl (M := M) y).toLinearMap =
      Set.range (dincl (M := M) y) := rfl
  rw [h_range_eq] at h_w
  -- Setup: `inwardCoordAt α₀ y = c • inwardCoordAt α₁ y + dincl y w'` for some `w'`.
  rcases h_w with ⟨w', hw'⟩
  -- The mismatch between `TangentSpace I y` and `E` (which are equal as types via alias) is
  -- bridged by working at type `E` throughout. We treat `inwardCoordAt α y : TangentSpace I y`
  -- by coercion to `E` (which is definitional).
  have hc_ne : c ≠ 0 := ne_of_gt hc
  -- `hw' : (dincl y) w' = inwardCoordAt α₀ y - c • inwardCoordAt α₁ y` in `E`.
  -- Both sides of `hw'` are of type `E`. We use this directly.
  refine ⟨fun h₀ => ?_, fun h₁ => ?_⟩
  · -- `α₀-inward ∈ range` implies `α₁-inward ∈ range`.
    rcases h₀ with ⟨u, hu⟩
    refine ⟨c⁻¹ • (u - w'), ?_⟩
    -- Goal: `dincl y (c⁻¹ • (u - w')) = inwardCoordAt α₁ y`.
    -- Compute `c • inwardCoordAt α₁ y = inwardCoordAt α₀ y - dincl y w'`,
    -- then `inwardCoordAt α₁ y = c⁻¹ • (inwardCoordAt α₀ y - dincl y w')
    --   = c⁻¹ • (dincl y u - dincl y w') = dincl y (c⁻¹ • (u - w'))`.
    have h_target : (c : ℝ) • inwardCoordAt (M := M) α₁ y =
        (dincl (M := M) y) u - (dincl (M := M) y) w' := by
      rw [hu, hw']; abel
    -- Multiply by c⁻¹: `c⁻¹ • (c • α₁-inward) = α₁-inward`.
    have h_inv_smul : (c : ℝ)⁻¹ • ((c : ℝ) • inwardCoordAt (M := M) α₁ y) =
        inwardCoordAt (M := M) α₁ y := by
      rw [← mul_smul, inv_mul_cancel₀ hc_ne, one_smul]
    have h_target_inv : inwardCoordAt (M := M) α₁ y =
        (c : ℝ)⁻¹ • ((dincl (M := M) y) u - (dincl (M := M) y) w') := by
      rw [← h_inv_smul, h_target]
      rfl
    rw [h_target_inv, ContinuousLinearMap.map_smul, map_sub]
  · -- `α₁-inward ∈ range` implies `α₀-inward ∈ range`.
    rcases h₁ with ⟨u, hu⟩
    refine ⟨c • u + w', ?_⟩
    -- Goal: `dincl y (c • u + w') = inwardCoordAt α₀ y`.
    -- `dincl y (c • u + w') = c • dincl y u + dincl y w' = c • inwardCoordAt α₁ y + dincl y w'`.
    rw [map_add, ContinuousLinearMap.map_smul, hu]
    -- Goal: `c • inwardCoordAt α₁ y + dincl y w' = inwardCoordAt α₀ y`.
    -- We work in `TangentSpace I y` (= E by alias) using a `set` for `dincl y w'`.
    set vw : TangentSpace I (y : M) := dincl (M := M) y w' with hvw_def
    -- `hw' : vw = inwardCoordAt α₀ y - c • inwardCoordAt α₁ y` (with vw on LHS).
    change (c : ℝ) • inwardCoordAt (M := M) α₁ y + vw = inwardCoordAt (M := M) α₀ y
    have hw'' : vw = inwardCoordAt (M := M) α₀ y -
        (c : ℝ) • inwardCoordAt (M := M) α₁ y := hw'
    rw [hw'']; abel

/-- Under the orientation hypothesis, the unparameterised version: `inwardCoordAt α₀ y ∉ range`
iff `inwardCoordAt α₁ y ∉ range`. -/
private lemma inwardCoordAt_not_mem_range_iff_of_orientation
    (α₀ α₁ y : BoundaryManifold I M)
    (c : ℝ) (hc : 0 < c)
    (h_w : inwardCoordAt (M := M) α₀ y - c • inwardCoordAt (M := M) α₁ y ∈
        Set.range (dincl (M := M) y).toLinearMap) :
    inwardCoordAt (M := M) α₀ y ∉ Set.range (dincl (M := M) y) ↔
      inwardCoordAt (M := M) α₁ y ∉ Set.range (dincl (M := M) y) := by
  rw [not_iff_not]
  exact inwardCoordAt_mem_range_iff_of_orientation (M := M) α₀ α₁ y c hc h_w

/-- The chart-α₀ inward "outward" sign condition for `N₁ := outwardNormalAt α₁ g y`,
under the orientation hypothesis. Concretely:
`g.inner y N₁ (inwardCoordAt α₀ y) < 0`.

This uses:
* `inwardCoordAt α₀ y = c • inwardCoordAt α₁ y + dincl y w` with `c > 0`,
* `N₁ ∈ normalSubspace g y` (so `g.inner y N₁ (dincl y w) = 0`),
* `g.inner y N₁ (inwardCoordAt α₁ y) < 0` (parameterised sign at α₁).
-/
private lemma g_inner_outwardNormalAt_inwardCoordAt_other_neg
    (g : Measure.SmoothRiemannianMetric I M) (α₀ α₁ y : BoundaryManifold I M)
    (h_trans₁ : inwardCoordAt (M := M) α₁ y ∉ Set.range (dincl (M := M) y))
    (c : ℝ) (hc : 0 < c)
    (h_w : inwardCoordAt (M := M) α₀ y - c • inwardCoordAt (M := M) α₁ y ∈
        Set.range (dincl (M := M) y).toLinearMap) :
    g.inner (y : M) (outwardNormalAt (M := M) g α₁ y)
        (inwardCoordAt (M := M) α₀ y) < 0 := by
  -- Decompose `inwardCoordAt α₀ y = c • inwardCoordAt α₁ y + dincl y w'`.
  have h_range_eq : Set.range (dincl (M := M) y).toLinearMap =
      Set.range (dincl (M := M) y) := rfl
  rw [h_range_eq] at h_w
  rcases h_w with ⟨w', hw'⟩
  -- Set up local names that avoid the `TangentSpace I y` vs `E` mismatch.
  set N₁ : TangentSpace I (y : M) := outwardNormalAt (M := M) g α₁ y with hN₁_def
  set v₀ : TangentSpace I (y : M) := inwardCoordAt (M := M) α₀ y with hv₀_def
  set v₁ : TangentSpace I (y : M) := inwardCoordAt (M := M) α₁ y with hv₁_def
  set vw : TangentSpace I (y : M) := dincl (M := M) y w' with hvw_def
  -- `hw' : vw = v₀ - c • v₁`.
  have hw'' : vw = v₀ - c • v₁ := hw'
  -- Hence `v₀ = c • v₁ + vw`.
  have hv₀_eq : v₀ = c • v₁ + vw := by rw [hw'']; abel
  -- Compute `g.inner y N₁ v₀`.
  rw [hv₀_eq, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, smul_eq_mul]
  -- LHS: `c * g(N₁, v₁) + g(N₁, vw)`.
  -- `g(N₁, vw) = 0` because `N₁ ∈ normalSubspace` and `vw = dincl y w'`.
  have h_orth : g.inner (y : M) N₁ vw = 0 := by
    rw [hvw_def]
    exact (outwardNormalAt_mem_normalSubspace (M := M) g α₁ y) w'
  rw [h_orth, add_zero]
  -- LHS: `c * g(N₁, v₁)`.
  have h_neg : g.inner (y : M) N₁ v₁ < 0 :=
    outwardNormalAt_inner_inwardCoordAt_neg_of_transverse (M := M) g α₁ y h_trans₁
  exact mul_neg_of_pos_of_neg hc h_neg

/-! ### Final assembly: chart-invariance of the parameterised outward unit normal -/

/-- **Chart-invariance with explicit orientation hypothesis.** If the
parameterised inward direction at `y` viewed in two different charts differs
only by a positive scalar multiple modulo a boundary-tangent correction, the
parameterised outward unit normal is the same. -/
theorem outwardNormalAt_chart_invariance_of_orientation
    (g : Measure.SmoothRiemannianMetric I M) (α₀ α₁ y : BoundaryManifold I M)
    {c : ℝ} (hc : 0 < c)
    (h_w : inwardCoordAt (M := M) α₀ y - c • inwardCoordAt (M := M) α₁ y ∈
        Set.range (dincl (M := M) y).toLinearMap) :
    outwardNormalAt (M := M) g α₀ y = outwardNormalAt (M := M) g α₁ y := by
  classical
  -- Distinguish based on transversality at α₁ (and α₀ — both equivalent under orientation).
  by_cases h_trans₁ : inwardCoordAt (M := M) α₁ y ∈ Set.range (dincl (M := M) y)
  · -- Non-transverse case: both outward dirs are zero, both normals are zero.
    have h_trans₀ : inwardCoordAt (M := M) α₀ y ∈ Set.range (dincl (M := M) y) := by
      have h_iff := inwardCoordAt_mem_range_iff_of_orientation (M := M) α₀ α₁ y c hc h_w
      exact h_iff.mpr h_trans₁
    -- `outwardDirAt α₀ y = 0` and `outwardDirAt α₁ y = 0`.
    have h0_α₀ : outwardDirAt (M := M) g α₀ y = 0 :=
      (outwardDirAt_eq_zero_iff_inwardCoordAt_mem_range (M := M) g α₀ y).mpr h_trans₀
    have h0_α₁ : outwardDirAt (M := M) g α₁ y = 0 :=
      (outwardDirAt_eq_zero_iff_inwardCoordAt_mem_range (M := M) g α₁ y).mpr h_trans₁
    -- Squared norms are zero, not positive, so `outwardNormalAt = 0` for both (by `dif_neg`).
    have h_q_α₀ : g.inner (y : M) (outwardDirAt (M := M) g α₀ y)
        (outwardDirAt (M := M) g α₀ y) = 0 := by
      rw [h0_α₀]; simp
    have h_q_α₁ : g.inner (y : M) (outwardDirAt (M := M) g α₁ y)
        (outwardDirAt (M := M) g α₁ y) = 0 := by
      rw [h0_α₁]; simp
    have h_normal_α₀ : outwardNormalAt (M := M) g α₀ y = 0 := by
      unfold outwardNormalAt
      rw [dif_neg]
      rw [h_q_α₀]; exact lt_irrefl 0
    have h_normal_α₁ : outwardNormalAt (M := M) g α₁ y = 0 := by
      unfold outwardNormalAt
      rw [dif_neg]
      rw [h_q_α₁]; exact lt_irrefl 0
    rw [h_normal_α₀, h_normal_α₁]
  · -- Transverse case: both outward unit normals are non-zero, sign argument applies.
    -- Translate to "not in range" (the form we use).
    have h_trans₁_ne : inwardCoordAt (M := M) α₁ y ∉ Set.range (dincl (M := M) y) :=
      h_trans₁
    -- α₀ also transverse.
    have h_trans₀_ne : inwardCoordAt (M := M) α₀ y ∉ Set.range (dincl (M := M) y) := by
      have h_iff := inwardCoordAt_not_mem_range_iff_of_orientation (M := M) α₀ α₁ y c hc h_w
      exact h_iff.mpr h_trans₁_ne
    -- Set up: `N₀ := outwardNormalAt α₀ y`, `N₁ := outwardNormalAt α₁ y`.
    -- Both are in `normalSubspace g y` with unit `g`-length. By 1-dim, they're ±1 apart.
    have hN₀_mem : outwardNormalAt (M := M) g α₀ y ∈ normalSubspace (M := M) g y :=
      outwardNormalAt_mem_normalSubspace (M := M) g α₀ y
    have hN₁_mem : outwardNormalAt (M := M) g α₁ y ∈ normalSubspace (M := M) g y :=
      outwardNormalAt_mem_normalSubspace (M := M) g α₁ y
    have hN₀_unit : g.inner (y : M) (outwardNormalAt (M := M) g α₀ y)
        (outwardNormalAt (M := M) g α₀ y) = 1 :=
      outwardNormalAt_norm_one_of_transverse (M := M) g α₀ y h_trans₀_ne
    have hN₁_unit : g.inner (y : M) (outwardNormalAt (M := M) g α₁ y)
        (outwardNormalAt (M := M) g α₁ y) = 1 :=
      outwardNormalAt_norm_one_of_transverse (M := M) g α₁ y h_trans₁_ne
    have h_finrank : Module.finrank ℝ (normalSubspace (M := M) g y) = 1 :=
      normalSubspace_finrank_one (M := M) g y
    -- Apply Block 2: `N₀ = N₁ ∨ N₀ = -N₁`.
    have h_eq_or_neg :=
      unit_vectors_in_1dim_equal_or_opposite (M := M) g h_finrank hN₀_mem hN₁_mem
        hN₀_unit hN₁_unit
    -- Sign matching: under orientation, the chart-α₀ sign condition holds for `N₁`.
    have h_sign : g.inner (y : M) (outwardNormalAt (M := M) g α₁ y)
        (inwardCoordAt (M := M) α₀ y) < 0 :=
      g_inner_outwardNormalAt_inwardCoordAt_other_neg (M := M) g α₀ α₁ y
        h_trans₁_ne c hc h_w
    -- Contrast with chart-α₀ sign condition for `N₀`.
    have h_sign₀ : g.inner (y : M) (outwardNormalAt (M := M) g α₀ y)
        (inwardCoordAt (M := M) α₀ y) < 0 :=
      outwardNormalAt_inner_inwardCoordAt_neg_of_transverse (M := M) g α₀ y h_trans₀_ne
    -- Rule out `N₀ = -N₁` by sign.
    rcases h_eq_or_neg with h_eq | h_neg_eq
    · exact h_eq
    · -- `N₀ = -N₁`, then `g(N₀, α₀-inward) = g(-N₁, α₀-inward) = -g(N₁, α₀-inward) > 0`,
      -- contradicting `h_sign₀ < 0`.
      exfalso
      have h_contra : g.inner (y : M) (outwardNormalAt (M := M) g α₀ y)
          (inwardCoordAt (M := M) α₀ y) =
          -g.inner (y : M) (outwardNormalAt (M := M) g α₁ y)
            (inwardCoordAt (M := M) α₀ y) := by
        rw [h_neg_eq]
        rw [show g.inner (y : M) (-outwardNormalAt (M := M) g α₁ y) =
              -g.inner (y : M) (outwardNormalAt (M := M) g α₁ y) from
            map_neg _ _]
        rfl
      rw [h_contra] at h_sign₀
      linarith

end Smoothness


end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
