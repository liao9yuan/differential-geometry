import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.WeakSolutionHeadline
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.CanonicalTensorRepr

/-!
# Building a smooth compactly-supported tensor section from prescribed chart-frame components

For a smooth Riemannian metric `g` on a closed (compact, boundaryless) smooth
manifold `M`, fixed ranks `(r, s)`, and a chart center `α : M`, the chart-frame
component API of `ChartTensor/Components.lean` *reads off* — from a smooth
compactly-supported `(r, s)`-tensor section `S : SmoothCcTensor g r s` — the
scalar component functions of `S` in the chart-`α` frame, indexed by the
component multi-index type `TensorCompIdx r s`. The raw chart-frame component
`tensorChartComponentRaw g r s S α Idx Jdx` is the read-out functional.

This file builds the **inverse** of that read-out: a constructor

```
tensorBundleSectionOfChartComponents g r s α u hu hsupp : SmoothCcTensor g r s
```

that takes a prescribed family of smooth, compactly-supported chart-frame
component functions `u : TensorCompIdx r s → EuclN → ℝ` (smooth on the Euclidean
chart target, each compactly supported strictly inside it) and produces the
unique smooth compactly-supported `(r, s)`-tensor section whose chart-`α` frame
*is* the family `u`, extended by zero off the chart source.

## The construction

The `(r, s)`-tensor bundle has, at the chart center `α`, a trivialization whose
base set is the chart-`α` source and whose fibrewise inverse `symmL` transports
a constant model tensor to a chart-locally smooth section. The chart-`α`-frame
constant basis tensor section `chartBasisTensorSection g r s α χ … P`
(`RotatedTestSection.lean`) is, in the chart-`α` frame, the constant chart basis
tensor at the component multi-index `P`, cut off by a scalar bump `χ`.

The section assembled here is the finite sum, over the component multi-indices
`P : TensorCompIdx r s`, of the chart-frame constant basis sections cut off by
the manifold-side pull-back `chartTestPullback α (u P)` of the prescribed
component function `u P`. Each `u P` is — being smooth on the open chart target
and compactly supported strictly inside it — globally `C^∞`
(`contDiff_of_contDiffOn_chartTarget_zero_off`), so its manifold-side pull-back
is `C^∞` on the chart source with topological support inside it
(`chartTestPullback_contMDiffOn`, `chartTestPullback_tsupport_subset_source`),
the data `chartBasisTensorSection` requires.

## Main definitions

* `tensorBundleSectionOfChartComponents g r s α u hu hsupp` — the smooth
  compactly-supported `(r, s)`-tensor section whose chart-`α` frame is the
  prescribed family of component functions `u`.

## Main results

* `tensorChartComponentRaw_tensorBundleSectionOfChartComponents` — on the
  Euclidean chart target the raw chart-`α` frame scalar component of the
  assembled section at a component multi-index `P`, read at the chart-source
  preimage of a chart-target point `y`, recovers `u P y`. This is the precise
  sense in which the assembled section "has chart-`α` components `u`".
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Global smoothness of a compactly-supported chart-target component function

A component function smooth on the open Euclidean chart target and compactly
supported strictly inside it is globally `C^∞`: on the open target it is the
given smooth function, and off the closed support it vanishes — the
extension-by-zero gluing of `contDiff_of_contDiffOn_chartTarget_zero_off`. -/

/-- A chart-frame component function `C^∞` on the open Euclidean chart target,
with topological support inside that target, is globally `C^∞`. -/
private lemma component_contDiff_of_contDiffOn (α : M)
    {f : EuclN → ℝ}
    (hf : ContDiffOn ℝ ∞ f (chartTargetEuclid (I := I) (M := M) α))
    (hf_supp : tsupport f ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContDiff ℝ ∞ f :=
  contDiff_of_contDiffOn_chartTarget_zero_off (I := I) (M := M) α
    (isClosed_tsupport f) hf_supp hf
    (fun _ hy => image_eq_zero_of_notMem_tsupport hy)

/-! ## The manifold-side chart bump of a prescribed component function

For a prescribed component function `u P`, the manifold-side pull-back
`chartTestPullback α (u P)` is the scalar bump fed to `chartBasisTensorSection`.
Its smoothness on the chart source and the containment of its topological
support inside the chart source — the two `chartBasisTensorSection` hypotheses —
are recorded here, both consequences of global `C^∞`-ness of `u P`. -/

/-- The manifold-side chart bump `chartTestPullback α (u P)` is `C^∞` on the
chart-`α` source. -/
private lemma componentBump_contMDiffOn
    (α : M) {f : EuclN → ℝ}
    (hf : ContDiffOn ℝ ∞ f (chartTargetEuclid (I := I) (M := M) α))
    (hf_supp : tsupport f ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (chartTestPullback (I := I) α f)
      (chartAt H α).source :=
  chartTestPullback_contMDiffOn (I := I) (M := M) α
    (component_contDiff_of_contDiffOn (I := I) (M := M) α hf hf_supp)

/-- The manifold-side chart bump `chartTestPullback α (u P)` has topological
support inside the chart-`α` source. -/
private lemma componentBump_tsupport_subset
    (α : M) {f : EuclN → ℝ}
    (hf_cs : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (chartTestPullback (I := I) α f) ⊆ (chartAt H α).source :=
  chartTestPullback_tsupport_subset_source (I := I) (M := M) α hf_cs hf_supp

/-! ## Additivity of the raw chart-frame component over a finite sum of sections

The trivialization projection `tensorTrivProj` is built from the bundle
`continuousLinearMapAt`, and the chart-frame component projection
`tensorChartComponentProjection` is a continuous linear map; the raw chart-frame
component is therefore additive in the section argument, and the raw chart
component of a finite sum of sections is the finite sum of the raw chart
components. -/

/-- The trivialization-projected scalar `tensorTrivProj` is additive over a
finite sum of tensor sections. -/
private lemma tensorTrivProj_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {ι : Type*} (t : Finset ι) (S : ι → SmoothCcTensor g r s) (b : M) :
    tensorTrivProj (I := I) (M := M) g r s (∑ i ∈ t, S i) α b =
      ∑ i ∈ t, tensorTrivProj (I := I) (M := M) g r s (S i) α b := by
  classical
  have hadd : ∀ S₁ S₂ : SmoothCcTensor g r s,
      tensorTrivProj (I := I) (M := M) g r s (S₁ + S₂) α b =
        tensorTrivProj (I := I) (M := M) g r s S₁ α b +
          tensorTrivProj (I := I) (M := M) g r s S₂ α b := by
    intro S₁ S₂
    unfold tensorTrivProj
    rw [show (S₁ + S₂).toSection b = S₁.toSection b + S₂.toSection b from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    exact map_add _ _ _
  have hzero : tensorTrivProj (I := I) (M := M) g r s
      (0 : SmoothCcTensor g r s) α b = 0 := by
    unfold tensorTrivProj
    rw [show (0 : SmoothCcTensor g r s).toSection b = 0 from by
      rw [SmoothCcTensor.toSection_zero]; rfl]
    exact map_zero _
  induction t using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, hzero]
  | insert i A hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, ih]

/-- The raw chart-frame scalar component `tensorChartComponentRaw` is additive
over a finite sum of tensor sections. -/
private lemma tensorChartComponentRaw_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {ι : Type*} (t : Finset ι) (S : ι → SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (b : M) :
    tensorChartComponentRaw (I := I) (M := M) g r s (∑ i ∈ t, S i)
        α Idx Jdx b =
      ∑ i ∈ t, tensorChartComponentRaw (I := I) (M := M) g r s (S i)
        α Idx Jdx b := by
  classical
  unfold tensorChartComponentRaw
  rw [tensorTrivProj_sum (I := I) (M := M) g r s α t S b]
  exact map_sum (tensorChartComponentProjection (E := E) r s Idx Jdx) _ _

/-! ## The chart-frame tensor section from prescribed component functions

The assembled section is the finite sum, over component multi-indices
`P : TensorCompIdx r s`, of the chart-`α`-frame constant basis sections cut off
by the manifold-side pull-back `chartTestPullback α (u P)` of the prescribed
component function `u P`. The summands are elements of the `ℝ`-module
`SmoothCcTensor g r s`, so the finite sum stays inside it. -/

/-- **The chart-`α`-frame tensor section from prescribed component functions.**
For a chart center `α : M` and a family `u : TensorCompIdx r s → EuclN → ℝ` of
chart-frame component functions, each `C^∞` on the Euclidean chart target and
compactly supported strictly inside it, this is the smooth compactly-supported
`(r, s)`-tensor section whose chart-`α` frame *is* the family `u`, extended by
zero off the chart source. It is built as the finite sum, over component
multi-indices `P`, of the chart-`α`-frame constant basis sections cut off by the
manifold-side pull-back `chartTestPullback α (u P)` of the component `u P`. -/
noncomputable def tensorBundleSectionOfChartComponents
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ)
    (hu : ∀ P, ContDiffOn ℝ ∞ (u P)
      (chartTargetEuclid (I := I) (M := M) α))
    (hsupp : ∀ P, HasCompactSupport (u P) ∧
      tsupport (u P) ⊆ chartTargetEuclid (I := I) (M := M) α) :
    SmoothCcTensor g r s := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  classical
  exact
    ∑ P : TensorCompIdx (E := E) r s,
      chartBasisTensorSection (I := I) (M := M) g r s α
        (chartTestPullback (I := I) α (u P))
        (componentBump_contMDiffOn (I := I) (M := M) α (hu P) (hsupp P).2)
        (componentBump_tsupport_subset (I := I) (M := M) α
          (hsupp P).1 (hsupp P).2)
        P

/-- The assembled section unfolds to the finite sum of chart-`α`-frame constant
basis sections cut off by the manifold-side pull-backs of the components. -/
private lemma tensorBundleSectionOfChartComponents_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ)
    (hu : ∀ P, ContDiffOn ℝ ∞ (u P)
      (chartTargetEuclid (I := I) (M := M) α))
    (hsupp : ∀ P, HasCompactSupport (u P) ∧
      tsupport (u P) ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tensorBundleSectionOfChartComponents (I := I) (M := M) g r s α u hu hsupp =
      ∑ P : TensorCompIdx (E := E) r s,
        chartBasisTensorSection (I := I) (M := M) g r s α
          (chartTestPullback (I := I) α (u P))
          (componentBump_contMDiffOn (I := I) (M := M) α (hu P) (hsupp P).2)
          (componentBump_tsupport_subset (I := I) (M := M) α
            (hsupp P).1 (hsupp P).2)
          P := by
  classical
  rfl

/-- **The assembled section is supported in its chart.** The underlying section
of `tensorBundleSectionOfChartComponents g r s α u hu hsupp` vanishes off the
chart-`α` source: each summand is a chart-`α`-frame basis section cut off by the
chart-`α` pull-back of a component function, and the pull-back is zero off the
chart source. -/
theorem tensorBundleSectionOfChartComponents_toSection_eq_zero_off_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ)
    (hu : ∀ P, ContDiffOn ℝ ∞ (u P)
      (chartTargetEuclid (I := I) (M := M) α))
    (hsupp : ∀ P, HasCompactSupport (u P) ∧
      tsupport (u P) ⊆ chartTargetEuclid (I := I) (M := M) α)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    (tensorBundleSectionOfChartComponents (I := I) (M := M) g r s α
        u hu hsupp).toSection x = 0 := by
  classical
  -- Unfold into the finite sum of chart-basis sections.
  rw [tensorBundleSectionOfChartComponents_eq (I := I) (M := M) g r s α u hu hsupp]
  -- Abbreviate the summand sections.
  set S : TensorCompIdx (E := E) r s → SmoothCcTensor g r s :=
    fun P => chartBasisTensorSection (I := I) (M := M) g r s α
      (chartTestPullback (I := I) α (u P))
      (componentBump_contMDiffOn (I := I) (M := M) α (hu P) (hsupp P).2)
      (componentBump_tsupport_subset (I := I) (M := M) α
        (hsupp P).1 (hsupp P).2) P with hS_def
  -- The underlying section of the finite sum is the finite sum of the sections.
  have h_sum_section :
      (∑ P : TensorCompIdx (E := E) r s, S P).toSection =
        ∑ P : TensorCompIdx (E := E) r s, (S P).toSection :=
    map_sum (SmoothCcTensor.toSectionAddHom (I := I) (M := M) (g := g)
      (r := r) (s := s)) _ _
  -- Evaluating the finite sum of sections at `x` is the finite sum of values.
  have h_coe : ⇑(∑ P : TensorCompIdx (E := E) r s, (S P).toSection) =
      ∑ P : TensorCompIdx (E := E) r s, ⇑(S P).toSection :=
    map_sum (ContMDiffSection.coeAddHom I (TensorRSModel r s ℝ E) ∞
      (fun b : M => TensorRSSpace r s I b)) _ _
  have h_eval : (∑ P : TensorCompIdx (E := E) r s, S P).toSection x =
      ∑ P : TensorCompIdx (E := E) r s, (S P).toSection x := by
    rw [h_sum_section]
    have := congrFun h_coe x
    rw [Finset.sum_apply] at this
    exact this
  rw [h_eval]
  -- Each summand section vanishes at `x`: the chart-pull bump is `0` there.
  refine Finset.sum_eq_zero (fun P _ => ?_)
  rw [hS_def, chartBasisTensorSection_toSection_apply (I := I) (M := M) g r s α
    (componentBump_contMDiffOn (I := I) (M := M) α (hu P) (hsupp P).2)
    (componentBump_tsupport_subset (I := I) (M := M) α
      (hsupp P).1 (hsupp P).2) P x,
    chartTestPullback_apply_of_notMem (I := I) α _ hx, zero_smul]

/-! ## Recovery of the prescribed chart-frame components

The raw chart-`α` frame scalar component of the assembled section recovers, on
the Euclidean chart target, the prescribed component family `u`. Expanding the
raw component of the finite sum (additivity), the raw component of the `P`-th
summand is the chart-pushed bump times the Kronecker delta `[(Idx, Jdx) = P]`
(`chartBasisTensorSection_chartComp`); only the diagonal term survives, and the
chart-pushed bump of `chartTestPullback α (u P)` agrees with `u P` on the chart
target (`chartPushedRaw_chartTestPullback_eqOn`). -/

/-- **Recovery of the prescribed chart-frame components.** On the Euclidean
chart target the raw chart-`α` frame scalar component of the assembled section
`tensorBundleSectionOfChartComponents g r s α u hu hsupp` at a component
multi-index `P`, read at the chart-source preimage of a chart-target point `y`,
equals the prescribed component value `u P y`. -/
theorem tensorChartComponentRaw_tensorBundleSectionOfChartComponents
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ)
    (hu : ∀ P, ContDiffOn ℝ ∞ (u P)
      (chartTargetEuclid (I := I) (M := M) α))
    (hsupp : ∀ P, HasCompactSupport (u P) ∧
      tsupport (u P) ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (tensorBundleSectionOfChartComponents (I := I) (M := M) g r s α
          u hu hsupp)
        α P.1 P.2 ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      u P y := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  classical
  -- Expand the assembled section into the finite sum of summands.
  rw [tensorBundleSectionOfChartComponents_eq (I := I) (M := M) g r s α
    u hu hsupp]
  -- Additivity: the raw component of the finite sum is the sum of raw
  -- components of the summands.
  rw [tensorChartComponentRaw_sum (I := I) (M := M) g r s α Finset.univ _
    P.1 P.2 ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))]
  -- The raw component of the `Q`-th summand is the chart-pushed bump of
  -- `chartTestPullback α (u Q)` times the Kronecker delta `[(P.1, P.2) = Q]`.
  have hterm : ∀ Q : TensorCompIdx (E := E) r s,
      tensorChartComponentRaw (I := I) (M := M) g r s
          (chartBasisTensorSection (I := I) (M := M) g r s α
            (chartTestPullback (I := I) α (u Q))
            (componentBump_contMDiffOn (I := I) (M := M) α (hu Q) (hsupp Q).2)
            (componentBump_tsupport_subset (I := I) (M := M) α
              (hsupp Q).1 (hsupp Q).2)
            Q)
          α P.1 P.2 ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
        chartPushedRaw I α (chartTestPullback (I := I) α (u Q)) y *
          (if (P.1, P.2) = Q then (1 : ℝ) else 0) :=
    fun Q => chartBasisTensorSection_chartComp (I := I) (M := M) g r s α
      (componentBump_contMDiffOn (I := I) (M := M) α (hu Q) (hsupp Q).2)
      (componentBump_tsupport_subset (I := I) (M := M) α
        (hsupp Q).1 (hsupp Q).2)
      Q P.1 P.2 hy
  rw [Finset.sum_congr rfl (fun Q _ => hterm Q)]
  -- Only the diagonal term `Q = (P.1, P.2) = P` survives.
  rw [Finset.sum_eq_single P]
  · -- Diagonal term: the Kronecker delta is `1`.
    rw [show ((P.1, P.2) : TensorCompIdx (E := E) r s) = P from Prod.ext rfl rfl]
    rw [if_pos rfl, mul_one]
    -- The chart-pushed bump of `chartTestPullback α (u P)` agrees with `u P`.
    exact chartPushedRaw_chartTestPullback_eqOn (I := I) (M := M) α (u P) hy
  · -- Off-diagonal terms vanish: the Kronecker delta is `0`.
    intro Q _ hne
    rw [show ((P.1, P.2) : TensorCompIdx (E := E) r s) = P from Prod.ext rfl rfl]
    rw [if_neg (fun h => hne h.symm), mul_zero]
  · intro hP
    exact absurd (Finset.mem_univ P) hP

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
