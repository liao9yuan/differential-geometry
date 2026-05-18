import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.ChartTransitionTransportCLM

/-!
# The abstract a.e. decomposition of the cutoff-weighted chart component

For a closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)` and a chart base
point `α`, this file proves that the cutoff-weighted chart `P₀`-component of an
arbitrary abstract `L²` tensor element `u : TensorL2 r s g` equals, almost
everywhere on the Euclidean chart target, a finite sum — over the chart centres
`β` whose partition-of-unity weight meets the chart-`α` cutoff support, and over
the component multi-indices `Q` — of the chart-transition transport of the
partition-of-unity `Q`-components of `u`.

## The finite index set

`transportChartCenters α` is the finite set of chart centres `β : M` such that
the support of the chart-atlas partition-of-unity weight `chartAtlasPOU β` meets
the topological support of the chart-kernel cutoff `chartKernelCutoff α`. It is
finite because the partition-of-unity weight family is locally finite and the
cutoff's topological support is compact.

## The decomposition

The headline `tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum` states the
a.e.-identity

`(tensorL2ChartComponentCutoff g r s u α P₀)
   =ᵐ[chartL2Measure α]
   fun y => ∑ β ∈ transportChartCenters α, ∑ Q,
     (chartTransitionTransportCLM g r s β α P₀ Q
        (tensorL2ChartComponent g r s u β Q)) y`.

Both sides are continuous-linear in `u`. They agree on smooth compactly-supported
sections: there the transport operator's smooth-section compatibility
(`chartTransitionTransportCLM_coeFn_smooth`) turns the right side into a finite
sum of chart-pushed transport-coefficient-weighted partition-of-unity
components, and the `(r, s)`-tensor transformation law
(`tensorChartComponentRaw_chartTransition_decomp`) together with the
partition-of-unity identity `∑ β, chartAtlasPOU β = 1` recovers the cutoff
component. Smooth sections are dense in the abstract `L²` completion, so the
identity extends to every `u`.

## Main definitions

* `transportChartCenters α` — the finite set of relevant chart centres.

## Main results

* `tensorL2ChartComponentCutoff_eq_pou_transport_sum` — the underlying equality
  of `L²` classes.
* `tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum` — the headline
  a.e.-identity on the Euclidean chart target.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
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

/-! ## A finite-sum coercion helper for `L²` classes

The underlying function of a finite sum of `L²` classes agrees almost everywhere
with the finite sum of the underlying functions. -/

/-- The function underlying a finite sum of `L²` classes agrees almost
everywhere with the finite sum of the underlying functions. -/
lemma coeFn_finsetSum_chartL2
    (α : M) {ι : Type*} (s : Finset ι)
    (G : ι → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    (((∑ a ∈ s, G a) : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
        EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, ((G a : EuclN → ℝ) y) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero _ _ _
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      refine (Lp.coeFn_add (G a) (∑ b ∈ t, G b)).trans ?_
      filter_upwards [ih] with y hy
      rw [Pi.add_apply, hy, Finset.sum_insert ha]

/-! ## The finite set of transport chart centres

The chart-atlas partition-of-unity weight family `fun β => chartAtlasPOU β` is a
locally finite family of functions on `M`. The chart-kernel cutoff
`chartKernelCutoff α` has compact topological support. The set of indices `β`
whose partition-of-unity weight has support meeting that compact set is
therefore finite. -/

/-- The set of chart centres `β` whose partition-of-unity weight has support
meeting the topological support of the chart-`α` kernel cutoff is finite: the
weight family is locally finite, and the cutoff support is compact. -/
private lemma transportChartCenters_finite (α : M) :
    {β : M |
        (Function.support
            (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport
            ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
              M → ℝ)).Nonempty}.Finite := by
  classical
  -- The partition-of-unity weight family is locally finite.
  have hlf : LocallyFinite
      (fun β : M =>
        Function.support
          (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    (chartAtlasPOU I M).locallyFinite
  -- The cutoff has compact topological support.
  have hcompact : IsCompact
      (tsupport
        ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
    chartKernelCutoff_hasCompactSupport (I := I) (M := M) α
  exact hlf.finite_nonempty_inter_compact hcompact

/-- **The transport chart centres.** For a chart base point `α : M`, the finite
set of chart centres `β : M` such that the support of the chart-atlas
partition-of-unity weight at `β` meets the topological support of the
chart-kernel cutoff at `α`.

This is the index set over which the cutoff-weighted chart component of an
abstract `L²` tensor decomposes as a finite sum of transported
partition-of-unity components: outside this finite set the partition-of-unity
weight misses the cutoff support, so its contribution vanishes. -/
def transportChartCenters (α : M) : Finset M :=
  (transportChartCenters_finite (I := I) (M := M) α).toFinset

/-- Membership in `transportChartCenters α`: a chart centre `β` belongs to it
exactly when its partition-of-unity weight has support meeting the chart-`α`
cutoff support. -/
lemma mem_transportChartCenters (α β : M) :
    β ∈ transportChartCenters (I := I) (M := M) α ↔
      (Function.support
          (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
        tsupport
          ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
            M → ℝ)).Nonempty := by
  unfold transportChartCenters
  rw [Set.Finite.mem_toFinset]
  rfl

/-- If the partition-of-unity weight at `β` and the chart-kernel cutoff at `α`
are both nonzero at a common point `x`, then `β` is a transport chart centre. -/
lemma mem_transportChartCenters_of_pou_cutoff_ne
    (α β : M) {x : M}
    (hβ : ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≠ 0)
    (hα : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≠ 0) :
    β ∈ transportChartCenters (I := I) (M := M) α := by
  rw [mem_transportChartCenters]
  exact ⟨x, hβ, subset_tsupport _ hα⟩

/-! ## The partition-of-unity sum over the transport chart centres

At a point where the chart-kernel cutoff at `α` is nonzero, every chart centre
`β` carrying a nonzero partition-of-unity weight is a transport chart centre, so
the partition-of-unity values over `transportChartCenters α` sum to `1`. -/

/-- At a point where the chart-`α` cutoff is nonzero, the partition-of-unity
weights summed over the transport chart centres equal `1`. The finite support of
the partition-of-unity at that point is contained in `transportChartCenters α`,
so the partition-of-unity sum identity applies. -/
private lemma sum_chartAtlasPOU_transportChartCenters_eq_one
    (α : M) {x : M}
    (hα : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≠ 0) :
    ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1 := by
  classical
  -- The finite support of the partition-of-unity at `x` sits inside the
  -- transport chart centres.
  have hsubset :
      (chartAtlasPOU I M).finsupport x ⊆
        transportChartCenters (I := I) (M := M) α := by
    intro β hβ
    rw [SmoothPartitionOfUnity.mem_finsupport] at hβ
    exact mem_transportChartCenters_of_pou_cutoff_ne
      (I := I) (M := M) α β hβ hα
  exact (chartAtlasPOU I M).sum_finsupport' x (Set.mem_univ x) hsubset

/-! ## The manifold-side decomposition of the cutoff chart-frame scalar

The cutoff-weighted raw chart-frame scalar component centred at `α` decomposes,
pointwise on `M`, as a finite sum over the transport chart centres `β` and the
component multi-indices `Q` of transport-coefficient-weighted
partition-of-unity components centred at `β`. -/

/-- For any chart centre `β`, any point `x` of the chart-`α` source, and any
component multi-index `P₀`, the partition-of-unity weight at `β` times the raw
chart-`α` component equals the sum, over component multi-indices `Q`, of the
chart-kernel cutoff at `β` times the transition coefficient times the
partition-of-unity-weighted raw chart-`β` component.

When the partition-of-unity weight at `β` vanishes both sides vanish; otherwise
the point lies in the chart-`β` source too — so the `(r, s)`-tensor
transformation law expands the raw chart-`α` component in the raw chart-`β`
components — and lies in the closed support of the partition-of-unity weight, so
the chart-`β` cutoff equals `1` there. -/
private lemma pou_smul_raw_eq_transition_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (β α : M)
    (P₀ : TensorCompIdx (E := E) r s) {x : M}
    (hx_α : x ∈ (chartAt H α).source) :
    ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        tensorChartComponentRaw (I := I) (M := M) g r s S α P₀.1 P₀.2 x =
      ∑ Q : TensorCompIdx (E := E) r s,
        ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q x *
            tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x := by
  classical
  by_cases hβ : ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0
  · -- The partition-of-unity weight at `β` vanishes: both sides are zero.
    rw [hβ, zero_mul]
    refine (Finset.sum_eq_zero (fun Q _ => ?_)).symm
    -- Each `tensorChartComponentPou` carries the vanishing weight factor.
    unfold tensorChartComponentPou
    rw [hβ]
    ring
  · -- The weight is nonzero: `x` lies in the chart-`β` source and in the
    -- closed support of the chart-`β` partition-of-unity weight.
    have hx_supp : x ∈
        tsupport
          (fun y : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) :=
      subset_tsupport _ hβ
    have hx_β : x ∈ (chartAt H β).source :=
      chartAtlasPOU_isSubordinate I M β hx_supp
    -- The chart-`β` cutoff equals `1` on the closed support of the chart-`β`
    -- partition-of-unity weight.
    have hχβ : ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
        M → ℝ) x = 1 :=
      chartKernelCutoff_eqOn_one (I := I) (M := M) β hx_supp
    -- The `(r, s)`-tensor transformation law on the chart overlap.
    have hdecomp :=
      tensorChartComponentRaw_eq_transitionCoeff_sum
        (E := E) (I := I) (M := M) g r s S β α P₀ ⟨hx_β, hx_α⟩
    -- Expand the raw chart-`α` component and distribute the weight factor.
    rw [hdecomp, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    -- Each summand: rewrite `tensorChartComponentPou` and `χβ = 1`.
    unfold tensorChartComponentPou
    rw [hχβ]
    ring

/-- **The manifold-side cutoff-component decomposition.** For a smooth
compactly-supported `(r, s)`-tensor section `S`, the cutoff-weighted raw
chart-frame scalar component centred at `α` equals, pointwise on `M`, the finite
sum over the transport chart centres `β` and the component multi-indices `Q` of
the transport-coefficient-weighted partition-of-unity `Q`-components centred at
`β`.

The proof splits on whether the chart-`α` kernel cutoff vanishes. Where it
vanishes both sides vanish — the transport coefficient carries the chart-`α`
cutoff factor. Where it is nonzero the point lies in the chart-`α` source; the
per-centre transformation-law identity `pou_smul_raw_eq_transition_sum` and the
partition-of-unity sum `sum_chartAtlasPOU_transportChartCenters_eq_one` over the
transport chart centres recover the raw chart-`α` component. -/
private lemma cutoffComponentScalar_eq_pou_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (x : M) :
    cutoffComponentScalar (I := I) (M := M) g r s S α P₀.1 P₀.2 x =
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
            tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x := by
  classical
  -- Unfold both sides into chart-kernel-cutoff-weighted expressions.
  unfold cutoffComponentScalar
  -- Abbreviate the chart-`α` cutoff value at `x`.
  set χα : ℝ := ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
    M → ℝ) x with hχα_def
  by_cases hχα : χα = 0
  · -- The chart-`α` cutoff vanishes: both sides are zero.
    rw [hχα, zero_mul]
    refine (Finset.sum_eq_zero (fun β _ => Finset.sum_eq_zero (fun Q _ => ?_))).symm
    -- Each `transportCoeffManifold` carries the vanishing chart-`α` factor.
    rw [transportCoeffManifold_apply]
    rw [show ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
          = χα from rfl, hχα]
    ring
  · -- The chart-`α` cutoff is nonzero: `x` lies in the chart-`α` source.
    have hx_supp : x ∈
        tsupport
          ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ hχα
    have hx_α : x ∈ (chartAt H α).source :=
      chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α hx_supp
    -- Rewrite the right side: factor the chart-`α` cutoff out of each summand.
    have h_rhs :
        (∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
              tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) =
        χα *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
                  M → ℝ) x *
                transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q x *
                tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      rw [transportCoeffManifold_apply,
        show ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
          = χα from rfl]
      ring
    rw [h_rhs]
    -- The inner double sum: for each `β`, the per-centre transformation law
    -- expands `χβ · transitionCoeff · pou` back to `ρβ · Raw_α`.
    have h_inner :
        (∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
                M → ℝ) x *
              transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q x *
              tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) =
        ∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
            tensorChartComponentRaw (I := I) (M := M) g r s S α P₀.1 P₀.2 x := by
      refine Finset.sum_congr rfl (fun β _ => ?_)
      exact (pou_smul_raw_eq_transition_sum
        (I := I) (M := M) g r s S β α P₀ hx_α).symm
    rw [h_inner, ← Finset.sum_mul,
      sum_chartAtlasPOU_transportChartCenters_eq_one (I := I) (M := M) α hχα,
      one_mul]

/-! ## The chart-pushforward of the manifold-side decomposition

The chart-`α` pushforward of a finite sum of manifold functions is the finite
sum of their chart-`α` pushforwards: on the chart target it reads the common
preimage point and the sum distributes; off the chart target every term
vanishes. -/

/-- The chart-`α` pushforward of a finite sum of manifold functions equals,
pointwise on the Euclidean model space, the finite sum of the chart-`α`
pushforwards of the summands. -/
lemma chartPushedRaw_finsetSum
    (α : M) {ι : Type*} (s : Finset ι) (F : ι → M → ℝ) (y : EuclN) :
    chartPushedRaw I α (fun x : M => ∑ a ∈ s, F a x) y =
      ∑ a ∈ s, chartPushedRaw I α (F a) y := by
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
    refine (Finset.sum_eq_zero (fun a _ => ?_)).symm
    rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]

/-- **The Euclidean cutoff-component decomposition.** For a smooth
compactly-supported `(r, s)`-tensor section `S`, the cutoff Euclidean chart
component centred at `α` equals, pointwise on the Euclidean model space, the
finite sum over the transport chart centres `β` and the component multi-indices
`Q` of the chart-`α` pushforwards of the transport-coefficient-weighted
partition-of-unity `Q`-components centred at `β`. -/
private lemma cutoffComponentEuclid_eq_pou_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (y : EuclN) :
    cutoffComponentEuclid (I := I) (M := M) g r s S α P₀.1 P₀.2 y =
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          chartPushedRaw I α
            (fun x : M =>
              transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
                tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x)
            y := by
  classical
  -- The cutoff Euclidean component is the chart-`α` pushforward of the cutoff
  -- scalar field, which decomposes via the manifold-side identity.
  rw [cutoffComponentEuclid_eq_chartPushedRaw (I := I) (M := M) g r s S α
    P₀.1 P₀.2]
  have h_scalar :
      cutoffComponentScalar (I := I) (M := M) g r s S α P₀.1 P₀.2 =
        fun x : M =>
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
                tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x := by
    funext x
    exact cutoffComponentScalar_eq_pou_transport_sum
      (I := I) (M := M) g r s S α P₀ x
  rw [h_scalar]
  -- Push the chart-`α` pushforward through the double finite sum.
  rw [chartPushedRaw_finsetSum (I := I) (M := M) α
    (transportChartCenters (I := I) (M := M) α)
    (fun β x => ∑ Q : TensorCompIdx (E := E) r s,
      transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
        tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) y]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  exact chartPushedRaw_finsetSum (I := I) (M := M) α
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q x => transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
      tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) y

/-! ## An a.e.-congruence helper for finite sums

A finite sum of summands agreeing almost everywhere agrees, as a function,
almost everywhere with the corresponding finite sum of the other summands. -/

/-- If finitely many summands agree almost everywhere, then so do their finite
sums. -/
lemma finsetSum_ae_eq
    (α : M) {ι : Type*} (s : Finset ι) {f h : ι → EuclN → ℝ}
    (hfh : ∀ a ∈ s,
      f a =ᵐ[chartL2Measure (I := I) (M := M) α] h a) :
    (fun y => ∑ a ∈ s, f a y) =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, h a y := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      have hfh_a : f a =ᵐ[chartL2Measure (I := I) (M := M) α] h a :=
        hfh a (Finset.mem_insert_self a t)
      have hfh_t : ∀ b ∈ t,
          f b =ᵐ[chartL2Measure (I := I) (M := M) α] h b :=
        fun b hb => hfh b (Finset.mem_insert_of_mem hb)
      filter_upwards [hfh_a, ih hfh_t] with y hya hyt
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hya, hyt]

/-! ## The smooth-section identity

On a smooth compactly-supported section the cutoff chart component equals, as an
`L²` class, the finite sum over the transport chart centres and component
multi-indices of the transported partition-of-unity components. -/

/-- **The smooth-section cutoff-component decomposition.** For a smooth
compactly-supported `(r, s)`-tensor section `S`, the cutoff chart component of
its image in the `L²` Hilbert space equals the finite sum over the transport
chart centres `β` and the component multi-indices `Q` of the transported
partition-of-unity `Q`-components centred at `β`. -/
private lemma tensorL2ChartComponentCutoff_smooth_eq_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (S : TensorL2 r s g) α P₀ =
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (S : TensorL2 r s g) β Q) := by
  classical
  -- Two `L²` classes are equal iff their representatives agree almost
  -- everywhere.
  apply Lp.ext
  -- The left side agrees a.e. with the concrete cutoff Euclidean chart
  -- component.
  refine (tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn
    (I := I) (M := M) g r s S α P₀).trans ?_
  -- The right side: push the coercion through the double finite sum.
  have h_rhs_coeFn :
      ((∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s
                (S : TensorL2 r s g) β Q)) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) =ᵐ[
          chartL2Measure (I := I) (M := M) α]
        fun y => ∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            chartPushedRaw I α
              (fun x : M =>
                transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
                  tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x)
              y := by
    -- Outer finite sum.
    refine (coeFn_finsetSum_chartL2 (I := I) (M := M) α
      (transportChartCenters (I := I) (M := M) α)
      (fun β => ∑ Q : TensorCompIdx (E := E) r s,
        chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (S : TensorL2 r s g) β Q))).trans ?_
    -- For each centre `β`, the inner finite sum.
    refine finsetSum_ae_eq (I := I) (M := M) α
      (transportChartCenters (I := I) (M := M) α) (fun β _ => ?_)
    refine (coeFn_finsetSum_chartL2 (I := I) (M := M) α
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q => chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (S : TensorL2 r s g) β Q))).trans ?_
    -- Each `(β, Q)`-summand: the transport operator's smooth-section
    -- compatibility.
    refine finsetSum_ae_eq (I := I) (M := M) α
      (Finset.univ : Finset (TensorCompIdx (E := E) r s)) (fun Q _ => ?_)
    exact chartTransitionTransportCLM_coeFn_smooth
      (I := I) (M := M) g r s β α S P₀ Q
  -- The double sum of chart-pushed components is, pointwise, the cutoff
  -- Euclidean chart component.
  have h_pointwise :
      cutoffComponentEuclid (I := I) (M := M) g r s S α P₀.1 P₀.2 =
        fun y => ∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            chartPushedRaw I α
              (fun x : M =>
                transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
                  tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x)
              y := by
    funext y
    exact cutoffComponentEuclid_eq_pou_transport_sum
      (I := I) (M := M) g r s S α P₀ y
  rw [h_pointwise]
  exact h_rhs_coeFn.symm

/-! ## Continuity of the two sides as functions of the abstract `L²` element

Both the cutoff chart component and the transport sum are continuous functions
of the abstract `L²` element: the former is a continuous linear map, the latter
a finite sum of compositions of continuous linear maps. -/

/-- The transport sum is a continuous function of the abstract `L²` element: a
finite sum over the transport chart centres and component multi-indices of
compositions of the transport operator with the canonical chart component, each
continuous. -/
private lemma continuous_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    Continuous (fun u : TensorL2 r s g =>
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s u β Q)) := by
  classical
  refine continuous_finset_sum _ (fun β _ => ?_)
  refine continuous_finset_sum _ (fun Q _ => ?_)
  exact (chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q).continuous.comp
    (continuous_tensorL2ChartComponent (I := I) (M := M) g r s β Q)

/-! ## The abstract `L²` decomposition

Both sides of the decomposition are continuous functions of the abstract `L²`
element and agree on the dense range of the smooth-section embedding, hence
agree everywhere. -/

/-- **The abstract cutoff-component decomposition.** For an arbitrary abstract
`L²` tensor element `u : TensorL2 r s g`, the cutoff chart `P₀`-component of `u`
equals — as an element of `Lp ℝ 2 (chartL2Measure α)` — the finite sum over the
transport chart centres `β` and the component multi-indices `Q` of the
chart-transition transport of the partition-of-unity `Q`-components of `u`.

Both sides are continuous-linear in `u`; they agree on the dense subspace of
smooth compactly-supported sections by
`tensorL2ChartComponentCutoff_smooth_eq_transport_sum`, so the dense-range
equaliser principle extends the identity to every `u`. -/
theorem tensorL2ChartComponentCutoff_eq_pou_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ =
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) := by
  classical
  -- Both sides as functions of the abstract `L²` element.
  set lhs : TensorL2 r s g → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    fun v => tensorL2ChartComponentCutoff (I := I) (M := M) g r s v α P₀
    with hlhs_def
  set rhs : TensorL2 r s g → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    fun v => ∑ β ∈ transportChartCenters (I := I) (M := M) α,
      ∑ Q : TensorCompIdx (E := E) r s,
        chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s v β Q)
    with hrhs_def
  -- It suffices to show the two functions are equal.
  suffices h_eq : lhs = rhs by
    exact congrFun h_eq u
  -- The left side is continuous (a continuous linear map).
  have h_lhs_cont : Continuous lhs := by
    rw [hlhs_def]
    have h_fun : (fun v : TensorL2 r s g =>
        tensorL2ChartComponentCutoff (I := I) (M := M) g r s v α P₀) =
        (tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀) := by
      funext v
      rw [tensorL2ChartComponentCutoffCLM_apply]
    rw [h_fun]
    exact (tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀).continuous
  -- The right side is continuous (a finite sum of continuous compositions).
  have h_rhs_cont : Continuous rhs := by
    rw [hrhs_def]
    exact continuous_transport_sum (I := I) (M := M) g r s α P₀
  -- The two functions agree on the dense range of the smooth-section
  -- embedding `(↑) : SmoothCcTensor g r s → TensorL2 r s g`.
  have h_denseRange :
      DenseRange ((↑) : SmoothCcTensor g r s → TensorL2 r s g) :=
    UniformSpace.Completion.denseRange_coe
  refine h_denseRange.equalizer h_lhs_cont h_rhs_cont ?_
  funext S
  -- On a smooth section the identity is the smooth-section decomposition.
  rw [Function.comp_apply, Function.comp_apply, hlhs_def, hrhs_def]
  exact tensorL2ChartComponentCutoff_smooth_eq_transport_sum
    (I := I) (M := M) g r s S α P₀

/-- **The abstract cutoff-component a.e. decomposition.** For an arbitrary
abstract `L²` tensor element `u : TensorL2 r s g`, the cutoff chart
`P₀`-component of `u` equals, almost everywhere on the Euclidean chart target,
the finite sum over the transport chart centres `β` and the component
multi-indices `Q` of the chart-transition transport of the partition-of-unity
`Q`-components of `u`.

This is the a.e.-identity form of `tensorL2ChartComponentCutoff_eq_pou_transport_sum`,
obtained by passing to representatives via the `L²` coercion lemmas. -/
theorem tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          ((chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
  classical
  -- Rewrite the left side by the equality of `L²` classes.
  rw [tensorL2ChartComponentCutoff_eq_pou_transport_sum
    (I := I) (M := M) g r s u α P₀]
  -- The representative of the double finite sum is, a.e., the double finite sum
  -- of the representatives.
  refine (coeFn_finsetSum_chartL2 (I := I) (M := M) α
    (transportChartCenters (I := I) (M := M) α)
    (fun β => ∑ Q : TensorCompIdx (E := E) r s,
      chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s u β Q))).trans ?_
  refine finsetSum_ae_eq (I := I) (M := M) α
    (transportChartCenters (I := I) (M := M) α) (fun β _ => ?_)
  exact coeFn_finsetSum_chartL2 (I := I) (M := M) α
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q => chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
      (tensorL2ChartComponent (I := I) (M := M) g r s u β Q))

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

example (α : M) : Finset M := transportChartCenters (I := I) (M := M) α

example (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ =
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) :=
  tensorL2ChartComponentCutoff_eq_pou_transport_sum
    (I := I) (M := M) g r s u α P₀

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
