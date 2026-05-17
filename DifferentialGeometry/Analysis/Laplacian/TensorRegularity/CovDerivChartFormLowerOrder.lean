import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.CovDerivChartForm

/-!
# Chart-coordinate lower-order remainder of the tensor `H^1` Dirichlet integrand

This file completes the chart-coordinate decomposition of the pointwise
integrand of the `H^1` Dirichlet form on `(r, s)`-tensor sections, begun in
`CovDerivChartForm.lean`. There the (component-coupled) principal part
`covPrincipalIntegrand` was built; here the lower-order remainder
`covLowerOrderIntegrand` is assembled and the headline coupled identity is
proved.

The covariant-derivative chart-component formula
`covDerivComponent_eq_euclidPartial_add_lowerOrder` expresses the raw
chart-scalar component of the chart-coordinate covariant derivative as
`euclidPartial + covDerivLowerOrderTerm` — a plain chart-Euclidean partial
derivative plus a zeroth-order Christoffel correction. The product of two such
sums splits into four groups:

```
(∂S + LO_S) · (∂T + LO_T)
  = ∂S · ∂T                    (principal — covPrincipalIntegrand)
  + ∂S · LO_T + LO_S · ∂T + LO_S · LO_T   (lower order — covLowerOrderIntegrand)
```

The lower-order remainder collects the three non-principal groups, weighted by
the same component-coupled chart-frame tensor-metric Gram `covChartMetricGram`
and un-weighted inverse Gram `chartInvGramEuclid` prefactor as the principal
part.

## Main definitions

* `covLowerOrderIntegrand g r s S T α` — the component-coupled lower-order
  remainder of the chart-coordinate Dirichlet integrand.

## Main results

* `tensorCovDerivPointwiseInner_chart_eq` — the headline coupled identity: in
  chart-Euclidean coordinates the pointwise `H^1` Dirichlet integrand
  `tensorCovDerivPointwiseInner g r s S T = ⟨∇S, ∇T⟩` equals
  `covPrincipalIntegrand + covLowerOrderIntegrand`.
* `covLowerOrderIntegrand_contDiffOn` — the lower-order remainder is `C^∞` on
  the Euclidean chart target.
* `covLowerOrderIntegrand_eqOn` — the lower-order remainder agrees, on the
  Euclidean chart target, with the genuine integrand minus the principal part;
  the principal/lower-order split is exact.
* `covLowerOrderIntegrand_symm` — symmetry of the lower-order remainder under
  the `(S, T)` swap.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## The lower-order remainder integrand

The lower-order remainder collects the three non-principal product groups of
the component-formula expansion `(∂S + LO_S) · (∂T + LO_T)`: the cross terms
`∂S · LO_T` and `LO_S · ∂T`, and the pure lower-order term `LO_S · LO_T`. The
prefactor — the chart-frame tensor-metric Gram `covChartMetricGram` and the
un-weighted inverse Gram `chartInvGramEuclid` — is identical to the principal
part `covPrincipalIntegrand`. -/

/-- **The component-coupled lower-order remainder of the chart-coordinate
Dirichlet integrand.** Same `covChartMetricGram` / `chartInvGramEuclid`
prefactor as `covPrincipalIntegrand`, but the inner factor is the sum of the
three non-principal product groups: `∂S · LO_T`, `LO_S · ∂T`, `LO_S · LO_T`,
where `∂` denotes the chart-Euclidean partial derivative of the Euclidean
push-forward of a raw chart component and `LO` denotes the zeroth-order
Christoffel correction `covDerivLowerOrderTerm`. -/
noncomputable def covLowerOrderIntegrand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
      ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                (euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s S α P.1 P.2)) y *
                    covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α l Q.1 Q.2 y
                  + covDerivLowerOrderTerm (I := I) (M := M)
                        g r s S α k P.1 P.2 y *
                      euclidPartial (E := E) l
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s T α Q.1 Q.2)) y
                  + covDerivLowerOrderTerm (I := I) (M := M)
                        g r s S α k P.1 P.2 y *
                      covDerivLowerOrderTerm (I := I) (M := M)
                        g r s T α l Q.1 Q.2 y)

/-- Unfolding lemma for `covLowerOrderIntegrand`. -/
lemma covLowerOrderIntegrand_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covLowerOrderIntegrand (I := I) (M := M) g r s S T α y =
      ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                  (euclidPartial (E := E) k
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s S α P.1 P.2)) y *
                      covDerivLowerOrderTerm (I := I) (M := M)
                        g r s T α l Q.1 Q.2 y
                    + covDerivLowerOrderTerm (I := I) (M := M)
                          g r s S α k P.1 P.2 y *
                        euclidPartial (E := E) l
                          (chartPushedRaw I α
                            (tensorChartComponentRaw (I := I) (M := M)
                              g r s T α Q.1 Q.2)) y
                    + covDerivLowerOrderTerm (I := I) (M := M)
                          g r s S α k P.1 P.2 y *
                        covDerivLowerOrderTerm (I := I) (M := M)
                          g r s T α l Q.1 Q.2 y) := rfl

/-! ## The headline coupled identity

Splitting the inner product `(∂S + LO_S) · (∂T + LO_T)` of the component-coupled
double sum `tensorCovDerivPointwiseInner_chart_eq_component_sum` into the
`∂S · ∂T` group and the three non-principal groups, the former collects into
the principal part `covPrincipalIntegrand` and the latter into the lower-order
remainder `covLowerOrderIntegrand`. The split is purely the distributive law
`(a + b)(c + d) = a·c + (a·d + b·c + b·d)` summed over the four nested
`Finset`s. -/

/-- **The chart-coordinate decomposition of the tensor `H^1` Dirichlet
integrand.** For `y` in the Euclidean chart target `chartTargetEuclid α`, set
`b := (extChartAt I α).symm (toEuclidean.symm y)`. The pointwise integrand
`tensorCovDerivPointwiseInner g r s S T b = ⟨∇S, ∇T⟩` of the `H^1` Dirichlet
form decomposes, in chart-Euclidean coordinates, as the component-coupled
principal part `covPrincipalIntegrand` plus the component-coupled lower-order
remainder `covLowerOrderIntegrand`.

The principal part is **component-coupled**: the chart-frame tensor metric
`covChartMetricGram` is not diagonal. -/
theorem tensorCovDerivPointwiseInner_chart_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      covPrincipalIntegrand (I := I) (M := M) g r s S T α y +
        covLowerOrderIntegrand (I := I) (M := M) g r s S T α y := by
  classical
  -- Start from the single component-coupled double sum.
  rw [tensorCovDerivPointwiseInner_chart_eq_component_sum (I := I) (M := M)
    g r s S T α hy]
  -- Unfold the principal part and the lower-order remainder.
  rw [covPrincipalIntegrand_def, covLowerOrderIntegrand_def]
  -- Distribute the `(P, Q)` sum across the principal / lower-order split.
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  -- `covG · A = covG · A₁ + covG · A₂` once `A = A₁ + A₂`.
  rw [← mul_add]
  congr 1
  -- Distribute the `(k, l)` sum across the split.
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  -- Pointwise: `Ginv · (∂S + LO_S)(∂T + LO_T) =
  --   Ginv · ∂S∂T + Ginv · (∂S·LO_T + LO_S·∂T + LO_S·LO_T)`.
  ring

/-! ## Smoothness of the lower-order remainder

On the Euclidean chart target the prefactors `covChartMetricGram` and
`chartInvGramEuclid` are `C^∞` (`covChartMetricGram_contDiffOn`,
`chartInvGramEuclid_contDiffOn`). The Euclidean push-forward
`chartPushedRaw I α (tensorChartComponentRaw …)` of a raw chart component is
`C^∞` there — the raw component is smooth on the chart source
(`tensorChartComponentRaw_contMDiffOn_chart_source`), transported through
`(extChartAt I α).symm` and `toEuclidean.symm` — hence its chart-Euclidean
partial derivative `euclidPartial` is again `C^∞`. The lower-order correction
`covDerivLowerOrderTerm` is `C^∞` (`covDerivComponent_lowerOrder_contDiffOn`,
with the raw-component `C^∞` hypothesis discharged from the same push-forward
smoothness). A finite sum and product of `C^∞` functions is `C^∞`. -/

/-- The Euclidean push-forward `chartPushedRaw I α (tensorChartComponentRaw …)`
of a raw chart component of a smooth compactly-supported tensor section is
`ContDiffOn ℝ ∞` on the Euclidean chart target. -/
theorem chartPushedRaw_tensorChartComponentRaw_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- The raw component is `C^∞` on the chart source.
  have hraw_src : ContMDiffOn I 𝓘(ℝ) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      ((chartAt H α).source) :=
    tensorChartComponentRaw_contMDiffOn_chart_source (I := I) (M := M)
      g r s S α Idx Jdx
  -- The chart source coincides with `(extChartAt I α).source`.
  have hraw_extsrc : ContMDiffOn I 𝓘(ℝ) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      ((extChartAt I α).source) := by
    rw [extChartAt_source]; exact hraw_src
  -- Compose with `(extChartAt I α).symm`: smooth on the chart target.
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (extChartAt I α).source := fun y hy => (extChartAt I α).map_target hy
  have hcomp_E : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target :=
    hraw_extsrc.comp hsymm hmaps
  have hcontDiff_E : ContDiffOn ℝ ∞
      ((tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target :=
    hcomp_E.contDiffOn
  -- Pre-compose with the linear isometry `toEuclidean.symm`.
  have hcomp_eucl : ContDiffOn ℝ ∞
      (((tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) ∘
          (extChartAt I α).symm) ∘
        (toEuclidean.symm :
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine hcontDiff_E.comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
  -- On the chart target `chartPushedRaw` is exactly this composition.
  refine hcomp_eucl.congr (fun z hz => ?_)
  exact chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hz

/-- The `k`-th chart-Euclidean partial derivative of the Euclidean push-forward
of a raw chart component is `ContDiffOn ℝ ∞` on the Euclidean chart target. -/
theorem euclidPartial_chartPushedRaw_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (euclidPartial (E := E) k
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- `euclidPartial k u = fderiv ℝ u · (single k 1)`. On the open Euclidean
  -- chart target, the Fréchet derivative of a `C^∞` function is `C^∞`, and
  -- evaluation at a fixed vector is a continuous linear map.
  set u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushedRaw I α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) with hu_def
  have hu : ContDiffOn ℝ ∞ u (chartTargetEuclid (I := I) (M := M) α) :=
    chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M)
      g r s S α Idx Jdx
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The Fréchet derivative is `C^∞` on the open set.
  have hfderiv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ u z)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have hsucc : ContDiffOn ℝ ((∞ : WithTop ℕ∞) + 1) u
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]; exact hu
    have hfw : ContDiffOn ℝ ∞ (fderivWithin ℝ u
        (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_succ_iff_fderivWithin hopen.uniqueDiffOn).mp hsucc).2.2
    refine hfw.congr (fun z hz => ?_)
    exact (fderivWithin_of_isOpen (f := u) (𝕜 := ℝ) hopen hz).symm
  -- Evaluation at `single k 1` is a continuous linear map; compose.
  have hcomp : ContDiffOn ℝ ∞
      ((fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
          L (EuclideanSpace.single k 1)) ∘ (fun z => fderiv ℝ u z))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single k 1)).contDiff.comp_contDiffOn hfderiv
  refine hcomp.congr (fun z _ => ?_)
  rw [hu_def]
  rfl

/-- **The lower-order remainder is `C^∞` on the Euclidean chart target.** A
finite sum and product of `C^∞` functions: the prefactors `covChartMetricGram`
and `chartInvGramEuclid` are `C^∞`, the chart-Euclidean partials of the raw
component push-forwards are `C^∞`, and the lower-order corrections
`covDerivLowerOrderTerm` are `C^∞`. -/
theorem covLowerOrderIntegrand_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M) :
    ContDiffOn ℝ ∞
      (covLowerOrderIntegrand (I := I) (M := M) g r s S T α)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- The raw-component push-forward `C^∞` hypotheses for `S` and `T`.
  have hrawS : ∀ (Idx' : Fin r → Fin (Module.finrank ℝ E))
      (Jdx' : Fin s → Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx'))
        (chartTargetEuclid (I := I) (M := M) α) := fun Idx' Jdx' =>
    chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M)
      g r s S α Idx' Jdx'
  have hrawT : ∀ (Idx' : Fin r → Fin (Module.finrank ℝ E))
      (Jdx' : Fin s → Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx'))
        (chartTargetEuclid (I := I) (M := M) α) := fun Idx' Jdx' =>
    chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M)
      g r s T α Idx' Jdx'
  -- The `(P, Q)`-summand is `C^∞`.
  have hsummand : ∀ P Q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                  (euclidPartial (E := E) k
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s S α P.1 P.2)) y *
                      covDerivLowerOrderTerm (I := I) (M := M)
                        g r s T α l Q.1 Q.2 y
                    + covDerivLowerOrderTerm (I := I) (M := M)
                          g r s S α k P.1 P.2 y *
                        euclidPartial (E := E) l
                          (chartPushedRaw I α
                            (tensorChartComponentRaw (I := I) (M := M)
                              g r s T α Q.1 Q.2)) y
                    + covDerivLowerOrderTerm (I := I) (M := M)
                          g r s S α k P.1 P.2 y *
                        covDerivLowerOrderTerm (I := I) (M := M)
                          g r s T α l Q.1 Q.2 y))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro P Q
    -- The chart-frame tensor-metric Gram prefactor is `C^∞`.
    have hgram : ContDiffOn ℝ ∞
        (covChartMetricGram (I := I) (M := M) g r s α P Q)
        (chartTargetEuclid (I := I) (M := M) α) :=
      covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q
    -- The inner `(k, l)`-summand is `C^∞`.
    have hinner : ∀ k l : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            chartInvGramEuclid (I := I) g α k l y *
              (euclidPartial (E := E) k
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M)
                        g r s S α P.1 P.2)) y *
                  covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α l Q.1 Q.2 y
                + covDerivLowerOrderTerm (I := I) (M := M)
                      g r s S α k P.1 P.2 y *
                    euclidPartial (E := E) l
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s T α Q.1 Q.2)) y
                + covDerivLowerOrderTerm (I := I) (M := M)
                      g r s S α k P.1 P.2 y *
                    covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α l Q.1 Q.2 y))
          (chartTargetEuclid (I := I) (M := M) α) := by
      intro k l
      have hGinv : ContDiffOn ℝ ∞ (chartInvGramEuclid (I := I) g α k l)
          (chartTargetEuclid (I := I) (M := M) α) :=
        chartInvGramEuclid_contDiffOn (I := I) (M := M) g α k l
      -- The four building blocks.
      have hSpartial : ContDiffOn ℝ ∞
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s S α P.1 P.2)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M)
          g r s S α k P.1 P.2
      have hTpartial : ContDiffOn ℝ ∞
          (euclidPartial (E := E) l
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s T α Q.1 Q.2)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M)
          g r s T α l Q.1 Q.2
      have hSlo : ContDiffOn ℝ ∞
          (covDerivLowerOrderTerm (I := I) (M := M) g r s S α k P.1 P.2)
          (chartTargetEuclid (I := I) (M := M) α) :=
        covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M)
          g r s S α k P.1 P.2 hrawS
      have hTlo : ContDiffOn ℝ ∞
          (covDerivLowerOrderTerm (I := I) (M := M) g r s T α l Q.1 Q.2)
          (chartTargetEuclid (I := I) (M := M) α) :=
        covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M)
          g r s T α l Q.1 Q.2 hrawT
      -- The three product groups are `C^∞`; so is their sum, and the product
      -- with the inverse Gram entry.
      exact hGinv.mul (((hSpartial.mul hTlo).add (hSlo.mul hTpartial)).add
        (hSlo.mul hTlo))
    -- A finite sum of `C^∞` functions is `C^∞`.
    have hklsum : ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                (euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s S α P.1 P.2)) y *
                    covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α l Q.1 Q.2 y
                  + covDerivLowerOrderTerm (I := I) (M := M)
                        g r s S α k P.1 P.2 y *
                      euclidPartial (E := E) l
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s T α Q.1 Q.2)) y
                  + covDerivLowerOrderTerm (I := I) (M := M)
                        g r s S α k P.1 P.2 y *
                      covDerivLowerOrderTerm (I := I) (M := M)
                        g r s T α l Q.1 Q.2 y))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ContDiffOn.sum (fun k _ => ContDiffOn.sum (fun l _ => hinner k l))
    exact hgram.mul hklsum
  -- A finite sum of `C^∞` functions is `C^∞`; the lower-order remainder is,
  -- definitionally, exactly this finite sum.
  have hsum : ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramEuclid (I := I) g α k l y *
                    (euclidPartial (E := E) k
                          (chartPushedRaw I α
                            (tensorChartComponentRaw (I := I) (M := M)
                              g r s S α P.1 P.2)) y *
                        covDerivLowerOrderTerm (I := I) (M := M)
                          g r s T α l Q.1 Q.2 y
                      + covDerivLowerOrderTerm (I := I) (M := M)
                            g r s S α k P.1 P.2 y *
                          euclidPartial (E := E) l
                            (chartPushedRaw I α
                              (tensorChartComponentRaw (I := I) (M := M)
                                g r s T α Q.1 Q.2)) y
                      + covDerivLowerOrderTerm (I := I) (M := M)
                            g r s S α k P.1 P.2 y *
                          covDerivLowerOrderTerm (I := I) (M := M)
                            g r s T α l Q.1 Q.2 y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    ContDiffOn.sum (fun P _ => ContDiffOn.sum (fun Q _ => hsummand P Q))
  exact hsum

/-! ## The principal/lower-order split is exact

The headline `tensorCovDerivPointwiseInner_chart_eq` reads, rearranged: on the
Euclidean chart target the lower-order remainder is exactly the genuine
chart-coordinate Dirichlet integrand minus the principal part. This `Set.EqOn`
form records that the decomposition is exact and is the channel through which a
downstream integral over the chart target reduces the lower-order remainder to
genuine-integrand and principal-part contributions. -/

/-- **The principal/lower-order split is exact.** On the Euclidean chart target
`chartTargetEuclid α`, the lower-order remainder `covLowerOrderIntegrand`
equals the genuine chart-coordinate Dirichlet integrand
`tensorCovDerivPointwiseInner g r s S T ((extChartAt I α).symm (toEuclidean.symm ·))`
minus the principal part `covPrincipalIntegrand`. -/
theorem covLowerOrderIntegrand_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M) :
    Set.EqOn (covLowerOrderIntegrand (I := I) (M := M) g r s S T α)
      (fun y => tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) -
          covPrincipalIntegrand (I := I) (M := M) g r s S T α y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  have h := tensorCovDerivPointwiseInner_chart_eq (I := I) (M := M)
    g r s S T α hy
  -- `LHS = P + L` ⟹ `L = LHS − P`.
  change covLowerOrderIntegrand (I := I) (M := M) g r s S T α y =
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) -
      covPrincipalIntegrand (I := I) (M := M) g r s S T α y
  rw [h]
  ring

/-! ## Symmetry of the lower-order remainder

Swapping the section pair `(S, T)` swaps the roles of `S` and `T` in every
product group: `∂S · LO_T ↔ LO_S · ∂T` and `LO_S · LO_T ↔ LO_T · LO_S`, with
the two component multi-index pairs `P, Q` and the two chart directions `k, l`
also swapped. The chart-frame tensor-metric Gram `covChartMetricGram` and the
inverse Gram `chartInvGramEuclid` are both symmetric, so the value is
unchanged. -/

/-- **Symmetry of the lower-order remainder under the `(S, T)` swap.** -/
theorem covLowerOrderIntegrand_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covLowerOrderIntegrand (I := I) (M := M) g r s S T α y =
      covLowerOrderIntegrand (I := I) (M := M) g r s T S α y := by
  classical
  rw [covLowerOrderIntegrand_def, covLowerOrderIntegrand_def]
  -- Swap the two outer `(P, Q)` sums.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  -- The chart-frame tensor-metric Gram is symmetric in `(Q, P)`.
  rw [covChartMetricGram_symm (I := I) (M := M) g r s α Q P y]
  congr 1
  -- Swap the two inner `(k, l)` sums.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  -- The inverse Gram is symmetric in `(l, k)`.
  rw [show chartInvGramEuclid (I := I) g α l k y =
      chartInvGramEuclid (I := I) g α k l y from ?_]
  · ring
  · -- Symmetry of the chart inverse Gram matrix.
    rw [chartInvGramEuclid_def, chartInvGramEuclid_def, chartInvGramOnE_def,
      chartInvGramOnE_def]
    have hHerm : (chartInvGramMatrix (I := I) g α
        ((extChartAt I α).symm (toEuclidean.symm y))).IsHermitian := by
      unfold chartInvGramMatrix
      exact (chartGramMatrix_isHermitian (I := I) g α
        ((extChartAt I α).symm (toEuclidean.symm y))).inv
    have hsymm := hHerm.apply k l
    rw [star_trivial] at hsymm
    exact hsymm

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
