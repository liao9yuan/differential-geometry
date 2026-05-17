import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartTestDecoupling
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartLowerOrderLimits

/-!
# The cross-right divergence-form `n → ∞` `L²`-limit

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with nonzero resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`,
and a base component multi-index `P₀`, the covariant-Leibniz **cross-right**
term of the per-approximant chart-bilinear divergence-form identity, evaluated
at the partition-of-unity-weighted smooth approximant
`Tₙ := pouSmul g r s α (eigenvectorSmoothApprox g r s h_uniform i n).toCcTensor`,
after the chart-pull `tensorCovDerivCrossRight_integral_eq_chartPull` and the
test-section decoupling
`tensorComponentEuclid_covDerivAlongGrad_rotatedTestSection_chartTestPullback_eqOn`,
splits into a `φ`-undifferentiated part and a part carrying `euclidPartial l φ`:

```
Σ_l ∫ y in chartTargetEuclid α, densityOnEuclid g α y * c[n,l] y * euclidPartial l φ y ∂volume
```

with

```
c[n,l] y = ∑_P ∑_Q covChartMetricGram g r s α P Q y
  * cutoffComponentEuclid g r s Tₙ α P.1 P.2 y
  * crossRightTestGradCoeff g r s α P₀ Q l y.
```

This `euclidPartial l φ`-carrying part must be folded into a single `φ`-term by
integration by parts. The limiting coefficient would involve a non-smooth `Lp`
chart component of the abstract eigenvector, so integration by parts at the
limit is impossible. Instead it is performed at level `n`, where the smooth
approximant makes `c[n,l]` globally `C^∞`, and the `n → ∞` `L²`-limit of the
resulting chart-Euclidean divergence is taken afterwards.

## The cutoff/partition-of-unity bridge

The cutoff Euclidean chart component `cutoffComponentEuclid` of the
partition-of-unity-weighted section `pouSmul g r s α S` equals the
partition-of-unity-weighted Euclidean chart component `tensorChartComponent` of
`S`: the chart-kernel cutoff `chartKernelCutoff α` equals `1` wherever the
partition-of-unity weight is nonzero, so the extra cutoff factor is inert. This
bridge identifies `c[n,l]`, built from `cutoffComponentEuclid`, with a finite
`C^∞`-coefficient-weighted sum of the partition-of-unity chart-component atom
`tensorChartComponent g r s wₙ.toCcTensor α P` — whose `n → ∞` `L²`-limit and
chart-Euclidean partial `L²`-limit are the committed objects `componentLpLimit`
and `partialLpLimit`.

## Main definitions

* `crossRightTestGradTerm g r s S α P₀ l` — the cross-right gradient-term
  coefficient `c[S,l]` for a smooth section `S` (built from
  `cutoffComponentEuclid g r s (pouSmul g r s α S)`).
* `crossRightGradCoeffDivLimit g r s h_uniform i α P₀` — the explicit `n → ∞`
  `L²`-limit of `∑_l euclidPartial l (densityOnEuclid g α · c[n,l])`.

## Main results

* `crossRightTestGradTerm_byParts` — the per-`n` integration-by-parts rewrite of
  the `euclidPartial l φ`-carrying part into a single `φ`-term.
* `crossRightGradCoeffDivSum_tendsto` — the `n → ∞` `L²`-convergence of the
  chart-Euclidean divergence to `crossRightGradCoeffDivLimit`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix ENNReal NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

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

/-! ## The cutoff/partition-of-unity bridge

The cutoff-weighted scalar chart component `cutoffComponentScalar` of the
partition-of-unity-weighted section `pouSmul g r s α S` is the chart-kernel
cutoff `chartKernelCutoff α` times the raw chart component of `pouSmul g r s α
S`, which by `tensorChartComponentRaw_smul_pou` is the partition-of-unity weight
`chartAtlasPOU I M α` times the raw chart component of `S`. The chart-kernel
cutoff equals `1` on the closed support of the partition-of-unity weight
(`chartKernelCutoff_eqOn_one`), so the cutoff factor multiplies `1` wherever the
weight is nonzero — the cutoff-weighted scalar component of `pouSmul g r s α S`
equals the partition-of-unity-weighted scalar component `tensorChartComponentPou`
of `S`. -/

/-- The cutoff-weighted scalar chart component of the partition-of-unity-weighted
section `pouSmul g r s α S` equals the partition-of-unity-weighted scalar
chart component `tensorChartComponentPou` of `S`: the chart-kernel cutoff is `1`
wherever the partition-of-unity weight is nonzero. -/
private lemma cutoffComponentScalar_pouSmul_eq_tensorChartComponentPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    cutoffComponentScalar (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α Idx Jdx =
      tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx := by
  classical
  funext x
  -- Expand both sides; the raw component of `pouSmul g r s α S` is the weight
  -- times the raw component of `S`.
  rw [cutoffComponentScalar,
    tensorChartComponentRaw_smul_pou (I := I) (M := M) g r s α S Idx Jdx,
    tensorChartComponentPou]
  beta_reduce
  by_cases hw : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0
  · -- Where the partition-of-unity weight vanishes, both sides are zero.
    simp only [hw, zero_mul, mul_zero]
  · -- Where the weight is nonzero, the point is in its closed support, on which
    -- the chart-kernel cutoff equals `1`.
    have hx_supp : x ∈ tsupport
        (fun y : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) :=
      subset_tsupport _ (by rw [Function.mem_support]; exact hw)
    rw [chartKernelCutoff_eqOn_one (I := I) (M := M) α hx_supp, Pi.one_apply,
      one_mul]

/-- **The cutoff/partition-of-unity bridge.** The cutoff Euclidean chart
component `cutoffComponentEuclid` of the partition-of-unity-weighted section
`pouSmul g r s α S` equals the partition-of-unity-weighted Euclidean chart
component `tensorChartComponent` of `S`. Both are the chart push-forward of a
manifold-side scalar; the chart-kernel cutoff is `1` wherever the
partition-of-unity weight is nonzero, so the extra cutoff factor is inert. -/
theorem cutoffComponentEuclid_pouSmul_eq_tensorChartComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    cutoffComponentEuclid (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α Idx Jdx =
      tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx := by
  rw [show cutoffComponentEuclid (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α Idx Jdx =
      chartPushedRaw I α
        (cutoffComponentScalar (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α S) α Idx Jdx) from rfl,
    cutoffComponentScalar_pouSmul_eq_tensorChartComponentPou
      (I := I) (M := M) g r s α S Idx Jdx, tensorChartComponent_def]

/-! ## The cross-right gradient-term coefficient

The `euclidPartial l φ`-carrying part of the chart-pulled, test-decoupled
cross-right term is `∑_l ∫ densityOnEuclid g α · c[S,l] · euclidPartial l φ`,
where `c[S,l]` is the cross-right gradient-term coefficient: a finite sum, over
component multi-index pairs `(P, Q)`, of the chart-frame tensor-metric Gram
`covChartMetricGram g r s α P Q`, the cutoff Euclidean chart component
`cutoffComponentEuclid` of the partition-of-unity-weighted approximant
`pouSmul g r s α S`, and the cross-right test-decoupling gradient coefficient
`crossRightTestGradCoeff g r s α P₀ Q l`.

By the cutoff/partition-of-unity bridge the cutoff chart component of the
partition-of-unity-weighted section is the partition-of-unity chart-component
atom `tensorChartComponent g r s S α P`, so `c[S,l]` is a finite
`C^∞`-coefficient-weighted sum of that atom. -/

/-- **The cross-right gradient-term coefficient `c[S,l]`.** For a chart center
`α`, ranks `(r, s)`, a smooth compactly-supported section `S`, a base component
multi-index `P₀`, and a chart direction `l`, the finite sum, over component
multi-index pairs `(P, Q)`, of the chart-frame tensor-metric Gram
`covChartMetricGram g r s α P Q`, the cutoff Euclidean chart component of the
partition-of-unity-weighted approximant `pouSmul g r s α S` at `P`, and the
cross-right test-decoupling gradient coefficient `crossRightTestGradCoeff`. -/
noncomputable def crossRightTestGradTerm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
            cutoffComponentEuclid (I := I) (M := M) g r s
              (pouSmul (I := I) (M := M) g r s α S) α P.1 P.2 y *
          crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y

/-! ## The `T`-independent `C^∞` factor of the density-weighted coefficient

Multiplying the cross-right gradient-term coefficient `c[S,l]` by the chart
density `densityOnEuclid g α` collects, per component multi-index pair `(P, Q)`,
the `T`-independent factor `crossRightDivFactor`: the chart density, the
chart-frame tensor-metric Gram `covChartMetricGram g r s α P Q`, and the
cross-right test-decoupling gradient coefficient `crossRightTestGradCoeff`. It is
`C^∞` on the open Euclidean chart target, being a product of `C^∞` factors. -/

/-- The `T`-independent factor of the `(P, Q, l)`-summand of the density-weighted
cross-right gradient-term coefficient: the chart density, the chart-frame
tensor-metric Gram, and the cross-right test-decoupling gradient coefficient. -/
private def crossRightDivFactor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
      crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y

/-- The `T`-independent factor of the density-weighted cross-right gradient-term
coefficient is `C^∞` on the Euclidean chart target. -/
private lemma crossRightDivFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞ (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q)
      (chartTargetEuclid (I := I) (M := M) α) :=
  ((densityOnEuclid_contDiffOn (I := I) g α).mul
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q)).mul
    (crossRightTestGradCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q l)

/-- The chart-Euclidean partial of the `T`-independent `C^∞` factor
`crossRightDivFactor` is `C^∞` on the Euclidean chart target. -/
private lemma euclidPartial_crossRightDivFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞
      (euclidPartial (E := E) l
        (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q))
      (chartTargetEuclid (I := I) (M := M) α) :=
  euclidPartial_contDiffOn_target (I := I) (M := M) α l
    (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)

/-! ## The density-weighted coefficient as a finite component-atom sum

By the cutoff/partition-of-unity bridge the cutoff chart component of
`pouSmul g r s α S` is the partition-of-unity chart-component atom
`tensorChartComponent g r s S α P`. Distributing the chart density across the
double finite sum of `c[S,l]` collects, per pair `(P, Q)`, the `T`-independent
`C^∞` factor `crossRightDivFactor` against that atom. -/

/-- The chart density times the cross-right gradient-term coefficient
`c[S,l]` is the double finite sum, over component multi-index pairs `(P, Q)`, of
the `T`-independent factor `crossRightDivFactor` times the partition-of-unity
chart-component atom `tensorChartComponent g r s S α P`. -/
private lemma densityOnEuclid_mul_crossRightTestGradTerm_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    (fun y => densityOnEuclid (I := I) g α y *
        crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l y) =
      fun y =>
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q y *
              tensorChartComponent (I := I) (M := M) g r s S α P.1 P.2 y := by
  classical
  funext y
  rw [crossRightTestGradTerm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [crossRightDivFactor,
    cutoffComponentEuclid_pouSmul_eq_tensorChartComponent
      (I := I) (M := M) g r s α S P.1 P.2]
  ring

/-! ## Smoothness of the density-weighted coefficient on the chart target

The cross-right gradient-term coefficient `c[S,l]` is, by the cutoff/partition-
of-unity bridge and `densityOnEuclid_mul_crossRightTestGradTerm_eq`, a finite
sum of products of the `C^∞` factor `crossRightDivFactor` and the globally
`C^∞` chart-component atom `tensorChartComponent g r s S α P`. The chart density
times `c[S,l]` is therefore `C^∞` on the open Euclidean chart target. -/

/-- The chart density times the cross-right gradient-term coefficient `c[S,l]`
is `C^∞` on the Euclidean chart target. -/
private lemma densityOnEuclid_mul_crossRightTestGradTerm_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y => densityOnEuclid (I := I) g α y *
        crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  rw [densityOnEuclid_mul_crossRightTestGradTerm_eq (I := I) (M := M)
    g r s S α P₀ l]
  refine ContDiffOn.sum (fun P _ => ContDiffOn.sum (fun Q _ => ?_))
  exact (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q).mul
    ((tensorChartComponent_contDiff' (I := I) (M := M)
      g r s S α P.1 P.2).contDiffOn)

/-! ## Integration by parts on the cross-right gradient term

The chart-Euclidean integration-by-parts identity `chartTarget_integral_byParts`
moves the derivative from the test function `φ` onto the `C^∞` coefficient
`densityOnEuclid g α · c[S,l]`, with a sign change. Because `φ` has compact
support contained in the open Euclidean chart target, no boundary term appears.
Summing over the chart directions `l` and pulling the finite sum out of the
integral folds the `euclidPartial l φ`-carrying part of the cross-right term
into a single `φ`-term carrying the chart-Euclidean divergence
`∑_l euclidPartial l (densityOnEuclid g α · c[S,l])`. -/

/-- The product of the chart-Euclidean partial of the density-weighted
cross-right gradient-term coefficient and a chart-target-supported test function
is globally `C^∞` with compact support, hence integrable. -/
private lemma integrable_euclidPartial_crossRightTestGradTerm_mul_test
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    {φ : EuclN → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_cs : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Integrable
      (fun y => euclidPartial (E := E) l
          (fun z => densityOnEuclid (I := I) g α z *
            crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l z) y * φ y)
      (volume : Measure EuclN) := by
  classical
  -- The integrand is globally `C^∞` with compact support: `C^∞` on the chart
  -- target (a product of a chart-target-`C^∞` factor and `φ`), vanishing off the
  -- compact support of `φ`.
  have hcontDiff : ContDiff ℝ ∞
      (fun y => euclidPartial (E := E) l
          (fun z => densityOnEuclid (I := I) g α z *
            crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l z) y *
        φ y) :=
    contDiff_partial_coeff_mul_test (I := I) (M := M) α l
      (densityOnEuclid_mul_crossRightTestGradTerm_contDiffOn
        (I := I) (M := M) g r s S α P₀ l)
      hφ.contDiffOn hφ_supp
  have hsupp : HasCompactSupport
      (fun y => euclidPartial (E := E) l
          (fun z => densityOnEuclid (I := I) g α z *
            crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l z) y *
        φ y) :=
    hasCompactSupport_partial_coeff_mul_test (E := E) l hφ_cs
  exact hcontDiff.continuous.integrable_of_hasCompactSupport hsupp

/-- **The per-`n` integration-by-parts rewrite of the cross-right gradient
term.** For a chart center `α`, ranks `(r, s)`, a smooth compactly-supported
section `S`, a base component multi-index `P₀`, and a Euclidean test function
`φ` that is `C^∞` with compact support contained in the Euclidean chart target,
the `euclidPartial l φ`-carrying part `∑_l ∫ densityOnEuclid g α · c[S,l] ·
euclidPartial l φ` of the chart-pulled, test-decoupled cross-right term equals
the negative of the single `φ`-term carrying the chart-Euclidean divergence
`∑_l euclidPartial l (densityOnEuclid g α · c[S,l])`.

`c[S,l]` is the cross-right gradient-term coefficient `crossRightTestGradTerm`.
The identity is the chart-Euclidean integration-by-parts `chartTarget_integral_
byParts` applied per chart direction `l` — `φ` has compact support inside the
open chart target, so no boundary term appears — followed by pulling the finite
sum out of the single `φ`-integral. -/
theorem crossRightTestGradTerm_byParts
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    {φ : EuclN → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_cs : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∑ l : Fin (Module.finrank ℝ E),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
              crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l y *
            euclidPartial (E := E) l φ y ∂(volume : Measure EuclN) =
      -∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ l : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) l
              (fun z => densityOnEuclid (I := I) g α z *
                crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l z) y) *
          φ y ∂(volume : Measure EuclN) := by
  classical
  -- The per-direction integration-by-parts identity.
  have hIBP : ∀ l : Fin (Module.finrank ℝ E),
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
              crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l y *
            euclidPartial (E := E) l φ y ∂(volume : Measure EuclN) =
        -∫ y in chartTargetEuclid (I := I) (M := M) α,
          euclidPartial (E := E) l
              (fun z => densityOnEuclid (I := I) g α z *
                crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l z) y *
            φ y ∂(volume : Measure EuclN) := by
    intro l
    -- Transport the integration-by-parts identity through the measure identity
    -- `Measure.map toEuclidean modelHaar = volume`.
    have hbyParts := chartTarget_integral_byParts (I := I) (M := M) α l
      (densityOnEuclid_mul_crossRightTestGradTerm_contDiffOn
        (I := I) (M := M) g r s S α P₀ l)
      hφ.contDiffOn hφ_cs hφ_supp
    rw [DifferentialGeometry.Integral.Measure.map_toEuclidean_modelHaar_eq_volume
      (E := E)] at hbyParts
    exact hbyParts
  -- Sum the per-direction identities and pull the finite sum out of the
  -- integral.
  rw [Finset.sum_congr rfl (fun l _ => hIBP l), Finset.sum_neg_distrib]
  congr 1
  -- The single `φ`-integral of the summed divergence equals the sum of the
  -- per-direction `φ`-integrals.
  have hsum_eq :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ l : Fin (Module.finrank ℝ E),
              euclidPartial (E := E) l
                (fun z => densityOnEuclid (I := I) g α z *
                  crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l z) y) *
            φ y ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ l : Fin (Module.finrank ℝ E),
              euclidPartial (E := E) l
                  (fun z => densityOnEuclid (I := I) g α z *
                    crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l z) y *
                φ y) ∂(volume : Measure EuclN) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y
    simp only [Finset.sum_mul]
  rw [hsum_eq, MeasureTheory.integral_finset_sum _ (fun l _ =>
    (integrable_euclidPartial_crossRightTestGradTerm_mul_test
      (I := I) (M := M) g r s S α P₀ l hφ hφ_cs hφ_supp).restrict)]

/-! ## The chart-Euclidean divergence as a finite Leibniz sum

On the open Euclidean chart target the chart density times the cross-right
gradient-term coefficient `c[Sₙ,l]` is a double finite sum of
`crossRightDivFactor` times the partition-of-unity chart-component atom. The
chart-Euclidean partial `euclidPartial l` therefore distributes — by the
chart-Euclidean sum rule and the Leibniz rule — into two summand groups: the
chart-Euclidean partial of `crossRightDivFactor` times the bare chart-component
atom (a component-atom summand), and `crossRightDivFactor` times the
chart-Euclidean partial of the bare chart-component atom (a chart-partial
summand). Summing over the chart directions `l` yields a finite sum over the
heterogeneously indexed triples `(l, P, Q)`. -/

/-- On the chart target, the `l`-th chart-Euclidean partial of the
density-weighted cross-right gradient-term coefficient at the smooth approximant
equals the double finite sum, over component multi-index pairs `(P, Q)`, of the
two Leibniz contributions: the chart-Euclidean partial of `crossRightDivFactor`
times the bare chart-component atom, plus `crossRightDivFactor` times the
chart-Euclidean partial of the bare chart-component atom. -/
private lemma euclidPartial_densityOnEuclid_mul_crossRightTestGradTerm_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (n : ℕ)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) l
        (fun z => densityOnEuclid (I := I) g α z *
          crossRightTestGradTerm (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_uniform i n).toCcTensor α P₀ l z) y =
      (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            euclidPartial (E := E) l
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              tensorChartComponent (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s h_uniform i n).toCcTensor α P.1 P.2 y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q y *
                euclidPartial (E := E) l
                  (tensorChartComponent (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_uniform i n).toCcTensor α P.1 P.2) y := by
  classical
  -- The chart target is open; on it the coefficient agrees with the double
  -- finite sum, so the chart-Euclidean partials agree at `y`.
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  set wₙ : SmoothCcTensor g r s :=
    (eigenvectorSmoothApprox (I := I) (M := M) g r s h_uniform i n).toCcTensor
    with hwₙ_def
  -- The double-sum representative on the chart target.
  set Sum2 : EuclN → ℝ := fun z =>
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q z *
          tensorChartComponent (I := I) (M := M) g r s wₙ α P.1 P.2 z
    with hSum2_def
  have hcoeff_evt :
      (fun z => densityOnEuclid (I := I) g α z *
        crossRightTestGradTerm (I := I) (M := M) g r s wₙ α P₀ l z)
        =ᶠ[𝓝 y] Sum2 := by
    have h_eq := densityOnEuclid_mul_crossRightTestGradTerm_eq
      (I := I) (M := M) g r s wₙ α P₀ l
    rw [hSum2_def]
    rw [h_eq]
  rw [euclidPartial_def, hcoeff_evt.fderiv_eq, ← euclidPartial_def]
  -- Differentiability of every `(P, Q)`-leaf at `y`.
  have hleaf_diff : ∀ P Q : TensorCompIdx (E := E) r s,
      DifferentiableAt ℝ
        (fun z => crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q z *
          tensorChartComponent (I := I) (M := M) g r s wₙ α P.1 P.2 z) y :=
    fun P Q =>
      (differentiableAt_of_contDiffOn_chartTarget (I := I) (M := M) α
        (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)
        hy).mul
      (differentiableAt_tensorChartComponent (I := I) (M := M) g r s wₙ α
        P.1 P.2 y)
  -- Distribute `euclidPartial l` across the two nested finite sums.
  rw [hSum2_def, euclidPartial_finsetSum (E := E) l Finset.univ
    (fun P _ => DifferentiableAt.fun_sum (fun Q _ => hleaf_diff P Q))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [euclidPartial_finsetSum (E := E) l Finset.univ
    (fun Q _ => hleaf_diff P Q)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  -- Leibniz on the `(P, Q)`-leaf.
  exact euclidPartial_mul (E := E) l
    (differentiableAt_of_contDiffOn_chartTarget (I := I) (M := M) α
      (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q) hy)
    (differentiableAt_tensorChartComponent (I := I) (M := M) g r s wₙ α
      P.1 P.2 y)

/-! ## Three-fold nested finite-sum `L²`-convergence

Iterating the single-level finite-sum `L²`-convergence step `tendsto_sumToLp`
over three nested finite types assembles the `L²`-limit of a three-fold nested
finite sum. The conclusion's `L²` classes are the correspondingly nested
`memLp_finset_sum` constructions. -/

/-- **Three-fold nested finite-sum `L²`-convergence.** Per-`(a, b, c)`-leaf
`L²`-convergence assembles into the `L²`-convergence of the three-fold nested
finite sum. -/
private lemma tendsto_sum3
    (α : M) {κ₁ κ₂ κ₃ : Type*}
    [Fintype κ₁] [Fintype κ₂] [Fintype κ₃]
    {f : κ₁ → κ₂ → κ₃ → ℕ → EuclN → ℝ}
    {flim : κ₁ → κ₂ → κ₃ → EuclN → ℝ}
    (hf : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (n : ℕ),
      MemLp (f a b c n) 2 (chartL2Measure (I := I) (M := M) α))
    (hflim : ∀ (a : κ₁) (b : κ₂) (c : κ₃),
      MemLp (flim a b c) 2 (chartL2Measure (I := I) (M := M) α))
    (h_tendsto : ∀ (a : κ₁) (b : κ₂) (c : κ₃),
      Filter.Tendsto (fun n => (hf a b c n).toLp (f a b c n)) atTop
        (𝓝 ((hflim a b c).toLp (flim a b c)))) :
    Filter.Tendsto
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun a _ => memLp_finset_sum Finset.univ
            (fun b _ => memLp_finset_sum Finset.univ
              (fun c _ => hf a b c n)))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, f a b c n y))
      atTop
      (𝓝 ((memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun a _ => memLp_finset_sum Finset.univ
            (fun b _ => memLp_finset_sum Finset.univ
              (fun c _ => hflim a b c)))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, flim a b c y))) :=
  tendsto_sumToLp (I := I) (M := M) α
    (f := fun a => fun n y => ∑ b, ∑ c, f a b c n y)
    (flim := fun a => fun y => ∑ b, ∑ c, flim a b c y)
    (fun a n => memLp_finset_sum Finset.univ
      (fun b _ => memLp_finset_sum Finset.univ (fun c _ => hf a b c n)))
    (fun a => memLp_finset_sum Finset.univ
      (fun b _ => memLp_finset_sum Finset.univ (fun c _ => hflim a b c)))
    (fun a => tendsto_sumToLp (I := I) (M := M) α
      (f := fun b => fun n y => ∑ c, f a b c n y)
      (flim := fun b => fun y => ∑ c, flim a b c y)
      (fun b n => memLp_finset_sum Finset.univ (fun c _ => hf a b c n))
      (fun b => memLp_finset_sum Finset.univ (fun c _ => hflim a b c))
      (fun b => tendsto_sumToLp (I := I) (M := M) α
        (hf := fun c n => hf a b c n) (hflim := fun c => hflim a b c)
        (h_tendsto a b)))

/-! ## The explicit `L²`-limit of the cross-right gradient-term divergence

The chart-Euclidean divergence `∑_l euclidPartial l (densityOnEuclid g α ·
c[Sₙ,l])` is, on the chart target, a finite sum over triples `(l, P, Q)` of two
summand groups: the chart-Euclidean partial of `crossRightDivFactor` times the
chart-component atom, and `crossRightDivFactor` times the chart-Euclidean
partial of the chart-component atom. Their `n → ∞` `L²`-limits are the committed
chart-component limit object `componentLpLimit` and the committed chart-partial
limit object `partialLpLimit`. The explicit limit is the corresponding finite
sum, each `C^∞` coefficient cut to the compact partition-of-unity kernel. -/

/-- **The explicit `n → ∞` `L²`-limit of the cross-right gradient-term
divergence.** A finite `C^∞`-coefficient-weighted sum, over chart directions and
component multi-index pairs, of the chart-component limit object
`componentLpLimit`: the chart-Euclidean partial of `crossRightDivFactor` against
the chart-component limit (from the component-atom group), plus
`crossRightDivFactor` against the chart-partial limit `partialLpLimit` (from the
chart-partial group). Each coefficient is cut to the compact partition-of-unity
kernel. -/
noncomputable def crossRightGradCoeffDivLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    (∑ l : Fin (Module.finrank ℝ E),
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q)) y *
              (componentLpLimit (I := I) (M := M) g r s h_uniform i α P :
                EuclN → ℝ) y)
      + ∑ l : Fin (Module.finrank ℝ E),
          ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
                (partialLpLimit (I := I) (M := M) g r s h_uniform i α P l :
                  EuclN → ℝ) y

/-! ## `L²`-membership of the cross-right gradient-term divergence

The chart-Euclidean divergence at the `n`-th smooth approximant is, on the chart
target, the finite Leibniz sum of `component`- and `partial`-atom summands; each
summand is `C^∞`-coefficient times an `L²` chart-component or chart-partial atom,
hence `L²`. The limit object `crossRightGradCoeffDivLimit` is, likewise, a finite
sum of indicator-cut `C^∞` coefficients times the `L²`-limit objects. -/

/-- The chart-Euclidean divergence `∑_l euclidPartial l (densityOnEuclid g α ·
c[Sₙ,l])` of the cross-right gradient-term coefficient at the `n`-th smooth
approximant is `L²`. -/
theorem crossRightGradCoeffDivSum_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    MemLp
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        euclidPartial (E := E) l
          (fun z => densityOnEuclid (I := I) g α z *
            crossRightTestGradTerm (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s h_uniform i n).toCcTensor α P₀ l z) y) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  -- The component-atom group: `∂_l crossRightDivFactor · chart component`.
  have hcomp : MemLp
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            euclidPartial (E := E) l
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              tensorChartComponent (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s h_uniform i n).toCcTensor α P.1 P.2 y) 2
      (chartL2Measure (I := I) (M := M) α) :=
    memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun P _ => memLp_finset_sum
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun Q _ => memLp_factor_mul_componentAtom (I := I) (M := M)
            g r s h_uniform i α P n
            (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
              g r s α P₀ l P Q))))
  -- The chart-partial-atom group: `crossRightDivFactor · ∂_l chart component`.
  have hpart : MemLp
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q y *
              euclidPartial (E := E) l
                (tensorChartComponent (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s h_uniform i n).toCcTensor α P.1 P.2) y) 2
      (chartL2Measure (I := I) (M := M) α) :=
    memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun P _ => memLp_finset_sum
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun Q _ => memLp_factor_mul_partialAtom (I := I) (M := M)
            g r s h_uniform i α P l n
            (crossRightDivFactor_contDiffOn (I := I) (M := M)
              g r s α P₀ l P Q))))
  refine (hcomp.add hpart).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartL2Measure]
  refine (ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  refine Filter.Eventually.of_forall (fun y hy => ?_)
  -- On the chart target the divergence is the summed Leibniz contributions.
  simp only [Pi.add_apply]
  rw [Finset.sum_congr rfl (fun l _ =>
    euclidPartial_densityOnEuclid_mul_crossRightTestGradTerm_eqOn
      (I := I) (M := M) g r s h_uniform i α P₀ l n hy),
    Finset.sum_add_distrib]

/-- The explicit `L²`-limit function of the cross-right gradient-term divergence
is `L²`. -/
theorem crossRightGradCoeffDivLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s h_uniform i α P₀) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold crossRightGradCoeffDivLimit
  refine MemLp.add ?_ ?_
  · exact memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun P _ => memLp_finset_sum
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun Q _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
            (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
              g r s α P₀ l P Q)
            (componentLpLimit (I := I) (M := M) g r s h_uniform i α P))))
  · exact memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l _ => memLp_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun P _ => memLp_finset_sum
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun Q _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
            (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)
            (partialLpLimit (I := I) (M := M) g r s h_uniform i α P l))))

/-! ## The `n → ∞` `L²`-limit of the cross-right gradient-term divergence

The chart-Euclidean divergence at the smooth approximant is, on the chart
target, the sum of a three-fold nested component-atom sum and a three-fold
nested chart-partial-atom sum. The chart-component atom and the chart-partial
atom converge, in `Lp ℝ 2 (chartL2Measure α)`, to the committed limit objects
`componentLpLimit` and `partialLpLimit`; the three-fold finite-sum convergence
`tendsto_sum3` assembles each group, and adding the two convergent groups gives
the headline `L²`-convergence to `crossRightGradCoeffDivLimit`. -/

/-- **The `n → ∞` `L²`-limit of the cross-right gradient-term divergence.** For a
closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index `i`, a
chart center `α : M`, and a base component multi-index `P₀`, the `L²` classes of
the chart-Euclidean divergence `∑_l euclidPartial l (densityOnEuclid g α ·
c[Sₙ,l])` of the cross-right gradient-term coefficient at the smooth
approximants `Sₙ := (eigenvectorSmoothApprox g r s h_uniform i n).toCcTensor`
converge, as `n → ∞` and in `Lp ℝ 2 (chartL2Measure α)`, to the `L²` class of
the explicit limit function `crossRightGradCoeffDivLimit g r s h_uniform i α P₀`.

This is the `n → ∞` `L²`-limit of the chart-Euclidean divergence produced by the
per-`n` integration-by-parts rewrite `crossRightTestGradTerm_byParts`; it folds
the `euclidPartial l φ`-carrying part of the chart-pulled, test-decoupled
cross-right term into a single `φ`-term at the limit. -/
theorem crossRightGradCoeffDivSum_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => (crossRightGradCoeffDivSum_memLp (I := I) (M := M)
        g r s h_uniform i α P₀ n).toLp _)
      atTop
      (𝓝 ((crossRightGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s h_uniform i α P₀).toLp _)) := by
  classical
  -- The component-atom group: `∂_l crossRightDivFactor · chart component`, with
  -- limit the kernel-cut `∂_l crossRightDivFactor` against `componentLpLimit`.
  have h_comp := tendsto_sum3 (I := I) (M := M) α
    (f := fun l P Q n y =>
      euclidPartial (E := E) l
          (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_uniform i n).toCcTensor α P.1 P.2 y)
    (flim := fun l P Q y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (euclidPartial (E := E) l
            (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q)) y *
        (componentLpLimit (I := I) (M := M) g r s h_uniform i α P :
          EuclN → ℝ) y)
    (fun l P Q n => memLp_factor_mul_componentAtom (I := I) (M := M)
      g r s h_uniform i α P n
      (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q))
    (fun l P Q => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q)
      (componentLpLimit (I := I) (M := M) g r s h_uniform i α P))
    (fun l P Q => tendsto_componentSummand (I := I) (M := M)
      g r s h_uniform i α P
      (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l P Q)
      (fun n => memLp_factor_mul_componentAtom (I := I) (M := M)
        g r s h_uniform i α P n
        (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l P Q))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l P Q)
        (componentLpLimit (I := I) (M := M) g r s h_uniform i α P)))
  -- The chart-partial-atom group: `crossRightDivFactor · ∂_l chart component`,
  -- with limit the kernel-cut `crossRightDivFactor` against `partialLpLimit`.
  have h_part := tendsto_sum3 (I := I) (M := M) α
    (f := fun l P Q n y =>
      crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q y *
        euclidPartial (E := E) l
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_uniform i n).toCcTensor α P.1 P.2) y)
    (flim := fun l P Q y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
        (partialLpLimit (I := I) (M := M) g r s h_uniform i α P l :
          EuclN → ℝ) y)
    (fun l P Q n => memLp_factor_mul_partialAtom (I := I) (M := M)
      g r s h_uniform i α P l n
      (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q))
    (fun l P Q => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)
      (partialLpLimit (I := I) (M := M) g r s h_uniform i α P l))
    (fun l P Q => tendsto_partialSummand (I := I) (M := M)
      g r s h_uniform i α P l
      (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)
      (fun n => memLp_factor_mul_partialAtom (I := I) (M := M)
        g r s h_uniform i α P l n
        (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q))
      (memLp_indicatorFactor_mul_lp (I := I) (M := M) α
        (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)
        (partialLpLimit (I := I) (M := M) g r s h_uniform i α P l)))
  -- Add the two convergent groups.
  have h_add := h_comp.add h_part
  -- Identify the `n`-th sum with the divergence `L²` class.
  have h_termN : ∀ n : ℕ,
      (crossRightGradCoeffDivSum_memLp (I := I) (M := M)
        g r s h_uniform i α P₀ n).toLp _ =
      (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun l _ => memLp_finset_sum Finset.univ
            (fun P _ => memLp_finset_sum Finset.univ
              (fun Q _ => memLp_factor_mul_componentAtom (I := I) (M := M)
                g r s h_uniform i α P n
                (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ l P Q))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun l _ => memLp_finset_sum Finset.univ
            (fun P _ => memLp_finset_sum Finset.univ
              (fun Q _ => memLp_factor_mul_partialAtom (I := I) (M := M)
                g r s h_uniform i α P l n
                (crossRightDivFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ l P Q))))).toLp _ := by
    intro n
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    rw [chartL2Measure]
    refine (ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    simp only []
    rw [Finset.sum_congr rfl (fun l _ =>
      euclidPartial_densityOnEuclid_mul_crossRightTestGradTerm_eqOn
        (I := I) (M := M) g r s h_uniform i α P₀ l n hy),
      Finset.sum_add_distrib]
  -- Identify the limiting sum with the divergence-limit `L²` class.
  have h_termLim :
      (crossRightGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s h_uniform i α P₀).toLp _ =
      (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun l _ => memLp_finset_sum Finset.univ
            (fun P _ => memLp_finset_sum Finset.univ
              (fun Q _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ l P Q)
                (componentLpLimit (I := I) (M := M)
                  g r s h_uniform i α P))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun l _ => memLp_finset_sum Finset.univ
            (fun P _ => memLp_finset_sum Finset.univ
              (fun Q _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
                (crossRightDivFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ l P Q)
                (partialLpLimit (I := I) (M := M)
                  g r s h_uniform i α P l))))).toLp _ := by
    refine toLp_add_eq (I := I) (M := M) α _ _ _ ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [crossRightGradCoeffDivLimit]
  rw [show (fun n => (crossRightGradCoeffDivSum_memLp
        (I := I) (M := M) g r s h_uniform i α P₀ n).toLp _) =
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun l _ => memLp_finset_sum Finset.univ
            (fun P _ => memLp_finset_sum Finset.univ
              (fun Q _ => memLp_factor_mul_componentAtom (I := I) (M := M)
                g r s h_uniform i α P n
                (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ l P Q))))).toLp _ +
        (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun l _ => memLp_finset_sum Finset.univ
            (fun P _ => memLp_finset_sum Finset.univ
              (fun Q _ => memLp_factor_mul_partialAtom (I := I) (M := M)
                g r s h_uniform i α P l n
                (crossRightDivFactor_contDiffOn (I := I) (M := M)
                  g r s α P₀ l P Q))))).toLp _)
      from funext h_termN, h_termLim]
  exact h_add

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_uniform : uniformTensorChartSobolevBound g r s)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) :
    EuclN → ℝ :=
  crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l

example (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    EuclN → ℝ :=
  crossRightGradCoeffDivLimit (I := I) (M := M) g r s h_uniform i α P₀

example (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    {φ : EuclN → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_cs : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∑ l : Fin (Module.finrank ℝ E),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
              crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l y *
            euclidPartial (E := E) l φ y ∂(volume : Measure EuclN) =
      -∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ l : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) l
              (fun z => densityOnEuclid (I := I) g α z *
                crossRightTestGradTerm (I := I) (M := M) g r s S α P₀ l z) y) *
          φ y ∂(volume : Measure EuclN) :=
  crossRightTestGradTerm_byParts (I := I) (M := M) g r s S α P₀ hφ hφ_cs hφ_supp

example (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => (crossRightGradCoeffDivSum_memLp (I := I) (M := M)
        g r s h_uniform i α P₀ n).toLp _)
      atTop
      (𝓝 ((crossRightGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s h_uniform i α P₀).toLp _)) :=
  crossRightGradCoeffDivSum_tendsto (I := I) (M := M) g r s h_uniform i α P₀

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
