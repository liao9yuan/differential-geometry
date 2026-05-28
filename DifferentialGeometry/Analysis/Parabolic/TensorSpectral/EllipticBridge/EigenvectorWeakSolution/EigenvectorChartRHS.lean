import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.SmoothApprox
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartComponentL2
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartWeightedMemLp
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartTestDecoupling
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossRightDiv
import DifferentialGeometry.Geometry.LocalChartConsistency

/-!
# The main-Dirichlet limit and the chart right-hand side of the eigenvector
# weak-solution assembly

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with nonzero resolvent eigenvalue `μ := i.fst.val`, the per-component
elliptic-regularity analysis realises the chart `P₀`-component of the abstract
connection-Laplacian eigenvector as a chart-local weak elliptic solution.

The variational-identity assembly applies the source-free per-approximant chart
bilinear identity to the partition-of-unity-weighted smooth approximants
`Tₙ := pouSmul g r s α wₙ`, with `wₙ := eigenvectorSmoothApprox g r s h_atlas i n`
the canonical smooth `H¹`-approximating sequence of the eigenvector resolvent.
Its Dirichlet term splits, by the covariant Leibniz rule, into the
genuine-gradient **main-Dirichlet** term

```
mainDir(n) := ∫ tensorCovDerivPointwiseInner g r s wₙ (scalarSmul ζ_α S)
```

(`ζ_α := chartAtlasPOU I M α`, `S` a fixed smooth `(r, s)`-tensor test section)
corrected by two cross terms. The cross terms' `n → ∞` limits are pre-proven in
the sibling cross-limit files; this file proves the `n → ∞` limit of the
main-Dirichlet term and packages the chart-Euclidean right-hand side of the
limiting variational identity.

## The main-Dirichlet limit

By the smooth-`H¹`-approximant Dirichlet-convergence theorem
`smoothApprox_dirichlet_tendsto`, the main-Dirichlet pairing of `wₙ` against the
*fixed* smooth section `S'` converges to

```
⟪eigenvectorResolvent …, smoothToTensorH1Compl S'⟫_{H¹}
  − ⟪TensorH1ComplToTensorL2 (eigenvectorResolvent …), S'.toCcTensor⟫_{L²}.
```

The eigenvector weak equation `eigenWeakEquation` rewrites the first `H¹` pairing
as the `L²` pairing `⟪S'.toCcTensor, φ⟫` of `S'` against the eigenvector `φ`; the
rescaling identity `eigenvector_eq_resolvent_smul` identifies
`TensorH1ComplToTensorL2 (eigenvectorResolvent …) = μ • φ`. Hence the
main-Dirichlet limit is the closed-form `(1 − μ) · ⟪S'.toCcTensor, φ⟫`.

## The chart right-hand side

`eigenvectorChartRHS g r s h_atlas i α P₀` is the chart-Euclidean right-hand
side of the limiting per-component variational identity: the explicit
`densityOnEuclid`-and-`C^∞`-coefficient-weighted finite combination of the
chart-component limit objects produced by the companion files of this campaign —

* the canonical eigenvector chart component `u_chart` (the chart `P₀`-component
  of the eigenvector `tensorResolventEigenbasisVec h_atlas i`);
* the cross-Leibniz limit objects `crossLeftLimitComponent`,
  `crossRightLimitComponent`;
* the three lower-order coefficient limits `covPrincipalRotationCoeffLimit`,
  `covLowerOrderRotationValueCoeffLimit`, `weightedGradCoeffDivLimit`.

Each limit object is, by its companion-file lemma, `MemLp 2` with respect to the
chart-pulled weighted measure restricted to `chartTargetEuclid α`; each multiplying
`C^∞` coefficient is bounded on the compact kernel where the limit object is
supported. The chart-Euclidean right-hand side is therefore again `MemLp 2` with
respect to the chart-pulled weighted measure
(`eigenvectorChartRHS_memLp_weighted`) — the `f_chart` membership of the
chart-bilinear divergence-form data structure.

## Main results

* `mainDir_tendsto` — the `n → ∞` limit of the main-Dirichlet term.
* `eigenvectorChartRHS` — the chart-Euclidean right-hand side of the limiting
  per-component variational identity.
* `eigenvectorChartRHS_memLp_weighted` — `eigenvectorChartRHS` is `MemLp 2` with
  respect to the chart-pulled weighted measure restricted to
  `chartTargetEuclid α`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## The `L²`-coercion of the eigenvector resolvent

The eigenbasis vector `φ := tensorResolventEigenbasisVec h_atlas i` satisfies,
by `eigenvector_eq_resolvent_smul`, the identity
`φ = μ⁻¹ • TensorH1ComplToTensorL2 (eigenvectorResolvent …)`; multiplying through
by the nonzero scalar `μ := i.fst.val` rearranges this to express the
`L²`-coercion of the eigenvector resolvent directly as `μ • φ`. -/

/-- **The `L²`-coercion of the eigenvector resolvent is `μ • φ`.** Multiplying the
rescaling identity `eigenvector_eq_resolvent_smul` through by the nonzero
eigenvalue `μ := i.fst.val` rearranges `φ = μ⁻¹ • TensorH1ComplToTensorL2
(eigenvectorResolvent …)` into `TensorH1ComplToTensorL2 (eigenvectorResolvent …)
= μ • φ`. -/
private lemma resolventL2_eq_mul_eigenvector
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i) =
      i.fst.val •
        tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i := by
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  rw [eigenvector_eq_resolvent_smul (I := I) (M := M) g r s h_atlas i,
    smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]

/-! ## The main-Dirichlet limit

The main-Dirichlet term `mainDir(n)` is the integrated covariant-gradient
(Dirichlet) pairing of the `n`-th canonical smooth approximant `wₙ` against a
*fixed* smooth compactly-supported `(r, s)`-tensor section `S'`. Its `n → ∞`
limit is extracted from the smooth-`H¹`-approximant Dirichlet-convergence theorem
`smoothApprox_dirichlet_tendsto`, then rewritten in closed form through the
eigenvector weak equation and the resolvent rescaling identity. -/

/-- **The `n → ∞` limit of the main-Dirichlet term.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with nonzero resolvent eigenvalue `μ := i.fst.val`, and a fixed smooth
compactly-supported `(r, s)`-tensor section `S'`, the main-Dirichlet pairings

```
∫_M ⟨∇(eigenvectorSmoothApprox g r s h_atlas i n).toCcTensor, ∇S'⟩ dμ_g
```

converge, as `n → ∞`, to the closed-form

```
(1 − μ) · ⟪(S' : TensorL2 r s g), tensorResolventEigenbasisVec h_atlas i⟫_{L²}.
```

The proof feeds the canonical-approximant Dirichlet-convergence theorem
`smoothApprox_dirichlet_tendsto` — whose limit is the difference of an `H¹` and an
`L²` pairing — through the eigenvector weak equation `eigenWeakEquation`
(rewriting the `H¹` pairing as the `L²` pairing against the eigenvector) and the
resolvent rescaling identity `resolventL2_eq_mul_eigenvector` (identifying the
`L²`-coercion of the resolvent with `μ • φ`).

This is the one `n → ∞` limit of the eigenvector weak-solution assembly that is
not packaged by the sibling cross-limit / lower-order-limit files; combined with
those, it furnishes the full limit of the source-free per-approximant chart
bilinear identity. -/
theorem mainDir_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (S' : SmoothCcTensor g r s) :
    Filter.Tendsto
      (fun n => ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
          S' x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      atTop
      (𝓝 ((1 - i.fst.val) *
        ⟪(S' : TensorL2 r s g),
          tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i⟫_ℝ)) := by
  classical
  -- View the fixed test section as a smooth compactly-supported `H¹` section.
  set Sh1 : SmoothCcTensorH1 g r s := ⟨S'⟩ with hSh1_def
  have hSh1_to : Sh1.toCcTensor = S' := rfl
  -- The canonical approximating sequence and its `H¹`-convergence.
  have hw_tendsto :
      Filter.Tendsto
        (fun n => smoothToTensorH1Compl (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n))
        atTop
        (𝓝 (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) :=
    eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s h_atlas i
  -- The Dirichlet-convergence theorem of the canonical approximating sequence.
  have h_dir :=
    smoothApprox_dirichlet_tendsto (I := I) (M := M) g r s h_atlas i Sh1
      hw_tendsto
  -- `⟪R, sToH1 Sh1⟫ = ⟪Sh1.toCcTensor, φ⟫` by the eigenvector weak equation.
  have h_weak :
      ⟪eigenvectorResolvent (I := I) (M := M) g r s h_atlas i,
          smoothToTensorH1Compl (I := I) (M := M) g r s Sh1⟫_ℝ =
        ⟪(Sh1.toCcTensor : TensorL2 r s g),
          tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i⟫_ℝ :=
    eigenWeakEquation (I := I) (M := M) g r s h_atlas i Sh1
  -- `TensorH1ComplToTensorL2 R = μ • φ`, so the `L²` part is
  -- `μ • ⟪φ, Sh1.toCcTensor⟫ = μ • ⟪Sh1.toCcTensor, φ⟫`.
  have h_l2part :
      ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i),
          (Sh1.toCcTensor : TensorL2 r s g)⟫_ℝ =
        i.fst.val *
          ⟪(Sh1.toCcTensor : TensorL2 r s g),
            tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i⟫_ℝ := by
    rw [resolventL2_eq_mul_eigenvector (I := I) (M := M) g r s h_atlas i,
      inner_smul_left, starRingEnd_apply, star_trivial, real_inner_comm]
  -- Assemble the closed-form limit.
  have h_limit_eq :
      ⟪eigenvectorResolvent (I := I) (M := M) g r s h_atlas i,
            smoothToTensorH1Compl (I := I) (M := M) g r s Sh1⟫_ℝ -
          ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i),
            (Sh1.toCcTensor : TensorL2 r s g)⟫_ℝ =
        (1 - i.fst.val) *
          ⟪(S' : TensorL2 r s g),
            tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i⟫_ℝ := by
    rw [h_weak, h_l2part, hSh1_to]; ring
  rw [h_limit_eq] at h_dir
  exact h_dir

/-! ## The chart-Euclidean right-hand side of the limiting variational identity

The source-free per-approximant chart bilinear identity, applied to the
partition-of-unity-weighted approximants `Tₙ := pouSmul g r s α wₙ`, has — after
the covariant-Leibniz Dirichlet split, the chart-pulls, the test-section
decouplings and the single integration by parts — a chart-Euclidean right-hand
side that is the explicit `densityOnEuclid`-and-`C^∞`-coefficient-weighted finite
combination of the six chart-component limit objects produced by the companion
files of this campaign.

`eigenvectorChartRHS` packages that finite combination, scaled overall by the
inverse `μ⁻¹` of the resolvent eigenvalue. Concretely the bracketed combination
collects:

* the canonical eigenvector chart component
  `tensorL2ChartComponent g r s (tensorResolventEigenbasisVec h_atlas i) α P₀`;
* the cross-Leibniz limit objects `crossLeftLimitComponent`,
  `crossRightLimitComponent`, each contracted by the chart-frame tensor-metric
  Gram and the test-decoupling coefficient;
* the two lower-order coefficient limits `covPrincipalRotationCoeffLimit`,
  `covLowerOrderRotationValueCoeffLimit`;
* the two divergence limits `weightedGradCoeffDivLimit` (the lower-order
  gradient divergence) and `crossRightGradCoeffDivLimit` (the cross-right
  gradient divergence), each divided by the chart density `densityOnEuclid g α`:
  each divergence limit enters the limiting variational identity as a bare
  `∫ (div) · ψ` term, and re-expressing it as `∫ densityOnEuclid · (div /
  densityOnEuclid) · ψ` puts it in the density-weighted shape of the
  variational-identity right-hand side. `densityOnEuclid g α` is `C^∞` and
  strictly positive on the open chart target, so `1 / densityOnEuclid g α` is
  `C^∞` there; the divergence limits are supported in the compact
  partition-of-unity kernel, where `1 / densityOnEuclid g α` is `C^∞` and
  bounded.

Each limit object is `MemLp 2` with respect to the chart-pulled weighted measure
restricted to `chartTargetEuclid α` (its companion-file `…_memLp_weighted`
lemma), and each multiplying coefficient is `C^∞` on the open chart target and
bounded on the compact kernel where the corresponding limit object is supported.
The chart-Euclidean right-hand side is therefore again `MemLp 2` with respect to
the chart-pulled weighted measure (`eigenvectorChartRHS_memLp_weighted`).

The chart-Euclidean right-hand side is **data** (a function `EuclN → ℝ`): it is
the `f_chart` field of the chart-bilinear divergence-form data structure
`TensorChartBilinearH1ComplData g r s α P₀`. -/

/-- **The chart-Euclidean right-hand side of the limiting per-component
variational identity.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with nonzero resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`,
and a component multi-index `P₀`, this is the explicit
`densityOnEuclid`-and-`C^∞`-coefficient-weighted finite combination of the
chart-component limit objects of the eigenvector weak-solution assembly,
collected into a bracketed seven-term combination scaled overall by `μ⁻¹`:

* the canonical eigenvector chart component
  `tensorL2ChartComponent g r s (tensorResolventEigenbasisVec h_atlas i) α P₀`;
* the cross-left limit object `crossLeftLimitComponent`, contracted by the
  rank-`(r, s + 1)` chart-frame tensor-metric Gram and the cross-left
  test-decoupling coefficient `crossLeftTestCoeff` (with the cross-left sign of
  the covariant Leibniz split);
* the cross-right limit object `crossRightLimitComponent`, contracted by the
  rank-`(r, s)` chart-frame tensor-metric Gram and the cross-right
  test-decoupling **value** coefficient `crossRightTestValueCoeff`;
* the two lower-order coefficient limits `covPrincipalRotationCoeffLimit`,
  `covLowerOrderRotationValueCoeffLimit`;
* the two divergence limits `weightedGradCoeffDivLimit` (lower-order gradient
  divergence) and `crossRightGradCoeffDivLimit` (cross-right gradient
  divergence), each divided by the chart density `densityOnEuclid g α`. Each
  enters the limiting variational identity as a bare `∫ (div) · ψ` term;
  dividing by the strictly-positive `C^∞` chart density re-expresses it in the
  density-weighted shape `∫ densityOnEuclid · (div / densityOnEuclid) · ψ`.

The overall `μ⁻¹` factor is the residue of the chart-component-rescaling: the
per-approximant chart-bilinear identity is taken at the canonical smooth
approximants `Tₙ := pouSmul g r s α (eigenvectorSmoothApprox g r s h_atlas i
n).toCcTensor`, whose chart `P₀`-component converges to `μ` times the eigenvector
chart component `u_chart`, so the limit of the principal Dirichlet integrand
carries a `μ` that, after the rearrangement isolating
`∫ ∑ weightedInvGramOnEuclid · weak_partial · ∂ψ + ∫ densityOnEuclid · u_chart ·
ψ = ∫ densityOnEuclid · f_chart · ψ`, becomes a global `μ⁻¹` on the right-hand
side.

It is the `f_chart` field of the chart-bilinear divergence-form data structure
`TensorChartBilinearH1ComplData g r s α P₀`. -/
def eigenvectorChartRHS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    (i.fst.val)⁻¹ *
      (-- The canonical eigenvector chart component.
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
        -- The cross-left limit contribution (with the cross-left sign).
        - (∑ P : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
                ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        -- The cross-right value-coefficient contribution.
        + (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              (covChartMetricGram (I := I) (M := M) g r s α P Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
                ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        -- The principal rotation coefficient limit (with the source sign).
        - covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y
        -- The lower-order rotation value coefficient limit (with the source sign).
        - covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y
        -- The lower-order gradient divergence limit, divided by the chart density.
        + (1 / densityOnEuclid (I := I) g α y) *
            (∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s h_atlas i α P₀ l y)
        -- The cross-right gradient divergence limit, divided by the chart density.
        - (1 / densityOnEuclid (I := I) g α y) *
            crossRightGradCoeffDivLimit (I := I) (M := M)
              g r s h_atlas i α P₀ y)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The chart-Euclidean right-hand side of the eigenvector weak-solution
assembly (chart-locality-free).** Chart-locality-free twin of
`eigenvectorChartRHS`, re-keyed onto the unconditional eigenvector chart
component and the unconditional cross- and lower-order limit objects. -/
noncomputable def eigenvectorChartRHS_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    (i.fst.val)⁻¹ *
      (-- The canonical eigenvector chart component.
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
        -- The cross-left limit contribution (with the cross-left sign).
        - (∑ P : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
                ((crossLeftLimitComponent_unconditional (I := I) (M := M)
                  g r s i α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        -- The cross-right value-coefficient contribution.
        + (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              (covChartMetricGram (I := I) (M := M) g r s α P Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
                ((crossRightLimitComponent_unconditional (I := I) (M := M)
                  g r s i α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        -- The principal rotation coefficient limit (with the source sign).
        - covPrincipalRotationCoeffLimit_unconditional (I := I) (M := M)
            g r s i α P₀ y
        -- The lower-order rotation value coefficient limit (with the source sign).
        - covLowerOrderRotationValueCoeffLimit_unconditional (I := I) (M := M)
            g r s i α P₀ y
        -- The lower-order gradient divergence limit, divided by the chart density.
        + (1 / densityOnEuclid (I := I) g α y) *
            (∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit_unconditional (I := I) (M := M)
                g r s i α P₀ l y)
        -- The cross-right gradient divergence limit, divided by the chart density.
        - (1 / densityOnEuclid (I := I) g α y) *
            crossRightGradCoeffDivLimit_unconditional (I := I) (M := M)
              g r s i α P₀ y)

/-! ## Auxiliary facts about the chart density and the divergence limits

The two divergence limits enter `eigenvectorChartRHS` divided by the chart
density `densityOnEuclid g α`. The reciprocal `1 / densityOnEuclid g α` is `C^∞`
on the open chart target (the chart density is `C^∞` and strictly positive
there), and the `crossRightGradCoeffDivLimit` divergence limit — being an
explicit finite sum each of whose summands carries an `indicator (chartPouKernel
α)` factor — vanishes pointwise off the compact partition-of-unity kernel
`chartPouKernel α`, hence is `MemLp 2` with respect to the chart-pulled weighted
measure. -/

/-- The reciprocal `1 / densityOnEuclid g α` of the chart density is `C^∞` on the
open Euclidean chart target: the chart density is `C^∞`
(`densityOnEuclid_contDiffOn`) and strictly positive (`densityOnEuclid_pos`)
there, so the quotient `1 / densityOnEuclid g α` is `C^∞`. -/
private lemma one_div_densityOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞ (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')

/-- The cross-right gradient-divergence limit `crossRightGradCoeffDivLimit`
vanishes pointwise off the compact partition-of-unity kernel `chartPouKernel α`:
every summand of its explicit finite-sum definition carries an
`indicator (chartPouKernel α)` factor. -/
lemma crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s h_atlas i α P₀ y = 0 := by
  classical
  -- `crossRightGradCoeffDivLimit` is a sum of two triple finite sums; each
  -- summand carries an `indicator (chartPouKernel α)` factor that vanishes at
  -- `y ∉ chartPouKernel α`. Both finite sums are therefore zero.
  rw [crossRightGradCoeffDivLimit,
    Finset.sum_eq_zero (fun l _ => Finset.sum_eq_zero (fun P _ =>
      Finset.sum_eq_zero (fun Q _ => by
        rw [Set.indicator_of_notMem hy, zero_mul]))),
    Finset.sum_eq_zero (fun l _ => Finset.sum_eq_zero (fun P _ =>
      Finset.sum_eq_zero (fun Q _ => by
        rw [Set.indicator_of_notMem hy, zero_mul]))),
    add_zero]

/-- The cross-right gradient-divergence limit vanishes pointwise off the compact
partition-of-unity kernel `chartPouKernel α` (chart-locality-free). Every summand
of its explicit finite-sum definition carries an `indicator (chartPouKernel α)`
factor. -/
lemma crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    crossRightGradCoeffDivLimit_unconditional (I := I) (M := M)
        g r s i α P₀ y = 0 := by
  classical
  rw [crossRightGradCoeffDivLimit_unconditional,
    Finset.sum_eq_zero (fun l _ => Finset.sum_eq_zero (fun P _ =>
      Finset.sum_eq_zero (fun Q _ => by
        rw [Set.indicator_of_notMem hy, zero_mul]))),
    Finset.sum_eq_zero (fun l _ => Finset.sum_eq_zero (fun P _ =>
      Finset.sum_eq_zero (fun Q _ => by
        rw [Set.indicator_of_notMem hy, zero_mul]))),
    add_zero]

/-- **Weighted-`L²` membership of the cross-right gradient-divergence limit.**
`crossRightGradCoeffDivLimit g r s h_atlas i α P₀` is `MemLp 2` with respect to
the chart-pulled weighted measure restricted to `chartTargetEuclid α`.

The limit is `MemLp 2 (chartL2Measure α) = MemLp 2 (volume.restrict (chartTarget
α))` by `crossRightGradCoeffDivLimit_memLp`; it vanishes pointwise — hence a.e. —
off the compact partition-of-unity kernel; the weighted-measure upgrade lemma
`memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact`
delivers weighted `MemLp`. -/
private lemma crossRightGradCoeffDivLimit_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s h_atlas i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : MemLp (crossRightGradCoeffDivLimit (I := I) (M := M)
      g r s h_atlas i α P₀) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    crossRightGradCoeffDivLimit_memLp (I := I) (M := M) g r s h_atlas i α P₀
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (Filter.Eventually.of_forall (fun y hy =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_atlas i α P₀ hy))
    h_plain

/-- **Weighted-`L²` membership of the cross-right gradient-divergence limit
(chart-locality-free).** Chart-locality-free twin of
`crossRightGradCoeffDivLimit_memLp_weighted`. The limit is
`MemLp 2 (chartL2Measure α)` by `crossRightGradCoeffDivLimit_memLp_unconditional`,
vanishes pointwise — hence a.e. — off the compact partition-of-unity kernel, and
the weighted-measure upgrade lemma delivers weighted `MemLp`. -/
private lemma crossRightGradCoeffDivLimit_memLp_weighted_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (crossRightGradCoeffDivLimit_unconditional (I := I) (M := M)
        g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : MemLp (crossRightGradCoeffDivLimit_unconditional (I := I) (M := M)
      g r s i α P₀) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    crossRightGradCoeffDivLimit_memLp_unconditional (I := I) (M := M)
      g r s i α P₀
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (Filter.Eventually.of_forall (fun y hy =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel_unconditional
        (I := I) (M := M) g r s i α P₀ hy))
    h_plain

/-! ## Weighted-`L²` membership of the chart-Euclidean right-hand side

`eigenvectorChartRHS` is a finite sum of products of a `C^∞` coefficient (smooth
on the open chart target, bounded on the relevant compact chart kernel) with a
chart-component limit object that is `MemLp 2` with respect to the chart-pulled
weighted measure restricted to `chartTargetEuclid α`. The product helper
`memLp_weighted_contDiffOn_mul` and finite-sum closure of `MemLp` deliver the
weighted-`L²` membership. -/

/-- **Weighted-`L²` membership of the chart-Euclidean right-hand side.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `P₀`, the chart-Euclidean
right-hand side `eigenvectorChartRHS g r s h_atlas i α P₀` is `MemLp 2` with
respect to the chart-pulled weighted measure
`(chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)`.

`eigenvectorChartRHS` is a finite sum of products of a `C^∞`-on-the-chart-target
coefficient (bounded on the relevant compact chart kernel) and a chart-component
limit object that is, by its companion-file `…_memLp_weighted` lemma, `MemLp 2`
with respect to the chart-pulled weighted measure restricted to
`chartTargetEuclid α`, and a.e. supported in the relevant compact kernel. The
product helper `memLp_weighted_contDiffOn_mul` and finite-sum closure of `MemLp`
deliver the membership. This is the `f_chart` weighted-`L²` field of the
chart-bilinear divergence-form data structure
`TensorChartBilinearH1ComplData g r s α P₀`. -/
theorem eigenvectorChartRHS_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- (1) The canonical eigenvector chart component: weighted-`MemLp` directly by
  -- the companion-file lemma `tensorL2ChartComponent_memLp_weighted`.
  have h_uchart : MemLp
      (fun y =>
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2 μw := by
    rw [hμw_def]
    exact tensorL2ChartComponent_memLp_weighted (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀
  -- (2) The cross-left limit contribution: a finite double sum. The `C^∞`
  -- coefficient is `covChartMetricGram · crossLeftTestCoeff`; the cross-left
  -- limit is a.e. supported in the compact cutoff kernel.
  have h_crossLeft : ∀ (P Q : TensorCompIdx (E := E) r (s + 1)),
      MemLp
        (fun y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
            crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2 μw := by
    intro P Q
    rw [hμw_def]
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
        (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) α P
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossLeftLimitComponent_memLp_weighted (I := I) (M := M)
        g r s h_atlas i α P)
      h_aezero
  -- (3) The cross-right value-coefficient contribution: a finite double sum.
  have h_crossRight : ∀ (P Q : TensorCompIdx (E := E) r s),
      MemLp
        (fun y => (covChartMetricGram (I := I) (M := M) g r s α P Q y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2 μw := by
    intro P Q
    rw [hμw_def]
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
        (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) α P
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossRightLimitComponent_memLp_weighted (I := I) (M := M)
        g r s h_atlas i α P)
      h_aezero
  -- (4) The principal rotation coefficient limit.
  have h_prc : MemLp (covPrincipalRotationCoeffLimit (I := I) (M := M)
      g r s h_atlas i α P₀) 2 μw := by
    rw [hμw_def]
    exact covPrincipalRotationCoeffLimit_memLp_weighted (I := I) (M := M)
      g r s h_atlas i α P₀
  -- (5) The lower-order rotation value coefficient limit.
  have h_lov : MemLp (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
      g r s h_atlas i α P₀) 2 μw := by
    rw [hμw_def]
    exact covLowerOrderRotationValueCoeffLimit_memLp_weighted (I := I) (M := M)
      g r s h_atlas i α P₀
  -- (6) The chart-density-weighted lower-order gradient divergence limit,
  -- divided by the chart density. The reciprocal `1 / densityOnEuclid g α` is
  -- the `C^∞` coefficient; the finite sum over chart directions of
  -- `weightedGradCoeffDivLimit` is a.e. supported in the partition-of-unity
  -- kernel (each summand vanishes off it).
  have h_gradDiv : MemLp
      (fun y => (1 / densityOnEuclid (I := I) g α y) *
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s h_atlas i α P₀ l y)) 2 μw := by
    rw [hμw_def]
    have h_div_sum : MemLp
        (fun y => ∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s h_atlas i α P₀ l y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      memLp_finset_sum (μ := (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l _ => weightedGradCoeffDivLimit_memLp_weighted (I := I) (M := M)
          g r s h_atlas i α P₀ l)
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ chartPouKernel (I := I) (M := M) α →
            (∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s h_atlas i α P₀ l y) = 0 :=
      Filter.Eventually.of_forall (fun y hy =>
        Finset.sum_eq_zero (fun l _ =>
          weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel
            (I := I) (M := M) g r s h_atlas i α P₀ l hy))
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_measurableSet (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      h_div_sum h_aezero
  -- (7) The cross-right gradient divergence limit, divided by the chart density.
  -- The reciprocal `1 / densityOnEuclid g α` is the `C^∞` coefficient; the
  -- divergence limit `crossRightGradCoeffDivLimit` is a.e. supported in the
  -- partition-of-unity kernel.
  have h_crossRightDiv : MemLp
      (fun y => (1 / densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s h_atlas i α P₀ y) 2 μw := by
    rw [hμw_def]
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ chartPouKernel (I := I) (M := M) α →
            crossRightGradCoeffDivLimit (I := I) (M := M)
              g r s h_atlas i α P₀ y = 0 :=
      Filter.Eventually.of_forall (fun y hy =>
        crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s h_atlas i α P₀ hy)
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_measurableSet (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossRightGradCoeffDivLimit_memLp_weighted (I := I) (M := M)
        g r s h_atlas i α P₀)
      h_aezero
  -- The cross-left and cross-right finite double sums.
  have h_crossLeft_sum : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      2 μw :=
    memLp_finset_sum (μ := μw)
      (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
      (fun P _ => memLp_finset_sum (μ := μw)
        (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
        (fun Q _ => h_crossLeft P Q))
  have h_crossRight_sum : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      2 μw :=
    memLp_finset_sum (μ := μw)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum (μ := μw)
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => h_crossRight P Q))
  -- Assemble: the bracket `(1) − (2) + (3) − (4) − (5) + (6) − (7)` is weighted
  -- `MemLp`; the global `μ⁻¹` factor preserves weighted `MemLp`.
  have h_total :
      MemLp (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀) 2
        μw := by
    have h_bracket :=
      ((((((h_uchart.sub h_crossLeft_sum).add h_crossRight_sum).sub h_prc).sub
        h_lov).add h_gradDiv).sub h_crossRightDiv)
    have h_assembled := h_bracket.const_mul (i.fst.val)⁻¹
    refine h_assembled.ae_eq ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only [eigenvectorChartRHS, Pi.add_apply, Pi.sub_apply]
  rw [hμw_def] at h_total
  exact h_total

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **Weighted-`L²` membership of the chart-Euclidean right-hand side
(chart-locality-free).** Chart-locality-free twin of
`eigenvectorChartRHS_memLp_weighted`: the chart-Euclidean right-hand side
`eigenvectorChartRHS_unconditional g r s i α P₀` is `MemLp 2` with respect to the
chart-pulled weighted measure `(chartPulledWeightedMeasure g α).restrict
(chartTargetEuclid α)`.

Re-keyed onto the unconditional eigenvector chart component, the unconditional
cross- and lower-order limit objects, and their chart-locality-free
`…_memLp_weighted_unconditional` lemmas. The product helper
`memLp_weighted_contDiffOn_mul` and finite-sum closure of `MemLp` deliver the
membership exactly as in the `h_atlas`-carrying original. -/
theorem eigenvectorChartRHS_memLp_weighted_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (eigenvectorChartRHS_unconditional (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- (1) The canonical eigenvector chart component: weighted-`MemLp` directly by
  -- `tensorL2ChartComponent_memLp_weighted`.
  have h_uchart : MemLp
      (fun y =>
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2 μw := by
    rw [hμw_def]
    exact tensorL2ChartComponent_memLp_weighted (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i) α P₀
  -- (2) The cross-left limit contribution: a finite double sum.
  have h_crossLeft : ∀ (P Q : TensorCompIdx (E := E) r (s + 1)),
      MemLp
        (fun y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
            crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossLeftLimitComponent_unconditional (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2 μw := by
    intro P Q
    rw [hμw_def]
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossLeftLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent_unconditional]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
        (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i)) α P
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossLeftLimitComponent_memLp_weighted_unconditional (I := I) (M := M)
        g r s i α P)
      h_aezero
  -- (3) The cross-right value-coefficient contribution: a finite double sum.
  have h_crossRight : ∀ (P Q : TensorCompIdx (E := E) r s),
      MemLp
        (fun y => (covChartMetricGram (I := I) (M := M) g r s α P Q y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossRightLimitComponent_unconditional (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2 μw := by
    intro P Q
    rw [hμw_def]
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossRightLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent_unconditional]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
        (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i)) α P
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossRightLimitComponent_memLp_weighted_unconditional (I := I) (M := M)
        g r s i α P)
      h_aezero
  -- (4) The principal rotation coefficient limit.
  have h_prc : MemLp (covPrincipalRotationCoeffLimit_unconditional (I := I) (M := M)
      g r s i α P₀) 2 μw := by
    rw [hμw_def]
    exact covPrincipalRotationCoeffLimit_memLp_weighted_unconditional
      (I := I) (M := M) g r s i α P₀
  -- (5) The lower-order rotation value coefficient limit.
  have h_lov : MemLp (covLowerOrderRotationValueCoeffLimit_unconditional
      (I := I) (M := M) g r s i α P₀) 2 μw := by
    rw [hμw_def]
    exact covLowerOrderRotationValueCoeffLimit_memLp_weighted_unconditional
      (I := I) (M := M) g r s i α P₀
  -- (6) The chart-density-weighted lower-order gradient divergence limit,
  -- divided by the chart density.
  have h_gradDiv : MemLp
      (fun y => (1 / densityOnEuclid (I := I) g α y) *
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit_unconditional (I := I) (M := M)
            g r s i α P₀ l y)) 2 μw := by
    rw [hμw_def]
    have h_div_sum : MemLp
        (fun y => ∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit_unconditional (I := I) (M := M)
            g r s i α P₀ l y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      memLp_finset_sum (μ := (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l _ => weightedGradCoeffDivLimit_memLp_weighted_unconditional
          (I := I) (M := M) g r s i α P₀ l)
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ chartPouKernel (I := I) (M := M) α →
            (∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit_unconditional (I := I) (M := M)
                g r s i α P₀ l y) = 0 :=
      Filter.Eventually.of_forall (fun y hy =>
        Finset.sum_eq_zero (fun l _ =>
          weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel_unconditional
            (I := I) (M := M) g r s i α P₀ l hy))
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_measurableSet (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      h_div_sum h_aezero
  -- (7) The cross-right gradient divergence limit, divided by the chart density.
  have h_crossRightDiv : MemLp
      (fun y => (1 / densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit_unconditional (I := I) (M := M)
          g r s i α P₀ y) 2 μw := by
    rw [hμw_def]
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ chartPouKernel (I := I) (M := M) α →
            crossRightGradCoeffDivLimit_unconditional (I := I) (M := M)
              g r s i α P₀ y = 0 :=
      Filter.Eventually.of_forall (fun y hy =>
        crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel_unconditional
          (I := I) (M := M) g r s i α P₀ hy)
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_measurableSet (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossRightGradCoeffDivLimit_memLp_weighted_unconditional (I := I) (M := M)
        g r s i α P₀)
      h_aezero
  -- The cross-left and cross-right finite double sums.
  have h_crossLeft_sum : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossLeftLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      2 μw :=
    memLp_finset_sum (μ := μw)
      (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
      (fun P _ => memLp_finset_sum (μ := μw)
        (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
        (fun Q _ => h_crossLeft P Q))
  have h_crossRight_sum : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossRightLimitComponent_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      2 μw :=
    memLp_finset_sum (μ := μw)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum (μ := μw)
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => h_crossRight P Q))
  -- Assemble: the bracket `(1) − (2) + (3) − (4) − (5) + (6) − (7)` is weighted
  -- `MemLp`; the global `μ⁻¹` factor preserves weighted `MemLp`.
  have h_total :
      MemLp (eigenvectorChartRHS_unconditional (I := I) (M := M) g r s i α P₀) 2
        μw := by
    have h_bracket :=
      ((((((h_uchart.sub h_crossLeft_sum).add h_crossRight_sum).sub h_prc).sub
        h_lov).add h_gradDiv).sub h_crossRightDiv)
    have h_assembled := h_bracket.const_mul (i.fst.val)⁻¹
    refine h_assembled.ae_eq ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only [eigenvectorChartRHS_unconditional, Pi.add_apply, Pi.sub_apply]
  rw [hμw_def] at h_total
  exact h_total

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (S' : SmoothCcTensor g r s) :
    Filter.Tendsto
      (fun n => ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
          S' x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      atTop
      (𝓝 ((1 - i.fst.val) *
        ⟪(S' : TensorL2 r s g),
          tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i⟫_ℝ)) :=
  mainDir_tendsto (I := I) (M := M) g r s h_atlas i S'

example (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀

example (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  eigenvectorChartRHS_memLp_weighted (I := I) (M := M) g r s h_atlas i α P₀

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
