import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartLowerOrderLimits

/-!
# The `n → ∞` `L²`-limit of the covariant-gradient Christoffel correction term

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with nonzero resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`,
a component multi-index `P₀`, and a chart-coordinate direction `k`, the raw
chart-component formula for the section-level covariant gradient carries, on its
right-hand side, the zeroth-order Christoffel correction term
`covDerivLowerOrderTerm g r s Tₙ α k P₀.1 P₀.2`, evaluated at the
partition-of-unity-weighted smooth approximant
`Tₙ := pouSmul g r s α (eigenvectorSmoothApprox g r s h_uniform i n).toCcTensor`.

This file produces the `n → ∞` `L²`-limit of that term in
`Lp ℝ 2 (chartL2Measure α)`.

## The tracing identity

The Christoffel correction `covDerivLowerOrderTerm` is, by
`covDerivLowerOrderTerm_def`, a finite linear combination — over component
multi-index pairs `p` — of the `C^∞` lower-order correction coefficient
`covDerivLowerOrderCoeff` times the *undifferentiated raw* chart component of
the section. For the partition-of-unity-weighted approximant `Tₙ`, the raw
chart component is the partition-of-unity-weighted chart component
(`tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou`), whose value at
the chart preimage is, on the chart target, the canonical Euclidean chart
component `tensorChartComponent g r s wₙ.toCcTensor α p`. Consequently the
Christoffel correction at `Tₙ`, restricted to the chart target, is a finite
`C^∞`-coefficient-weighted sum of the single `T`-dependent atom

* `tensorChartComponent g r s wₙ.toCcTensor α p` (the bare chart component).

The `L²`-limit of that atom is `componentLpLimit` (companion file
`EigenvectorChartChartComponentL2.lean`), which is `μ` times the canonical chart
component `tensorL2ChartComponent g r s φ α p` of the eigenvector
`φ := tensorResolventEigenbasisVec h_uniform i`. The `μ⁻¹`-rescaling of the
`n`-th term — matching the rescaling convention of every companion eigenvector
chart-component limit object — therefore converges to the finite
`C^∞`-coefficient-weighted sum of the genuine eigenvector chart components.

## Main definitions

* `covGradChristoffelLimit g r s h_uniform i α P₀ k` — the explicit `L²`-limit
  function of the `μ⁻¹`-rescaled Christoffel correction term: a finite
  `C^∞`-coefficient-weighted sum, over component multi-index pairs, of the
  canonical eigenvector chart-component limit object `tensorL2ChartComponent`,
  with each coefficient cut to the partition-of-unity kernel.

## Main results

* `covGradChristoffelLimit_memLp` — the limit function is `L²`.
* `covGradChristoffel_tendsto` — the `n → ∞` `L²`-convergence headline.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

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

/-! ## The Christoffel-correction tracing identity for the weighted approximant

The zeroth-order Christoffel correction `covDerivLowerOrderTerm` of the
partition-of-unity-weighted approximant `Tₙ := pouSmul g r s α S` collapses, on
the chart target, to a finite `C^∞`-coefficient-weighted sum of the canonical
Euclidean chart components: the raw chart component of `Tₙ` is the
partition-of-unity-weighted chart component, whose value at the chart preimage
is the canonical Euclidean chart component. -/

/-- On the Euclidean chart target, the zeroth-order Christoffel correction of
the partition-of-unity-weighted approximant is the finite linear combination,
over component multi-index pairs, of the lower-order correction coefficient
times the canonical Euclidean chart component. -/
private lemma covDerivLowerOrderTerm_pouSmul_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α m Idx Jdx y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
          tensorChartComponent (I := I) (M := M) g r s S α p.1 p.2 y := by
  classical
  rw [covDerivLowerOrderTerm_def]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou
    (I := I) (M := M) g r s α S p.1 p.2,
    tensorChartComponent_def,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentPou (I := I) (M := M) g r s S α p.1 p.2) hy]

/-! ## `L²`-membership of the weighted-approximant Christoffel correction

The Christoffel correction at the partition-of-unity-weighted approximant is, by
the tracing identity, a finite sum of `C^∞`-coefficient × chart-component
products; each summand is `L²` (`memLp_factor_mul_componentAtom`), and a finite
sum of `L²` functions is `L²`. -/

/-- The zeroth-order Christoffel correction at the partition-of-unity-weighted
approximant is `L²` with respect to the chart `L²` measure. -/
theorem covDerivLowerOrderTerm_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    MemLp
      (covDerivLowerOrderTerm (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_uniform i n).toCcTensor) α k P₀.1 P₀.2) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  refine (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun p _ =>
      memLp_factor_mul_componentAtom (I := I) (M := M) g r s h_uniform i α p n
        (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
          g r s α k P₀.1 p.1 P₀.2 p.2))).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartL2Measure]
  refine (ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    covDerivLowerOrderTerm_pouSmul_eqOn (I := I) (M := M) g r s α
      (eigenvectorSmoothApprox (I := I) (M := M)
        g r s h_uniform i n).toCcTensor k P₀.1 P₀.2 hy)

/-! ## The explicit `L²`-limit function

The `n`-th term of the headline carries a `μ⁻¹`-rescaling, matching the
rescaling convention of every companion eigenvector chart-component limit. The
`L²` limit of the chart-component atom is `componentLpLimit = μ •
tensorL2ChartComponent φ`, so the rescaled limit is the finite
`C^∞`-coefficient-weighted sum of the genuine eigenvector chart components. -/

/-- **The explicit `L²`-limit function of the covariant-gradient Christoffel
correction term.** A finite `C^∞`-coefficient-weighted sum, over component
multi-index pairs, of the canonical eigenvector chart-component limit object
`tensorL2ChartComponent g r s (tensorResolventEigenbasisVec h_uniform i) α p`,
with each correction coefficient `covDerivLowerOrderCoeff` cut to the
partition-of-unity kernel of the chart. -/
noncomputable def covGradChristoffelLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    ∑ p : TensorCompIdx (E := E) r s,
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (covDerivLowerOrderCoeff (I := I) (M := M)
            g r s α k P₀.1 p.1 P₀.2 p.2) y *
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i) α p :
          EuclN → ℝ) y

/-- **The `L²`-limit function of the covariant-gradient Christoffel correction
term is `L²`.** A finite sum of `C^∞`-coefficient-indicator × `L²`-limit-class
products. -/
theorem covGradChristoffelLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemLp (covGradChristoffelLimit (I := I) (M := M)
        g r s h_uniform i α P₀ k) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold covGradChristoffelLimit
  exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s α k P₀.1 p.1 P₀.2 p.2)
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i) α p))

/-! ## The un-rescaled `L²`-limit and its rescaling

The Christoffel correction at `Tₙ` is a finite sum of `C^∞`-coefficient ×
chart-component summands; `tendsto_componentSummand` gives per-summand
`L²`-convergence and `tendsto_toLp_finsetSum` assembles the finite sum. The
resulting un-rescaled limit carries `componentLpLimit`; rescaling by the
continuous map `μ⁻¹ • ·` and identifying `μ⁻¹ • componentLpLimit` with
`tensorL2ChartComponent φ` yields the headline. -/

/-- The un-rescaled `L²`-limit of the Christoffel correction term: the finite
sum over component multi-index pairs of the kernel-indicator correction
coefficient times the chart-component limit object `componentLpLimit`. -/
private noncomputable def covGradChristoffelUnscaledLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    ∑ p : TensorCompIdx (E := E) r s,
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (covDerivLowerOrderCoeff (I := I) (M := M)
            g r s α k P₀.1 p.1 P₀.2 p.2) y *
        (componentLpLimit (I := I) (M := M) g r s h_uniform i α p :
          EuclN → ℝ) y

/-- The un-rescaled `L²`-limit function of the Christoffel correction term is
`L²`. -/
private theorem covGradChristoffelUnscaledLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemLp (covGradChristoffelUnscaledLimit (I := I) (M := M)
        g r s h_uniform i α P₀ k) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold covGradChristoffelUnscaledLimit
  exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s α k P₀.1 p.1 P₀.2 p.2)
      (componentLpLimit (I := I) (M := M) g r s h_uniform i α p))

/-- The Christoffel correction at the partition-of-unity-weighted approximants
converges, in `Lp ℝ 2 (chartL2Measure α)`, to the un-rescaled limit. -/
private theorem covDerivLowerOrderTerm_pouSmul_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (covDerivLowerOrderTerm_pouSmul_memLp (I := I) (M := M)
        g r s h_uniform i α P₀ k n).toLp _)
      atTop
      (𝓝 ((covGradChristoffelUnscaledLimit_memLp (I := I) (M := M)
        g r s h_uniform i α P₀ k).toLp _)) := by
  classical
  -- The genuine `n`-th summand and the limiting summand, indexed by `p`.
  have hf : ∀ (p : TensorCompIdx (E := E) r s) (n : ℕ),
      MemLp (fun y => covDerivLowerOrderCoeff (I := I) (M := M)
            g r s α k P₀.1 p.1 P₀.2 p.2 y *
          tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_uniform i n).toCcTensor α p.1 p.2 y) 2
        (chartL2Measure (I := I) (M := M) α) := fun p n =>
    memLp_factor_mul_componentAtom (I := I) (M := M) g r s h_uniform i α p n
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s α k P₀.1 p.1 P₀.2 p.2)
  have hflim : ∀ p : TensorCompIdx (E := E) r s,
      MemLp (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
            (covDerivLowerOrderCoeff (I := I) (M := M)
              g r s α k P₀.1 p.1 P₀.2 p.2) y *
          (componentLpLimit (I := I) (M := M) g r s h_uniform i α p :
            EuclN → ℝ) y) 2
        (chartL2Measure (I := I) (M := M) α) := fun p =>
    memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s α k P₀.1 p.1 P₀.2 p.2)
      (componentLpLimit (I := I) (M := M) g r s h_uniform i α p)
  -- Per-summand `L²`-convergence: a chart-component summand.
  have h_tendsto : ∀ p : TensorCompIdx (E := E) r s,
      Filter.Tendsto (fun n => (hf p n).toLp _) atTop
        (𝓝 ((hflim p).toLp _)) := fun p =>
    tendsto_componentSummand (I := I) (M := M) g r s h_uniform i α p
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s α k P₀.1 p.1 P₀.2 p.2)
      (fun n => hf p n) (hflim p)
  -- The Christoffel correction is, on the chart target, the finite sum of the
  -- genuine summands.
  have hFn_eq : ∀ n : ℕ,
      covDerivLowerOrderTerm (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_uniform i n).toCcTensor) α k P₀.1 P₀.2
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ p : TensorCompIdx (E := E) r s,
          covDerivLowerOrderCoeff (I := I) (M := M)
              g r s α k P₀.1 p.1 P₀.2 p.2 y *
            tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s h_uniform i n).toCcTensor α p.1 p.2 y := by
    intro n
    rw [chartL2Measure]
    refine (ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    exact Filter.Eventually.of_forall (fun y hy =>
      covDerivLowerOrderTerm_pouSmul_eqOn (I := I) (M := M) g r s α
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s h_uniform i n).toCcTensor k P₀.1 P₀.2 hy)
  -- The un-rescaled limit function is, definitionally, the finite sum of the
  -- limiting summands.
  have hFlim_eq :
      covGradChristoffelUnscaledLimit (I := I) (M := M)
          g r s h_uniform i α P₀ k
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ p : TensorCompIdx (E := E) r s,
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (covDerivLowerOrderCoeff (I := I) (M := M)
                g r s α k P₀.1 p.1 P₀.2 p.2) y *
            (componentLpLimit (I := I) (M := M) g r s h_uniform i α p :
              EuclN → ℝ) y :=
    Filter.EventuallyEq.rfl
  exact tendsto_toLp_finsetSum (I := I) (M := M) α Finset.univ
    hf hflim h_tendsto
    (fun n => covDerivLowerOrderTerm_pouSmul_memLp (I := I) (M := M)
      g r s h_uniform i α P₀ k n)
    (covGradChristoffelUnscaledLimit_memLp (I := I) (M := M)
      g r s h_uniform i α P₀ k)
    hFn_eq hFlim_eq

/-! ## Identifying the rescaled un-rescaled limit with the headline limit

`componentLpLimit` is, by construction, `μ` times the canonical eigenvector
chart component `tensorL2ChartComponent φ`; rescaling the un-rescaled limit by
`μ⁻¹` therefore replaces `componentLpLimit` by `tensorL2ChartComponent φ`,
producing the headline limit function `covGradChristoffelLimit`. -/

/-- For each component multi-index pair `p`, `μ⁻¹` times the `coeFn` of the
chart-component limit `componentLpLimit` agrees, almost everywhere, with the
`coeFn` of the canonical eigenvector chart component `tensorL2ChartComponent φ`.

This is the `coeFn` form of the `Lp` identity
`μ⁻¹ • componentLpLimit = tensorL2ChartComponent φ`, which holds because
`componentLpLimit` is, by construction, `μ` times `tensorL2ChartComponent φ`. -/
private lemma smul_componentLpLimit_coeFn_ae
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (p : TensorCompIdx (E := E) r s) :
    (fun y : EuclN => (i.fst.val)⁻¹ *
        (componentLpLimit (I := I) (M := M) g r s h_uniform i α p :
          EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y : EuclN =>
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i) α p :
          EuclN → ℝ) y) := by
  classical
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  -- `μ⁻¹ • componentLpLimit = tensorL2ChartComponent φ` as `Lp` elements.
  have h_lp_eq :
      (i.fst.val)⁻¹ • componentLpLimit (I := I) (M := M)
          g r s h_uniform i α p =
        tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i) α p := by
    rw [componentLpLimit, smul_smul, inv_mul_cancel₀ hμ_ne, one_smul]
  -- The `coeFn` of the scalar multiple is `μ⁻¹ •` the `coeFn`, almost
  -- everywhere; combine with the `coeFn` of the `Lp` equality.
  refine (Lp.coeFn_smul (i.fst.val)⁻¹
    (componentLpLimit (I := I) (M := M) g r s h_uniform i α p)).symm.trans ?_
  exact Filter.EventuallyEq.of_eq
    (congrArg (fun z : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) =>
      (z : EuclN → ℝ)) h_lp_eq)

/-- The `μ⁻¹`-rescaled `L²` class of the un-rescaled limit equals the `L²` class
of the headline limit function `covGradChristoffelLimit`. -/
private lemma smul_unscaledLimit_toLp_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    (i.fst.val)⁻¹ •
        (covGradChristoffelUnscaledLimit_memLp (I := I) (M := M)
          g r s h_uniform i α P₀ k).toLp _ =
      (covGradChristoffelLimit_memLp (I := I) (M := M)
        g r s h_uniform i α P₀ k).toLp _ := by
  classical
  apply Lp.ext
  -- The underlying functions agree almost everywhere.
  refine (Lp.coeFn_smul (i.fst.val)⁻¹
    ((covGradChristoffelUnscaledLimit_memLp (I := I) (M := M)
      g r s h_uniform i α P₀ k).toLp _)).trans ?_
  refine Filter.EventuallyEq.trans ?_
    (MemLp.coeFn_toLp (covGradChristoffelLimit_memLp (I := I) (M := M)
      g r s h_uniform i α P₀ k)).symm
  -- Gather the finitely many per-`p` a.e. identities into a single
  -- a.e.-quantified statement, so each summand may be rewritten after
  -- `filter_upwards`.
  have h_all : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      ∀ p : TensorCompIdx (E := E) r s,
        (i.fst.val)⁻¹ *
            (componentLpLimit (I := I) (M := M) g r s h_uniform i α p :
              EuclN → ℝ) y =
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i) α p :
            EuclN → ℝ) y :=
    (ae_all_iff).mpr (fun p =>
      smul_componentLpLimit_coeFn_ae (I := I) (M := M) g r s h_uniform i α p)
  filter_upwards [MemLp.coeFn_toLp (covGradChristoffelUnscaledLimit_memLp
    (I := I) (M := M) g r s h_uniform i α P₀ k), h_all] with y hy hy_all
  rw [Pi.smul_apply, hy]
  -- Distribute `μ⁻¹` across the finite sum and match summand by summand.
  rw [covGradChristoffelUnscaledLimit, covGradChristoffelLimit, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  -- Reassociate the product so the `μ⁻¹` factor multiplies `componentLpLimit`,
  -- then apply the per-`p` a.e. identity (valid at `y` by `hy_all`).
  rw [mul_left_comm, hy_all p]

/-! ## The headline `L²`-convergence

Rescaling the un-rescaled convergence by the continuous map `μ⁻¹ • ·` and
identifying the rescaled limit with `covGradChristoffelLimit` produces the
headline. -/

/-- **The `n → ∞` `L²`-limit of the covariant-gradient Christoffel correction
term.** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis
index `i` with nonzero resolvent eigenvalue `μ := i.fst.val`, a chart center
`α : M`, a component multi-index `P₀`, and a chart-coordinate direction `k`, the
`μ⁻¹`-rescaled `L²` classes of the zeroth-order Christoffel correction term
`covDerivLowerOrderTerm g r s Tₙ α k P₀.1 P₀.2` at the partition-of-unity-
weighted approximants `Tₙ := pouSmul g r s α (eigenvectorSmoothApprox g r s
h_uniform i n).toCcTensor` converge, as `n → ∞` and in `Lp ℝ 2 (chartL2Measure
α)`, to the `L²` class of the explicit limit function
`covGradChristoffelLimit g r s h_uniform i α P₀ k`.

The `μ⁻¹`-rescaling matches the rescaling convention of every companion
eigenvector chart-component limit object: the limit function is the finite
`C^∞`-coefficient-weighted sum, over component multi-index pairs, of the
canonical eigenvector chart-component limit `tensorL2ChartComponent g r s
(tensorResolventEigenbasisVec h_uniform i) α p`. -/
theorem covGradChristoffel_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ •
        ((covDerivLowerOrderTerm_pouSmul_memLp (I := I) (M := M)
          g r s h_uniform i α P₀ k n).toLp
          (covDerivLowerOrderTerm (I := I) (M := M) g r s
            (pouSmul (I := I) (M := M) g r s α
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s h_uniform i n).toCcTensor) α k P₀.1 P₀.2) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)))
      atTop
      (𝓝 ((covGradChristoffelLimit_memLp (I := I) (M := M)
        g r s h_uniform i α P₀ k).toLp
        (covGradChristoffelLimit (I := I) (M := M)
          g r s h_uniform i α P₀ k))) := by
  classical
  -- Rescale the un-rescaled convergence by the continuous map `μ⁻¹ • ·`.
  have h_smul :=
    (covDerivLowerOrderTerm_pouSmul_tendsto (I := I) (M := M)
      g r s h_uniform i α P₀ k).const_smul (i.fst.val)⁻¹
  -- Identify the rescaled limit with the headline limit function.
  rwa [smul_unscaledLimit_toLp_eq (I := I) (M := M)
    g r s h_uniform i α P₀ k] at h_smul

/-! ## Sanity tests -/

example (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    EuclN → ℝ :=
  covGradChristoffelLimit (I := I) (M := M) g r s h_uniform i α P₀ k

example (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemLp (covGradChristoffelLimit (I := I) (M := M)
        g r s h_uniform i α P₀ k) 2
      (chartL2Measure (I := I) (M := M) α) :=
  covGradChristoffelLimit_memLp (I := I) (M := M) g r s h_uniform i α P₀ k

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
