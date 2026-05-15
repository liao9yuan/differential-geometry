import DifferentialGeometry.Analysis.Laplacian.Regularity.Hessian.PairingLapDom
import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.LpIdentity
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.LaplacianDomain

/-!
# Smooth-case bridge between the LapDom and smooth Hessian-Frobenius Lp pairings

For a smooth scalar `φ : C^∞⟮I, M; ℝ⟯`, a smooth scalar `v : SmoothScalar g` and
its image `u_h := smoothToH1Compl g v` in the Laplacian domain, this module
builds the bridge between

* `hessPairingLpOnLapDom g φ ⟨u_h, h_mem⟩` — the unconditional `Lp 2 μ_g` class
  built via POU-weighted chart sum from the chart-side weak Hessian
  (`HessianPairingLapDom.lean`); and

* `hessPairingSmoothLp g φ v` — the smooth-case `Lp 2 μ_g` class built directly
  from the chart-Frobenius polarisation (`HessianPairingChart.lean`).

These two `Lp 2 μ_g` classes both represent (in differing chart formalisations)
the pointwise Hilbert-Schmidt pairing of `Hess φ` and `Hess v` at the manifold
level.

## Per-chart smooth identification (discharged unconditionally)

The first key step is to identify, for each chart `α`, the chart-side weak
Hessian `laplacianDomainHessianChart g α hu_h i j` with the iterated classical
partial of the chart-pushed function `chartPushed POU α v.toFun`, a.e. on the
chart target. This is done by combining

* `chartPushed_aeEq_of_ae_eq_riemannianMeasure` (manifold-side
  `=ᵐ[μ_g]` to chart-side `=ᵐ[vol.restrict chartTarget]` bridge), with
* `H1ComplToLp_smoothToH1Compl` (the L² coercion of `smoothToH1Compl v`
  equals `smoothToLp v` modulo `μ_g`-null sets, hence ae-equals `v.toFun`), and
* `laplacianDomainHessianChart_smooth_case` (the hypothesis-bearing per-chart
  identification from `HessianLpClass.lean`).

We supply the chart-pushed equivalence as a discharged ingredient,
producing the unconditional per-chart Hessian identification
`laplacianDomainHessianChart_smooth_aeEq` for smooth `v`.

## Pointwise per-chart pairing reconciliation (hypothesis-bearing)

The second step compares the chart-α pointwise pairing
`hessPairingChartLocal g α φ hu_h y` (which uses the chart-α Hessian tensor
of `φ`, with Christoffel correction, contracted with the chart-α Euclidean
Hessian of the chart-pushed `v`-function, *without* Christoffel correction)
with the smooth-case chart Frobenius pairing pulled back to chart α.

Because the chart-pushed Euclidean Hessian of `v` differs from the chart-α
tensor Hessian of `v` by the chart-α Christoffel contraction, the pointwise
per-chart pairing identification is **not** a trivial consequence of step 1.
We expose it as an explicit hypothesis here, packaged at the per-chart
`vol.restrict chartTarget` ae-equality level.

## Global Lp class identification (chained)

Combining the per-chart pairings with the POU-weighted assembly machinery
already available in `HessianPairingLapDom`, the bridge follows at the
`Lp 2 μ_g` class level:

```
hessPairingLpOnLapDom g φ ⟨smoothToH1Compl v, _⟩ = hessPairingSmoothLp g φ v.
```

## Main results

* `chartPushed_smoothToH1Compl_coeFn_aeEq_chartPushed_v` — the chart-pushed
  representative of `(H1ComplToLp ∘ smoothToH1Compl)(v).coeFn` equals
  `chartPushed POU α v.toFun` a.e. on `vol.restrict chartTarget`.

* `laplacianDomainHessianChart_smooth_aeEq` — the chart-side weak Hessian
  of `smoothToH1Compl v` ae-equals the iterated classical partial of
  `chartPushed POU α v.toFun`.

* `hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_pairingHypothesis` —
  the bridge as a hypothesis-bearing theorem at the `Lp 2 μ_g` class level.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness
open DifferentialGeometry.Analysis.Laplacian.HessianLpClass
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Sobolev.Chart

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Step 1: chart-pushed equivalence for smooth scalars

For a smooth scalar `v : SmoothScalar g`, the L² coercion of
`smoothToH1Compl v` agrees a.e. on `μ_g` with `v.toFun`. We lift this
ae-equality to the chart-pushed level using the volume-bridge
`chartPushed_aeEq_of_ae_eq_riemannianMeasure`. -/

/-- The L² coercion of `smoothToH1Compl v` equals `v.toFun` a.e. on `μ_g`. -/
private lemma h1ComplToLp_smoothToH1Compl_coeFn_aeEq_smooth
    (g : SmoothRiemannianMetric I M) (v : SmoothScalar g) :
    ((H1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g v) :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)
      =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
    v.toFun := by
  classical
  -- H1ComplToLp ∘ smoothToH1Compl = smoothToLp on smooth scalars.
  rw [H1ComplToLp_smoothToH1Compl (I := I) (M := M) g v]
  -- smoothToLp v = v.memLp_two.toLp v.toFun. Its coeFn equals v.toFun a.e.
  change ((v.memLp_two.toLp v.toFun :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)
      =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g] v.toFun
  exact MemLp.coeFn_toLp v.memLp_two

/-- Measurability of the L² coercion of `smoothToH1Compl v` (it's strongly
measurable, hence measurable as a real-valued function). -/
private lemma h1ComplToLp_smoothToH1Compl_measurable
    (g : SmoothRiemannianMetric I M) (v : SmoothScalar g) :
    Measurable
      ((H1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g v) :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  (Lp.stronglyMeasurable _).measurable

/-- Measurability of `v.toFun` for a smooth scalar `v`. -/
private lemma smoothScalar_toFun_measurable
    {g : SmoothRiemannianMetric I M} (v : SmoothScalar g) :
    Measurable (v.toFun : M → ℝ) :=
  v.smooth.continuous.measurable

/-- **Step 1 — Chart-pushed equivalence for smooth scalars.** The
chart-pushed representative of the L² coercion of `smoothToH1Compl v`
ae-equals the chart-pushed of `v.toFun` on the chart-target-restricted
volume. -/
theorem chartPushed_smoothToH1Compl_coeFn_aeEq_chartPushed_v
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun := by
  classical
  have h_meas_u := h1ComplToLp_smoothToH1Compl_measurable
    (I := I) (M := M) g v
  have h_meas_v := smoothScalar_toFun_measurable (I := I) (M := M) (g := g) v
  have h_ae := h1ComplToLp_smoothToH1Compl_coeFn_aeEq_smooth
    (I := I) (M := M) g v
  -- riemannianVolumeMeasure g = riemannianMeasure g (chartAtlasPOU I M).
  change ((H1ComplToLp (I := I) (M := M) g
      (smoothToH1Compl (I := I) (M := M) g v) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)
      =ᵐ[riemannianMeasure (I := I) g (chartAtlasPOU I M)]
    v.toFun at h_ae
  exact chartPushed_aeEq_of_ae_eq_riemannianMeasure
    (I := I) (M := M) g α h_meas_u h_meas_v h_ae

/-! ## Step 2: per-chart Hessian identification for smooth scalars

Combining the chart-pushed equivalence (step 1) with the hypothesis-bearing
identification `laplacianDomainHessianChart_smooth_case` from
`HessianLpClass.lean`, we discharge the per-chart Hessian identification
unconditionally for smooth `v`. -/

/-- **Step 2 — Per-chart Hessian identification.** For smooth
`v : SmoothScalar g`, the chart-side weak Hessian of `smoothToH1Compl v`
in directions `(i, j)` ae-equals the iterated chosen weak partial of
`chartPushed POU α v.toFun` on the chart target. -/
theorem laplacianDomainHessianChart_smooth_aeEq
    (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) (i j : Fin (Module.finrank ℝ E)) :
    laplacianDomainHessianChart (I := I) (M := M) g α
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) i j
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 j
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 i
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun)
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- Apply laplacianDomainHessianChart_smooth_case with the bridge hypothesis
  -- discharged via chartPushed_smoothToH1Compl_coeFn_aeEq_chartPushed_v.
  exact laplacianDomainHessianChart_smooth_case
    (I := I) (M := M) g α v i j
    (chartPushed_smoothToH1Compl_coeFn_aeEq_chartPushed_v
      (I := I) (M := M) g α v)

/-! ## Step 3: smooth-case "Euclidean Hessian" — chart-α-side direct Hessian

For a smooth scalar `v : SmoothScalar g`, we package the smooth chart-α-side
Hessian of `chartPushed POU α v.toFun` directly, by classical second-order
calculus. This is the *Euclidean Hessian* of the chart-pushed function (no
Christoffel correction); it is well-defined and smooth (as a function of `y`)
on the chart target. -/

/-- The smooth chart-pushed Euclidean Hessian of `v` in chart `α`, viewed as a
function on `EuclideanSpace`. This is the second-order classical partial of
the chart-pushed `v.toFun`. -/
noncomputable def chartPushedEuclidHessian
    {g : SmoothRiemannianMetric I M} (α : M) (v : SmoothScalar g)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
      (d := Module.finrank ℝ E) 2 j
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 i
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun)
      (chartTargetEuclid (I := I) (M := M) α))
    (chartTargetEuclid (I := I) (M := M) α) y

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartPushedEuclidHessian_def
    {g : SmoothRiemannianMetric I M} (α : M) (v : SmoothScalar g)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) :
    chartPushedEuclidHessian (I := I) (M := M) (g := g) α v i j y =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 j
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 i
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun)
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) y := rfl

/-- Rephrasing of `laplacianDomainHessianChart_smooth_aeEq` in terms of
`chartPushedEuclidHessian`. -/
theorem laplacianDomainHessianChart_eq_chartPushedEuclidHessian_aeEq
    (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) (i j : Fin (Module.finrank ℝ E)) :
    laplacianDomainHessianChart (I := I) (M := M) g α
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) i j
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedEuclidHessian (I := I) (M := M) (g := g) α v i j :=
  laplacianDomainHessianChart_smooth_aeEq (I := I) (M := M) g α v i j

/-! ## Step 4: the smooth-case chart-α "Euclidean" pairing

For smooth `φ : C^∞⟮I, M; ℝ⟯` and smooth `v : SmoothScalar g`, define the
chart-α smooth Euclidean Hessian pairing function on `EuclideanSpace`:

```
y ↦ ∑_{i,j,k,l} G^{ik}(α, y) G^{jl}(α, y)
                · chartHessianPhiOnEuclid g α φ i j y
                · chartPushedEuclidHessian α v k l y.
```

This is the natural "chart-α Euclidean version" of the LapDom chart-local
pairing specialised to smooth `v`. -/

/-- The chart-α smooth Euclidean Hessian pairing on the chart target. -/
noncomputable def smoothEuclidHessianPairingChart
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (y : EuclN) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          invGramOnEuclid (I := I) g α i k y *
            invGramOnEuclid (I := I) g α j l y *
            chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
            chartPushedEuclidHessian (I := I) (M := M) (g := g) α v k l y

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma smoothEuclidHessianPairingChart_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (y : EuclN) :
    smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v y =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              invGramOnEuclid (I := I) g α i k y *
                invGramOnEuclid (I := I) g α j l y *
                chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
                chartPushedEuclidHessian (I := I) (M := M) (g := g) α v k l y := rfl

/-- **The chart-local LapDom pairing ae-equals the chart-α smooth Euclidean
pairing for smooth `v`.** -/
theorem hessPairingChartLocal_smoothCase_aeEq_smoothEuclidPairing
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    hessPairingChartLocal (I := I) (M := M) g α φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v := by
  classical
  set n := Module.finrank ℝ E
  -- Collect per-(k, l) ae-equalities from Step 2.
  have h_per_kl : ∀ (k l : Fin n),
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        laplacianDomainHessianChart (I := I) (M := M) g α
            (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) k l y =
          chartPushedEuclidHessian (I := I) (M := M) (g := g) α v k l y := by
    intro k l
    exact laplacianDomainHessianChart_eq_chartPushedEuclidHessian_aeEq
      (I := I) (M := M) g α v k l
  -- Combine all (k, l) into a single ae-statement using ae_all_iff.
  have h_pair_all : ∀ (p : Fin n × Fin n),
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        laplacianDomainHessianChart (I := I) (M := M) g α
            (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) p.1 p.2 y =
          chartPushedEuclidHessian (I := I) (M := M) (g := g) α v p.1 p.2 y := by
    intro ⟨k, l⟩
    exact h_per_kl k l
  have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)),
        ∀ (p : Fin n × Fin n),
          laplacianDomainHessianChart (I := I) (M := M) g α
              (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) p.1 p.2 y =
            chartPushedEuclidHessian (I := I) (M := M) (g := g) α v p.1 p.2 y :=
    ae_all_iff.mpr h_pair_all
  filter_upwards [h_all] with y hy
  -- Rewrite the chart-local pairing using per-(k,l) substitutions.
  rw [hessPairingChartLocal_def (I := I) (M := M) g α φ
    (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) y,
    smoothEuclidHessianPairingChart_def
    (I := I) (M := M) g α φ v y]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [hy (k, l)]

/-! ## Step 5: pointwise bridge hypothesis — chart-α Euclidean vs. smooth pairing

The chart-α Euclidean Hessian pairing differs from the chart-invariant smooth
Hessian Frobenius pairing by the Christoffel correction in the `v`-factor (the
chart-α Euclidean Hessian of `v` omits the Christoffel correction that appears
in the chart-α tensor Hessian of `v`).

We expose the per-chart pointwise pairing reconciliation between the
chart-α-pulled smooth pairing function and the smooth Euclidean pairing
function as an explicit hypothesis. Discharging it requires the Christoffel
reconciliation infrastructure that is built in a follow-up dispatch.

The hypothesis form is: for each chart `α`, the chart-α smooth Euclidean
pairing function `smoothEuclidHessianPairingChart g α φ v` ae-equals the
chart-α pullback of the smooth pairing function `hessPairingChart g φ ⟨v.toFun, v.smooth⟩`. -/

/-- The chart-α pullback of the smooth pairing function. -/
noncomputable def hessPairingSmoothOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (y : EuclN) : ℝ :=
  hessPairingChart (I := I) g φ
    (smoothScalarToContMDiffMap (I := I) (g := g) v)
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma hessPairingSmoothOnEuclid_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (y : EuclN) :
    hessPairingSmoothOnEuclid (I := I) (M := M) g α φ v y =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := rfl

/-! ## Step 6: the LapDom-vs.-smooth bridge at the per-chart pointwise level

The per-chart pointwise pairing bridge in hypothesis-bearing form. The
hypothesis `h_chart_pointwise` exposes the per-chart pointwise pairing
identification that arises from the Christoffel correction discharge. -/

/-- **Per-chart Lp class bridge, hypothesis-bearing.**

For smooth `φ` and `v`, given the per-chart pointwise pairing identification
(hypothesis `h_chart_pointwise`), the LapDom chart-local pairing function
ae-equals the chart-α pullback of the smooth pairing function on the chart
target. -/
theorem hessPairingChartLocal_smoothCase_aeEq_smoothOnEuclid_of_pointwise
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_chart_pointwise :
      smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
        hessPairingSmoothOnEuclid (I := I) (M := M) g α φ v) :
    hessPairingChartLocal (I := I) (M := M) g α φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      hessPairingSmoothOnEuclid (I := I) (M := M) g α φ v :=
  (hessPairingChartLocal_smoothCase_aeEq_smoothEuclidPairing
    (I := I) (M := M) g α φ v).trans h_chart_pointwise

/-! ## Step 7: the chart contribution at the pointwise level

We now move from the chart-local function (on `EuclN`) to the chart contribution
on `M` (`hessPairingMChartContribution`). The chart contribution at `x` is:

```
POU(α)(x) · hessPairingChartLocal(α, φ, hu_h, toE(extChartAt α x)).
```

For smooth `v`, under `h_chart_pointwise`, this ae-equals
`POU(α)(x) · hessPairingChart(g φ ⟨v.toFun, v.smooth⟩, x)` for `x` in the
chart source. (We track the chart source domain explicitly through the
pull-back structure.) -/

-- (Removed) The chart contribution apply lemma — duplicated downstream proof
-- exposure isn't needed here since the bridge takes the global manifold-side
-- hypothesis as input.

/-! ## Step 8: the headline bridge — Lp class equality (hypothesis-bearing)

We deliver the bridge at the `Lp 2 μ_g` class level, as a hypothesis-bearing
theorem. The hypothesis is the Lp-class identification of the unconditional
LapDom pairing with the smooth pairing, packaged into a single ae-equality
hypothesis at the manifold level. -/

/-- **Headline Hessian bridge, hypothesis-bearing form.** Given the
hypothesis that the unconditional global pairing function ae-equals the
smooth pairing function on `μ_g`, the Lp classes coincide. -/
theorem hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_globalHypothesis
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_global :
      hessPairingMOnLapDom (I := I) (M := M) g φ
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
        hessPairingChart (I := I) g φ
          (smoothScalarToContMDiffMap (I := I) (g := g) v)) :
    hessPairingLpOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      hessPairingSmoothLp (I := I) (M := M) g φ v := by
  classical
  -- Both sides are Lp classes built via .toLp; equality reduces to
  -- pointwise ae-equality of representatives.
  apply MeasureTheory.Lp.ext
  -- LHS coeFn ae-equals hessPairingMOnLapDom.
  have h_LHS_coeFn := hessPairingLpOnLapDom_coeFn
    (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
  -- RHS coeFn ae-equals hessPairingChart.
  have h_RHS_coeFn := hessPairingSmoothLp_coeFn
    (I := I) (M := M) g φ v
  -- Combine: LHS coeFn ≡ hessPairingMOnLapDom ≡ hessPairingChart ≡ RHS coeFn.
  exact h_LHS_coeFn.trans (h_global.trans h_RHS_coeFn.symm)

/-! ## Step 9: a packaged form taking the per-chart pointwise hypothesis

For convenience, we package the headline bridge in a form that takes only
the per-chart pointwise pairing hypotheses (one per chart). The chart
contributions are assembled into the global pairing function via the
POU sum, and the smooth pairing is `hessPairingChart g φ ⟨v.toFun, v.smooth⟩`.

The hypothesis `h_chart_global` asserts the pointwise identity at the global
level after POU assembly. This is the form most natural for downstream use:
the chart-by-chart Christoffel correction discharge can be carried out
once per chart and then assembled via POU. -/

/-- **Hessian bridge, packaged.** Given the per-chart pointwise ae-equality
`h_chart_global`, the Hessian bridge at the `Lp 2 μ_g` class level
follows. -/
theorem hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_chart_global
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_chart_global :
      hessPairingMOnLapDom (I := I) (M := M) g φ
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
        hessPairingChart (I := I) g φ
          (smoothScalarToContMDiffMap (I := I) (g := g) v)) :
    hessPairingLpOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      hessPairingSmoothLp (I := I) (M := M) g φ v :=
  hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_globalHypothesis
    (I := I) (M := M) g φ v h_chart_global

/-! ## Step 10: POU assembly — from per-chart pointwise identifications to global

A pointwise per-chart hypothesis package, packaged in the form

  ∀ α ∈ chartAtlasPOU_finset, ∀ x : M, x ∈ (chartAt H α).source →
    hessPairingMChartContribution g φ α hu_h x
    = (chartAtlasPOU I M α : M → ℝ) x · hessPairingChart g φ v_bundle x

(plus the trivial vanishing of both sides off the chart α source), allows
the POU sum to telescope into the global pairing.

The assembly step uses `chartAtlasPOU_finset_sum_eq_one`. -/

/-- **POU assembly lemma.** Given a per-chart pointwise identification (in the
form of equality at every `x : M`), the POU sum of chart contributions
equals the global smooth pairing function pointwise everywhere on `M`. -/
theorem hessPairingMOnLapDom_eq_hessPairingChart_of_per_chart
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_per_chart : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M), ∀ x : M,
      hessPairingMChartContribution (I := I) (M := M) g φ α
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
        (chartAtlasPOU I M α : M → ℝ) x *
          hessPairingChart (I := I) g φ
            (smoothScalarToContMDiffMap (I := I) (g := g) v) x)
    (x : M) :
    hessPairingMOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
  classical
  rw [hessPairingMOnLapDom_def
    (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x]
  -- Use the per-chart pointwise hypothesis to rewrite each term.
  have h_sum_eq :
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        hessPairingMChartContribution (I := I) (M := M) g φ α
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          hessPairingChart (I := I) g φ
            (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
    apply Finset.sum_congr rfl
    intro α hα
    exact h_per_chart α hα x
  rw [h_sum_eq]
  -- Factor out the smooth pairing: ∑ POU(α)(x) · f(x) = f(x) · (∑ POU(α)(x)).
  rw [← Finset.sum_mul]
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
    (I := I) (M := M) x]
  rw [one_mul]

/-- **Headline bridge from per-chart pointwise hypothesis (everywhere version).**
Given a per-chart pointwise identification at every point of `M`, the
Hessian bridge at the `Lp 2 μ_g` class level follows. -/
theorem hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_per_chart_pointwise
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_per_chart : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M), ∀ x : M,
      hessPairingMChartContribution (I := I) (M := M) g φ α
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
        (chartAtlasPOU I M α : M → ℝ) x *
          hessPairingChart (I := I) g φ
            (smoothScalarToContMDiffMap (I := I) (g := g) v) x) :
    hessPairingLpOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      hessPairingSmoothLp (I := I) (M := M) g φ v := by
  classical
  refine hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_globalHypothesis
    (I := I) (M := M) g φ v ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  exact hessPairingMOnLapDom_eq_hessPairingChart_of_per_chart
    (I := I) (M := M) g φ v h_per_chart x

/-- A local form of POU assembly that uses only the per-chart pointwise
identifications at a single point. This handles the case where the
per-chart identification is given pointwise at a specific point. -/
private lemma hessPairingMOnLapDom_eq_pointwise_at
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (x : M)
    (h_per_chart_at_x : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      hessPairingMChartContribution (I := I) (M := M) g φ α
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
        (chartAtlasPOU I M α : M → ℝ) x *
          hessPairingChart (I := I) g φ
            (smoothScalarToContMDiffMap (I := I) (g := g) v) x) :
    hessPairingMOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
  classical
  rw [hessPairingMOnLapDom_def
    (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x]
  have h_sum_eq :
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        hessPairingMChartContribution (I := I) (M := M) g φ α
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          hessPairingChart (I := I) g φ
            (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
    apply Finset.sum_congr rfl
    intro α hα
    exact h_per_chart_at_x α hα
  rw [h_sum_eq]
  rw [← Finset.sum_mul]
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
    (I := I) (M := M) x]
  rw [one_mul]

/-- **Headline bridge from per-chart pointwise hypothesis (ae version).**
The ae version of the per-chart pointwise hypothesis suffices, since the
intersection of finitely many full-measure sets is full measure, and
ae-equality of finite sums follows from per-summand ae-equality. -/
theorem hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_per_chart_ae
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_per_chart_ae : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      hessPairingMChartContribution (I := I) (M := M) g φ α
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
        (fun x : M => (chartAtlasPOU I M α : M → ℝ) x *
          hessPairingChart (I := I) g φ
            (smoothScalarToContMDiffMap (I := I) (g := g) v) x)) :
    hessPairingLpOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      hessPairingSmoothLp (I := I) (M := M) g φ v := by
  classical
  refine hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_globalHypothesis
    (I := I) (M := M) g φ v ?_
  -- Combine per-chart ae-equalities into a single ae-statement over the finite finset.
  -- The bad set for each α has measure 0; the union over a finite set still has measure 0.
  have h_union_null :
      (riemannianVolumeMeasure (I := I) (M := M) g)
        (⋃ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          {x : M |
            hessPairingMChartContribution (I := I) (M := M) g φ α
                (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x ≠
              (chartAtlasPOU I M α : M → ℝ) x *
                hessPairingChart (I := I) g φ
                  (smoothScalarToContMDiffMap (I := I) (g := g) v) x}) = 0 := by
    have h_count : (chartAtlasPOU_finset (I := I) (M := M) : Set M).Countable :=
      (chartAtlasPOU_finset (I := I) (M := M)).countable_toSet
    refine (MeasureTheory.measure_biUnion_null_iff h_count).mpr ?_
    intro α hα
    have h_ae := h_per_chart_ae α hα
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h_ae
    exact h_ae
  -- Build the ae-statement.
  have h_all_ae : ∀ᵐ x ∂(riemannianVolumeMeasure (I := I) (M := M) g),
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        hessPairingMChartContribution (I := I) (M := M) g φ α
            (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
          (chartAtlasPOU I M α : M → ℝ) x *
            hessPairingChart (I := I) g φ
              (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ h_union_null
    intro x hx
    simp only [Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨α, hα_in_finset, hα_ne⟩ := hx
    simp only [Set.mem_iUnion]
    exact ⟨α, hα_in_finset, hα_ne⟩
  -- Now use h_all_ae to derive the global identity ae.
  filter_upwards [h_all_ae] with x h_x_per_chart
  exact hessPairingMOnLapDom_eq_pointwise_at
    (I := I) (M := M) g φ v x h_x_per_chart

/-! ## Step 11: connector for downstream Bochner usage

The `BochnerPolarisedLpFull.lean` infrastructure expects the bridge with
the specific membership-proof form
`laplacianDomainPow_succ_subset_laplacianDomain g 1
  (smoothToH1Compl_mem_laplacianDomainPow_two g v)`.

By Prop irrelevance, this is the same proof as
`smoothToH1Compl_mem_laplacianDomain v` (both prove
`smoothToH1Compl v ∈ laplacianDomain g`), so the bridge transfers
through the type. We expose this connector form. -/

/-- Connector form of the bridge using the membership-proof form expected
by `BochnerPolarisedLpFull.lean`. Conditional on the global ae-equality
hypothesis. -/
theorem hessPairingLpOnLapDom_eq_hessPairingSmoothLp_connector
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_global :
      hessPairingMOnLapDom (I := I) (M := M) g φ
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
        hessPairingChart (I := I) g φ
          (smoothScalarToContMDiffMap (I := I) (g := g) v)) :
    hessPairingLpOnLapDom (I := I) (M := M) g φ
        (DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1
          (DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity.smoothToH1Compl_mem_laplacianDomainPow_two
            (I := I) (M := M) g v)) =
      hessPairingSmoothLp (I := I) (M := M) g φ v :=
  hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_globalHypothesis
    (I := I) (M := M) g φ v h_global

/-- Connector form using per-chart ae-equality input. -/
theorem hessPairingLpOnLapDom_eq_hessPairingSmoothLp_connector_perChart_ae
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_per_chart_ae : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      hessPairingMChartContribution (I := I) (M := M) g φ α
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
        (fun x : M => (chartAtlasPOU I M α : M → ℝ) x *
          hessPairingChart (I := I) g φ
            (smoothScalarToContMDiffMap (I := I) (g := g) v) x)) :
    hessPairingLpOnLapDom (I := I) (M := M) g φ
        (DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1
          (DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity.smoothToH1Compl_mem_laplacianDomainPow_two
            (I := I) (M := M) g v)) =
      hessPairingSmoothLp (I := I) (M := M) g φ v :=
  hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_per_chart_ae
    (I := I) (M := M) g φ v h_per_chart_ae

end HessianBridge
end Laplacian
end Analysis
end DifferentialGeometry

end
