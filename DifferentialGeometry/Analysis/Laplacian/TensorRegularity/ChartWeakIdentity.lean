import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.RotatedTestSection
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.PrincipalForm
import DifferentialGeometry.Analysis.Laplacian.Operator.ChartMeasureEquiv

/-!
# Chart-pull of the tensor `H^1` Dirichlet integral and the rotated principal collapse

For a smooth Riemannian metric `g` on a closed manifold `(M, g)`, a chart center
`α : M`, and tensor ranks `(r, s)`, this file performs two reductions on the
`H^1` Dirichlet form of `(r, s)`-tensor sections.

* It pulls the global Riemannian-volume integral of the pointwise Dirichlet
  integrand `tensorCovDerivPointwiseInner g r s S T = ⟨∇S, ∇T⟩` to the Euclidean
  chart target: when one of the two sections is supported inside the chart, the
  integral over `(M, g)` becomes a chart-Euclidean integral of the density-weighted
  chart-coordinate decomposition `densityOnEuclid · (covPrincipalIntegrand +
  covLowerOrderIntegrand)`.

* It substitutes the inverse-Gram-rotated test section
  `rotatedTestSection g r s α P₀ χ` into the second slot of the component-coupled
  principal part `covPrincipalIntegrand`. The Gram / inverse-Gram collapse
  `covChartMetricGram_mul_inv_collapse` decouples the component-coupled double
  sum: the principal part of the rotated test section collapses to the single
  component `P₀`, isolating the scalar elliptic principal integrand
  `∑_{k,l} g^{kl} · ∂_k(S_{P₀}) · ∂_l χ̃`, plus a genuine first-order remainder
  `covPrincipalRotationRemainder` collecting the contributions where the
  Euclidean partial derivative falls on the inverse-Gram coefficient.

A final identification ties the scalar principal integrand to the divergence-form
data `tensorPrincipalForm`: on the compact chart-interior set `K`, the
density-weighted inverse-Gram pairing is exactly the `principalIntegrand` of the
principal-part elliptic bilinear form.

## Main definitions

* `covPrincipalRotationRemainder g r s S α P₀ χ hχs hχt` — the first-order
  remainder of the rotated principal part: the contributions in which the
  chart-Euclidean partial derivative `∂_l` of the rotated test section's chart
  component falls on the inverse-Gram coefficient `covChartMetricGramInv`. It is
  a plain function `EuclideanSpace ℝ (Fin n) → ℝ`, first-order in `S`, with `C^∞`
  coefficients.

## Main results

* `tensorCovDerivPointwiseInner_integral_chart_pull` — the chart-pull of the
  global `H^1` Dirichlet integral to the Euclidean chart target.
* `covPrincipalIntegrand_rotated_collapse` — on the Euclidean chart target the
  rotated principal part collapses to the single-component scalar elliptic
  principal integrand plus `covPrincipalRotationRemainder`.
* `covPrincipalRotationRemainder_contDiffOn` — the rotation remainder is `C^∞`
  on the Euclidean chart target.
* `weightedInvGram_principalIntegrand_eq` — on the compact chart-interior set the
  density-weighted inverse-Gram pairing equals the `principalIntegrand` of
  `tensorPrincipalForm`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix

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
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M`

Match the convention in the surrounding chart-local Laplacian files: install
the Borel σ-algebras locally, without leaking global instances onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Chart-pull of the global `H^1` Dirichlet integral

The pointwise `H^1` Dirichlet integrand `tensorCovDerivPointwiseInner g r s S T`
is continuous (`tensorCovDerivPointwiseInner_continuous`) and vanishes wherever
the first section vanishes (`tensorCovDerivPointwiseInner_tsupport_subset_left`).
Hence whenever the first section is supported inside the chart source, the
integrand itself is chart-supported, and the chart-pulled volume identity
`integral_riemannianVolumeMeasure_eq_euclidean_chartTarget` applies. The
chart-coordinate decomposition `tensorCovDerivPointwiseInner_chart_eq` rewrites
the chart-pulled integrand into `covPrincipalIntegrand + covLowerOrderIntegrand`
on the Euclidean chart target. -/

/-- **Chart-pull of the tensor `H^1` Dirichlet integral.** For smooth compactly
supported `(r, s)`-tensor sections `S`, `T` with the topological support of `S`
contained in the chart source `(chartAt H α).source`, the global integral of the
pointwise `H^1` Dirichlet integrand `tensorCovDerivPointwiseInner g r s S T =
⟨∇S, ∇T⟩` against the Riemannian volume measure equals the Euclidean chart-target
integral of `densityOnEuclid` times the chart-coordinate decomposition
`covPrincipalIntegrand + covLowerOrderIntegrand`.

The hypothesis `tsupport S.toFun ⊆ (chartAt H α).source` is the honest
chart-containment hypothesis: the integrand `tensorCovDerivPointwiseInner g r s
S T` vanishes off `tsupport S.toFun`, so this hypothesis forces the integrand to
be chart-supported, which is exactly what the volume chart-pull consumes. -/
theorem tensorCovDerivPointwiseInner_integral_chart_pull
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M)
    (hS_supp : tsupport S.toFun ⊆ (chartAt H α).source) :
    ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (covPrincipalIntegrand (I := I) (M := M) g r s S T α y +
            covLowerOrderIntegrand (I := I) (M := M) g r s S T α y)
        ∂(MeasureTheory.Measure.map (toEuclidean : E →
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
            (modelHaar (E := E))) := by
  classical
  -- The integrand is continuous on `M`.
  have hcont : Continuous
      (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T) :=
    tensorCovDerivPointwiseInner_continuous (I := I) (M := M) g r s S T
  -- The integrand is chart-supported: it vanishes off `tsupport S.toFun`, which
  -- the hypothesis places inside the chart source.
  have hsupp : tsupport
      (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T) ⊆
      (chartAt H α).source :=
    (tensorCovDerivPointwiseInner_tsupport_subset_left
      (I := I) (M := M) g r s S T).trans hS_supp
  -- Pull the global integral to the Euclidean chart target.
  rw [integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
    (I := I) (M := M) g α hcont hsupp]
  -- The Euclidean chart target is open, hence measurable.
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  -- On the chart target rewrite the chart-pulled integrand by the
  -- principal / lower-order decomposition.
  refine setIntegral_congr_fun hctE_meas (fun y hy => ?_)
  rw [tensorCovDerivPointwiseInner_chart_eq (I := I) (M := M) g r s S T α hy]

/-! ## Smoothness of the Euclidean push-forward of the scalar bump

The scalar bump `χ`, smooth on the chart source `(chartAt H α).source`, has a
Euclidean push-forward `chartPushedRaw I α χ` that is `C^∞` on the Euclidean
chart target: on the target it is the composition of `χ` with the smooth
inverse chart map and the linear isometry `toEuclidean.symm`. This mirrors the
push-forward smoothness of the raw chart components. -/

/-- The Euclidean push-forward `chartPushedRaw I α χ` of a scalar bump `χ` that
is smooth on the chart source is `ContDiffOn ℝ ∞` on the Euclidean chart
target. -/
theorem chartPushedRaw_bump_contDiffOn
    (α : M) {χ : M → ℝ}
    (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source) :
    ContDiffOn ℝ ∞ (chartPushedRaw I α χ)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- The bump is `C^∞` on `(extChartAt I α).source = (chartAt H α).source`.
  have hχ_extsrc : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hχs
  -- Compose with `(extChartAt I α).symm`: smooth on the chart target.
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (extChartAt I α).source := fun y hy => (extChartAt I α).map_target hy
  have hcomp_E : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (χ ∘ (extChartAt I α).symm) (extChartAt I α).target :=
    hχ_extsrc.comp hsymm hmaps
  have hcontDiff_E : ContDiffOn ℝ ∞
      (χ ∘ (extChartAt I α).symm) (extChartAt I α).target :=
    hcomp_E.contDiffOn
  -- Pre-compose with the linear isometry `toEuclidean.symm`.
  have hcomp_eucl : ContDiffOn ℝ ∞
      ((χ ∘ (extChartAt I α).symm) ∘
        (toEuclidean.symm :
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine hcontDiff_E.comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
  -- On the chart target `chartPushedRaw` is this composition.
  refine hcomp_eucl.congr (fun z hz => ?_)
  exact chartPushedRaw_apply_of_mem (I := I) (M := M) α χ hz

/-! ## A chart-target Leibniz rule for the Euclidean partial derivative

The chart-Euclidean partial derivative `euclidPartial l u y = fderiv ℝ u y
(EuclideanSpace.single l 1)` is computed from the Fréchet derivative; the
Leibniz / product rule `fderiv_fun_mul` for the Fréchet derivative of a product
of two functions differentiable at `y` therefore yields the corresponding
product rule for `euclidPartial`. -/

/-- **Leibniz rule for the Euclidean partial derivative.** For functions `f`,
`h : EuclideanSpace ℝ (Fin n) → ℝ` both differentiable at `y`, the `l`-th
chart-Euclidean partial derivative of the product `f · h` satisfies
`∂_l (f · h) = (∂_l f) · h + f · (∂_l h)` at `y`. -/
lemma euclidPartial_mul
    (l : Fin (Module.finrank ℝ E))
    {f h : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hf : DifferentiableAt ℝ f y) (hh : DifferentiableAt ℝ h y) :
    euclidPartial (E := E) l (fun z => f z * h z) y =
      euclidPartial (E := E) l f y * h y + f y * euclidPartial (E := E) l h y := by
  -- Unfold `euclidPartial` to the Fréchet derivative and apply `fderiv_fun_mul`.
  rw [euclidPartial_def, euclidPartial_def, euclidPartial_def,
    fderiv_fun_mul hf hh]
  -- Evaluate the sum of continuous linear maps at the basis vector.
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

/-! ## A chart-target smoothness rule for the Euclidean partial derivative

If a scalar function `u` is `C^∞` on the open Euclidean chart target, its `l`-th
chart-Euclidean partial derivative is again `C^∞` there: on the open set the
Fréchet derivative coincides with the within-derivative, which is `C^∞` by
`contDiffOn_succ_iff_fderivWithin`, and evaluation at a fixed basis vector is a
continuous linear map. -/

/-- The `l`-th chart-Euclidean partial derivative of a function `C^∞` on the
Euclidean chart target is again `C^∞` on the Euclidean chart target. -/
private lemma euclidPartial_contDiffOn_chartTarget
    (α : M) (l : Fin (Module.finrank ℝ E))
    {u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hu : ContDiffOn ℝ ∞ u (chartTargetEuclid (I := I) (M := M) α)) :
    ContDiffOn ℝ ∞ (euclidPartial (E := E) l u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The Fréchet derivative of `u` is `C^∞` on the open chart target.
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
  -- Evaluation at `single l 1` is a continuous linear map; compose.
  have hcomp : ContDiffOn ℝ ∞
      ((fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
          L (EuclideanSpace.single l 1)) ∘ (fun z => fderiv ℝ u z))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single l 1)).contDiff.comp_contDiffOn hfderiv
  refine hcomp.congr (fun z _ => ?_)
  rfl

/-! ## The chart component of the rotated test section as a chart-target function

The headline component identity `rotatedTestSection_chartComp` evaluates the raw
chart component of `rotatedTestSection g r s α P₀ χ` at the chart-source preimage
of a chart-target point. Composing it through the Euclidean push-forward
`chartPushedRaw` records the corresponding identity of *functions* on the open
Euclidean chart target: the push-forward of the rotated test section's raw chart
component agrees there with the product of the inverse-Gram entry
`covChartMetricGramInv g r s α · Q P₀` and the chart-pushed bump
`chartPushedRaw I α χ`. -/

/-- The inverse-Gram column entry `covChartMetricGramInv g r s α · Q P₀` as a
function on the Euclidean chart target. -/
noncomputable def gramInvEntry
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Q P₀ : CompIdx E r s) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y => covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀

/-- The inverse-Gram column entry `gramInvEntry g r s α Q P₀` is `C^∞` on the
Euclidean chart target — a restatement of `covChartMetricGramInv_entry_contDiffOn`. -/
lemma gramInvEntry_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Q P₀ : CompIdx E r s) :
    ContDiffOn ℝ ∞ (gramInvEntry (I := I) (M := M) g r s α Q P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
  covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α Q P₀

/-- On the Euclidean chart target the Euclidean push-forward of the raw chart
component of `rotatedTestSection g r s α P₀ χ` at the multi-index `Q` agrees
with the product of the inverse-Gram column entry `gramInvEntry g r s α Q P₀`
and the chart-pushed bump `chartPushedRaw I α χ`. -/
lemma chartPushedRaw_rotatedTestSection_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s) :
    Set.EqOn
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s
          (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
          α Q.1 Q.2))
      (fun y => gramInvEntry (I := I) (M := M) g r s α Q P₀ y *
        chartPushedRaw I α χ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  -- On the chart target the push-forward is the raw component at the preimage.
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  -- The headline component identity for the rotated test section.
  rw [rotatedTestSection_chartComp (I := I) (M := M) g r s α P₀ hχs hχt Q hy]
  rfl

/-! ## The first-order rotation remainder

When the inverse-Gram-rotated test section is substituted into the second slot
of the component-coupled principal part `covPrincipalIntegrand`, the chart
component of the rotated test section is the product
`covChartMetricGramInv g r s α · Q P₀ · chartPushedRaw I α χ`. The chart-Euclidean
partial derivative `∂_l` of this product splits, by the Leibniz rule, into a
term where `∂_l` falls on the chart-pushed bump and a term where it falls on the
inverse-Gram coefficient. The first term collapses cleanly through the Gram /
inverse-Gram contraction; the second term is genuine and is collected here as
the **rotation remainder**.

It pairs the chart-Euclidean partial `∂_k` of the raw chart component of `S`
against `(∂_l covChartMetricGramInv) · χ̃` — first-order in `S`, with `C^∞`
coefficients. -/

/-- **The first-order rotation remainder of the rotated principal part.** The
contributions to the rotated principal part `covPrincipalIntegrand g r s S
(rotatedTestSection …) α` in which the chart-Euclidean partial derivative `∂_l`
falls on the inverse-Gram coefficient `covChartMetricGramInv g r s α · Q P₀`
rather than on the chart-pushed bump.

It is a plain function `EuclideanSpace ℝ (Fin n) → ℝ` — first-order in `S`, with
`C^∞` coefficients — collected so the rotated principal part decomposes as the
single-component scalar elliptic principal integrand plus this remainder. -/
noncomputable def covPrincipalRotationRemainder
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (χ : M → ℝ)
    (_hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (_hχt : tsupport χ ⊆ (chartAt H α).source) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    ∑ P : CompIdx E r s,
      ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                  euclidPartial (E := E) k
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M)
                        g r s S α P.1 P.2)) y *
                (euclidPartial (E := E) l
                    (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
                  chartPushedRaw I α χ y)

/-- Unfolding lemma for `covPrincipalRotationRemainder`. -/
lemma covPrincipalRotationRemainder_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covPrincipalRotationRemainder (I := I) (M := M) g r s S α P₀ χ hχs hχt y =
      ∑ P : CompIdx E r s,
        ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                    euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s S α P.1 P.2)) y *
                  (euclidPartial (E := E) l
                      (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
                    chartPushedRaw I α χ y) := rfl

/-! ## Smoothness of the rotation remainder

Every constituent of the rotation remainder is `C^∞` on the Euclidean chart
target: the chart-frame tensor-metric Gram `covChartMetricGram` and the
un-weighted inverse Gram `chartInvGramEuclid` are `C^∞`; the chart-Euclidean
partial of the raw chart component push-forward of `S` is `C^∞`; the inverse-Gram
column entry `gramInvEntry` is `C^∞` and so is its chart-Euclidean partial; and
the chart-pushed bump `chartPushedRaw I α χ` is `C^∞`. A finite sum and product
of `C^∞` functions is `C^∞`. -/

/-- **The first-order rotation remainder is `C^∞` on the Euclidean chart
target.** A finite sum and product of `C^∞` functions: the prefactors
`covChartMetricGram` and `chartInvGramEuclid`, the chart-Euclidean partials of
the raw chart component push-forwards and of the inverse-Gram column entries,
and the chart-pushed bump are all `C^∞`. -/
theorem covPrincipalRotationRemainder_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) :
    ContDiffOn ℝ ∞
      (covPrincipalRotationRemainder (I := I) (M := M) g r s S α P₀ χ hχs hχt)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- The chart-pushed bump is `C^∞` on the chart target.
  have hbump : ContDiffOn ℝ ∞ (chartPushedRaw I α χ)
      (chartTargetEuclid (I := I) (M := M) α) :=
    chartPushedRaw_bump_contDiffOn (I := I) (M := M) α hχs
  -- The `(P, Q)`-summand is `C^∞`.
  have hsummand : ∀ P Q : CompIdx E r s,
      ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                    euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s S α P.1 P.2)) y *
                  (euclidPartial (E := E) l
                      (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
                    chartPushedRaw I α χ y))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro P Q
    -- The chart-frame tensor-metric Gram prefactor is `C^∞`.
    have hgram : ContDiffOn ℝ ∞
        (covChartMetricGram (I := I) (M := M) g r s α P Q)
        (chartTargetEuclid (I := I) (M := M) α) :=
      covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q
    -- The chart-Euclidean partial of the raw-component push-forward of `S`.
    have hSpartial : ∀ k : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s S α P.1 P.2)))
          (chartTargetEuclid (I := I) (M := M) α) := fun k =>
      euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M)
        g r s S α k P.1 P.2
    -- The chart-Euclidean partial of the inverse-Gram column entry.
    have hGinvPartial : ∀ l : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞
          (euclidPartial (E := E) l
            (gramInvEntry (I := I) (M := M) g r s α Q P₀))
          (chartTargetEuclid (I := I) (M := M) α) := fun l =>
      euclidPartial_contDiffOn_chartTarget (I := I) (M := M) α l
        (gramInvEntry_contDiffOn (I := I) (M := M) g r s α Q P₀)
    -- The inner `(k, l)`-summand is `C^∞`.
    have hinner : ∀ k l : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            chartInvGramEuclid (I := I) g α k l y *
                euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M)
                      g r s S α P.1 P.2)) y *
              (euclidPartial (E := E) l
                  (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
                chartPushedRaw I α χ y))
          (chartTargetEuclid (I := I) (M := M) α) := by
      intro k l
      have hGinv : ContDiffOn ℝ ∞ (chartInvGramEuclid (I := I) g α k l)
          (chartTargetEuclid (I := I) (M := M) α) :=
        chartInvGramEuclid_contDiffOn (I := I) (M := M) g α k l
      exact ((hGinv.mul (hSpartial k)).mul
        ((hGinvPartial l).mul hbump))
    -- A finite sum of `C^∞` functions is `C^∞`.
    have hklsum : ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                  euclidPartial (E := E) k
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M)
                        g r s S α P.1 P.2)) y *
                (euclidPartial (E := E) l
                    (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
                  chartPushedRaw I α χ y))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ContDiffOn.sum (fun k _ => ContDiffOn.sum (fun l _ => hinner k l))
    exact hgram.mul hklsum
  -- A finite sum of `C^∞` functions is `C^∞`; the rotation remainder is,
  -- definitionally, exactly this finite sum.
  have hsum : ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        ∑ P : CompIdx E r s,
          ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramEuclid (I := I) g α k l y *
                      euclidPartial (E := E) k
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s S α P.1 P.2)) y *
                    (euclidPartial (E := E) l
                        (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
                      chartPushedRaw I α χ y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    ContDiffOn.sum (fun P _ => ContDiffOn.sum (fun Q _ => hsummand P Q))
  exact hsum

/-! ## The rotated principal collapse

The component-coupled principal part `covPrincipalIntegrand` evaluated at the
rotated test section is collapsed in four steps.

1. On the open chart target the Euclidean push-forward of the rotated test
   section's raw chart component is the product `covChartMetricGramInv · Q P₀ ·
   chartPushedRaw I α χ` (`chartPushedRaw_rotatedTestSection_eqOn`); since the
   chart-Euclidean partial derivative `∂_l` is a local operation, it agrees with
   the partial of that product on the open chart target.

2. The Leibniz rule `euclidPartial_mul` splits `∂_l (covChartMetricGramInv · Q P₀
   · χ̃)` into `(∂_l covChartMetricGramInv · Q P₀) · χ̃` and `covChartMetricGramInv
   · Q P₀ · (∂_l χ̃)`.

3. The summand factorises; the only `Q`-dependence of the second Leibniz piece
   is `covChartMetricGram P Q · covChartMetricGramInv Q P₀`, which contracts —
   over `Q` — to the Kronecker delta `[P = P₀]` by
   `covChartMetricGram_mul_inv_collapse`.

4. The `[P = P₀]` delta collapses the outer `P`-sum to the single `P₀`-term: the
   scalar elliptic principal integrand `∑_{k,l} g^{kl} · ∂_k(S_{P₀}) · ∂_l χ̃`.
   The first Leibniz piece is the rotation remainder. -/

/-- On the open Euclidean chart target the chart-Euclidean partial derivative of
the Euclidean push-forward of the rotated test section's raw chart component
splits, by the Leibniz rule, into the inverse-Gram-coefficient term and the
chart-pushed-bump term. -/
lemma euclidPartial_chartPushedRaw_rotatedTestSection_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s) (l : Fin (Module.finrank ℝ E)) :
    Set.EqOn
      (euclidPartial (E := E) l
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s
            (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
            α Q.1 Q.2)))
      (fun y =>
        euclidPartial (E := E) l
            (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
          chartPushedRaw I α χ y +
        gramInvEntry (I := I) (M := M) g r s α Q P₀ y *
          euclidPartial (E := E) l (chartPushedRaw I α χ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
  -- `C^∞`-ness of the two factors of the product.
  have hGinv : ContDiffOn ℝ ∞ (gramInvEntry (I := I) (M := M) g r s α Q P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
    gramInvEntry_contDiffOn (I := I) (M := M) g r s α Q P₀
  have hbump : ContDiffOn ℝ ∞ (chartPushedRaw I α χ)
      (chartTargetEuclid (I := I) (M := M) α) :=
    chartPushedRaw_bump_contDiffOn (I := I) (M := M) α hχs
  -- The push-forward of the rotated test section's raw component is the product.
  have heqOn := chartPushedRaw_rotatedTestSection_eqOn (I := I) (M := M)
    g r s α P₀ hχs hχt Q
  intro y hy
  -- `∂_l` agrees with `∂_l` of the product, since on the open chart target
  -- the two functions coincide.
  have hpartial_eq : euclidPartial (E := E) l
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s
            (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
            α Q.1 Q.2)) y =
      euclidPartial (E := E) l
        (fun z => gramInvEntry (I := I) (M := M) g r s α Q P₀ z *
          chartPushedRaw I α χ z) y := by
    rw [euclidPartial_def, euclidPartial_def]
    -- The Fréchet derivatives agree, since the functions agree on an open
    -- neighbourhood of `y`.
    have hfderiv_eq :=
      Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (x := y)
        (Filter.eventuallyEq_of_mem (hopen.mem_nhds hy) heqOn)
    rw [hfderiv_eq]
  rw [hpartial_eq]
  -- The Leibniz rule for the chart-Euclidean partial derivative of the product.
  have hGinv_diff : DifferentiableAt ℝ
      (gramInvEntry (I := I) (M := M) g r s α Q P₀) y :=
    (hGinv.differentiableOn (by simp)).differentiableAt
      (hopen.mem_nhds hy)
  have hbump_diff : DifferentiableAt ℝ (chartPushedRaw I α χ) y :=
    (hbump.differentiableOn (by simp)).differentiableAt
      (hopen.mem_nhds hy)
  exact euclidPartial_mul (E := E) l hGinv_diff hbump_diff

/-- **The rotated principal collapse.** On the Euclidean chart target the
component-coupled principal part `covPrincipalIntegrand` evaluated at the
inverse-Gram-rotated test section `rotatedTestSection g r s α P₀ χ` collapses to
the single-component scalar elliptic principal integrand `∑_{k,l} g^{kl} ·
∂_k(S_{P₀}) · ∂_l χ̃` plus the first-order rotation remainder
`covPrincipalRotationRemainder`.

The Gram / inverse-Gram contraction `covChartMetricGram_mul_inv_collapse` is the
mechanism: only the Leibniz piece in which `∂_l` falls on the chart-pushed bump
`χ̃` contracts the component-coupled double sum to the single component `P₀`. -/
theorem covPrincipalIntegrand_rotated_collapse
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covPrincipalIntegrand (I := I) (M := M) g r s S
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α y =
      (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramEuclid (I := I) g α k l y *
              euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s S α P₀.1 P₀.2)) y *
            euclidPartial (E := E) l (chartPushedRaw I α χ) y) +
        covPrincipalRotationRemainder (I := I) (M := M) g r s S α P₀ χ hχs hχt y := by
  classical
  -- Unfold the principal part and the rotation remainder.
  rw [covPrincipalIntegrand_def, covPrincipalRotationRemainder_def]
  -- Step 1+2: rewrite the `∂_l` of the rotated test section's chart component
  -- by the Leibniz split, valid at `y` in the chart target.
  have hleibniz : ∀ Q : CompIdx E r s, ∀ l : Fin (Module.finrank ℝ E),
      euclidPartial (E := E) l
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s
              (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
              α Q.1 Q.2)) y =
        euclidPartial (E := E) l
            (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
          chartPushedRaw I α χ y +
        gramInvEntry (I := I) (M := M) g r s α Q P₀ y *
          euclidPartial (E := E) l (chartPushedRaw I α χ) y := fun Q l =>
    euclidPartial_chartPushedRaw_rotatedTestSection_eqOn (I := I) (M := M)
      g r s α P₀ hχs hχt Q l hy
  -- Abbreviations for the recurring `(k, l)`-sums.
  set bumpSum :
      (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
    fun P =>
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramEuclid (I := I) g α k l y *
              euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s S α P.1 P.2)) y *
            euclidPartial (E := E) l (chartPushedRaw I α χ) y with hbumpSum_def
  set remSum :
      (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) →
      (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
    fun P Q =>
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramEuclid (I := I) g α k l y *
              euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s S α P.1 P.2)) y *
            (euclidPartial (E := E) l
                (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
              chartPushedRaw I α χ y) with hremSum_def
  -- Step 1+2+3: rewrite the `(P, Q)` double sum of the principal part as a
  -- `bumpSum` group (weighted by `covG · gramInvEntry`) plus the `remSum` group.
  have hLHS :
      (∑ P : CompIdx E r s,
        ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                    euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s S α P.1 P.2)) y *
                  euclidPartial (E := E) l
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M) g r s
                        (rotatedTestSection (I := I) (M := M) g r s α P₀
                          χ hχs hχt)
                        α Q.1 Q.2)) y) =
        (∑ P : CompIdx E r s,
          ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              gramInvEntry (I := I) (M := M) g r s α Q P₀ y * bumpSum P) +
        ∑ P : CompIdx E r s,
          ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y * remSum P Q := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    -- Substitute the Leibniz split into the inner `(k, l)`-sum.
    have hinner :
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
                euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M)
                      g r s S α P.1 P.2)) y *
              euclidPartial (E := E) l
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s
                    (rotatedTestSection (I := I) (M := M) g r s α P₀
                      χ hχs hχt)
                    α Q.1 Q.2)) y) =
          gramInvEntry (I := I) (M := M) g r s α Q P₀ y * bumpSum P +
            remSum P Q := by
      rw [hbumpSum_def, hremSum_def, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [hleibniz Q l]
      ring
    rw [hinner, mul_add]
    ring
  rw [hLHS]
  -- Step 3+4: the `bumpSum`-group's `Q`-collapse factor contracts to the
  -- Kronecker delta, collapsing the outer `P`-sum to the single `P₀`-term.
  have hcollapse : ∀ P : CompIdx E r s,
      (∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          gramInvEntry (I := I) (M := M) g r s α Q P₀ y * bumpSum P) =
        (if P = P₀ then (1 : ℝ) else 0) * bumpSum P := by
    intro P
    -- Factor `bumpSum P` (constant in `Q`) out of the `Q`-sum.
    rw [← Finset.sum_mul]
    congr 1
    -- `gramInvEntry g r s α Q P₀ y = covChartMetricGramInv g r s α y Q P₀`.
    have hrw : ∀ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
            gramInvEntry (I := I) (M := M) g r s α Q P₀ y =
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ := fun Q => rfl
    rw [Finset.sum_congr rfl (fun Q _ => hrw Q)]
    exact covChartMetricGram_mul_inv_collapse (I := I) (M := M) g r s α hy P P₀
  -- The `bumpSum` group collapses to the single-component `P₀`-term.
  have hbump_collapse :
      (∑ P : CompIdx E r s,
        ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            gramInvEntry (I := I) (M := M) g r s α Q P₀ y * bumpSum P) =
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
                euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M)
                      g r s S α P₀.1 P₀.2)) y *
              euclidPartial (E := E) l (chartPushedRaw I α χ) y := by
    rw [Finset.sum_congr rfl (fun P _ => hcollapse P)]
    rw [Finset.sum_eq_single P₀]
    · rw [if_pos rfl, one_mul, hbumpSum_def]
    · intro P _ hP
      rw [if_neg hP, zero_mul]
    · intro hP₀
      exact absurd (Finset.mem_univ P₀) hP₀
  rw [hbump_collapse]

/-! ## The density-weighted inverse-Gram pairing as a `principalIntegrand`

The principal coefficient matrix of the principal-part elliptic bilinear form
`tensorPrincipalForm g α hK hK_target` agrees on the compact chart-interior set
`K` with the volume-weighted inverse Gram matrix `weightedInvGramEuclid g α`
(`= √(det g) · gᵏˡ`). Since `weightedInvGramEuclid` is, definitionally, the
product of the chart density `densityOnEuclid` and the un-weighted inverse Gram
`chartInvGramEuclid`, the density-weighted inverse-Gram pairing
`densityOnEuclid · ∑ g^{kl} ∂_k u ∂_l φ` is exactly the `principalIntegrand` of
`tensorPrincipalForm`. -/

/-- The volume-weighted inverse Gram entry `weightedInvGramEuclid g α k l`
factorises as the chart density `densityOnEuclid g α` times the un-weighted
inverse Gram entry `chartInvGramEuclid g α k l`. -/
private lemma weightedInvGramEuclid_eq_density_mul_invGram
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    weightedInvGramEuclid (I := I) g α k l y =
      densityOnEuclid (I := I) g α y *
        chartInvGramEuclid (I := I) g α k l y :=
  rfl

/-- **The density-weighted inverse-Gram pairing as a `principalIntegrand`.** For
`y` in the compact chart-interior set `K ⊆ chartTargetEuclid α`, the
density-weighted contraction of the chart inverse Gram `chartInvGramEuclid g α`
against the chart-Euclidean partial derivatives of `u` and `φ` equals the
`principalIntegrand` of the principal-part elliptic bilinear form
`tensorPrincipalForm g α hK hK_target`. -/
theorem weightedInvGram_principalIntegrand_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (u φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))} (hy : y ∈ K) :
    densityOnEuclid (I := I) g α y *
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
              euclidPartial (E := E) k u y *
              euclidPartial (E := E) l φ y) =
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
        u φ y := by
  classical
  -- Unfold the form's `principalIntegrand` and pull the density factor inside.
  rw [SmoothEllipticBilinearForm.principalIntegrand, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  -- On `K` the form's coefficient is the volume-weighted inverse Gram entry.
  rw [tensorPrincipalForm_a_eq_weightedInvGramEuclid
    (I := I) (M := M) g α hK hK_target hy k l]
  -- Factorise the weighted inverse Gram entry and match the partial-derivative
  -- conventions (`euclidPartial · = fderiv · (single · 1)`).
  rw [weightedInvGramEuclid_eq_density_mul_invGram (I := I) (M := M) g α k l y,
    euclidPartial_def, euclidPartial_def]
  ring

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
