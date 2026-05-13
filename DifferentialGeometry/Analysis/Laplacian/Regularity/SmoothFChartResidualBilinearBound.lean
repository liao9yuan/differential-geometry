import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChartBilinearH1ComplResidualUnconditional
import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInnerCLMChartFormula
import DifferentialGeometry.Analysis.Sobolev.Chart.StrictCutoffPushedRawBound
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothMulQuant
import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifoldHigherOrder
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MultiplyQuantK

/-!
# Chart-target bilinear bound for the smooth Leibniz residual

For a closed Riemannian manifold `(M, g)` and a chart-atlas index `α : M`, the
smooth chart-pulled Leibniz residual

```
smoothFChartResidual g α v y =
  chartPushedRaw α (-2 g(∇ρα, ∇v) - Δρα · v.toFun) y
```

(see `DiffChartBilinearH1ComplResidualMemW1p.lean` for the manifold-side
representative) satisfies a quantitative `W^{1,2}` bound on `chartTargetEuclid α`
in terms of the chart-based `W^{2,2}` norm of `v.toFun`. Precisely, there is a
positive constant `C = C(g, α)` such that for every smooth scalar
`v : SmoothScalar g`,

```
wkpNorm 1 2 (smoothFChartResidual g α v) chartTargetEuclid α
  ≤ C · wkpNormChart g 2 2 v.toFun.
```

## Strategy

The proof inserts the smooth strict cutoff `η_α := chartStrictCutoff α` from
`Chart/StrictCutoff.lean`, which equals `1` on `tsupport ρ_α` and has tsupport
contained in `(chartAt H α).source`. Setting `H := η_α · v.toFun`, the
manifold-side residual representative satisfies pointwise on `M`:

```
fHLeibnizResidualSmoothRep g α v
  = -2 g(∇ρα, ∇H) - Δρα · H.
```

This holds because `∇ρα` and `Δρα` are concentrated on `tsupport ρ_α`, where
`η_α ≡ 1` and `∇η_α = 0`.

After pushing forward to `EuclN` via `chartPushedRaw α`, the chart formula for
the smooth gradient inner product (from `GradInnerCLMChartFormula.lean`) gives

```
chartPushedRaw α (g(∇ρα, ∇H)) y =
  ∑_{ij} G⁻¹_{ij}(y) · ∂_i ρ̃α(y) · ∂_j (chartPushedRaw α H)(y)
```

on `chartTargetEuclid α`. The smooth coefficient
`y ↦ G⁻¹_{ij}(y) · ∂_i ρ̃α(y)` is realized as `smoothExtensionScalar α (B_α_ij)`
for a manifold-side smooth function `B_α_ij` whose tsupport is contained in
`(chartAt H α).source`. Hence it has uniformly bounded iterated derivatives on
`chartTargetEuclid α`, and the Euclidean quantitative Leibniz bound
`wkpNorm_smul_smooth_bounded_le` controls its `W^{1,2}` product with
`∂_j (chartPushedRaw α H)`, which lies in `W^{1,2}` because
`chartPushedRaw α H` lies in `W^{2,2}` (by `T1.2`).

The second piece `chartPushedRaw α (Δρα · H)` similarly reduces to a
smooth-coefficient product with `chartPushedRaw α H ∈ W^{1,2}`.

## Main result

* `wkpNorm_smoothFChartResidual_le_wkpNormChart` — the headline bilinear
  bound.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace SmoothFChartResidualBilinearBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidualUnconditional
open DifferentialGeometry.Analysis.Laplacian.GradInnerCLMChartFormula
open DifferentialGeometry.Analysis.Sobolev.Chart

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## The smooth strict cutoff lifted to a `SmoothScalar` multiplier

For `v : SmoothScalar g`, define `etaTimesV α v : M → ℝ` as
`chartStrictCutoff α · v.toFun`. This is the smooth replacement of `v.toFun`
that equals `v.toFun` on `tsupport ρ_α` and has tsupport in
`(chartAt H α).source`. -/

/-- The pointwise product `chartStrictCutoff α · v.toFun` as a function on
`M`. -/
private noncomputable def etaTimesV (α : M) (v : M → ℝ) : M → ℝ :=
  fun x => chartStrictCutoff (I := I) (M := M) α x * v x

private lemma etaTimesV_apply (α : M) (v : M → ℝ) (x : M) :
    etaTimesV (I := I) (M := M) α v x =
      chartStrictCutoff (I := I) (M := M) α x * v x := rfl

private lemma etaTimesV_smooth (α : M) {v : M → ℝ}
    (hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (etaTimesV (I := I) (M := M) α v) := by
  unfold etaTimesV
  exact (chartStrictCutoff_contMDiff (I := I) (M := M) α).mul hv

/-- Package `etaTimesV α v.toFun` as a `SmoothScalar g`. -/
private noncomputable def etaTimesVScalar
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    SmoothScalar g where
  toFun := etaTimesV (I := I) (M := M) α v.toFun
  smooth := etaTimesV_smooth (I := I) (M := M) α v.smooth

@[simp] private lemma etaTimesVScalar_toFun (g : SmoothRiemannianMetric I M)
    (α : M) (v : SmoothScalar g) :
    (etaTimesVScalar (I := I) (M := M) g α v).toFun =
      etaTimesV (I := I) (M := M) α v.toFun := rfl

/-- The tsupport of `etaTimesV α v` is contained in `tsupport (chartStrictCutoff α)`,
which is contained in `(chartAt H α).source`. -/
private lemma tsupport_etaTimesV_subset (α : M) (v : M → ℝ) :
    tsupport (etaTimesV (I := I) (M := M) α v) ⊆ (chartAt H α).source := by
  have h_supp_subset : Function.support (etaTimesV (I := I) (M := M) α v) ⊆
      Function.support (chartStrictCutoff (I := I) (M := M) α) := by
    intro x hx
    by_contra hxnot
    apply hx
    change chartStrictCutoff (I := I) (M := M) α x * v x = 0
    have h0 : chartStrictCutoff (I := I) (M := M) α x = 0 := by
      simpa [Function.mem_support, not_not] using hxnot
    rw [h0]; ring
  have h_tsupp_subset : tsupport (etaTimesV (I := I) (M := M) α v) ⊆
      tsupport (chartStrictCutoff (I := I) (M := M) α) :=
    closure_minimal (h_supp_subset.trans (subset_tsupport _))
      (isClosed_tsupport _)
  exact h_tsupp_subset.trans (chartStrictCutoff_tsupport_subset (I := I) (M := M) α)

/-! ## File-local manifold-side smooth representative of the Leibniz residual

We redefine the smooth manifold representative `smoothRep g α v : M → ℝ` of
`fHLeibnizResidualLp g α (smoothToH1Compl v)` locally, since the original
in `DiffChartBilinearH1ComplResidualMemW1p.lean` is `private`. This is the
function `-2 g(∇ρα, ∇v) - Δρα · v` on `M`. -/

/-- The smooth manifold representative of `fHLeibnizResidualLp g α
(smoothToH1Compl v)`: the explicit pointwise function `-2 g(∇ρα, ∇v) - Δρα · v`. -/
private noncomputable def smoothRep
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) : M → ℝ :=
  fun x : M =>
    -((2 : ℝ) * g.inner x (gradFun (I := I) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)
      (gradFun (I := I) g v.toFun x)) -
    (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x * v.toFun x

private lemma smoothRep_apply (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) (x : M) :
    smoothRep (I := I) (M := M) g α v x =
      -((2 : ℝ) * g.inner x (gradFun (I := I) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)
        (gradFun (I := I) g v.toFun x)) -
      (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x * v.toFun x := rfl

/-! ## The η_α replacement identity on the manifold

The crucial pointwise identity: on `M`, the smooth Leibniz residual
representative `smoothRep g α v` equals the same expression
with `v.toFun` replaced by `chartStrictCutoff α · v.toFun`. -/

/-- For any `x : M`, if `x ∉ tsupport (chartAtlasPOU I M α)`, then
`smoothRep g α v x = 0`. -/
private lemma smoothRep_eq_zero_off_tsupport_chartAtlasPOU
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) {x : M}
    (hx : x ∉ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    smoothRep (I := I) (M := M) g α v x = 0 := by
  classical
  -- Local zero argument: on a neighborhood of x, ρα ≡ 0, so ∇ρα = 0 and Δρα = 0.
  have h_open : IsOpen
      (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))ᶜ :=
    (isClosed_tsupport _).isOpen_compl
  have h_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 x]
      (fun _ : M => (0 : ℝ)) := by
    filter_upwards [h_open.mem_nhds hx] with y hy
    by_contra hne
    exact hy (subset_tsupport _ hne)
  have h_grad_zero : gradFun (I := I) g
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
    gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_ev
  have h_lap_zero : (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x = 0 := by
    rw [laplacianOfChartPOU_apply]
    rw [Δ_g_def]
    have h_grad_ev : ∀ᶠ y in 𝓝 x,
        (DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y =
        (0 : TangentSpace I y) := by
      filter_upwards [h_open.mem_nhds hx] with y hy
      have h_y_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 y]
          (fun _ : M => (0 : ℝ)) := by
        filter_upwards [h_open.mem_nhds hy] with z hz
        by_contra hne
        exact hz (subset_tsupport _ hne)
      have h_g := gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_y_ev
      rw [DifferentialGeometry.Integral.DivergenceTheorem.grad_g_apply]
      exact h_g
    exact DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_zero_of_eventuallyEq_zero
      (I := I) g _ h_grad_ev
  -- Substitute into the formula.
  rw [smoothRep_apply, h_grad_zero, h_lap_zero]
  simp

/-- Identity: `gradFun g v` and `gradFun g (η_α · v)` agree at any point `x`
where `chartStrictCutoff α ≡ 1` in a neighborhood. -/
private lemma gradFun_eq_gradFun_etaTimesV_of_eventuallyOne
    (g : SmoothRiemannianMetric I M) (α : M) {v : M → ℝ} {x : M}
    (h_one : chartStrictCutoff (I := I) (M := M) α =ᶠ[𝓝 x]
      (fun _ : M => (1 : ℝ))) :
    gradFun (I := I) g (etaTimesV (I := I) (M := M) α v) x =
      gradFun (I := I) g v x := by
  -- On the neighborhood, etaTimesV α v ≡ 1 · v = v.
  have h_eq : etaTimesV (I := I) (M := M) α v =ᶠ[𝓝 x] v := by
    filter_upwards [h_one] with y hy
    change chartStrictCutoff (I := I) (M := M) α y * v y = v y
    rw [hy]; ring
  -- mfderiv depends only on the local function near x.
  have h_mfderiv : mfderiv I 𝓘(ℝ, ℝ) (etaTimesV (I := I) (M := M) α v) x =
      mfderiv I 𝓘(ℝ, ℝ) v x := Filter.EventuallyEq.mfderiv_eq h_eq
  unfold gradFun
  rw [h_mfderiv]

/-- The Laplacian replacement identity for the second piece: when
`chartStrictCutoff α ≡ 1` in a neighborhood of `x`, then `etaTimesV α v x = v x`. -/
private lemma etaTimesV_eq_of_eventuallyOne
    (α : M) {v : M → ℝ} {x : M}
    (h_one : chartStrictCutoff (I := I) (M := M) α =ᶠ[𝓝 x]
      (fun _ : M => (1 : ℝ))) :
    etaTimesV (I := I) (M := M) α v x = v x := by
  have h_self : chartStrictCutoff (I := I) (M := M) α x = 1 := h_one.self_of_nhds
  change chartStrictCutoff (I := I) (M := M) α x * v x = v x
  rw [h_self]; ring

/-- The η_α replacement identity on `M`: pointwise,
`smoothRep g α v = -2 g(∇ρα, ∇(η_α · v)) - Δρα · (η_α · v)`. -/
private lemma smoothRep_eq_etaTimesV
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) (x : M) :
    smoothRep (I := I) (M := M) g α v x =
    -((2 : ℝ) * g.inner x
        (gradFun (I := I) g
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
        (gradFun (I := I) g
          (etaTimesV (I := I) (M := M) α v.toFun) x)) -
    (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x *
      etaTimesV (I := I) (M := M) α v.toFun x := by
  classical
  by_cases hx_supp : x ∈ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  · -- Inside the support of POU: η_α ≡ 1 on an open neighborhood.
    have h_one : chartStrictCutoff (I := I) (M := M) α =ᶠ[𝓝 x]
        (fun _ : M => (1 : ℝ)) :=
      (chartStrictCutoff_eventually_one_nhdsSet_tsupport_chartAtlasPOU
        (I := I) (M := M) α).filter_mono (nhds_le_nhdsSet hx_supp)
    have h_grad := gradFun_eq_gradFun_etaTimesV_of_eventuallyOne
      (I := I) (M := M) g α h_one (v := v.toFun)
    have h_eta_v : etaTimesV (I := I) (M := M) α v.toFun x = v.toFun x :=
      etaTimesV_eq_of_eventuallyOne (I := I) (M := M) α h_one
    rw [smoothRep_apply, ← h_grad, ← h_eta_v]
  · -- Outside the support of POU: both sides are 0.
    have hLHS : smoothRep (I := I) (M := M) g α v x = 0 :=
      smoothRep_eq_zero_off_tsupport_chartAtlasPOU
        (I := I) (M := M) g α v hx_supp
    rw [hLHS]
    -- RHS: gradFun ρα x = 0 and Δρα x = 0.
    have h_open : IsOpen
        (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have h_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 x]
        (fun _ : M => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hx_supp] with y hy
      by_contra hne
      exact hy (subset_tsupport _ hne)
    have h_grad_zero : gradFun (I := I) g
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
      gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_ev
    have h_lap_zero : (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x = 0 := by
      rw [laplacianOfChartPOU_apply, Δ_g_def]
      have h_grad_ev : ∀ᶠ y in 𝓝 x,
          (DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y =
          (0 : TangentSpace I y) := by
        filter_upwards [h_open.mem_nhds hx_supp] with y hy
        have h_y_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 y]
            (fun _ : M => (0 : ℝ)) := by
          filter_upwards [h_open.mem_nhds hy] with z hz
          by_contra hne
          exact hz (subset_tsupport _ hne)
        rw [DifferentialGeometry.Integral.DivergenceTheorem.grad_g_apply]
        exact gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_y_ev
      exact DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_zero_of_eventuallyEq_zero
        (I := I) g _ h_grad_ev
    rw [h_grad_zero, h_lap_zero]
    simp

/-! ## Function-level identity on `M`

The functional identity `fHLeibnizResidualSmoothRep g α v = F_grad - F_lap` on
`M`, where
* `F_grad x := 2 g(∇ρα x, ∇(η_α · v) x)`,
* `F_lap x := Δρα x · (η_α · v) x`,
both with tsupport in `(chartAt H α).source`. -/

/-- The gradient-inner-product piece `2 g(∇ρα, ∇(η_α · v))` as a function on `M`. -/
private noncomputable def gradInnerPiece
    (g : SmoothRiemannianMetric I M) (α : M) (v : M → ℝ) : M → ℝ :=
  fun x => (2 : ℝ) * g.inner x
      (gradFun (I := I) g ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
      (gradFun (I := I) g (etaTimesV (I := I) (M := M) α v) x)

private lemma gradInnerPiece_apply (g : SmoothRiemannianMetric I M) (α : M)
    (v : M → ℝ) (x : M) :
    gradInnerPiece (I := I) (M := M) g α v x =
      (2 : ℝ) * g.inner x
        (gradFun (I := I) g ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
        (gradFun (I := I) g (etaTimesV (I := I) (M := M) α v) x) := rfl

/-- The Laplacian-product piece `Δρα · (η_α · v)` as a function on `M`. -/
private noncomputable def lapPiece
    (g : SmoothRiemannianMetric I M) (α : M) (v : M → ℝ) : M → ℝ :=
  fun x => (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x *
    etaTimesV (I := I) (M := M) α v x

private lemma lapPiece_apply (g : SmoothRiemannianMetric I M) (α : M)
    (v : M → ℝ) (x : M) :
    lapPiece (I := I) (M := M) g α v x =
      (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x *
        etaTimesV (I := I) (M := M) α v x := rfl

/-- The functional identity: `smoothRep g α v = -gradInnerPiece - lapPiece`. -/
private lemma smoothRep_eq_pieces
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    smoothRep (I := I) (M := M) g α v =
      fun x => -gradInnerPiece (I := I) (M := M) g α v.toFun x -
        lapPiece (I := I) (M := M) g α v.toFun x := by
  funext x
  rw [smoothRep_eq_etaTimesV (I := I) (M := M) g α v x]
  rfl

/-! ## Smoothness and support of the two pieces -/

private lemma gradInnerPiece_smooth (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (gradInnerPiece (I := I) (M := M) g α v.toFun) := by
  unfold gradInnerPiece
  -- Two parts of the product: 2 ∈ C^∞, and g.inner of two smooth tangent sections.
  have hα_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  have hetaV_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (etaTimesV (I := I) (M := M) α v.toFun) :=
    etaTimesV_smooth (I := I) (M := M) α v.smooth
  have h_inner : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g.inner x
        (gradFun (I := I) g
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
        (gradFun (I := I) g
          (etaTimesV (I := I) (M := M) α v.toFun) x)) := by
    have h := DifferentialGeometry.Integral.DivergenceTheorem.contMDiff_g_inner_of_smooth_sections
      (I := I) (M := M) g
      (DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hα_smooth)
      (DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hetaV_smooth)
    refine h.congr (fun x => ?_)
    rw [DifferentialGeometry.Integral.DivergenceTheorem.grad_g_apply,
        DifferentialGeometry.Integral.DivergenceTheorem.grad_g_apply]
  exact (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (2 : ℝ))).mul h_inner

private lemma lapPiece_smooth (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (lapPiece (I := I) (M := M) g α v.toFun) := by
  unfold lapPiece
  exact (laplacianOfChartPOU (I := I) (M := M) g α).contMDiff.mul
    (etaTimesV_smooth (I := I) (M := M) α v.smooth)

/-- The tsupport of `gradInnerPiece` is contained in `tsupport (chartAtlasPOU I M α)`
(hence in `(chartAt H α).source`). -/
private lemma tsupport_gradInnerPiece_subset
    (g : SmoothRiemannianMetric I M) (α : M) (v : M → ℝ) :
    tsupport (gradInnerPiece (I := I) (M := M) g α v) ⊆
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  classical
  have h_supp_subset : Function.support (gradInnerPiece (I := I) (M := M) g α v) ⊆
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
    intro x hx
    by_contra hxoff
    apply hx
    -- x ∉ tsupport ρα: gradFun ρα x = 0.
    have h_open : IsOpen
        (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have h_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 x]
        (fun _ : M => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hxoff] with y hy
      by_contra hne
      exact hy (subset_tsupport _ hne)
    have h_grad_zero : gradFun (I := I) g
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
      gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_ev
    change gradInnerPiece (I := I) (M := M) g α v x = 0
    rw [gradInnerPiece_apply, h_grad_zero]
    simp
  exact closure_minimal h_supp_subset (isClosed_tsupport _)

private lemma tsupport_gradInnerPiece_subset_source
    (g : SmoothRiemannianMetric I M) (α : M) (v : M → ℝ) :
    tsupport (gradInnerPiece (I := I) (M := M) g α v) ⊆ (chartAt H α).source :=
  (tsupport_gradInnerPiece_subset (I := I) (M := M) g α v).trans
    (chartAtlasPOU_isSubordinate I M α)

private lemma tsupport_lapPiece_subset
    (g : SmoothRiemannianMetric I M) (α : M) (v : M → ℝ) :
    tsupport (lapPiece (I := I) (M := M) g α v) ⊆
      tsupport (etaTimesV (I := I) (M := M) α v) := by
  classical
  have h_supp_subset : Function.support (lapPiece (I := I) (M := M) g α v) ⊆
      Function.support (etaTimesV (I := I) (M := M) α v) := by
    intro x hx
    by_contra hxoff
    apply hx
    have h0 : etaTimesV (I := I) (M := M) α v x = 0 := by
      simpa [Function.mem_support, not_not] using hxoff
    change lapPiece (I := I) (M := M) g α v x = 0
    rw [lapPiece_apply, h0]; ring
  exact closure_minimal (h_supp_subset.trans (subset_tsupport _))
    (isClosed_tsupport _)

private lemma tsupport_lapPiece_subset_source
    (g : SmoothRiemannianMetric I M) (α : M) (v : M → ℝ) :
    tsupport (lapPiece (I := I) (M := M) g α v) ⊆ (chartAt H α).source :=
  (tsupport_lapPiece_subset (I := I) (M := M) g α v).trans
    (tsupport_etaTimesV_subset (I := I) (M := M) α v)

/-! ## Chart formula on `chartTargetEuclid α` for the gradient piece

For smooth `v : SmoothScalar g`, the chart-pushed-raw `gradInnerPiece g α v.toFun`
agrees on `chartTargetEuclid α` with `2 · chartFormulaRhsSmooth g α ρα (etaTimesV α v.toFun)`,
which is the smooth chart-coordinate sum
`Σ_{ij} G⁻¹_{ij}(y) · ∂_i ρ̃α(y) · ∂_j (η̃·v)(y) · 2`. -/

/-- Pointwise on `chartTargetEuclid α`, the chart-pushed-raw `gradInnerPiece` is
twice the chart formula RHS evaluated at `(ρα, etaTimesV α v.toFun)`. -/
private lemma chartPushedRaw_gradInnerPiece_eq_rhs
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun) y =
      (2 : ℝ) * chartFormulaRhsSmooth (I := I) (M := M) g α
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        (etaTimesVScalar (I := I) (M := M) g α v).toFun y := by
  classical
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (gradInnerPiece (I := I) (M := M) g α v.toFun) hy]
  rw [gradInnerPiece_apply]
  rw [etaTimesVScalar_toFun]
  -- Convert the inner expression to chartFormulaRhsSmooth (which equals the
  -- chart-formula sum) using the chart formula.
  have h_inner_eq :
      g.inner ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (gradFun (I := I) g
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (gradFun (I := I) g
          (etaTimesV (I := I) (M := M) α v.toFun)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      chartFormulaRhsSmooth (I := I) (M := M) g α
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        (etaTimesV (I := I) (M := M) α v.toFun) y := by
    have := DifferentialGeometry.Analysis.Laplacian.GradInnerCLMChartFormula.chartPushedRaw_gradInnerSmooth_pointwise
      (I := I) (M := M) g α (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
      (etaTimesVScalar (I := I) (M := M) g α v) hy
    simpa using this
  rw [h_inner_eq]

/-! ## Chart-pushed-raw factorisation of `lapPiece`

The chart-pushed-raw `lapPiece` factors as
`smoothExtensionScalar α (b · Δρα)(y) · chartPushedRaw α (η · v)(y)`
on `chartTargetEuclid α`, where `b` is the manifold-side chart cutoff equal to
`1` on `tsupport ρ_α`. This factorisation expresses the chart-pushed-raw
product as a smooth-coefficient times the chart-pushed-raw of `η · v`. -/

/-- The chart-pushed-raw `lapPiece` agrees on `chartTargetEuclid α` with the
product of `smoothExtensionScalar α (b · Δρα)` and `chartPushedRaw α (η · v)`,
where `b` is any chart-cutoff equal to `1` on `tsupport ρ_α`. -/
private lemma chartPushedRaw_lapPiece_factor
    (g : SmoothRiemannianMetric I M) (α : M) (v : M → ℝ)
    {b : M → ℝ}
    (hb_one : ∀ x ∈ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
      b x = 1)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
        (lapPiece (I := I) (M := M) g α v) y =
      smoothExtensionScalar (I := I) (M := M) α
          (fun x => b x *
            (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x) y *
        chartPushedRaw (I := I) (M := M) α
          (etaTimesV (I := I) (M := M) α v) y := by
  classical
  -- LHS at y on chartTarget: lapPiece(symm(y)).
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have hLHS : chartPushedRaw (I := I) (M := M) α
      (lapPiece (I := I) (M := M) g α v) y =
      lapPiece (I := I) (M := M) g α v x := by
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (lapPiece (I := I) (M := M) g α v) hy]
  -- RHS factors:
  have hRHS_smooth : smoothExtensionScalar (I := I) (M := M) α
      (fun x => b x * (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x) y =
      b x * (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x := by
    have h_tgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy; exact hy
    classical
    change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
        b ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      else 0) = b x * (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x
    rw [if_pos h_tgt]
  have hRHS_etav : chartPushedRaw (I := I) (M := M) α
      (etaTimesV (I := I) (M := M) α v) y =
      etaTimesV (I := I) (M := M) α v x := by
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (etaTimesV (I := I) (M := M) α v) hy]
  rw [hLHS, hRHS_smooth, hRHS_etav]
  -- Goal:
  --   Δρα x · (η x · v x) = (b x · Δρα x) · (η x · v x).
  -- True when b x · Δρα x = Δρα x, i.e. when either Δρα x = 0 or b x = 1.
  -- If Δρα x ≠ 0, then x ∈ support(Δρα). We don't directly have support
  -- (Δρα) ⊆ tsupport(ρα), so we reduce via tsupport-of-Δρα analysis.
  by_cases h_lap_zero : (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x = 0
  · -- Δρα x = 0 → both sides are zero.
    rw [lapPiece_apply, h_lap_zero]; ring
  · -- Δρα x ≠ 0 → x ∈ tsupport(Δρα). We have tsupport(Δρα) ⊆ tsupport(ρα),
    -- so x ∈ tsupport(ρα), hence b x = 1.
    have h_supp_Δρα : Function.support
        ((laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ)) ⊆
        tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      intro z hz
      by_contra hz_off
      apply hz
      have h_open : IsOpen
          (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      have h_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 z]
          (fun _ : M => (0 : ℝ)) := by
        filter_upwards [h_open.mem_nhds hz_off] with w hw
        by_contra hne
        exact hw (subset_tsupport _ hne)
      rw [laplacianOfChartPOU_apply, Δ_g_def]
      have h_grad_ev : ∀ᶠ w in 𝓝 z,
          (DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) w =
          (0 : TangentSpace I w) := by
        filter_upwards [h_open.mem_nhds hz_off] with w hw
        have h_w_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 w]
            (fun _ : M => (0 : ℝ)) := by
          filter_upwards [h_open.mem_nhds hw] with u hu
          by_contra hne
          exact hu (subset_tsupport _ hne)
        rw [DifferentialGeometry.Integral.DivergenceTheorem.grad_g_apply]
        exact gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_w_ev
      exact DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_zero_of_eventuallyEq_zero
        (I := I) g _ h_grad_ev
    have hx_supp : x ∈ Function.support
        ((laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ)) := h_lap_zero
    have hx_tsupp : x ∈ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      h_supp_Δρα hx_supp
    have h_bx : b x = 1 := hb_one x hx_tsupp
    rw [lapPiece_apply, h_bx]
    ring

/-! ## Manifold-side smooth coefficient for the `(i, j)`-th chart formula term

For each `(i, j)`, define `coefIJ_M g α i j : M → ℝ` as the manifold-side smooth
function that pulls back to `G⁻¹_{ij}(y) · ∂_i ρ̃α(y)` (times the cutoff) on
`chartTargetEuclid α`. -/

/-- The manifold-side coefficient `(chartStrictCutoff α · chartInvGramMatrix g α · ∂_i ρ̃α)`
for the `(i, j)`-th chart formula term. -/
private noncomputable def coefIJ_M
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun x : M =>
    chartStrictCutoff (I := I) (M := M) α x *
      chartInvGramMatrix (I := I) g α x i j *
      partialDeriv (E := E) i
        (scalarOnE (I := I) α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
        (extChartAt I α x)

private lemma coefIJ_M_apply (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    coefIJ_M (I := I) (M := M) g α i j x =
      chartStrictCutoff (I := I) (M := M) α x *
        chartInvGramMatrix (I := I) g α x i j *
        partialDeriv (E := E) i
          (scalarOnE (I := I) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
          (extChartAt I α x) := rfl

/-- Support of `coefIJ_M` is contained in tsupport(chartStrictCutoff α). -/
private lemma coefIJ_M_eq_zero_off_tsupport_chartStrictCutoff
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : chartStrictCutoff (I := I) (M := M) α x = 0) :
    coefIJ_M (I := I) (M := M) g α i j x = 0 := by
  unfold coefIJ_M
  rw [hx]
  ring

/-- `coefIJ_M g α i j` is smooth on M. -/
private lemma coefIJ_M_smooth
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (coefIJ_M (I := I) (M := M) g α i j) := by
  classical
  -- Strategy: smoothness at every point.
  intro x₀
  by_cases hx_src : x₀ ∈ (chartAt H α).source
  · -- On chart α source, all factors are smooth.
    have h_chart_src_open : IsOpen ((chartAt H α).source) :=
      (chartAt H α).open_source
    -- chartStrictCutoff α is smooth globally.
    have h_cut_smooth : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (chartStrictCutoff (I := I) (M := M) α) x₀ :=
      (chartStrictCutoff_contMDiff (I := I) (M := M) α).contMDiffAt
    -- chartInvGramMatrix g α (·) i j is ContMDiffOn on chart base set = chart α source.
    have hbase : x₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx_src
    have h_invGram_on : ContMDiffOn I 𝓘(ℝ) ∞
        (fun x : M => chartInvGramMatrix (I := I) g α x i j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
    have h_base_open : IsOpen ((trivializationAt E (TangentSpace I) α).baseSet) := by
      rw [trivializationAt_baseSet_eq_chartAt_source]; exact h_chart_src_open
    have h_invGram_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => chartInvGramMatrix (I := I) g α x i j) x₀ := by
      have h := (h_invGram_on x₀ hbase).contMDiffAt
        (h_base_open.mem_nhds hbase)
      exact h
    -- The partialDeriv factor on chart source.
    -- partialDeriv i (scalarOnE α ρα) (extChartAt I α x):
    -- scalarOnE α ρα = ρα ∘ symm is ContDiffOn ∞ on (extChartAt I α).target.
    -- Hence its fderiv is ContDiffOn ∞ on the open target.
    -- Composed with extChartAt I α (smooth on source), we get smoothness on source.
    have hα_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
    have h_scalarOnE_contDiffOn : ContDiffOn ℝ ∞
        (scalarOnE (I := I) α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
        (extChartAt I α).target :=
      DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
        (I := I) α hα_smooth
    -- The partial deriv of scalarOnE α ρα is ContDiffOn ∞ on the open target.
    have h_target_open : IsOpen ((extChartAt I α).target) :=
      isOpen_extChartAt_target (I := I) α
    have h_partial_contDiffOn : ContDiffOn ℝ ∞
        (fun y : E => partialDeriv (E := E) i
          (scalarOnE (I := I) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y)
        (extChartAt I α).target := by
      unfold partialDeriv
      have h_fderiv_smooth :
          ContDiffOn ℝ ∞ (fun y : E => fderiv ℝ
            (scalarOnE (I := I) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y)
            (extChartAt I α).target := by
        have h_le : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
          rw [show ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = ((⊤ : ℕ∞) : WithTop ℕ∞) from by simp]
        exact h_scalarOnE_contDiffOn.fderiv_of_isOpen h_target_open h_le
      exact h_fderiv_smooth.clm_apply contDiffOn_const
    -- The composition with extChartAt I α (smooth on source mapping to target).
    have hx_target : extChartAt I α x₀ ∈ (extChartAt I α).target := by
      have hx_ext_src : x₀ ∈ (extChartAt I α).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_src
      exact (extChartAt I α).map_source hx_ext_src
    have h_partial_at_E : ContDiffAt ℝ ∞
        (fun y : E => partialDeriv (E := E) i
          (scalarOnE (I := I) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y)
        (extChartAt I α x₀) := by
      have h_within := h_partial_contDiffOn (extChartAt I α x₀) hx_target
      exact h_within.contDiffAt (h_target_open.mem_nhds hx_target)
    -- Compose with extChartAt I α (smooth at x₀ on chart source).
    have h_extChart_contMDiff : ContMDiffAt I 𝓘(ℝ, E) ∞
        (extChartAt I α) x₀ := by
      have h_open_src : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
      have h_on : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
        contMDiffOn_extChartAt (I := I) (x := α)
      exact (h_on x₀ hx_src).contMDiffAt (h_open_src.mem_nhds hx_src)
    have h_partial_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => partialDeriv (E := E) i
          (scalarOnE (I := I) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
          (extChartAt I α x)) x₀ := by
      have h_partial_at_E_mDiff : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
          (fun y : E => partialDeriv (E := E) i
            (scalarOnE (I := I) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y)
          (extChartAt I α x₀) :=
        (contMDiffAt_iff_contDiffAt).mpr h_partial_at_E
      exact h_partial_at_E_mDiff.comp _ h_extChart_contMDiff
    unfold coefIJ_M
    exact (h_cut_smooth.mul h_invGram_at).mul h_partial_at
  · -- Outside chart α source: use that chartStrictCutoff α ≡ 0 in a neighborhood,
    -- hence coefIJ_M ≡ 0 in a neighborhood, hence smooth.
    have hx_compl : x₀ ∈ ((chartAt H α).source)ᶜ := hx_src
    have h_ev_zero : ∀ᶠ x in 𝓝 x₀,
        chartStrictCutoff (I := I) (M := M) α x = 0 := by
      have h_ev_nhdsSet :=
        chartStrictCutoff_eventually_zero_nhdsSet_compl_source (I := I) (M := M) α
      exact h_ev_nhdsSet.filter_mono (nhds_le_nhdsSet hx_compl)
    have h_ev_zero_coef : ∀ᶠ x in 𝓝 x₀,
        coefIJ_M (I := I) (M := M) g α i j x = 0 := by
      filter_upwards [h_ev_zero] with x hx
      exact coefIJ_M_eq_zero_off_tsupport_chartStrictCutoff (I := I) (M := M)
        g α i j hx
    -- coefIJ_M ≡ 0 in a neighborhood of x₀ → ContMDiffAt.
    -- The function coefIJ_M is locally 0, so by congr_of_eventuallyEq from
    -- the constant 0, it is smooth at x₀.
    have h_const : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ)) x₀ :=
      contMDiffAt_const
    have h_evEq : coefIJ_M (I := I) (M := M) g α i j =ᶠ[𝓝 x₀]
        (fun _ : M => (0 : ℝ)) := h_ev_zero_coef
    exact h_const.congr_of_eventuallyEq h_evEq

/-- `tsupport (coefIJ_M g α i j) ⊆ (chartAt H α).source`. -/
private lemma tsupport_coefIJ_M_subset
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    tsupport (coefIJ_M (I := I) (M := M) g α i j) ⊆ (chartAt H α).source := by
  classical
  have h_supp_subset : Function.support (coefIJ_M (I := I) (M := M) g α i j) ⊆
      Function.support (chartStrictCutoff (I := I) (M := M) α) := by
    intro x hx
    by_contra hxoff
    apply hx
    have h0 : chartStrictCutoff (I := I) (M := M) α x = 0 := by
      simpa [Function.mem_support, not_not] using hxoff
    exact coefIJ_M_eq_zero_off_tsupport_chartStrictCutoff (I := I) (M := M)
      g α i j h0
  have h_tsupp_subset : tsupport (coefIJ_M (I := I) (M := M) g α i j) ⊆
      tsupport (chartStrictCutoff (I := I) (M := M) α) :=
    closure_minimal (h_supp_subset.trans (subset_tsupport _))
      (isClosed_tsupport _)
  exact h_tsupp_subset.trans (chartStrictCutoff_tsupport_subset (I := I) (M := M) α)

/-- Identification of `chartPushedRaw α (coefIJ_M g α i j)` with the chart-formula
coefficient on `chartTargetEuclid α`. -/
private lemma chartPushedRaw_coefIJ_M_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
        (coefIJ_M (I := I) (M := M) g α i j) y =
      chartStrictCutoff (I := I) (M := M) α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        invGramOnEuclid (I := I) g α i j y *
        partialDerivOnEuclid (I := I) (M := M) α i
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y := by
  classical
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (coefIJ_M (I := I) (M := M) g α i j) hy]
  unfold coefIJ_M
  -- Note: partialDeriv (E := E) i (scalarOnE α ρα) (extChartAt I α x_y) =
  --       partialDeriv (E := E) i (scalarOnE α ρα) ((toEuclidean.symm y))
  -- because x_y := (extChartAt I α).symm ((toEuclidean.symm y))
  -- and `extChartAt I α (extChartAt I α).symm y' = y'` on target.
  have h_tgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy; exact hy
  have h_φx_eq : extChartAt I α ((extChartAt I α).symm
        ((toEuclidean (E := E)).symm y)) =
      (toEuclidean (E := E)).symm y :=
    (extChartAt I α).right_inv h_tgt
  rw [h_φx_eq]
  -- Now identify partialDeriv with partialDerivOnEuclid.
  unfold partialDerivOnEuclid invGramOnEuclid
  rfl

/-! ## Bound for the `lapPiece` chart-pushed-raw `W^{1,2}` norm

For `v : SmoothScalar g`, we show there exists `C_lap = C_lap(g, α)` such that
```
wkpNorm 1 2 (chartPushedRaw α (lapPiece g α v.toFun)) chartTargetEuclid α
  ≤ ENNReal.ofReal C_lap *
    wkpNorm 1 2 (chartPushedRaw α (etaTimesV α v.toFun)) chartTargetEuclid α.
```

Strategy:
1. The pointwise factorisation
   `chartPushedRaw α lapPiece = smoothExt α (b · Δρα) · chartPushedRaw α (η · v)`
   on `chartTargetEuclid α`.
2. The smooth Euclidean extension has uniformly bounded iterated derivatives,
   so the Euclidean quantitative Leibniz bound applies. -/

private lemma wkpNorm_chartPushedRaw_lapPiece_le_etaTimesV_aux
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 2
          (chartPushedRaw (I := I) (M := M) α
            (etaTimesV (I := I) (M := M) α v.toFun))
          (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- Obtain the chart cutoff b_α.
  obtain ⟨b, hb_smooth, _, hb_one_on_tsupp, hb_supp⟩ :=
    exists_chart_cutoff_M (I := I) (M := M) α
  -- Define Λ := smoothExt α (b · Δρα).
  set bΔρα : M → ℝ := fun x : M =>
    b x * (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x with hbΔρα_def
  have hbΔρα_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ bΔρα :=
    hb_smooth.mul (laplacianOfChartPOU (I := I) (M := M) g α).contMDiff
  have hbΔρα_supp : tsupport bΔρα ⊆ (chartAt H α).source := by
    have h_eq : bΔρα = (fun x : M => b x •
      (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x) := by
      funext x; rfl
    rw [h_eq]
    exact (tsupport_smul_subset_left (f := b)
      (g := ((laplacianOfChartPOU (I := I) (M := M) g α : C^∞⟮I, M; ℝ⟯) : M → ℝ))).trans
      hb_supp
  -- Get uniform iteratedFDeriv bound on Λ.
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    smoothExtensionScalar_iteratedFDeriv_bound (I := I) (M := M) α
      hbΔρα_smooth hbΔρα_supp 1
  -- Set Λ explicitly.
  set Λ : EuclN → ℝ := smoothExtensionScalar (I := I) (M := M) α bΔρα with hΛ_def
  have hΛ_smooth : ContDiff ℝ (⊤ : ℕ∞) Λ :=
    contDiff_smoothExtensionScalar (I := I) (M := M) α hbΔρα_smooth hbΔρα_supp
  have hΛ_bound : ∀ j ≤ 1, ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ‖iteratedFDeriv ℝ j Λ y‖ ≤ C := fun j hj y _ => hC_bound j hj y
  -- Apply Euclidean quantitative Leibniz bound at k=1.
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le
      (d := Module.finrank ℝ E) 1 (p := 2) (by norm_num) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      hΛ_smooth hC_nn hΛ_bound
  refine ⟨K, hK_pos, ?_⟩
  intro v
  -- The pointwise factorisation on chartTarget.
  have h_factor : (fun y : EuclN => chartPushedRaw (I := I) (M := M) α
        (lapPiece (I := I) (M := M) g α v.toFun) y) =ᵐ[
        volume.restrict (chartTargetEuclid (I := I) (M := M) α)]
      fun y : EuclN => Λ y * chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun) y := by
    refine (MeasureTheory.ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    exact chartPushedRaw_lapPiece_factor (I := I) (M := M) g α v.toFun
      hb_one_on_tsupp hy
  -- The wkpNorm is invariant under a.e. equality.
  have h_norm_eq :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y : EuclN => Λ y * chartPushedRaw (I := I) (M := M) α
          (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_factor
  rw [h_norm_eq]
  -- Apply the per-α quantitative bound. We need chartPushedRaw α (η · v) ∈ MemWkp 1 2.
  have hH_W12 : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
    -- The η · v.toFun is smooth on M with tsupport in chart α source, so chartPushedRaw is in MemW1p.
    have h_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (etaTimesV (I := I) (M := M) α v.toFun) :=
      etaTimesV_smooth (I := I) (M := M) α v.smooth
    have h_supp : tsupport (etaTimesV (I := I) (M := M) α v.toFun) ⊆
        (chartAt H α).source :=
      tsupport_etaTimesV_subset (I := I) (M := M) α v.toFun
    have h_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartPushedRaw (I := I) (M := M) α
          (etaTimesV (I := I) (M := M) α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) :=
      DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidualMemW1p.memW1p_chartPushedRaw_of_contMDiff_tsupport
        (I := I) (M := M) (α := α) h_smooth h_supp 2
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p).mpr h_w1p
  exact hK_bound hH_W12

/-! ## Manifold-side smooth coefficient for the chart-formula `gradInnerPiece` decomposition

For each `i : Fin n`, define `gradInnerCoefI_M g α i : M → ℝ` by
`x ↦ chartStrictCutoff α x · gradChartCoeff g α ρα i x`. This is smooth on `M`
with `tsupport ⊆ chartStrictCutoff α tsupport ⊆ chartAt H α .source`. On the
chart-α source, we have the manifold-side identity

```
gradInnerPiece g α v.toFun x =
  2 · ∑_i (gradChartCoeff g α ρα i x) ·
    partialDeriv i (scalarOnE α (η · v.toFun)) (extChart x).
```

After cutoff, this becomes a sum of products of smooth M-side coefficients
times chart-pulled partials of `η · v.toFun`. -/

/-- The `i`-th chart-α coefficient for the gradient inner product `g(∇ρα, ∇·)`,
multiplied by the strict cutoff. Smooth on `M` with `tsupport` in chart α source. -/
private noncomputable def gradInnerCoefI_M
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun x : M =>
    chartStrictCutoff (I := I) (M := M) α x *
      gradChartCoeff (I := I) g α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x

private lemma gradInnerCoefI_M_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    gradInnerCoefI_M (I := I) (M := M) g α i x =
      chartStrictCutoff (I := I) (M := M) α x *
        gradChartCoeff (I := I) g α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x := rfl

private lemma gradInnerCoefI_M_eq_zero_of_cutoff_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {x : M}
    (hx : chartStrictCutoff (I := I) (M := M) α x = 0) :
    gradInnerCoefI_M (I := I) (M := M) g α i x = 0 := by
  unfold gradInnerCoefI_M
  rw [hx]; ring

/-- `gradInnerCoefI_M g α i` is smooth on M. -/
private lemma gradInnerCoefI_M_smooth
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (gradInnerCoefI_M (I := I) (M := M) g α i) := by
  classical
  intro x₀
  by_cases hx_src : x₀ ∈ (chartAt H α).source
  · -- On chart α source, the gradChartCoeff is smooth (per Geometry/Gradient.lean's
    -- gradChartCoeff_contMDiffOn).
    have h_chart_src_open : IsOpen ((chartAt H α).source) :=
      (chartAt H α).open_source
    have h_cut_smooth : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (chartStrictCutoff (I := I) (M := M) α) x₀ :=
      (chartStrictCutoff_contMDiff (I := I) (M := M) α).contMDiffAt
    have hbase : x₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx_src
    have h_base_open : IsOpen ((trivializationAt E (TangentSpace I) α).baseSet) := by
      rw [trivializationAt_baseSet_eq_chartAt_source]; exact h_chart_src_open
    have hα_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
    -- gradChartCoeff g α ρα i is ContMDiffOn (chart base set).
    have h_coeff_on : ContMDiffOn I 𝓘(ℝ) ∞
        (gradChartCoeff (I := I) g α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i)
        (trivializationAt E (TangentSpace I) α).baseSet := by
      -- gradChartCoeff is sum over j of chartInvGramMatrix · partialDeriv-of-scalarOnE.
      -- chartInvGramMatrix entries are smooth on base set.
      -- partialDeriv of scalarOnE α ρα at extChart x is smooth on chart source.
      unfold gradChartCoeff
      refine contMDiffOn_finset_sum (fun j _ => ?_)
      refine ContMDiffOn.mul ?_ ?_
      · exact chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
      · -- ContMDiffOn x ↦ partialDeriv j (scalarOnE α ρα) (extChart x) on base set.
        -- This is a composition: first extChart x (smooth on chart α source ⊇ base set),
        -- then partialDeriv j (scalarOnE α ρα) (·) (smooth on chart target).
        have h_extChartOn_M : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α)
            (chartAt H α).source :=
          contMDiffOn_extChartAt (I := I) (x := α)
        have h_extChartOn : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α)
            (trivializationAt E (TangentSpace I) α).baseSet := by
          have h_eq : (trivializationAt E (TangentSpace I) α).baseSet =
              (chartAt H α).source := by
            rw [trivializationAt_baseSet_eq_chartAt_source]
          rw [h_eq]; exact h_extChartOn_M
        have h_scalar_target : ContDiffOn ℝ ∞
            (scalarOnE (I := I) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
            (extChartAt I α).target :=
          DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
            (I := I) α hα_smooth
        have h_target_open : IsOpen ((extChartAt I α).target) :=
          isOpen_extChartAt_target (I := I) α
        have h_partial_E_on : ContDiffOn ℝ ∞
            (fun y : E => partialDeriv (E := E) j
              (scalarOnE (I := I) α
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y)
            (extChartAt I α).target := by
          unfold partialDeriv
          have h_fderiv_smooth :
              ContDiffOn ℝ ∞ (fun y : E => fderiv ℝ
                (scalarOnE (I := I) α
                  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y)
                (extChartAt I α).target := by
            have h_le : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
              rw [show ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = ((⊤ : ℕ∞) : WithTop ℕ∞) from by simp]
            exact h_scalar_target.fderiv_of_isOpen h_target_open h_le
          exact h_fderiv_smooth.clm_apply contDiffOn_const
        -- Convert to ContMDiffOn at the M level.
        have h_partial_M_E : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
            (fun y : E => partialDeriv (E := E) j
              (scalarOnE (I := I) α
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y)
            (extChartAt I α).target :=
          (contMDiffOn_iff_contDiffOn).mpr h_partial_E_on
        have h_maps : Set.MapsTo (extChartAt I α)
            (trivializationAt E (TangentSpace I) α).baseSet
            (extChartAt I α).target := by
          intro x hx
          have hsrc : x ∈ (chartAt H α).source := by
            rw [trivializationAt_baseSet_eq_chartAt_source] at hx; exact hx
          have h_ext_src : x ∈ (extChartAt I α).source := by
            rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrc
          exact (extChartAt I α).map_source h_ext_src
        exact h_partial_M_E.comp h_extChartOn h_maps
    exact h_cut_smooth.mul ((h_coeff_on x₀ hbase).contMDiffAt
      (h_base_open.mem_nhds hbase))
  · -- Outside chart α source: chartStrictCutoff α ≡ 0 in a neighborhood, so
    -- gradInnerCoefI_M is locally 0, hence smooth.
    have hx_compl : x₀ ∈ ((chartAt H α).source)ᶜ := hx_src
    have h_ev_zero : ∀ᶠ x in 𝓝 x₀,
        chartStrictCutoff (I := I) (M := M) α x = 0 := by
      have h_ev_nhdsSet :=
        chartStrictCutoff_eventually_zero_nhdsSet_compl_source (I := I) (M := M) α
      exact h_ev_nhdsSet.filter_mono (nhds_le_nhdsSet hx_compl)
    have h_ev_zero_coef : ∀ᶠ x in 𝓝 x₀,
        gradInnerCoefI_M (I := I) (M := M) g α i x = 0 := by
      filter_upwards [h_ev_zero] with x hx
      exact gradInnerCoefI_M_eq_zero_of_cutoff_zero (I := I) (M := M) g α i hx
    have h_const : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ)) x₀ :=
      contMDiffAt_const
    exact h_const.congr_of_eventuallyEq h_ev_zero_coef

private lemma tsupport_gradInnerCoefI_M_subset
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    tsupport (gradInnerCoefI_M (I := I) (M := M) g α i) ⊆ (chartAt H α).source := by
  classical
  have h_supp_subset : Function.support (gradInnerCoefI_M (I := I) (M := M) g α i) ⊆
      Function.support (chartStrictCutoff (I := I) (M := M) α) := by
    intro x hx
    by_contra hxoff
    apply hx
    have h0 : chartStrictCutoff (I := I) (M := M) α x = 0 := by
      simpa [Function.mem_support, not_not] using hxoff
    exact gradInnerCoefI_M_eq_zero_of_cutoff_zero (I := I) (M := M) g α i h0
  have h_tsupp_subset : tsupport (gradInnerCoefI_M (I := I) (M := M) g α i) ⊆
      tsupport (chartStrictCutoff (I := I) (M := M) α) :=
    closure_minimal (h_supp_subset.trans (subset_tsupport _))
      (isClosed_tsupport _)
  exact h_tsupp_subset.trans (chartStrictCutoff_tsupport_subset (I := I) (M := M) α)

/-! ## Chart-pushed-raw `gradInnerPiece` factorisation

Pointwise identity on `chartTargetEuclid α`:
`chartPushedRaw α (gradInnerPiece g α v.toFun) y =
  2 · ∑_i (smoothExtensionScalar α (gradInnerCoefI_M g α i))(y) ·
        partialDerivOnEuclid α i (etaTimesV α v.toFun) y`. -/

/-- The smooth Euclidean coefficient `Λ_i` := `smoothExtensionScalar α (gradInnerCoefI_M g α i)`.
This is `ContDiff ℝ ∞` on `EuclN` with compact support contained in
`chartTargetEuclid α`. -/
private noncomputable def Λgrad
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  smoothExtensionScalar (I := I) (M := M) α
    (gradInnerCoefI_M (I := I) (M := M) g α i)

private lemma Λgrad_contDiff
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (Λgrad (I := I) (M := M) g α i) := by
  unfold Λgrad
  exact contDiff_smoothExtensionScalar (I := I) (M := M) α
    (gradInnerCoefI_M_smooth (I := I) (M := M) g α i)
    (tsupport_gradInnerCoefI_M_subset (I := I) (M := M) g α i)

/-- For any `y ∈ chartTargetEuclid α`, `Λgrad g α i y` agrees with
`gradInnerCoefI_M g α i (extChart.symm(toEuclidean.symm y))`. -/
private lemma Λgrad_apply_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    Λgrad (I := I) (M := M) g α i y =
      gradInnerCoefI_M (I := I) (M := M) g α i
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  unfold Λgrad
  have h_tgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy; exact hy
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      gradInnerCoefI_M (I := I) (M := M) g α i
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = _
  rw [if_pos h_tgt]

/-- Uniform iterated-derivative bound on `Λgrad g α i` up to order 1. -/
private lemma Λgrad_iteratedFDeriv_bound
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ 1, ∀ y : EuclN,
      ‖iteratedFDeriv ℝ j (Λgrad (I := I) (M := M) g α i) y‖ ≤ C := by
  unfold Λgrad
  exact smoothExtensionScalar_iteratedFDeriv_bound (I := I) (M := M) α
    (gradInnerCoefI_M_smooth (I := I) (M := M) g α i)
    (tsupport_gradInnerCoefI_M_subset (I := I) (M := M) g α i) 1

/-! ## Chart formula for the chart-pushed-raw of `gradInnerPiece`

The chart-pushed-raw of `gradInnerPiece` has a pointwise sum expansion on
`chartTargetEuclid α`. -/

/-- Pointwise identity: on `chartTargetEuclid α`,
`chartPushedRaw α (gradInnerPiece g α v.toFun) y =
  2 · ∑_i Λgrad g α i y · partialDerivOnEuclid α i (η · v.toFun) y`. -/
private lemma chartPushedRaw_gradInnerPiece_eq_sum
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun) y =
      (2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
        Λgrad (I := I) (M := M) g α i y *
          partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun) y := by
  classical
  -- Step 1: chartPushedRaw α (gradInnerPiece) at y in chartTarget evaluates at the
  -- chart-pulled point.
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (gradInnerPiece (I := I) (M := M) g α v.toFun) hy]
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  -- Step 2: gradInnerPiece x = 2 g(∇ρα, ∇(η · v))(x).
  rw [gradInnerPiece_apply]
  -- Step 3: Use the chart-α formula for g(∇ρα, ∇·) on chart source.
  -- This requires x ∈ chart α source.
  have h_tgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy; exact hy
  have hx_src : x ∈ (chartAt H α).source := by
    have hsrc : x ∈ (extChartAt I α).source := (extChartAt I α).map_target h_tgt
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hsrc
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx_src
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target := by
    have h_φx : extChartAt I α x = (toEuclidean (E := E)).symm y := by
      rw [hx_def]; exact (extChartAt I α).right_inv h_tgt
    rw [h_φx]
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α h_tgt
  have hηv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (etaTimesV (I := I) (M := M) α v.toFun) :=
    etaTimesV_smooth (I := I) (M := M) α v.smooth
  -- Apply chart formula step 1: gradInner = ∑_{ij} G⁻¹_{ij} ∂_i ρα · ∂_j (η·v).
  -- But we want a SINGLE sum decomposition: gradInner = ∑_i gradChartCoeff ρα i x ·
  --                                                    ∂_i(scalarOnE α (η · v))(extChart x).
  -- This is from `gradFun = ∑_i gradChartCoeff i · chartBasisVecFiber i`, applied via
  -- inner product with ∇(η · v) and the chart-basis-vec-fiber action.
  have hα_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  -- We use: g.inner x (gradFun g ρα x) (gradFun g (η·v) x) = ∑_i gradChartCoeff ρα i x ·
  --          mfderiv (η·v) x (chartBasisVecFiber i x).
  -- And mfderiv (η·v) x (chartBasisVecFiber i x) = partialDeriv i (scalarOnE α (η·v)) (φ x).
  -- (Note we ALREADY have the chart-formula in `gradInner_eq_invGramMatrix_partials_smooth`
  -- in ChartBilinearSmooth.lean. We could use a single sum decomposition for cleanness.)
  -- For our purposes, expand g(∇ρα, ∇·) via the gradFun chart-local decomposition
  -- and inner_gradFun:
  -- g.inner x (gradFun ρα x) (∇u x) = mfderiv u x (gradFun ρα x).
  -- gradFun ρα x = ∑_i gradChartCoeff ρα i x • chartBasisVecFiber i x (on chart source).
  -- So mfderiv u x (gradFun ρα x) = ∑_i gradChartCoeff ρα i x · mfderiv u x (chartBasisVecFiber i x)
  --                            = ∑_i gradChartCoeff ρα i x · partialDeriv i (scalarOnE α u) (extChart x).
  have hgradFun_decomp : gradFun (I := I) g
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x =
      ∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x •
          chartBasisVecFiber (I := I) α i x := by
    have hα_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
      hα_smooth.mdifferentiableAt (by simp)
    have h := gradChartLocal_eq_gradFun (I := I) g (α := α)
      hα_mdiff hx_base hx_int
    rw [← h]; rfl
  have h_mfderiv_apply : ∀ i : Fin (Module.finrank ℝ E),
      mfderiv I 𝓘(ℝ, ℝ) (etaTimesV (I := I) (M := M) α v.toFun) x
          (chartBasisVecFiber (I := I) α i x) =
      partialDeriv (E := E) i
        (scalarOnE (I := I) α (etaTimesV (I := I) (M := M) α v.toFun))
        (extChartAt I α x) := fun i =>
    mfderiv_chartBasisVecFiber (I := I) (α := α) hηv_smooth hx_src hx_int i
  -- Compute g.inner x (gradFun ρα x) (gradFun (η·v) x) = mfderiv (η·v) x (gradFun ρα x).
  have h_inner_eq :
      g.inner x (gradFun (I := I) g
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
          (gradFun (I := I) g (etaTimesV (I := I) (M := M) α v.toFun) x) =
      mfderiv I 𝓘(ℝ, ℝ) (etaTimesV (I := I) (M := M) α v.toFun) x
        (gradFun (I := I) g
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
    rw [g.symm x _ _]
    exact inner_gradFun (I := I) g
      (etaTimesV (I := I) (M := M) α v.toFun) x _
  rw [h_inner_eq, hgradFun_decomp]
  -- Compute mfderiv applied to a sum of scaled vectors via linearity.
  -- We set the CLM to ℝ explicitly to avoid TangentSpace-vs-ℝ confusion.
  set L : TangentSpace I x →L[ℝ] ℝ :=
    mfderiv I 𝓘(ℝ, ℝ) (etaTimesV (I := I) (M := M) α v.toFun) x with hL_def
  have h_mfderiv_sum : L
      (∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x •
          chartBasisVecFiber (I := I) α i x) =
      ∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x *
          L (chartBasisVecFiber (I := I) α i x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_smul, smul_eq_mul]
  -- Goal: 2 * L (∑ ...) = 2 * ∑ ...
  -- Rewrite the L (∑ ...) using h_mfderiv_sum.
  have h_LHS_eq : (2 : ℝ) * L
      (∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x •
          chartBasisVecFiber (I := I) α i x) =
    (2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x *
          L (chartBasisVecFiber (I := I) α i x) := by
    rw [h_mfderiv_sum]
  -- Use h_mfderiv_apply to rewrite each `L (chartBasisVecFiber ...)`.
  have h_mfderiv_apply_L : ∀ i : Fin (Module.finrank ℝ E),
      L (chartBasisVecFiber (I := I) α i x) =
      partialDeriv (E := E) i
        (scalarOnE (I := I) α (etaTimesV (I := I) (M := M) α v.toFun))
        (extChartAt I α x) := by
    intro i
    rw [hL_def]
    exact h_mfderiv_apply i
  -- The goal mentions `mfderiv` rather than `L`. Convert.
  show (2 : ℝ) * L _ = _
  rw [h_LHS_eq]
  simp_rw [h_mfderiv_apply_L]
  -- We need to match coefficients:
  -- gradChartCoeff ρα i x = Λgrad g α i y (at y on chartTarget, x = extChart.symm(...))?
  -- Actually Λgrad y = chartStrictCutoff α x · gradChartCoeff ρα i x.
  have hΛ_apply : ∀ i : Fin (Module.finrank ℝ E),
      Λgrad (I := I) (M := M) g α i y =
        chartStrictCutoff (I := I) (M := M) α x *
          gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x := by
    intro i
    rw [Λgrad_apply_of_mem (I := I) (M := M) g α i hy]
    rfl
  have h_partialDerivOnEuclid_apply : ∀ i : Fin (Module.finrank ℝ E),
      partialDerivOnEuclid (I := I) (M := M) α i
          (etaTimesV (I := I) (M := M) α v.toFun) y =
        partialDeriv (E := E) i
          (scalarOnE (I := I) α
            (etaTimesV (I := I) (M := M) α v.toFun))
          (extChartAt I α x) := by
    intro i
    have hφx_eq : extChartAt I α x = (toEuclidean (E := E)).symm y := by
      rw [hx_def]; exact (extChartAt I α).right_inv h_tgt
    rw [hφx_eq]; rfl
  simp_rw [hΛ_apply, h_partialDerivOnEuclid_apply]
    -- Now goal: -((2:ℝ) · ∑_i gradCoeff · mfderiv-applied) = 2 · ∑_i (cutoff · gradCoeff) · partial.
  -- The cutoff factor: at x = extChart.symm(symm_E y), what is chartStrictCutoff α x?
  -- For y in chartTarget, x ∈ chart α source, but x may or may not be in tsupport(ρα).
  -- If x ∉ support(gradChartCoeff ρα i): the i-th coefficient is 0, so the equation is 0 = 0
  -- for that i.
  -- If x ∈ support(gradChartCoeff ρα i) ⊆ support(dρα) ⊆ tsupport(ρα): chartStrictCutoff α x = 1.
  -- Use: gradChartCoeff i x ≠ 0 → x ∈ tsupport(ρα) → chartStrictCutoff α x = 1.
  -- Express via a `by_cases` on each summand.
  have h_sum_eq :
      ∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x *
          partialDeriv (E := E) i
            (scalarOnE (I := I) α
              (etaTimesV (I := I) (M := M) α v.toFun))
            (extChartAt I α x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartStrictCutoff (I := I) (M := M) α x *
          gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x) *
          partialDeriv (E := E) i
            (scalarOnE (I := I) α
              (etaTimesV (I := I) (M := M) α v.toFun))
            (extChartAt I α x) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h_grad_zero : gradChartCoeff (I := I) g α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x = 0
    · rw [h_grad_zero]; ring
    · -- gradChartCoeff i x ≠ 0 → x ∈ support(dρα). For chart-α formula on chart source,
      -- gradChartCoeff i x = Σ_j G⁻¹_{ij}(x) · ∂_j(scalarOnE α ρα)(extChart x).
      -- Nonzero implies some j with ∂_j(scalarOnE α ρα)(extChart x) ≠ 0.
      -- This implies that mfderiv ρα x ≠ 0 (the j-th partial of pulled-back).
      -- But strictly we need x ∈ tsupport(ρα): we proceed differently.
      -- Use mfderiv ρα x = sum of partials × chartBasisDualFiber, and mfderiv = 0
      -- outside support(dρα) ⊆ tsupport(ρα).
      -- Simpler argument: outside tsupport(ρα), ρα ≡ 0 in a nhd, so all partials of
      -- scalarOnE α ρα ∘ extChart at x are 0, hence gradChartCoeff i x = 0.
      have hx_supp : x ∈ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
        by_contra hx_off
        apply h_grad_zero
        have h_open : IsOpen
            (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))ᶜ :=
          (isClosed_tsupport _).isOpen_compl
        have h_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 x]
            (fun _ : M => (0 : ℝ)) := by
          filter_upwards [h_open.mem_nhds hx_off] with z hz
          by_contra hne
          exact hz (subset_tsupport _ hne)
        -- Show gradChartCoeff = 0 from local zero.
        -- gradChartCoeff i x = Σ_j G⁻¹_{ij} · ∂_j(scalarOnE α ρα)(extChart x).
        -- We need partialDeriv j (scalarOnE α ρα) (extChart x) = 0 for all j.
        unfold gradChartCoeff
        refine Finset.sum_eq_zero (fun j _ => ?_)
        -- partialDeriv j (scalarOnE α ρα) (extChart x) = 0 when ρα ≡ 0 near x.
        have h_scalar_ev : scalarOnE (I := I) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 (extChartAt I α x)]
            (fun _ : E => (0 : ℝ)) := by
          -- This requires h_ev (M-side eventual zero) → scalarOnE α ρα locally 0 at φ x.
          -- Take z near extChart x in chart α target. Then symm z is near x in chart α source.
          -- If z is close enough, symm z is in the open set where ρα ≡ 0.
          -- Hence scalarOnE α ρα z = ρα(symm z) = 0.
          have h_target_open : IsOpen ((extChartAt I α).target) :=
            isOpen_extChartAt_target (I := I) α
          have h_open_target : (extChartAt I α).target ∈ 𝓝 (extChartAt I α x) := by
            have h_ext_src : x ∈ (extChartAt I α).source := by
              rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_src
            exact h_target_open.mem_nhds ((extChartAt I α).map_source h_ext_src)
          have h_symm_cont : ContinuousAt (extChartAt I α).symm (extChartAt I α x) := by
            have h_continuousOn := continuousOn_extChartAt_symm (I := I) α
            have h_target_mem : extChartAt I α x ∈ (extChartAt I α).target := by
              have h_ext_src : x ∈ (extChartAt I α).source := by
                rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_src
              exact (extChartAt I α).map_source h_ext_src
            exact (h_continuousOn _ h_target_mem).continuousAt h_open_target
          have h_left_inv : ∀ᶠ z in 𝓝 (extChartAt I α x),
              (extChartAt I α) ((extChartAt I α).symm z) = z := by
            filter_upwards [h_open_target] with z hz
            exact (extChartAt I α).right_inv hz
          -- Pull back the ev.zero through symm.
          have h_symm_x : (extChartAt I α).symm (extChartAt I α x) = x := by
            have h_ext_src : x ∈ (extChartAt I α).source := by
              rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_src
            exact (extChartAt I α).left_inv h_ext_src
          -- For z near φ x in target, symm z is near x in M.
          have h_ev_through_symm : ∀ᶠ z in 𝓝 (extChartAt I α x),
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm z) = 0 := by
            have h_pre : (extChartAt I α).symm ⁻¹' {x : M | ((chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0} ∈ 𝓝 (extChartAt I α x) := by
              have h_set_open : {x : M | ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0}
                  ∈ 𝓝 x := h_ev
              exact h_symm_cont.preimage_mem_nhds (by rwa [h_symm_x])
            filter_upwards [h_pre] with z hz using hz
          filter_upwards [h_ev_through_symm] with z hz using hz
        have h_partial_zero :
            partialDeriv (E := E) j (scalarOnE (I := I) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
              (extChartAt I α x) = 0 := by
          unfold partialDeriv
          rw [Filter.EventuallyEq.fderiv_eq h_scalar_ev]
          simp
        rw [h_partial_zero]; ring
      -- Now hx_supp : x ∈ tsupport(ρα). So chartStrictCutoff α x = 1.
      have h_cut : chartStrictCutoff (I := I) (M := M) α x = 1 :=
        chartStrictCutoff_eq_one_on_tsupport_chartAtlasPOU (I := I) (M := M) α hx_supp
      rw [h_cut]; ring
  -- Apply h_sum_eq to finish.
  rw [h_sum_eq]

end SmoothFChartResidualBilinearBound
end Laplacian
end Analysis
end DifferentialGeometry

end
