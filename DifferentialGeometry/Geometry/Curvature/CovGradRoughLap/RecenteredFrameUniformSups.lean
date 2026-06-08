import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentitySmoothFrame
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivSecondOrderCommutation
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.DiffCurvatureGenuineTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureContractionLeibnizGridConstruction

/-!
# Frame-free uniform sups of the recentered orthonormal frame and the differentiated curvature

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file builds, frame-freely,
the two uniform moving-frame sups consumed by the per-direction third-order-cancellation envelopes of
`RemDiffFibThirdOrderCancellation`:

* `exists_uniform_recentered_christoffel_direction_gNorm_bound` — the **recentered orthonormal-frame
  Christoffel-direction uniform sup**: a single nonnegative constant `Kchr`, independent of the base
  point `x` and the frame index `i`, bounding the squared `g`-norm of the Christoffel direction
  `(∇_{Bᵢ} Bᵢ)(x)` of the *recentered* orthonormal frame `Bᵢ := smoothOrthoFrame g x i` (centred at `x`
  itself) at its own centre. This is the `R(diff) V` curvature-class fibre envelope's one remaining
  uniform input (`exists_riemannSecClass_tensor0SAsRS_fiberOrder_bound`).

* `exists_uniform_proportional_diffCurvOp` — the **frame-free `‖∇R‖_∞` uniform sup at the
  differentiated-curvature operator-tower level** (the deep-well bottom of the `(∇R)` content): a single
  nonnegative per-rank constant `Kdr : ℕ → ℝ`, independent of the base point, bounding the intrinsic
  fibre norm of the order-`p` differentiated-curvature contraction `diffCurvOp p r W = (∇^p R)(X, Y) W`
  by `Kdr r` times the order-`≤ p` covariant jet of `W`, uniformly over the compact `M`. It is the
  base-point-uniform companion of the continuous tower envelope `exists_continuous_proportional_diffCurvOp`
  (the `∇R` analogue of the uniform curvature sup
  `riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound`), and the frame-free uniform
  `‖∇^{≤ p} R‖_∞` input the per-direction `nablaTensorCurvSec` envelope `Child A`
  (`exists_uniform_nablaTensorCurvSec_tensor0SAsRS_proportional_local` of
  `RemDiffFibThirdOrderCancellation`) ultimately rests on.

## Why the recentered frame is not jointly continuous (the documented obstruction)

The recentered orthonormal frame `smoothOrthoFrame g x i = (chartBumpAt x : M → ℝ) · • chartFrameNorm
g x i` is, for a *fixed* centre `x`, a globally smooth section (`smoothOrthoFrame_smooth`); but its germ
at the diagonal point `x` depends on `x` through the chart `chartAt H x` selected at `x`
(`chartFrameNorm_eq_of_chartAt_eq`), which jumps with `x` on a multi-chart manifold (e.g. `S²`). So the
diagonal value family `x ↦ (∇_{Bᵢ} Bᵢ)(x)` is **not continuous** in `x` by elementary means, and its
`g`-norm cannot be supremised directly by `IsCompact.bddAbove_image`. This is exactly why the existing
uniform curvature sups (`UniformProportionalCurvatureSup`, `RankRUniformProportionalCurvatureSup`) are
computed frame-freely through the dual-frame route.

## The frame-free route — locality reduction onto the chart-frame self-Christoffel chart-data sup

The covariant derivative `(LeviCivita g).toFun σ x v` is local in its section argument `σ`: it depends
only on the germ of `σ` at `x` and the value `v` (`IsCovariantDerivativeOn.congr_of_eventuallyEq`). On
the open neighbourhood `smoothOrthoFrameNbhd x` (where the centring bump equals `1`), the recentered
frame agrees with the un-bumped Gram-Schmidt chart-frame section `chartFrameNorm g x i`
(`smoothOrthoFrame_eq_on_nbhd`), and the two agree at the centre `x` itself
(`mem_smoothOrthoFrameNbhd_self`). Hence the recentered Christoffel direction at the centre equals the
*chart-frame* self-Christoffel direction at the centre:
```
(∇_{smoothOrthoFrame g x i} smoothOrthoFrame g x i)(x)
  = (∇_{chartFrameNorm g x i} chartFrameNorm g x i)(x).
```
The right-hand side is governed by the chart-`(chartAt H x)`-coordinate covariant-derivative data — the
chart Christoffel symbols and the Gram-Schmidt coordinate matrix and its first partials — all `C^∞` and
uniformly bounded on the compact chart partition-of-unity supports that cover `M`
(`exists_chartRiemannData_uniform_bound_compact`,
`leviCivita_chartFrame_self_chartCoord_pullback_contDiffOn_chartTarget`). That uniform chart-data bound
on the chart-frame self-Christoffel direction is the genuinely-irreducible joint-smoothness analytic
content; it is isolated below as the precise child
`exists_uniform_chartFrameNorm_self_christoffel_gNorm_bound`, and the recentered sup is assembled on top
of it by the locality reduction.

## Convention

All fibre norms are the intrinsic Riemannian fibre norm `riemannianFiberNormSq` (`rfns`); all magnitudes
of the Christoffel directions are measured in the intrinsic metric inner product `g.inner`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- Non-negativity of `g.inner x v v` for a smooth Riemannian metric. -/
private lemma metric_inner_self_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with hv0 | hv0
  · rw [hv0]; simp
  · exact (g.pos x v hv0).le

/-- **Connection-locality reduction of the recentered Christoffel direction to the chart frame.** The
covariant derivative of the recentered orthonormal frame `smoothOrthoFrame g x i` along itself, at the
centre `x`, equals the covariant derivative of the un-bumped Gram-Schmidt chart-frame section
`chartFrameNorm g x i` along itself at `x`. The two sections agree on the open neighbourhood
`smoothOrthoFrameNbhd x` of `x` (centring bump `= 1`, `smoothOrthoFrame_eq_on_nbhd`), and the
Levi-Civita covariant derivative is local in its section argument
(`IsCovariantDerivativeOn.congr_of_eventuallyEq`). -/
private lemma recentered_eq_chartFrame_christoffel_direction
    (g : SmoothRiemannianMetric I M) (x : M) (i : Fin (Module.finrank ℝ E)) :
    (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
        (smoothOrthoFrame (I := I) g x i x) =
      (LeviCivita (I := I) g).toFun (chartFrameNorm (I := I) g x i) x
        (chartFrameNorm (I := I) g x i x) := by
  classical
  -- The two sections are eventually equal near `x`.
  have hev : ∀ᶠ b in 𝓝 x,
      smoothOrthoFrame (I := I) g x i b = chartFrameNorm (I := I) g x i b := by
    filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x] with b hb
    exact smoothOrthoFrame_eq_on_nbhd (I := I) g x i hb
  -- `chartFrameNorm g x i` is `MDifferentiable` at `x` (its chart source is a neighbourhood of `x`).
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hbaseNhds : (trivializationAt E (TangentSpace I) x).baseSet ∈ 𝓝 x :=
    (trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds hx_base
  -- Connection locality: the `toFun`-CLMs agree (expected types drive the model elaboration).
  have hclm :
      (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x =
        (LeviCivita (I := I) g).toFun (chartFrameNorm (I := I) g x i) x :=
    (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      ((smoothOrthoFrame_smooth (I := I) g x i).contMDiffAt.mdifferentiableAt (by simp))
      (((chartFrameNorm_contMDiffOn (I := I) g x i x hx_base).contMDiffAt hbaseNhds).mdifferentiableAt
        (by simp))
      (Filter.univ_mem) hev
  -- The applied centre values also agree.
  have hval : smoothOrthoFrame (I := I) g x i x = chartFrameNorm (I := I) g x i x :=
    smoothOrthoFrame_eq_on_nbhd (I := I) g x i (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
  rw [hval]
  exact congrFun (congrArg DFunLike.coe hclm) (chartFrameNorm (I := I) g x i x)

/-- **The chart-frame self-Christoffel-direction uniform sup (the genuinely-irreducible
joint-smoothness chart-data content).** For a closed smooth Riemannian manifold `(M, g)` there is a
single nonnegative constant `Kchr`, independent of the chart/frame centre `α` and the frame index `i`,
bounding the squared `g`-norm of the chart-frame self-Christoffel direction
`(∇_{chartFrameNorm g α i} chartFrameNorm g α i)(α)` of the un-bumped Gram-Schmidt chart-frame section
`chartFrameNorm g α i`, evaluated at the chart centre `α` itself:
```
∀ α i, g((∇_{chartFrameNorm g α i} chartFrameNorm g α i)(α),
         (∇_{chartFrameNorm g α i} chartFrameNorm g α i)(α)) ≤ Kchr.
```

**Why this is TRUE.** At the centre `α`, the chart `chartAt H α` selected at `α` is exactly the chart
the Gram-Schmidt frame `chartFrameNorm g α i` is built from, so frame-chart and computation-chart
coincide there. In chart-`α` coordinates the covariant derivative
`(LeviCivita g).toFun (chartFrameNorm g α i) α v` is, by the Leibniz expansion
`cov_RS_covApply_frameVec_eq_coord_expansion` specialised to the tangent connection, a polynomial in the
chart Christoffel symbols `chartChristoffel g α · · ·`, the Gram-Schmidt coordinate matrix
`chartFrameNormGlobalSmoothCoordMatrix g α i k` and its first chart-coordinate partials — every factor
`C^∞` on the chart-target interior and *uniformly bounded* on the compact chart-`α` partition-of-unity
support that covers `M` (`exists_chartRiemannData_uniform_bound_compact` for the Christoffel data;
`leviCivita_chartFrame_self_chartCoord_pullback_contDiffOn_chartTarget` for the assembled chart-frame
self-Christoffel coordinate, `C^∞` on the chart target hence bounded on the compact chart image). Taking
the finite maximum over the partition-of-unity index set `chartAtlasPOU_finset` (which covers every
centre `α` through the chart at which the frame is read) gives the single base-point/index-uniform
constant. This is the chart-locality-free route (no `HasLocallyConstantChartAt`, no chart-trivialisation
operator-norm scalar; only the bounded chart Christoffel / Gram-Schmidt data).

**Non-vacuity (the litmus).** With `Kchr = 0` the bound forces
`(∇_{chartFrameNorm g α i} chartFrameNorm g α i)(α) = 0` for every centre `α` and index `i` — i.e. the
Gram-Schmidt chart frame would be parallel along itself at every chart centre, false on a curved
manifold (where no smooth frame is parallel). So `Kchr` is genuinely positive and the envelope carries
the genuine Christoffel magnitude.

This is the precise atomic chart-data primitive isolated as the genuinely-large analytic node; the
recentered orthonormal-frame sup `exists_uniform_recentered_christoffel_direction_gNorm_bound` is
assembled on top of it by the connection-locality reduction `smoothOrthoFrame g x i =ᶠ[𝓝 x]
chartFrameNorm g x i`. The body is `sorry` and consumers transitively depend on its `sorryAx`. -/
theorem exists_uniform_chartFrameNorm_self_christoffel_gNorm_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Kchr : ℝ, 0 ≤ Kchr ∧
      ∀ (α : M) (i : Fin (Module.finrank ℝ E)),
        g.inner α ((LeviCivita (I := I) g).toFun (chartFrameNorm (I := I) g α i) α
            (chartFrameNorm (I := I) g α i α))
          ((LeviCivita (I := I) g).toFun (chartFrameNorm (I := I) g α i) α
            (chartFrameNorm (I := I) g α i α)) ≤ Kchr := by
  sorry

/-- **The recentered orthonormal-frame Christoffel-direction uniform sup (frame-free, glued over the
chart-frame chart-data sup).** For a closed smooth Riemannian manifold `(M, g)` there is a single
nonnegative constant `Kchr`, independent of the base point `x` and the frame index `i`, bounding the
squared `g`-norm of the Christoffel direction `(∇_{Bᵢ} Bᵢ)(x)` of the *recentered* orthonormal frame
`Bᵢ := smoothOrthoFrame g x i` (centred at `x` itself) at its own centre:
```
∀ x i, g((∇_{Bᵢ} Bᵢ)(x), (∇_{Bᵢ} Bᵢ)(x)) ≤ Kchr.
```

This is the genuine `‖∇B‖_∞`-style envelope of the recentered orthonormal frame's covariant derivative
at its own centre — the one remaining uniform input of the `R(diff) V` curvature-class fibre envelope
`exists_riemannSecClass_tensor0SAsRS_fiberOrder_bound`.

**Proof (glue, TRANSIT over the chart-frame chart-data sup).** The recentered orthonormal frame
`smoothOrthoFrame g x i` agrees with the un-bumped Gram-Schmidt chart-frame section `chartFrameNorm g x
i` on the open neighbourhood `smoothOrthoFrameNbhd x` of `x` (where the centring bump equals `1`,
`smoothOrthoFrame_eq_on_nbhd`), and the centre `x` itself lies in that neighbourhood
(`mem_smoothOrthoFrameNbhd_self`). The Levi-Civita covariant derivative is local in its section
argument (`IsCovariantDerivativeOn.congr_of_eventuallyEq`, both sections smooth at `x` —
`smoothOrthoFrame_smooth`, `chartFrameNorm_contMDiffOn`), so
`(LeviCivita g).toFun (smoothOrthoFrame g x i) x = (LeviCivita g).toFun (chartFrameNorm g x i) x` as
continuous-linear maps; applied to the equal centre values `smoothOrthoFrame g x i x = chartFrameNorm g
x i x` this gives `(∇_{Bᵢ} Bᵢ)(x) = (∇_{chartFrameNorm g x i} chartFrameNorm g x i)(x)`. The right-hand
side is bounded uniformly over `(x, i)` by the chart-frame self-Christoffel chart-data sup
`exists_uniform_chartFrameNorm_self_christoffel_gNorm_bound` (instantiated at the centre `α = x`).
Transits that child's `sorryAx`.

This is the canonical proof home of the recentered Christoffel-direction sup; its conclusion matches
verbatim the consumer leaf `exists_uniform_recentered_christoffel_direction_gNorm_bound` of
`RemDiffFibThirdOrderCancellation` (the `R(diff) V` class envelope `Child B`), which is discharged by
`exact` against this lemma. -/
theorem exists_recenteredFrame_christoffelDirection_gNormSq_uniform_sup
    (g : SmoothRiemannianMetric I M) :
    ∃ Kchr : ℝ, 0 ≤ Kchr ∧
      ∀ (x : M) (i : Fin (Module.finrank ℝ E)),
        g.inner x ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
            (smoothOrthoFrame (I := I) g x i x))
          ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
            (smoothOrthoFrame (I := I) g x i x)) ≤ Kchr := by
  classical
  obtain ⟨Kchr, hKchr_nn, hKchr⟩ :=
    exists_uniform_chartFrameNorm_self_christoffel_gNorm_bound (I := I) (M := M) g
  refine ⟨Kchr, hKchr_nn, fun x i => ?_⟩
  -- The recentered Christoffel direction at the centre equals the chart-frame self-Christoffel
  -- direction at the centre, by connection-locality.
  have hreduce :
      (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x) =
        (LeviCivita (I := I) g).toFun (chartFrameNorm (I := I) g x i) x
          (chartFrameNorm (I := I) g x i x) :=
    recentered_eq_chartFrame_christoffel_direction (I := I) (M := M) g x i
  rw [hreduce]
  exact hKchr x i

/-- **The frame-free `‖∇^{≤ p} R‖_∞` uniform sup at the differentiated-curvature operator-tower level.**
For a closed smooth Riemannian manifold `(M, g)`, smooth global tangent fields `X, Y`, and every
differentiation order `p`, there is a single nonnegative *per-rank* constant family `Kdr : ℕ → ℝ`,
independent of the base point, such that, for every covariant rank `r`, smooth compactly-supported
`(0, r)`-tensor section `W`, and every point `x`, the order-`p` differentiated-curvature contraction
`(∇^p R)(X, Y) W = diffCurvOp p r W` has intrinsic squared fibre norm at most `Kdr r` times the
order-`≤ p` covariant jet of `W`:
```
rfns(diffCurvOp p r W)(x) ≤ Kdr r · ∑_{q < p + 1} rfns(∇^q W)(x).
```

This is the base-point-uniform companion of the *continuous* per-rank tower envelope
`exists_continuous_proportional_diffCurvOp` — the `∇R` analogue of the uniform curvature-operator sup
`riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound`, one differentiation tower up. It is
the genuine frame-free `‖∇^{≤ p} R‖_∞` deep-well bottom that the per-direction differentiated-curvature
fibre envelope (`Child A`, `exists_uniform_nablaTensorCurvSec_tensor0SAsRS_proportional_local` of
`RemDiffFibThirdOrderCancellation`) ultimately rests on (the `nablaTensorCurvSec` per-direction
contraction is, through the abstract differentiated-curvature unfolding `nablaTensorCurvSec_def`, the
covariant derivative of the bundled curvature operator field — i.e. the `diffCurvOp 1`-class — contracted
on the per-frame directions and the `≤ 1`-jet of the unit-evaluated section).

**Proof.** The continuous per-rank envelope `Cp r : M → ℝ` of `exists_continuous_proportional_diffCurvOp`
is continuous and nonnegative; its range over the compact `M` is bounded above
(`IsCompact.bddAbove_image` through `(isCompact_univ).image`), so for each rank `r` the supremum
`Kdr r := max (C₀ r) 0` (with `C₀ r` an upper bound of the image) dominates `Cp r x` at every `x` while
staying nonnegative. Multiplying the continuous proportional bound by the (nonnegative) jet factor and
the pointwise envelope inequality `Cp r x ≤ Kdr r` gives the uniform bound. No frame is chosen and no
chart-trivialisation operator-norm scalar enters; the only chart data are the bounded chart
Christoffel / Riemann coefficients inside the continuous envelope. -/
theorem exists_uniform_proportional_diffCurvOp
    (g : SmoothRiemannianMetric I M) {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (p : ℕ) :
    ∃ Kdr : ℕ → ℝ, (∀ r, 0 ≤ Kdr r) ∧
      ∀ (r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x
            ((diffCurvOp (I := I) (M := M) g hX hY p r W).toSection x) ≤
          Kdr r * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  classical
  obtain ⟨Cp, hCp_cont, hCp_nn, hCp_bound⟩ :=
    exists_continuous_proportional_diffCurvOp (I := I) (M := M) g hX hY p
  -- Per-rank supremum of the continuous envelope over the compact `M`.
  have hsup : ∀ r : ℕ, ∃ C₀ : ℝ, ∀ x : M, Cp r x ≤ C₀ := by
    intro r
    have hCpt := (isCompact_univ (X := M)).image (hCp_cont r)
    obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
    exact ⟨C₀, fun x => hC₀ ⟨x, Set.mem_univ _, rfl⟩⟩
  choose C₀ hC₀ using hsup
  refine ⟨fun r => max (C₀ r) 0, fun r => le_max_right _ _, fun r W x => ?_⟩
  -- The order-`≤ p` jet factor is nonnegative.
  have hjet_nn : 0 ≤ ∑ q ∈ Finset.range (p + 1),
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
        ((iteratedCovGrad g 0 r q W).toSection x) :=
    Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _
  have hCp_le : Cp r x ≤ max (C₀ r) 0 := le_trans (hC₀ r x) (le_max_left _ _)
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x
        ((diffCurvOp (I := I) (M := M) g hX hY p r W).toSection x)
        ≤ Cp r x * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := hCp_bound r W x
    _ ≤ max (C₀ r) 0 * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) :=
          mul_le_mul_of_nonneg_right hCp_le hjet_nn

end Connection
end Integral
end DifferentialGeometry

end
