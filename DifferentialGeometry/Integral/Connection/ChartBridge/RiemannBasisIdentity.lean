import DifferentialGeometry.Integral.Connection.ChartBridge.Ricci
import DifferentialGeometry.Integral.Connection.ChartBridge.Hessian
import DifferentialGeometry.Integral.Connection.CurvatureBundling
import DifferentialGeometry.Integral.Connection.ChartLieBracket
import DifferentialGeometry.Integral.Connection.CovApplyCovRSChartBasisExtension

/-!
# Unconditional discharge of the chart-Christoffel Riemann identity

This file proves, unconditionally, the deep basis-coordinate identification of the
abstract Riemann operator of the Levi-Civita connection with the chart-Christoffel
Riemann tensor:
`chartRiemannBasisIdentity g x` for every smooth Riemannian metric `g` on a closed
(boundaryless, σ-compact, Hausdorff) manifold and every point `x`.

The abstract Riemann operator `riemannOp (LeviCivita g)` is the curvature
`∇∇ - ∇∇ - ∇_{[·,·]}` of Mathlib's bundled covariant derivative. The chart Riemann
tensor `R^l{}_{ijk}` is the classical Christoffel expression
`∂_j Γ^l{}_{ik} - ∂_k Γ^l{}_{ij} + Γ^l{}_{jm} Γ^m{}_{ik} - Γ^l{}_{km} Γ^m{}_{ij}`.

## Strategy

We mirror the proof of `chartHessianMatrixIdentity_holds` in `ChartBridge.Hessian`,
one order of differentiation deeper. The genuinely new ingredient is the second
covariant derivative of a chart-basis section
`∇_{e_a}(∇_{e_b} e_i)(x)`: the inner derivative is the section
`b ↦ ∑_m Γ^m{}_{ib}(φ b) • e_m(b)` whose coefficients are now *non-constant* (unlike
the Hessian case, where the chart-pullback of the constant basis section has vanishing
`fderiv`). Differentiating that section by the Leibniz rule produces the partial
derivative `∂_a Γ^l{}_{ib}` together with the quadratic Christoffel term
`∑_m Γ^l{}_{am} Γ^m{}_{ib}`. Subtracting the two orderings `(a,b) = (j,k)` and
`(a,b) = (k,j)` and using the symmetry of the Christoffel symbol in the lower indices
recovers exactly `chartRiemannTensor`.

## Main results

* `LeviCivita_chartBasisVec_secondCovDeriv` — the second covariant derivative of the
  chart-basis section in coordinates.
* `chartRiemannBasisIdentity_holds` — the unconditional basis-coordinate identity.
* `riemannOp_eq_chartRiemannCLM_apply` — the unconditional trilinear bridge:
  `riemannOp (LeviCivita g) x v w u = chartRiemannCLM g x v w u` for all tangent
  vectors `v, w, u`, with no hypothesis.
-/

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open Bundle Manifold Set FiberBundle Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## Directional derivative of a chart-pulled-back scalar along a model-basis vector

For a function `gE : E → ℝ` that is `C¹` near `φ x`, the manifold directional derivative
of the chart-pullback `b ↦ gE (φ b)` along the model-basis vector `e_a`, evaluated at the
basepoint `x`, is the Euclidean partial derivative `∂_a gE (φ x)`. This is the engine for
computing the partial derivative `∂_a Γ^l{}_{ib}(φ x)` of the Christoffel coefficient
appearing in the second covariant derivative. -/

/-- The manifold directional derivative along `e_a` of the chart-pullback `b ↦ gE (φ b)`,
at the basepoint `x`, equals the Euclidean partial derivative `∂_a gE (φ x)`. -/
lemma extDerivFun_comp_extChartAt_apply_basis [I.Boundaryless]
    (x : M) {gE : E → ℝ}
    (hgE : ContDiffAt ℝ ∞ gE (extChartAt I x x))
    (a : Fin (Module.finrank ℝ E)) :
    extDerivFun (I := I) (fun b : M => gE (extChartAt I x b)) x
        ((chartModelBasis E) a) =
      partialDeriv (E := E) a gE (extChartAt I x x) := by
  classical
  -- Basepoint chart data.
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxsrc
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  -- The composite `gE ∘ φ` is `MDifferentiableAt` at `x`.
  set Gfun : M → ℝ := fun b : M => gE (extChartAt I x b) with hGfun_def
  -- Smoothness of `gE` at `φ x` ⟹ DifferentiableAt.
  have hgE_diff : DifferentiableAt ℝ gE (extChartAt I x x) :=
    hgE.differentiableAt (by simp)
  have hgE_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) gE (extChartAt I x x) := by
    rw [mdifferentiableAt_iff_differentiableAt]; exact hgE_diff
  have hphi_mdiff : MDiffAt (extChartAt I x) x :=
    mdifferentiableAt_extChartAt (I := I) (x := x) hxsrc
  have hG_mdiff : MDiffAt Gfun x := hgE_mdiff.comp x hphi_mdiff
  -- `extDerivFun h x v = mfderiv h x v` definitionally for ℝ-valued `h`.
  have hed_to_mfderiv :
      extDerivFun (I := I) Gfun x ((chartModelBasis E) a) =
        (mfderiv I 𝓘(ℝ) Gfun x : TangentSpace I x →L[ℝ] _) ((chartModelBasis E) a) := rfl
  rw [hed_to_mfderiv]
  -- Chart-bridge: `mfderiv Gfun x v = fderiv (Gfun ∘ φ.symm)(φ x) (trivToE x x v)`.
  rw [mfderiv_scalar_eq_chart_fderiv (I := I) x Gfun hxsrc hxint hG_mdiff
    ((chartModelBasis E) a)]
  rw [trivToE_self_apply (I := I) x ((chartModelBasis E) a)]
  -- `Gfun ∘ φ.symm = gE` near `φ x`, so the fderiv coincides with `fderiv gE (φ x)`.
  have htgt_nhds : ((extChartAt I x).target : Set E) ∈ 𝓝 (extChartAt I x x) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hxint) interior_subset
  have hcompose_eq : (Gfun ∘ (extChartAt I x).symm) =ᶠ[𝓝 (extChartAt I x x)] gE := by
    filter_upwards [htgt_nhds] with y hy
    change gE (extChartAt I x ((extChartAt I x).symm y)) = gE y
    rw [(extChartAt I x).right_inv hy]
  rw [hcompose_eq.fderiv_eq]
  rw [partialDeriv]

/-! ## Global smooth bump extension of a chart-basis tangent field

The chart-basis tangent field `chartBasisVecFiber x j` is smooth only on the
trivialization base set. To feed it into `riemannOp_apply_smooth`, we replace it by a
globally smooth field that agrees with `chartBasisVecFiber x j` on an open neighbourhood
of `x`: multiply by a smooth bump function supported inside `chartLeviCivitaGoodSet x` and
identically `1` near `x`. -/

/-- A globally smooth tangent field `Xext = χ • chartBasisVecFiber x j` agreeing with
`chartBasisVecFiber x j` on an open neighbourhood `U ∋ x` inside `chartLeviCivitaGoodSet x`. -/
lemma exists_globalSmooth_chartBasisVec_ext
    (x : M) (j : Fin (Module.finrank ℝ E)) :
    ∃ (Xext : Π b : M, TangentSpace I b) (U : Set M),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xext) ∧
        IsOpen U ∧ x ∈ U ∧ U ⊆ chartLeviCivitaGoodSet (I := I) x ∧
        ∀ y ∈ U, Xext y = chartBasisVecFiber (I := I) x j y := by
  classical
  -- `x` lies in its own good set.
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  -- A bump function based at `x` with tsupport inside the good set.
  have hopen : IsOpen (chartLeviCivitaGoodSet (I := I) x) :=
    chartLeviCivitaGoodSet_isOpen (I := I) x
  have hnhds : chartLeviCivitaGoodSet (I := I) x ∈ 𝓝 x := hopen.mem_nhds hx_good
  obtain ⟨χ, _, hχ_tsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hnhds
  -- The bumped field is globally smooth.
  have hXext_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y : M => (χ : M → ℝ) y • chartBasisVecFiber (I := I) x j y)) :=
    bumpedChartBasis_contMDiff (I := I) x (b₀ := x) j χ hχ_tsupp
  -- On a neighbourhood where `χ ≡ 1`, intersected with the good set, the bumped field
  -- agrees with the un-bumped chart-basis field.
  have hχ_eq_one_nhds : ∀ᶠ y in 𝓝 x, (χ : M → ℝ) y = 1 := χ.eventuallyEq_one
  obtain ⟨V_set, hV_nhds, hχ_one_V⟩ :=
    Filter.eventually_iff_exists_mem.mp hχ_eq_one_nhds
  obtain ⟨V_open, hV_sub_V_set, hV_open_isOpen, hx_in_V_open⟩ :=
    mem_nhds_iff.mp hV_nhds
  refine ⟨fun y : M => (χ : M → ℝ) y • chartBasisVecFiber (I := I) x j y,
    V_open ∩ chartLeviCivitaGoodSet (I := I) x, hXext_smooth,
    hV_open_isOpen.inter hopen, ⟨hx_in_V_open, hx_good⟩, fun y hy => hy.2, ?_⟩
  intro y hyU
  have hχ_one_y : (χ : M → ℝ) y = 1 := hχ_one_V y (hV_sub_V_set hyU.1)
  change (χ : M → ℝ) y • chartBasisVecFiber (I := I) x j y = chartBasisVecFiber (I := I) x j y
  rw [hχ_one_y, one_smul]

/-! ## Christoffel smoothness at the basepoint

The chart Christoffel symbol `chartChristoffel g x b i m` is `C^∞` at `φ x` (an interior
point of the chart target), so its directional derivative is computed by
`extDerivFun_comp_extChartAt_apply_basis`. -/

/-- The chart Christoffel symbol is `C^∞` at the chart basepoint `φ x`. -/
lemma chartChristoffel_contDiffAt_self [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (b i m : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞ (chartChristoffel (I := I) g x b i m) (extChartAt I x x) := by
  classical
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxsrc
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  have hon : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g x b i m)
      (interior (extChartAt I x).target) :=
    chartChristoffel_contDiffOn_interior (I := I) g x b i m
  exact hon.contDiffAt (isOpen_interior.mem_nhds hxint)

/-- Finite-sum linearity of the bundled covariant derivative in the section argument:
`(∇_v (∑_i σ i))(x) = ∑_i (∇_v (σ i))(x)` for sections `σ i` differentiable at `x`. -/
lemma leviCivita_finset_sum_apply
    {ι : Type*} (g : SmoothRiemannianMetric I M)
    (t : Finset ι) (σ : ι → Π y : M, TangentSpace I y)
    {x : M} (v : TangentSpace I x)
    (hσ : ∀ i, MDiffAt (T% (σ i)) x) :
    ((LeviCivita (I := I) g).toFun (t.sum σ) x) v =
      t.sum (fun i => ((LeviCivita (I := I) g).toFun (σ i) x) v) := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  induction t using Finset.induction_on with
  | empty => simp [cov.isCovariantDerivativeOnUniv.zero]
  | insert i t hit ih =>
      have hσi : MDiffAt (T% (σ i)) x := hσ i
      have hsum : MDiffAt (T% (t.sum σ)) x := by
        have hsum_raw := MDifferentiableAt.sum_section (s := t) (t := σ) hσ
        simpa using hsum_raw
      calc
        (cov.toFun ((insert i t).sum σ) x) v
            = (cov.toFun (σ i + t.sum σ) x) v := by
              simp [Finset.sum_insert, hit]
        _ = ((cov.toFun (σ i) x + cov.toFun (t.sum σ) x) v) := by
              rw [cov.isCovariantDerivativeOnUniv.add hσi hsum]
        _ = (cov.toFun (σ i) x) v + (cov.toFun (t.sum σ) x) v := by simp
        _ = (insert i t).sum (fun j => (cov.toFun (σ j) x) v) := by
              rw [ih]; simp [Finset.sum_insert, hit]

/-! ## Second covariant derivative of a chart-basis section

This is the genuinely new, one-order-deeper computation. We differentiate the section
`y ↦ (LeviCivita g) (X_i) y (X_b y)` (which equals `∇_{e_b} e_i` near `x`) along `e_a`. The
inner derivative is the non-constant-coefficient section
`y ↦ ∑_m Γ^m{}_{bi}(φ y) • e_m(y)`. The Leibniz rule produces the first partial
`∂_a Γ^l{}_{bi}(φ x)` and the quadratic Christoffel term `∑_m Γ^l{}_{am}(φ x) Γ^m{}_{bi}(φ x)`. -/

/-- **Second covariant derivative of a chart-basis section.** Let `Xa, Xb, Xi` be globally
smooth tangent fields agreeing with the chart-basis fields `e_a, e_b, e_i` on an open
neighbourhood `U ∋ x` inside `chartLeviCivitaGoodSet x`. Then
`∇_{e_a}(∇_{e_b} e_i)(x) =
   ∑_l (∂_a Γ^l{}_{bi}(φ x) + ∑_m Γ^l{}_{am}(φ x) Γ^m{}_{bi}(φ x)) • e_l(x)`. -/
lemma LeviCivita_chartBasisVec_secondCovDeriv [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (a b i : Fin (Module.finrank ℝ E))
    {Xa Xb Xi : Π b : M, TangentSpace I b} {U : Set M}
    (_hXa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xa))
    (hXb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xb))
    (hXi : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xi))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) x)
    (hXa_eq : ∀ y ∈ U, Xa y = chartBasisVecFiber (I := I) x a y)
    (hXb_eq : ∀ y ∈ U, Xb y = chartBasisVecFiber (I := I) x b y)
    (hXi_eq : ∀ y ∈ U, Xi y = chartBasisVecFiber (I := I) x i y) :
    (LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) Xb Xi) x (Xa x) =
      ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) a (chartChristoffel (I := I) g x b i l) (extChartAt I x x) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x a m l (extChartAt I x x) *
              chartChristoffel (I := I) g x b i m (extChartAt I x x)) •
          (chartModelBasis E) l := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  -- `Xa x = e_a` at the basepoint.
  have hXa_x : Xa x = chartBasisVecFiber (I := I) x a x := hXa_eq x hxU
  -- The inner section `S := covApply cov Xb Xi = ∇_{Xb} Xi`.
  set S : Π y : M, TangentSpace I y := covApply cov Xb Xi with hS_def
  -- `S` is globally smooth (so `MDiffAt` at `x`).
  have hXi_plus : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% Xi) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]; exact hXi
  have hS_diff : MDiffAt (T% S) x :=
    covApply_mdifferentiableAt (cov := cov) hXb hXi_plus
  -- The chart-basis frame fields `e_m`, smooth at `x` and on the good set.
  -- The "model frame coefficient" near `x`: Γ^m_{bi}(φ ·).
  set Γc : Fin (Module.finrank ℝ E) → M → ℝ :=
    fun m y => chartChristoffel (I := I) g x b i m (extChartAt I x y) with hΓc_def
  -- The "frame term" near `x`: y ↦ Γc m y • e_m(y).
  set term : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun m y => Γc m y • chartBasisVecFiber (I := I) x m y with hterm_def
  -- On `U`, `S` equals the sum of the frame terms: `S y = ∑_m Γ^m_{bi}(φ y) • e_m(y)`.
  have hS_eq_sum_on_U : ∀ y ∈ U, S y = ∑ m : Fin (Module.finrank ℝ E), term m y := by
    intro y hy
    have hy_good : y ∈ chartLeviCivitaGoodSet (I := I) x := hU_good hy
    -- `S y = cov.toFun Xi y (Xb y)`, and near `y`, `Xi = e_i`, `Xb = e_b`.
    have hSval : S y = cov.toFun Xi y (Xb y) := rfl
    rw [hSval]
    -- Replace `Xi` by `chartBasisVec x i` (agree on the open set `U ∋ y`) inside `cov`.
    have hXi_diff_y : MDiffAt (T% Xi) y := (hXi y).mdifferentiableAt (by simp)
    have hchart_i_diff_y : MDiffAt (T% (fun z : M => chartBasisVecFiber (I := I) x i z)) y :=
      chartBasisVec_alpha_mdifferentiableAt (I := I) x i hy_good
    have hXi_ev : (fun z : M => Xi z) =ᶠ[𝓝 y]
        (fun z : M => chartBasisVecFiber (I := I) x i z) := by
      filter_upwards [hU_open.mem_nhds hy] with z hz using hXi_eq z hz
    have hcov_congr :
        cov.toFun Xi y = cov.toFun (fun z : M => chartBasisVecFiber (I := I) x i z) y :=
      cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hXi_diff_y hchart_i_diff_y
        Filter.univ_mem hXi_ev
    rw [hcov_congr]
    -- Replace `Xb y` by `e_b y`.
    rw [hXb_eq y hy]
    -- Apply the chart-frame first covariant-derivative formula.
    rw [LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g x b i hy_good]
  -- Differentiability of each `term m` at `x`.
  -- `Γc m` is `MDiffAt x` (chart-Christoffel pulled back through `φ`).
  have hΓc_diff : ∀ m : Fin (Module.finrank ℝ E), MDiffAt (Γc m) x := by
    intro m
    have hΓ_cda : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g x b i m) (extChartAt I x x) :=
      chartChristoffel_contDiffAt_self (I := I) g x b i m
    have hΓ_d : DifferentiableAt ℝ (chartChristoffel (I := I) g x b i m) (extChartAt I x x) :=
      hΓ_cda.differentiableAt (by simp)
    have hΓ_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
        (chartChristoffel (I := I) g x b i m) (extChartAt I x x) := by
      rw [mdifferentiableAt_iff_differentiableAt]; exact hΓ_d
    have hphi_mdiff : MDiffAt (extChartAt I x) x :=
      mdifferentiableAt_extChartAt (I := I) (x := x) (mem_chart_source H x)
    exact hΓ_mdiff.comp x hphi_mdiff
  -- `e_m` is `MDiffAt x`.
  have hframe_diff : ∀ m : Fin (Module.finrank ℝ E),
      MDiffAt (T% (fun y : M => chartBasisVecFiber (I := I) x m y)) x :=
    fun m => chartBasisVec_alpha_mdifferentiableAt (I := I) x m
      (self_mem_chartLeviCivitaGoodSet (I := I) (α := x))
  -- Each `term m` is `MDiffAt x`.
  have hterm_diff : ∀ m : Fin (Module.finrank ℝ E), MDiffAt (T% (term m)) x :=
    fun m => MDifferentiableAt.smul_section (hΓc_diff m) (hframe_diff m)
  -- The sum of `term m` is `MDiffAt x`.
  have hsum_diff :
      MDiffAt (T% fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) x :=
    MDifferentiableAt.sum_section (s := Finset.univ) (t := term) hterm_diff
  -- `S` agrees with the sum near `x`, so `cov.toFun S = cov.toFun (sum)` at `x`.
  have hS_ev_sum :
      (fun y : M => S y) =ᶠ[𝓝 x]
        (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) := by
    filter_upwards [hU_open.mem_nhds hxU] with y hy using hS_eq_sum_on_U y hy
  have hcov_S_eq :
      cov.toFun S x =
        cov.toFun (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hS_diff hsum_diff
      Filter.univ_mem hS_ev_sum
  -- Now apply `cov.toFun S x (Xa x)` and substitute.
  rw [hS_def] at hcov_S_eq ⊢
  rw [hcov_S_eq, hXa_x]
  -- Finset linearity of `cov` in the section argument.
  have hsum_apply :
      (cov.toFun (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) x)
          (chartBasisVecFiber (I := I) x a x) =
        ∑ m : Fin (Module.finrank ℝ E),
          (cov.toFun (term m) x) (chartBasisVecFiber (I := I) x a x) := by
    have hfun :
        (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) =
          (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum term := by
      funext y; simp
    rw [hfun]
    exact leviCivita_finset_sum_apply (I := I) g
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))) term
      (chartBasisVecFiber (I := I) x a x) hterm_diff
  rw [hsum_apply]
  -- Leibniz on each frame term: `cov.toFun (Γc m • e_m) x (e_a) =
  --   (∂_a Γc m) • e_m(x) + Γc m (x) • cov.toFun e_m x (e_a)`.
  have hleib : ∀ m : Fin (Module.finrank ℝ E),
      (cov.toFun (term m) x) (chartBasisVecFiber (I := I) x a x) =
        extDerivFun (I := I) (Γc m) x (chartBasisVecFiber (I := I) x a x) •
            chartBasisVecFiber (I := I) x m x +
          Γc m x •
            (cov.toFun (fun y : M => chartBasisVecFiber (I := I) x m y) x)
              (chartBasisVecFiber (I := I) x a x) := by
    intro m
    have hleibniz := cov.isCovariantDerivativeOnUniv.leibniz
      (σ := fun y : M => chartBasisVecFiber (I := I) x m y) (g := Γc m) (x := x)
      (hframe_diff m) (hΓc_diff m)
    -- `term m = Γc m • e_m`.
    have hterm_eq : term m = (Γc m) • (fun y : M => chartBasisVecFiber (I := I) x m y) := by
      funext y; rfl
    rw [hterm_eq]
    have happ := congr($(hleibniz) (chartBasisVecFiber (I := I) x a x))
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply] at happ
    rw [happ]
    rw [add_comm]
  rw [Finset.sum_congr rfl (fun m _ => hleib m)]
  -- Substitute the chart values:
  --   `extDerivFun (Γc m) x (e_a) = ∂_a Γ^m_{bi}(φ x)`,
  --   `e_m(x) = chartModelBasis E m`,
  --   `Γc m x = Γ^m_{bi}(φ x)`,
  --   `cov.toFun e_m x (e_a) = ∑_l Γ^l_{am}(φ x) • e_l(x)` (chart-frame first formula).
  have hder : ∀ m : Fin (Module.finrank ℝ E),
      extDerivFun (I := I) (Γc m) x (chartBasisVecFiber (I := I) x a x) =
        partialDeriv (E := E) a (chartChristoffel (I := I) g x b i m) (extChartAt I x x) := by
    intro m
    -- `e_a x = chartModelBasis E a`.
    rw [chartBasisVecFiber_self (I := I) x a]
    -- `Γc m = (chartChristoffel … ) ∘ φ`.
    exact extDerivFun_comp_extChartAt_apply_basis (I := I) x
      (chartChristoffel_contDiffAt_self (I := I) g x b i m) a
  have hframe_x : ∀ m : Fin (Module.finrank ℝ E),
      chartBasisVecFiber (I := I) x m x = (chartModelBasis E) m :=
    fun m => chartBasisVecFiber_self (I := I) x m
  have hΓc_x : ∀ m : Fin (Module.finrank ℝ E),
      Γc m x = chartChristoffel (I := I) g x b i m (extChartAt I x x) := fun m => rfl
  have hinner : ∀ m : Fin (Module.finrank ℝ E),
      (cov.toFun (fun y : M => chartBasisVecFiber (I := I) x m y) x)
          (chartBasisVecFiber (I := I) x a x) =
        ∑ l : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g x a m l (extChartAt I x x) • (chartModelBasis E) l := by
    intro m
    have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
      self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
    rw [LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g x a m hx_good]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [chartBasisVecFiber_self (I := I) x l]
    rfl
  -- Assemble the final sum.
  rw [Finset.sum_congr rfl (fun m _ => by
    rw [hder m, hframe_x m, hΓc_x m, hinner m])]
  -- The remaining identity is a purely formal manipulation of finite sums of scalar
  -- multiples of the model basis vectors `e_l : TangentSpace I x`.
  -- Abbreviate the model basis vectors as a function `e`.
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun l => (chartModelBasis E) l with he_def
  -- Abbreviate the two scalar families.
  set D : Fin (Module.finrank ℝ E) → ℝ :=
    fun m => partialDeriv (E := E) a (chartChristoffel (I := I) g x b i m) (extChartAt I x x)
    with hD_def
  set Γq : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun m l => chartChristoffel (I := I) g x a m l (extChartAt I x x) with hΓq_def
  set Γr : Fin (Module.finrank ℝ E) → ℝ :=
    fun m => chartChristoffel (I := I) g x b i m (extChartAt I x x) with hΓr_def
  -- The goal now reads, in the abbreviations:
  --   ∑_m (D m • e m + Γr m • ∑_l Γq m l • e l)
  --     = ∑_l (D l + ∑_m Γq m l * Γr m) • e l.
  calc
    (∑ m : Fin (Module.finrank ℝ E),
        (D m • e m + Γr m • ∑ l : Fin (Module.finrank ℝ E), Γq m l • e l))
        = (∑ m : Fin (Module.finrank ℝ E), D m • e m) +
            (∑ m : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E), (Γr m * Γq m l) • e l) := by
          rw [Finset.sum_add_distrib]
          refine congrArg (fun t => (∑ m : Fin (Module.finrank ℝ E), D m • e m) + t) ?_
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [smul_smul]
      _ = (∑ l : Fin (Module.finrank ℝ E), D l • e l) +
            (∑ l : Fin (Module.finrank ℝ E),
              ∑ m : Fin (Module.finrank ℝ E), (Γr m * Γq m l) • e l) := by
          rw [Finset.sum_comm]
      _ = ∑ l : Fin (Module.finrank ℝ E),
            (D l + ∑ m : Fin (Module.finrank ℝ E), Γq m l * Γr m) • e l := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [← Finset.sum_smul, ← add_smul]
          congr 1
          refine congrArg (fun t => D l + t) ?_
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [mul_comm]

/-! ## Vanishing of the Lie bracket of two chart-basis fields at the basepoint

Coordinate basis fields commute, so the third term of the Riemann formula vanishes.
We prove this for the bumped global extensions, which agree with the chart-basis fields
on an open neighbourhood of `x`. -/

/-- The chart-trivialised representation of a tangent field that agrees with
`chartBasisVecFiber x j` on a neighbourhood of `x` has vanishing chart-pullback `fderiv`
at `φ x`. -/
lemma fderiv_chartE_section_repr_eq_zero_of_eventuallyEq [I.Boundaryless]
    (x : M) (j : Fin (Module.finrank ℝ E))
    {X : Π b : M, TangentSpace I b} {U : Set M}
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (hX_eq : ∀ y ∈ U, X y = chartBasisVecFiber (I := I) x j y) :
    fderiv ℝ (chartE_section_repr (I := I) x X ∘ (extChartAt I x).symm)
        (extChartAt I x x) = 0 := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  -- The two pullbacks agree near `φ x`.
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxsrc
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  -- `V := φ.symm ⁻¹' U ∩ target` is an open neighbourhood of `φ x` on which the pullbacks agree.
  have hcont_symm : ContinuousOn (extChartAt I x).symm (extChartAt I x).target :=
    continuousOn_extChartAt_symm x
  set V : Set E :=
    (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' U with hV_def
  have hxV : extChartAt I x x ∈ V := by
    refine ⟨hxtgt, ?_⟩
    rw [Set.mem_preimage, (extChartAt I x).left_inv hxsrc_ext]; exact hxU
  have hopen_V : IsOpen V :=
    ContinuousOn.isOpen_inter_preimage hcont_symm (isOpen_extChartAt_target (I := I) x) hU_open
  have hev :
      (chartE_section_repr (I := I) x X ∘ (extChartAt I x).symm) =ᶠ[𝓝 (extChartAt I x x)]
        (chartE_section_repr (I := I) x
          (fun b : M => chartBasisVecFiber (I := I) x j b) ∘ (extChartAt I x).symm) := by
    filter_upwards [hopen_V.mem_nhds hxV] with y hy
    obtain ⟨_hy_tgt, hy_pre⟩ := hy
    rw [Set.mem_preimage] at hy_pre
    change chartE_section_repr (I := I) x X ((extChartAt I x).symm y) =
      chartE_section_repr (I := I) x
        (fun b : M => chartBasisVecFiber (I := I) x j b) ((extChartAt I x).symm y)
    -- `chartE_section_repr x σ b` depends on `σ b` only; replace `X (φ.symm y)` by the basis.
    unfold chartE_section_repr
    rw [hX_eq ((extChartAt I x).symm y) hy_pre]
  rw [hev.fderiv_eq]
  exact fderiv_chartE_chartBasisVec_alpha_eq_zero (I := I) x j hx_good

/-- The Lie bracket of two tangent fields agreeing with the chart-basis fields `e_j, e_k`
on a neighbourhood of `x` vanishes at `x`. -/
lemma mlieBracket_chartBasisVec_ext_self_eq_zero [I.Boundaryless]
    (x : M) (j k : Fin (Module.finrank ℝ E))
    {Xj Xk : Π b : M, TangentSpace I b} {U : Set M}
    (hXj : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xj))
    (hXk : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xk))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (hXj_eq : ∀ y ∈ U, Xj y = chartBasisVecFiber (I := I) x j y)
    (hXk_eq : ∀ y ∈ U, Xk y = chartBasisVecFiber (I := I) x k y) :
    VectorField.mlieBracket I Xj Xk x = 0 := by
  classical
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxsrc
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  have hXj_at : MDiffAt (T% Xj) x := (hXj x).mdifferentiableAt (by simp)
  have hXk_at : MDiffAt (T% Xk) x := (hXk x).mdifferentiableAt (by simp)
  rw [mlieBracket_eq_chart_fderiv_diff (I := I) x Xj Xk hxint hXj_at hXk_at]
  rw [fderiv_chartE_section_repr_eq_zero_of_eventuallyEq (I := I) x k hU_open hxU hXk_eq]
  rw [fderiv_chartE_section_repr_eq_zero_of_eventuallyEq (I := I) x j hU_open hxU hXj_eq]
  rw [ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply]
  exact sub_self 0

/-! ## The basis-coordinate Riemann identity, unconditionally

We assemble the section-level Riemann formula. The third (Lie-bracket) term vanishes; the
two second-covariant-derivative terms produce, after using the symmetry of the Christoffel
symbol in its lower indices, exactly the chart Riemann tensor entries. -/

/-- **The basis identity on a single basis triple.** For the canonical model-basis triple
`(e_j, e_k, e_i)`, the abstract Riemann operator of the Levi-Civita connection agrees with
the chart Riemann CLM:
`riemannOp (LeviCivita g) x e_j e_k e_i = chartRiemannCLM g x e_j e_k e_i`. -/
lemma riemannOp_chartBasis_eq_chartRiemannCLM_basis [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    riemannOp (cov := LeviCivita (I := I) g) x
        ((chartModelBasis E) j) ((chartModelBasis E) k) ((chartModelBasis E) i) =
      chartRiemannCLM (I := I) g x
        ((chartModelBasis E) j) ((chartModelBasis E) k) ((chartModelBasis E) i) := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  -- Globally smooth bumped extensions of the three chart-basis fields.
  obtain ⟨Xj, Uj, hXj_sm, hUj_open, hxUj, hUj_good, hXj_eq⟩ :=
    exists_globalSmooth_chartBasisVec_ext (I := I) x j
  obtain ⟨Xk, Uk, hXk_sm, hUk_open, hxUk, hUk_good, hXk_eq⟩ :=
    exists_globalSmooth_chartBasisVec_ext (I := I) x k
  obtain ⟨Xi, Ui, hXi_sm, hUi_open, hxUi, hUi_good, hXi_eq⟩ :=
    exists_globalSmooth_chartBasisVec_ext (I := I) x i
  -- The common neighbourhood on which all three agree with the chart-basis fields.
  set U : Set M := Uj ∩ Uk ∩ Ui with hU_def
  have hU_open : IsOpen U := (hUj_open.inter hUk_open).inter hUi_open
  have hxU : x ∈ U := ⟨⟨hxUj, hxUk⟩, hxUi⟩
  have hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) x :=
    fun y hy => hUj_good hy.1.1
  have hXj_eqU : ∀ y ∈ U, Xj y = chartBasisVecFiber (I := I) x j y :=
    fun y hy => hXj_eq y hy.1.1
  have hXk_eqU : ∀ y ∈ U, Xk y = chartBasisVecFiber (I := I) x k y :=
    fun y hy => hXk_eq y hy.1.2
  have hXi_eqU : ∀ y ∈ U, Xi y = chartBasisVecFiber (I := I) x i y :=
    fun y hy => hXi_eq y hy.2
  -- Values of the extensions at `x` are the model-basis vectors.
  have hXj_x : Xj x = (chartModelBasis E) j := by
    rw [hXj_eqU x hxU, chartBasisVecFiber_self (I := I) x j]
  have hXk_x : Xk x = (chartModelBasis E) k := by
    rw [hXk_eqU x hxU, chartBasisVecFiber_self (I := I) x k]
  have hXi_x : Xi x = (chartModelBasis E) i := by
    rw [hXi_eqU x hxU, chartBasisVecFiber_self (I := I) x i]
  -- Replace the basis vectors by the smooth extensions' values and apply `riemannOp_apply_smooth`.
  rw [show ((chartModelBasis E) j : TangentSpace I x) = Xj x from hXj_x.symm,
      show ((chartModelBasis E) k : TangentSpace I x) = Xk x from hXk_x.symm,
      show ((chartModelBasis E) i : TangentSpace I x) = Xi x from hXi_x.symm]
  rw [riemannOp_apply_smooth (cov := cov) hXj_sm hXk_sm hXi_sm]
  -- Unfold the section-level Riemann formula.
  rw [riemannSec_def]
  -- Term 3 (Lie bracket) vanishes; substitute its arguments back to model-basis vectors.
  rw [mlieBracket_chartBasisVec_ext_self_eq_zero (I := I) x j k hXj_sm hXk_sm
    hU_open hxU hXj_eqU hXk_eqU]
  rw [ContinuousLinearMap.map_zero, sub_zero]
  -- Term 1 and Term 2 via the second covariant derivative formula (the slot vectors are
  -- `Xj x` resp. `Xk x`, which the formula handles internally).
  rw [LeviCivita_chartBasisVec_secondCovDeriv (I := I) g x j k i
    hXj_sm hXk_sm hXi_sm hU_open hxU hU_good hXj_eqU hXk_eqU hXi_eqU]
  rw [LeviCivita_chartBasisVec_secondCovDeriv (I := I) g x k j i
    hXk_sm hXj_sm hXi_sm hU_open hxU hU_good hXk_eqU hXj_eqU hXi_eqU]
  -- Match the chart side: substitute the basepoint values `Xj x = e_j`, `Xk x = e_k`,
  -- `Xi x = e_i` into the chart Riemann CLM, then evaluate on the basis triple.
  rw [hXj_x, hXk_x, hXi_x, chartRiemannCLM_basis_apply]
  -- Scalar coefficient identity at each index `l`, after reconciling the chart-Christoffel
  -- index conventions via the symmetry of the Christoffel symbol in its lower indices.
  have hcoeff : ∀ l : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) j (chartChristoffel (I := I) g x k i l) (extChartAt I x x) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x j m l (extChartAt I x x) *
              chartChristoffel (I := I) g x k i m (extChartAt I x x)) -
        (partialDeriv (E := E) k (chartChristoffel (I := I) g x j i l) (extChartAt I x x) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x k m l (extChartAt I x x) *
              chartChristoffel (I := I) g x j i m (extChartAt I x x)) =
      chartRiemannTensor (I := I) g x i j k l (extChartAt I x x) := by
    intro l
    rw [chartRiemannTensor_def]
    -- Partial-derivative terms: ∂_j Γ_{ki}^l = ∂_j Γ_{ik}^l, ∂_k Γ_{ji}^l = ∂_k Γ_{ij}^l.
    have hΓsym1 : (chartChristoffel (I := I) g x k i l) = (chartChristoffel (I := I) g x i k l) := by
      funext y; exact chartChristoffel_symm (I := I) g x k i l y
    have hΓsym2 : (chartChristoffel (I := I) g x j i l) = (chartChristoffel (I := I) g x i j l) := by
      funext y; exact chartChristoffel_symm (I := I) g x j i l y
    rw [hΓsym1, hΓsym2]
    -- Quadratic terms: pointwise Christoffel symmetry on the second factor.
    have hquad :
        (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x j m l (extChartAt I x x) *
              chartChristoffel (I := I) g x i k m (extChartAt I x x)) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x k m l (extChartAt I x x) *
              chartChristoffel (I := I) g x i j m (extChartAt I x x)) =
        ∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g x j m l (extChartAt I x x) *
              chartChristoffel (I := I) g x i k m (extChartAt I x x) -
            chartChristoffel (I := I) g x k m l (extChartAt I x x) *
              chartChristoffel (I := I) g x i j m (extChartAt I x x)) :=
      (Finset.sum_sub_distrib _ _).symm
    -- Reconcile the second factors of the quadratic sums (`Γ_{ki}^m = Γ_{ik}^m`,
    -- `Γ_{ji}^m = Γ_{ij}^m`) so the goal's quadratic difference matches the chart form.
    have hq1 : ∀ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x j m l (extChartAt I x x) *
            chartChristoffel (I := I) g x k i m (extChartAt I x x) =
          chartChristoffel (I := I) g x j m l (extChartAt I x x) *
            chartChristoffel (I := I) g x i k m (extChartAt I x x) := by
      intro m; rw [chartChristoffel_symm (I := I) g x k i m]
    have hq2 : ∀ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x k m l (extChartAt I x x) *
            chartChristoffel (I := I) g x j i m (extChartAt I x x) =
          chartChristoffel (I := I) g x k m l (extChartAt I x x) *
            chartChristoffel (I := I) g x i j m (extChartAt I x x) := by
      intro m; rw [chartChristoffel_symm (I := I) g x j i m]
    rw [Finset.sum_congr rfl (fun m _ => hq1 m), Finset.sum_congr rfl (fun m _ => hq2 m)]
    rw [← hquad]
    ring
  -- Conclude: both sides are `∑_l (coeff l) • e_l`; the LHS difference of sums collapses to a
  -- single sum (`Finset.sum_sub_distrib`), then each coefficient matches via `hcoeff`.
  refine (Finset.sum_sub_distrib _ _).symm.trans ?_
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← hcoeff l]
  exact (sub_smul _ _ _).symm

/-- **Unconditional discharge of `chartRiemannBasisIdentity`.** For every smooth Riemannian
metric `g` on a closed (boundaryless, σ-compact, Hausdorff) manifold and every point `x`,
the basis-coordinate identification of the abstract Riemann operator of the Levi-Civita
connection with the chart-Christoffel Riemann tensor holds. -/
theorem chartRiemannBasisIdentity_holds [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    chartRiemannBasisIdentity (I := I) g x := by
  rw [chartRiemannBasisIdentity_iff]
  intro i j k
  exact riemannOp_chartBasis_eq_chartRiemannCLM_basis (I := I) g x i j k

/-- **Unconditional trilinear bridge.** The abstract Riemann operator of the Levi-Civita
connection agrees with the chart Riemann CLM as trilinear maps, with no hypothesis:
`riemannOp (LeviCivita g) x v w u = chartRiemannCLM g x v w u` for all tangent vectors
`v, w, u`. -/
theorem riemannOp_eq_chartRiemannCLM_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x) :
    riemannOp (cov := LeviCivita (I := I) g) x v w u =
      chartRiemannCLM (I := I) g x v w u :=
  riemannOp_eq_chartRiemannCLM_apply_of_basis_identity (I := I) g x
    (chartRiemannBasisIdentity_holds (I := I) g x) v w u

end Connection
end Integral
end DifferentialGeometry

end
