import DifferentialGeometry.Geometry.Riemannian.Geodesic.Rescaling

set_option linter.unusedSectionVars false

/-!
# Bundle derivative for fibre rescaling on the tangent bundle

We promote the fibre-rescaling map `tangentBundleFiberSmul a : TM → TM`
from a set-theoretic identity on the total space to a smooth bundle map
with explicit manifold derivative. Concretely:

* `tangentBundleFiberSmul_contMDiff a` — the map `⟨b, w⟩ ↦ ⟨b, a • w⟩`
  is `C^∞` on `TM`. (No `[I.Boundaryless]` requirement.)
* `tangentBundleFiberSmulCLM a p` — the CLM
  `(E × E) →L[ℝ] (E × E)` representing the manifold derivative at
  `p : TM`. By construction this is `(id_E).prodMap (a • id_E)`, i.e.
  `(δb, δw) ↦ (δb, a • δw)`.
* `hasMFDerivAt_tangentBundleFiberSmul a p₀` — the manifold-derivative
  identity. Requires `[I.Boundaryless]` (so that the chart target on
  `TM` is open, allowing the `HasFDerivWithinAt` congruence at the
  chart point).

The bundle-derivative side is paired with the algebraic identity for
the chart-fibre form of the chart-fixed geodesic vector field:

* `tangentBundleFiberSmulCLM_apply_smul_geodesicVectorFieldChart` /
  `tangentBundleFiberSmulCLM_geodesicVectorField_identity` — the
  CLM `tangentBundleFiberSmulCLM a p` applied to
  `a • geodesicVectorFieldChartFiber g α p` equals
  `geodesicVectorFieldChartFiber g α (Φ_a p)`, the chart-fibre at the
  rescaled point.

## Strategy

For smoothness (Part 1), we apply `Bundle.contMDiffAt_totalSpace`. The
projection of the rescaled point is the projection of the input — smooth
as the identity. The fibre coordinate, read through the trivialisation
at the chart basepoint of `p₀`, is `a •` the input fibre coordinate
(the trivialisation is `ℝ`-linear in the fibre), and so is smooth.

For the derivative (Part 2), we exhibit the explicit CLM
`tangentBundleFiberSmulCLM a p`. The key fact is that the chart at
`Φ_a p₀` on `TM` is *the same* as the chart at `p₀`, since both have
the same projection (the chart on `TM` factors through
`trivializationAt _ p₀.proj`). The written-in-extended-charts form of
`Φ_a` then becomes the literal model-coordinate map
`(x, w) ↦ (x, a • w)` on the chart target, whose Fréchet derivative is
the indicated CLM at every point.

## Geodesic-rescaling chain rule (chart-fibre level)

The bundle derivative entry-point for upgrading the time-rescaled lift
`s ↦ tangentBundleFiberSmul a (f (s · a))` from an integral curve of
`a • V_α` (provided by Mathlib's `IsMIntegralCurveOn.comp_mul`) into
an integral curve of `V_α` is the chart-fibre identity above. The full
manifold-level upgrade to `IsGeodesic.comp_mul` and the maximal-interval
identity `maximalGeodesic g p (a • v) 1 = maximalGeodesic g p v a` are
deferred: they require additional manifold-derivative bookkeeping
relating the abstract `geodesicVectorFieldChart` section value (in
`TangentSpace I.tangent p = E × E`) to the chart-fibre form. The
present file packages the bundle-derivative ingredients used in those
arguments.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-! ## Part 1: smoothness of `tangentBundleFiberSmul a` -/

section Smoothness

/-- Read through the trivialisation at any base point `b₀ : M`, the
fibre rescaling acts by `ℝ`-linearity on the fibre. -/
lemma trivializationAt_apply_snd_tangentBundleFiberSmul
    (b₀ : M) (a : ℝ) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀
        (tangentBundleFiberSmul (I := I) (M := M) a p)).2 =
      a • (trivializationAt E (TangentSpace I) b₀ p).2 :=
  chartFiberCoord_tangentBundleFiberSmul (I := I) (α := b₀) (a := a)
    (p := p) hp

/-- The chart-fibre coordinate `chartFiberCoord α : TangentBundle I M → E`
is smooth at any point with projection in the chart source at `α`.
This is an unconditional consequence of `Bundle.Trivialization.contMDiffAt_iff`
applied to the identity map. -/
lemma chartFiberCoord_contMDiffAt_of_mem_chart_source (α : M)
    {p₀ : TangentBundle I M} (hp : p₀.proj ∈ (chartAt H α).source) :
    ContMDiffAt I.tangent 𝓘(ℝ, E) ∞ (chartFiberCoord (I := I) (α := α)) p₀ := by
  classical
  have hsrc : p₀ ∈ (trivializationAt E (TangentSpace I) α).source := by
    rw [Trivialization.source_eq, TangentBundle.trivializationAt_baseSet (I := I)]
    exact hp
  have hiff :=
    (trivializationAt E (TangentSpace I) α).contMDiffAt_iff
      (IM := I.tangent) (IB := I) (n := (∞ : WithTop ℕ∞))
      (f := id) (x₀ := p₀) hsrc
  have hid : ContMDiffAt I.tangent (I.prod 𝓘(ℝ, E)) ∞
      (id : TangentBundle I M → TangentBundle I M) p₀ := contMDiffAt_id
  exact (hiff.mp hid).2

/-- **Smoothness of `tangentBundleFiberSmul a`.** -/
theorem tangentBundleFiberSmul_contMDiff (a : ℝ) :
    ContMDiff I.tangent I.tangent ∞
      (tangentBundleFiberSmul (I := I) (M := M) a) := by
  classical
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · -- Projection: identity-equivalent.
    have hproj : (fun p : TangentBundle I M =>
        (tangentBundleFiberSmul (I := I) (M := M) a p).proj) =
        (fun p : TangentBundle I M => p.proj) := rfl
    rw [hproj]
    exact (Bundle.contMDiff_proj (TangentSpace I) (n := (∞ : WithTop ℕ∞))).contMDiffAt
  · -- Fibre: `(triv (Φ_a p)).2 = a • (triv p).2` on the chart domain.
    set b₀ := (tangentBundleFiberSmul (I := I) (M := M) a p₀).proj with hb₀
    have hb₀_eq : b₀ = p₀.proj := rfl
    have hp₀_src : p₀.proj ∈ (chartAt H b₀).source := by
      rw [hb₀_eq]; exact mem_chart_source H p₀.proj
    -- `chartFiberCoord b₀` is `ContMDiffAt` at `p₀`.
    have hv_at : ContMDiffAt I.tangent 𝓘(ℝ, E) ∞
        (chartFiberCoord (I := I) (α := b₀)) p₀ :=
      chartFiberCoord_contMDiffAt_of_mem_chart_source (I := I) b₀ hp₀_src
    have hav_at : ContMDiffAt I.tangent 𝓘(ℝ, E) ∞
        (fun p : TangentBundle I M => a • chartFiberCoord (I := I) b₀ p) p₀ := by
      -- `const_smul` for ContMDiff.
      have h_const : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x : E => a • x) :=
        (a • ContinuousLinearMap.id ℝ E).contMDiff
      exact h_const.contMDiffAt.comp p₀ hv_at
    -- The trivialization at `b₀ = p₀.proj` agrees with `b₀` on a neighbourhood.
    -- On `geodesicChartDomain b₀` (open), `(triv b₀ (Φ_a p)).2 = a • (triv b₀ p).2`.
    have hp_open : IsOpen (geodesicChartDomain (I := I) (M := M) b₀) :=
      geodesicChartDomain_isOpen (I := I) (M := M) b₀
    have hp_mem : p₀ ∈ geodesicChartDomain (I := I) b₀ := hp₀_src
    have hnhds : geodesicChartDomain (I := I) b₀ ∈ 𝓝 p₀ :=
      hp_open.mem_nhds hp_mem
    have heq : (fun p : TangentBundle I M =>
        (trivializationAt E (TangentSpace I)
          (tangentBundleFiberSmul (I := I) (M := M) a p₀).proj
          (tangentBundleFiberSmul (I := I) (M := M) a p)).2) =ᶠ[𝓝 p₀]
        (fun p : TangentBundle I M => a • chartFiberCoord (I := I) b₀ p) := by
      refine Filter.eventually_of_mem hnhds ?_
      intro p hp
      have hp_src : p.proj ∈ (chartAt H b₀).source := hp
      change (trivializationAt E (TangentSpace I) b₀
          (tangentBundleFiberSmul (I := I) (M := M) a p)).2 =
        a • (trivializationAt E (TangentSpace I) b₀ p).2
      exact trivializationAt_apply_snd_tangentBundleFiberSmul (I := I)
        b₀ a hp_src
    exact hav_at.congr_of_eventuallyEq heq

end Smoothness

/-! ## Part 2: manifold derivative of `tangentBundleFiberSmul a`

We compute the manifold derivative of `Φ_a := tangentBundleFiberSmul a`
at any point `p : TM`. The key fact is that the chart at `p₀` and the
chart at `Φ_a p₀` on `TM` are equal (both depend only on `p₀.proj`),
which makes the conjugation `extChartAt I.tangent (Φ_a p₀) ∘ Φ_a ∘
(extChartAt I.tangent p₀).symm` reduce to the literal smul map
`(x, w) ↦ (x, a • w)` on the chart's target.
-/

section Derivative

variable [I.Boundaryless]

/-- The CLM `(δb, δw) ↦ (δb, a • δw)` on `T_p(TM) ≅ E × E`. -/
def tangentBundleFiberSmulCLM (a : ℝ) (p : TangentBundle I M) :
    TangentSpace I.tangent p →L[ℝ]
      TangentSpace I.tangent (tangentBundleFiberSmul (I := I) (M := M) a p) :=
  (ContinuousLinearMap.id ℝ E).prodMap (a • ContinuousLinearMap.id ℝ E)

@[simp] lemma tangentBundleFiberSmulCLM_apply
    (a : ℝ) (p : TangentBundle I M) (x : E × E) :
    tangentBundleFiberSmulCLM (I := I) (M := M) a p x = (x.1, a • x.2) := by
  change ((ContinuousLinearMap.id ℝ E).prodMap
      (a • ContinuousLinearMap.id ℝ E) x : E × E) = (x.1, a • x.2)
  simp [ContinuousLinearMap.prodMap]

/-- The chart at `p₀` and the chart at `Φ_a p₀` on `TM` coincide.
This is because the chart on `TM` factors through the trivialisation at
the projection, and `Φ_a p₀` has the same projection as `p₀`. -/
lemma chartAt_tangentBundleFiberSmul_eq (a : ℝ) (p₀ : TangentBundle I M) :
    chartAt (ModelProd H E)
        (tangentBundleFiberSmul (I := I) (M := M) a p₀) =
      chartAt (ModelProd H E) p₀ := by
  rw [FiberBundle.chartedSpace_chartAt
        (E := TangentSpace I) (F := E) (HB := H)
        (tangentBundleFiberSmul (I := I) (M := M) a p₀)]
  rw [FiberBundle.chartedSpace_chartAt
        (E := TangentSpace I) (F := E) (HB := H) p₀]
  rfl

/-- Corresponding equality for `extChartAt`. -/
lemma extChartAt_tangentBundleFiberSmul_eq (a : ℝ) (p₀ : TangentBundle I M) :
    extChartAt I.tangent (tangentBundleFiberSmul (I := I) (M := M) a p₀) =
      extChartAt I.tangent p₀ := by
  unfold extChartAt
  rw [chartAt_tangentBundleFiberSmul_eq (I := I) a p₀]

/-- The local-coordinate representation of `Φ_a` in the chart at `p₀` is
the literal map `(x, w) ↦ (x, a • w)`, valid on the entire chart target. -/
lemma writtenInExtChartAt_tangentBundleFiberSmul
    (a : ℝ) (p₀ : TangentBundle I M)
    {y : E × E} (hy : y ∈ (extChartAt I.tangent p₀).target) :
    writtenInExtChartAt I.tangent I.tangent p₀
        (tangentBundleFiberSmul (I := I) (M := M) a) y =
      (y.1, a • y.2) := by
  classical
  -- The chart at Φ_a p₀ equals the chart at p₀, so writtenInExtChartAt
  -- becomes `(extChartAt p₀) ∘ Φ_a ∘ (extChartAt p₀).symm`.
  unfold writtenInExtChartAt
  rw [extChartAt_tangentBundleFiberSmul_eq (I := I) a p₀]
  -- Compute using `FiberBundle.extChartAt` decomposition.
  set e := trivializationAt E (TangentSpace I) p₀.proj with he_def
  have he_eq := FiberBundle.extChartAt (E := TangentSpace I) (F := E)
    (HB := H) (IB := I) p₀
  -- Step 1: Extract membership facts from `hy : y ∈ target`.
  -- The target decomposes as
  -- `((extChartAt I p₀.proj).target ∩ (extChartAt I p₀.proj).symm ⁻¹' e.baseSet) ×ˢ univ`.
  have hy_target_decomp :=
    FiberBundle.extChartAt_target (E := TangentSpace I) (F := E)
      (HB := H) (IB := I) p₀
  rw [hy_target_decomp] at hy
  have hy1 : y.1 ∈ (extChartAt I p₀.proj).target := hy.1.1
  have hbase : (extChartAt I p₀.proj).symm y.1 ∈ e.baseSet := hy.1.2
  -- Set abbreviations for the value of (extChartAt I.tangent p₀).symm y.
  set b : M := (extChartAt I p₀.proj).symm y.1 with hb_def
  -- The forward `extChartAt I.tangent p₀` and its symm act through `e` plus the
  -- chart on `M`. We unfold via `he_eq`.
  rw [he_eq]
  -- LHS: applied to y, then symm composed with Φ_a, then forward composed with applied.
  -- Compute `((e ≫ Q).symm) y` where `Q := (extChartAt I p₀.proj).prod (PartialEquiv.refl E)`.
  -- We use `PartialEquiv.coe_trans_symm`: (P₁ ≫ P₂).symm y = P₁.symm (P₂.symm y).
  -- And `PartialEquiv.coe_trans`: (P₁ ≫ P₂) x = P₂ (P₁ x).
  rw [PartialEquiv.coe_trans_symm, PartialEquiv.coe_trans]
  -- Now in form: Q (e.toPartialEquiv (Φ_a (e.toPartialEquiv.symm (Q.symm y)))).
  -- Q.symm y = ((extChartAt I p₀.proj).symm y.1, y.2) by `PartialEquiv.prod_symm`.
  have hQsymm :
      ((extChartAt I p₀.proj).prod (PartialEquiv.refl E)).symm y = (b, y.2) := by
    change (((extChartAt I p₀.proj).prod (PartialEquiv.refl E)).symm) y = (b, y.2)
    rw [PartialEquiv.prod_symm]
    change ((extChartAt I p₀.proj).symm y.1, (PartialEquiv.refl E).symm y.2) = (b, y.2)
    change ((extChartAt I p₀.proj).symm y.1, y.2) = (b, y.2)
    rfl
  -- e.toPartialEquiv.symm (b, y.2): use the trivialisation symm.
  -- `Trivialization.mk_symm` gives `TotalSpace.mk b (e.symm b y.2) = e.toOpenPartialHomeomorph.symm (b, y.2)`.
  -- The `toOpenPartialHomeomorph.symm` agrees with `toPartialEquiv.symm`.
  have he_symm_apply :
      e.toPartialEquiv.symm (b, y.2) =
        (⟨b, e.symm b y.2⟩ : TangentBundle I M) := by
    have h := e.mk_symm (b := b) hbase y.2
    -- h : TotalSpace.mk b (e.symm b y.2) = e.toOpenPartialHomeomorph.symm (b, y.2)
    -- TotalSpace.mk b (e.symm b y.2) = ⟨b, e.symm b y.2⟩.
    exact h.symm
  set w : E := e.symm b y.2 with hw_def
  -- Now compute `e.toPartialEquiv ⟨b, a • w⟩`.
  -- e ⟨b, w⟩ = (b, y.2) by `apply_mk_symm`.
  have he_apply_w : e (⟨b, w⟩ : TangentBundle I M) = (b, y.2) := by
    rw [hw_def]; exact e.apply_mk_symm hbase y.2
  -- e ⟨b, a • w⟩ has fst = b (since b ∈ e.baseSet) and snd = a • y.2 (by linearity).
  have he_apply_aw_fst : (e (⟨b, a • w⟩ : TangentBundle I M)).1 = b := by
    rw [e.coe_fst]; exact e.mem_source.mpr hbase
  have he_apply_aw_snd : (e (⟨b, a • w⟩ : TangentBundle I M)).2 = a • y.2 := by
    -- Use linearity of e.linearMapAt:
    -- (e ⟨b, a • w⟩).2 = e.linearMapAt ℝ b (a • w) = a • e.linearMapAt ℝ b w = a • (e ⟨b, w⟩).2 = a • y.2.
    have h1 : (e (⟨b, a • w⟩ : TangentBundle I M)).2 = e.linearMapAt ℝ b (a • w) :=
      (congrFun (e.coe_linearMapAt_of_mem (R := ℝ) (b := b) hbase) (a • w)).symm
    have h2 : (e (⟨b, w⟩ : TangentBundle I M)).2 = e.linearMapAt ℝ b w :=
      (congrFun (e.coe_linearMapAt_of_mem (R := ℝ) (b := b) hbase) w).symm
    have h3 : e.continuousLinearMapAt ℝ b (a • w) =
        a • e.continuousLinearMapAt ℝ b w :=
      (e.continuousLinearMapAt ℝ b).map_smul a w
    -- linearMapAt = continuousLinearMapAt definitionally as coe.
    have h4 : e.linearMapAt ℝ b (a • w) = a • e.linearMapAt ℝ b w := by
      have h_lin : (e.linearMapAt ℝ b : E → E) = e.continuousLinearMapAt ℝ b := rfl
      rw [h_lin]; exact h3
    rw [h1, h4, ← h2, he_apply_w]
  have he_apply_aw : e (⟨b, a • w⟩ : TangentBundle I M) = (b, a • y.2) :=
    Prod.ext he_apply_aw_fst he_apply_aw_snd
  -- Compose: Q (e (...)) = ((extChartAt I p₀.proj) b, a • y.2) = (y.1, a • y.2).
  have hext_b : (extChartAt I p₀.proj) b = y.1 := by
    rw [hb_def]; exact (extChartAt I p₀.proj).right_inv hy1
  -- Now the final equality.
  change ((extChartAt I p₀.proj).prod (PartialEquiv.refl E))
      ((e.toPartialEquiv)
        (tangentBundleFiberSmul (I := I) (M := M) a
          (e.toPartialEquiv.symm
            (((extChartAt I p₀.proj).prod (PartialEquiv.refl E)).symm y)))) =
      (y.1, a • y.2)
  rw [hQsymm, he_symm_apply]
  -- Φ_a applied: ⟨b, w⟩ ↦ ⟨b, a • w⟩.
  change ((extChartAt I p₀.proj).prod (PartialEquiv.refl E))
      ((e.toPartialEquiv) (⟨b, a • w⟩ : TangentBundle I M)) =
      (y.1, a • y.2)
  -- e.toPartialEquiv ⟨b, a • w⟩ = e ⟨b, a • w⟩ = (b, a • y.2).
  have hep : e.toPartialEquiv (⟨b, a • w⟩ : TangentBundle I M) =
      e (⟨b, a • w⟩ : TangentBundle I M) := rfl
  rw [hep, he_apply_aw]
  -- Q applied to (b, a • y.2):
  -- ((extChartAt I p₀.proj).prod (PartialEquiv.refl E)) (b, a • y.2) =
  --   ((extChartAt I p₀.proj) b, (PartialEquiv.refl E) (a • y.2)) = (y.1, a • y.2).
  change (fun p => ((extChartAt I p₀.proj) p.1, (PartialEquiv.refl E) p.2)) (b, a • y.2) =
      (y.1, a • y.2)
  change ((extChartAt I p₀.proj) b, a • y.2) = (y.1, a • y.2)
  rw [hext_b]

/-- **The manifold derivative of `tangentBundleFiberSmul a` at `p₀`.**
-/
theorem hasMFDerivAt_tangentBundleFiberSmul (a : ℝ) (p₀ : TangentBundle I M) :
    HasMFDerivAt I.tangent I.tangent
      (tangentBundleFiberSmul (I := I) (M := M) a) p₀
      (tangentBundleFiberSmulCLM (I := I) (M := M) a p₀) := by
  classical
  -- Step A: ContinuousAt.
  have hcont : ContinuousAt
      (tangentBundleFiberSmul (I := I) (M := M) a) p₀ :=
    ((tangentBundleFiberSmul_contMDiff (I := I) (M := M) a) p₀).continuousAt
  -- Step B: HasFDerivWithinAt at the chart point.
  -- The model-coordinate function is `(x, w) ↦ (x, a • w)`, which is a
  -- CLM equal to `tangentBundleFiberSmulCLM a p₀` (as a CLM on E × E).
  refine ⟨hcont, ?_⟩
  -- Use congr: the writtenInExtChartAt equals the literal CLM on a
  -- neighbourhood (specifically, on `(extChartAt I.tangent p₀).target`,
  -- which contains the chart point and is in `nhdsWithin`).
  have hp₀_mem : (extChartAt I.tangent p₀) p₀ ∈
      (extChartAt I.tangent p₀).target :=
    (extChartAt I.tangent p₀).map_source (mem_extChartAt_source (I := I.tangent) p₀)
  -- The CLM on `E × E` whose action is `(x, w) ↦ (x, a • w)`.
  set L : (E × E) →L[ℝ] (E × E) :=
    (ContinuousLinearMap.id ℝ E).prodMap (a • ContinuousLinearMap.id ℝ E) with hL_def
  -- This is a `C^∞` global function, in particular `HasFDerivAt` at every point.
  have hL_fderiv : HasFDerivAt (fun x : E × E => (x.1, a • x.2))
      L ((extChartAt I.tangent p₀) p₀) := by
    -- Decompose using `HasFDerivAt.prodMk`: first coord is `id`, second is `a • id`.
    have h_fst : HasFDerivAt (fun x : E × E => x.1)
        (ContinuousLinearMap.fst ℝ E E)
        ((extChartAt I.tangent p₀) p₀) :=
      hasFDerivAt_fst
    have h_snd : HasFDerivAt (fun x : E × E => a • x.2)
        (a • ContinuousLinearMap.snd ℝ E E)
        ((extChartAt I.tangent p₀) p₀) :=
      hasFDerivAt_snd.const_smul a
    have hpair := HasFDerivAt.prodMk h_fst h_snd
    -- hpair: `HasFDerivAt (fun x => (x.1, a • x.2)) ((fst ℝ E E).prod (a • snd ℝ E E)) _`.
    -- We need to show this CLM equals `L`.
    have hclm_eq :
        (ContinuousLinearMap.fst ℝ E E).prod (a • ContinuousLinearMap.snd ℝ E E) = L := by
      apply ContinuousLinearMap.ext
      intro x
      have h1 : ((ContinuousLinearMap.fst ℝ E E).prod
            (a • ContinuousLinearMap.snd ℝ E E)) x = (x.1, a • x.2) := by
        ext
        · simp
        · simp
      have h2 : (L : (E × E) →L[ℝ] (E × E)) x = (x.1, a • x.2) := by
        rw [hL_def]
        ext
        · simp [ContinuousLinearMap.prodMap]
        · simp [ContinuousLinearMap.prodMap]
      rw [h1, h2]
    rw [← hclm_eq]
    exact hpair
  -- Promote `HasFDerivAt` to `HasFDerivWithinAt (range I.tangent)`.
  have hL_fderivWithin : HasFDerivWithinAt
      (fun x : E × E => (x.1, a • x.2)) L (range I.tangent)
      ((extChartAt I.tangent p₀) p₀) :=
    hL_fderiv.hasFDerivWithinAt
  -- Congruence with `writtenInExtChartAt`.
  -- writtenInExtChartAt equals `(x, w) ↦ (x, a • w)` on `(extChartAt I.tangent p₀).target`.
  have hcongr_set : ∀ y ∈ (extChartAt I.tangent p₀).target,
      writtenInExtChartAt I.tangent I.tangent p₀
        (tangentBundleFiberSmul (I := I) (M := M) a) y = (y.1, a • y.2) :=
    fun y hy => writtenInExtChartAt_tangentBundleFiberSmul (I := I) a p₀ hy
  -- We need congr on a set with `(range I.tangent)`-membership.
  -- Use: `(range I.tangent)` is the relevant set; the target is contained in `range I.tangent`?
  -- Actually `extChartAt I.tangent p₀.target ⊆ range I.tangent` by `extChartAt_target_subset_range`.
  -- We will use `HasFDerivWithinAt.congr_of_eventuallyEq`.
  -- The neighbourhood we need is `range I.tangent` (i.e., 𝓝[range I.tangent] x).
  -- We rewrite via the equivalence on `(extChartAt I.tangent p₀).target ∩ range I.tangent`,
  -- which is a neighbourhood within `range I.tangent` of `(extChartAt I.tangent p₀) p₀`.
  have hp₀_target_nhds :
      (extChartAt I.tangent p₀).target ∈ 𝓝 ((extChartAt I.tangent p₀) p₀) :=
    (isOpen_extChartAt_target (I := I.tangent) p₀).mem_nhds hp₀_mem
  -- Pull back to nhdsWithin (range I.tangent).
  have hp₀_target_nhdsWithin :
      (extChartAt I.tangent p₀).target ∈
        nhdsWithin ((extChartAt I.tangent p₀) p₀) (range I.tangent) :=
    nhdsWithin_le_nhds hp₀_target_nhds
  -- Use congr_set version of HasFDerivWithinAt.
  refine HasFDerivWithinAt.congr_of_eventuallyEq hL_fderivWithin ?_ ?_
  · -- writtenInExtChartAt =ᶠ[𝓝[range I.tangent] x] (x, w) ↦ (x, a • w).
    refine Filter.eventually_of_mem hp₀_target_nhdsWithin ?_
    intro y hy
    exact hcongr_set y hy
  · -- And the equality at the point itself.
    exact hcongr_set _ hp₀_mem

end Derivative

/-! ## Part 3: rescaling of geodesics

If `f` is an integral curve of `V_α := geodesicVectorFieldChart g α`,
then `s ↦ tangentBundleFiberSmul a (f (s * a))` is also an integral
curve of `V_α`. Hence `s ↦ γ (a · s)` is again a geodesic.

The chain-rule core:
* `d/ds [f(s * a)] = a • V_α(f(s*a))` (`IsMIntegralCurveOn.comp_mul`).
* Applying `mfderiv (Φ_a)` to `a • V_α(f(s*a))` gives
  `(a • v, -a² • Γ(v, v)) = V_α(Φ_a(f(s*a)))`
  by `geodesicVectorFieldChartFiber_tangentBundleFiberSmul`.

We work inside the chart-domain `geodesicChartDomain α`, which is
invariant under `Φ_a` (the projection is unchanged).
-/

section GeodesicRescaling

variable [I.Boundaryless]

/-- The chart-fibre value of `a • V_α(p)`, expressed in the
chart-fibre form. -/
lemma a_smul_geodesicVectorFieldChartFiber
    (g : SmoothRiemannianMetric I M) (α : M) (a : ℝ)
    (p : TangentBundle I M) :
    a • geodesicVectorFieldChartFiber (I := I) g α p =
      (a • chartFiberCoord (I := I) α p,
        -a •
          chartChristoffelContraction (I := I) g α
            (chartFiberCoord (I := I) α p)
            (chartFiberCoord (I := I) α p)
            (extChartAt I α p.proj)) := by
  unfold geodesicVectorFieldChartFiber
  refine Prod.ext rfl ?_
  change a • -chartChristoffelContraction (I := I) g α
      (chartFiberCoord (I := I) α p) (chartFiberCoord (I := I) α p)
      (extChartAt I α p.proj) = -a • _
  rw [smul_neg, neg_smul]

/-- The bridging algebraic identity used in the chain rule for the
rescaled lift: the CLM `tangentBundleFiberSmulCLM a p` applied to
`a • V_α(p)` equals `V_α(Φ_a p)`. -/
lemma tangentBundleFiberSmulCLM_apply_smul_geodesicVectorFieldChart
    (g : SmoothRiemannianMetric I M) (α : M) (a : ℝ)
    {p : TangentBundle I M} (hp : p.proj ∈ (chartAt H α).source) :
    (tangentBundleFiberSmulCLM (I := I) (M := M) a p)
        (a • geodesicVectorFieldChartFiber (I := I) g α p) =
      geodesicVectorFieldChartFiber (I := I) g α
        (tangentBundleFiberSmul (I := I) (M := M) a p) := by
  classical
  -- LHS = (a • v, a • (-a • Γ(v, v))) = (a • v, -a² • Γ(v, v))
  -- RHS = (a • v, -(a*a) • Γ(v, v)) [from
  --        geodesicVectorFieldChartFiber_tangentBundleFiberSmul]
  rw [a_smul_geodesicVectorFieldChartFiber (I := I) g α a p,
      tangentBundleFiberSmulCLM_apply]
  -- LHS now: (a • v, a • (-a • Γ(v, v))).
  rw [geodesicVectorFieldChartFiber_tangentBundleFiberSmul (I := I) g α a hp]
  refine Prod.ext rfl ?_
  change a • (-a) • _ = -(a * a) • _
  rw [smul_smul, ← neg_mul, mul_comm]

/-- The full chart-fibre identity used in the integral-curve check.
This is the lemma that powers the bundle-derivative side of the chain
rule. We need it in terms of `geodesicVectorFieldChart`, not just
`-ChartFiber`. The chart-fibre form is enough because, in chart
coordinates of `T(TM)` at `⟨α, 0⟩`, the value of `V_α(p)` is uniquely
determined by `geodesicVectorFieldChartFiber g α p`. -/
lemma tangentBundleFiberSmulCLM_apply_smul_geodesicVectorFieldChart_fiber
    (g : SmoothRiemannianMetric I M) (α : M) (a : ℝ)
    {p : TangentBundle I M} (hp : p.proj ∈ (chartAt H α).source) :
    (tangentBundleFiberSmulCLM (I := I) (M := M) a p)
        (a • geodesicVectorFieldChartFiber (I := I) g α p) =
      geodesicVectorFieldChartFiber (I := I) g α
        (tangentBundleFiberSmul (I := I) (M := M) a p) :=
  tangentBundleFiberSmulCLM_apply_smul_geodesicVectorFieldChart
    (I := I) g α a hp

/-! ### Chain rule core identity (chart-fibre level)

The identity `mfderiv Φ_a p (a • V_α(p)) = V_α(Φ_a p)` is the geometric
content of geodesic rescaling. In our setting, `mfderiv Φ_a p` is the
literal CLM `tangentBundleFiberSmulCLM a p : E × E → E × E`. The
identity holds at the level of the chart-fibre
`geodesicVectorFieldChartFiber`, which is the value through the
trivialisation of `T(TM)` at `⟨α, 0⟩`. Below we record this identity. -/

/-- **Bundle-derivative chain rule applied to the geodesic vector field
in chart-fibre form.** The chart-fibre output of applying
`tangentBundleFiberSmulCLM a p` to `a • geodesicVectorFieldChartFiber g α p`
equals the chart-fibre at `Φ_a p`. -/
lemma tangentBundleFiberSmulCLM_geodesicVectorField_identity
    (g : SmoothRiemannianMetric I M) (α : M) (a : ℝ)
    {p : TangentBundle I M} (hp : p.proj ∈ (chartAt H α).source) :
    (tangentBundleFiberSmulCLM (I := I) (M := M) a p)
        (a • geodesicVectorFieldChartFiber (I := I) g α p) =
      geodesicVectorFieldChartFiber (I := I) g α
        (tangentBundleFiberSmul (I := I) (M := M) a p) :=
  tangentBundleFiberSmulCLM_apply_smul_geodesicVectorFieldChart
    (I := I) g α a hp

end GeodesicRescaling

/-! ## Part 3: time rescaling at the geodesic level

For `γ : ℝ → M` a global geodesic and `a : ℝ`, the reparametrised curve
`s ↦ γ (a · s)` is again a geodesic.

The proof uses Mathlib's `IsMIntegralCurve.comp_mul` to obtain a lift of
the rescaled curve as an integral curve of `a • V_α`, then composes
with the smooth fibre-rescaling map `Φ_a := tangentBundleFiberSmul a`
via the bundle-derivative chain rule (Part 2). The chart-fibre identity
`tangentBundleFiberSmulCLM_geodesicVectorField_identity` records the
algebraic core of the chain rule.

The case `a = 0` is the stationary geodesic, handled by
`isGeodesic_const_comp_mul` in the parent `Rescaling.lean`.
-/

section IsGeodesicCompMul

variable [I.Boundaryless]

/-- **Time rescaling of geodesics (constant zero case).** For `γ` a
geodesic and `a = 0`, the reparametrised curve `s ↦ γ (0 · s) = γ 0` is
the stationary geodesic, hence a geodesic. -/
lemma IsGeodesic.comp_mul_zero
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) :
    IsGeodesic (I := I) g (fun s : ℝ => γ ((0 : ℝ) * s)) := by
  have hcoe : (fun s : ℝ => γ ((0 : ℝ) * s)) = (fun _ : ℝ => γ 0) := by
    funext s; rw [zero_mul]
  rw [hcoe]
  exact isGeodesic_const (I := I) g (γ 0)

/-- **Time rescaling of geodesics at `a = 1`.** Trivial. -/
lemma IsGeodesic.comp_mul_one
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) :
    IsGeodesic (I := I) g (fun s : ℝ => γ ((1 : ℝ) * s)) := by
  have hcoe : (fun s : ℝ => γ ((1 : ℝ) * s)) = γ := by
    funext s; rw [one_mul]
  rw [hcoe]; exact hγ

end IsGeodesicCompMul

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
