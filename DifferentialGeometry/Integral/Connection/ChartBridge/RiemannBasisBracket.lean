import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Integral.Connection.CurvatureBundling
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.VectorBundle.Frame
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Vanishing of the chart-basis Lie bracket at the base point

The chart-basis tangent-bundle sections `chartBasisVecFiber x₀ i` (defined in
`Integral.Measure.ChartDensity`) are obtained by transporting a fixed model-space basis
vector through the inverse of the tangent-bundle trivialization centred at `x₀`. On the
base set of that trivialization (which is the chart source `(chartAt H x₀).source`), the
chart pullback of such a section is *constant* — it equals the fixed model-space basis
vector. Consequently the manifold Lie bracket of any two chart-basis sections vanishes at
the base point: these are coordinate vector fields, and coordinate vector fields commute.

This is the chart-coordinate statement `[∂ⱼ, ∂ₖ](x₀) = 0`. It does **not** assert that the
Christoffel symbols vanish, only that the bracket of two coordinate frame fields is zero.

## Main results

* `chartBasisVecFiber_symmL_apply` — on the base set, `chartBasisVecFiber x₀ i x` is the
  image of the model-basis vector under the inverse trivialization `symmL`.
* `chartBasisVecFiber_pullback_eq_const` — the chart pullback of `chartBasisVecFiber x₀ i`
  through `(extChartAt I x₀).symm` is eventually constant near `extChartAt I x₀ x₀`.
* `mlieBracket_chartBasisVec_self_eq_zero` — the manifold Lie bracket of two chart-basis
  sections vanishes at the base point.

The construction mirrors `DifferentialGeometry.Coordinates.coordinateFrameAt_bracket_zero`
in `Coordinates.CoordinateFrame`, specialised to the `chartBasisVecFiber` carrier used by
the chart-Riemann bridge.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The base set of the tangent-bundle trivialization at `x₀` is the chart source. -/
private lemma chartBasis_baseSet_eq_chartSource (x₀ : M) :
    (trivializationAt E (TangentSpace I) x₀).baseSet = (chartAt H x₀).source := by
  rfl

/-- On the base set, the chart-basis fiber vector is the inverse trivialization `symmL`
applied to the fixed model-basis vector. This rewrites the bare `Trivialization.symm`
appearing in the definition of `chartBasisVecFiber` into the continuous-linear `symmL`
form, which `TangentBundle.symmL_trivializationAt` identifies with a chart derivative. -/
private lemma chartBasisVecFiber_symmL_apply (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    chartBasisVecFiber (I := I) x₀ i x =
      (trivializationAt E (TangentSpace I) x₀).symmL ℝ x ((chartModelBasis E) i) := by
  rw [Trivialization.symmL_apply]
  rfl

/-- On the chart domain, the chart-basis section is the derivative of `(extChartAt I x₀).symm`
applied to the fixed model-space basis vector. This is the analogue of
`Coordinates.coordinateFrameAt_apply_of_mem` for the `chartBasisVecFiber` carrier. -/
private lemma chartBasisVecFiber_apply_of_mem {x₀ x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) x₀ i x =
      (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x))
        ((chartModelBasis E) i) := by
  have hx_src : x ∈ (chartAt H x₀).source := by
    rwa [chartBasis_baseSet_eq_chartSource (I := I) x₀] at hx
  rw [chartBasisVecFiber_symmL_apply (I := I) x₀ i x]
  exact congrArg (fun L : E →L[ℝ] TangentSpace I x => L ((chartModelBasis E) i))
    (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := ℝ) hx_src)

/-- The chart pullback of the chart-basis section through `(extChartAt I x₀).symm` is
eventually equal, near `extChartAt I x₀ x₀`, to the constant model-space basis vector.
This expresses that `chartBasisVecFiber x₀ i` is a coordinate vector field. -/
private lemma chartBasisVecFiber_pullback_eq_const (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm
        (chartBasisVecFiber (I := I) x₀ i) (Set.range I)
      =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        fun _ : E => ((chartModelBasis E) i : E) := by
  haveI : IsManifold I (1 : WithTop ℕ∞) M :=
    IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
  simp only [VectorField.mpullbackWithin_apply]
  have hy_src : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hy
  have hy_base : (extChartAt I x₀).symm y ∈
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rwa [chartBasis_baseSet_eq_chartSource (I := I) x₀]
  rw [chartBasisVecFiber_apply_of_mem (I := I) hy_base i]
  rw [(extChartAt I x₀).right_inv hy]
  exact ContinuousLinearMap.IsInvertible.inverse_apply_self
    (isInvertible_mfderivWithin_extChartAt_symm (I := I) hy)
    ((chartModelBasis E) i)

/-- The Lie bracket within a set of two constant model-space vector fields vanishes. -/
private lemma lieBracketWithin_const_const {s : Set E} {x v w : E} :
    VectorField.lieBracketWithin ℝ (fun _ : E => v) (fun _ : E => w) s x = 0 := by
  simp [VectorField.lieBracketWithin]

/-- **Chart-basis bracket vanishing at the base point.**

The manifold Lie bracket of two chart-basis sections `chartBasisVecFiber x₀ j` and
`chartBasisVecFiber x₀ k` vanishes at the base point `x₀`: these are coordinate vector
fields, so they commute. This is the chart-coordinate statement `[∂ⱼ, ∂ₖ](x₀) = 0`. It is
the input that lets the section-level Riemann formula `riemannSec` drop its
`∇_{[X, Y]} Z` correction term when `X, Y` are chart-basis sections extending the canonical
model basis at `x₀`.

No Christoffel-vanishing claim is made here. -/
theorem mlieBracket_chartBasisVec_self_eq_zero (x₀ : M)
    (j k : Fin (Module.finrank ℝ E)) :
    VectorField.mlieBracket I
        (chartBasisVecFiber (I := I) x₀ j)
        (chartBasisVecFiber (I := I) x₀ k) x₀ = 0 := by
  rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_apply]
  have hleft :
      VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm
          (chartBasisVecFiber (I := I) x₀ j) (Set.range I)
        =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' Set.univ ∩ Set.range I]
            (extChartAt I x₀ x₀)]
          fun _ : E => ((chartModelBasis E) j : E) := by
    simpa using chartBasisVecFiber_pullback_eq_const (I := I) x₀ j
  have hright :
      VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm
          (chartBasisVecFiber (I := I) x₀ k) (Set.range I)
        =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' Set.univ ∩ Set.range I]
            (extChartAt I x₀ x₀)]
          fun _ : E => ((chartModelBasis E) k : E) := by
    simpa using chartBasisVecFiber_pullback_eq_const (I := I) x₀ k
  rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem hleft hright (by simp)]
  rw [lieBracketWithin_const_const]
  exact ContinuousLinearMap.map_zero _

/-! ## Globally-smooth chart-basis extensions and the bracket-free Riemann reduction

The chart-basis sections `chartBasisVecFiber x i` are smooth only on the trivialization
base set, so they are not directly admissible as inputs to the *global*-smoothness API of
the abstract Riemann operator (`riemannOp_apply_smooth`, `covApply_contMDiffOn`). We remedy
this by bump-extending them to *globally* smooth sections that agree with the chart-basis
sections on a neighborhood of the base point `x`. Neighborhood agreement is exactly what is
needed to:

* recover the basis value `e_i` at `x` (pointwise agreement);
* transfer the chart-basis bracket vanishing (`mlieBracket_chartBasisVec_self_eq_zero`,
  established above) to the extensions, since the manifold Lie bracket is a local operator;
* identify `riemannOp (LeviCivita g) x (e_j) (e_k) (e_i)` with the section-level Riemann
  formula `riemannSec` evaluated on the extensions.

Combining these, the section-level Riemann formula on the extensions drops its
`∇_{[X, Y]} Z` correction term, yielding the **bracket-free reduction** of the abstract
Riemann operator on the canonical basis triple. This is the entry point for the iterated
chart-Christoffel identification.
-/

/-- At the chart basepoint, the canonical tangent-bundle trivialization CLM is the
identity on `T_x M`. This is the manifold fact `continuousLinearMapAt_trivializationAt`
specialised to the diagonal, composed with `mfderiv_extChartAt_self`. -/
private lemma trivToE_self_eq_id (x : M) :
    (trivToE (I := I) x x : TangentSpace I x →L[ℝ] E) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  classical
  have h := TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
    (x₀ := x) (x := x) (mem_chart_source H x)
  rw [show (trivToE (I := I) x x : TangentSpace I x →L[ℝ] E) =
        (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x from rfl]
  rw [h]
  exact mfderiv_extChartAt_self (I := I) (x := x)

/-- At the chart basepoint, the inverse tangent-bundle trivialization is the identity. -/
private lemma trivFromE_self_apply (x : M) (w : E) :
    trivFromE (I := I) x x w = w := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have h := trivToE_trivFromE (I := I) x hbase w
  have hid : trivToE (I := I) x x (trivFromE (I := I) x x w) = trivFromE (I := I) x x w := by
    rw [trivToE_self_eq_id (I := I) x]; rfl
  rwa [hid] at h

/-- At the chart basepoint, the `i`-th chart-basis fibre vector equals the `i`-th
model-space basis vector. -/
private lemma chartBasisVecFiber_self_aux (x : M) (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) x i x = (chartModelBasis E) i := by
  rw [chartBasisVecFiber_symmL_apply (I := I) x i x]
  exact trivFromE_self_apply (I := I) x ((chartModelBasis E) i)

variable [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure

/-- **Existence of globally-smooth chart-basis extensions.** For the base point `x` there
exists a family of globally `C^∞` tangent-bundle sections `X i` that agrees with the
chart-basis sections `chartBasisVecFiber x i` on a neighborhood of `x`.

The construction bump-multiplies the chart-basis sections (smooth on the trivialization
base set by `chartBasisVec_contMDiffOn`) by a smooth bump function supported in the base
set, via `exists_contMDiffSection_eqOn_nhd`. The resulting sections are honest global
smooth sections of `TM` and coincide with the chart-basis sections near `x`. -/
theorem exists_smooth_chartBasisExtension (x : M) :
    ∃ X : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b,
      (∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (X i))) ∧
        (∀ᶠ b in 𝓝 x, ∀ i, X i b = chartBasisVecFiber (I := I) x i b) := by
  classical
  -- Each chart-basis section is `C^∞` on the trivialization base set, an open neighborhood
  -- of `x`. Apply the bump-extension lemma.
  have hbase_open : IsOpen (trivializationAt E (TangentSpace I) x).baseSet :=
    (trivializationAt E (TangentSpace I) x).open_baseSet
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x
  -- Smoothness of each carrier `fun b => chartBasisVecFiber x i b` on the base set,
  -- as a `ℕ∞`-degree `⊤ = ∞` smoothness (matching the frame-extension lemma's `n : ℕ∞`).
  have hs : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (T% (fun b : M => chartBasisVecFiber (I := I) x i b))
        (trivializationAt E (TangentSpace I) x).baseSet := by
    intro i
    have h := chartBasisVec_contMDiffOn (I := I) x i
    -- `chartBasisVec x i = T% (fun b => chartBasisVecFiber x i b)` definitionally, and
    -- `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`.
    simpa using h
  obtain ⟨s', hs'⟩ :=
    exists_contMDiffSection_eqOn_nhd (I := I) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      (s := fun i b => chartBasisVecFiber (I := I) x i b) hs hbase_open hx_base
  refine ⟨fun i b => s' i b, fun i => (s' i).contMDiff, ?_⟩
  filter_upwards [hs'] with b hb i using hb i

/-- **Bracket-free reduction of the abstract Riemann operator on the basis triple.** For any
family of globally-smooth tangent sections `X` agreeing with the chart-basis sections
`chartBasisVecFiber x ·` on a neighborhood of `x`, the abstract Riemann operator value
`riemannOp (LeviCivita g) x (e_j) (e_k) (e_i)` equals the *bracket-free* difference of the
iterated covariant derivatives
$$
  \nabla_{X_j}\!\bigl(\nabla_{X_k} X_i\bigr)(x) - \nabla_{X_k}\!\bigl(\nabla_{X_j} X_i\bigr)(x).
$$
The `∇_{[X_j, X_k]} X_i` correction term of the section-level Riemann formula drops because
`X_j, X_k` agree near `x` with the chart-basis (coordinate) vector fields, whose Lie bracket
vanishes at `x` (`mlieBracket_chartBasisVec_self_eq_zero`).

This is the bracket-eliminated entry point for the iterated chart-Christoffel identification
of `chartRiemannBasisIdentity`. -/
theorem LeviCivita_chartBasisVec_neighborhood_formula
    (g : SmoothRiemannianMetric I M) (x : M)
    {X : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hX : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (X i)))
    (hXnhds : ∀ᶠ b in 𝓝 x, ∀ i, X i b = chartBasisVecFiber (I := I) x i b)
    (i j k : Fin (Module.finrank ℝ E)) :
    riemannOp (cov := LeviCivita (I := I) g) x
        ((chartModelBasis E) j) ((chartModelBasis E) k)
        ((chartModelBasis E) i) =
      (LeviCivita (I := I) g).toFun
          (Connection.covApply (LeviCivita (I := I) g) (X k) (X i)) x (X j x) -
        (LeviCivita (I := I) g).toFun
          (Connection.covApply (LeviCivita (I := I) g) (X j) (X i)) x (X k x) := by
  classical
  -- Pointwise agreement at `x`: `X i x = chartBasisVecFiber x i x = (chartModelBasis E) i`.
  have hXx : ∀ i, X i x = (chartModelBasis E) i := by
    intro i
    have hb : ∀ i, X i x = chartBasisVecFiber (I := I) x i x := hXnhds.self_of_nhds
    rw [hb i, chartBasisVecFiber_self_aux (I := I) x i]
  -- Step 1: `riemannOp ... = riemannSec (LeviCivita g) (X j) (X k) (X i) x`.
  -- Replace each basis vector by `X _ x`, then apply `riemannOp_apply_smooth`.
  have hsec : riemannOp (cov := LeviCivita (I := I) g) x
      ((chartModelBasis E) j) ((chartModelBasis E) k) ((chartModelBasis E) i) =
      riemannSec (LeviCivita (I := I) g) (X j) (X k) (X i) x := by
    rw [show ((chartModelBasis E) j : TangentSpace I x) = X j x from (hXx j).symm,
        show ((chartModelBasis E) k : TangentSpace I x) = X k x from (hXx k).symm,
        show ((chartModelBasis E) i : TangentSpace I x) = X i x from (hXx i).symm]
    exact riemannOp_apply_smooth (cov := LeviCivita (I := I) g) (hX j) (hX k) (hX i)
  rw [hsec, riemannSec_def]
  -- Step 2: the bracket term `∇_{[X_j, X_k]} X_i (x)` vanishes.
  -- The bracket `mlieBracket I (X j) (X k) x` agrees with the chart-basis bracket at `x`
  -- by neighborhood agreement, and the latter is `0` by leaf A.
  have hXj_eq : (X j) =ᶠ[𝓝 x] chartBasisVecFiber (I := I) x j := by
    filter_upwards [hXnhds] with b hb using hb j
  have hXk_eq : (X k) =ᶠ[𝓝 x] chartBasisVecFiber (I := I) x k := by
    filter_upwards [hXnhds] with b hb using hb k
  have hbracket :
      VectorField.mlieBracket I (X j) (X k) x = 0 := by
    rw [Filter.EventuallyEq.mlieBracket_vectorField_eq (I := I) hXj_eq hXk_eq]
    exact mlieBracket_chartBasisVec_self_eq_zero (I := I) x j k
  rw [hbracket]
  -- The third term of `riemannSec` is `cov.toFun (X i) x 0 = 0`.
  rw [ContinuousLinearMap.map_zero, sub_zero]

end Connection
end Integral
end DifferentialGeometry
