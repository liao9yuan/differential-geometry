import DifferentialGeometry.Integral.Connection.ChartTensorRSSecondCovariantDerivative
import DifferentialGeometry.Integral.L2.SmoothSections.Defs

/-!
# Global smooth extension of the `(r,s)`-tensor covariant derivative along the chart
basis on the chart-α good set

For a smooth compactly-supported `(r, s)`-tensor section `T₀ : SmoothCcTensor g r s`, a
chart-centre `α : M`, and a coordinate index `k : Fin (Module.finrank ℝ E)`, the
fiber-valued tangent section `chartBasisVecFiber α k : Π x : M, TangentSpace I x` is
smooth only on the trivialization base set `(triv α).baseSet`; in particular it is
smooth on `chartLeviCivitaGoodSet α`. The pointwise raw section

  `S_k y := covApply cov_RS (chartBasisVecFiber α k) T₀.toSection y
          := (cov_RS).toFun T₀.toSection y (chartBasisVecFiber α k y)`

is therefore well-defined on all of `M` but only smooth on
`chartLeviCivitaGoodSet α`.

This file packages a *globally smooth bundle section* `S_k_ext` of the `(r, s)`-tensor
bundle that agrees with `S_k` on an open neighbourhood of any given chart-α good-set
point `b₀`. The construction multiplies the chart-basis tangent section by a
`SmoothBumpFunction I b₀` whose topological support lies inside
`chartLeviCivitaGoodSet α`; the bump is identically `1` on a neighbourhood of `b₀`,
so the covariant-derivative section based on the bumped tangent field coincides with
the un-bumped one on that neighbourhood.

## Main result

* `covApply_covRS_chartBasis_globalSmoothExtension` — the global smooth extension
  exists, witnessed together with the open neighbourhood `U ∋ b₀` of agreement.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open Tensor0SBundle

/-! ## A bump function supported in the chart-α good set, with value 1 near `b₀` -/

/-- For any chart-α good-set point `b₀`, there exists a smooth bump function based
at `b₀` whose topological support is contained in `chartLeviCivitaGoodSet α`. -/
private lemma exists_bump_tsupport_in_goodSet
    (α : M) {b₀ : M} (hb₀ : b₀ ∈ chartLeviCivitaGoodSet (I := I) α) :
    ∃ χ : SmoothBumpFunction I b₀,
      tsupport (fun y : M => (χ : M → ℝ) y) ⊆ chartLeviCivitaGoodSet (I := I) α := by
  classical
  -- The good set is an open neighbourhood of `b₀`.
  have hopen : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  have hnhds : chartLeviCivitaGoodSet (I := I) α ∈ 𝓝 b₀ := hopen.mem_nhds hb₀
  -- Extract a bump function with the required tsupport bound from
  -- `SmoothBumpFunction.nhds_basis_tsupport`.
  obtain ⟨χ, _, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) b₀).mem_iff.mp hnhds
  exact ⟨χ, hχ⟩

/-! ## The bumped chart-basis tangent field

The bumped chart-basis tangent field `χ • chartBasisVecFiber α k` is globally smooth
on `M`: on `chartLeviCivitaGoodSet α` it is smooth (because both `χ` and the
chart-basis field are smooth there, and `chartLeviCivitaGoodSet α ⊆ (triv α).baseSet`
where the chart-basis field is smooth); off `tsupport χ`, the bump vanishes, hence so
does the scaled field. The gluing is supplied by
`ContMDiffOn.smul_section_of_tsupport`. -/

private lemma bumpedChartBasis_contMDiff
    (α : M) {b₀ : M}
    (k : Fin (Module.finrank ℝ E))
    (χ : SmoothBumpFunction I b₀)
    (hχ_tsupp : tsupport (fun y : M => (χ : M → ℝ) y) ⊆
      chartLeviCivitaGoodSet (I := I) α) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y : M => (χ : M → ℝ) y • chartBasisVecFiber (I := I) α k y)) := by
  classical
  -- Smoothness of the chart-basis tangent field on the trivialization base set,
  -- which contains the chart-α good set.
  have hChart_baseSet : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (chartBasisVec (I := I) α k)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartBasisVec_contMDiffOn (I := I) α k
  -- Restrict to the chart-α good set.
  have hGood_sub_baseSet :
      chartLeviCivitaGoodSet (I := I) α ⊆
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro x hx
    exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hChart_on_good : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y : M => chartBasisVecFiber (I := I) α k y))
      (chartLeviCivitaGoodSet (I := I) α) :=
    hChart_baseSet.mono hGood_sub_baseSet
  -- The bump function is globally `C^∞`, hence smooth on the chart-α good set.
  have hχ_global : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (χ : M → ℝ) y) :=
    χ.contMDiff
  have hχ_on_good : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y : M => (χ : M → ℝ) y)
      (chartLeviCivitaGoodSet (I := I) α) :=
    hχ_global.contMDiffOn
  -- Apply the smooth-section smul-of-tsupport lemma. The bump's tsupport sits
  -- inside the open chart-α good set, and the section is smooth on that set.
  exact ContMDiffOn.smul_section_of_tsupport hχ_on_good
    (chartLeviCivitaGoodSet_isOpen (I := I) α) hχ_tsupp hChart_on_good

/-! ## The extension section

Given the bumped chart-basis field `X_ext := χ • chartBasisVecFiber α k`, the section
`covApply cov_RS X_ext T₀.toSection` is globally smooth via `covApply_contMDiffOn`.
On a neighbourhood of `b₀` where `χ = 1`, it agrees with the un-bumped section
`covApply cov_RS (chartBasisVecFiber α k) T₀.toSection`. -/

/-- **The global smooth extension.** For any chart-α good-set point `b₀`, there is a
globally smooth bundle section `S_k_ext` of the `(r, s)`-tensor bundle that agrees
on an open neighbourhood `U ∋ b₀` (with `U ⊆ chartLeviCivitaGoodSet α`) with the raw
section `y ↦ (cov_RS).toFun T₀.toSection y (chartBasisVecFiber α k y)`. -/
theorem covApply_covRS_chartBasis_globalSmoothExtension
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E))
    {b₀ : M} (hb₀ : b₀ ∈ chartLeviCivitaGoodSet (I := I) α) :
    ∃ (S_k_ext : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                       fun b : M => TensorRSSpace r s I b⟯),
      ∃ U : Set M, IsOpen U ∧ b₀ ∈ U ∧
        U ⊆ chartLeviCivitaGoodSet (I := I) α ∧
        ∀ y ∈ U,
          (S_k_ext : Π b : M, TensorRSSpace r s I b) y =
            covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
              (chartBasisVecFiber (I := I) α k) T₀.toSection y := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  -- Step 1: pick a smooth bump function based at `b₀` whose tsupport sits inside
  -- the chart-α good set.
  obtain ⟨χ, hχ_tsupp⟩ :=
    exists_bump_tsupport_in_goodSet (I := I) α (b₀ := b₀) hb₀
  -- Step 2: the bumped chart-basis tangent field is globally smooth.
  have hX_ext_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y : M => (χ : M → ℝ) y • chartBasisVecFiber (I := I) α k y)) :=
    bumpedChartBasis_contMDiff (I := I) α (b₀ := b₀) k χ hχ_tsupp
  -- Step 3: the underlying section `T₀.toSection` of `T₀` is smooth (`C^∞`).
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  have hT_smooth : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (T% (fun y : M => T₀.toSection y)) :=
    T₀.toSection.contMDiff
  -- Step 4: bump the smoothness witness of `T₀` from `∞` to `∞ + 1 = ∞`
  -- (the input convention of `covApply_contMDiffOn`).
  have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (T% (fun y : M => T₀.toSection y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hT_smooth
  -- Step 5: smoothness of `covApply cov X_ext T₀.toSection` over the whole
  -- manifold, supplied by `covApply_contMDiffOn`.
  have hSk_on : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (T% (fun y : M =>
        covApply cov
          (fun z : M => (χ : M → ℝ) z • chartBasisVecFiber (I := I) α k z)
          T₀.toSection y))
      Set.univ :=
    covApply_contMDiffOn (cov := cov) hX_ext_smooth hT_plus
  have hSk_global : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (T% (fun y : M =>
        covApply cov
          (fun z : M => (χ : M → ℝ) z • chartBasisVecFiber (I := I) α k z)
          T₀.toSection y)) := by
    intro y
    exact (hSk_on y (by trivial)).contMDiffAt (Filter.univ_mem)
  -- Step 6: package the global section as a `Cₛ^∞⟮…⟯` element.
  set S_k_ext : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      fun b : M => TensorRSSpace r s I b⟯ :=
    { toFun := fun y : M =>
        covApply cov
          (fun z : M => (χ : M → ℝ) z • chartBasisVecFiber (I := I) α k z)
          T₀.toSection y
      contMDiff_toFun := hSk_global } with hSk_def
  -- Step 7: choose the open neighbourhood `U` of `b₀` on which `χ ≡ 1`,
  -- intersected with the chart-α good set. On this `U`, the bumped tangent
  -- field agrees with the un-bumped one, hence so do the covariant-derivative
  -- sections.
  -- From the bump function: `χ =ᶠ[𝓝 b₀] 1` (`SmoothBumpFunction.eventuallyEq_one`).
  have hχ_eq_one_nhds : ∀ᶠ y in 𝓝 b₀, (χ : M → ℝ) y = 1 := χ.eventuallyEq_one
  obtain ⟨V_set, hV_nhds, hχ_one_V⟩ :=
    Filter.eventually_iff_exists_mem.mp hχ_eq_one_nhds
  obtain ⟨V_open, hV_sub_V_set, hV_open_isOpen, hb₀_in_V_open⟩ :=
    mem_nhds_iff.mp hV_nhds
  -- Intersect with the chart-α good set to get `U`.
  set U : Set M :=
    V_open ∩ chartLeviCivitaGoodSet (I := I) α with hU_def
  have hU_open : IsOpen U :=
    hV_open_isOpen.inter (chartLeviCivitaGoodSet_isOpen (I := I) α)
  have hb₀_U : b₀ ∈ U := ⟨hb₀_in_V_open, hb₀⟩
  have hU_sub_good : U ⊆ chartLeviCivitaGoodSet (I := I) α := by
    intro y hy
    exact hy.2
  refine ⟨S_k_ext, U, hU_open, hb₀_U, hU_sub_good, ?_⟩
  -- Step 8: on `U`, the values agree. At `y ∈ U`, `χ y = 1`, hence
  -- `χ y • chartBasisVecFiber α k y = chartBasisVecFiber α k y`, and the inner
  -- argument of `cov.toFun T₀.toSection y` agrees. By linearity (or by direct
  -- equality of arguments), the two `covApply` values agree.
  intro y hyU
  -- `χ y = 1` on `U` by the agreement set `V_set`.
  have hχ_one_y : (χ : M → ℝ) y = 1 := by
    have hy_V_set : y ∈ V_set := hV_sub_V_set hyU.1
    exact hχ_one_V y hy_V_set
  -- Compute the value of `S_k_ext` at `y`.
  have hS_k_val :
      (S_k_ext : Π b : M, TensorRSSpace r s I b) y =
        covApply cov
          (fun z : M => (χ : M → ℝ) z • chartBasisVecFiber (I := I) α k z)
          T₀.toSection y := rfl
  rw [hS_k_val]
  -- Unfold `covApply` on both sides.
  change cov.toFun T₀.toSection y
      ((fun z : M => (χ : M → ℝ) z • chartBasisVecFiber (I := I) α k z) y)
    = cov.toFun T₀.toSection y (chartBasisVecFiber (I := I) α k y)
  -- The inner argument simplifies via `χ y = 1`.
  have hinner :
      (fun z : M => (χ : M → ℝ) z • chartBasisVecFiber (I := I) α k z) y
        = chartBasisVecFiber (I := I) α k y := by
    change (χ : M → ℝ) y • chartBasisVecFiber (I := I) α k y
        = chartBasisVecFiber (I := I) α k y
    rw [hχ_one_y, one_smul]
  rw [hinner]

end Connection
end Integral
end DifferentialGeometry

end
