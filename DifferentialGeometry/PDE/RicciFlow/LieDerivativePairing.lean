import DifferentialGeometry.PDE.RicciFlow.SmoothQuasilinear

/-!
# Smoothness of the metric Lie-derivative pairing on smooth tangent sections

For a smooth Riemannian metric `g`, a smooth tangent vector field `W`, and two smooth
tangent sections `Y, Z`, the scalar pairing
$$
  b \;\longmapsto\; (\mathcal L_W g)_b\bigl(Y_b, Z_b\bigr)
$$
is `C^\infty` on `M`.  This is the analogue of `ricciTensor_pairing_contMDiff` for
the metric Lie derivative.

## Strategy

The proof mirrors the local-frame trace-formula descent used for the Ricci pairing.
At every base point `b₀ ∈ M`, the trivialisation at `b₀` provides a smooth local
frame `e_i^{b₀}(b) := (\mathrm{triv}\,b_0).\mathrm{symmL}\,\mathbb R\,b\,(e_i)`.  On
the chart-`b₀` source we expand the smooth sections in this frame,
$$
  Y_b = \sum_i (\chartCoeff\,b_0\,Y\,i\,b)\;e_i^{b_0}(b), \qquad
  Z_b = \sum_j (\chartCoeff\,b_0\,Z\,j\,b)\;e_j^{b_0}(b),
$$
and use the bilinearity of `lieDerivMetric g W b` to reduce the pairing to a
finite linear combination of scalar functions of the form
`b ↦ chartCoeff b₀ Y i b · chartCoeff b₀ Z j b · lieDerivMetric g W b
  (chartFrameVec b₀ i b) (chartFrameVec b₀ j b)`.
Each factor is smooth on the chart-`b₀` source:

* the chart components `chartCoeff b₀ Y i` and `chartCoeff b₀ Z j` are smooth on the
  trivialisation base set (= chart source) by `chartCoeff_contMDiffOn`;
* the bilinear-form evaluation on the chart-frame vectors is smooth by
  `liederivmetric_chart_component_smooth_in_g_w_input`.

The product of finitely many smooth scalars is smooth, and the sum is smooth, so
the pairing is `ContMDiffAt` at every `b₀`.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- Pointwise identity:
`chartFrameVec α i b = chartBasisVecFiber α i b` at every base point `b`. Both
sides expand to `(trivializationAt E (TangentSpace I) α).symm b (chartModelBasis E i)`
as elements of `TangentSpace I b`; the only nominal difference is that
`chartFrameVec` invokes the continuous-linear-map coercion `symmL` of the bundle
symmetry, whose underlying function is the same `symm`. -/
lemma chartFrameVec_eq_chartBasisVecFiber
    (α : M) (i : Fin (Module.finrank ℝ E)) (b : M) :
    chartFrameVec (I := I) α i b = chartBasisVecFiber (I := I) α i b := rfl

/-- **Smoothness of the metric Lie-derivative pairing on smooth tangent sections.**
For a smooth Riemannian metric `g`, a smooth tangent vector field `W`, and two
smooth tangent sections `Y, Z`, the scalar function
`b ↦ lieDerivMetric g W b (Y b) (Z b)` is `C^∞` on `M`. -/
theorem lieDerivMetric_pairing_contMDiff
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => lieDerivMetric (I := I) g W b (Y b) (Z b)) := by
  classical
  -- Localise: it suffices to show `ContMDiffAt` at every `b₀ ∈ M`.
  intro b₀
  -- Trivialisation at `b₀`; its base set equals the chart source.
  set e := trivializationAt E (TangentSpace I : M → Type _) b₀ with he_def
  have h_baseSet_eq :
      (trivializationAt E (TangentSpace I) b₀).baseSet = (chartAt H b₀).source :=
    TangentBundle.trivializationAt_baseSet (I := I) b₀
  have hb₀_chartSrc : b₀ ∈ (chartAt H b₀).source := mem_chart_source H b₀
  have hb₀_baseSet : b₀ ∈ e.baseSet := by
    rw [he_def, h_baseSet_eq]; exact hb₀_chartSrc
  have h_chart_open : IsOpen ((chartAt H b₀).source) :=
    (chartAt H b₀).open_source
  have h_chart_nhd : (chartAt H b₀).source ∈ 𝓝 b₀ :=
    h_chart_open.mem_nhds hb₀_chartSrc
  -- Step 1.  Smoothness of each chart-component coefficient `chartCoeff b₀ Y i` and
  -- `chartCoeff b₀ Z j` on the chart source.
  have h_coeffY : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (chartCoeff (I := I) b₀ Y i) (chartAt H b₀).source := by
    intro i
    have h := chartCoeff_contMDiffOn (I := I) b₀ Y i
    rwa [h_baseSet_eq] at h
  have h_coeffZ : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (chartCoeff (I := I) b₀ Z j) (chartAt H b₀).source := by
    intro j
    have h := chartCoeff_contMDiffOn (I := I) b₀ Z j
    rwa [h_baseSet_eq] at h
  -- Step 2.  Smoothness of the chart-frame pairing on the chart source.
  have h_pair :
      ∀ i j : Fin (Module.finrank ℝ E),
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun b : M =>
            lieDerivMetric (I := I) g W b
              (chartFrameVec (I := I) b₀ i b) (chartFrameVec (I := I) b₀ j b))
          (chartAt H b₀).source := fun i j =>
    liederivmetric_chart_component_smooth_in_g_w_input (I := I) g W b₀ i j
  -- Step 3.  On the chart source, expand `lieDerivMetric g W b (Y b) (Z b)` via the
  -- decomposition `Y b = ∑_i chartCoeff b₀ Y i b • chartBasisVecFiber b₀ i b` (and
  -- similarly for `Z b`) and the bilinearity of `lieDerivMetric g W b`.
  have h_decomp : ∀ b ∈ (chartAt H b₀).source,
      lieDerivMetric (I := I) g W b (Y b) (Z b) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartCoeff (I := I) b₀ Y i b *
              chartCoeff (I := I) b₀ Z j b *
              lieDerivMetric (I := I) g W b
                (chartFrameVec (I := I) b₀ i b)
                (chartFrameVec (I := I) b₀ j b) := by
    intro b hb_chart
    have hb_baseSet : b ∈ e.baseSet := by
      rw [he_def, h_baseSet_eq]; exact hb_chart
    -- Decompose `Y b` and `Z b` in the chart-basis frame attached to `b₀`.
    have hY_decomp : Y b =
        ∑ i, chartCoeff (I := I) b₀ Y i b •
          chartBasisVecFiber (I := I) b₀ i b :=
      chartCoeff_recompose (I := I) b₀ Y hb_baseSet
    have hZ_decomp : Z b =
        ∑ j, chartCoeff (I := I) b₀ Z j b •
          chartBasisVecFiber (I := I) b₀ j b :=
      chartCoeff_recompose (I := I) b₀ Z hb_baseSet
    -- Expand the bilinear form by linearity in each slot.  `lieDerivMetric g W b`
    -- is a `LinearMap.mk₂`, hence linear in `(v, w)`.
    set B : TangentSpace I b →ₗ[ℝ] TangentSpace I b →ₗ[ℝ] ℝ :=
      lieDerivMetric (I := I) g W b with hB_def
    have hB_sum_left : ∀ (w : TangentSpace I b)
        (f : Fin (Module.finrank ℝ E) → ℝ)
        (v : Fin (Module.finrank ℝ E) → TangentSpace I b),
        B (∑ i, f i • v i) w = ∑ i, f i * B (v i) w := by
      intro w f v
      classical
      induction Finset.univ (α := Fin (Module.finrank ℝ E)) using Finset.induction_on with
      | empty =>
        simp
      | insert hk ih =>
        rename_i k s
        rw [Finset.sum_insert hk, Finset.sum_insert hk]
        rw [map_add, LinearMap.add_apply, ih]
        rw [LinearMap.map_smul, LinearMap.smul_apply]
        rw [smul_eq_mul]
    have hB_sum_right : ∀ (v : TangentSpace I b)
        (f : Fin (Module.finrank ℝ E) → ℝ)
        (w : Fin (Module.finrank ℝ E) → TangentSpace I b),
        B v (∑ j, f j • w j) = ∑ j, f j * B v (w j) := by
      intro v f w
      classical
      induction Finset.univ (α := Fin (Module.finrank ℝ E)) using Finset.induction_on with
      | empty =>
        simp
      | insert hk ih =>
        rename_i k s
        rw [Finset.sum_insert hk, Finset.sum_insert hk]
        rw [LinearMap.map_add, ih, LinearMap.map_smul, smul_eq_mul]
    -- Now compute.
    rw [hY_decomp]
    rw [show (B (∑ i, chartCoeff (I := I) b₀ Y i b •
              chartBasisVecFiber (I := I) b₀ i b)) (Z b) =
        ∑ i, chartCoeff (I := I) b₀ Y i b *
          B (chartBasisVecFiber (I := I) b₀ i b) (Z b) from
      hB_sum_left (Z b) (fun i => chartCoeff (I := I) b₀ Y i b)
        (fun i => chartBasisVecFiber (I := I) b₀ i b)]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hZ_decomp]
    rw [show B (chartBasisVecFiber (I := I) b₀ i b)
          (∑ j, chartCoeff (I := I) b₀ Z j b •
            chartBasisVecFiber (I := I) b₀ j b) =
        ∑ j, chartCoeff (I := I) b₀ Z j b *
          B (chartBasisVecFiber (I := I) b₀ i b)
            (chartBasisVecFiber (I := I) b₀ j b) from
      hB_sum_right (chartBasisVecFiber (I := I) b₀ i b)
        (fun j => chartCoeff (I := I) b₀ Z j b)
        (fun j => chartBasisVecFiber (I := I) b₀ j b)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    -- `chartFrameVec α i b = chartBasisVecFiber α i b` definitionally.
    rw [show chartFrameVec (I := I) b₀ i b = chartBasisVecFiber (I := I) b₀ i b from rfl,
        show chartFrameVec (I := I) b₀ j b = chartBasisVecFiber (I := I) b₀ j b from rfl]
    ring
  -- Step 4.  Smoothness of the sum on the chart source.
  have h_summand_smooth :
      ∀ i j : Fin (Module.finrank ℝ E),
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun b : M =>
            chartCoeff (I := I) b₀ Y i b *
              chartCoeff (I := I) b₀ Z j b *
              lieDerivMetric (I := I) g W b
                (chartFrameVec (I := I) b₀ i b)
                (chartFrameVec (I := I) b₀ j b))
          (chartAt H b₀).source := by
    intro i j
    exact ((h_coeffY i).mul (h_coeffZ j)).mul (h_pair i j)
  have h_sum_smooth :
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun b : M =>
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartCoeff (I := I) b₀ Y i b *
                chartCoeff (I := I) b₀ Z j b *
                lieDerivMetric (I := I) g W b
                  (chartFrameVec (I := I) b₀ i b)
                  (chartFrameVec (I := I) b₀ j b))
        (chartAt H b₀).source := by
    refine contMDiffOn_finset_sum (fun i _ => ?_)
    exact contMDiffOn_finset_sum (fun j _ => h_summand_smooth i j)
  -- Step 5.  Glue: by `h_decomp`, the pairing equals the sum on the chart source;
  -- transfer smoothness via `ContMDiffOn.congr` and conclude `ContMDiffAt` at `b₀`.
  have h_pair_on_chart :
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun b : M => lieDerivMetric (I := I) g W b (Y b) (Z b))
        (chartAt H b₀).source :=
    h_sum_smooth.congr (fun b hb => (h_decomp b hb).symm)
  exact (h_pair_on_chart b₀ hb₀_chartSrc).contMDiffAt h_chart_nhd

end RicciFlow
end PDE
end DifferentialGeometry
