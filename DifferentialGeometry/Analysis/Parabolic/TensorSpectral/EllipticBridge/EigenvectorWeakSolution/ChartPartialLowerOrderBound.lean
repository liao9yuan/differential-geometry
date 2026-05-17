import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.CovDerivComponentFormula
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ChristoffelBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.CanonicalTensorRepr

/-!
# A uniform `L²` bound for the partition-of-unity-weighted lower-order term

The lower-order term `covDerivLowerOrderTerm` of the chart-coordinate
covariant-derivative component formula is, by
`covDerivComponent_lowerOrder_eq_linearCombination`, a finite linear combination
of *undifferentiated* raw chart components of a section `S`, with `C^∞`
Christoffel coefficients `covDerivLowerOrderCoeff`. Built from the raw,
un-weighted chart component `tensorChartComponentRaw`, this term does not decay
at the (non-precompact) chart-target boundary, so its `L²` norm there is `⊤`.

Weighting by the pushed partition-of-unity weight `ρ_α` cures this: on the
chart target the weighted term equals a finite linear combination of the
*weighted* Euclidean chart components `tensorChartComponent`, each of which is
compactly supported inside the canonical compact partition-of-unity kernel and
carries an unconditional uniform-in-`S` order-0 `L²` bound
(`tensorChartComponent_eLpNorm_le_uniform`). The Christoffel coefficients are
uniformly bounded on that same compact kernel
(`chartChristoffel_bdd_on_pou_tsupport`); since each weighted chart component
vanishes off the kernel, the product of coefficient and component has its `L²`
norm controlled by the coefficient sup times the component `L²` norm. The
result is a single non-negative constant — depending only on `(g, r, s, α)`,
independent of `S` and of the component multi-indices — bounding the `L²` norm
of the partition-of-unity-weighted lower-order term summed over all
chart-coordinate directions.

## Main results

* `exists_const_sum_eLpNorm_pou_covDerivLowerOrderTerm_le_uniform` — the
  headline unconditional uniform `L²` bound for the partition-of-unity-weighted
  lower-order term.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
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

/-! ## The pushed partition-of-unity weight

The headline weight is `chartPushedRaw I α (⇑(chartAtlasPOU I M α))`, the
canonical partition-of-unity weight at `α` pushed to the Euclidean chart
target. On the chart target it is `ρ_α ∘ symm`, valued in `[0, 1]`. -/

/-- The closed support of the canonical partition-of-unity weight at `α`. -/
private def pouTsupport (α : M) : Set M :=
  tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)

/-! ## The Christoffel-coefficient sup bound on the partition-of-unity kernel

The lower-order coefficient `covDerivLowerOrderCoeff` is a finite combination
of the slot coefficients `inputSlotCoeff`, `outputSlotCoeff`. Each slot
coefficient factorises (`inputSlotCoeff_eq_entry_mul_const`,
`outputSlotCoeff_eq_entry_mul_const`) as a chart-frame matrix entry of the
chart Levi-Civita parallel CLM times a product of Kronecker deltas; that matrix
entry is a chart Christoffel symbol
(`chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel`), uniformly
bounded on the chart image of the partition-of-unity support
(`chartChristoffel_bdd_on_pou_tsupport`). -/

/-- A product of Kronecker deltas has absolute value at most `1`. -/
private lemma abs_prod_kronecker_le_one
    {ι : Type*} (t : Finset ι) (f : ι → Prop) [DecidablePred f] :
    |∏ i ∈ t, (if f i then (1 : ℝ) else 0)| ≤ 1 := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ih =>
      rw [Finset.prod_insert hi, abs_mul]
      by_cases hf : f i
      · rw [if_pos hf, abs_one, one_mul]; exact ih
      · rw [if_neg hf, abs_zero, zero_mul]; exact zero_le_one

/-- A Kronecker delta has absolute value at most `1`. -/
private lemma abs_kronecker_le_one {P : Prop} [Decidable P] :
    |if P then (1 : ℝ) else 0| ≤ 1 := by
  by_cases h : P
  · rw [if_pos h, abs_one]
  · rw [if_neg h, abs_zero]; exact zero_le_one

/-- The absolute value of a finite sum of `coefficient · Kronecker-delta`
products, with each coefficient bounded by `Cχ` in absolute value, is at most
`card · Cχ`. -/
private lemma abs_sum_coeff_kronecker_le
    {ι : Type*} (t : Finset ι) (f : ι → ℝ) (P : ι → Prop) [DecidablePred P]
    {Cχ : ℝ} (hCχ_nn : 0 ≤ Cχ) (hf : ∀ i ∈ t, |f i| ≤ Cχ) :
    |∑ i ∈ t, f i * (if P i then (1 : ℝ) else 0)| ≤ t.card * Cχ := by
  classical
  have hbound : ∀ i ∈ t,
      |f i * (if P i then (1 : ℝ) else 0)| ≤ Cχ := by
    intro i hi
    rw [abs_mul]
    calc |f i| * |if P i then (1 : ℝ) else 0|
        ≤ Cχ * 1 :=
          mul_le_mul (hf i hi) abs_kronecker_le_one (abs_nonneg _) hCχ_nn
      _ = Cχ := mul_one _
  calc |∑ i ∈ t, f i * (if P i then (1 : ℝ) else 0)|
      ≤ ∑ i ∈ t, |f i * (if P i then (1 : ℝ) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ t, Cχ := Finset.sum_le_sum hbound
    _ = t.card * Cχ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Uniform sup bound for `covDerivLowerOrderCoeff` on the partition-of-unity
kernel.** There is a single non-negative constant `C` such that for every
chart-coordinate direction `m`, every component multi-index pair, and every
Euclidean chart-target point `y` whose chart-Euclidean preimage lies in the
closed support of the canonical partition-of-unity weight at `α`, the
lower-order Christoffel coefficient `covDerivLowerOrderCoeff` is bounded in
absolute value by `C`. -/
private theorem exists_const_covDerivLowerOrderCoeff_bdd
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m : Fin (Module.finrank ℝ E))
        (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
        (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E))
        {y : EuclN},
        y ∈ chartTargetEuclid (I := I) (M := M) α →
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
          pouTsupport (I := I) (M := M) α →
        |covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
          Jdx Jdx' y| ≤ C := by
  classical
  -- The uniform Christoffel sup bound on the chart image of the POU support.
  obtain ⟨Cχ, hCχ_nn, hCχ⟩ :=
    chartChristoffel_bdd_on_pou_tsupport (I := I) (M := M) g α
  refine ⟨(r + s) * Cχ, by positivity, ?_⟩
  intro m Idx Idx' Jdx Jdx' y hy hb
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  -- `b` lies in the chart base set, so the chart-frame matrix entry of the
  -- parallel CLM is a chart Christoffel symbol.
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  -- `extChartAt I α b` lies in the chart image of the POU support.
  have himg : extChartAt I α b ∈ (extChartAt I α) ''
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    ⟨b, hb, rfl⟩
  -- Each input-slot coefficient is bounded by `Cχ`.
  have hinput : ∀ k : Fin r,
      |inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y| ≤ Cχ := by
    intro k
    rw [inputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g r α m k
      Idx Idx' hy,
      chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel
        (I := I) (M := M) g α hb_base m (Idx k) (Idx' k),
      abs_mul]
    calc |chartChristoffel (I := I) g α (Idx' k) m (Idx k)
              (extChartAt I α b)| *
            |∏ i ∈ Finset.univ.erase k,
              (if Idx' i = Idx i then (1 : ℝ) else 0)|
        ≤ Cχ * 1 := by
          refine mul_le_mul (hCχ _ himg _ _ _)
            (abs_prod_kronecker_le_one _ _) (abs_nonneg _) hCχ_nn
      _ = Cχ := mul_one _
  -- Each output-slot coefficient is bounded by `Cχ`.
  have houtput : ∀ l : Fin s,
      |outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y| ≤ Cχ := by
    intro l
    rw [outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g s α m l
      Jdx Jdx' hy,
      chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel
        (I := I) (M := M) g α hb_base m (Jdx' l) (Jdx l),
      abs_mul]
    calc |chartChristoffel (I := I) g α (Jdx l) m (Jdx' l)
              (extChartAt I α b)| *
            |∏ j ∈ Finset.univ.erase l,
              (if Jdx j = Jdx' j then (1 : ℝ) else 0)|
        ≤ Cχ * 1 := by
          refine mul_le_mul (hCχ _ himg _ _ _)
            (abs_prod_kronecker_le_one _ _) (abs_nonneg _) hCχ_nn
      _ = Cχ := mul_one _
  -- Bound the input contribution by `r · Cχ`.
  have hsum_input :
      |∑ k : Fin r,
          inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
            (if Jdx' = Jdx then (1 : ℝ) else 0)| ≤ r * Cχ := by
    have h := abs_sum_coeff_kronecker_le (Finset.univ : Finset (Fin r))
      (fun k => inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y)
      (fun _ => Jdx' = Jdx) hCχ_nn (fun k _ => hinput k)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  -- Bound the output contribution by `s · Cχ`.
  have hsum_output :
      |∑ l : Fin s,
          outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
            (if Idx' = Idx then (1 : ℝ) else 0)| ≤ s * Cχ := by
    have h := abs_sum_coeff_kronecker_le (Finset.univ : Finset (Fin s))
      (fun l => outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y)
      (fun _ => Idx' = Idx) hCχ_nn (fun l _ => houtput l)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  -- Assemble: `|input − output| ≤ |input| + |output| ≤ (r + s) · Cχ`.
  rw [covDerivLowerOrderCoeff_def]
  have habs_sub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
    intro a b
    calc |a - b| = |a + -b| := by rw [sub_eq_add_neg]
      _ ≤ |a| + |-b| := abs_add_le a (-b)
      _ = |a| + |b| := by rw [abs_neg]
  refine (habs_sub _ _).trans ?_
  have := add_le_add hsum_input hsum_output
  rw [add_mul]
  linarith

/-! ## The partition-of-unity factor folds the raw component into the weighted one

On the chart target, multiplying the pushed partition-of-unity weight into the
raw chart component recovers the weighted Euclidean chart component
`tensorChartComponent`: by construction
`tensorChartComponentPou = ρ_α · tensorChartComponentRaw`, and `chartPushedRaw`
is a pointwise pushforward on the chart target. -/

/-- On the chart target, the pushed partition-of-unity weight times the raw
chart component (read at the chart-Euclidean preimage) equals the weighted
Euclidean chart component `tensorChartComponent`. -/
private lemma chartPushedRaw_pou_mul_raw_eq_component
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
          (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx y := by
  classical
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) hy,
    tensorChartComponent_def,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx) hy]
  rfl

/-- On the chart target, the pushed partition-of-unity weight times the
lower-order term `covDerivLowerOrderTerm` equals the finite linear combination,
over component multi-index pairs, of `covDerivLowerOrderCoeff` times the
weighted Euclidean chart component `tensorChartComponent`. -/
private lemma chartPushedRaw_pou_mul_lowerOrderTerm_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
          (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y *
        covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
          tensorChartComponent (I := I) (M := M) g r s S α p.1 p.2 y := by
  classical
  rw [covDerivComponent_lowerOrder_eq_linearCombination
    (I := I) (M := M) g r s S α m Idx Jdx y, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  -- Pull the partition-of-unity factor onto the raw component, then fold.
  rw [← mul_assoc, mul_comm (chartPushedRaw (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y)
      (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y),
    mul_assoc,
    chartPushedRaw_pou_mul_raw_eq_component (I := I) (M := M) g r s S α
      p.1 p.2 hy]

/-! ## The `L²` bound for a single coefficient-component product

Each summand `covDerivLowerOrderCoeff · tensorChartComponent` of the weighted
lower-order term has its `L²` norm controlled by the coefficient sup on the
partition-of-unity kernel (off which the weighted chart component vanishes)
times the unconditional uniform component `L²` bound. -/

/-- The weighted Euclidean chart component is continuous on the Euclidean model
space. -/
private lemma tensorChartComponent_continuous'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) :=
  (tensorChartComponent_contMDiff (I := I) (M := M) g r s S α Idx Jdx).continuous

/-- If the weighted Euclidean chart component is nonzero at `y`, then `y` lies
in the chart target and its chart-Euclidean preimage lies in the closed support
of the canonical partition-of-unity weight at `α`. -/
private lemma mem_pouTsupport_of_tensorChartComponent_ne_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hne : tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx y ≠ 0) :
    y ∈ chartTargetEuclid (I := I) (M := M) α ∧
      (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        pouTsupport (I := I) (M := M) α := by
  classical
  -- First, `y` lies in the chart target: otherwise `chartPushedRaw` is zero.
  have hy : y ∈ chartTargetEuclid (I := I) (M := M) α := by
    by_contra hy
    exact hne (by
      rw [tensorChartComponent_def,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy])
  refine ⟨hy, ?_⟩
  -- On the chart target the component is `ρ_α(b) · raw(b)`; nonzero forces
  -- `ρ_α(b) ≠ 0`, hence `b ∈ tsupport ρ_α`.
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hval : tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx y =
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
    rw [tensorChartComponent_def,
      chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx) hy]
    rfl
  rw [hval] at hne
  have hρ_ne : (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b ≠ 0 := by
    intro hρ_zero
    exact hne (by rw [hρ_zero, zero_mul])
  exact subset_tsupport
    (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) hρ_ne

/-- **The `L²` bound for a single coefficient-component product.** For a fixed
component multi-index pair `p` and chart-coordinate direction `m`, the `L²`
norm of `covDerivLowerOrderCoeff · tensorChartComponent` against the Euclidean
volume restricted to the chart target is bounded by the Christoffel-coefficient
sup `Ccoeff` times the order-0 component `L²` norm. -/
private lemma eLpNorm_coeff_mul_component_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E))
    {Ccoeff : ℝ} (hCcoeff_nn : 0 ≤ Ccoeff)
    (hCcoeff : ∀ {y : EuclN},
      y ∈ chartTargetEuclid (I := I) (M := M) α →
      (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        pouTsupport (I := I) (M := M) α →
      |covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
        Jdx Jdx' y| ≤ Ccoeff) :
    eLpNorm
        (fun y : EuclN =>
          covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
              Jdx Jdx' y *
            tensorChartComponent (I := I) (M := M) g r s S α Idx' Jdx' y) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      ENNReal.ofReal Ccoeff *
        eLpNorm (tensorChartComponent (I := I) (M := M) g r s S α Idx' Jdx') 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set μ : Measure EuclN :=
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
  set comp : EuclN → ℝ :=
    tensorChartComponent (I := I) (M := M) g r s S α Idx' Jdx' with hcomp_def
  -- Pointwise: `|coeff y · comp y| ≤ |Ccoeff • comp y|`.
  have hpt : ∀ y : EuclN,
      ‖covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
            Jdx Jdx' y * comp y‖ ≤
        ‖(Ccoeff : ℝ) • comp y‖ := by
    intro y
    rw [Real.norm_eq_abs, abs_mul, smul_eq_mul, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg hCcoeff_nn]
    by_cases hcz : comp y = 0
    · rw [hcz, abs_zero, mul_zero, mul_zero]
    · -- `comp y ≠ 0` puts us inside the partition-of-unity kernel.
      obtain ⟨hy, hb⟩ :=
        mem_pouTsupport_of_tensorChartComponent_ne_zero
          (I := I) (M := M) g r s S α Idx' Jdx' (by rw [← hcomp_def]; exact hcz)
      exact mul_le_mul_of_nonneg_right (hCcoeff hy hb) (abs_nonneg _)
  -- `eLpNorm` is monotone in the pointwise norm; `Ccoeff • comp` pulls out.
  calc eLpNorm
          (fun y : EuclN =>
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
                Jdx Jdx' y * comp y) 2 μ
      ≤ eLpNorm ((Ccoeff : ℝ) • comp) 2 μ := eLpNorm_mono hpt
    _ = ‖(Ccoeff : ℝ)‖ₑ * eLpNorm comp 2 μ :=
        eLpNorm_const_smul (Ccoeff : ℝ) comp 2 _
    _ = ENNReal.ofReal Ccoeff * eLpNorm comp 2 μ := by
        rw [Real.enorm_eq_ofReal hCcoeff_nn]

/-! ## Assembling the bound over component multi-index pairs and directions

Summing the per-summand bound over the (finite) component multi-index pairs and
the (finite) chart-coordinate directions, and chaining the unconditional
uniform-in-`S` order-0 component `L²` bound, produces the headline. -/

/-- **A uniform `L²` bound for the partition-of-unity-weighted lower-order
term.** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, and a chart
center `α : M`, there is a single non-negative real constant `C` — depending
only on `(g, r, s, α)`, **independent of the section `S` and of the component
multi-indices `(Idx, Jdx)`** — such that for every smooth compactly-supported
`H¹` tensor section `S`, the `L²` norm (against the Euclidean volume restricted
to the chart target) of the pushed-partition-of-unity-weighted lower-order
correction term `covDerivLowerOrderTerm`, summed over all chart-coordinate
directions, is bounded by `ENNReal.ofReal C` times the `H¹` norm of `S`.

The pushed partition-of-unity weight `chartPushedRaw I α (⇑(chartAtlasPOU I M
α))` is essential: the raw (un-weighted) lower-order term does not decay at the
non-precompact chart-target boundary, so its un-weighted `L²` norm there is
infinite. The weight confines the term to the compact partition-of-unity
kernel, on which the Christoffel coefficients are uniformly bounded and the
weighted chart components carry an unconditional order-0 `L²` bound. -/
theorem exists_const_sum_eLpNorm_pou_covDerivLowerOrderTerm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      ∑ m : Fin (Module.finrank ℝ E),
        eLpNorm
          (fun y : EuclN =>
            chartPushedRaw (I := I) (M := M) α
                (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y *
              covDerivLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
                m Idx Jdx y) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  -- The uniform Christoffel-coefficient sup bound on the POU kernel.
  obtain ⟨Ccoeff, hCcoeff_nn, hCcoeff⟩ :=
    exists_const_covDerivLowerOrderCoeff_bdd (I := I) (M := M) g r s α
  -- The unconditional uniform-in-`S` order-0 component `L²` bound.
  obtain ⟨Ccomp, hCcomp_nn, hCcomp⟩ :=
    tensorChartComponent_eLpNorm_le_uniform (I := I) (M := M) g r s α
  -- The number of component multi-index pairs and chart-coordinate directions.
  set n : ℕ := Module.finrank ℝ E with hn_def
  set Npair : ℕ := Fintype.card ((Fin r → Fin n) × (Fin s → Fin n))
    with hNpair_def
  -- The headline constant.
  refine ⟨n * (Npair * (Ccoeff * Ccomp)), by positivity, ?_⟩
  intro S Idx Jdx
  -- Notation for the per-direction summand.
  set μ : Measure EuclN :=
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
    with hμ_def
  have hμ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  -- Per-direction bound: the weighted lower-order term has `L²` norm at most
  -- `Npair · Ccoeff · Ccomp · ‖S‖₊`.
  have hdir : ∀ m : Fin n,
      eLpNorm
          (fun y : EuclN =>
            chartPushedRaw (I := I) (M := M) α
                (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y *
              covDerivLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
                m Idx Jdx y) 2 μ ≤
        ENNReal.ofReal (Npair * (Ccoeff * Ccomp)) * (‖S‖₊ : ℝ≥0∞) := by
    intro m
    -- On the chart target the weighted lower-order term is the finite sum of
    -- coefficient-component product functions; rewrite `eLpNorm` via this a.e.
    -- equality (in sum-of-functions form, for the finite-sum triangle ineq).
    have hae :
        (fun y : EuclN =>
            chartPushedRaw (I := I) (M := M) α
                (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y *
              covDerivLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
                m Idx Jdx y)
          =ᵐ[μ]
        ∑ p : (Fin r → Fin n) × (Fin s → Fin n),
          (fun y : EuclN =>
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                Jdx p.2 y *
              tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α
                p.1 p.2 y) := by
      rw [hμ_def]
      refine (ae_restrict_iff' hμ_meas).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [Finset.sum_apply]
      exact chartPushedRaw_pou_mul_lowerOrderTerm_eq
        (I := I) (M := M) g r s S.toCcTensor α m Idx Jdx hy
    rw [eLpNorm_congr_ae hae]
    -- Each summand is `AEStronglyMeasurable`: a continuous-on-the-chart-target
    -- function against the volume restricted to that target.
    have hmeas : ∀ p : (Fin r → Fin n) × (Fin s → Fin n),
        AEStronglyMeasurable
          (fun y : EuclN =>
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                Jdx p.2 y *
              tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α
                p.1 p.2 y) μ := by
      intro p
      rw [hμ_def]
      have hcont_on : ContinuousOn
          (fun y : EuclN =>
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                Jdx p.2 y *
              tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α
                p.1 p.2 y)
          (chartTargetEuclid (I := I) (M := M) α) := by
        refine ContinuousOn.mul ?_ ?_
        · exact (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
            g r s α m Idx p.1 Jdx p.2).continuousOn
        · exact (tensorChartComponent_continuous' (I := I) (M := M)
            g r s S.toCcTensor α p.1 p.2).continuousOn
      exact hcont_on.aestronglyMeasurable hμ_meas
    -- The order-0 uniform-in-`S` component `L²` bound, restated against the
    -- `H¹` norm of `S` via `‖S.toCcTensor‖ ≤ ‖S‖`.
    have hcomp_h1 : ∀ p : (Fin r → Fin n) × (Fin s → Fin n),
        eLpNorm (tensorChartComponent (I := I) (M := M)
            g r s S.toCcTensor α p.1 p.2) 2 μ ≤
          ENNReal.ofReal Ccomp * (‖S‖₊ : ℝ≥0∞) := by
      intro p
      rw [hμ_def]
      have hb := hCcomp S.toCcTensor p.1 p.2
      rw [chartL2Measure] at hb
      refine hb.trans (mul_le_mul_of_nonneg_left ?_ (zero_le _))
      rw [show ((‖S‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖S‖ from by
        rw [show ((‖S‖₊ : ℝ≥0∞)) = ‖S‖ₑ from (enorm_eq_nnnorm S).symm,
          ← ofReal_norm_eq_enorm S]]
      exact ENNReal.ofReal_le_ofReal
        (SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S)
    -- Triangle inequality for finite sums, then per-summand bound: the
    -- coefficient sup bound chained with the order-0 component bound.
    have hsummand : ∀ p : (Fin r → Fin n) × (Fin s → Fin n),
        eLpNorm
            (fun y : EuclN =>
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                  Jdx p.2 y *
                tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α
                  p.1 p.2 y) 2 μ ≤
          ENNReal.ofReal (Ccoeff * Ccomp) * (‖S‖₊ : ℝ≥0∞) := by
      intro p
      have h1 :
          eLpNorm
              (fun y : EuclN =>
                covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                    Jdx p.2 y *
                  tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α
                    p.1 p.2 y) 2 μ ≤
            ENNReal.ofReal Ccoeff *
              eLpNorm (tensorChartComponent (I := I) (M := M)
                g r s S.toCcTensor α p.1 p.2) 2 μ := by
        rw [hμ_def]
        exact eLpNorm_coeff_mul_component_le (I := I) (M := M) g r s
          S.toCcTensor α m Idx p.1 Jdx p.2 hCcoeff_nn
          (fun {y} hy hb => hCcoeff m Idx p.1 Jdx p.2 hy hb)
      refine (h1.trans
        (mul_le_mul_of_nonneg_left (hcomp_h1 p) (zero_le _))).trans_eq ?_
      rw [ENNReal.ofReal_mul hCcoeff_nn, mul_assoc]
    refine (eLpNorm_sum_le (fun p _ => hmeas p) (by norm_num)).trans ?_
    -- Sum the per-summand bounds over the finite multi-index pairs.
    refine (Finset.sum_le_sum (fun p _ => hsummand p)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, ← hNpair_def, nsmul_eq_mul]
    rw [show ((Npair : ℝ≥0∞)) = ENNReal.ofReal (Npair : ℝ) from by
      rw [ENNReal.ofReal_natCast]]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  -- Sum the per-direction bounds over the finite chart-coordinate directions.
  refine (Finset.sum_le_sum (fun m _ => hdir m)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show ((n : ℝ≥0∞)) = ENNReal.ofReal (n : ℝ) from by
    rw [ENNReal.ofReal_natCast]]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
