import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import DifferentialGeometry.Integral.Connection.ChartMetric
import DifferentialGeometry.Integral.Connection.ChartSection

/-!
# Chart-local Levi-Civita covariant derivative

Given a smooth Riemannian metric `g : SmoothRiemannianMetric I M` and a base
point `α : M`, this file constructs the *chart-local* Levi-Civita covariant
derivative on the tangent bundle in the chart at `α`, and verifies that it
satisfies Mathlib's `IsCovariantDerivativeOn` (additivity in the section
argument and the Leibniz rule for scalar-function smul) on a suitable open
"good set".

## Construction

For `x` in the open *good set*

  `chartLeviCivitaGoodSet α := (extChartAt I α).source ∩
       (trivializationAt E (TangentSpace I) α).baseSet ∩
       (extChartAt I α) ⁻¹' interior ((extChartAt I α).target : Set E)`

and a section `σ : Π x : M, TangentSpace I x`, the chart-local Levi-Civita
covariant derivative `chartLeviCivita g α σ x : TangentSpace I x →L[ℝ]
TangentSpace I x` is defined by the standard chart-coordinate formula

  `(∇_v σ)(x) =`
    `trivFromE α x [ fderiv (σ̃ ∘ φ.symm)(φ x)(triv v)`
    `              + Σᵢⱼₖ (b.repr (triv v))ᵢ (b.repr σ̃(x))ⱼ Γᵏᵢⱼ(φ x) eₖ ]`

where `σ̃ := chartE_section_repr α σ`, `φ := extChartAt I α`, `Γᵏᵢⱼ` is
`chartChristoffel g α i j k`, and `triv := trivToE α x` is the canonical
tangent-bundle trivialization. Off the good set, the operator is the zero CLM
(junk).

## API

* `chartLeviCivitaGoodSet α` and `chartLeviCivitaGoodSet_isOpen`: the open
  good set on which the construction is well-defined.
* `chartLeviCivita g α σ x`: the chart-local Levi-Civita CLM.
* `chartLeviCivita_isCovariantDerivativeOn g α`:
  `IsCovariantDerivativeOn E (chartLeviCivita g α) (chartLeviCivitaGoodSet α)`.

The torsion-free and metric-compatibility properties of `chartLeviCivita`
are verified in subsequent files.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## The good set -/

/-- The open *good set* at `α` on which the chart-local Levi-Civita
construction is well-defined: the intersection of the chart source, the
trivialization base set at `α`, and the preimage under `extChartAt I α` of the
interior of the chart target. -/
def chartLeviCivitaGoodSet (α : M) : Set M :=
  (extChartAt I α).source ∩
    (trivializationAt E (TangentSpace I) α).baseSet ∩
    (extChartAt I α) ⁻¹' interior ((extChartAt I α).target : Set E)

/-- The good set is open. -/
lemma chartLeviCivitaGoodSet_isOpen (α : M) :
    IsOpen (chartLeviCivitaGoodSet (I := I) α) := by
  classical
  set S₁ : Set M := (extChartAt I α).source
  set S₂ : Set M := (trivializationAt E (TangentSpace I) α).baseSet
  set S₃ : Set M :=
    (extChartAt I α) ⁻¹' interior ((extChartAt I α).target : Set E)
  -- `S₁` is open: chart sources are open.
  have hS₁ : IsOpen S₁ := isOpen_extChartAt_source α
  -- `S₂` is open: trivialization base sets are open.
  have hS₂ : IsOpen S₂ := (trivializationAt E (TangentSpace I) α).open_baseSet
  -- `S₃` is open: continuity of `extChartAt I α` on its source plus openness of
  -- `interior _` gives a relative open in `S₁`; but we need it open in `M`.
  -- We show `S₃ = S₁ ∩ S₃` ∪ (M \ S₁); after intersecting with `S₁` later in the
  -- definition we don't need `S₃` itself to be open in `M`. Take the joint:
  have hcap_open : IsOpen (S₁ ∩ S₃) := by
    -- This is the preimage under `extChartAt I α` (continuous on `S₁`) of the
    -- open set `interior target`, intersected with `S₁`.
    have hcont : ContinuousOn (extChartAt I α) S₁ := continuousOn_extChartAt α
    have hopen_int : IsOpen (interior ((extChartAt I α).target : Set E)) :=
      isOpen_interior
    have hpre :
        S₁ ∩ S₃ =
          S₁ ∩ (extChartAt I α) ⁻¹' interior ((extChartAt I α).target : Set E) := rfl
    rw [hpre]
    exact hcont.isOpen_inter_preimage hS₁ hopen_int
  -- Now `chartLeviCivitaGoodSet α = S₁ ∩ S₂ ∩ S₃ = (S₁ ∩ S₃) ∩ S₂`.
  have heq : chartLeviCivitaGoodSet (I := I) α = (S₁ ∩ S₃) ∩ S₂ := by
    ext x
    simp only [chartLeviCivitaGoodSet, S₁, S₂, S₃, Set.mem_inter_iff]
    tauto
  rw [heq]
  exact hcap_open.inter hS₂

/-- Membership in the good set unfolded. -/
lemma mem_chartLeviCivitaGoodSet_iff {α x : M} :
    x ∈ chartLeviCivitaGoodSet (I := I) α ↔
      x ∈ (extChartAt I α).source ∧
        x ∈ (trivializationAt E (TangentSpace I) α).baseSet ∧
        extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) := by
  unfold chartLeviCivitaGoodSet
  rw [Set.mem_inter_iff, Set.mem_inter_iff, and_assoc]
  rfl

/-- A point in the good set lies in the extended-chart source. -/
lemma chartLeviCivitaGoodSet_mem_extChartAt_source {α x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    x ∈ (extChartAt I α).source :=
  ((mem_chartLeviCivitaGoodSet_iff.mp hx)).1

/-- A point in the good set lies in the chart source at `α`. -/
lemma chartLeviCivitaGoodSet_mem_chartAt_source {α x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    x ∈ (chartAt H α).source := by
  have := chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  simpa using this

/-- A point in the good set lies in the trivialization base set at `α`. -/
lemma chartLeviCivitaGoodSet_mem_baseSet {α x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
  ((mem_chartLeviCivitaGoodSet_iff.mp hx)).2.1

/-- The chart image of a good-set point lies in the interior of the chart target. -/
lemma chartLeviCivitaGoodSet_extChartAt_mem_interior {α x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
  ((mem_chartLeviCivitaGoodSet_iff.mp hx)).2.2

/-! ## The Christoffel-correction CLM

The Christoffel-correction term in the chart-local Levi-Civita formula,
expressed as a continuous linear map in its tangent-vector argument. The
"section component" `Y : E` is fixed; the linearity is in the input
`v : TangentSpace I x` (acting through `trivToE α x v ∈ E`). -/

/-- The Christoffel-correction CLM at a good-set point `x`, as a function of
`Y : E` representing the section's chart-trivialised value. The map sends
`v ↦ ∑ᵢⱼₖ (b.repr (trivToE α x v))ᵢ * (b.repr Y)ⱼ * Γᵏᵢⱼ(φ x) • eₖ`. -/
def christoffelCorrection (g : SmoothRiemannianMetric I M)
    (α : M) (x : M) (Y : E) :
    TangentSpace I x →L[ℝ] E :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        (((chartModelBasis E).coord i).toContinuousLinearMap.comp
            (trivToE (I := I) α x)).smulRight
          (((chartModelBasis E).repr Y j *
              chartChristoffel (I := I) g α i j k (extChartAt I α x)) •
            (chartModelBasis E) k)

/-- Pointwise formula for `christoffelCorrection`. -/
lemma christoffelCorrection_apply
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) (Y : E)
    (v : TangentSpace I x) :
    christoffelCorrection (I := I) g α x Y v =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr (trivToE (I := I) α x v)) i *
                ((chartModelBasis E).repr Y) j *
                chartChristoffel (I := I) g α i j k (extChartAt I α x)) •
              (chartModelBasis E) k := by
  classical
  unfold christoffelCorrection
  -- Iteratively apply `ContinuousLinearMap.sum_apply` and pointwise
  -- `smulRight_apply` reductions.
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- The `smulRight` step:
  -- `((b.coord i).toCLM.comp (trivToE α x)).smulRight (...) v`
  -- `= ((b.coord i).toCLM.comp (trivToE α x)) v • (...)`
  -- `= ((b.coord i) (trivToE α x v)) • (...)`
  -- `= ((b.repr (trivToE α x v)) i) • (...)`.
  rw [ContinuousLinearMap.smulRight_apply]
  rw [ContinuousLinearMap.comp_apply]
  -- `((b.coord i).toContinuousLinearMap (trivToE α x v)) = (b.coord i) (trivToE α x v) = (b.repr (trivToE α x v)) i`.
  have hcoord : ((chartModelBasis E).coord i).toContinuousLinearMap
      (trivToE (I := I) α x v) =
        ((chartModelBasis E).repr (trivToE (I := I) α x v)) i := by
    rfl
  rw [hcoord]
  -- Now the goal is:
  -- `((b.repr (trivToE α x v)) i) • ((b.repr Y j * Γ^k_{ij}) • e_k)
  --  = (b.repr (trivToE α x v)) i * (b.repr Y) j * Γ^k_{ij} • e_k`
  rw [smul_smul, ← mul_assoc]

/-- Additivity of `christoffelCorrection` in the section component `Y`. -/
lemma christoffelCorrection_add
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) (Y Y' : E)
    (v : TangentSpace I x) :
    christoffelCorrection (I := I) g α x (Y + Y') v =
      christoffelCorrection (I := I) g α x Y v +
        christoffelCorrection (I := I) g α x Y' v := by
  classical
  rw [christoffelCorrection_apply, christoffelCorrection_apply,
      christoffelCorrection_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- Linearity of `b.repr` in `Y`.
  have hrepr : ((chartModelBasis E).repr (Y + Y')) j =
      ((chartModelBasis E).repr Y) j +
        ((chartModelBasis E).repr Y') j := by
    rw [map_add]; rfl
  rw [hrepr]
  -- Goal: `(a * (b₁ + b₂) * c) • d = (a * b₁ * c) • d + (a * b₂ * c) • d`.
  rw [show ((chartModelBasis E).repr (trivToE (I := I) α x v)) i *
        (((chartModelBasis E).repr Y) j + ((chartModelBasis E).repr Y') j) *
        chartChristoffel (I := I) g α i j k (extChartAt I α x) =
      ((chartModelBasis E).repr (trivToE (I := I) α x v)) i *
          ((chartModelBasis E).repr Y) j *
          chartChristoffel (I := I) g α i j k (extChartAt I α x) +
        ((chartModelBasis E).repr (trivToE (I := I) α x v)) i *
          ((chartModelBasis E).repr Y') j *
          chartChristoffel (I := I) g α i j k (extChartAt I α x) by ring]
  rw [add_smul]

/-- Scalar-multiplication compatibility of `christoffelCorrection` in the
section component `Y`. -/
lemma christoffelCorrection_smul
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) (c : ℝ) (Y : E)
    (v : TangentSpace I x) :
    christoffelCorrection (I := I) g α x (c • Y) v =
      c • christoffelCorrection (I := I) g α x Y v := by
  classical
  rw [christoffelCorrection_apply, christoffelCorrection_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hrepr : ((chartModelBasis E).repr (c • Y)) j =
      c * ((chartModelBasis E).repr Y) j := by
    rw [map_smul]; rfl
  rw [hrepr]
  -- Goal: `(a * (c * b) * d) • e = c • ((a * b * d) • e)`.
  rw [show ((chartModelBasis E).repr (trivToE (I := I) α x v)) i *
        (c * ((chartModelBasis E).repr Y) j) *
        chartChristoffel (I := I) g α i j k (extChartAt I α x) =
      c * (((chartModelBasis E).repr (trivToE (I := I) α x v)) i *
          ((chartModelBasis E).repr Y) j *
          chartChristoffel (I := I) g α i j k (extChartAt I α x)) by ring]
  rw [← smul_smul]

/-! ## The chart-local Levi-Civita CLM -/

/-- The "inner CLM" of the chart-local Levi-Civita derivative at a good-set
point: the sum of the chart-pulled-back Fréchet derivative of the section's
representation and the Christoffel-correction CLM. Returns a CLM
`TangentSpace I x →L[ℝ] E`. -/
def chartLeviCivitaInnerCLM (g : SmoothRiemannianMetric I M)
    (α : M) (σ : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] E :=
  (fderiv ℝ (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
      (extChartAt I α x)).comp (trivToE (I := I) α x) +
  christoffelCorrection (I := I) g α x (chartE_section_repr (I := I) α σ x)

/-- Pointwise formula for the inner CLM. -/
lemma chartLeviCivitaInnerCLM_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (σ : Π x : M, TangentSpace I x) (x : M) (v : TangentSpace I x) :
    chartLeviCivitaInnerCLM (I := I) g α σ x v =
      fderiv ℝ (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
          (extChartAt I α x) (trivToE (I := I) α x v) +
        christoffelCorrection (I := I) g α x
          (chartE_section_repr (I := I) α σ x) v := by
  classical
  unfold chartLeviCivitaInnerCLM
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]

open scoped Classical in
/-- The chart-local Levi-Civita covariant derivative on the tangent bundle, at
the basepoint `α`. On the *good set* of `α` it is the standard chart-coordinate
Levi-Civita; off the good set it is the zero CLM (junk value). -/
def chartLeviCivita (g : SmoothRiemannianMetric I M) (α : M) :
    (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x) :=
  fun σ x =>
    if x ∈ chartLeviCivitaGoodSet (I := I) α then
      (trivFromE (I := I) α x).comp
        (chartLeviCivitaInnerCLM (I := I) g α σ x)
    else 0

/-- On the good set, `chartLeviCivita` unfolds. -/
lemma chartLeviCivita_eq_of_mem (g : SmoothRiemannianMetric I M) (α : M)
    (σ : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartLeviCivita (I := I) g α σ x =
      (trivFromE (I := I) α x).comp
        (chartLeviCivitaInnerCLM (I := I) g α σ x) := by
  classical
  simp only [chartLeviCivita, if_pos hx]

/-- Pointwise formula for `chartLeviCivita` on the good set. -/
lemma chartLeviCivita_apply (g : SmoothRiemannianMetric I M)
    (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) (v : TangentSpace I x) :
    chartLeviCivita (I := I) g α σ x v =
      trivFromE (I := I) α x
        (fderiv ℝ (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x v) +
          christoffelCorrection (I := I) g α x
            (chartE_section_repr (I := I) α σ x) v) := by
  classical
  rw [chartLeviCivita_eq_of_mem (I := I) g α σ hx]
  rw [ContinuousLinearMap.comp_apply]
  rw [chartLeviCivitaInnerCLM_apply]

/-! ## Differentiability bridge

We extract the `DifferentiableAt`-of-the-chart-pullback from the
`MDiffAt`-of-the-section hypothesis at a good-set point. -/

/-- At a good-set point, `MDiffAt (T% σ) x` implies
`DifferentiableAt ℝ (chartE_section_repr α σ ∘ (extChartAt I α).symm) (extChartAt I α x)`. -/
lemma differentiableAt_chartE_pullback_of_MDiff
    (α : M) {σ : Π x : M, TangentSpace I x} {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hσ : MDiffAt (T% σ) x) :
    DifferentiableAt ℝ
      (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
      (extChartAt I α x) :=
  (mdifferentiableAt_section_iff_chartE_fderiv (I := I) α σ
    (chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx)
    (chartLeviCivitaGoodSet_mem_baseSet (I := I) hx)
    (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx)).mp hσ

/-! ## Additivity axiom -/

/-- **Additivity of `chartLeviCivita`.** For sections `σ σ'` differentiable at
a good-set point, `chartLeviCivita g α (σ + σ') x = chartLeviCivita g α σ x +
chartLeviCivita g α σ' x` (as CLMs). -/
lemma chartLeviCivita_add (g : SmoothRiemannianMetric I M) (α : M)
    {σ σ' : Π x : M, TangentSpace I x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartLeviCivita (I := I) g α (σ + σ') x =
      chartLeviCivita (I := I) g α σ x + chartLeviCivita (I := I) g α σ' x := by
  classical
  -- Reduce to pointwise CLM equality.
  apply ContinuousLinearMap.ext
  intro v
  -- Unfold via `chartLeviCivita_apply` on both sides.
  rw [chartLeviCivita_apply (I := I) g α (σ + σ') hx v]
  rw [ContinuousLinearMap.add_apply,
      chartLeviCivita_apply (I := I) g α σ hx v,
      chartLeviCivita_apply (I := I) g α σ' hx v]
  -- Now we need:
  -- `trivFromE α x [ fderiv (rep_(σ+σ') ∘ φ⁻¹)(φ x) (triv v)
  --                + Christoffel(rep_(σ+σ') x) v ]
  --  = trivFromE α x [ fderiv (rep_σ ∘ φ⁻¹)(φ x) (triv v) + Christoffel(rep_σ x) v ]
  --  + trivFromE α x [ fderiv (rep_σ' ∘ φ⁻¹)(φ x) (triv v) + Christoffel(rep_σ' x) v ]`
  -- Use the linearity of `trivFromE` and combine the brackets.
  rw [← map_add]
  congr 1
  -- The function-level identity:
  -- `chartE_section_repr α (σ + σ') ∘ φ⁻¹ = (chartE_section_repr α σ ∘ φ⁻¹) + (chartE_section_repr α σ' ∘ φ⁻¹)`
  have hsum_pull :
      (chartE_section_repr (I := I) α (σ + σ') ∘ (extChartAt I α).symm) =
        (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm) +
          (chartE_section_repr (I := I) α σ' ∘ (extChartAt I α).symm) := by
    funext y
    change chartE_section_repr (I := I) α (σ + σ') ((extChartAt I α).symm y) =
      chartE_section_repr (I := I) α σ ((extChartAt I α).symm y) +
        chartE_section_repr (I := I) α σ' ((extChartAt I α).symm y)
    exact chartE_section_repr_add (I := I) α σ σ' ((extChartAt I α).symm y)
  -- Apply `fderiv_add` on the chart pullback at `(extChartAt I α x)`.
  have hdiff_σ : DifferentiableAt ℝ
      (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
      (extChartAt I α x) :=
    differentiableAt_chartE_pullback_of_MDiff (I := I) α hx hσ
  have hdiff_σ' : DifferentiableAt ℝ
      (chartE_section_repr (I := I) α σ' ∘ (extChartAt I α).symm)
      (extChartAt I α x) :=
    differentiableAt_chartE_pullback_of_MDiff (I := I) α hx hσ'
  -- Rewrite the LHS fderiv using `hsum_pull` and `fderiv_add`.
  have hfderiv_split :
      fderiv ℝ
          (chartE_section_repr (I := I) α (σ + σ') ∘ (extChartAt I α).symm)
          (extChartAt I α x) =
        fderiv ℝ
            (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
            (extChartAt I α x) +
          fderiv ℝ
              (chartE_section_repr (I := I) α σ' ∘ (extChartAt I α).symm)
              (extChartAt I α x) := by
    rw [hsum_pull]
    exact fderiv_add hdiff_σ hdiff_σ'
  -- Rewrite the LHS Christoffel-section component using `chartE_section_repr_add`.
  have hsec_add :
      chartE_section_repr (I := I) α (σ + σ') x =
        chartE_section_repr (I := I) α σ x +
          chartE_section_repr (I := I) α σ' x :=
    chartE_section_repr_add (I := I) α σ σ' x
  -- Combine.
  rw [hfderiv_split]
  rw [hsec_add]
  rw [christoffelCorrection_add (I := I) g α x
        (chartE_section_repr (I := I) α σ x)
        (chartE_section_repr (I := I) α σ' x) v]
  -- Goal now: `(A + B) (triv v) + (C + D) = (A (triv v) + C) + (B (triv v) + D)`.
  rw [ContinuousLinearMap.add_apply]
  abel

/-! ## Leibniz axiom -/

/-- **Leibniz rule for `chartLeviCivita`.** For a section `σ` and a scalar
function `f` differentiable at a good-set point, `chartLeviCivita g α (f • σ) x
= f x • chartLeviCivita g α σ x + (extDerivFun f x).smulRight (σ x)` (as CLMs).

The proof uses:
- `chartE_section_repr_smul_function` to identify
  `chartE_section_repr α (f • σ) = (f) • (chartE_section_repr α σ)` pointwise.
- `fderiv_smul` (Mathlib) for the Fréchet derivative of a scalar–vector product.
- `mfderiv_scalar_eq_chart_fderiv` (from `ChartSection.lean`) to bridge the
  chart-pulled-back derivative of `f` to its manifold derivative `mfderiv I 𝓘(ℝ)
  f x`.
- `christoffelCorrection_smul` to scale the Christoffel-correction term by
  `f x`.
- The trivialization round-trip `trivFromE_trivToE` to identify
  `trivFromE α x (chartE_section_repr α σ x) = σ x` on the trivialization base
  set. -/
lemma chartLeviCivita_leibniz (g : SmoothRiemannianMetric I M) (α : M)
    {σ : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M}
    (hσ : MDiffAt (T% σ) x) (hf : MDiffAt f x)
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartLeviCivita (I := I) g α (f • σ) x =
      f x • chartLeviCivita (I := I) g α σ x +
        (extDerivFun f x).smulRight (σ x) := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  -- LHS: unfold via `chartLeviCivita_apply`.
  rw [chartLeviCivita_apply (I := I) g α (f • σ) hx v]
  -- RHS: unfold via `chartLeviCivita_apply` and CLM operations.
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      chartLeviCivita_apply (I := I) g α σ hx v,
      ContinuousLinearMap.smulRight_apply]
  -- Identify the `f • σ` chart-pullback with `(f ∘ φ.symm) • (σ̃ ∘ φ.symm)`.
  have hsmul_pull :
      (chartE_section_repr (I := I) α (f • σ) ∘ (extChartAt I α).symm) =
        ((f ∘ (extChartAt I α).symm) •
          (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)) := by
    funext y
    -- LHS at y: `chartE_section_repr α (f • σ) (φ.symm y)`.
    -- Use `chartE_section_repr_smul_function` to rewrite.
    -- `(f • σ) z = f z • σ z` by `Pi.smul_apply`.
    have heq :
        chartE_section_repr (I := I) α (f • σ) ((extChartAt I α).symm y) =
          f ((extChartAt I α).symm y) •
            chartE_section_repr (I := I) α σ ((extChartAt I α).symm y) := by
      -- `(f • σ) z = f z • σ z` is `rfl` for the `Pi.instSMul` instance.
      have hpt :
          chartE_section_repr (I := I) α
              (fun z => f z • σ z)
              ((extChartAt I α).symm y) =
            f ((extChartAt I α).symm y) •
              chartE_section_repr (I := I) α σ ((extChartAt I α).symm y) :=
        chartE_section_repr_smul_function (I := I) α f σ
          ((extChartAt I α).symm y)
      exact hpt
    -- `(f ∘ φ.symm) • (σ̃ ∘ φ.symm) y = (f ∘ φ.symm) y • (σ̃ ∘ φ.symm) y`.
    -- Both sides match by `heq`.
    change chartE_section_repr (I := I) α (f • σ) ((extChartAt I α).symm y) =
      f ((extChartAt I α).symm y) •
        chartE_section_repr (I := I) α σ ((extChartAt I α).symm y)
    exact heq
  -- Apply `fderiv_smul` on the chart pullback at `(extChartAt I α x)`.
  have hdiff_σ : DifferentiableAt ℝ
      (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
      (extChartAt I α x) :=
    differentiableAt_chartE_pullback_of_MDiff (I := I) α hx hσ
  -- `f` MDifferentiable at `x` and `φ.symm` MDifferentiable at `φ x` give
  -- `f ∘ φ.symm` MDifferentiable at `φ x`, hence (vector-space target)
  -- `DifferentiableAt`.
  have hdiff_f : DifferentiableAt ℝ (f ∘ (extChartAt I α).symm)
      (extChartAt I α x) := by
    -- We get this from `mdifferentiableAt_iff_pullback_of_mem_source`-style
    -- reasoning, but a cleaner path: `f = (f ∘ φ.symm) ∘ φ` near `x`, with
    -- `φ.symm (φ x) = x`. Re-derive via the chain rule from `mfderiv_scalar`.
    -- Use `MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ) (f ∘ φ.symm)` at `φ x`, then convert.
    have hxsrc : x ∈ (extChartAt I α).source := by
      have := chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
      simpa using this
    have hxφ_inv : (extChartAt I α).symm (extChartAt I α x) = x :=
      (extChartAt I α).left_inv hxsrc
    have hxφ_tgt : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hxsrc
    have hsymm_within :
        MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I α).symm
          (range I) (extChartAt I α x) :=
      mdifferentiableWithinAt_extChartAt_symm (I := I) (x := α) hxφ_tgt
    have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) :=
      isOpen_interior
    have hxint :
        extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
      chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
    have hrange_nhds : range I ∈ 𝓝 (extChartAt I α x) := by
      exact Filter.mem_of_superset
        (Filter.mem_of_superset (hint_open.mem_nhds hxint) interior_subset)
        (extChartAt_target_subset_range α)
    have hf_within :
        MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ) (f ∘ (extChartAt I α).symm)
          (range I) (extChartAt I α x) :=
      MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq
        (I' := I) (I'' := 𝓘(ℝ)) (g := f) (f := (extChartAt I α).symm)
        (s := range I) (x := extChartAt I α x) (y := x)
        hf hsymm_within hxφ_inv
    have hf_at : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (f ∘ (extChartAt I α).symm)
        (extChartAt I α x) :=
      hf_within.mdifferentiableAt hrange_nhds
    exact hf_at.differentiableAt
  -- Compute the LHS fderiv using `fderiv_smul` and `hsmul_pull`.
  have hfderiv_split :
      fderiv ℝ
          (chartE_section_repr (I := I) α (f • σ) ∘ (extChartAt I α).symm)
          (extChartAt I α x) =
        (f ∘ (extChartAt I α).symm) (extChartAt I α x) •
            fderiv ℝ
              (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
              (extChartAt I α x) +
          (fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)).smulRight
            ((chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
                (extChartAt I α x)) := by
    rw [hsmul_pull]
    exact fderiv_smul hdiff_f hdiff_σ
  -- Identify `(extChartAt I α).symm (extChartAt I α x) = x`.
  have hxsrc : x ∈ (extChartAt I α).source := by
    have := chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
    simpa using this
  have hxφ_inv : (extChartAt I α).symm (extChartAt I α x) = x :=
    (extChartAt I α).left_inv hxsrc
  -- `(f ∘ φ.symm)(φ x) = f x` and `(σ̃ ∘ φ.symm)(φ x) = σ̃ x`.
  have hfφ : (f ∘ (extChartAt I α).symm) (extChartAt I α x) = f x := by
    change f ((extChartAt I α).symm (extChartAt I α x)) = f x
    rw [hxφ_inv]
  have hσφ : (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
        (extChartAt I α x) = chartE_section_repr (I := I) α σ x := by
    change chartE_section_repr (I := I) α σ
        ((extChartAt I α).symm (extChartAt I α x)) =
      chartE_section_repr (I := I) α σ x
    rw [hxφ_inv]
  rw [hfφ, hσφ] at hfderiv_split
  -- Apply at `(trivToE α x v)`.
  have hLfd_apply :
      fderiv ℝ
          (chartE_section_repr (I := I) α (f • σ) ∘ (extChartAt I α).symm)
          (extChartAt I α x) (trivToE (I := I) α x v) =
        f x • fderiv ℝ
            (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x v) +
          fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)
              (trivToE (I := I) α x v) •
            chartE_section_repr (I := I) α σ x := by
    rw [hfderiv_split]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]
  -- Identify the Christoffel piece: scaling by `f x`.
  have hsec_smul :
      chartE_section_repr (I := I) α (f • σ) x =
        f x • chartE_section_repr (I := I) α σ x :=
    chartE_section_repr_smul_function (I := I) α f σ x
  have hChristoffel_lhs :
      christoffelCorrection (I := I) g α x
          (chartE_section_repr (I := I) α (f • σ) x) v =
        f x • christoffelCorrection (I := I) g α x
            (chartE_section_repr (I := I) α σ x) v := by
    rw [hsec_smul, christoffelCorrection_smul]
  -- Bridge the chart-pulled-back fderiv of `f` to the manifold derivative.
  have hxsrc_chart : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hxint :
      extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  have hmf_to_fderiv :
      (mfderiv I 𝓘(ℝ) f x) v =
        fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)
          (trivToE (I := I) α x v) :=
    mfderiv_scalar_eq_chart_fderiv (I := I) α f hxsrc_chart hxint hf v
  -- `extDerivFun f x v = mfderiv I 𝓘(ℝ) f x v`.
  -- `extDerivFun f x = fromTangentSpace ∘L (mfderiv f x)`, and
  -- `fromTangentSpace` is the identity on `TangentSpace 𝓘(ℝ,ℝ) (f x) ≃ ℝ`.
  have hextDeriv :
      extDerivFun (I := I) f x v = (mfderiv I 𝓘(ℝ) f x) v := rfl
  -- Now combine. The full LHS is:
  -- `trivFromE α x (LHS_fderiv + Christoffel_(f • σ))`
  -- which we expand as:
  -- `trivFromE α x ([f x • fderiv σ + (mfderiv f) v • σ̃ x] + f x • Christoffel_σ)`
  -- which equals:
  -- `f x • trivFromE α x (fderiv σ + Christoffel_σ) + (mfderiv f) v • trivFromE α x (σ̃ x)`
  -- and `trivFromE α x (σ̃ x) = σ x`.
  -- Substitute everything inside `trivFromE α x (...)`.
  -- First, rewrite the additive structure inside the trivFromE.
  rw [hLfd_apply, hChristoffel_lhs]
  -- Goal (with abbreviations introduced via `let`):
  -- `trivFromE α x ((f x • A + D • σ̃ x) + f x • C) =
  --   f x • trivFromE α x (A + C) + (extDerivFun f x v) • σ x`,
  -- where `A := fderiv (σ̃ ∘ φ.symm)(φ x)(triv v)`,
  --       `D := fderiv (f ∘ φ.symm)(φ x)(triv v)`,
  --       `C := christoffelCorrection ...`.
  -- We perform the bracket reorganisation, distribute trivFromE, then
  -- identify `trivFromE α x (σ̃ x) = σ x` and `D = extDerivFun f x v`.
  have hreorg :
      (f x • fderiv ℝ (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
          (extChartAt I α x) (trivToE (I := I) α x v) +
        fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)
          (trivToE (I := I) α x v) • chartE_section_repr (I := I) α σ x) +
      f x • christoffelCorrection (I := I) g α x
              (chartE_section_repr (I := I) α σ x) v =
      f x • (fderiv ℝ (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
          (extChartAt I α x) (trivToE (I := I) α x v) +
          christoffelCorrection (I := I) g α x
              (chartE_section_repr (I := I) α σ x) v) +
      fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)
        (trivToE (I := I) α x v) • chartE_section_repr (I := I) α σ x := by
    rw [smul_add]; abel
  rw [hreorg]
  -- Distribute trivFromE over the sum and over the scalar:
  rw [map_add, map_smul, map_smul]
  -- Goal:
  -- `f x • trivFromE α x (A + C) + D • trivFromE α x (σ̃ x)
  --  = f x • trivFromE α x (A + C) + (extDerivFun f x v) • σ x`.
  congr 1
  -- We need `D • trivFromE α x (σ̃ x) = (extDerivFun f x v) • σ x`.
  -- Identify `trivFromE α x (σ̃ x) = σ x` via the round-trip.
  have htriv_round :
      trivFromE (I := I) α x (chartE_section_repr (I := I) α σ x) = σ x := by
    rw [chartE_section_repr_eq_trivToE]
    exact trivFromE_trivToE (I := I) α
      (chartLeviCivitaGoodSet_mem_baseSet (I := I) hx) (σ x)
  rw [htriv_round]
  -- Identify `D = (mfderiv I 𝓘(ℝ) f x) v = extDerivFun f x v`.
  rw [← hmf_to_fderiv, ← hextDeriv]

/-! ## `IsCovariantDerivativeOn` properties -/

/-- **The chart-local Levi-Civita satisfies `IsCovariantDerivativeOn`** on the
good set at `α`. -/
theorem chartLeviCivita_isCovariantDerivativeOn (g : SmoothRiemannianMetric I M)
    (α : M) :
    IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (chartLeviCivita (I := I) g α) (chartLeviCivitaGoodSet (I := I) α) where
  add hσ hσ' hx := chartLeviCivita_add (I := I) g α hσ hσ' hx
  leibniz hσ hf hx := chartLeviCivita_leibniz (I := I) g α hσ hf hx

end Connection
end Integral
end DifferentialGeometry
