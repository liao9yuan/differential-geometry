import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivTimeDeriv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicBoundGoodFrame
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.MetricCovDerivProducer
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Order-1 covariant → coordinate derivative conversion (P3 Brick A1)

The genuinely new layer of MSM135 Corollary `lbl351` (metrics with bounded
covariant derivatives preconverge).  For a fixed background metric `gRef` and a
`(0,2)` field `A0`, the chart-model first derivative of a tower-component scalar

  `s_p^V(y) := (covDerivOfField gRef A0 p) y (V·y)`

is bounded on an inner compact `Kc` of the chart source by a constant `CV`
(collecting `gRef`/chart/slot data only — independent of `A0`) times the next
two covariant-order norms `Cp1 + Cp`.  This is the order-1 step of the
`iteratedFDeriv` induction (Brick A2).

**Route.**  The model `fderiv` is bounded by a finite sum over a basis of the
model fibre (`opNorm_le_sum_coord`); each basis direction is evaluated by the
pointwise chart bridge `extDerivFun_tangentConstInChart_eq_fderiv`
(`FixedBase.lean`).  The chart-constant direction field is globalized to a
genuine smooth section by a bump (`exists_section_eqOn_compact`), so the P2 step
decomposition `totalNabla0SFun_apply_section` + `nabla0SFun_eval_smooth_slots`
rewrites the directional derivative of the level-`p` scalar as the level-`(p+1)`
scalar minus Christoffel corrections (each a level-`p` scalar at a modified slot
tuple).  Cauchy–Schwarz for covariant tensors (`abs_apply_le_sqrt_normSq0S`) at a
`gRef`-orthonormal basis (`exists_ON_tangentBasis`) bounds each term by the
covariant norm times the product of the slot fields' `gRef`-norms, which are
continuous, hence bounded on the compact `Kc` (`exists_family_bound`).

The quantifier discipline (constants — `CV` — before the varying field `A0`) is
load-bearing: when applied to a metric SEQUENCE `A0 = g_k`, `CV` is
`k`-independent and `Cp, Cp1` carry the `k`-dependence.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology
open Bundle Tensor0SBundle TensorLieDeriv
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

/-! ## Generic finite-dimensional operator-norm bound -/

/-- **Operator-norm bound via a basis.**  A real continuous linear functional on a
finite-dimensional space is bounded by the sum over a basis of the dual-basis
norms times the values on the basis.  Used to reduce the chart `fderiv` operator
norm to finitely many directional derivatives. -/
theorem opNorm_le_sum_coord {n : ℕ}
    (bE : Module.Basis (Fin n) Real E) (L : E →L[Real] Real) :
    ‖L‖ ≤ ∑ i : Fin n, ‖LinearMap.toContinuousLinearMap (bE.coord i)‖ * |L (bE i)| := by
  have hL : L = ∑ i : Fin n, (L (bE i)) • LinearMap.toContinuousLinearMap (bE.coord i) := by
    ext w
    rw [ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply, smul_eq_mul]
    conv_lhs => rw [← bE.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, smul_eq_mul, mul_comm]
  calc ‖L‖
      = ‖∑ i : Fin n, (L (bE i)) • LinearMap.toContinuousLinearMap (bE.coord i)‖ := by rw [← hL]
    _ ≤ ∑ i : Fin n, ‖(L (bE i)) • LinearMap.toContinuousLinearMap (bE.coord i)‖ :=
        norm_sum_le _ _
    _ = ∑ i : Fin n, ‖LinearMap.toContinuousLinearMap (bE.coord i)‖ * |L (bE i)| := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [norm_smul, Real.norm_eq_abs, mul_comm]

/-! ## A `gRef`-orthonormal tangent basis at each point -/

/-- **A `gRef`-orthonormal basis of the tangent space at any point** (general
dimension).  Repackages the trivialization-frame orthonormal basis
`exists_trivONBasis` as a basis of `TangentSpace I y`. -/
theorem exists_ON_tangentBasis (gRef : SmoothRiemannianMetric I M) (y : M) :
    ∃ b : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I y),
      ∀ i j, gRef.inner y (b i) (b j) = if i = j then (1 : Real) else 0 := by
  obtain ⟨basisE, hON⟩ := exists_trivONBasis (I := I) gRef y
  set e := trivializationAt E (TangentSpace I : M → Type _) y with he
  have hy : y ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' y
  refine ⟨(e.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hy, fun i j => ?_⟩
  rw [IsLocalFrameOn.toBasisAt_coe, IsLocalFrameOn.toBasisAt_coe]
  exact hON i j

/-! ## Globalizing a chart-constant direction field on a compact -/

/-- **Bump-globalization of a chart-constant tangent field on a compact.**  For
a compact `Kc` inside the chart source at `x₀`, there is a genuine smooth global
section agreeing with the chart-constant field `tangentConstInChart x₀ v` on
`Kc`.  This lets the step decomposition (which consumes global smooth slot
sections) see the chart-constant direction. -/
theorem exists_section_eqOn_compact
    (x₀ : M) (v : E) {Kc : Set M} (hKc : IsCompact Kc)
    (hKchart : Kc ⊆ (chartAt H x₀).source) :
    ∃ σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
      ∀ x ∈ Kc, σ x = tangentConstInChart (𝕜 := Real) (I := I) x₀ v x := by
  classical
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  haveI : NormalSpace M := inferInstance
  set e := trivializationAt E (TangentSpace I : M → Type _) x₀ with he
  have hbase : e.baseSet = (chartAt H x₀).source :=
    TangentBundle.trivializationAt_baseSet (𝕜 := Real) (I := I) x₀
  have hKbase : Kc ⊆ e.baseSet := by rw [hbase]; exact hKchart
  have hUopen : IsOpen e.baseSet := e.open_baseSet
  have hKclosed : IsClosed Kc := hKc.isClosed
  obtain ⟨W, hWopen, hKW, hWU⟩ := normal_exists_closure_subset hKclosed hUopen hKbase
  have hKintW : Kc ⊆ interior W := by rw [hWopen.interior_eq]; exact hKW
  obtain ⟨χ, hχ_one, hχ_zero, -⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := I) (M := M)
      (n := (⊤ : ℕ∞)) hKclosed hKintW
  have htsupp : tsupport (χ : M → Real) ⊆ e.baseSet := by
    refine subset_trans (closure_mono ?_) hWU
    intro x hx
    by_contra hxW
    exact hx (hχ_zero x hxW)
  have hχ_on : ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (χ : M → Real) e.baseSet :=
    χ.contMDiff.contMDiffOn
  have hconst_on :
      ContMDiffOn I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y
          (tangentConstInChart (𝕜 := Real) (I := I) x₀ v y)) e.baseSet := by
    simpa [he] using
      tangentConstInChart_contMDiffOn_baseSet (𝕜 := Real) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) x₀ v
  refine ⟨⟨fun y : M => χ y • tangentConstInChart (𝕜 := Real) (I := I) x₀ v y, ?_⟩, ?_⟩
  · exact hχ_on.smul_section_of_tsupport hUopen htsupp hconst_on
  · intro x hx
    have h1 : χ x = 1 := hχ_one.self_of_nhdsSet x hx
    simp [h1]

/-! ## Compact bound for the `gRef`-norm of a smooth section -/

/-- The `gRef`-norm of a smooth tangent section is bounded on a compact set. -/
theorem exists_sqrtInner_bound (gRef : SmoothRiemannianMetric I M)
    {Kc : Set M} (hKc : IsCompact Kc)
    (s : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ∃ C : Real, 0 ≤ C ∧ ∀ y ∈ Kc,
      Real.sqrt (gRef.inner y (s y) (s y)) ≤ C := by
  -- Smoothness of `y ↦ gRef.inner y (s y) (s y)` from the metric bundle map paired
  -- with the smooth section twice (no inner-product structure on `E` required).
  have hg : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun b : M => TotalSpace.mk' (E →L[Real] E →L[Real] Real)
        (E := fun x : M => TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real) b
        (gRef.inner b)) := gRef.contMDiff
  have hgY : ContMDiff I (I.prod 𝓘(Real, E →L[Real] Real)) ∞
      (fun b : M => TotalSpace.mk' (E →L[Real] Real)
        (E := fun x : M => TangentSpace I x →L[Real] Real) b (gRef.inner b (s b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[Real] Real)
      (b := fun b : M => b)
      (ϕ := fun b => gRef.inner b) (v := fun b => s b) hg s.contMDiff
  have hap : ContMDiff I (I.prod 𝓘(Real, Real)) ∞
      (fun b : M => TotalSpace.mk' Real (E := Bundle.Trivial M Real) b
        (gRef.inner b (s b) (s b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun _ : M => Real)
      (b := fun b : M => b)
      (ϕ := fun b => gRef.inner b (s b)) (v := fun b => s b) hgY s.contMDiff
  have hpair : ContMDiff I 𝓘(Real, Real) ∞ (fun b : M => gRef.inner b (s b) (s b)) := by
    intro b
    exact (contMDiffAt_section (F := Real) (E := Bundle.Trivial M Real) b).mp (hap b)
  have hcont : Continuous (fun y : M => Real.sqrt (gRef.inner y (s y) (s y))) :=
    Real.continuous_sqrt.comp hpair.continuous
  obtain ⟨C, hC⟩ := hKc.bddAbove_image hcont.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun y hy => le_trans (hC ⟨y, hy, rfl⟩) (le_max_left _ _)⟩

/-- A uniform `gRef`-norm bound over a finite family of smooth tangent sections,
on a compact set. -/
theorem exists_family_bound (gRef : SmoothRiemannianMetric I M)
    {Kc : Set M} (hKc : IsCompact Kc)
    {ι : Type*} [Fintype ι]
    (s : ι → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ∃ D : Real, 0 ≤ D ∧ ∀ i : ι, ∀ y ∈ Kc,
      Real.sqrt (gRef.inner y (s i y) (s i y)) ≤ D := by
  classical
  have h : ∀ i : ι, ∃ C : Real, 0 ≤ C ∧ ∀ y ∈ Kc,
      Real.sqrt (gRef.inner y (s i y) (s i y)) ≤ C :=
    fun i => exists_sqrtInner_bound (I := I) gRef hKc (s i)
  choose C hC0 hC using h
  refine ⟨∑ i : ι, C i, Finset.sum_nonneg (fun i _ => hC0 i), fun i y hy => ?_⟩
  exact le_trans (hC i y hy)
    (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i))

/-! ## Brick A1 — the order-1 conversion -/

/-- **Order-1 covariant → coordinate conversion** (MSM135 `lbl351`, P3 Brick A1).
The chart-model first derivative of the level-`p` tower-component scalar
`y ↦ (covDerivOfField gRef A0 p) y (V·y)` is bounded on an inner compact `Kc` of
the chart source by a constant `CV` (collecting `gRef`/chart/slot data only,
independent of `A0`) times `Cp1 + Cp`, where `Cp1`/`Cp` are uniform `gRef`-norms
of the next two covariant orders.  Base case of the `iteratedFDeriv` induction. -/
theorem fderiv_comp_le_tower
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {x₀ : M} {Kc : Set M} (hKc : IsCompact Kc)
    (hKchart : Kc ⊆ (chartAt H x₀).source) :
    ∃ CV : Real, 0 ≤ CV ∧ ∀ y ∈ Kc, ∀ Cp Cp1 : Real,
      (∀ z ∈ Kc, Real.sqrt
          (normSq0S (I := I) gRef z (p + 2) (covDerivOfField (I := I) gRef A0 p z)) ≤ Cp) →
      (∀ z ∈ Kc, Real.sqrt
          (normSq0S (I := I) gRef z (p + 3) (covDerivOfField (I := I) gRef A0 (p + 1) z)) ≤ Cp1) →
      ‖fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun z : M => (covDerivOfField (I := I) gRef A0 p) z (fun a => V a z)))
        (extChartAt I x₀ y)‖ ≤ CV * (Cp1 + Cp) := by
  classical
  set n := Module.finrank Real E with hn
  set bE := Module.finBasis Real E with hbE
  -- Globalize each model-basis chart-constant direction to a smooth section.
  have hσex : ∀ i : Fin n, ∃ σ : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _), ∀ x ∈ Kc,
      σ x = tangentConstInChart (𝕜 := Real) (I := I) x₀ (bE i) x :=
    fun i => exists_section_eqOn_compact (I := I) x₀ (bE i) hKc hKchart
  choose σ hσ using hσex
  -- Levi-Civita smoothness witness for the Christoffel-correction sections.
  have hcov : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) gRef) (∞ : WithTop ℕ∞) :=
    ⟨leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) gRef isOpen_univ⟩
  -- Correction sections `W i a = ∇_{σ i} (V a)`.
  let W : Fin n → Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := fun i a =>
    ⟨fun y : M =>
      ((leviCivitaConnectionOfMetric (I := I) gRef) (fun q : M => V a q) y) ((σ i) y),
      by
        simpa [TensorLieDeriv.covariantDeriv_vectorField] using
          TensorLieDeriv.covariantDeriv_vectorField_contMDiff (I := I)
            (leviCivitaConnectionOfMetric (I := I) gRef) hcov (σ i) (V a)⟩
  -- Uniform `gRef`-norm bound `D` over directions, slots, and corrections.
  obtain ⟨Dσ, hDσ0, hDσ⟩ := exists_family_bound (I := I) gRef hKc σ
  obtain ⟨DV, hDV0, hDV⟩ := exists_family_bound (I := I) gRef hKc V
  obtain ⟨DW, hDW0, hDW⟩ := exists_family_bound (I := I) gRef hKc
    (fun ia : Fin n × Fin (p + 2) => W ia.1 ia.2)
  set D := max Dσ (max DV DW) with hD
  have hD0 : 0 ≤ D := le_trans hDσ0 (le_max_left _ _)
  have hDσD : Dσ ≤ D := le_max_left _ _
  have hDVD : DV ≤ D := le_trans (le_max_left _ _) (le_max_right _ _)
  have hDWD : DW ≤ D := le_trans (le_max_right _ _) (le_max_right _ _)
  -- Pointwise direction/slot/correction `gRef`-norm bounds by `D`.
  have hσbd : ∀ i : Fin n, ∀ y ∈ Kc, Real.sqrt (gRef.inner y (σ i y) (σ i y)) ≤ D :=
    fun i y hy => le_trans (hDσ i y hy) hDσD
  have hVbd : ∀ a : Fin (p + 2), ∀ y ∈ Kc, Real.sqrt (gRef.inner y (V a y) (V a y)) ≤ D :=
    fun a y hy => le_trans (hDV a y hy) hDVD
  have hWbd : ∀ i : Fin n, ∀ a : Fin (p + 2), ∀ y ∈ Kc,
      Real.sqrt (gRef.inner y (W i a y) (W i a y)) ≤ D :=
    fun i a y hy => le_trans (hDW (i, a) y hy) hDWD
  -- The coefficient constant.
  set Ccoord : Real := ∑ i : Fin n, ‖LinearMap.toContinuousLinearMap (bE.coord i)‖
    with hCcoord
  have hCcoord0 : 0 ≤ Ccoord := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  refine ⟨max (Ccoord * D ^ (p + 3)) (Ccoord * ((p + 2 : ℕ) * D ^ (p + 2))),
    le_trans (mul_nonneg hCcoord0 (pow_nonneg hD0 _)) (le_max_left _ _), ?_⟩
  intro y hy Cp Cp1 hCp hCp1
  set CV := max (Ccoord * D ^ (p + 3)) (Ccoord * ((p + 2 : ℕ) * D ^ (p + 2))) with hCV
  -- The scalar whose chart derivative we bound.
  set f : M → Real := fun z : M => (covDerivOfField (I := I) gRef A0 p) z (fun a => V a z)
    with hf
  -- Nonnegativity of the order norms (from the hypotheses at `y`).
  have hCpnn : 0 ≤ Cp := le_trans (Real.sqrt_nonneg _) (hCp y hy)
  have hCp1nn : 0 ≤ Cp1 := le_trans (Real.sqrt_nonneg _) (hCp1 y hy)
  -- The `gRef`-orthonormal tangent basis at `y` for Cauchy–Schwarz.
  obtain ⟨bON, hbON⟩ := exists_ON_tangentBasis (I := I) gRef y
  -- Differentiability of the scalar at `y` (for the chart bridge).
  have hfmd : MDifferentiableAt I 𝓘(Real, Real) f y :=
    covDerivOfField_eval_mdiffAt (I := I) gRef A0 p V y
  have hychart : y ∈ (chartAt H x₀).source := hKchart hy
  -- The per-direction bound, valid for every model-basis index.
  have hdir : ∀ i : Fin n,
      |fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x₀ f) (extChartAt I x₀ y) (bE i)|
        ≤ Cp1 * D ^ (p + 3) + (p + 2 : ℕ) * (Cp * D ^ (p + 2)) := by
    intro i
    -- Chart bridge: the directional model derivative is the exterior derivative.
    have hbridge :
        fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x₀ f) (extChartAt I x₀ y) (bE i)
          = extDerivFun (I := I) f y (σ i y) := by
      rw [← extDerivFun_tangentConstInChart_eq_fderiv (I := I) (f := f)
        (x := x₀) (p := y) hychart hfmd (bE i)]
      rw [hσ i y hy]
    -- Step decomposition of the directional derivative.
    have hdecomp :
        extDerivFun (I := I) f y (σ i y)
          = (covDerivOfField (I := I) gRef A0 (p + 1)) y
              (Fin.cons (σ i y) (fun a : Fin (p + 2) => V a y))
            + ∑ a : Fin (p + 2),
                (covDerivOfField (I := I) gRef A0 p) y
                  (Function.update (fun b : Fin (p + 2) => V b y) a
                    (((leviCivitaConnectionOfMetric (I := I) gRef)
                      (fun q : M => V a q) y) (σ i y))) := by
      have key :
          (covDerivOfField (I := I) gRef A0 (p + 1)) y
              (Fin.cons (σ i y) (fun a : Fin (p + 2) => V a y))
            = extDerivFun (I := I) f y (σ i y)
              - ∑ a : Fin (p + 2),
                  (covDerivOfField (I := I) gRef A0 p) y
                    (Function.update (fun b : Fin (p + 2) => V b y) a
                      (((leviCivitaConnectionOfMetric (I := I) gRef)
                        (fun q : M => V a q) y) (σ i y))) := by
        rw [covDerivOfField_succ, metricCovDerivStep_apply,
          Tensor0SBundle.totalNabla0SFun_apply_section,
          Tensor0SBundle.nabla0SFun_eval_smooth_slots]
      linarith [key]
    rw [hbridge, hdecomp]
    -- Triangle inequality.
    refine le_trans (abs_add_le _ _) ?_
    refine add_le_add ?_ ?_
    · -- Cauchy–Schwarz for the level-`(p+1)` term.
      have hCS := abs_apply_le_sqrt_normSq0S (I := I) gRef y (p + 3) bON hbON
        (covDerivOfField (I := I) gRef A0 (p + 1) y)
        (Fin.cons (σ i y) (fun a : Fin (p + 2) => V a y))
      refine le_trans hCS ?_
      have hprod :
          (∏ a : Fin (p + 3), Real.sqrt (gRef.inner y
              ((Fin.cons (σ i y) (fun a : Fin (p + 2) => V a y) :
                  Fin (p + 3) → TangentSpace I y) a)
              ((Fin.cons (σ i y) (fun a : Fin (p + 2) => V a y) :
                  Fin (p + 3) → TangentSpace I y) a)))
            ≤ D ^ (p + 3) := by
        refine le_trans (Finset.prod_le_prod (g := fun _ : Fin (p + 3) => D)
          (fun a _ => Real.sqrt_nonneg _) (fun a _ => ?_)) (le_of_eq ?_)
        · refine Fin.cases ?_ ?_ a
          · simpa using hσbd i y hy
          · intro a'
            simpa using hVbd a' y hy
        · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      refine le_trans (mul_le_mul (hCp1 y hy) hprod
        (Finset.prod_nonneg (fun a _ => Real.sqrt_nonneg _)) hCp1nn) ?_
      exact le_of_eq rfl
    · -- Cauchy–Schwarz for the correction sum.
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hterm : ∀ a : Fin (p + 2),
          |(covDerivOfField (I := I) gRef A0 p) y
              (Function.update (fun b : Fin (p + 2) => V b y) a
                (((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun q : M => V a q) y) (σ i y)))|
            ≤ Cp * D ^ (p + 2) := by
        intro a
        have hCS := abs_apply_le_sqrt_normSq0S (I := I) gRef y (p + 2) bON hbON
          (covDerivOfField (I := I) gRef A0 p y)
          (Function.update (fun b : Fin (p + 2) => V b y) a
            (((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun q : M => V a q) y) (σ i y)))
        refine le_trans hCS ?_
        have hprod :
            (∏ b : Fin (p + 2), Real.sqrt (gRef.inner y
                (Function.update (fun c : Fin (p + 2) => V c y) a
                  (((leviCivitaConnectionOfMetric (I := I) gRef)
                    (fun q : M => V a q) y) (σ i y)) b)
                (Function.update (fun c : Fin (p + 2) => V c y) a
                  (((leviCivitaConnectionOfMetric (I := I) gRef)
                    (fun q : M => V a q) y) (σ i y)) b)))
              ≤ D ^ (p + 2) := by
          refine le_trans (Finset.prod_le_prod (g := fun _ : Fin (p + 2) => D)
            (fun b _ => Real.sqrt_nonneg _) (fun b _ => ?_)) (le_of_eq ?_)
          · by_cases hba : b = a
            · rw [hba, Function.update_self]
              exact hWbd i a y hy
            · simp only [Function.update_of_ne hba]
              exact hVbd b y hy
          · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        refine le_trans (mul_le_mul (hCp y hy) hprod
          (Finset.prod_nonneg (fun b _ => Real.sqrt_nonneg _)) hCpnn) ?_
        exact le_of_eq rfl
      refine le_trans (Finset.sum_le_sum (fun a _ => hterm a)) ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Assemble: operator norm ≤ Σ over basis ≤ CV · (Cp1 + Cp).
  set Lz := fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x₀ f) (extChartAt I x₀ y)
    with hLz
  refine le_trans (opNorm_le_sum_coord (E := E) bE Lz) ?_
  have hsum :
      (∑ i : Fin n, ‖LinearMap.toContinuousLinearMap (bE.coord i)‖ * |Lz (bE i)|)
        ≤ Ccoord * (Cp1 * D ^ (p + 3) + (p + 2 : ℕ) * (Cp * D ^ (p + 2))) := by
    rw [hCcoord, Finset.sum_mul]
    refine Finset.sum_le_sum (fun i _ => ?_)
    exact mul_le_mul_of_nonneg_left (hdir i) (norm_nonneg _)
  refine le_trans hsum ?_
  -- `Ccoord · (Cp1·D^(p+3) + (p+2)·Cp·D^(p+2)) ≤ CV · (Cp1 + Cp)`.
  have hb1 : Ccoord * D ^ (p + 3) ≤ CV := le_max_left _ _
  have hb2 : Ccoord * ((p + 2 : ℕ) * D ^ (p + 2)) ≤ CV := le_max_right _ _
  have hexpand :
      Ccoord * (Cp1 * D ^ (p + 3) + (p + 2 : ℕ) * (Cp * D ^ (p + 2)))
        = (Ccoord * D ^ (p + 3)) * Cp1
          + (Ccoord * ((p + 2 : ℕ) * D ^ (p + 2))) * Cp := by ring
  rw [hexpand]
  have h1 : (Ccoord * D ^ (p + 3)) * Cp1 ≤ CV * Cp1 :=
    mul_le_mul_of_nonneg_right hb1 hCp1nn
  have h2 : (Ccoord * ((p + 2 : ℕ) * D ^ (p + 2))) * Cp ≤ CV * Cp :=
    mul_le_mul_of_nonneg_right hb2 hCpnn
  calc (Ccoord * D ^ (p + 3)) * Cp1 + (Ccoord * ((p + 2 : ℕ) * D ^ (p + 2))) * Cp
      ≤ CV * Cp1 + CV * Cp := add_le_add h1 h2
    _ = CV * (Cp1 + Cp) := by ring

end HCGCompactness
end DifferentialGeometry
