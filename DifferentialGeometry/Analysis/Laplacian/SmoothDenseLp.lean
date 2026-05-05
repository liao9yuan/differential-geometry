import DifferentialGeometry.Analysis.Laplacian.L2Inclusion
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Density of smooth scalar functions in `Lp` on a closed Riemannian manifold

For a closed (compact, Hausdorff) smooth Riemannian manifold `(M, g)` modelled on
a finite-dimensional real inner-product space, the continuous linear map
`smoothToLp g : SmoothScalar g →L[ℝ] Lp ℝ 2 μ_g` has dense range.

The proof uses the Stone–Weierstrass theorem: the smooth real-valued functions
on `M` form a unital `ℝ`-subalgebra of `C(M, ℝ)` that separates points (using
`SmoothBumpFunction` to construct distinguishing functions). Hence smooth
functions are sup-norm dense in `C(M, ℝ)`. Combined with
`BoundedContinuousFunction.toLp_denseRange` (continuous functions are
`Lp`-dense on a finite weakly regular measure), this yields that smooth
functions are `Lp`-dense.

The density of `smoothToLp` lifts to density of the H¹ extension
`H1ComplToLp g : H1Compl g →L[ℝ] Lp ℝ 2 μ_g`, which is the form used by the
variational Laplacian construction (see `Operator.lean`).

## Main results

* `smoothScalarSubalgebra g`: the unital ℝ-subalgebra of `C(M, ℝ)` consisting
  of (continuous representatives of) smooth real-valued functions on `M`.
* `smoothScalarSubalgebra_separatesPoints`: the smooth subalgebra separates
  points.
* `denseRange_smoothToLp`: `smoothToLp g` has dense range in `Lp ℝ 2 μ_g`.
* `denseRange_H1ComplToLp`: `H1ComplToLp g` has dense range in `Lp ℝ 2 μ_g`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter BoundedContinuousFunction
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace BoundedContinuousFunction

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-! ## Continuous-map view of a smooth scalar -/

/-- Convert a smooth real-valued function on `M` (packaged as a `SmoothScalar g`)
into a continuous map `C(M, ℝ)`. -/
def SmoothScalar.toContinuousMap {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) : C(M, ℝ) :=
  ⟨f.toFun, f.smooth.continuous⟩

@[simp] lemma SmoothScalar.toContinuousMap_apply {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) (x : M) :
    f.toContinuousMap x = f.toFun x := rfl

@[simp] lemma SmoothScalar.toContinuousMap_zero {g : SmoothRiemannianMetric I M} :
    (0 : SmoothScalar g).toContinuousMap = (0 : C(M, ℝ)) := by
  ext x
  rfl

@[simp] lemma SmoothScalar.toContinuousMap_add {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    (f + h).toContinuousMap = f.toContinuousMap + h.toContinuousMap := by
  ext x
  rfl

@[simp] lemma SmoothScalar.toContinuousMap_smul {g : SmoothRiemannianMetric I M}
    (c : ℝ) (f : SmoothScalar g) :
    (c • f).toContinuousMap = c • f.toContinuousMap := by
  ext x
  rfl

/-! ## The smooth subalgebra of continuous functions

We build `smoothScalarSubalgebra g`: the set of `φ : C(M, ℝ)` that arise as the
underlying continuous map of a smooth scalar (i.e. as `f.toContinuousMap` for
some `f : SmoothScalar g`). This set is closed under sums, scalar
multiplication, and pointwise products, and contains the constant function `1`,
because each of these operations preserves smoothness of real-valued functions
on a manifold. -/

/-- The constant-1 smooth scalar. -/
def SmoothScalar.one (g : SmoothRiemannianMetric I M) : SmoothScalar g where
  toFun := fun _ => (1 : ℝ)
  smooth := contMDiff_const

@[simp] lemma SmoothScalar.one_toFun (g : SmoothRiemannianMetric I M) :
    (SmoothScalar.one g).toFun = fun _ : M => (1 : ℝ) := rfl

/-- Pointwise product of two smooth scalars. -/
def SmoothScalar.mul {g : SmoothRiemannianMetric I M} (f h : SmoothScalar g) :
    SmoothScalar g where
  toFun := fun x => f.toFun x * h.toFun x
  smooth := f.smooth.mul h.smooth

@[simp] lemma SmoothScalar.mul_toFun {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    (SmoothScalar.mul f h).toFun = fun x => f.toFun x * h.toFun x := rfl

/-- The set of smooth real-valued functions on `M`, viewed as a subset of
`C(M, ℝ)` via the canonical "continuous representative" map. -/
def SmoothScalar.imageInContinuousMap (g : SmoothRiemannianMetric I M) :
    Set C(M, ℝ) :=
  { φ : C(M, ℝ) | ∃ f : SmoothScalar g, f.toContinuousMap = φ }

/-- The unital ℝ-subalgebra of `C(M, ℝ)` consisting of smooth real-valued
functions on `M`. -/
def smoothScalarSubalgebra (g : SmoothRiemannianMetric I M) :
    Subalgebra ℝ C(M, ℝ) where
  carrier := SmoothScalar.imageInContinuousMap g
  mul_mem' := by
    rintro φ ψ ⟨f, hf⟩ ⟨h, hh⟩
    refine ⟨SmoothScalar.mul f h, ?_⟩
    -- Need: `(SmoothScalar.mul f h).toContinuousMap = φ * ψ`.
    ext x
    have h1 : φ x = f.toFun x := by rw [← hf]; rfl
    have h2 : ψ x = h.toFun x := by rw [← hh]; rfl
    -- LHS: `(SmoothScalar.mul f h).toContinuousMap x = f.toFun x * h.toFun x`.
    -- RHS: `(φ * ψ) x = φ x * ψ x`.
    change f.toFun x * h.toFun x = (φ * ψ) x
    rw [ContinuousMap.mul_apply, h1, h2]
  one_mem' := ⟨SmoothScalar.one g, by ext x; rfl⟩
  add_mem' := by
    rintro φ ψ ⟨f, hf⟩ ⟨h, hh⟩
    refine ⟨f + h, ?_⟩
    ext x
    have h1 : φ x = f.toFun x := by rw [← hf]; rfl
    have h2 : ψ x = h.toFun x := by rw [← hh]; rfl
    change f.toFun x + h.toFun x = (φ + ψ) x
    rw [ContinuousMap.add_apply, h1, h2]
  zero_mem' := ⟨(0 : SmoothScalar g), by ext x; rfl⟩
  algebraMap_mem' c := by
    refine ⟨c • SmoothScalar.one g, ?_⟩
    -- `(c • SmoothScalar.one g).toContinuousMap = algebraMap ℝ C(M,ℝ) c`.
    -- Both sides are constant `c` viewed as `C(M, ℝ)`.
    apply ContinuousMap.ext
    intro x
    -- LHS: `c * 1 = c`. RHS: `c • (1 : ℝ) = c`. Both unfolds give `c`.
    change c * (1 : ℝ) = (algebraMap ℝ C(M, ℝ) c) x
    rw [mul_one, Algebra.algebraMap_eq_smul_one]
    -- Now: `c = (c • (1 : C(M, ℝ))) x`. Pointwise: `c = c • 1 = c`.
    change c = (c • (1 : C(M, ℝ))) x
    rw [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]

@[simp] lemma mem_smoothScalarSubalgebra_iff {g : SmoothRiemannianMetric I M}
    {φ : C(M, ℝ)} :
    φ ∈ smoothScalarSubalgebra (I := I) (M := M) g ↔
      ∃ f : SmoothScalar g, f.toContinuousMap = φ := Iff.rfl

/-! ## Separation of points by smooth bump functions -/

/-- Auxiliary: for any two distinct points `x, y` in a smooth manifold modelled
on a finite-dimensional inner-product space (with `[T2Space]`), there exists a
smooth real-valued function `f : M → ℝ` with `f x = 1` and `f y = 0`.

We construct a `SmoothBumpFunction` centred at `x`. It always satisfies
`f x = 1`. We then choose its outer radius small enough that its support
avoids `y`, so that `f y = 0`. -/
private lemma exists_smooth_separating
    (x y : M) (hxy : x ≠ y) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ f x = 1 ∧ f y = 0 := by
  classical
  -- Build a `SmoothBumpFunction I x` whose topological support avoids `y`.
  -- Use `nhds_basis_support` on the open set `{y}ᶜ`, which is a neighbourhood of
  -- `x` because `M` is `T2` and `x ≠ y`.
  have h_compl_open : IsOpen ({y}ᶜ : Set M) := isOpen_compl_singleton
  have h_x_in_compl : x ∈ ({y}ᶜ : Set M) := by
    intro hx
    -- `hx : x ∈ {y}` says `x = y`.
    rw [Set.mem_singleton_iff] at hx
    exact hxy hx
  have h_compl_mem : ({y}ᶜ : Set M) ∈ 𝓝 x :=
    h_compl_open.mem_nhds h_x_in_compl
  -- `SmoothBumpFunction.nhds_basis_support` says: there's a smooth bump
  -- whose tsupport is contained in any given neighbourhood of `x`.
  have hbasis := SmoothBumpFunction.nhds_basis_support (I := I) h_compl_mem
  -- `hbasis.ex_mem` : `∃ φ : SmoothBumpFunction I x, tsupport φ ⊆ {y}ᶜ`.
  obtain ⟨φ, hφ_tsupp⟩ := hbasis.ex_mem
  refine ⟨(φ : M → ℝ), φ.contMDiff, ?_, ?_⟩
  · -- `φ x = 1` because `x` is the centre.
    exact φ.eq_one
  · -- `φ y = 0` because `y ∉ tsupport φ ⊆ {y}ᶜ`.
    by_contra hy
    have hy_supp : y ∈ tsupport (φ : M → ℝ) := subset_tsupport _ hy
    have hy_in_compl : y ∈ ({y}ᶜ : Set M) := hφ_tsupp hy_supp
    exact hy_in_compl rfl

/-- The smooth subalgebra of `C(M, ℝ)` separates points. -/
theorem smoothScalarSubalgebra_separatesPoints (g : SmoothRiemannianMetric I M) :
    (smoothScalarSubalgebra (I := I) (M := M) g).SeparatesPoints := by
  intro x y hxy
  obtain ⟨f, hf, hfx, hfy⟩ := exists_smooth_separating (I := I) (M := M) x y hxy
  -- `SeparatesPoints` requires: ∃ f' ∈ ((·) '' subalgebra), f' x ≠ f' y.
  -- The underlying continuous map of `⟨f, hf⟩ : SmoothScalar g`.
  refine ⟨f, ?_, ?_⟩
  · -- Membership in `(fun g => ⇑g) '' (smoothScalarSubalgebra g : Set C(M, ℝ))`.
    refine ⟨(⟨f, hf⟩ : SmoothScalar g).toContinuousMap, ?_, rfl⟩
    -- `(⟨f, hf⟩ : SmoothScalar g).toContinuousMap ∈ smoothScalarSubalgebra g`.
    exact ⟨⟨f, hf⟩, rfl⟩
  · -- `f x ≠ f y`, since `f x = 1 ≠ 0 = f y`.
    rw [hfx, hfy]
    exact one_ne_zero

/-! ## Density of the smooth subalgebra in `C(M, ℝ)` (sup norm) -/

/-- For any continuous `φ : C(M, ℝ)` and `ε > 0`, there exists a smooth scalar
function `f : SmoothScalar g` with `‖f.toContinuousMap - φ‖ < ε` (sup norm). -/
theorem exists_smoothScalar_sup_close (g : SmoothRiemannianMetric I M)
    (φ : C(M, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : SmoothScalar g, ‖f.toContinuousMap - φ‖ < ε := by
  -- Apply Stone–Weierstrass to the smooth subalgebra.
  obtain ⟨g', hg'_lt⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      (smoothScalarSubalgebra (I := I) (M := M) g)
      (smoothScalarSubalgebra_separatesPoints (I := I) (M := M) g) φ ε hε
  obtain ⟨f, hf⟩ := g'.2
  refine ⟨f, ?_⟩
  -- `‖f.toContinuousMap - φ‖ = ‖g' - φ‖ < ε` (since `f.toContinuousMap = g'`).
  rw [hf]
  exact hg'_lt

/-! ## Sup-norm convergence implies `Lp`-norm convergence on a finite measure -/

/-- A continuous function with `‖φ‖_∞ ≤ K` on a compact `M` has `Lp` norm at
most `μ(univ)^(1/p) · K`. We work with `p = 2`. The Mathlib lemma puts the
measure factor on the left. -/
private lemma eLpNorm_two_le_of_norm_le
    (g : SmoothRiemannianMetric I M) (φ : M → ℝ) (_hφ : Continuous φ) (K : ℝ)
    (hK : ∀ x, ‖φ x‖ ≤ K) :
    eLpNorm φ 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (riemannianVolumeMeasure (I := I) (M := M) g
          (Set.univ : Set M)) ^ (2 : ℝ≥0∞).toReal⁻¹ *
        ENNReal.ofReal K := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  -- `eLpNorm_le_of_ae_bound` gives the bound directly.
  exact MeasureTheory.eLpNorm_le_of_ae_bound (μ := riemannianVolumeMeasure (I := I) (M := M) g)
    (f := φ) (C := K) (Filter.Eventually.of_forall hK)

/-! ## Density of `smoothToLp` in `Lp ℝ 2 μ_g`

The continuous linear map `smoothToLp g : SmoothScalar g →L[ℝ] Lp ℝ 2 μ_g`
has dense range.

The proof composes two density results:

* sup-norm dense: smooth functions on a compact manifold sup-norm-approximate
  continuous functions, by Stone–Weierstrass applied to
  `smoothScalarSubalgebra g`;
* `Lp`-dense: continuous functions on a compact `M` are `Lp`-dense via
  `BoundedContinuousFunction.toLp_denseRange`.

We extract intermediate lemmas to keep elaboration manageable. -/

/-- The pointwise L² eLpNorm of the difference between a smooth function and a
bounded continuous function is bounded by the sup-norm of the pointwise
difference times the measure factor. This is a pure-`eLpNorm` statement,
avoiding `BoundedContinuousFunction.toLp` in the type signature so that no
`[IsFiniteMeasure]` instance is needed at signature elaboration time. -/
private lemma eLpNorm_smooth_sub_bc_le
    (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) (ψ : M →ᵇ ℝ) (δ : ℝ)
    (h_pt : ∀ x : M, ‖f.toFun x - ψ x‖ ≤ δ) :
    eLpNorm (fun x : M => f.toFun x - ψ x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (riemannianVolumeMeasure (I := I) (M := M) g) Set.univ ^
          ((2 : ℝ≥0∞).toReal⁻¹) * ENNReal.ofReal δ := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  -- Continuity of the difference.
  have h_diff_cont : Continuous (fun x : M => f.toFun x - ψ x) :=
    f.smooth.continuous.sub ψ.continuous
  exact eLpNorm_two_le_of_norm_le (I := I) (M := M) g _ h_diff_cont δ h_pt

/-- Auxiliary: equality between the `Lp`-edist of `MemLp.toLp` of two functions
and the `eLpNorm` of their pointwise difference. Just `Lp.edist_toLp_toLp`
specialised to our setting. -/
private lemma edist_toLp_eq_eLpNorm
    {μ : Measure M} (a b : M → ℝ) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    edist (ha.toLp a) (hb.toLp b) = eLpNorm (fun x : M => a x - b x) 2 μ := by
  -- The Mathlib lemma uses the `Pi.sub_apply` form of the difference.
  rw [Lp.edist_toLp_toLp]
  rfl

/-- Auxiliary: smooth scalars approximate any `MemLp 2 μ_g` function via a
sup-norm-then-eLpNorm decomposition. Returns a smooth function whose
`MemLp.toLp` is `edist`-close in `Lp ℝ 2 μ`. -/
private lemma exists_smoothToLp_close_to_memLp
    (g : SmoothRiemannianMetric I M)
    [hμ_fin : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g)]
    [hμ_wreg : (riemannianVolumeMeasure (I := I) (M := M) g).WeaklyRegular]
    (h : M → ℝ) (h_mem : MemLp h 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ f : SmoothScalar g,
      edist (f.memLp_two.toLp f.toFun) (h_mem.toLp h) ≤ ε := by
  classical
  set μvol := riemannianVolumeMeasure (I := I) (M := M) g with hμvol_def
  -- Approximate `h` by a bounded continuous function `ψ_bc` with eLpNorm ≤ ε / 2.
  have h2 : (ε / 2 : ℝ≥0∞) ≠ 0 := by
    rw [Ne, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨hε, ENNReal.ofNat_ne_top⟩
  obtain ⟨ψ_bc, hψ_eLpNorm_le, _hψ_mem⟩ :=
    h_mem.exists_boundedContinuous_eLpNorm_sub_le (E := ℝ) (μ := μvol) (p := 2)
      ENNReal.ofNat_ne_top h2
  -- Pick the real δ used for the Stone-Weierstrass step.
  -- We want eLpNorm (f_smooth - ψ_bc) ≤ ε / 2.
  -- That eLpNorm is ≤ μ(univ)^(1/2) * sup-norm of the difference.
  -- The sup-norm bound: choose `δ_real > 0` such that the resulting eLpNorm
  -- ≤ ε / 2. We use the `ENNReal` formulation throughout.
  have h_finite : μvol Set.univ < ⊤ := IsFiniteMeasure.measure_univ_lt_top
  set Cμ_enn : ℝ≥0∞ := μvol Set.univ ^ ((2 : ℝ≥0∞).toReal⁻¹) with hCμ_enn_def
  have hCμ_enn_ne_top : Cμ_enn ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ ((2 : ℝ≥0∞).toReal⁻¹))
      h_finite.ne
  -- `δ_enn := (ε/2) / (Cμ_enn + 1)`. In real terms, choose any positive real
  -- mapping to ≤ this. We pick `δ_real := (ε/2).toReal / (Cμ + 1)` where
  -- `Cμ := Cμ_enn.toReal`. This always satisfies the eLpNorm bound when
  -- ε / 2 < ∞; when ε / 2 = ⊤ any δ works.
  -- We bypass real-number reasoning by using a single existential: pick any
  -- δ_real > 0 with `ENNReal.ofReal δ_real * Cμ_enn ≤ ε / 2`.
  -- Such a `δ_real` exists because `Cμ_enn < ⊤` and `ε / 2 > 0`.
  -- We construct it explicitly.
  obtain ⟨δ_real, hδ_pos, hδ_bound⟩ :
      ∃ δ_real : ℝ, 0 < δ_real ∧ Cμ_enn * ENNReal.ofReal δ_real ≤ ε / 2 := by
    -- Case ε / 2 = ⊤: any δ_real := 1 works.
    by_cases h_top : ε / 2 = ⊤
    · refine ⟨1, by norm_num, ?_⟩
      rw [h_top]; exact le_top
    · -- ε / 2 finite. Then ε / 2 > 0 (from h2). Pick
      -- δ_real := (ε/2).toReal / max(Cμ + 1, 1).
      set Cμ : ℝ := Cμ_enn.toReal with hCμ_def
      have hCμ_nn : 0 ≤ Cμ := ENNReal.toReal_nonneg
      set δ_real : ℝ := (ε / 2).toReal / (Cμ + 1) with hδ_def
      have hε2_pos : 0 < (ε / 2).toReal := by
        rw [ENNReal.toReal_pos_iff]
        exact ⟨pos_iff_ne_zero.mpr h2, lt_top_iff_ne_top.mpr h_top⟩
      have hCμ1_pos : 0 < Cμ + 1 := by linarith
      have hδ_pos : 0 < δ_real := by positivity
      refine ⟨δ_real, hδ_pos, ?_⟩
      -- `Cμ_enn * ENNReal.ofReal δ_real ≤ ε / 2`.
      -- ENNReal calculation: rewrite Cμ_enn = ENNReal.ofReal Cμ (since Cμ_enn ne_top).
      have hCμ_enn_eq : Cμ_enn = ENNReal.ofReal Cμ := by
        rw [hCμ_def, ENNReal.ofReal_toReal hCμ_enn_ne_top]
      rw [hCμ_enn_eq, ← ENNReal.ofReal_mul hCμ_nn]
      -- Cμ * δ_real = Cμ * ((ε/2).toReal / (Cμ + 1)) ≤ (ε/2).toReal.
      have hreal_le : Cμ * δ_real ≤ (ε / 2).toReal := by
        rw [hδ_def]
        rw [mul_comm Cμ ((ε / 2).toReal / (Cμ + 1))]
        rw [div_mul_eq_mul_div]
        rw [div_le_iff₀ hCμ1_pos]
        nlinarith
      calc ENNReal.ofReal (Cμ * δ_real)
          ≤ ENNReal.ofReal (ε / 2).toReal := ENNReal.ofReal_le_ofReal hreal_le
        _ = ε / 2 := ENNReal.ofReal_toReal h_top
  -- Step 2: Stone-Weierstrass.
  set ψ_cont : C(M, ℝ) := ψ_bc.toContinuousMap with hψ_cont_def
  obtain ⟨f_smooth, hf_close⟩ := exists_smoothScalar_sup_close (I := I) (M := M) g ψ_cont hδ_pos
  -- Pointwise bound.
  have h_pointwise_bound : ∀ x : M, ‖f_smooth.toFun x - ψ_bc x‖ ≤ δ_real := by
    intro x
    have heq : f_smooth.toFun x - ψ_bc x =
        (f_smooth.toContinuousMap - ψ_cont) x := rfl
    rw [heq]
    exact (norm_coe_le_norm _ x).trans hf_close.le
  -- The eLpNorm bound from the helper.
  have h_eLpNorm_diff :
      eLpNorm (fun x : M => f_smooth.toFun x - ψ_bc x) 2 μvol ≤
        Cμ_enn * ENNReal.ofReal δ_real :=
    eLpNorm_smooth_sub_bc_le (I := I) (M := M) g f_smooth ψ_bc δ_real h_pointwise_bound
  refine ⟨f_smooth, ?_⟩
  -- Triangle inequality on `edist`, then bound each term.
  have hψ_mem : MemLp (ψ_bc : M → ℝ) 2 μvol := _hψ_mem
  -- First term: edist ≤ Cμ_enn * δ_real ≤ ε / 2.
  have h1 :
      edist (f_smooth.memLp_two.toLp f_smooth.toFun)
          (hψ_mem.toLp (ψ_bc : M → ℝ)) ≤ ε / 2 := by
    rw [edist_toLp_eq_eLpNorm]
    exact le_trans h_eLpNorm_diff hδ_bound
  -- Second term: edist (ψ.toLp) (h.toLp) ≤ ε / 2.
  have h2_bound :
      edist (hψ_mem.toLp (ψ_bc : M → ℝ)) (h_mem.toLp h) ≤ ε / 2 := by
    rw [edist_toLp_eq_eLpNorm]
    -- eLpNorm (ψ - h) = eLpNorm (h - ψ) by `eLpNorm_neg`.
    rw [show (fun x : M => (ψ_bc : M → ℝ) x - h x) = -(fun x : M => h x - ψ_bc x) from
        funext fun x => by rw [Pi.neg_apply]; ring]
    rw [eLpNorm_neg]
    exact hψ_eLpNorm_le
  -- Combine via two-term triangle.
  calc edist (f_smooth.memLp_two.toLp f_smooth.toFun) (h_mem.toLp h)
      ≤ edist (f_smooth.memLp_two.toLp f_smooth.toFun)
            (hψ_mem.toLp (ψ_bc : M → ℝ)) +
          edist (hψ_mem.toLp (ψ_bc : M → ℝ)) (h_mem.toLp h) :=
        edist_triangle _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2_bound
    _ = ε := ENNReal.add_halves _

/-- Smooth scalars on a closed Riemannian manifold are dense in `Lp ℝ 2 μ_g`.

Proof: Stone–Weierstrass gives smooth-dense-in-continuous in sup norm, and
continuous-dense-in-`Lp` from `MemLp.exists_boundedContinuous_eLpNorm_sub_le`. -/
theorem denseRange_smoothToLp (g : SmoothRiemannianMetric I M) :
    DenseRange (smoothToLp (I := I) (M := M) g) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  haveI : (riemannianVolumeMeasure (I := I) (M := M) g).WeaklyRegular :=
    (riemannianVolumeMeasure_regular (I := I) (M := M) g).weaklyRegular
  intro v
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun ε hε ↦ ?_
  obtain ⟨f, hf⟩ := exists_smoothToLp_close_to_memLp (I := I) (M := M) g
    (v : M → ℝ) (Lp.memLp v) (ne_of_gt hε)
  refine ⟨smoothToLp (I := I) (M := M) g f, mem_range_self _, ?_⟩
  -- After `Metric.mem_closedEBall`, the goal is `edist v ((smoothToLp g) f) ≤ ε`.
  rw [Metric.mem_closedEBall]
  -- `(smoothToLp g) f = f.memLp_two.toLp f.toFun` definitionally; rewrite it.
  have h_smooth_eq : (smoothToLp (I := I) (M := M) g f : Lp ℝ 2 _) =
      f.memLp_two.toLp f.toFun := rfl
  rw [h_smooth_eq]
  -- Goal: `edist v (f.memLp_two.toLp f.toFun) ≤ ε`.
  -- hf : edist (f.memLp_two.toLp f.toFun) ((Lp.memLp v).toLp ↑↑v) ≤ ε.
  -- v's class equals `(Lp.memLp v).toLp ↑↑v`, so we rewrite `v`.
  have h_v_eq : v = (Lp.memLp v).toLp (v : M → ℝ) := (Lp.toLp_coeFn v _).symm
  conv_lhs => rw [show v = (Lp.memLp v).toLp (v : M → ℝ) from h_v_eq]
  -- Goal now matches `hf` after `edist_comm`.
  exact hf

/-! ## Density of `H1ComplToLp` in `Lp ℝ 2 μ_g` -/

/-- The continuous linear map `H1ComplToLp g : H1Compl g →L[ℝ] Lp ℝ 2 μ_g`
has dense range. This follows from `denseRange_smoothToLp` together with the
identity `H1ComplToLp ∘ smoothToH1Compl = smoothToLp`. -/
theorem denseRange_H1ComplToLp (g : SmoothRiemannianMetric I M) :
    DenseRange (H1ComplToLp (I := I) (M := M) g) := by
  -- `range(H1ComplToLp) ⊇ range(smoothToLp)` because
  -- `H1ComplToLp(smoothToH1Compl u) = smoothToLp u`.
  -- `range(smoothToLp)` is dense, so `range(H1ComplToLp)` is dense.
  refine Dense.mono ?_ (denseRange_smoothToLp (I := I) (M := M) g)
  rintro y ⟨u, hu⟩
  refine ⟨smoothToH1Compl (I := I) (M := M) g u, ?_⟩
  rw [H1ComplToLp_smoothToH1Compl]
  exact hu

end Laplacian
end Analysis
end DifferentialGeometry

end
