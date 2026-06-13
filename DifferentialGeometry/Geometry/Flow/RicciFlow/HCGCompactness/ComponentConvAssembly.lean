import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ComponentConvTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvBridge

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# P3 final assembly — Gap B → `metricPreconvInf` (MSM135 Ch3 `lbl351`)

This file assembles the covariant-tower component convergence into the spatial P3
endpoint `metricPreconvInf`.  It consumes (does NOT edit):

* `bumpTowerCarrier_all`, `hbase_of_framePairs`, `exists_frameData`,
  `exists_chart_engineInput_family` (`ComponentConvTower.lean`) — the all-orders
  bump-carrier convergence induction and its frame/base inputs;
* `metricPreconv_gInf`, `exists_engine_frameCInfConv(_eq_gm)`,
  `componentConv_covDeriv_zero`, `exists_diag_subseq` (`MetricPreconvDiag.lean`) —
  the limit metric `gInf` and the engine frame-component convergence;
* `metricDerivNorm_le_compSq_uniform`, `metricCInfConvOnCompacts_of_normConv`
  (`MetricPreconvBridge.lean`) — the norm bridge and the spatial endpoint.

The four assembly steps (ComponentConvTower.md "REMAINING"): (1) diagonal → one `φ`;
(2) limit-pinning; (3) feed `hbase_of_framePairs` → `bumpTowerCarrier_all`;
(4) finite-cover extraction → `componentConv_covDeriv_of_chartCInf` → `metricPreconvInf`.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection
open Tensor0SBundle TensorLieDeriv
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- **Finite-family `C∞`-on-compacts diagonal.**  Given a finite family of Euclidean
section sequences, each `ContDiff ⊤` with uniform iterated-derivative bounds on every
compact, one subsequence `φ` makes every member converge `C∞`-on-compacts (each to its
own limit).  Finite fold of `exists_cInf_subseq`, keeping earlier members convergent
under the further refinement via `MapCInfConvOnCompacts.comp_subseq`. -/
theorem exists_cInf_subseq_finiteFamily
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F]
    {ι : Type*} (s : Finset ι) (Φ : ι → ℕ → E → F)
    (hΦ : ∀ p ∈ s, ∀ k, ContDiff Real (⊤ : ℕ∞) (Φ p k))
    (hbdd : ∀ p ∈ s, ∀ r : ℕ, ∀ K : Set E, IsCompact K →
        ∃ Mr : Real, ∀ k, ∀ x ∈ K, ‖iteratedFDeriv Real r (Φ p k) x‖ ≤ Mr) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∀ p ∈ s,
      ∃ Φinf : E → F, MapCInfConvOnCompacts (Set.univ : Set E) (fun k => Φ p (φ k)) Φinf := by
  classical
  revert hΦ hbdd
  induction s using Finset.induction with
  | empty =>
    intro _ _
    exact ⟨id, strictMono_id, fun p hp => by simp at hp⟩
  | @insert a s ha IH =>
    intro hΦ hbdd
    obtain ⟨φ, hφ, hconv⟩ := IH (fun p hp => hΦ p (Finset.mem_insert_of_mem hp))
      (fun p hp => hbdd p (Finset.mem_insert_of_mem hp))
    obtain ⟨ψ, Φa, hψ, -, hΦaconv⟩ :=
      exists_cInf_subseq (fun k => Φ a (φ k))
        (fun k => hΦ a (Finset.mem_insert_self a s) (φ k))
        (fun r K hK => by
          obtain ⟨Mr, hMr⟩ := hbdd a (Finset.mem_insert_self a s) r K hK
          exact ⟨Mr, fun k x hx => hMr (φ k) x hx⟩)
    refine ⟨φ ∘ ψ, hφ.comp hψ, fun p hp => ?_⟩
    rcases Finset.mem_insert.mp hp with rfl | hps
    · exact ⟨Φa, hΦaconv⟩
    · obtain ⟨Φinf, hΦinf⟩ := hconv p hps
      exact ⟨Φinf, hΦinf.comp_subseq hψ⟩

/-- **Step 1 — the `n²`-frame-pair diagonal (shared `χ`, one subsequence).**  For a
chart center `x₀`, a compact `K₀ ⊆ source`, and the chart-constant frame `frame`,
the `n²` order-0 frame-pair carriers `![frameᵢ, frameⱼ]` (built against the metric
sequence `gSeq ∘ φ`) share ONE bump `χ` (via `exists_chart_engineInput_family`) and,
via `exists_cInf_subseq_finiteFamily`, ONE further subsequence `ψ` along which every
pair converges `C∞`-on-compacts to some limit.  This is the `hpairs` precursor; the
limit is pinned to the `gInf` carrier in `framePairs_pinned`. -/
theorem exists_framePairs_diag
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (frame : Fin (Module.finrank Real E) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (φ : ℕ → ℕ) :
    ∃ (ψ : ℕ → ℕ) (χ : E → Real),
      StrictMono ψ ∧ ContDiff Real (∞ : WithTop ℕ∞) χ ∧
      tsupport χ ⊆ (extChartAt I x₀).target ∧
      (∀ y ∈ K₀, χ (extChartAt I x₀ y) = 1) ∧
      ∀ (i j : Fin (Module.finrank Real E)), ∃ Φinf : E → Real,
        MapCInfConvOnCompacts (Set.univ : Set E)
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k)))) 0) w
                (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z) Φinf := by
  classical
  set Vfam : (Fin (Module.finrank Real E) × Fin (Module.finrank Real E)) →
      Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun p => Function.update (fun _ : Fin 2 => frame p.1) 1 (frame p.2) with hVfam
  have hbdd' : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q ((gSeq ∘ φ) k) gRef z ≤ C := by
    intro q K hK; obtain ⟨C, hC⟩ := hbdd q K hK; exact ⟨C, fun k z hz => hC (φ k) z hz⟩
  obtain ⟨χ, hχcd, htsupp, hχ1, hfam⟩ :=
    exists_chart_engineInput_family (I := I) gRef (gSeq ∘ φ) hbdd' x₀ Vfam hK₀ hK₀chart
  set Φ : (Fin (Module.finrank Real E) × Fin (Module.finrank Real E)) → ℕ → E → Real :=
    fun p k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
      (fun w : M => (covDerivOfField (I := I) gRef
        (Tensor0SBundle.metricTensorField (I := I) ((gSeq ∘ φ) k)) 0) w
          (fun a => Vfam p a w)) z with hΦ
  obtain ⟨ψ, hψ, hconv⟩ :=
    exists_cInf_subseq_finiteFamily (Finset.univ : Finset (Fin (Module.finrank Real E) ×
        Fin (Module.finrank Real E))) Φ
      (fun p _ k => (hfam p).1 k)
      (fun p _ r K _ => by
        obtain ⟨Mr, hMr⟩ := (hfam p).2 r
        exact ⟨Mr, fun k x _ => hMr k x⟩)
  refine ⟨ψ, χ, hψ, hχcd, htsupp, hχ1, fun i j => ?_⟩
  obtain ⟨Φinf, hΦinf⟩ := hconv (i, j) (Finset.mem_univ _)
  exact ⟨Φinf, hΦinf⟩

/-- **Step 2 — limit pinning ⇒ `hpairs`.**  The per-pair `C∞`-on-compacts limit of
`exists_framePairs_diag` is pinned to the `gInf` frame-pair carrier by pointwise-limit
uniqueness (`tendsto_of_cInf` + `metricPreconv_gInf`'s `hconv` + `tendsto_nhds_unique`),
yielding the `hpairs` input to `hbase_of_framePairs`.  `A0Seq k = metricTensorField
(gSeq (φ (ψ k)))`, `A0inf = metricTensorField gInf`. -/
theorem framePairs_pinned
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (frame : Fin (Module.finrank Real E) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (φ : ℕ → ℕ) (gInf : SmoothRiemannianMetric I M)
    (hconv : ∀ x : M, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop
      (nhds (gInf.inner x))) :
    ∃ (ψ : ℕ → ℕ) (χ : E → Real),
      StrictMono ψ ∧ ContDiff Real (∞ : WithTop ℕ∞) χ ∧
      tsupport χ ⊆ (extChartAt I x₀).target ∧
      (∀ y ∈ K₀, χ (extChartAt I x₀ y) = 1) ∧
      ∀ (i j : Fin (Module.finrank Real E)),
        MapCInfConvOnCompacts (Set.univ : Set E)
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k)))) 0) w
                (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z)
          (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) gInf) 0) w
                (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z) := by
  classical
  obtain ⟨ψ, χ, hψ, hχcd, htsupp, hχ1, hpairs0⟩ :=
    exists_framePairs_diag (I := I) gRef gSeq hbdd x₀ hK₀ hK₀chart frame φ
  refine ⟨ψ, χ, hψ, hχcd, htsupp, hχ1, fun i j => ?_⟩
  obtain ⟨Φinf, hΦinf⟩ := hpairs0 i j
  -- carrier value at a point, for any metric `g`
  have hinner : ∀ (g : SmoothRiemannianMetric I M) (w : M),
      (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) g) 0) w
          (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)
        = g.inner w (frame i w) (frame j w) := by
    intro g w
    show (Tensor0SBundle.metricTensorField (I := I) g) w
        (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)
      = g.inner w (frame i w) (frame j w)
    rw [Tensor0SBundle.metricTensorField_apply]
    simp [Function.update_of_ne, Function.update_self]
  have hval : ∀ (g : SmoothRiemannianMetric I M) (z : E),
      χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef
            (Tensor0SBundle.metricTensorField (I := I) g) 0) w
              (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z
        = χ z * g.inner ((extChartAt I x₀).symm z)
            (frame i ((extChartAt I x₀).symm z)) (frame j ((extChartAt I x₀).symm z)) := by
    intro g z
    rw [writtenInExtChartAt_real_apply, hinner g ((extChartAt I x₀).symm z)]
  have hpin : Φinf = (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
      (fun w : M => (covDerivOfField (I := I) gRef
        (Tensor0SBundle.metricTensorField (I := I) gInf) 0) w
          (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z) := by
    funext z
    have hseq := tendsto_of_cInf hΦinf (Set.mem_univ z)
    have hlim : Filter.Tendsto
        (fun k => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef
            (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k)))) 0) w
              (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z)
        Filter.atTop (nhds (χ z * (gInf.inner ((extChartAt I x₀).symm z)
          (frame i ((extChartAt I x₀).symm z)) (frame j ((extChartAt I x₀).symm z))))) := by
      have hcont : Continuous
          (fun η : TangentSpace I ((extChartAt I x₀).symm z) →L[Real]
              TangentSpace I ((extChartAt I x₀).symm z) →L[Real] Real =>
            η (frame i ((extChartAt I x₀).symm z)) (frame j ((extChartAt I x₀).symm z))) :=
        ((ContinuousLinearMap.apply Real Real
            (frame j ((extChartAt I x₀).symm z))).comp
          (ContinuousLinearMap.apply Real (TangentSpace I ((extChartAt I x₀).symm z) →L[Real] Real)
            (frame i ((extChartAt I x₀).symm z)))).continuous
      have hbase := ((hcont.tendsto _).comp
        ((hconv ((extChartAt I x₀).symm z)).comp hψ.tendsto_atTop)).const_mul (χ z)
      refine hbase.congr (fun k => ?_)
      rw [hval (gSeq (φ (ψ k))) z]
      simp only [Function.comp_apply]
    rw [hval gInf z]
    exact tendsto_nhds_unique hseq hlim
  rw [hpin] at hΦinf
  exact hΦinf

/-- **Step 3 — feed `hpairs` into the tower induction.**  Combines `exists_frameData`
(frame), `framePairs_pinned` (`hpairs`), and `bumpTowerCarrier_all` (via
`hbase_of_framePairs`) to produce, along one subsequence `ψ`, the all-orders
`C∞`-on-compacts convergence of the bump tower carriers on the open patch
`U = target ∩ symm⁻¹(interior K₀)` — for EVERY covariant order `a` and section tuple. -/
theorem exists_tower_conv
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (φ : ℕ → ℕ) (gInf : SmoothRiemannianMetric I M)
    (hconv : ∀ x : M, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop
      (nhds (gInf.inner x))) :
    ∃ (ψ : ℕ → ℕ) (χ : E → Real) (U : Set E),
      StrictMono ψ ∧ IsOpen U ∧
      (extChartAt I x₀ '' interior K₀ ⊆ U) ∧ Set.EqOn χ 1 U ∧
      ∀ (a : ℕ) (V : Fin (a + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _)),
        MapCInfConvOnCompacts U
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k)))) a) w
                (fun a => V a w)) z)
          (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) gInf) a) w
                (fun a => V a w)) z) := by
  classical
  obtain ⟨frame, vbasis, hframeσ, hspan⟩ := exists_frameData (I := I) x₀ hK₀ hK₀chart
  obtain ⟨ψ, χ, hψ, hχcd, htsupp, hχ1, hpairs⟩ :=
    framePairs_pinned (I := I) gRef gSeq hbdd x₀ hK₀ hK₀chart frame φ gInf hconv
  -- the open patch `U = target ∩ symm⁻¹(interior K₀)`
  set U : Set E := (extChartAt I x₀).target ∩
    (extChartAt I x₀).symm ⁻¹' interior K₀ with hUdef
  have hUopen : IsOpen U :=
    (continuousOn_extChartAt_symm (I := I) x₀).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := I) x₀) isOpen_interior
  have hUtarget : U ⊆ (extChartAt I x₀).target := fun z hz => hz.1
  have hUKc : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ K₀ := fun z hz => interior_subset hz.2
  have hχU : Set.EqOn χ 1 U := by
    intro z hz
    have hzK₀ : (extChartAt I x₀).symm z ∈ K₀ := hUKc z hz
    have := hχ1 ((extChartAt I x₀).symm z) hzK₀
    rwa [(extChartAt I x₀).right_inv hz.1] at this
  have hImg : extChartAt I x₀ '' interior K₀ ⊆ U := by
    rintro z ⟨y, hy, rfl⟩
    have hysrc : y ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source]; exact hK₀chart (interior_subset hy)
    exact ⟨(extChartAt I x₀).map_source hysrc, by
      rw [Set.mem_preimage, (extChartAt I x₀).left_inv hysrc]; exact hy⟩
  refine ⟨ψ, χ, U, hψ, hUopen, hImg, hχU, fun a V => ?_⟩
  -- restrict `hpairs` from `univ` to `U`
  have hpairsU : ∀ (i j : Fin (Module.finrank Real E)),
      MapCInfConvOnCompacts U
        (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef
            (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k)))) 0) w
              (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z)
        (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef
            (Tensor0SBundle.metricTensorField (I := I) gInf) 0) w
              (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z) :=
    fun i j K hK hKU p => (hpairs i j) K hK (Set.subset_univ K) p
  exact bumpTowerCarrier_all (I := I) gRef
    (fun k => Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k))))
    (Tensor0SBundle.metricTensorField (I := I) gInf) x₀ hχcd htsupp hUopen hχU hUtarget
    hK₀chart hUKc Finset.univ frame vbasis hframeσ hspan
    (fun V => hbase_of_framePairs (I := I) gRef
      (fun k => Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k))))
      (Tensor0SBundle.metricTensorField (I := I) gInf) x₀ hχcd htsupp hUopen hχU hUtarget
      hUKc Finset.univ frame hspan hpairsU V) a V

/-- **Step 4a — pointwise covariant-tower component convergence (general order
`a`).**  The `a ≥ 1` analogue of `componentConv_covDeriv_zero`: along a further
subsequence `ψ`, the order-`a` covariant-tower component in ANY fibre basis `b`
converges at the fixed point `x`.  POINTWISE (the norm bridge's component basis is
point-dependent, so a uniform statement is ill-typed — planner ruling).  Proof:
chart at `x`, `exists_tower_conv`, `tendsto_of_cInf` at `extChartAt x x`; the section
`V_q` with `V_q x = b (I0 q)` is `ContMDiffSection.exists_eq_at_gen`, and the carrier
value equals `component0S b (metricCovDeriv g gRef a x) I0` (`component0S_apply` +
`metricCovDeriv_eq_covDerivOfField`, both `rfl`). -/
theorem componentConv_covDeriv_of_chartCInf
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (φ : ℕ → ℕ) (gInf : SmoothRiemannianMetric I M)
    (hconv : ∀ x : M, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop
      (nhds (gInf.inner x)))
    (a : ℕ) (x : M)
    (b : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x))
    (I0 : Fin (a + 2) → Fin (Module.finrank Real E)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Filter.Tendsto (fun m => Tensor0SBundle.component0S (I := I) b
          (metricCovDeriv (I := I) (gSeq (φ (ψ m))) gRef a x) I0) Filter.atTop
        (nhds (Tensor0SBundle.component0S (I := I) b
          (metricCovDeriv (I := I) gInf gRef a x) I0)) := by
  classical
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨K₀, hK₀cpt, hxint, hK₀src⟩ :=
    exists_compact_subset (chartAt H x).open_source (mem_chart_source H x)
  obtain ⟨ψ, χ, U, hψ, hUopen, hImg, hχU, htower⟩ :=
    exists_tower_conv (I := I) gRef gSeq hbdd x hK₀cpt hK₀src φ gInf hconv
  refine ⟨ψ, hψ, ?_⟩
  have hxU : extChartAt I x x ∈ U := hImg ⟨x, hxint, rfl⟩
  set V : Fin (a + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun q => (ContMDiffSection.exists_eq_at_gen (I := I) (n := (⊤ : ℕ∞)) x (b (I0 q))).choose
    with hVdef
  have hVval : ∀ q, V q x = b (I0 q) := fun q =>
    (ContMDiffSection.exists_eq_at_gen (I := I) (n := (⊤ : ℕ∞)) x (b (I0 q))).choose_spec
  have hcar : ∀ (g : SmoothRiemannianMetric I M),
      χ (extChartAt I x x) * writtenInExtChartAt I 𝓘(Real, Real) x
          (fun w : M => (covDerivOfField (I := I) gRef
            (Tensor0SBundle.metricTensorField (I := I) g) a) w (fun q => V q w)) (extChartAt I x x)
        = Tensor0SBundle.component0S (I := I) b (metricCovDeriv (I := I) g gRef a x) I0 := by
    intro g
    rw [hχU hxU, Pi.one_apply, one_mul, writtenInExtChartAt_real_apply,
      (extChartAt I x).left_inv (mem_extChartAt_source x)]
    simp only [hVval]
    rfl
  have htend := tendsto_of_cInf (htower a V) hxU
  rw [hcar gInf] at htend
  exact htend.congr (fun k => hcar (gSeq (φ (ψ k))))

/-- **Constant-`M` expansion (4b-ii algebraic core).**  A chart-constant frame vector
for the basis `basisE` of `E` is a CONSTANT-coefficient (`z`-independent) linear combo
of the chart-constant frame vectors for the model basis `finBasis`, the coefficients
being the `basisE`-in-`finBasis` change of basis.  Both sides are `(trivAt x₀).symmL p`
(linear) applied to a fixed `E`-vector, so this is `Basis.sum_repr` + `map_sum`/`map_smul`. -/
theorem tangentConst_basis_expand (x₀ : M)
    (basisE : Module.Basis (Fin (Module.finrank Real E)) Real E)
    (i : Fin (Module.finrank Real E)) (p : M) :
    tangentConstInChart (𝕜 := Real) (I := I) x₀ (basisE i) p
      = ∑ j : Fin (Module.finrank Real E),
          (Module.finBasis Real E).repr (basisE i) j •
            tangentConstInChart (𝕜 := Real) (I := I) x₀ (Module.finBasis Real E j) p := by
  simp only [tangentConstInChart_apply]
  conv_lhs => rw [← (Module.finBasis Real E).sum_repr (basisE i)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]

/-- **The norm-bridge basis `bz` IS the chart-constant frame (4b-ii).**  The basis
`metricDerivNorm_le_compSq_uniform` uses at `z`, `(trivAt x).localFrame(basisE).toBasisAt hz`,
equals the chart-constant frame `tangentConstInChart x (basisE i) z`
(`IsLocalFrameOn.toBasisAt_coe` + `localFrame_apply_of_mem_baseSet`). -/
theorem bz_eq_tangentConst (x : M)
    (basisE : Module.Basis (Fin (Module.finrank Real E)) Real E)
    (i : Fin (Module.finrank Real E)) {z : M}
    (hz : z ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet) :
    (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
        I 1 basisE).toBasisAt hz) i
      = tangentConstInChart (𝕜 := Real) (I := I) x (basisE i) z := by
  set e := trivializationAt E (TangentSpace I : M → Type _) x with he
  rw [IsLocalFrameOn.toBasisAt_coe, e.localFrame_apply_of_mem_baseSet basisE hz]
  simp [Bundle.Trivialization.basisAt, tangentConstInChart_apply, he]

/-- **(4b-ii a) `component0S bz` IS a coordinate-frame tower value.**  The good-frame
component of the covariant tower equals the tower evaluated on the constant-coefficient
section combo `V^{I0}_q = Σ_j (finBasis.repr (basisE (I0 q)) j) • frame_j` (whose value at
`z` is `bz (I0 q)`), for `z ∈ baseSet ∩ Kc` (where the chart-constant frame bridge holds).
Combines `component0S_apply`, `bz_eq_tangentConst`, `tangentConst_basis_expand`, the
section-sum eval, and `hframeσ`. -/
theorem componentBz_eq_covDeriv
    (gRef : SmoothRiemannianMetric I M) (x : M)
    (basisE : Module.Basis (Fin (Module.finrank Real E)) Real E)
    (frame : Fin (Module.finrank Real E) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {Kc : Set M}
    (hframeσ : ∀ i, ∀ᶠ y in 𝓝ˢ Kc, frame i y
       = tangentConstInChart (𝕜 := Real) (I := I) x (Module.finBasis Real E i) y)
    (a : ℕ) (I0 : Fin (a + 2) → Fin (Module.finrank Real E))
    (g : SmoothRiemannianMetric I M)
    {z : M} (hzbase : z ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet)
    (hzKc : z ∈ Kc) :
    Tensor0SBundle.component0S (I := I)
        (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
            I 1 basisE).toBasisAt hzbase)
        (metricCovDeriv (I := I) g gRef a z) I0
      = (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) g) a) z
          (fun q => (∑ j : Fin (Module.finrank Real E),
            (Module.finBasis Real E).repr (basisE (I0 q)) j • frame j) z) := by
  rw [Tensor0SBundle.component0S_apply]
  show (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) g) a) z
      (fun q => (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
          I 1 basisE).toBasisAt hzbase) (I0 q))
    = (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) g) a) z
      (fun q => (∑ j : Fin (Module.finrank Real E),
        (Module.finBasis Real E).repr (basisE (I0 q)) j • frame j) z)
  congr 1
  funext q
  rw [bz_eq_tangentConst, tangentConst_basis_expand, ContMDiffSection.finset_sum_apply_gen]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [(hframeσ j).self_of_nhdsSet z hzKc]

end HCGCompactness
end DifferentialGeometry
