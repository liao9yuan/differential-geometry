import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRatePro
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueSdec
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueDensReg
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRmReg
import DifferentialGeometry.Analysis.Integration.Measure.FamilyContinuity

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Slab-uniform inputs of the forward-uniqueness endgame

`Evolution/ForwardUniqueAssembly.lean` packages the six slab-uniform pointwise estimates that
the Grönwall step consumes into `ForwardUniqueSlab g₁ g₂ Adot Sfield Uflux rem a c C_A C_R
C_Ric C_V C_U C_rem`, and `Evolution/ForwardUniqueWiring.lean` leaves an instance of it
(`hbounds`) as the dominant residual hypothesis of `forward_unique_of_gram`.  Every named
sub-producer of those six fields (`fluxNormSq_le`, `remNormSq_le`, `ricciDiffSq_le`,
`connDiffDot_normSq_le`, …) takes a **slab-uniform background norm** as an explicit argument,
and nothing in the tree supplies one.  This file is the layer that does.

## Main results

* `slabBound` / `slabBound_ioo` — the compactness engine: a jointly continuous scalar on the
  closed subslab `Icc a c ×ˢ univ` of a compact manifold is bounded, so every background norm
  quantity produces its constant by the extreme value theorem.  This is the piece
  `ForwardUniqueWiring.md` records as missing ("a genuine compactness-of-`Icc a c × M`
  sup-bound layer is still missing").
* `normSqSlabBound` — the same statement in the shape the sub-producers consume: a bound
  `|A t x|²_{g t} ≤ B` valid on the whole subslab.
* `ricciSlabLe` — the **`ricciLe` field of `ForwardUniqueSlab`, unconditionally**, with
  `C_Ric = n⁴`.  No background norm and no compactness enter: `ricciDiff_eq_trace` exhibits the
  Ricci difference as a `g₁`-trace of a slot permutation of `S₀₄`, `normSq_ricciTraceRep` says
  the permutation is a fibre isometry, so `ricciDiffSq_le` applies with `B = 0`.
* `tracePairSq_le` — `(tr_g Q)² ≤ n·|Q|²_g`; with it, `volSlabSup` gives the **`volLe` field**
  from the flow identity `tr_{g₁}(∂ₜg₁) = −2·tr_{g₁}Ric₁` and the Ricci sup alone, so no joint
  continuity of the volume drift is needed.
* `fu_metric_comp_le` / `metricCompSlab` — the **pointwise metric comparison** `g₁ ≤ Λ·g₂`, the `Λ`
  input of `connDiffDot_normSq_le`, with `Λ = √(sup |g₁|²_{g₂})`.  No unit-sphere-bundle
  compactness enters: it is the ON-frame component estimate with both slots equal.
* `nablaRicSlabSup` — the closed-slab bound for `|∇Ric|²`, obtained from the
  one-sided chart derivative tower and `nablaRicChartJoint`.
* `nablaKRmSlabSup`, `crossRm1SlabSup`, `crossRm2SlabSup` — the corresponding
  rank-uniform own-curvature and rank-five/rank-six cross-curvature bounds used
  by the final remainder estimate.
* `movingReactAbs_le` — the **rank-uniform moving-metric reaction bound** owed since plan №25:
  `|movingReact0S (g t) x s Q W| ≤ 2·s·n^{2s+2}·√(|Q|²)·|W|²`, whence `reactSlabLe`, the
  **`reactLe` field**.
* `reLowerPairSq_le` — the missing norm bound for the re-lowering defect carrier
  `reLowerPair`: `|tr_g(σ(T ⊗ K))|²_g ≤ n^{s+4}·|T|²_g·|K|²_g`.
* `sdecFluxSq_le` — the **`fluxLe` estimate at the carrier the wiring actually builds**
  (`sdecUflux`, not `rmDiffFlux`): `|U′|²_{g₁} ≤ C(n)·|A₀₃|²_{g₁}·(background)`.
* `fluxSlabLe` — the same, absorbed into the energy density: the **`fluxLe` field** with
  `C_U = 32·n⁵·B₂ + 8·n¹⁰·B_P·B_g` exhibited in terms of three background norms.

## What is *not* here

`remLe` and `adotLe` are assembled in the wiring layer.  This file supplies
`adotLe`'s previously missing closed-slab `B₁ ≥ |∇Ric₂|²`; the remainder still
needs the full rank-five and rank-six curvature derivative sups recorded in
`ForwardUniqueSup.md`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]

section SlabSup

/-! ## The compactness engine

`ForwardUniqueSlab`'s constants are slab-local by design: they are produced per closed
subslab `Icc a c`, `c ∈ Ioo a b`.  On a compact manifold `Icc a c ×ˢ univ` is compact, so a
jointly continuous scalar on it is bounded — and that single fact is what turns every
background norm quantity (`|Ric₁|²`, `|Rm₂|²`, `|∇²Rm₂|²`, the volume drift, …) into a
constant.  The two statements below are the only form in which compactness enters the lane. -/

variable {a c : Real}

/-- **The slab sup.**  A jointly continuous scalar on the closed subslab is bounded there, by
a nonnegative constant.  The conclusion is two-sided (`|F t x| ≤ C`) so that it also serves the
fields — such as `volLe` — that need a bound on a signed quantity. -/
theorem slabBound (F : Real → M → Real)
    (hF : ContinuousOn (fun p : Real × M => F p.1 p.2) (Icc a c ×ˢ (univ : Set M))) :
    ∃ C : Real, 0 ≤ C ∧ ∀ t ∈ Icc a c, ∀ x : M, |F t x| ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set M))).exists_bound_of_continuousOn hF
  refine ⟨max C 0, le_max_right _ _, fun t ht x => ?_⟩
  have h := hC (t, x) ⟨ht, mem_univ x⟩
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

/-- **The slab sup, in the shape `ForwardUniqueSlab` quantifies over.**  Its six fields range
over the *open* interval `Ioo a c`, whose closure is the compact `Icc a c`; so continuity up to
the closed initial edge is exactly what a uniform constant on `Ioo a c` costs. -/
theorem slabBound_ioo (F : Real → M → Real)
    (hF : ContinuousOn (fun p : Real × M => F p.1 p.2) (Icc a c ×ˢ (univ : Set M))) :
    ∃ C : Real, 0 ≤ C ∧ ∀ t ∈ Ioo a c, ∀ x : M, F t x ≤ C := by
  obtain ⟨C, hC0, hC⟩ := slabBound (M := M) F hF
  exact ⟨C, hC0, fun t ht x => (le_abs_self _).trans (hC t (Ioo_subset_Icc_self ht) x)⟩

/-- **The background-norm sup.**  The five named sub-producers of `ForwardUniqueSlab`'s fields
take their background bounds in exactly this shape: a single constant `B` with
`|A t x|²_{g t} ≤ B` for every point of the closed subslab. -/
theorem normSqSlabBound {s : Nat} (g : Real → SmoothRiemannianMetric I M)
    (A : Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (hA : ContinuousOn (fun p : Real × M => normSq0S (I := I) (g p.1) p.2 s (A p.1 p.2))
      (Icc a c ×ˢ (univ : Set M))) :
    ∃ B : Real, 0 ≤ B ∧
      ∀ t ∈ Icc a c, ∀ x : M, normSq0S (I := I) (g t) x s (A t x) ≤ B := by
  obtain ⟨B, hB0, hB⟩ := slabBound (M := M) (fun t x => normSq0S (I := I) (g t) x s (A t x)) hA
  exact ⟨B, hB0, fun t ht x => (le_abs_self _).trans (hB t ht x)⟩

end SlabSup

section RicciField

/-! ## `ricciLe`, unconditionally

The Ricci-difference field of `ForwardUniqueSlab` needs no background norm at all.  Both
flows' Ricci tensors are the `g₁`-trace of the *same* `(0,4)` carrier — the Kotschwar
difference `S₀₄`, up to the slot permutation `rm04TraceSlots` — so `ricciDiffSq_le` applies
with a vanishing metric-difference coefficient, and its output is already the
curvature-difference third of the energy density. -/

/-- **The `ricciLe` field of `ForwardUniqueSlab`, with `C_Ric = n⁴` and no hypotheses.**

`|Ric₁ − Ric₂|²_{g₁} ≤ n⁴ · density`,  `n = finrank ℝ E`.

`ricciDiff_eq_trace` writes the difference as `tr_{g₁}(σ S₀₄)`, `normSq_ricciTraceRep` says the
slot permutation `σ` is a fibre isometry so the trace representative has norm exactly
`rmDiffSq`, and `rmDiffSq_le_dens` absorbs it into the density. -/
theorem ricciSlabLe (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    normSq0S (I := I) (g₁ t) x 2
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) ≤
      (Module.finrank Real E : Real) ^ 4 * forwardUniqueDensity (I := I) g₁ g₂ t x := by
  have hrep : normSq0S (I := I) (g₁ t) x 4
      (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)) ≤
      rmDiffSq (I := I) (g₁ t) (g₂ t) x + (0 : Real) * metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [normSq_ricciTraceRep (I := I) (g₁ t) (g₂ t) x]
    exact le_of_eq (by ring)
  refine (ricciDiffSq_le (I := I) (g₁ t) (g₂ t) x
    (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
      (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))
    (ricciDiff_eq_trace (I := I) (g₁ t) (g₂ t) x) hrep).trans ?_
  have hdens := rmDiffSq_le_dens (I := I) g₁ g₂ t x
  have hpow : (0 : Real) ≤ (Module.finrank Real E : Real) ^ 4 := by positivity
  nlinarith [hdens, hpow]

end RicciField

section FluxField

/-! ## `fluxLe` at the carrier the wiring actually builds

`ForwardUniqueAssembly.md`'s ledger names `rmFluxNormSq_le` as the producer of `fluxLe`.  That
was written before the carriers were constructed: `ForwardUniqueWiring.lean` builds the flux as
`sdecUflux = sdecFlux g₁ g₂ Rm₂ P`, which is the K2.4 flux of the background curvature **minus**
a re-lowering defect `reLowerPair g₁ P (lapDiffFlux g₁ g₂ g₂)`.  The subtracted term has no norm
bound anywhere in the tree; the two statements below supply it and assemble the field. -/

/-- A `g`-orthonormal tangent basis at a point.  (Fourth private copy in the lane — see
`ForwardUniqueRatePro.lean`'s note; the campaign-end dedup is to promote one public pair to
`Tensor/RSTensor/Tensor0SRiemannian/`.) -/
private theorem exists_onFrame (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ b : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
        (TangentSpace I x),
      ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : Real) else 0 := by
  classical
  let D := (tangentMetricData_gen (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  refine ⟨ob.toBasis, ?_⟩
  intro i j
  have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
    MetricFiberData.toCore_inner D (ob i) (ob j)
  change g.inner x (ob.toBasis i) (ob.toBasis j) = if i = j then (1 : Real) else 0
  rw [← TangentMetricData_gen.inner_eq_gen
    (tangentMetricData_gen (I := I) g x) (ob.toBasis i) (ob.toBasis j)]
  change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
  rw [← hinner]
  exact ob.inner_eq_ite i j

/-- The identity inverse-metric witness attached to a `g`-orthonormal basis. -/
private theorem onFrame_inv {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0) :
    MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)) := by
  intro i j
  constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]

/-- **Norm bound for the re-lowering defect carrier.**

`|reLowerPair g T K|²_g ≤ n^{s+4} · |T|²_g · |K|²_g`,  `n = finrank ℝ E`.

`reLowerPair` is a metric trace of a slot permutation of the tensor product `T ⊗ K`.  Slot
permutation is a fibre isometry (`normSq0S_domDomCongr`), the tensor product multiplies fibre
norms exactly (`normSq0S_product`), and the trace costs the dimension factor of
`traceNormSq_le`.  No hypothesis beyond the two carriers. -/
theorem reLowerPairSq_le (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (K : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3)
    (x : M) :
    normSq0S (I := I) g x (s + 2) (reLowerPair (I := I) g T K x) ≤
      (Module.finrank Real E : Real) ^ (s + 4) *
        (normSq0S (I := I) g x (s + 1) (T x) * normSq0S (I := I) g x 3 (K x)) := by
  classical
  obtain ⟨basis, hON⟩ := exists_onFrame (I := I) g x
  have hinv := onFrame_inv (I := I) g basis hON
  have hprod : normSq0S (I := I) g x (s + 1 + 3)
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K x) =
      normSq0S (I := I) g x (s + 1) (T x) * normSq0S (I := I) g x 3 (K x) :=
    normSq0S_product (I := I) g x basis hinv T K
  have hcongr : normSq0S (I := I) g x (s + 1 + 3)
      (ContinuousMultilinearMap.domDomCongr (reLowerPerm2 s)
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K x)) =
      normSq0S (I := I) g x (s + 1 + 3)
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K x) :=
    normSq0S_domDomCongr (I := I) g x basis hinv (reLowerPerm2 s) _
  have htr := traceNormSq_le (I := I) (s := s + 2) g x
    (ContinuousMultilinearMap.domDomCongr (reLowerPerm2 s)
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K x))
  rw [hcongr, hprod] at htr
  exact htr

/-- **The `fluxLe` estimate at the constructed carrier.**

The Kotschwar `S`-equation flux `U′ = sdecFlux g₁ g₂ Rm₂ P` obeys

`|U′|²_{g₁} ≤ 32·n⁵·|A₀₃|²_{g₁}·B₂ + 8·n^{10}·|A₀₃|²_{g₁}·B_P·B_g`,

with the three background norms — `B₂ ≥ |Rm₂|²_{g₁}`, `B_P ≥ |P|²_{g₁}` and `B_g ≥ |g₂|²_{g₁}`
— as explicit hypothesis arguments, to be supplied by `normSqSlabBound` on the subslab.  Both
summands carry the connection-difference density `|A₀₃|²_{g₁}` as a factor, which is what makes
the field absorbable into `C_U · density` (`connDiffSq_le_dens`). -/
theorem sdecFluxSq_le (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 P : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) {B₂ BP Bg : Real}
    (hB₂ : normSq0S (I := I) g₁ x 4 (Rm2 x) ≤ B₂)
    (hBP : normSq0S (I := I) g₁ x 4 (P x) ≤ BP)
    (hBg : normSq0S (I := I) g₁ x 2 (metricTensorField (I := I) g₂ x) ≤ Bg) :
    normSq0S (I := I) g₁ x 5 (sdecFlux (I := I) g₁ g₂ Rm2 P x) ≤
      32 * (Module.finrank Real E : Real) ^ 5 * connDiffSq (I := I) g₁ g₂ x * B₂ +
        8 * (Module.finrank Real E : Real) ^ 10 * connDiffSq (I := I) g₁ g₂ x * (BP * Bg) := by
  classical
  have hcd : 0 ≤ connDiffSq (I := I) g₁ g₂ x := by
    rw [connDiffSq_def]; exact normSq0S_nonneg (I := I) g₁ x 3 _
  have hn : (0 : Real) ≤ (Module.finrank Real E : Real) := by positivity
  -- the two summands of `sdecFlux`
  have hsplit : sdecFlux (I := I) g₁ g₂ Rm2 P x =
      lapDiffFlux (I := I) g₁ g₂ Rm2 x -
        reLowerPair (I := I) g₁ P
          (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂)) x := rfl
  rw [hsplit]
  refine (normSq0S_sub_le (I := I) g₁ x 5 _ _).trans ?_
  -- first summand: the K2.4 flux of the background curvature
  have hfirst : normSq0S (I := I) g₁ x 5 (lapDiffFlux (I := I) g₁ g₂ Rm2 x) ≤
      16 * (Module.finrank Real E : Real) ^ 5 * connDiffSq (I := I) g₁ g₂ x * B₂ := by
    refine (fluxNormSq_le (I := I) g₁ g₂ (s := 4) Rm2 x).trans ?_
    have hfac : (0 : Real) ≤ (4 : Real) ^ 2 * (Module.finrank Real E : Real) ^ 5 *
        connDiffSq (I := I) g₁ g₂ x := by positivity
    have h := mul_le_mul_of_nonneg_left hB₂ hfac
    calc (4 : Real) ^ 2 * (Module.finrank Real E : Real) ^ 5 *
            connDiffSq (I := I) g₁ g₂ x * normSq0S (I := I) g₁ x 4 (Rm2 x)
        ≤ (4 : Real) ^ 2 * (Module.finrank Real E : Real) ^ 5 *
            connDiffSq (I := I) g₁ g₂ x * B₂ := h
      _ = _ := by norm_num
  -- the `(0,3)` factor of the defect term
  have hK : normSq0S (I := I) g₁ x 3
      (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂) x) ≤
      4 * (Module.finrank Real E : Real) ^ 3 * connDiffSq (I := I) g₁ g₂ x * Bg := by
    refine (fluxNormSq_le (I := I) g₁ g₂ (s := 2) (metricTensorField (I := I) g₂) x).trans ?_
    have hfac : (0 : Real) ≤ (2 : Real) ^ 2 * (Module.finrank Real E : Real) ^ 3 *
        connDiffSq (I := I) g₁ g₂ x := by positivity
    have h := mul_le_mul_of_nonneg_left hBg hfac
    calc (2 : Real) ^ 2 * (Module.finrank Real E : Real) ^ 3 *
            connDiffSq (I := I) g₁ g₂ x *
            normSq0S (I := I) g₁ x 2 (metricTensorField (I := I) g₂ x)
        ≤ (2 : Real) ^ 2 * (Module.finrank Real E : Real) ^ 3 *
            connDiffSq (I := I) g₁ g₂ x * Bg := h
      _ = _ := by norm_num
  -- second summand: the re-lowering defect
  have hPnn : 0 ≤ normSq0S (I := I) g₁ x 4 (P x) := normSq0S_nonneg (I := I) g₁ x 4 _
  have hKnn : 0 ≤ normSq0S (I := I) g₁ x 3
      (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂) x) :=
    normSq0S_nonneg (I := I) g₁ x 3 _
  have hsecond : normSq0S (I := I) g₁ x 5
      (reLowerPair (I := I) g₁ P
        (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂)) x) ≤
      (Module.finrank Real E : Real) ^ 7 *
        (BP * (4 * (Module.finrank Real E : Real) ^ 3 *
          connDiffSq (I := I) g₁ g₂ x * Bg)) := by
    refine (reLowerPairSq_le (I := I) (s := 3) g₁ P
      (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂)) x).trans ?_
    have hpow : (0 : Real) ≤ (Module.finrank Real E : Real) ^ 7 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hpow
    have h1 : normSq0S (I := I) g₁ x 4 (P x) *
        normSq0S (I := I) g₁ x 3
          (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂) x) ≤
        BP * normSq0S (I := I) g₁ x 3
          (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂) x) :=
      mul_le_mul_of_nonneg_right hBP hKnn
    have hBPnn : 0 ≤ BP := le_trans hPnn hBP
    exact h1.trans (mul_le_mul_of_nonneg_left hK hBPnn)
  have hpow10 : (Module.finrank Real E : Real) ^ 7 * (4 * (Module.finrank Real E : Real) ^ 3) =
      4 * (Module.finrank Real E : Real) ^ 10 := by ring
  nlinarith [hfirst, hsecond, hcd, hpow10]

/-- **The `fluxLe` field of `ForwardUniqueSlab`, with `C_U` exhibited.**

`|U′|²_{g₁} ≤ (32·n⁵·B₂ + 8·n¹⁰·B_P·B_g) · density`.

Both summands of `sdecFluxSq_le` carry the connection-difference density as a factor, so
`connDiffSq_le_dens` absorbs them into the energy density and the three background norms are
all that is left in the constant.  The nonnegativity hypotheses are exactly what
`normSqSlabBound` returns alongside each sup. -/
theorem fluxSlabLe (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Rm2 P : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (t : Real) (x : M) {B₂ BP Bg : Real}
    (hB₂0 : 0 ≤ B₂) (hBP0 : 0 ≤ BP) (hBg0 : 0 ≤ Bg)
    (hB₂ : normSq0S (I := I) (g₁ t) x 4 (Rm2 t x) ≤ B₂)
    (hBP : normSq0S (I := I) (g₁ t) x 4 (P t x) ≤ BP)
    (hBg : normSq0S (I := I) (g₁ t) x 2 (metricTensorField (I := I) (g₂ t) x) ≤ Bg) :
    normSq0S (I := I) (g₁ t) x 5 (sdecFlux (I := I) (g₁ t) (g₂ t) (Rm2 t) (P t) x) ≤
      (32 * (Module.finrank Real E : Real) ^ 5 * B₂ +
          8 * (Module.finrank Real E : Real) ^ 10 * (BP * Bg)) *
        forwardUniqueDensity (I := I) g₁ g₂ t x := by
  have hbr : (0 : Real) ≤ 32 * (Module.finrank Real E : Real) ^ 5 * B₂ +
      8 * (Module.finrank Real E : Real) ^ 10 * (BP * Bg) := by
    have h1 : (0 : Real) ≤ 32 * (Module.finrank Real E : Real) ^ 5 := by positivity
    have h2 : (0 : Real) ≤ 8 * (Module.finrank Real E : Real) ^ 10 := by positivity
    have h3 := mul_nonneg h1 hB₂0
    have h4 := mul_nonneg h2 (mul_nonneg hBP0 hBg0)
    linarith
  refine (sdecFluxSq_le (I := I) (g₁ t) (g₂ t) (Rm2 t) (P t) x hB₂ hBP hBg).trans ?_
  calc 32 * (Module.finrank Real E : Real) ^ 5 * connDiffSq (I := I) (g₁ t) (g₂ t) x * B₂ +
        8 * (Module.finrank Real E : Real) ^ 10 *
          connDiffSq (I := I) (g₁ t) (g₂ t) x * (BP * Bg)
      = (32 * (Module.finrank Real E : Real) ^ 5 * B₂ +
          8 * (Module.finrank Real E : Real) ^ 10 * (BP * Bg)) *
        connDiffSq (I := I) (g₁ t) (g₂ t) x := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (connDiffSq_le_dens (I := I) g₁ g₂ t x) hbr

end FluxField

section BackgroundSups

/-! ## The background-norm sups on the closed subslab

`slabBound` needs joint continuity **up to the closed initial edge** `t = a`, which black box
(B)'s one-sided `Ico a b` chart-Gram field could not feed before the `ContDiffWithinAt` tower
(`Analysis/Parabolic/RicciLinearization/RicciDifferenceMeanValueWithin.lean`) and the
arbitrary-time-set upgrade of `Evolution/ForwardUniqueDensReg.lean`'s brick.  With those, every
background quantity whose chart-frame components are readable from the two chart-Gram packages
produces its constant.  The four below are the ones the remaining fields consume:
the moving metric itself, the background curvature (in any lowering), the Ricci tensors, and
the first covariant derivative of Ricci. -/

variable {a c : Real}

/-- **The background-norm slab sup.**  Composition of the closed-edge joint brick
`normSq0S_jointContMDiffOn` with the extreme value theorem `normSqSlabBound`.  Both hypotheses
are stated on the *closed* subslab, which is what the initial edge costs. -/
theorem normSqSlabSup {s : Nat} (g : Real → SmoothRiemannianMetric I M)
    (A : Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hA : ∀ (x₀ : M) (K : Fin s → Fin (Module.finrank Real E)) {t : Real}, t ∈ Icc a c →
      ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          A p.1 p.2 (fun i : Fin s => chartBasisVecFiber (I := I) x₀ (K i) p.2))
        (Icc a c ×ˢ (univ : Set M)) (t, x₀)) :
    ∃ B : Real, 0 ≤ B ∧
      ∀ t ∈ Icc a c, ∀ x : M, normSq0S (I := I) (g t) x s (A t x) ≤ B :=
  normSqSlabBound (I := I) g A
    ((normSq0S_jointContMDiffOn (I := I) g A hgram hA).continuousOn)

/-- **The sup of the metric-difference density on the closed subslab.** -/
theorem metricDiffSlabSup (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Icc a c, ∀ x : M,
      metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ B := by
  obtain ⟨B, hB0, hB⟩ := slabBound (M := M)
    (fun t x => metricDiffSq (I := I) (g₁ t) (g₂ t) x)
    ((metricDiffSq_jointContMDiffOn (I := I) g₁ g₂ hgram₁ hgram₂).continuousOn)
  exact ⟨B, hB0, fun t ht x => (le_abs_self _).trans (hB t ht x)⟩

/-- **The sup of `|g₂|²_{g₁}` on the closed subslab** — the `B_g` constant of `sdecFluxSq_le`.
The chart-frame components of the `(0,2)` carrier `metricTensorField (g₂ t)` *are* the chart-Gram
entries of `g₂`, so no curvature tower is involved. -/
theorem metricSlabSup (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Icc a c, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 2 (metricTensorField (I := I) (g₂ t) x) ≤ B :=
  normSqSlabSup (I := I) g₁ (fun t x => metricTensorField (I := I) (g₂ t) x) hgram₁
    (fun x₀ K _ ht => metricChartJoint (I := I) g₂ x₀ (hgram₂ x₀) K ht)

/-- **The sup of a background curvature on the closed subslab.**

`|Rm(∇^{gC}) lowered by gL|²_{gN} ≤ B` on `Icc a c ×ˢ univ`, with the three roles — the metric
taking the norm, the metric lowering the last slot, and the metric supplying the connection —
independent.  Two instances carry all the curvature constants of the endgame:

* `(gN, gL, gC) = (g₁, g₂, g₂)` is `B₂ ≥ |Rm₂|²_{g₁}`;
* `(gN, gL, gC) = (g₁, g₁, g₂)` is `B_P ≥ |P|²_{g₁}`, `P` being the cross-lowered curvature
  `Rm₂` that `sdecFlux`'s re-lowering defect carries. -/
theorem rm04SlabSup (gN gL gC : Real → SmoothRiemannianMetric I M)
    (hgramN : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gN p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramL : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gL p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramC : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gC p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Icc a c, ∀ x : M,
      normSq0S (I := I) (gN t) x 4
        (CovariantDerivative.riemannCurvature04At (I := I) (gL t) (metricCov (I := I) (gC t))
          (metricCov_smooth (I := I) (gC t)) x) ≤ B :=
  normSqSlabSup (I := I) gN
    (fun t x => CovariantDerivative.riemannCurvature04At (I := I) (gL t)
      (metricCov (I := I) (gC t)) (metricCov_smooth (I := I) (gC t)) x) hgramN
    (fun x₀ K _ ht => rm04ChartJoint (I := I) gL gC x₀ (hgramL x₀) (hgramC x₀) K ht)

/-- **The Ricci tensor is `n⁴`-controlled by the curvature it traces.**

`|Ric₂|²_{g₁} ≤ n⁴ · |Rm(∇²) lowered by g₁|²_{g₁}`.

`metricRicci_eq_trace_cross` writes `Ric₂` as the `g₁`-trace of a slot permutation of the
cross-lowered curvature, `normSq0S_domDomCongr` says the permutation is a fibre isometry, and
`traceNormSq_le` pays the dimension factor.  Taking `g₂ := g₁` gives `|Ric₁|²_{g₁} ≤
n⁴·|Rm₁|²_{g₁}`, which is `adotLe`'s `Λric` and `reactLe`'s only background norm. -/
theorem ricciSq_le_rm04 (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    normSq0S (I := I) g₁ x 2 (metricRicciAt (I := I) g₂ x) ≤
      (Module.finrank Real E : Real) ^ 4 *
        normSq0S (I := I) g₁ x 4
          (CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
            (metricCov_smooth (I := I) g₂) x) := by
  classical
  obtain ⟨basis, hON⟩ := exists_onFrame (I := I) g₁ x
  have hinv := onFrame_inv (I := I) g₁ basis hON
  have htr := traceNormSq_le (I := I) (s := 2) g₁ x
    (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
      (CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
        (metricCov_smooth (I := I) g₂) x))
  rw [normSq0S_domDomCongr (I := I) g₁ x basis hinv rm04TraceSlots _] at htr
  rw [metricRicci_eq_trace_cross (I := I) g₁ g₂ x]
  exact htr

/-- **The sup of `|Ric₂|²_{g₁}` on the closed subslab.**  `ricciSq_le_rm04` on top of
`rm04SlabSup` at `(gN, gL, gC) = (g₁, g₁, g₂)`.  With `g₂ := g₁` this is `Λric`; as stated it is
`adotLe`'s `B₃`. -/
theorem ricciSlabSup (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Icc a c, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₂ t) x) ≤ B := by
  obtain ⟨B, hB0, hB⟩ := rm04SlabSup (I := I) g₁ g₁ g₂ hgram₁ hgram₁ hgram₂
  have hpow : (0 : Real) ≤ (Module.finrank Real E : Real) ^ 4 := by positivity
  refine ⟨(Module.finrank Real E : Real) ^ 4 * B, mul_nonneg hpow hB0, fun t ht x => ?_⟩
  exact (ricciSq_le_rm04 (I := I) (g₁ t) (g₂ t) x).trans
    (mul_le_mul_of_nonneg_left (hB t ht x) hpow)

/-- **The sup of `|∇^{gC} Ric(gC)|²_{gN}` on the closed subslab.**

The chart-frame regularity input is `nablaRicChartJoint`, so the estimate is
valid at the one-sided initial edge.  Taking `(gN, gC) = (g₁, g₂)` supplies
`connDiffDot_normSq_le`'s `B₁`. -/
theorem nablaRicSlabSup (gN gC : Real → SmoothRiemannianMetric I M)
    (hgramN : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gN p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramC : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gC p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Icc a c, ∀ x : M,
      normSq0S (I := I) (gN t) x 3
        (metricNabla0S (I := I) (gC t)
          (CovariantDerivative.ricciSection (I := I)
            (metricCov (I := I) (gC t)) (metricCov_smooth (I := I) (gC t))) x) ≤ B :=
  normSqSlabSup (I := I) gN
    (fun t x =>
      metricNabla0S (I := I) (gC t)
        (CovariantDerivative.ricciSection (I := I)
          (metricCov (I := I) (gC t)) (metricCov_smooth (I := I) (gC t))) x)
    hgramN
    (fun x₀ K _ ht => nablaRicChartJoint (I := I) gC x₀ (hgramC x₀) K ht)

/-- **The sup of `|∇ᵏRm(gC)|²_{gN}` on the closed subslab.**

The norm metric and curvature metric are independent.  The closed-edge chart
regularity is supplied by `nablaKRmChartJoint`; the compactness step is the
rank-uniform `normSqSlabSup`. -/
theorem nablaKRmSlabSup (gN gC : Real → SmoothRiemannianMetric I M)
    (hgramN : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gN p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramC : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gC p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (k : ℕ) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Icc a c, ∀ x : M,
      normSq0S (I := I) (gN t) x (4 + k)
        (nablaKRm04Field (I := I)
          (solOfMetric (I := I) (D := RealTimeInterval.univ 0) gC) t k x) ≤ B :=
  normSqSlabSup (I := I) gN
    (fun t x =>
      nablaKRm04Field (I := I)
        (solOfMetric (I := I) (D := RealTimeInterval.univ 0) gC) t k x)
    hgramN
    (fun x₀ K _ ht => nablaKRmChartJoint (I := I) gC x₀ (hgramC x₀) k K ht)

/-- **The sup of the first covariant derivative of a cross-lowered curvature.**

The four metric roles are independent: `gN` takes the norm, `gL` lowers the
curvature, `gC` supplies its connection, and `gD` differentiates it. -/
theorem crossRm1SlabSup
    (gN gL gC gD : Real → SmoothRiemannianMetric I M)
    (hgramN : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gN p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramL : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gL p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramC : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gC p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramD : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gD p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Icc a c, ∀ x : M,
      normSq0S (I := I) (gN t) x 5
        (metricNabla0S (I := I) (gD t)
          (CovariantDerivative.rm04Section (I := I) (gL t)
            (metricCov (I := I) (gC t))
            (metricCov_smooth (I := I) (gC t))) x) ≤ B :=
  normSqSlabSup (I := I) gN
    (fun t =>
      metricNabla0S (I := I) (gD t)
        (CovariantDerivative.rm04Section (I := I) (gL t)
          (metricCov (I := I) (gC t))
          (metricCov_smooth (I := I) (gC t))))
    hgramN
    (fun x₀ K _ ht =>
      crossRm1ChartJoint (I := I) gL gC gD x₀
        (hgramL x₀) (hgramC x₀) (hgramD x₀) K ht)

/-- **The sup of the second covariant derivative of a cross-lowered curvature.**

This is the rank-six background bound required by the rough-Laplacian defect
in the forward-uniqueness remainder. -/
theorem crossRm2SlabSup
    (gN gL gC gD : Real → SmoothRiemannianMetric I M)
    (hgramN : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gN p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramL : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gL p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramC : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gC p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramD : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (gD p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Icc a c, ∀ x : M,
      normSq0S (I := I) (gN t) x 6
        (metricNabla0S (I := I) (gD t)
          (metricNabla0S (I := I) (gD t)
            (CovariantDerivative.rm04Section (I := I) (gL t)
              (metricCov (I := I) (gC t))
              (metricCov_smooth (I := I) (gC t)))) x) ≤ B :=
  normSqSlabSup (I := I) gN
    (fun t =>
      metricNabla0S (I := I) (gD t)
        (metricNabla0S (I := I) (gD t)
          (CovariantDerivative.rm04Section (I := I) (gL t)
            (metricCov (I := I) (gC t))
            (metricCov_smooth (I := I) (gC t)))))
    hgramN
    (fun x₀ K _ ht =>
      crossRm2ChartJoint (I := I) gL gC gD x₀
        (hgramL x₀) (hgramC x₀) (hgramD x₀) K ht)

/-- **The pointwise metric comparison `g₁ ≤ Λ·g₂`, from a fibre-norm bound.**

`g₁(v,v) ≤ √(|g₁|²_{g₂}) · g₂(v,v)` for **every** tangent vector — no eigenvalue, no positivity
argument and no unit-sphere-bundle compactness.  The whole content is the ON-frame component
estimate `abs_apply_le_sqrt_normSq0S` at rank `2` with both slots equal to `v`: the two
`√(g₂(v,v))` factors it produces multiply back to `g₂(v,v)`.

This is the `Λ` input of `connDiffDot_normSq_le` (`Evolution/ForwardUniqueConnBound.lean`), and
`metricSlabSup g₂ g₁` supplies the sup of its coefficient on a closed subslab — so `Λ` is a
`normSq0S` sup after all, contrary to the previous note's reading. -/
theorem fu_metric_comp_le (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    g₁.inner x v v ≤
      Real.sqrt (normSq0S (I := I) g₂ x 2 (metricTensorField (I := I) g₁ x)) *
        g₂.inner x v v := by
  classical
  have hvv : (0 : Real) ≤ g₂.inner x v v := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0]; simp
    · exact (g₂.pos x v hv0).le
  obtain ⟨basis, hON⟩ := exists_onFrame (I := I) g₂ x
  have h := abs_apply_le_sqrt_normSq0S (I := I) g₂ x 2 basis hON
    (metricTensorField (I := I) g₁ x) (fun _ : Fin 2 => v)
  have hval : metricTensorField (I := I) g₁ x (fun _ : Fin 2 => v) = g₁.inner x v v :=
    metricTensorField_apply (I := I) g₁ x (fun _ : Fin 2 => v)
  have hprod : (∏ _d : Fin 2, Real.sqrt (g₂.inner x v v)) = g₂.inner x v v := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [sq]
    exact Real.mul_self_sqrt hvv
  rw [hval, hprod] at h
  exact (le_abs_self _).trans h

/-- **The `Λ` of `connDiffDot_normSq_le`, uniform on the closed subslab.**  `fu_metric_comp_le`
on top of `metricSlabSup` with the two metric roles exchanged. -/
theorem metricCompSlab (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ Λ : Real, 0 ≤ Λ ∧ ∀ t ∈ Icc a c, ∀ (x : M) (v : TangentSpace I x),
      (g₁ t).inner x v v ≤ Λ * (g₂ t).inner x v v := by
  obtain ⟨B, hB0, hB⟩ := metricSlabSup (I := I) g₂ g₁ hgram₂ hgram₁
  refine ⟨Real.sqrt B, Real.sqrt_nonneg _, fun t ht x v => ?_⟩
  have hvv : (0 : Real) ≤ (g₂ t).inner x v v := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0]; simp
    · exact ((g₂ t).pos x v hv0).le
  refine (fu_metric_comp_le (I := I) (g₁ t) (g₂ t) x v).trans ?_
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hB t ht x)) hvv

/-- **Two-sided metric equivalence, uniform on a closed subslab.**

The two one-sided constants from `metricCompSlab` are absorbed into one
constant `C ≥ 1`, in the exact form consumed by the tensor norm-comparison
API. -/
theorem metricEquivSlab (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ C : Real, 1 ≤ C ∧ ∀ t ∈ Icc a c, ∀ (x : M) (v : TangentSpace I x),
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v := by
  obtain ⟨Λ₁₂, hΛ₁₂0, hΛ₁₂⟩ := metricCompSlab (I := I) g₁ g₂ hgram₁ hgram₂
  obtain ⟨Λ₂₁, hΛ₂₁0, hΛ₂₁⟩ := metricCompSlab (I := I) g₂ g₁ hgram₂ hgram₁
  let C : Real := 1 + Λ₁₂ + Λ₂₁
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith
  have hΛ₁₂C : Λ₁₂ ≤ C := by
    dsimp [C]
    linarith
  have hΛ₂₁C : Λ₂₁ ≤ C := by
    dsimp [C]
    linarith
  refine ⟨C, hC, fun t ht x v => ?_⟩
  have hv₁ : 0 ≤ (g₁ t).inner x v v := by
    rcases eq_or_ne v 0 with hv | hv
    · rw [hv]
      simp
    · exact ((g₁ t).pos x v hv).le
  have hv₂ : 0 ≤ (g₂ t).inner x v v := by
    rcases eq_or_ne v 0 with hv | hv
    · rw [hv]
      simp
    · exact ((g₂ t).pos x v hv).le
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have h₁₂ : (g₁ t).inner x v v ≤ C * (g₂ t).inner x v v :=
    (hΛ₁₂ t ht x v).trans (mul_le_mul_of_nonneg_right hΛ₁₂C hv₂)
  constructor
  · calc
      C⁻¹ * (g₁ t).inner x v v ≤ C⁻¹ * (C * (g₂ t).inner x v v) :=
        mul_le_mul_of_nonneg_left h₁₂ (inv_nonneg.mpr hCpos.le)
      _ = (g₂ t).inner x v v := by field_simp [hCpos.ne']
  · exact (hΛ₂₁ t ht x v).trans
      (mul_le_mul_of_nonneg_right hΛ₂₁C hv₁)

/-- **The metric trace of a `(0,2)` tensor costs exactly one dimension factor.**

`(tr_g Q)² ≤ n · |Q|²_g`,  `n = finrank ℝ E`.

`metricTracePair0SAt_sq_le_card_mul_normSq0S` is Cauchy–Schwarz against the metric tensor,
whose own fibre norm is the dimension; evaluating it at a `g`-orthonormal frame replaces the
abstract index cardinality by `n`. -/
theorem tracePairSq_le (g : SmoothRiemannianMetric I M) (x : M)
    (Q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    (metricTracePair0SAt (I := I) g Q) ^ 2 ≤
      (Module.finrank Real E : Real) * normSq0S (I := I) g x 2 Q := by
  classical
  obtain ⟨basis, hON⟩ := exists_onFrame (I := I) g x
  simpa using metricTracePair0SAt_sq_le_card_mul_normSq0S (I := I) g basis
    (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x))))
    (onFrame_inv (I := I) g basis hON) Q

/-- **The `volLe` field from the Ricci sup, under the flow identity `∂ₜg = −2Ric`.**

`½·tr_{g₁}(∂ₜg₁) = −tr_{g₁}Ric₁`, and `tracePairSq_le` turns a sup on `|Ric₁|²_{g₁}` into a
two-sided bound on that scalar.  The identity input `htr` is the Ricci-flow equation read
through `traceTimeDerivMetric`; the wiring supplies it from black box (B)'s own PDE field. -/
theorem volSlabSup (g₁ : Real → SmoothRiemannianMetric I M) {B : Real}
    (htr : ∀ t ∈ Ioo a c, ∀ x : M, traceTimeDerivMetric (I := I) g₁ t x =
      (-2 : Real) * metricTracePair0SAt (I := I) (g₁ t) (metricRicciAt (I := I) (g₁ t) x))
    (hric : ∀ t ∈ Ioo a c, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x) ≤ B) :
    ∃ C_V : Real, 0 ≤ C_V ∧ ∀ t ∈ Ioo a c, ∀ x : M,
      (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V := by
  refine ⟨Real.sqrt ((Module.finrank Real E : Real) * B), Real.sqrt_nonneg _,
    fun t ht x => ?_⟩
  set S : Real := metricTracePair0SAt (I := I) (g₁ t) (metricRicciAt (I := I) (g₁ t) x) with hS
  have hsq : S ^ 2 ≤ (Module.finrank Real E : Real) * B := by
    refine (tracePairSq_le (I := I) (g₁ t) x (metricRicciAt (I := I) (g₁ t) x)).trans ?_
    exact mul_le_mul_of_nonneg_left (hric t ht x) (by positivity)
  have habs : |S| ≤ Real.sqrt ((Module.finrank Real E : Real) * B) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  have hneg : -S ≤ Real.sqrt ((Module.finrank Real E : Real) * B) :=
    (neg_le_abs S).trans habs
  rw [htr t ht x]
  linarith

end BackgroundSups

section ReactField

/-! ## `reactLe`: the moving-metric reaction at every rank

`movingReact0S g x s Q W` is *defined* through the canonical basis `Module.finBasis`, so it
carries no norm bound directly.  `normSq0S_moving_deriv` identifies it as the honest derivative
`∂ᵣ|W|²_{g r}` of a **frozen** carrier, which is basis-free; running
`hasDerivWithinAt_normSq0S_ricciFlow` again in a `g t`-*orthonormal* frame and matching the two
derivatives by `HasDerivAt.unique` therefore rewrites it as a component contraction against the
identity inverse metric, where every factor is bounded by an ON-frame component estimate.  This
is the route recorded as owed since plan №25; nothing here imports the rank-2
`movingMetricReact` bound. -/

variable {a c : Real}

/-- **The moving reaction, read in a `g t`-orthonormal frame.**

The frozen-carrier moving norm has two readings of one and the same derivative: the definitional
`movingReact0S` (canonical basis) and `ricReactionContract` in the supplied frame.  Under
`∂ₜg = −2Q` the frame's inverse metric at time `t` is the identity, so the second reading is a
plain component contraction of `Q` against `W ⊗ W`. -/
private theorem reactOrtho {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {s : Nat} {x : M} {t : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (Q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (W : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, (g t).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun d : Fin 2 => if d = 0 then X else Y)) t) :
    movingReact0S (I := I) (g t) x s Q W =
      ricReactionContract (identityInvMetric (Idx := Idx))
        (fun i j => Q (fun d : Fin 2 => if d = 0 then basis i else basis j))
        (fun I0 => tensor0SComponent (I := I) W (fun i => basis i) I0)
        (fun J0 => tensor0SComponent (I := I) W (fun i => basis i) J0) := by
  classical
  have hz : inner0S (I := I) (g t) x s
      (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) W = 0 := by
    simpa using inner0S_smul_left (I := I) (g t) x s (0 : Real) W W
  -- the basis-free reading of the left-hand side
  have hL : HasDerivAt (fun r : Real => normSq0S (I := I) (g r) x s W)
      (movingReact0S (I := I) (g t) x s Q W) t := by
    have hT : ∀ v : Fin s → TangentSpace I x,
        HasDerivAt (fun _ : Real => W v)
          ((0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) v) t := by
      intro v
      rw [Tensor0SSpace.zero_apply (I := I) s x v]
      exact hasDerivAt_const t (W v)
    have h := normSq0S_moving_deriv (I := I) g Q (fun _ => W) 0 hg hT
    rw [hz, mul_zero, add_zero] at h
    exact h
  -- the same derivative, computed in the supplied frame
  set ric : Idx → Idx → Real := fun i j =>
    Q (fun d : Fin 2 => if d = 0 then basis i else basis j) with hricdef
  set gI : Real → Idx → Idx → Real := fun r => basisInvMetric (I := I) (g r) x basis with hgIdef
  set gIDt : Idx → Idx → Real := fun i j =>
    -(∑ p : Idx, ∑ q : Idx, gI t i p * ((-2 : Real) * ric p q) * gI t q j) with hgIDtdef
  have hinvAll : ∀ r : Real, MetricInverseInBasis (I := I) (g r) x basis (gI r) := by
    intro r
    simpa [gI] using basisInvMetric_real (I := I) (g r) x basis
  have hgI : ∀ i j : Idx,
      HasDerivWithinAt (fun r : Real => gI r i j) (gIDt i j) Set.univ t := by
    intro i j
    simpa [gI, gIDt, ric] using
      (basisInv_time (I := I) g (fun p q => (-2 : Real) * ric p q) basis
        (fun p q => by simpa [ric] using hg (basis p) (basis q)) i j)
  have hflow : ∀ i j : Idx,
      gIDt i j = 2 * (∑ p : Idx, ∑ q : Idx, gI t i p * gI t j q * ric p q) := by
    intro i j
    have hterm : (∑ p : Idx, ∑ q : Idx, gI t i p * ((-2 : Real) * ric p q) * gI t q j) =
        ∑ p : Idx, ∑ q : Idx, (-2 : Real) * (gI t i p * gI t j q * ric p q) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [gI]
      rw [basisInvMetric_symm (I := I) (g t) x basis q j]
      ring
    have hfactor : (∑ p : Idx, ∑ q : Idx, (-2 : Real) * (gI t i p * gI t j q * ric p q)) =
        (-2 : Real) * (∑ p : Idx, ∑ q : Idx, gI t i p * gI t j q * ric p q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
    simp only [gIDt]
    rw [hterm, hfactor]
    ring
  have hTcomp : ∀ I0 : Fin s → Idx,
      HasDerivWithinAt
        (fun r : Real => tensor0SComponent (I := I) ((fun _ : Real => W) r)
          (fun i => basis i) I0) ((fun _ : Fin s → Idx => (0 : Real)) I0) Set.univ t :=
    fun I0 => hasDerivWithinAt_const _ _ _
  have hTdot : ∀ I0 : Fin s → Idx,
      tensor0SComponent (I := I)
          (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
          (fun i => basis i) I0 = (0 : Real) :=
    fun I0 => Tensor0SSpace.zero_apply (I := I) s x _
  have hR := hasDerivWithinAt_normSq0S_ricciFlow (I := I) (s := s) (u := Set.univ) (t := t)
    g gI gIDt ric (fun _ : Real => W) (fun _ : Fin s → Idx => (0 : Real)) 0 basis
    hinvAll hgI hTcomp hTdot hflow
  rw [hz, mul_zero, add_zero] at hR
  -- at `t` the frame's inverse metric is the identity
  have hid : gI t = identityInvMetric (Idx := Idx) := by
    funext i j
    have h := (hinvAll t i j).1
    simp only [hON, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h
    simpa [identityInvMetric, diagonalInvMetric] using h
  rw [hid] at hR
  exact hL.unique (hR.hasDerivAt (by simp))

/-- **The array bound for the Ricci reaction at the identity inverse metric.**

Every factor of `ricReactionContract` is bounded on the nose in an orthonormal frame: the
Kronecker entries by `1`, the reaction components by `Bq`, and the carrier components by `N`.
The constant is deliberately crude — the field it feeds only needs *a* slab constant. -/
private theorem ricReactAbs_le {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {s : Nat}
    (ric : Idx → Idx → Real) (cc : (Fin s → Idx) → Real) {Bq N : Real}
    (hBq0 : 0 ≤ Bq) (hN0 : 0 ≤ N)
    (hBq : ∀ i j, |ric i j| ≤ Bq) (hc : ∀ I0, |cc I0| ≤ N) :
    |ricReactionContract (identityInvMetric (Idx := Idx)) ric cc cc| ≤
      2 * ((Fintype.card (Fin s → Idx) : Real) ^ 2 *
        ((s : Real) * (Fintype.card Idx : Real) ^ 2 * Bq * N ^ 2)) := by
  classical
  have hδ : ∀ i j : Idx, |identityInvMetric (Idx := Idx) i j| ≤ 1 := by
    intro i j
    by_cases h : i = j
    · subst h; simp [identityInvMetric]
    · simp [identityInvMetric, diagonalInvMetric, h]
  have hδ0 : ∀ i j : Idx, (0 : Real) ≤ |identityInvMetric (Idx := Idx) i j| := fun i j =>
    abs_nonneg _
  -- the doubly-contracted reaction entry
  have hinner : ∀ i j : Idx,
      |∑ p : Idx, ∑ q : Idx, identityInvMetric (Idx := Idx) i p *
        identityInvMetric (Idx := Idx) j q * ric p q| ≤
        (Fintype.card Idx : Real) ^ 2 * Bq := by
    intro i j
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hrow : ∀ p : Idx, |∑ q : Idx, identityInvMetric (Idx := Idx) i p *
        identityInvMetric (Idx := Idx) j q * ric p q| ≤ (Fintype.card Idx : Real) * Bq := by
      intro p
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ q : Idx, |identityInvMetric (Idx := Idx) i p *
          identityInvMetric (Idx := Idx) j q * ric p q| ≤ Bq := by
        intro q
        rw [abs_mul, abs_mul]
        calc |identityInvMetric (Idx := Idx) i p| * |identityInvMetric (Idx := Idx) j q| *
              |ric p q|
            ≤ 1 * 1 * Bq := by
              refine mul_le_mul (mul_le_mul (hδ i p) (hδ j q) (hδ0 j q) zero_le_one)
                (hBq p q) (abs_nonneg _) (by norm_num)
          _ = Bq := by ring
      refine (Finset.sum_le_sum fun q _ => hterm q).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    refine (Finset.sum_le_sum fun p _ => hrow p).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [sq]
    ring_nf
    exact le_refl _
  -- the slot sum
  have hslot : ∀ I0 J0 : Fin s → Idx,
      |∑ b : Fin s, (∏ α ∈ (Finset.univ : Finset (Fin s)).erase b,
          identityInvMetric (Idx := Idx) (I0 α) (J0 α)) *
        (∑ p : Idx, ∑ q : Idx, identityInvMetric (Idx := Idx) (I0 b) p *
          identityInvMetric (Idx := Idx) (J0 b) q * ric p q)| ≤
        (s : Real) * ((Fintype.card Idx : Real) ^ 2 * Bq) := by
    intro I0 J0
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ b : Fin s,
        |(∏ α ∈ (Finset.univ : Finset (Fin s)).erase b,
            identityInvMetric (Idx := Idx) (I0 α) (J0 α)) *
          (∑ p : Idx, ∑ q : Idx, identityInvMetric (Idx := Idx) (I0 b) p *
            identityInvMetric (Idx := Idx) (J0 b) q * ric p q)| ≤
          (Fintype.card Idx : Real) ^ 2 * Bq := by
      intro b
      rw [abs_mul]
      have hprod : |∏ α ∈ (Finset.univ : Finset (Fin s)).erase b,
          identityInvMetric (Idx := Idx) (I0 α) (J0 α)| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one (fun α _ => hδ0 _ _) (fun α _ => hδ _ _)
      calc |∏ α ∈ (Finset.univ : Finset (Fin s)).erase b,
              identityInvMetric (Idx := Idx) (I0 α) (J0 α)| *
            |∑ p : Idx, ∑ q : Idx, identityInvMetric (Idx := Idx) (I0 b) p *
              identityInvMetric (Idx := Idx) (J0 b) q * ric p q|
          ≤ 1 * ((Fintype.card Idx : Real) ^ 2 * Bq) := by
            refine mul_le_mul hprod (hinner _ _) (abs_nonneg _) zero_le_one
        _ = (Fintype.card Idx : Real) ^ 2 * Bq := by ring
    refine (Finset.sum_le_sum fun b _ => hterm b).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- assemble
  unfold ricReactionContract
  rw [abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have houter : ∀ I0 : Fin s → Idx,
      |∑ J0 : Fin s → Idx,
        (∑ b : Fin s, (∏ α ∈ (Finset.univ : Finset (Fin s)).erase b,
            identityInvMetric (Idx := Idx) (I0 α) (J0 α)) *
          (∑ p : Idx, ∑ q : Idx, identityInvMetric (Idx := Idx) (I0 b) p *
            identityInvMetric (Idx := Idx) (J0 b) q * ric p q)) * cc I0 * cc J0| ≤
        (Fintype.card (Fin s → Idx) : Real) *
          ((s : Real) * (Fintype.card Idx : Real) ^ 2 * Bq * N ^ 2) := by
    intro I0
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ J0 : Fin s → Idx,
        |(∑ b : Fin s, (∏ α ∈ (Finset.univ : Finset (Fin s)).erase b,
            identityInvMetric (Idx := Idx) (I0 α) (J0 α)) *
          (∑ p : Idx, ∑ q : Idx, identityInvMetric (Idx := Idx) (I0 b) p *
            identityInvMetric (Idx := Idx) (J0 b) q * ric p q)) * cc I0 * cc J0| ≤
          (s : Real) * (Fintype.card Idx : Real) ^ 2 * Bq * N ^ 2 := by
      intro J0
      rw [abs_mul, abs_mul]
      calc |∑ b : Fin s, (∏ α ∈ (Finset.univ : Finset (Fin s)).erase b,
              identityInvMetric (Idx := Idx) (I0 α) (J0 α)) *
            (∑ p : Idx, ∑ q : Idx, identityInvMetric (Idx := Idx) (I0 b) p *
              identityInvMetric (Idx := Idx) (J0 b) q * ric p q)| * |cc I0| * |cc J0|
          ≤ ((s : Real) * ((Fintype.card Idx : Real) ^ 2 * Bq)) * N * N := by
            refine mul_le_mul (mul_le_mul (hslot I0 J0) (hc I0) (abs_nonneg _) ?_)
              (hc J0) (abs_nonneg _) ?_
            · positivity
            · positivity
        _ = (s : Real) * (Fintype.card Idx : Real) ^ 2 * Bq * N ^ 2 := by ring
    refine (Finset.sum_le_sum fun J0 _ => hterm J0).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine (Finset.sum_le_sum fun I0 _ => houter I0).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [sq]
  ring_nf
  exact le_refl _

/-- **The rank-uniform bound on the moving-metric reaction** — the `reactLe` micro-estimate
owed since plan №25.

`|movingReact0S (g t) x s Q W| ≤ 2·s·n^{2s+2}·√(|Q|²_{g t})·|W|²_{g t}`,  `n = finrank ℝ E`.

The only hypothesis is the metric variation `∂ₜg = −2Q` at `t`, which is what makes the
frame-pinned definition readable in a `g t`-orthonormal frame.  No operator bound on `Q` is
required: the ON-frame components of `Q` are already controlled by its fibre norm. -/
theorem movingReactAbs_le {s : Nat} {x : M} {t : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (Q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (W : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun d : Fin 2 => if d = 0 then X else Y)) t) :
    |movingReact0S (I := I) (g t) x s Q W| ≤
      2 * (s : Real) * (Module.finrank Real E : Real) ^ (2 * s + 2) *
        Real.sqrt (normSq0S (I := I) (g t) x 2 Q) * normSq0S (I := I) (g t) x s W := by
  classical
  obtain ⟨basis, hON⟩ := exists_onFrame (I := I) (g t) x
  have hinv := onFrame_inv (I := I) (g t) basis hON
  set NQ : Real := Real.sqrt (normSq0S (I := I) (g t) x 2 Q) with hNQ
  set NW : Real := Real.sqrt (normSq0S (I := I) (g t) x s W) with hNW
  have hNQ0 : 0 ≤ NQ := Real.sqrt_nonneg _
  have hNW0 : 0 ≤ NW := Real.sqrt_nonneg _
  have hQc : ∀ i j : Fin (Module.finrank Real (TangentSpace I x)),
      |Q (fun d : Fin 2 => if d = 0 then basis i else basis j)| ≤ NQ := by
    intro i j
    have h := abs_apply_le_sqrt_normSq0S (I := I) (g t) x 2 basis hON Q
      (fun d : Fin 2 => if d = 0 then basis i else basis j)
    have hprod : (∏ d : Fin 2, Real.sqrt ((g t).inner x
        (if d = 0 then basis i else basis j) (if d = 0 then basis i else basis j))) = 1 := by
      refine Finset.prod_eq_one fun d _ => ?_
      by_cases hd : d = 0
      · simp [hd, hON i i]
      · simp [hd, hON j j]
    rw [hprod, mul_one] at h
    exact h
  have hWc : ∀ I0 : Fin s → Fin (Module.finrank Real (TangentSpace I x)),
      |tensor0SComponent (I := I) W (fun i => basis i) I0| ≤ NW := by
    intro I0
    have h := abs_apply_le_sqrt_normSq0S (I := I) (g t) x s basis hON W
      (fun d : Fin s => basis (I0 d))
    have hprod : (∏ d : Fin s, Real.sqrt ((g t).inner x (basis (I0 d)) (basis (I0 d)))) = 1 := by
      refine Finset.prod_eq_one fun d _ => ?_
      simp [hON (I0 d) (I0 d)]
    rw [hprod, mul_one] at h
    simpa [tensor0SComponent] using h
  rw [reactOrtho (I := I) g Q W basis hON hg]
  refine (ricReactAbs_le (Idx := Fin (Module.finrank Real (TangentSpace I x)))
    (s := s) _ _ hNQ0 hNW0 hQc hWc).trans (le_of_eq ?_)
  have hcard : (Fintype.card (Fin s → Fin (Module.finrank Real (TangentSpace I x))) : Real)
      = (Module.finrank Real E : Real) ^ s := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  have hcard1 : (Fintype.card (Fin (Module.finrank Real (TangentSpace I x))) : Real)
      = (Module.finrank Real E : Real) := by
    rw [Fintype.card_fin]
    rfl
  have hNW2 : NW ^ 2 = normSq0S (I := I) (g t) x s W :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) (g t) x s W)
  rw [hcard, hcard1, hNW2, show 2 * s + 2 = s * 2 + 2 from by ring, pow_add, pow_mul]
  ring

/-- **The `reactLe` field of `ForwardUniqueSlab` from the Ricci sup.**

The three moving-metric reactions of the energy's three carriers are each controlled by
`movingReactAbs_le` at ranks `2`, `3`, `4`; each carrier's fibre norm is a third of the density,
so the whole reaction is `C_R · density` with

`C_R = (4n⁶ + 6n⁸ + 8n¹⁰)·√Λric`,  `Λric ≥ |Ric₁|²_{g₁}` on the subslab. -/
theorem reactSlabLe (g₁ g₂ : Real → SmoothRiemannianMetric I M) {Λric : Real}
    (hpde : ∀ t ∈ Ioo a c, ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun d : Fin 2 => if d = 0 then X else Y)) t)
    (hric : ∀ t ∈ Ioo a c, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x) ≤ Λric) :
    ∃ C_R : Real, 0 ≤ C_R ∧ ∀ t ∈ Ioo a c, ∀ x : M,
      movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
          (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
          (connDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
      C_R * forwardUniqueDensity (I := I) g₁ g₂ t x := by
  refine ⟨(4 * (Module.finrank Real E : Real) ^ 6 + 6 * (Module.finrank Real E : Real) ^ 8 +
      8 * (Module.finrank Real E : Real) ^ 10) * Real.sqrt Λric, by positivity,
    fun t ht x => ?_⟩
  have hSΛ0 : (0 : Real) ≤ Real.sqrt Λric := Real.sqrt_nonneg _
  have hS : Real.sqrt (normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)) ≤
      Real.sqrt Λric := Real.sqrt_le_sqrt (hric t ht x)
  -- one rank at a time
  have hstep : ∀ (s : Nat)
      (W : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x),
      normSq0S (I := I) (g₁ t) x s W ≤ forwardUniqueDensity (I := I) g₁ g₂ t x →
      movingReact0S (I := I) (g₁ t) x s (metricRicciAt (I := I) (g₁ t) x) W ≤
        2 * (s : Real) * (Module.finrank Real E : Real) ^ (2 * s + 2) * Real.sqrt Λric *
          forwardUniqueDensity (I := I) g₁ g₂ t x := by
    intro s W hW
    have hcoef : (0 : Real) ≤
        2 * (s : Real) * (Module.finrank Real E : Real) ^ (2 * s + 2) := by positivity
    have hprod : Real.sqrt (normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)) *
        normSq0S (I := I) (g₁ t) x s W ≤
        Real.sqrt Λric * forwardUniqueDensity (I := I) g₁ g₂ t x :=
      mul_le_mul hS hW (normSq0S_nonneg (I := I) (g₁ t) x s W) hSΛ0
    refine le_trans (le_abs_self _)
      ((movingReactAbs_le (I := I) g₁ (metricRicciAt (I := I) (g₁ t) x) W (hpde t ht x)).trans ?_)
    exact le_trans (le_of_eq (by ring))
      (le_trans (mul_le_mul_of_nonneg_left hprod hcoef) (le_of_eq (by ring)))
  have h2 := hstep 2 (metricDiffAt (I := I) (g₁ t) (g₂ t) x)
    (by simpa [metricDiffSq_def] using metricDiffSq_le_dens (I := I) g₁ g₂ t x)
  have h3 := hstep 3 (connDiffLowAt (I := I) (g₁ t) (g₂ t) x)
    (by simpa [connDiffSq_def] using connDiffSq_le_dens (I := I) g₁ g₂ t x)
  have h4 := hstep 4 (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)
    (by simpa [rmDiffSq_def] using rmDiffSq_le_dens (I := I) g₁ g₂ t x)
  norm_num at h2 h3 h4
  linarith

end ReactField

section EdgeContinuity

/-! ## The closed initial edge of the energy

`ForwardUniqueWiring.lean` leaves, next to `hbounds`, one further residual hypothesis:
`hedge : ContinuousWithinAt (forwardUniqueEnergy g₁ g₂) (Ico a b) a` — continuity of the
Kotschwar energy at the *single* closed initial time.  `fuEnergyCont` supplies the interior of
`Ico a b` from the exact first variation, which needs an open time window and therefore cannot
see `t = a`.

The edge is a **moving-measure** statement: both the density and the volume measure move with
`t`.  `integral_family_cont` (`Analysis/Integration/Measure/FamilyContinuity.lean`) is exactly
the required dominated-convergence layer — on a compact time set, entrywise joint continuity of
the metric family plus joint continuity of the integrand give continuity of
`t ↦ ∫ f t dμ_{g t}` — and its hypotheses are purely `C⁰` on an *arbitrary compact* time set,
so the closed edge is admissible.  The integrand input is `dens_jointContMDiffOn` at
`J := Icc a c`, which is available since the closed-edge upgrade of
`Evolution/ForwardUniqueDensReg.lean`. -/

/-- **The `hedge` residual of `forward_unique_of_gram`, discharged.**

`ContinuousWithinAt (forwardUniqueEnergy g₁ g₂) (Ico a b) a` from black box (B)'s own
chart-Gram fields alone.  No estimate, no PDE and no initial condition enter: the energy is
continuous up to the closed initial edge purely by joint regularity of the density and of the
moving volume on the compact subslab `Icc a (a+b)/2`. -/
theorem energyEdgeCont (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContinuousWithinAt (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (Ico a b) a := by
  set c : Real := (a + b) / 2 with hcdef
  have hac : a < c := by rw [hcdef]; linarith
  have hcb : c < b := by rw [hcdef]; linarith
  have hsub : Icc a c ⊆ Ico a b := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hcb⟩
  have hres₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (hgram₁ x₀ i j).mono (Set.prod_mono hsub (Set.Subset.refl _))
  have hres₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (hgram₂ x₀ i j).mono (Set.prod_mono hsub (Set.Subset.refl _))
  have hdens : ContinuousOn
      (fun p : Real × M => forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (Icc a c ×ˢ (univ : Set M)) :=
    (dens_jointContMDiffOn (I := I) g₁ g₂ hres₁ hres₂).continuousOn
  have hE : ContinuousOn
      (fun t : Real => ∫ x, forwardUniqueDensity (I := I) g₁ g₂ t x
        ∂(riemannianMeasureFamily (I := I) (M := M) g₁ t)) (Icc a c) :=
    integral_family_cont (I := I) isCompact_Icc
      (fun x₀ i j => (hres₁ x₀ i j).continuousOn) hdens
  have hmem : Icc a c ∈ 𝓝[Ico a b] a := by
    refine Filter.mem_of_superset
      (inter_mem_nhdsWithin (Ico a b) (isOpen_Iio.mem_nhds hac)) ?_
    rintro p ⟨hp1, hp2⟩
    exact ⟨hp1.1, le_of_lt hp2⟩
  exact (hE a ⟨le_refl a, hac.le⟩).mono_of_mem_nhdsWithin hmem

end EdgeContinuity

end DifferentialGeometry.PDE.RicciFlow

end
