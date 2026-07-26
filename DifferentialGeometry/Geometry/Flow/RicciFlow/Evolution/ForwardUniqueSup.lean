import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRatePro
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueSdec

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
* `volSlabLe` — the **`volLe` field**, from continuity of the volume drift on the closed
  subslab.
* `reLowerPairSq_le` — the missing norm bound for the re-lowering defect carrier
  `reLowerPair`: `|tr_g(σ(T ⊗ K))|²_g ≤ n^{s+4}·|T|²_g·|K|²_g`.
* `sdecFluxSq_le` — the **`fluxLe` estimate at the carrier the wiring actually builds**
  (`sdecUflux`, not `rmDiffFlux`): `|U′|²_{g₁} ≤ C(n)·|A₀₃|²_{g₁}·(background)`.
* `fluxSlabLe` — the same, absorbed into the energy density: the **`fluxLe` field** with
  `C_U = 32·n⁵·B₂ + 8·n¹⁰·B_P·B_g` exhibited in terms of three background norms.

## What is *not* here

`remLe`, `reactLe` and `adotLe` are not produced; see `ForwardUniqueSup.md` for the
field-by-field ledger and the exact obstruction of each.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.Measure

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

section VolumeField

/-! ## `volLe` from compactness

The volume drift `½ tr_{g₁}(∂ₜg₁)` is a background quantity: it does not involve the second
flow at all.  Under the Ricci-flow equation it equals `−scal_{g₁}`, so it is continuous
wherever the flow is, and the field is the extreme value theorem. -/

variable {a c : Real}

/-- **The `volLe` field of `ForwardUniqueSlab` from continuity of the volume drift.**

This is the route recorded in `ForwardUniqueAssembly.md`'s ledger ("`volLe` ← compactness of
`Icc a c` applied to `traceTimeDerivMetric`").  The hypothesis is a *regularity* statement —
joint continuity of the drift up to the closed initial edge — not a disguised copy of the
conclusion. -/
theorem volSlabLe (g₁ : Real → SmoothRiemannianMetric I M)
    (hdrift : ContinuousOn
      (fun p : Real × M => traceTimeDerivMetric (I := I) g₁ p.1 p.2)
      (Icc a c ×ˢ (univ : Set M))) :
    ∃ C_V : Real, 0 ≤ C_V ∧ ∀ t ∈ Ioo a c, ∀ x : M,
      (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V := by
  obtain ⟨C, hC0, hC⟩ :=
    slabBound (M := M) (fun t x => traceTimeDerivMetric (I := I) g₁ t x) hdrift
  refine ⟨C, hC0, fun t ht x => ?_⟩
  have h := (le_abs_self _).trans (hC t (Ioo_subset_Icc_self ht) x)
  linarith

end VolumeField

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

end DifferentialGeometry.PDE.RicciFlow

end
