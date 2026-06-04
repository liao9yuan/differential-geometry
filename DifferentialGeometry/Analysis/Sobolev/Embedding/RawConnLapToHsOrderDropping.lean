import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapChartComponentSecondCovDerivFormula
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity
import DifferentialGeometry.Tensor.Multilinear.HsBoundOp
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNormReverseOrderZero
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.TensorSectionL2BoundByComponents
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorChartComponentSobolevBound

/-! # Order-dropping completion-norm bounds for the rough tensor connection Laplacian

This file ships the intrinsic chart-Sobolev (`SmoothCcTensor.toHs`) boundedness of the rough
tensor connection Laplacian `Δ_∇ = rawTensorConnLapSmooth`, in the **easy** (differentiation)
direction needed by the order-`a` chart-RHS spectral tower.

The rough Laplacian is the frame trace of the second covariant derivative
(`rawTensorConnLap_eq_frame_trace_secondCovDeriv`), hence a *single* second-order operator: it
maps `H^{2(k+1)} → H^{2k}` boundedly, losing exactly **one** `toHs`-order (`= 2` derivatives),
not two.  This is the elliptic-boundedness primitive `exists_rawConnLapSmooth_toHs_le_toHs_succ`
(the order-`k` analogue of the on-disk `L²`/`H¹` instance
`rawTensorConnLapIter_intrinsicL2_le_tensorPouSobolevNorm_sq_one`, which is the `k = 0` case in
`∫⁻`-form): the tight single-step `H^σ(Δ_∇ T) ≤ C · H^{σ+1}(T)` bound, with no curvature
commutator / Gårding regularity (no `Order2GardingFamily`, no `CommutatorDefectBound`).  It is the
rough-Laplacian counterpart of the covariant-derivative order-dropping bound `covGrad_toHs_norm_le`
— but tight at `+1` `toHs`-order, since `Δ_∇` is a single second-order operator whereas a naive
`covGrad ∘ covGrad` composition would charge `+2`.

The `ℝ≥0∞` form `exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le`, and on top of it the
completion-norm forms `exists_rawConnLapSmooth_toHs_le_toHs_succ` and the iterated bound
`exists_rawConnLapIter_toHs_le_toHs` (`H^k(Δ_∇^i T) ≤ C · H^{k+i}(T)`, the mirror of
`iteratedCovGrad_toHs_norm_le`), are proved by assembling the per-chart order-drop
`exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le_perChart` over the chart base points.  The
per-chart order-drop is itself assembled — Tonelli for finite sums plus a monotone `lintegral` of a
pointwise integrand bound — from the pointwise second-order rough-Laplacian chart-component
operator-norm primitive `exists_rawConnLapComp_iteratedFDeriv_norm_sq_le_rawConnLapRhsHsContent`,
which is proved here (Leibniz on each chart block + compact-kernel coefficient sup-bounds + finite
active-set assembly) on top of the open-good-set `T₀`-linear chart-coordinate formula
`rawTensorConnLap_chartα_raw_eq_T₀_linear_formula_on_goodSet` — the single remaining `sorry` of this
chart-port: the open-good-set strengthening (dropping the inessential partition-of-unity-tsupport
restriction) of the on-disk `rawTensorConnLap_chartα_raw_eq_T₀_linear_formula`, true because the
connection Laplacian is the metric trace of the second covariant derivative at every good-set point.

The companion primitive `exists_l2Norm_le_toHs_zero` records the reverse of the on-disk
`tensorPouSobolevHsNorm_zero_le_tensorL2Norm`: the global metric `L²` norm of a smooth
compactly-supported section is controlled by its order-`0` partition-of-unity chart-Sobolev
norm (the partition of unity sums to one, so the chart-`H⁰` norm recovers the full `L²` norm up
to the bounded metric-density factor on the compact manifold).  It is proved sorry-free, by
composing the on-disk reverse fibre-norm component bound
`tensorL2Norm_sq_le_const_mul_sum_componentL2Norm_sq` with the reverse measure-bridge comparison
`exists_sum_componentL2Norm_sq_le_tensorPouSobolevHsNormSq_zero` (itself proved here from the
reverse change-of-variables bridge `eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw`). -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

section RawConnLapOrderDrop

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

/-- The Euclidean pull-back of a raw `(r, s)`-component of `T` to the chart target: the leaf's
chart-pulled integrand factor `raw_{IJ} ∘ chart⁻¹ ∘ toEuclidean⁻¹`. -/
private noncomputable def rawConnLapPull (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
    ∘ (extChartAt I α).symm
    ∘ (toEuclidean (E := E)).symm

/-- `rawConnLapPull` is definitionally the chart-pulled raw component. -/
private lemma rawConnLapPull_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) =
      rawConnLapPull (I := I) (M := M) g r s T α Idx Jdx := rfl

/-- `rawConnLapPull` is `C^∞` on the (open) Euclidean chart target. -/
private lemma rawConnLapPull_contDiffOn (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (rawConnLapPull (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  refine (chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M)
    g r s T α Idx Jdx).congr (fun y hy => ?_)
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  rfl

/-- `rawConnLapPull` is `C^∞` at every point of the (open) Euclidean chart target. -/
private lemma rawConnLapPull_contDiffAt (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ (rawConnLapPull (I := I) (M := M) g r s T α Idx Jdx) y :=
  (rawConnLapPull_contDiffOn (I := I) (M := M) g r s T α Idx Jdx).contDiffAt
    ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy)

/-- The order-`(k + 1)` Hilbert-Schmidt content of `T` at chart `α`, at a fixed target point `y`:
the finite sum over component multi-index pairs `q`, over Fréchet orders `l ≤ 2(k + 1)`, and over
basis-index tuples, of the squared basis-evaluation of `D^l (rawConnLapPull q)`. -/
private noncomputable def rawConnLapRhsHsContent (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M) (y : EuclN) : ℝ :=
  ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
    ∑ l ∈ Finset.range (2 * (k + 1) + 1),
      ∑ bIdx : Fin l → Fin (Module.finrank ℝ E),
        |(iteratedFDeriv ℝ l (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y)
            (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2

/-- `rawConnLapRhsHsContent` is non-negative. -/
private lemma rawConnLapRhsHsContent_nonneg (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M) (y : EuclN) :
    0 ≤ rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- A single iterated-derivative operator-norm squared of a raw component of `T`, at order
`l ≤ 2(k + 1)`, is dominated by the full order-`(k + 1)` Hilbert-Schmidt content. -/
private lemma rawConnLapPull_iteratedFDeriv_norm_sq_le_rhsContent
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (l : ℕ) (hl : l ≤ 2 * (k + 1)) (y : EuclN) :
    ‖iteratedFDeriv ℝ l (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖ ^ 2 ≤
      rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y := by
  classical
  set basisSum : ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) → ℕ → ℝ :=
    fun q' l' => ∑ bIdx : Fin l' → Fin (Module.finrank ℝ E),
      |(iteratedFDeriv ℝ l' (rawConnLapPull (I := I) (M := M) g r s T α q'.1 q'.2) y)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2 with hbasisSum_def
  have hbasisSum_nn : ∀ q' l', 0 ≤ basisSum q' l' :=
    fun q' l' => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_op : ‖iteratedFDeriv ℝ l (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖ ^ 2 ≤
      basisSum q l :=
    ContinuousMultilinearMap.opNorm_sq_le_sum_sq_basisEval
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ)
      (iteratedFDeriv ℝ l (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y)
  refine le_trans h_op ?_
  have h_unfold : rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y =
      ∑ q' : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        ∑ l' ∈ Finset.range (2 * (k + 1) + 1), basisSum q' l' := rfl
  rw [h_unfold]
  have hl_mem : l ∈ Finset.range (2 * (k + 1) + 1) := Finset.mem_range.mpr (by omega)
  have h_inner : basisSum q l ≤ ∑ l' ∈ Finset.range (2 * (k + 1) + 1), basisSum q l' :=
    Finset.single_le_sum (f := fun l' => basisSum q l')
      (fun l' _ => hbasisSum_nn q l') hl_mem
  refine le_trans h_inner ?_
  exact Finset.single_le_sum
    (f := fun q' => ∑ l' ∈ Finset.range (2 * (k + 1) + 1), basisSum q' l')
    (fun q' _ => Finset.sum_nonneg (fun l' _ => hbasisSum_nn q' l'))
    (Finset.mem_univ q)

/-- `euclidPartial l u` is, as a function, the direction-`l` evaluation of the Fréchet derivative
of `u`. -/
private lemma euclidPartial_eq_fderiv_apply (l : Fin (Module.finrank ℝ E)) (u : EuclN → ℝ) :
    euclidPartial (E := E) l u = fun z => fderiv ℝ u z (EuclideanSpace.single l 1) := rfl

/-- If `u` is `C^∞` at `y`, then so is `euclidPartial l u`. -/
private lemma euclidPartial_contDiffAt
    (l : Fin (Module.finrank ℝ E)) {u : EuclN → ℝ} {y : EuclN}
    (hu : ContDiffAt ℝ ∞ u y) :
    ContDiffAt ℝ ∞ (euclidPartial (E := E) l u) y := by
  have h_fderiv_cdAt : ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun z => fderiv ℝ u z) y := by
    have hle : (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) from rfl]
    simpa using hu.fderiv_right (m := (∞ : WithTop ℕ∞)) hle
  rw [euclidPartial_eq_fderiv_apply (E := E) l u]
  exact (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.single l (1 : ℝ))).contDiff.contDiffAt.comp y h_fderiv_cdAt

/-- One `euclidPartial` costs exactly one Fréchet order in operator norm: if `u` is `C^∞` at `y`,
then `‖D^m (euclidPartial l u) y‖ ≤ ‖D^{m + 1} u y‖`. -/
private lemma euclidPartial_iteratedFDeriv_norm_le
    (l : Fin (Module.finrank ℝ E)) {u : EuclN → ℝ} {y : EuclN}
    (hu : ContDiffAt ℝ ∞ u y) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (euclidPartial (E := E) l u) y‖ ≤
      ‖iteratedFDeriv ℝ (m + 1) u y‖ := by
  have h_fderiv_cdAt : ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun z => fderiv ℝ u z) y := by
    have hle : (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) from rfl]
    simpa using hu.fderiv_right (m := (∞ : WithTop ℕ∞)) hle
  rw [euclidPartial_eq_fderiv_apply (E := E) l u]
  have h_clm := norm_iteratedFDeriv_clm_apply_const
    (𝕜 := ℝ) (f := fun z => fderiv ℝ u z) (c := EuclideanSpace.single l 1)
    (x := y) (n := m) h_fderiv_cdAt (by exact_mod_cast le_top)
  have h_single_norm : ‖(EuclideanSpace.single l (1 : ℝ))‖ = 1 := by
    rw [PiLp.norm_single]; simp
  have h_fderiv_iter : ‖iteratedFDeriv ℝ m (fun z => fderiv ℝ u z) y‖ =
      ‖iteratedFDeriv ℝ (m + 1) u y‖ := norm_iteratedFDeriv_fderiv
  calc ‖iteratedFDeriv ℝ m (fun z => (fderiv ℝ u z) (EuclideanSpace.single l 1)) y‖
      ≤ ‖(EuclideanSpace.single l (1 : ℝ))‖ *
          ‖iteratedFDeriv ℝ m (fun z => fderiv ℝ u z) y‖ := h_clm
    _ = ‖iteratedFDeriv ℝ (m + 1) u y‖ := by rw [h_single_norm, one_mul, h_fderiv_iter]

/-- A `C^∞` (on the chart target) coefficient family is `C^∞` at every interior point. -/
private lemma contDiffAt_of_contDiffOn_chartTarget (α : M)
    {C : EuclN → ℝ} (hC : ContDiffOn ℝ ∞ C (chartTargetEuclid (I := I) (M := M) α))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ C y :=
  hC.contDiffAt ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy)

/-- **The product-summand Leibniz operator-norm bound.** For a `T`-independent `C^∞` coefficient
`C`, a component pair `q`, an interior point `y`, and a derivative-loss `a ∈ {0, 1, 2}` encoded as
the `a`-fold `euclidPartial` iterate of the chart pull-back `F = rawConnLapPull g r s T α q`, the
order-`j` Fréchet derivative of `C · (euclidPartial^a F)` is dominated, by the Leibniz product rule,
by the sum over split orders `i ≤ j` of `C(j, i) · ‖D^i C y‖ · ‖D^{(j - i) + a} F y‖`.  The
`euclidPartial` iterate costs exactly `a` Fréchet orders. -/
private lemma rawConnLapProductSummand_iteratedFDeriv_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (C : EuclN → ℝ) (hC : ContDiffOn ℝ ∞ C (chartTargetEuclid (I := I) (M := M) α))
    (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (Fa : EuclN → ℝ) (a : ℕ)
    (hFa_cd : ∀ z : EuclN, z ∈ chartTargetEuclid (I := I) (M := M) α →
        ContDiffAt ℝ ∞ Fa z)
    (hFa_bd : ∀ (m : ℕ) (z : EuclN), z ∈ chartTargetEuclid (I := I) (M := M) α →
        ‖iteratedFDeriv ℝ m Fa z‖ ≤
          ‖iteratedFDeriv ℝ (m + a)
            (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) z‖)
    (j : ℕ) {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ j (fun z => C z * Fa z) y‖ ≤
      ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i C y‖ *
          ‖iteratedFDeriv ℝ ((j - i) + a)
            (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖ := by
  classical
  set s_set : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hs_set
  have h_open : IsOpen s_set := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_uniq : UniqueDiffOn ℝ s_set := h_open.uniqueDiffOn
  have hC_cdon : ContDiffOn ℝ (j : WithTop ℕ∞) C s_set := hC.of_le (by exact_mod_cast le_top)
  have hFa_cdon : ContDiffOn ℝ (j : WithTop ℕ∞) Fa s_set := by
    intro z hz
    exact (hFa_cd z hz).of_le (by exact_mod_cast le_top) |>.contDiffWithinAt
  rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => C z * Fa z) j h_open hy]
  have hmul := norm_iteratedFDerivWithin_mul_le hC_cdon hFa_cdon h_uniq hy
    (le_refl (j : WithTop ℕ∞))
  refine le_trans hmul ?_
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hi_le : i ≤ j := by have := Finset.mem_range.mp hi; omega
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := C) i h_open hy,
      iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Fa) (j - i) h_open hy]
  have hFa_le := hFa_bd (j - i) y hy
  have h_coeff_nn : 0 ≤ (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i C y‖ := by positivity
  calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i C y‖ * ‖iteratedFDeriv ℝ (j - i) Fa y‖
      ≤ (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i C y‖ *
          ‖iteratedFDeriv ℝ ((j - i) + a)
            (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖ :=
        mul_le_mul_of_nonneg_left hFa_le h_coeff_nn

/-- Near an interior point of the chart target, the chart-pushed raw `q`-component of `T` agrees
with the plain `rawConnLapPull` of that component, so their iterated Fréchet derivatives coincide
there. -/
private lemma chartPushedRaw_eventuallyEq_rawConnLapPull
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)) =ᶠ[nhds y]
      rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2 := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  filter_upwards [h_open.mem_nhds hy] with z hz
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hz]
  rfl

/-- `rawConnLapPull g r s T α q` is `C^∞` at every interior point of the chart target. -/
private lemma rawConnLapPull_contDiffAt'
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y :=
  rawConnLapPull_contDiffAt (I := I) (M := M) g r s T α q.1 q.2 hy

/-- `euclidPartial^a (chartPushedRaw raw_q T)` agrees, near an interior point, with
`euclidPartial^a (rawConnLapPull T α q)`; combined with the one-order `euclidPartial` cost this
yields the operator-norm bound `‖D^m (euclidPartial^a (chartPushedRaw raw_q T)) z‖ ≤
‖D^{m + a} (rawConnLapPull T α q) z‖` for `a = 0, 1, 2`. -/
private lemma euclidPartialIter_chartPushedRaw_norm_le_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (m : ℕ) {z : EuclN} (hz : z ∈ chartTargetEuclid (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ m
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)) z‖ ≤
      ‖iteratedFDeriv ℝ (m + 0)
        (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) z‖ := by
  rw [Nat.add_zero,
    (chartPushedRaw_eventuallyEq_rawConnLapPull (I := I) (M := M) g r s T α q hz).iteratedFDeriv
      ℝ m |>.self_of_nhds]

private lemma euclidPartialIter_chartPushedRaw_norm_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (k : Fin (Module.finrank ℝ E))
    (m : ℕ) {z : EuclN} (hz : z ∈ chartTargetEuclid (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ m
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2))) z‖ ≤
      ‖iteratedFDeriv ℝ (m + 1)
        (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) z‖ := by
  have hev : euclidPartial (E := E) k
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)) =ᶠ[nhds z]
      euclidPartial (E := E) k (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) := by
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_fderiv_ev :
        (fun w => fderiv ℝ
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)) w) =ᶠ[nhds z]
          (fun w => fderiv ℝ (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) w) := by
      filter_upwards [h_open.mem_nhds hz] with w hw
      exact Filter.EventuallyEq.fderiv_eq
        (chartPushedRaw_eventuallyEq_rawConnLapPull (I := I) (M := M) g r s T α q hw)
    filter_upwards [h_fderiv_ev] with w hw
    simp only [euclidPartial_def, hw]
  rw [(hev.iteratedFDeriv ℝ m).self_of_nhds]
  exact euclidPartial_iteratedFDeriv_norm_le (E := E) k
    (rawConnLapPull_contDiffAt' (I := I) (M := M) g r s T α q hz) m

private lemma euclidPartialIter_chartPushedRaw_norm_le_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (k l : Fin (Module.finrank ℝ E))
    (m : ℕ) {z : EuclN} (hz : z ∈ chartTargetEuclid (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ m
        (euclidPartial (E := E) l
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)))) z‖ ≤
      ‖iteratedFDeriv ℝ (m + 2)
        (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) z‖ := by
  set u : EuclN → ℝ := rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2 with hu_def
  have hu_cdAt : ∀ {w : EuclN}, w ∈ chartTargetEuclid (I := I) (M := M) α →
      ContDiffAt ℝ ∞ u w := fun hw =>
    rawConnLapPull_contDiffAt' (I := I) (M := M) g r s T α q hw
  have hev_inner : euclidPartial (E := E) k
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)) =ᶠ[nhds z]
      euclidPartial (E := E) k u := by
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_fderiv_ev :
        (fun w => fderiv ℝ
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)) w) =ᶠ[nhds z]
          (fun w => fderiv ℝ u w) := by
      filter_upwards [h_open.mem_nhds hz] with w hw
      exact Filter.EventuallyEq.fderiv_eq
        (chartPushedRaw_eventuallyEq_rawConnLapPull (I := I) (M := M) g r s T α q hw)
    filter_upwards [h_fderiv_ev] with w hw
    simp only [euclidPartial_def, hw]
  have hev_outer : euclidPartial (E := E) l
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2))) =ᶠ[nhds z]
      euclidPartial (E := E) l (euclidPartial (E := E) k u) := by
    have h_fderiv_ev :
        (fun w => fderiv ℝ
            (euclidPartial (E := E) k
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2))) w) =ᶠ[nhds z]
          (fun w => fderiv ℝ (euclidPartial (E := E) k u) w) :=
      hev_inner.fderiv
    filter_upwards [h_fderiv_ev] with w hw
    simp only [euclidPartial_def, hw]
  rw [(hev_outer.iteratedFDeriv ℝ m).self_of_nhds]
  calc ‖iteratedFDeriv ℝ m (euclidPartial (E := E) l (euclidPartial (E := E) k u)) z‖
      ≤ ‖iteratedFDeriv ℝ (m + 1) (euclidPartial (E := E) k u) z‖ :=
        euclidPartial_iteratedFDeriv_norm_le (E := E) l
          (euclidPartial_contDiffAt (E := E) k (hu_cdAt hz)) m
    _ ≤ ‖iteratedFDeriv ℝ (m + 1 + 1) u z‖ :=
        euclidPartial_iteratedFDeriv_norm_le (E := E) k (hu_cdAt hz) (m + 1)
    _ = ‖iteratedFDeriv ℝ (m + 2) u z‖ := by ring_nf

/-- `chartPushedRaw (raw_q T)` is `C^∞` at interior points of the chart target. -/
private lemma chartPushedRaw_raw_contDiffAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    {z : EuclN} (hz : z ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)) z :=
  (chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g r s T α q.1 q.2).contDiffAt
    ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hz)

/-- The `a`-fold `euclidPartial` iterate of `chartPushedRaw (raw_q T)` is `C^∞` at interior points
of the chart target (`a = 0, 1, 2`). -/
private lemma euclidPartialIter1_chartPushedRaw_contDiffAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))) (k : Fin (Module.finrank ℝ E))
    {z : EuclN} (hz : z ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞
      (euclidPartial (E := E) k
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2))) z :=
  euclidPartial_contDiffAt (E := E) k
    (chartPushedRaw_raw_contDiffAt (I := I) (M := M) g r s T α q hz)

private lemma euclidPartialIter2_chartPushedRaw_contDiffAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))) (k l : Fin (Module.finrank ℝ E))
    {z : EuclN} (hz : z ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞
      (euclidPartial (E := E) l
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)))) z :=
  euclidPartial_contDiffAt (E := E) l
    (euclidPartialIter1_chartPushedRaw_contDiffAt (I := I) (M := M) g r s T α q k hz)

/-- **The open-good-set `T₀`-linear chart-coordinate formula for the connection-Laplacian raw
component (a genuine differential-geometric prerequisite).**

There exist `T₀`-independent `C^∞` coefficient families `C_2`, `C_1`, `C_0` on the Euclidean chart
target such that for *every* smooth compactly-supported section `T₀` and *every* base point `b` in
the chart-`α` Levi-Civita good set (the open chart source on a boundaryless manifold), the chart-`α`
`(Idx, Jdx)` raw scalar component of `Δ_∇ T₀ = rawTensorConnLapSmooth g r s T₀` equals the explicit
mixed-second-partial principal block plus a first-partial block plus a zeroth-order block:
```
raw_{IJ}(Δ_∇ T₀)(b)
  = Σ_{k, l} C_2 k l · ∂_l ∂_k (chartPushedRaw raw_{IJ}(T₀))
  + Σ_{I', J', m} C_1 I' J' m · ∂_m (chartPushedRaw raw_{I'J'}(T₀))
  + Σ_{I', J'} C_0 I' J' · chartPushedRaw raw_{I'J'}(T₀)    (at toEuclidean (chart b)).
```

This is the open-good-set strengthening of the tsupport-restricted on-disk formula
`rawTensorConnLap_chartα_raw_eq_T₀_linear_formula`: the connection Laplacian is the metric trace of
the second covariant derivative — a pointwise identity at *every* point of the good set,
`Δ_∇ T₀ = Σ_{k, l} g^{kl} (∇² T₀)(∂_k, ∂_l)` — and each chart-projected `(∇² T₀)(∂_k, ∂_l)` expands,
by the open-good-set second-covariant-derivative chart expansion
`secondCovDeriv_chartα_proj_eq_iteratedFDeriv_T₀_eqOn`, into the principal mixed-second partial plus
`T₀`-independent-coefficient first- and zeroth-order chart blocks.  The tsupport restriction in the
on-disk version is inessential to the trace identity (it is inherited from the global orthonormal
frame's support-localised orthonormality, removable by using the chart inverse-Gram contraction in
place of that frame).  Posited here as the genuine remaining DG prerequisite; the pointwise
operator-norm bound below is proved sorry-free on top of it. -/
theorem rawTensorConnLap_chartα_raw_eq_T₀_linear_formula_on_goodSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ (C_2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ),
    ∃ (C_1 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) →
              Fin (Module.finrank ℝ E) → EuclN → ℝ),
    ∃ (C_0 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ),
      (∀ k l, ContDiffOn ℝ ∞ (C_2 k l) (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ I' J' m, ContDiffOn ℝ ∞ (C_1 I' J' m) (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ I' J', ContDiffOn ℝ ∞ (C_0 I' J') (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∀ (T₀ : Integral.L2.SmoothCcTensor g r s),
        ∀ {b : M}, b ∈ chartLeviCivitaGoodSet (I := I) α →
          tensorChartComponentRaw (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
            (∑ k, ∑ l,
              C_2 k l ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                euclidPartial (E := E) l
                  (euclidPartial (E := E) k
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) +
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              ∑ m,
              C_1 I' J' m ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                euclidPartial (E := E) m
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J'))
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) +
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              C_0 I' J' ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) :=
  sorry

/-- A `C^∞` function on an open set has, on any compact subset, a uniform bound on all its iterated
Fréchet derivative norms up to a fixed order `N`. -/
private lemma exists_iteratedFDeriv_norm_bound_on_compact
    {f : EuclN → ℝ} {sset : Set EuclN} (hf : ContDiffOn ℝ ∞ f sset) (hs : IsOpen sset)
    {K : Set EuclN} (hK : IsCompact K) (hKs : K ⊆ sset) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l ≤ N, ∀ y ∈ K, ‖iteratedFDeriv ℝ l f y‖ ≤ C := by
  classical
  have h_uniq : UniqueDiffOn ℝ sset := hs.uniqueDiffOn
  have h_per_order : ∀ l : ℕ, ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ y ∈ K,
      ‖iteratedFDeriv ℝ l f y‖ ≤ Cl := by
    intro l
    by_cases hKne : K.Nonempty
    · have h_iter_contOn : ContinuousOn (fun y => iteratedFDerivWithin ℝ l f sset y) sset :=
        hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) h_uniq
      have h_iter_K : ContinuousOn (iteratedFDerivWithin ℝ l f sset) K :=
        h_iter_contOn.mono hKs
      have h_norm_K : ContinuousOn (fun y => ‖iteratedFDerivWithin ℝ l f sset y‖) K :=
        continuous_norm.comp_continuousOn h_iter_K
      obtain ⟨y₀, _, hy₀_max⟩ := hK.exists_isMaxOn hKne h_norm_K
      refine ⟨‖iteratedFDerivWithin ℝ l f sset y₀‖, norm_nonneg _, fun y hy => ?_⟩
      have h₁ : ‖iteratedFDerivWithin ℝ l f sset y‖ ≤
          ‖iteratedFDerivWithin ℝ l f sset y₀‖ := hy₀_max hy
      rwa [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) l hs (hKs hy)] at h₁
    · exact ⟨0, le_refl _, fun y hy => absurd ⟨y, hy⟩ hKne⟩
  choose Cl hCl_nn hCl using h_per_order
  refine ⟨(Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩ Cl, ?_, ?_⟩
  · exact le_trans (hCl_nn 0)
      (Finset.le_sup' Cl (Finset.mem_range.mpr (Nat.succ_pos N)))
  · intro l hl y hy
    exact (hCl l y hy).trans
      (Finset.le_sup' Cl (Finset.mem_range.mpr (by omega)))

/-- For `y` in the chart target, the preimage base point
`(extChartAt I α).symm (toEuclidean.symm y)` lies in the chart-`α` Levi-Civita good set (the chart
source, on a boundaryless manifold), and its chart image recovers `y`. -/
private lemma chartTargetEuclid_preimage_mem_goodSet
    (α : M) {y : EuclN} (hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ chartLeviCivitaGoodSet (I := I) α ∧
      (toEuclidean (E := E)) ((extChartAt I α)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) = y := by
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
    exact hy_target
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_src : b ∈ (extChartAt I α).source := (extChartAt I α).map_target hy_pre
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I)]; exact hb_src
  refine ⟨hb_good, ?_⟩
  have h_round : (extChartAt I α) b = (toEuclidean (E := E)).symm y :=
    (extChartAt I α).right_inv hy_pre
  rw [h_round]; simp

/-- A finite sum of product summands `C_ι · Fa_ι`, each with order-`j` Fréchet derivative
operator-norm bounded by `Mb` at an interior point `y`, has total order-`j` Fréchet derivative
operator norm at `y` bounded by `(card ι) · Mb`. -/
private lemma block_iteratedFDeriv_norm_le
    {ι : Type*} [Fintype ι] (α : M) (Cf Faf : ι → EuclN → ℝ) {y : EuclN}
    (hCf_cd : ∀ i : ι, ContDiffOn ℝ ∞ (Cf i) (chartTargetEuclid (I := I) (M := M) α))
    (hFaf_cd : ∀ i : ι, ContDiffAt ℝ ∞ (Faf i) y)
    (Mb : ℝ) (j : ℕ)
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hsummand : ∀ i : ι,
        ‖iteratedFDeriv ℝ j (fun z => Cf i z * Faf i z) y‖ ≤ Mb) :
    ‖iteratedFDeriv ℝ j (fun z => ∑ i : ι, Cf i z * Faf i z) y‖ ≤
      (Fintype.card ι : ℝ) * Mb := by
  classical
  set s_set : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hs_set
  have h_open : IsOpen s_set := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_uniq : UniqueDiffOn ℝ s_set := h_open.uniqueDiffOn
  have h_prod_cdwa : ∀ i : ι,
      ContDiffWithinAt ℝ j (fun z => Cf i z * Faf i z) s_set y := by
    intro i
    have hC : ContDiffWithinAt ℝ j (Cf i) s_set y :=
      ((hCf_cd i).of_le (by exact_mod_cast le_top)) y hy
    have hF : ContDiffWithinAt ℝ j (Faf i) s_set y :=
      ((hFaf_cd i).of_le (by exact_mod_cast le_top)).contDiffWithinAt
    exact hC.mul hF
  rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
      (f := fun z => ∑ i : ι, Cf i z * Faf i z) j h_open hy]
  rw [iteratedFDerivWithin_fun_sum_apply h_uniq hy (fun i _ => h_prod_cdwa i)]
  refine le_trans (norm_sum_le _ _) ?_
  have hsummand' : ∀ i ∈ (Finset.univ : Finset ι),
      ‖iteratedFDerivWithin ℝ j (fun z => Cf i z * Faf i z) s_set y‖ ≤ Mb := by
    intro i _
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => Cf i z * Faf i z) j h_open hy]
    exact hsummand i
  refine le_trans (Finset.sum_le_sum hsummand') ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The per-chart pointwise second-order rough-Laplacian chart-component operator-norm bound.**

The chart-`α`-localised form of the headline pointwise bound: for each fixed chart base point `α`,
there is a non-negative constant `B_α` such that on the compact kernel `chartImagePOUTsupport α`,
every order-`j` (`j ≤ 2k`) Fréchet derivative operator norm of the chart-pulled raw `(Idx, Jdx)`
component of `Δ_∇ T` is square-bounded by `B_α` times the order-`(k + 1)` Hilbert-Schmidt content of
`T`.  Proved sorry-free on top of the open-good-set `T₀`-linear formula
`rawTensorConnLap_chartα_raw_eq_T₀_linear_formula_on_goodSet`: the chart pull-back agrees on the open
chart target with the explicit principal-`∂²` plus first-`∂` plus zeroth blocks; an order-`j` Fréchet
derivative of each block is dominated, by the Leibniz product rule, by uniformly-bounded coefficient
derivatives times order-`≤ j + 2 ≤ 2(k + 1)` derivatives of the raw components of `T`, the latter
controlled by the Hilbert-Schmidt content; the coefficients are uniformly bounded on the compact
kernel.  The atlas-uniform constant is assembled from this per-chart form over the finite active set
of the partition of unity. -/
private lemma exists_rawConnLapComp_iteratedFDeriv_norm_sq_le_rawConnLapRhsHsContent_perAlpha
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ Bα : ℝ, 0 ≤ Bα ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s) (j : ℕ), j ≤ 2 * k →
        ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ j
              (rawConnLapPull (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) y‖ ^ 2 ≤
            Bα * rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y := by
  classical
  obtain ⟨C_2, C_1, C_0, hC2cd, hC1cd, hC0cd, hform⟩ :=
    rawTensorConnLap_chartα_raw_eq_T₀_linear_formula_on_goodSet (I := I) (M := M) g r s α Idx Jdx
  let n : ℕ := Module.finrank ℝ E
  set K : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  -- Uniform coefficient sup-bounds on the compact kernel, up to order `2k`.
  obtain ⟨B2, hB2_nn, hB2⟩ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k' l' : Fin n), ∀ i ≤ 2 * k, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ i (C_2 k' l') y‖ ≤ C := by
    have h_each : ∀ p : Fin n × Fin n, ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ 2 * k, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ i (C_2 p.1 p.2) y‖ ≤ C := fun p =>
      exists_iteratedFDeriv_norm_bound_on_compact (hC2cd p.1 p.2) h_open hK_compact hK_sub (2 * k)
    choose Cf hCf_nn hCf using h_each
    refine ⟨(Finset.univ : Finset (Fin n × Fin n)).sup' Finset.univ_nonempty Cf, ?_, ?_⟩
    · obtain ⟨p₀, _⟩ := Finset.univ_nonempty (α := Fin n × Fin n)
      exact (hCf_nn p₀).trans (Finset.le_sup'_of_le Cf (Finset.mem_univ p₀) le_rfl)
    · intro k' l' i hi y hy
      exact (hCf ⟨k', l'⟩ i hi y hy).trans
        (Finset.le_sup'_of_le Cf (Finset.mem_univ (⟨k', l'⟩ : Fin n × Fin n)) le_rfl)
  obtain ⟨B1, hB1_nn, hB1⟩ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I' : Fin r → Fin n) (J' : Fin s → Fin n) (m : Fin n), ∀ i ≤ 2 * k, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ i (C_1 I' J' m) y‖ ≤ C := by
    have h_each : ∀ p : (Fin r → Fin n) × (Fin s → Fin n) × Fin n,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ 2 * k, ∀ y ∈ K,
          ‖iteratedFDeriv ℝ i (C_1 p.1 p.2.1 p.2.2) y‖ ≤ C := fun p =>
      exists_iteratedFDeriv_norm_bound_on_compact (hC1cd p.1 p.2.1 p.2.2)
        h_open hK_compact hK_sub (2 * k)
    choose Cf hCf_nn hCf using h_each
    refine ⟨(Finset.univ : Finset ((Fin r → Fin n) × (Fin s → Fin n) × Fin n)).sup'
        Finset.univ_nonempty Cf, ?_, ?_⟩
    · obtain ⟨p₀, _⟩ := Finset.univ_nonempty (α := (Fin r → Fin n) × (Fin s → Fin n) × Fin n)
      exact (hCf_nn p₀).trans (Finset.le_sup'_of_le Cf (Finset.mem_univ p₀) le_rfl)
    · intro I' J' m i hi y hy
      exact (hCf ⟨I', J', m⟩ i hi y hy).trans
        (Finset.le_sup'_of_le Cf (Finset.mem_univ
          (⟨I', J', m⟩ : (Fin r → Fin n) × (Fin s → Fin n) × Fin n)) le_rfl)
  obtain ⟨B0, hB0_nn, hB0⟩ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I' : Fin r → Fin n) (J' : Fin s → Fin n), ∀ i ≤ 2 * k, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ i (C_0 I' J') y‖ ≤ C := by
    have h_each : ∀ p : (Fin r → Fin n) × (Fin s → Fin n),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ 2 * k, ∀ y ∈ K,
          ‖iteratedFDeriv ℝ i (C_0 p.1 p.2) y‖ ≤ C := fun p =>
      exists_iteratedFDeriv_norm_bound_on_compact (hC0cd p.1 p.2) h_open hK_compact hK_sub (2 * k)
    choose Cf hCf_nn hCf using h_each
    refine ⟨(Finset.univ : Finset ((Fin r → Fin n) × (Fin s → Fin n))).sup'
        Finset.univ_nonempty Cf, ?_, ?_⟩
    · obtain ⟨p₀, _⟩ := Finset.univ_nonempty (α := (Fin r → Fin n) × (Fin s → Fin n))
      exact (hCf_nn p₀).trans (Finset.le_sup'_of_le Cf (Finset.mem_univ p₀) le_rfl)
    · intro I' J' i hi y hy
      exact (hCf ⟨I', J'⟩ i hi y hy).trans
        (Finset.le_sup'_of_le Cf (Finset.mem_univ
          (⟨I', J'⟩ : (Fin r → Fin n) × (Fin s → Fin n))) le_rfl)
  -- Uniform coefficient bound and combinatorial cardinalities.
  set Bmax : ℝ := max B2 (max B1 B0) with hBmax_def
  have hBmax_nn : 0 ≤ Bmax := le_trans hB2_nn (le_max_left _ _)
  have hB2_le : B2 ≤ Bmax := le_max_left _ _
  have hB1_le : B1 ≤ Bmax := le_trans (le_max_left _ _) (le_max_right _ _)
  have hB0_le : B0 ≤ Bmax := le_trans (le_max_right _ _) (le_max_right _ _)
  set NP : ℕ := Fintype.card ((Fin r → Fin n) × (Fin s → Fin n)) with hNP_def
  set Ntot : ℕ := n * n + NP * n + NP with hNtot_def
  set Ktot : ℝ := (Ntot : ℝ) * (2 : ℝ) ^ (2 * k) * Bmax with hKtot_def
  have hKtot_nn : 0 ≤ Ktot := by rw [hKtot_def]; positivity
  refine ⟨Ktot ^ 2, by positivity, ?_⟩
  intro T j hj y hyK
  set R : ℝ := rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y with hR_def
  have hR_nn : 0 ≤ R := rawConnLapRhsHsContent_nonneg (I := I) (M := M) g r s k T α y
  have hsqrtR_nn : 0 ≤ Real.sqrt R := Real.sqrt_nonneg _
  have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := hK_sub hyK
  -- The chart pull-back of `Δ_∇ T`, as a function near `y`, equals the explicit three-block sum.
  set Δpull : EuclN → ℝ := rawConnLapPull (I := I) (M := M) g r s
    (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx with hΔpull_def
  set RHSfun : EuclN → ℝ := fun z =>
    (∑ k', ∑ l',
      C_2 k' l' z *
        euclidPartial (E := E) l'
          (euclidPartial (E := E) k'
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))) z) +
    (∑ I' : Fin r → Fin n, ∑ J' : Fin s → Fin n, ∑ m,
      C_1 I' J' m z *
        euclidPartial (E := E) m
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α I' J')) z) +
    (∑ I' : Fin r → Fin n, ∑ J' : Fin s → Fin n,
      C_0 I' J' z *
        chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α I' J') z) with hRHSfun_def
  have h_evEq : Δpull =ᶠ[nhds y] RHSfun := by
    filter_upwards [h_open.mem_nhds hy_target] with z hz
    obtain ⟨hb_good, hb_round⟩ := chartTargetEuclid_preimage_mem_goodSet (I := I) (M := M) α hz
    have hform_z := hform T hb_good
    rw [hΔpull_def]
    change tensorChartComponentRaw (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) = RHSfun z
    rw [hform_z, hb_round, hRHSfun_def]
  rw [(h_evEq.iteratedFDeriv ℝ j).self_of_nhds]
  -- A single summand operator-norm bound, after Leibniz: ≤ 2^{2k} · Bmax · √R.
  have hraw_sqrt : ∀ (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))) (m : ℕ), m ≤ 2 * (k + 1) →
      ‖iteratedFDeriv ℝ m (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖ ≤
        Real.sqrt R := by
    intro q m hm
    have hsq := rawConnLapPull_iteratedFDeriv_norm_sq_le_rhsContent (I := I) (M := M)
      g r s k T α q m hm y
    calc ‖iteratedFDeriv ℝ m (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖
        = Real.sqrt (‖iteratedFDeriv ℝ m
            (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖ ^ 2) := by
          rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt R := Real.sqrt_le_sqrt hsq
  have h_summand : ∀ (C : EuclN → ℝ)
      (hC : ContDiffOn ℝ ∞ C (chartTargetEuclid (I := I) (M := M) α))
      (hCbd : ∀ i ≤ 2 * k, ∀ z ∈ K, ‖iteratedFDeriv ℝ i C z‖ ≤ Bmax)
      (q : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)))
      (Fa : EuclN → ℝ) (a : ℕ) (ha : a ≤ 2)
      (hFa_cd : ∀ z : EuclN, z ∈ chartTargetEuclid (I := I) (M := M) α →
          ContDiffAt ℝ ∞ Fa z)
      (hFa_bd : ∀ (m : ℕ) (z : EuclN), z ∈ chartTargetEuclid (I := I) (M := M) α →
          ‖iteratedFDeriv ℝ m Fa z‖ ≤
            ‖iteratedFDeriv ℝ (m + a)
              (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) z‖),
      ‖iteratedFDeriv ℝ j (fun z => C z * Fa z) y‖ ≤ (2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R := by
    intro C hC hCbd q Fa a ha hFa_cd hFa_bd
    have hbound := rawConnLapProductSummand_iteratedFDeriv_norm_le (I := I) (M := M)
      g r s T α C hC q Fa a hFa_cd hFa_bd j hy_target
    refine le_trans hbound ?_
    have h_per : ∀ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i C y‖ *
          ‖iteratedFDeriv ℝ ((j - i) + a)
            (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖ ≤
        (j.choose i : ℝ) * (Bmax * Real.sqrt R) := by
      intro i hi
      have hi_le : i ≤ 2 * k := by have := Finset.mem_range.mp hi; omega
      have hC_le : ‖iteratedFDeriv ℝ i C y‖ ≤ Bmax := hCbd i hi_le y hyK
      have hord : (j - i) + a ≤ 2 * (k + 1) := by omega
      have hraw_le := hraw_sqrt q ((j - i) + a) hord
      have h1 : (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i C y‖ *
            ‖iteratedFDeriv ℝ ((j - i) + a)
              (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖ ≤
          (j.choose i : ℝ) * Bmax * Real.sqrt R := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hC_le (by positivity)) hraw_le
          (norm_nonneg _) (by positivity)
      calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i C y‖ *
            ‖iteratedFDeriv ℝ ((j - i) + a)
              (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖
          ≤ (j.choose i : ℝ) * Bmax * Real.sqrt R := h1
        _ = (j.choose i : ℝ) * (Bmax * Real.sqrt R) := by ring
    refine le_trans (Finset.sum_le_sum h_per) ?_
    rw [← Finset.sum_mul]
    have hsum_choose : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
      rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
    rw [hsum_choose]
    have h2j_le : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (2 * k) := pow_le_pow_right₀ (by norm_num) hj
    calc (2 : ℝ) ^ j * (Bmax * Real.sqrt R)
        ≤ (2 : ℝ) ^ (2 * k) * (Bmax * Real.sqrt R) :=
          mul_le_mul_of_nonneg_right h2j_le (by positivity)
      _ = (2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R := by ring
  -- Bound `‖D^j RHSfun y‖` by `Ktot · √R` via the three blocks.
  have h_block2_le :
      ‖iteratedFDeriv ℝ j (fun z =>
        ∑ p : Fin n × Fin n,
          C_2 p.1 p.2 z *
            euclidPartial (E := E) p.2
              (euclidPartial (E := E) p.1
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))) z) y‖ ≤
        (n * n : ℝ) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) := by
    have hcardN : (Fintype.card (Fin n × Fin n) : ℝ) = (n * n : ℝ) := by
      have : Fintype.card (Fin n × Fin n) = n * n := by
        simp [Fintype.card_prod, Fintype.card_fin]
      rw [this]; push_cast; ring
    rw [show (n * n : ℝ) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) =
        (Fintype.card (Fin n × Fin n) : ℝ) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) by
      rw [hcardN]]
    refine block_iteratedFDeriv_norm_le (I := I) (M := M) α
      (fun p : Fin n × Fin n => C_2 p.1 p.2)
      (fun p : Fin n × Fin n =>
        euclidPartial (E := E) p.2
          (euclidPartial (E := E) p.1
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))))
      (fun p => hC2cd p.1 p.2)
      (fun p => euclidPartialIter2_chartPushedRaw_contDiffAt (I := I) (M := M)
        g r s T α ⟨Idx, Jdx⟩ p.1 p.2 hy_target)
      _ j hy_target (fun p => ?_)
    exact h_summand (C_2 p.1 p.2) (hC2cd p.1 p.2)
      (fun i hi z hz => le_trans (hB2 p.1 p.2 i hi z hz) hB2_le)
      ⟨Idx, Jdx⟩ _ 2 le_rfl
      (fun z hz => euclidPartialIter2_chartPushedRaw_contDiffAt (I := I) (M := M)
        g r s T α ⟨Idx, Jdx⟩ p.1 p.2 hz)
      (fun m z hz => euclidPartialIter_chartPushedRaw_norm_le_two (I := I) (M := M)
        g r s T α ⟨Idx, Jdx⟩ p.1 p.2 m hz)
  have h_block1_le :
      ‖iteratedFDeriv ℝ j (fun z =>
        ∑ p : ((Fin r → Fin n) × (Fin s → Fin n)) × Fin n,
          C_1 p.1.1 p.1.2 p.2 z *
            euclidPartial (E := E) p.2
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1.1 p.1.2)) z) y‖ ≤
        ((NP : ℝ) * n) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) := by
    have hcardN : (Fintype.card (((Fin r → Fin n) × (Fin s → Fin n)) × Fin n) : ℝ) =
        ((NP : ℝ) * n) := by
      rw [Fintype.card_prod, hNP_def]
      simp [Fintype.card_fin]
    rw [show ((NP : ℝ) * n) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) =
        (Fintype.card (((Fin r → Fin n) × (Fin s → Fin n)) × Fin n) : ℝ) *
          ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) by rw [hcardN]]
    refine block_iteratedFDeriv_norm_le (I := I) (M := M) α
      (fun p : ((Fin r → Fin n) × (Fin s → Fin n)) × Fin n => C_1 p.1.1 p.1.2 p.2)
      (fun p : ((Fin r → Fin n) × (Fin s → Fin n)) × Fin n =>
        euclidPartial (E := E) p.2
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1.1 p.1.2)))
      (fun p => hC1cd p.1.1 p.1.2 p.2)
      (fun p => euclidPartialIter1_chartPushedRaw_contDiffAt (I := I) (M := M)
        g r s T α p.1 p.2 hy_target)
      _ j hy_target (fun p => ?_)
    exact h_summand (C_1 p.1.1 p.1.2 p.2) (hC1cd p.1.1 p.1.2 p.2)
      (fun i hi z hz => le_trans (hB1 p.1.1 p.1.2 p.2 i hi z hz) hB1_le)
      p.1 _ 1 (by norm_num)
      (fun z hz => euclidPartialIter1_chartPushedRaw_contDiffAt (I := I) (M := M)
        g r s T α p.1 p.2 hz)
      (fun m z hz => euclidPartialIter_chartPushedRaw_norm_le_one (I := I) (M := M)
        g r s T α p.1 p.2 m hz)
  have h_block0_le :
      ‖iteratedFDeriv ℝ j (fun z =>
        ∑ p : (Fin r → Fin n) × (Fin s → Fin n),
          C_0 p.1 p.2 z *
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2) z) y‖ ≤
        (NP : ℝ) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) := by
    rw [show (NP : ℝ) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) =
        (Fintype.card ((Fin r → Fin n) × (Fin s → Fin n)) : ℝ) *
          ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) by rw [← hNP_def]]
    refine block_iteratedFDeriv_norm_le (I := I) (M := M) α
      (fun p : (Fin r → Fin n) × (Fin s → Fin n) => C_0 p.1 p.2)
      (fun p : (Fin r → Fin n) × (Fin s → Fin n) =>
        chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2))
      (fun p => hC0cd p.1 p.2)
      (fun p => chartPushedRaw_raw_contDiffAt (I := I) (M := M) g r s T α p hy_target)
      _ j hy_target (fun p => ?_)
    exact h_summand (C_0 p.1 p.2) (hC0cd p.1 p.2)
      (fun i hi z hz => le_trans (hB0 p.1 p.2 i hi z hz) hB0_le)
      p _ 0 (by norm_num)
      (fun z hz => chartPushedRaw_raw_contDiffAt (I := I) (M := M) g r s T α p hz)
      (fun m z hz => euclidPartialIter_chartPushedRaw_norm_le_zero (I := I) (M := M)
        g r s T α p m hz)
  -- Assemble: ‖D^j RHSfun‖ ≤ Ktot · √R, then square.
  have h_norm_le : ‖iteratedFDeriv ℝ j RHSfun y‖ ≤ Ktot * Real.sqrt R := by
    set b2fn : EuclN → ℝ := fun z =>
      ∑ p : Fin n × Fin n,
        C_2 p.1 p.2 z *
          euclidPartial (E := E) p.2
            (euclidPartial (E := E) p.1
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))) z with hb2fn_def
    set b1fn : EuclN → ℝ := fun z =>
      ∑ p : ((Fin r → Fin n) × (Fin s → Fin n)) × Fin n,
        C_1 p.1.1 p.1.2 p.2 z *
          euclidPartial (E := E) p.2
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1.1 p.1.2)) z with hb1fn_def
    set b0fn : EuclN → ℝ := fun z =>
      ∑ p : (Fin r → Fin n) × (Fin s → Fin n),
        C_0 p.1 p.2 z *
          chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2) z with hb0fn_def
    have hb2_cd : ContDiffAt ℝ (j : WithTop ℕ∞) b2fn y := by
      rw [hb2fn_def]
      refine ContDiffAt.sum (fun p _ => ?_)
      exact ((contDiffAt_of_contDiffOn_chartTarget (I := I) (M := M) α
        (hC2cd p.1 p.2) hy_target).mul
        (euclidPartialIter2_chartPushedRaw_contDiffAt (I := I) (M := M)
          g r s T α ⟨Idx, Jdx⟩ p.1 p.2 hy_target)).of_le (by exact_mod_cast le_top)
    have hb1_cd : ContDiffAt ℝ (j : WithTop ℕ∞) b1fn y := by
      rw [hb1fn_def]
      refine ContDiffAt.sum (fun p _ => ?_)
      exact ((contDiffAt_of_contDiffOn_chartTarget (I := I) (M := M) α
        (hC1cd p.1.1 p.1.2 p.2) hy_target).mul
        (euclidPartialIter1_chartPushedRaw_contDiffAt (I := I) (M := M)
          g r s T α p.1 p.2 hy_target)).of_le (by exact_mod_cast le_top)
    have hb0_cd : ContDiffAt ℝ (j : WithTop ℕ∞) b0fn y := by
      rw [hb0fn_def]
      refine ContDiffAt.sum (fun p _ => ?_)
      exact ((contDiffAt_of_contDiffOn_chartTarget (I := I) (M := M) α
        (hC0cd p.1 p.2) hy_target).mul
        (chartPushedRaw_raw_contDiffAt (I := I) (M := M) g r s T α p hy_target)).of_le
        (by exact_mod_cast le_top)
    have he2 : ∀ z, b2fn z =
        ∑ k', ∑ l',
          C_2 k' l' z *
            euclidPartial (E := E) l'
              (euclidPartial (E := E) k'
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))) z := by
      intro z; rw [hb2fn_def]; dsimp only; rw [Fintype.sum_prod_type]
    have he1 : ∀ z, b1fn z =
        ∑ I' : Fin r → Fin n, ∑ J' : Fin s → Fin n, ∑ m,
          C_1 I' J' m z *
            euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T α I' J')) z := by
      intro z
      rw [hb1fn_def]
      dsimp only
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    have he0 : ∀ z, b0fn z =
        ∑ I' : Fin r → Fin n, ∑ J' : Fin s → Fin n,
          C_0 I' J' z *
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α I' J') z := by
      intro z; rw [hb0fn_def]; dsimp only; rw [Fintype.sum_prod_type]
    have hRHS_eq : RHSfun = fun z => (b2fn z + b1fn z) + b0fn z := by
      funext z
      rw [he2 z, he1 z, he0 z, hRHSfun_def]
    have hadd : iteratedFDeriv ℝ j RHSfun y =
        iteratedFDeriv ℝ j b2fn y + (iteratedFDeriv ℝ j b1fn y + iteratedFDeriv ℝ j b0fn y) := by
      rw [hRHS_eq,
        fun_iteratedFDeriv_add_apply (hb2_cd.add hb1_cd) hb0_cd,
        fun_iteratedFDeriv_add_apply hb2_cd hb1_cd]
      exact add_assoc _ _ _
    rw [hadd]
    have hsplit : ‖iteratedFDeriv ℝ j b2fn y +
          (iteratedFDeriv ℝ j b1fn y + iteratedFDeriv ℝ j b0fn y)‖ ≤
        ‖iteratedFDeriv ℝ j b2fn y‖ +
          (‖iteratedFDeriv ℝ j b1fn y‖ + ‖iteratedFDeriv ℝ j b0fn y‖) := by
      refine le_trans (norm_add_le _ _) ?_
      gcongr
      exact norm_add_le _ _
    refine le_trans hsplit ?_
    have h3 := add_le_add h_block2_le (add_le_add h_block1_le h_block0_le)
    refine le_trans h3 ?_
    rw [hKtot_def]
    have : ((Ntot : ℝ) * (2 : ℝ) ^ (2 * k) * Bmax) * Real.sqrt R =
        (n * n : ℝ) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) +
        (((NP : ℝ) * n) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) +
          (NP : ℝ) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R)) := by
      rw [hNtot_def]; push_cast; ring
    rw [this]
  calc ‖iteratedFDeriv ℝ j RHSfun y‖ ^ 2
      ≤ (Ktot * Real.sqrt R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h_norm_le 2
    _ = Ktot ^ 2 * R := by rw [mul_pow, Real.sq_sqrt hR_nn]

/-- **The pointwise second-order rough-Laplacian chart-component operator-norm bound (the genuine
atomic 2nd-order elliptic-boundedness primitive).**

For a closed Riemannian manifold and ranks `(r, s)`, there is a non-negative constant `B`, uniform
in the tensor `T` and the chart base point `α`, such that on the compact chart image of the
chart-`α` partition-of-unity support, every order-`j` (`j ≤ 2k`) Fréchet derivative operator norm of
the chart-pulled raw `(Idx, Jdx)`-component of the smooth rough Laplacian `Δ_∇ T =
rawTensorConnLapSmooth g r s T` is square-bounded by `B` times the order-`(k + 1)` Hilbert-Schmidt
content of the raw components of `T`:
```
‖D^j (raw_{IJ}(Δ_∇ T) ∘ chart⁻¹ ∘ toEuclidean⁻¹) y‖²
  ≤ B · rawConnLapRhsHsContent g r s k T α y      (y ∈ chartImagePOUTsupport α,  j ≤ 2k).
```

This is the genuine analytic single-step (`+1` `toHs`-order) rough-Laplacian content.  It is proved
on top of the open-good-set `T₀`-linear chart-coordinate formula
`rawTensorConnLap_chartα_raw_eq_T₀_linear_formula_on_goodSet`: on the open chart target the chart
pull-back of `Δ_∇ T` agrees (eventually, by `chartTargetEuclid_preimage_mem_goodSet`) with the
explicit sum of a principal mixed-second-partial block `Σ C_2 · ∂²(chartPushedRaw raw)`, a
first-partial block `Σ C_1 · ∂(chartPushedRaw raw)`, and a zeroth block `Σ C_0 · chartPushedRaw raw`,
with `T`-independent `C^∞` coefficients.  An order-`j` (`j ≤ 2k`) Fréchet derivative of each block is
dominated, by the Leibniz product rule (`norm_iteratedFDerivWithin_mul_le`) and the one-order
`euclidPartial` cost, by uniformly-bounded (on the compact kernel) coefficient derivatives times
order-`(j - i) + a ≤ 2(k + 1)` Fréchet derivatives of the raw components of `T` (with block arity
`a ∈ {2, 1, 0}`), the latter controlled by the order-`(k + 1)` Hilbert-Schmidt content.  The
atlas-uniform constant `B` is assembled from the per-chart constant over the finite active set of the
partition of unity (`chartAtlasPOU_activeFinset`), the kernel being empty off it.  It carries no
spectral nonlinearity and no Weyl dependence. -/
theorem exists_rawConnLapComp_iteratedFDeriv_norm_sq_le_rawConnLapRhsHsContent
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (j : ℕ), j ≤ 2 * k →
        ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ j
              (rawConnLapPull (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) y‖ ^ 2 ≤
            B * rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y := by
  classical
  -- Per-chart constants, assembled into an atlas-uniform `B` over the finite active set.
  have hperα : ∀ w : M × (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)), ∃ Bα : ℝ, 0 ≤ Bα ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s) (j : ℕ), j ≤ 2 * k →
        ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) w.1,
          ‖iteratedFDeriv ℝ j
              (rawConnLapPull (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T) w.1 w.2.1 w.2.2) y‖ ^ 2 ≤
            Bα * rawConnLapRhsHsContent (I := I) (M := M) g r s k T w.1 y := fun w =>
    exists_rawConnLapComp_iteratedFDeriv_norm_sq_le_rawConnLapRhsHsContent_perAlpha
      (I := I) (M := M) g r s k w.1 w.2.1 w.2.2
  choose Bfun hBfun_nn hBfun using hperα
  set actF : Finset M := chartAtlasPOU_activeFinset I M with hactF_def
  refine ⟨∑ α ∈ actF, ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α, Idx, Jdx⟩,
    Finset.sum_nonneg (fun α _ => Finset.sum_nonneg (fun Idx _ =>
      Finset.sum_nonneg (fun Jdx _ => hBfun_nn ⟨α, Idx, Jdx⟩))), ?_⟩
  intro T α Idx Jdx j hj y hyK
  by_cases hα : α ∈ actF
  · -- Active chart: dominate `Bfun ⟨α, Idx, Jdx⟩` by the finite nonnegative sum.
    have hBle : Bfun ⟨α, Idx, Jdx⟩ ≤
        ∑ α' ∈ actF, ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α', Idx', Jdx'⟩ := by
      have h_inner : Bfun ⟨α, Idx, Jdx⟩ ≤
          ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α, Idx, Jdx'⟩ :=
        Finset.single_le_sum (f := fun Jdx' => Bfun ⟨α, Idx, Jdx'⟩)
          (fun Jdx' _ => hBfun_nn ⟨α, Idx, Jdx'⟩) (Finset.mem_univ Jdx)
      have h_mid : (∑ Jdx' : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α, Idx, Jdx'⟩) ≤
          ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α, Idx', Jdx'⟩ :=
        Finset.single_le_sum
          (f := fun Idx' => ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α, Idx', Jdx'⟩)
          (fun Idx' _ => Finset.sum_nonneg (fun Jdx' _ => hBfun_nn ⟨α, Idx', Jdx'⟩))
          (Finset.mem_univ Idx)
      have h_outer : (∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α, Idx', Jdx'⟩) ≤
          ∑ α' ∈ actF, ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α', Idx', Jdx'⟩ :=
        Finset.single_le_sum
          (f := fun α' => ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α', Idx', Jdx'⟩)
          (fun α' _ => Finset.sum_nonneg (fun Idx' _ =>
            Finset.sum_nonneg (fun Jdx' _ => hBfun_nn ⟨α', Idx', Jdx'⟩))) hα
      exact le_trans h_inner (le_trans h_mid h_outer)
    have hpt := hBfun ⟨α, Idx, Jdx⟩ T j hj y hyK
    refine le_trans hpt ?_
    exact mul_le_mul_of_nonneg_right hBle
      (rawConnLapRhsHsContent_nonneg (I := I) (M := M) g r s k T α y)
  · -- Inactive chart: the kernel is empty, so the bound is vacuous at `y`.
    exfalso
    have hρ0 : ∀ x : M, ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
      chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
    have h_tsupp_empty : tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = ∅ := by
      rw [tsupport, Function.support]
      simp only [hρ0, ne_eq, not_true_eq_false, Set.setOf_false, closure_empty]
    have hyK' : y ∈ chartImagePOUTsupport (I := I) (M := M) α := hyK
    rw [chartImagePOUTsupport] at hyK'
    obtain ⟨z, ⟨x, hx_supp, _⟩, _⟩ := hyK'
    rw [h_tsupp_empty] at hx_supp
    exact hx_supp

/-- The pushed partition-of-unity weight `ρ_α` (read at the chart-source preimage of a target point
`y`) vanishes when `y` lies in the chart target but outside the compact kernel
`chartImagePOUTsupport α`. -/
private lemma rawConnLapPouPull_eq_zero_off_kernel (α : M) (y : EuclN)
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hy_off : y ∉ chartImagePOUTsupport (I := I) (M := M) α) :
    (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  by_contra hne
  have hb_supp : b ∈ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    subset_tsupport _ (by simpa [Function.mem_support] using hne)
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have h_round : (extChartAt I α) b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  apply hy_off
  refine ⟨(extChartAt I α) b, ⟨b, hb_supp, rfl⟩, ?_⟩
  rw [h_round]; simp

/-- Continuity of the chart-pushed partition-of-unity weight on the chart target. -/
private lemma rawConnLapPouPullCont (α : M) :
    ContinuousOn
      (fun y : EuclN =>
        (chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hPOU_cont : Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff).continuous
  have hSymmCont : ContinuousOn ((extChartAt I α).symm) (extChartAt I α).target :=
    continuousOn_extChartAt_symm α
  have h_inner : ContinuousOn
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine hSymmCont.comp (toEuclidean (E := E)).symm.continuous.continuousOn ?_
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  exact hPOU_cont.comp_continuousOn h_inner

/-- AEMeasurability of one Hilbert-Schmidt integrand term on the chart-target-restricted volume. -/
private lemma rawConnLapPullIntegrand_aemeasurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))) (l : ℕ)
    (bIdx : Fin l → Fin (Module.finrank ℝ E)) :
    AEMeasurable
      (fun y : EuclN => ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ l (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
      ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_iter_contOn :
      ContinuousOn (iteratedFDeriv ℝ l (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro y hy
    have h_cd : ContDiffAt ℝ ∞ (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y :=
      rawConnLapPull_contDiffAt (I := I) (M := M) g r s T α q.1 q.2 hy
    exact (h_cd.continuousAt_iteratedFDeriv (k := l)
      (by exact_mod_cast le_top)).continuousWithinAt
  have h_eval : ContinuousOn
      (fun y : EuclN => (iteratedFDeriv ℝ l (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y)
          (fun i => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ (bIdx i)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (continuous_eval_const _).comp_continuousOn h_iter_contOn
  have h_real : ContinuousOn
      (fun y : EuclN => ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ l (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (rawConnLapPouPullCont (I := I) (M := M) α).mul (h_eval.abs.pow 2)
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    (h_real.aestronglyMeasurable h_open.measurableSet).aemeasurable

/-- The chart-`α` Hilbert-Schmidt inner double-sum-of-integrals of a tensor `S` equals the integral
of the partition-of-unity-weighted full Hilbert-Schmidt content.  (Tonelli for finite sums.) -/
private lemma rawConnLapSumIntegrals_eq_integral_sum
    (g : SmoothRiemannianMetric I M) (r' s' : ℕ) (S : Integral.L2.SmoothCcTensor g r' s')
    (α : M) (K : ℕ) :
    (∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
          (Fin s' → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range K,
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
              ∂(volume : Measure EuclN)) =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            (∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
                  (Fin s' → Fin (Module.finrank ℝ E)),
              ∑ j ∈ Finset.range K,
                ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                  |(iteratedFDeriv ℝ j
                        (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
        ∂(volume : Measure EuclN) := by
  classical
  have h_bIdx : ∀ (IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
        (Fin s' → Fin (Module.finrank ℝ E))) (j : ℕ),
      (∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ j
                    (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
          ∂(volume : Measure EuclN)) =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ j
                    (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
        ∂(volume : Measure EuclN) := by
    intro IJ j
    rw [MeasureTheory.lintegral_finset_sum' _
      (fun bIdx _ => rawConnLapPullIntegrand_aemeasurable (I := I) (M := M) g r' s' S α IJ j bIdx)]
  have h_j : ∀ (IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
        (Fin s' → Fin (Module.finrank ℝ E))),
      (∑ j ∈ Finset.range K,
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
          ∂(volume : Measure EuclN)) =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ j ∈ Finset.range K,
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
        ∂(volume : Measure EuclN) := by
    intro IJ
    have hmeas : ∀ j ∈ Finset.range K,
        AEMeasurable (fun y : EuclN =>
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
          ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
      intro j _
      have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin j → Fin (Module.finrank ℝ E)))
        (fun bIdx (_ : bIdx ∈ Finset.univ) =>
          rawConnLapPullIntegrand_aemeasurable (I := I) (M := M) g r' s' S α IJ j bIdx)
      refine h.congr (Filter.EventuallyEq.of_eq (funext (fun y => ?_)))
      rw [Finset.sum_apply]
    rw [MeasureTheory.lintegral_finset_sum' _ hmeas]
  calc (∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
          (Fin s' → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range K,
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
              ∂(volume : Measure EuclN))
      = ∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
            (Fin s' → Fin (Module.finrank ℝ E)),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ j ∈ Finset.range K,
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
            ∂(volume : Measure EuclN) := by
        refine Finset.sum_congr rfl (fun IJ _ => ?_)
        rw [← h_j IJ]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← h_bIdx IJ j]
    _ = ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
              (Fin s' → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range K,
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
          ∂(volume : Measure EuclN) := by
        have hmeas2 : ∀ IJ ∈ (Finset.univ : Finset ((Fin r' → Fin (Module.finrank ℝ E)) ×
            (Fin s' → Fin (Module.finrank ℝ E)))),
            AEMeasurable (fun y : EuclN =>
              ∑ j ∈ Finset.range K,
                ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                      |(iteratedFDeriv ℝ j
                            (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                          (fun i => EuclideanSpace.basisFun
                            (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
              ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
          intro IJ _
          have h := Finset.aemeasurable_sum (Finset.range K)
            (fun j (_ : j ∈ Finset.range K) =>
              (Finset.aemeasurable_sum
                (Finset.univ : Finset (Fin j → Fin (Module.finrank ℝ E)))
                (fun bIdx (_ : bIdx ∈ Finset.univ) =>
                  rawConnLapPullIntegrand_aemeasurable
                    (I := I) (M := M) g r' s' S α IJ j bIdx)).congr
                (Filter.EventuallyEq.of_eq (funext (fun y => by rw [Finset.sum_apply]))))
          refine h.congr (Filter.EventuallyEq.of_eq (funext (fun y => ?_)))
          rw [Finset.sum_apply]
        rw [MeasureTheory.lintegral_finset_sum' _ hmeas2]
    _ = ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              (∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
                    (Fin s' → Fin (Module.finrank ℝ E)),
                ∑ j ∈ Finset.range K,
                  ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                    |(iteratedFDeriv ℝ j
                          (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
          ∂(volume : Measure EuclN) := by
        refine setLIntegral_congr_fun
          (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet (fun y _ => ?_)
        set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) with hρ_def
        have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α _
        rw [Finset.mul_sum,
          ENNReal.ofReal_sum_of_nonneg
            (fun IJ _ => mul_nonneg hρ_nn (Finset.sum_nonneg
              (fun j _ => Finset.sum_nonneg (fun bIdx _ => sq_nonneg _))))]
        refine Finset.sum_congr rfl (fun IJ _ => ?_)
        rw [Finset.mul_sum,
          ENNReal.ofReal_sum_of_nonneg
            (fun j _ => mul_nonneg hρ_nn (Finset.sum_nonneg (fun bIdx _ => sq_nonneg _)))]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum,
          ENNReal.ofReal_sum_of_nonneg (fun bIdx _ => mul_nonneg hρ_nn (sq_nonneg _))]

/-- **The per-chart pointwise integrand bound.** For `y` in the chart target, the
partition-of-unity-weighted full Hilbert-Schmidt content (over all components, orders `≤ 2k`, and
basis tuples) of the chart-pulled `Δ_∇ T` component is bounded by `Ccomb · ρ_α ·
rawConnLapRhsHsContent`, where `Ccomb = (#pairs) · (2k + 1) · n^{2k} · B` and the right side is the
order-`(k + 1)` Hilbert-Schmidt content of `T`. -/
private lemma rawConnLap_pointwise_integrand_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (j : ℕ), j ≤ 2 * k →
        ∀ z ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ j
              (rawConnLapPull (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) z‖ ^ 2 ≤
            B * rawConnLapRhsHsContent (I := I) (M := M) g r s k T α z)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
              |(iteratedFDeriv ℝ j
                    (rawConnLapPull (I := I) (M := M) g r s
                      (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2) y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2) ≤
      ((Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E))) : ℝ) * ((2 * k + 1 : ℕ) : ℝ) *
          ((Module.finrank ℝ E : ℝ) ^ (2 * k)) * B) *
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y) := by
  classical
  set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) with hρ_def
  have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α _
  set R : ℝ := rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y with hR_def
  have hR_nn : 0 ≤ R := rawConnLapRhsHsContent_nonneg (I := I) (M := M) g r s k T α y
  set Ccomb : ℝ := (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) : ℝ) * ((2 * k + 1 : ℕ) : ℝ) *
      ((Module.finrank ℝ E : ℝ) ^ (2 * k)) * B with hCcomb_def
  set LHSsum : ℝ := ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * k + 1),
        ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          |(iteratedFDeriv ℝ j
                (rawConnLapPull (I := I) (M := M) g r s
                  (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2 with hLHSsum_def
  change ρ * LHSsum ≤ Ccomb * (ρ * R)
  by_cases hyK : y ∈ chartImagePOUTsupport (I := I) (M := M) α
  · -- Per-component, per-order basis-sum bound from the pointwise primitive.
    have h_perIJorder : ∀ (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E))) (j : ℕ), j ≤ 2 * k →
        (∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          |(iteratedFDeriv ℝ j
                (rawConnLapPull (I := I) (M := M) g r s
                  (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2) ≤
          ((Module.finrank ℝ E : ℝ) ^ (2 * k)) * (B * R) := by
      intro IJ j hj
      set F : EuclN → ℝ := rawConnLapPull (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2 with hF_def
      set Fop : ℝ := ‖iteratedFDeriv ℝ j F y‖ with hFop_def
      have hFop_sq_le : Fop ^ 2 ≤ B * R := hB IJ.1 IJ.2 j hj y hyK
      have h_eval_le : ∀ bIdx : Fin j → Fin (Module.finrank ℝ E),
          |(iteratedFDeriv ℝ j F y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2 ≤ Fop ^ 2 := by
        intro bIdx
        have h_le : |(iteratedFDeriv ℝ j F y)
            (fun i => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ≤ Fop := by
          have h := (iteratedFDeriv ℝ j F y).le_opNorm
            (fun i => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ (bIdx i))
          have hprod : (∏ i : Fin j,
              ‖EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ (bIdx i)‖) = 1 := by
            refine Finset.prod_eq_one (fun i _ => ?_)
            rw [EuclideanSpace.basisFun_apply, PiLp.norm_single]; simp
          rw [hprod, mul_one] at h
          rw [← Real.norm_eq_abs]; exact h
        exact pow_le_pow_left₀ (abs_nonneg _) h_le 2
      have h_card : (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ) =
          (Module.finrank ℝ E : ℝ) ^ j := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
      calc (∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            |(iteratedFDeriv ℝ j F y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
          ≤ ∑ _bIdx : Fin j → Fin (Module.finrank ℝ E), Fop ^ 2 :=
            Finset.sum_le_sum (fun bIdx _ => h_eval_le bIdx)
        _ = (Module.finrank ℝ E : ℝ) ^ j * Fop ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h_card]
        _ ≤ (Module.finrank ℝ E : ℝ) ^ j * (B * R) :=
            mul_le_mul_of_nonneg_left hFop_sq_le (by positivity)
        _ ≤ ((Module.finrank ℝ E : ℝ) ^ (2 * k)) * (B * R) := by
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg hB_nn hR_nn)
            have hn1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
              have : 1 ≤ Module.finrank ℝ E :=
                Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E))
              exact_mod_cast this
            exact pow_le_pow_right₀ hn1 hj
    have h_LHSsum_le : LHSsum ≤ Ccomb * R := by
      have h_perIJ : ∀ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          (∑ j ∈ Finset.range (2 * k + 1),
            ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
              |(iteratedFDeriv ℝ j
                    (rawConnLapPull (I := I) (M := M) g r s
                      (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2) y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2) ≤
          ((2 * k + 1 : ℕ) : ℝ) * (((Module.finrank ℝ E : ℝ) ^ (2 * k)) * (B * R)) := by
        intro IJ
        calc (∑ j ∈ Finset.range (2 * k + 1),
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                |(iteratedFDeriv ℝ j
                      (rawConnLapPull (I := I) (M := M) g r s
                        (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
            ≤ ∑ _j ∈ Finset.range (2 * k + 1),
                ((Module.finrank ℝ E : ℝ) ^ (2 * k)) * (B * R) := by
              refine Finset.sum_le_sum (fun j hj => ?_)
              exact h_perIJorder IJ j (by have := Finset.mem_range.mp hj; omega)
          _ = ((2 * k + 1 : ℕ) : ℝ) * (((Module.finrank ℝ E : ℝ) ^ (2 * k)) * (B * R)) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      calc LHSsum
          ≤ ∑ _IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
              ((2 * k + 1 : ℕ) : ℝ) * (((Module.finrank ℝ E : ℝ) ^ (2 * k)) * (B * R)) :=
            Finset.sum_le_sum (fun IJ _ => h_perIJ IJ)
        _ = Ccomb * R := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hCcomb_def]
            ring
    calc ρ * LHSsum ≤ ρ * (Ccomb * R) := mul_le_mul_of_nonneg_left h_LHSsum_le hρ_nn
      _ = Ccomb * (ρ * R) := by ring
  · have hρ0 : ρ = 0 :=
      rawConnLapPouPull_eq_zero_off_kernel (I := I) (M := M) α y hy hyK
    rw [hρ0]; simp

/-- **The per-chart inner-sum bound** assembled from the pointwise integrand bound: integrating the
pointwise bound over the chart target (Tonelli for finite sums + monotone `lintegral`), turning the
chart-`α` order-`k` inner sum of `Δ_∇ T` into `ofReal Ccomb` times the chart-`α` order-`(k + 1)`
inner sum of `T`.  On inactive charts the partition of unity vanishes, killing the left side. -/
private lemma rawConnLap_per_alpha_inner_bound
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ (T' : Integral.L2.SmoothCcTensor g r s) (α' : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (j : ℕ), j ≤ 2 * k →
        ∀ z ∈ chartImagePOUTsupport (I := I) (M := M) α',
          ‖iteratedFDeriv ℝ j
              (rawConnLapPull (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T') α' Idx Jdx) z‖ ^ 2 ≤
            B * rawConnLapRhsHsContent (I := I) (M := M) g r s k T' α' z)
    (Ccomb : ℝ)
    (hCcomb_def : Ccomb = (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E))) : ℝ) * ((2 * k + 1 : ℕ) : ℝ) *
        ((Module.finrank ℝ E : ℝ) ^ (2 * k)) * B)
    {lhsInner rhsInner : ℝ≥0∞}
    (hlhsInner_def : lhsInner =
      ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * k + 1),
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s
                            (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2
                          ∘ (extChartAt I α).symm
                          ∘ (toEuclidean (E := E)).symm)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
              ∂(volume : Measure EuclN))
    (hrhsInner_def : rhsInner =
      ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * (k + 1) + 1),
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                          ∘ (extChartAt I α).symm
                          ∘ (toEuclidean (E := E)).symm)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
              ∂(volume : Measure EuclN)) :
    lhsInner ≤ ENNReal.ofReal Ccomb * rhsInner := by
  classical
  subst hlhsInner_def hrhsInner_def
  have hCcomb_nn : 0 ≤ Ccomb := by rw [hCcomb_def]; positivity
  simp only [rawConnLapPull_eq (I := I) (M := M)]
  rw [rawConnLapSumIntegrals_eq_integral_sum (I := I) (M := M) g r s
    (rawTensorConnLapSmooth (I := I) g r s T) α (2 * k + 1)]
  rw [rawConnLapSumIntegrals_eq_integral_sum (I := I) (M := M) g r s T α (2 * (k + 1) + 1)]
  rw [show (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * (k + 1) + 1),
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                |(iteratedFDeriv ℝ j
                      (rawConnLapPull (I := I) (M := M) g r s T α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
        ∂(volume : Measure EuclN)) =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y)
        ∂(volume : Measure EuclN) from rfl]
  rw [← MeasureTheory.lintegral_const_mul' _ _
    (ENNReal.ofReal_ne_top (r := Ccomb))]
  refine setLIntegral_mono_ae'
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    (Filter.Eventually.of_forall (fun y hy => ?_))
  have hpt := rawConnLap_pointwise_integrand_le (I := I) (M := M) g r s k T α B hB_nn
    (fun Idx Jdx j hj z hz => hB T α Idx Jdx j hj z hz) hy
  rw [← hCcomb_def] at hpt
  have h_rhs_nn : 0 ≤ ((chartAtlasPOU I M α : M → ℝ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y :=
    mul_nonneg ((chartAtlasPOU I M).nonneg α _)
      (rawConnLapRhsHsContent_nonneg (I := I) (M := M) g r s k T α y)
  rw [← ENNReal.ofReal_mul hCcomb_nn]
  exact ENNReal.ofReal_le_ofReal hpt

/-- **The per-chart inner-sum order-drop for the rough connection Laplacian (the genuine atomic
analytic primitive).**

For a closed Riemannian manifold and ranks `(r, s)`, there is a non-negative constant `C` such
that, for every smooth compactly-supported `(r, s)`-tensor section `T` and every chart base point
`α : M`, the chart-`α` order-`k` Hilbert-Schmidt partition-of-unity-weighted summand of
`Δ_∇ T = rawTensorConnLapSmooth g r s T` is bounded by `ofReal C` times the chart-`α`
order-`(k + 1)` summand of `T`:
```
∑_{IJ} ∑_{j ≤ 2k} ∑_{bIdx} ∫_{ChTE α} ρ_α · |D^j (raw_{IJ}(Δ_∇ T))(bIdx)|²
  ≤ ofReal C · ∑_{IJ} ∑_{j ≤ 2(k+1)} ∑_{bIdx} ∫_{ChTE α} ρ_α · |D^j (raw_{IJ}(T))(bIdx)|² .
```
The constant `C` is uniform in `(T, α)`.

This is the genuine analytic single-step rough-Laplacian chart-Sobolev order-dropping content,
localised per chart.  The rough Laplacian `Δ_∇` is the frame trace of the second covariant
derivative (`rawTensorConnLap_eq_frame_trace_secondCovDeriv`); in chart-Euclidean coordinates its
raw `(Idx, Jdx)`-component is a finite linear combination of *second* Euclidean partials of the raw
components of `T` with smooth (volume-weighted inverse-Gram) coefficients plus a lower-order
correction (`tensorChartComponentRaw_rawTensorConnLap_eq_chart_α_coord_formula`).  An order-`j`
(`j ≤ 2k`) Fréchet derivative of such a component is therefore dominated by order-`(j + 2) ≤
2(k + 1)` Fréchet derivatives of the raw components of `T` (the second-order operator costs exactly
two Fréchet, hence one `tensorPouSobolevHsNorm`-order); the smooth coefficients are uniformly bounded
on the compact chart image of the partition-of-unity support.  This is the exact rough-Laplacian
analogue of the per-chart bound underlying `exists_covGrad_tensorPouSobolevHsNorm_le`, tight at `+1`
order.

It is assembled — sorry-free — from the genuine pointwise second-order elliptic-boundedness primitive
`exists_rawConnLapComp_iteratedFDeriv_norm_sq_le_rawConnLapRhsHsContent` (the only remaining `sorry`
in this chart-port): that primitive states that, on the compact chart image of the
partition-of-unity support, every order-`j` (`j ≤ 2k`) Fréchet derivative operator norm of the
chart-pulled raw `(Idx, Jdx)`-component of `Δ_∇ T` is square-bounded by a `T`-uniform constant times
the order-`(k + 1)` Hilbert-Schmidt content of the raw components of `T`.  Squaring the basis
evaluations, summing over the basis tuples / Fréchet orders / component multi-index pairs, weighting
by the partition of unity (which vanishes off the chart image of its support, by
`rawConnLapPouPull_eq_zero_off_kernel`), and integrating against the chart-Euclidean volume measure
(Tonelli for finite sums, `rawConnLapSumIntegrals_eq_integral_sum`) turns the pointwise bound into
the stated chart-`α` inner-sum inequality.  It carries no spectral nonlinearity and no Weyl
dependence. -/
theorem exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le_perChart
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s) (α : M),
        (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * k + 1),
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                      |(iteratedFDeriv ℝ j
                            (tensorChartComponentRaw (I := I) (M := M) g r s
                                (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2
                              ∘ (extChartAt I α).symm
                              ∘ (toEuclidean (E := E)).symm)
                            y)
                          (fun i => EuclideanSpace.basisFun
                            (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
                  ∂(volume : Measure EuclN)) ≤
          ENNReal.ofReal C *
            (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E)),
              ∑ j ∈ Finset.range (2 * (k + 1) + 1),
                ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                  ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                    ENNReal.ofReal
                      (((chartAtlasPOU I M α : M → ℝ)
                          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                        |(iteratedFDeriv ℝ j
                              (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                                ∘ (extChartAt I α).symm
                                ∘ (toEuclidean (E := E)).symm)
                              y)
                            (fun i => EuclideanSpace.basisFun
                              (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
                    ∂(volume : Measure EuclN)) := by
  classical
  obtain ⟨B, hB_nn, hB⟩ :=
    exists_rawConnLapComp_iteratedFDeriv_norm_sq_le_rawConnLapRhsHsContent
      (I := I) (M := M) g r s k
  refine ⟨(Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) : ℝ) * ((2 * k + 1 : ℕ) : ℝ) *
      ((Module.finrank ℝ E : ℝ) ^ (2 * k)) * B, by positivity, fun T α => ?_⟩
  refine rawConnLap_per_alpha_inner_bound (I := I) (M := M) g r s k T α B hB_nn hB _ rfl ?_ ?_
  · rfl
  · rfl

/-- **The tight single-step order-dropping `ℝ≥0∞` chart-Sobolev norm bound for the rough
connection Laplacian (the genuine analytic primitive).**

For a closed Riemannian manifold and ranks `(r, s)`, there is a non-negative constant `C` such
that for every smooth compactly-supported `(r, s)`-tensor section `T`,
```
tensorPouSobolevHsNorm g k (Δ_∇ T) ≤ ENNReal.ofReal C · tensorPouSobolevHsNorm g (k + 1) T ,
```
where `Δ_∇ = rawTensorConnLapSmooth g r s`.  This is the `ℝ≥0∞`-level (`tensorPouSobolevHsNorm`)
form of the tight single-step bound: the rough Laplacian is the frame trace of the second
covariant derivative (`rawTensorConnLap_eq_frame_trace_secondCovDeriv`), hence a single
second-order operator `H^{2(k+1)} → H^{2k}`, losing exactly **one** `toHs`-order.  It is the
rough-Laplacian counterpart of `exists_covGrad_tensorPouSobolevHsNorm_le`, tight at `+1` order.

It is assembled from the per-chart order-drop
`exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le_perChart`: unfolding both
`tensorPouSobolevHsNorm`s via `tensorPouSobolevHsNorm_eq`, the per-chart inner-summand bound is
summed over the chart base points (`ENNReal.tsum_le_tsum` and `ENNReal.tsum_mul_left`), and the
outer `^(1/2)` is distributed (`ENNReal.mul_rpow_of_nonneg`), turning `ofReal C` into
`ofReal (√C)`.  The completion-norm forms `exists_rawConnLapSmooth_toHs_le_toHs_succ` and
`exists_rawConnLapIter_toHs_le_toHs` are proved on top of it via `tensorPouSobolevHilbert_norm_eq`. -/
theorem exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g r s,
        tensorPouSobolevHsNorm (I := I) (M := M) g k
            (rawTensorConnLapSmooth (I := I) g r s T) ≤
          ENNReal.ofReal C *
            tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le_perChart (I := I) (M := M) g r s k
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun T => ?_⟩
  rw [tensorPouSobolevHsNorm_eq, tensorPouSobolevHsNorm_eq]
  set lhsInner : M → ℝ≥0∞ := fun α =>
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * k + 1),
        ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s
                          (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
            ∂(volume : Measure EuclN) with hlhsInner_def
  set rhsInner : M → ℝ≥0∞ := fun α =>
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * (k + 1) + 1),
        ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
            ∂(volume : Measure EuclN) with hrhsInner_def
  have h_main : (∑' α : M, lhsInner α) ≤ ENNReal.ofReal C * ∑' α : M, rhsInner α := by
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum (fun α => ?_)
    rw [hlhsInner_def, hrhsInner_def]
    exact hC T α
  have h_rpow : (∑' α : M, lhsInner α) ^ (1 / 2 : ℝ) ≤
      (ENNReal.ofReal C * ∑' α : M, rhsInner α) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow h_main (by norm_num)
  calc (∑' α : M, lhsInner α) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal C * ∑' α : M, rhsInner α) ^ (1 / 2 : ℝ) := h_rpow
    _ = ENNReal.ofReal (Real.sqrt C) * (∑' α : M, rhsInner α) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        congr 1
        rw [ENNReal.ofReal_rpow_of_nonneg hC_nn (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ← Real.sqrt_eq_rpow]

end RawConnLapOrderDrop

/-- **The tight single-step order-dropping completion-norm bound for the rough connection
Laplacian (the genuine atomic elliptic-boundedness primitive).**

For a closed Riemannian manifold and an order `k`, there is a non-negative constant `C` such
that for every smooth compactly-supported `(0, 2)`-tensor section `T`,
```
‖(Δ_∇ T).toHs k‖ ≤ C · ‖T.toHs (k + 1)‖ ,
```
where `Δ_∇ = rawTensorConnLapSmooth g 0 2`.  This is the intrinsic `H^{2k}(Δ_∇ T) ≤
C · H^{2(k+1)}(T)` order-dropping inequality: the rough Laplacian is the frame trace of the
second covariant derivative (`rawTensorConnLap_eq_frame_trace_secondCovDeriv`), hence a *single*
second-order operator, so it loses exactly **one** `toHs`-order (`= 2` derivatives) — the tight
count, as opposed to the `+2` a naive `covGrad ∘ covGrad` composition would charge.  It is proved
on top of the `ℝ≥0∞`-level primitive `exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le` via
`tensorPouSobolevHilbert_norm_eq`, exactly as `covGrad_toHs_norm_le` is built from
`exists_covGrad_tensorPouSobolevHsNorm_le`. -/
theorem exists_rawConnLapSmooth_toHs_le_toHs_succ
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g 0 2,
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
            (rawTensorConnLapSmooth (I := I) g 0 2 T)‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (k + 1) T‖ := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le (I := I) (M := M) g 0 2 k
  refine ⟨C, hC_nn, fun T => ?_⟩
  rw [tensorPouSobolevHilbert_norm_eq, tensorPouSobolevHilbert_norm_eq]
  have hle := hC T
  have h_rhs_ne_top :
      ENNReal.ofReal C *
          tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g (k + 1) T).ne
  calc (tensorPouSobolevHsNorm (I := I) (M := M) g k
          (rawTensorConnLapSmooth (I := I) g 0 2 T)).toReal
      ≤ (ENNReal.ofReal C *
          tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T).toReal :=
        ENNReal.toReal_mono h_rhs_ne_top hle
    _ = (ENNReal.ofReal C).toReal *
          (tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T).toReal := by
        rw [ENNReal.toReal_mul]
    _ = C * (tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T).toReal := by
        rw [ENNReal.toReal_ofReal hC_nn]

/-- **The iterated order-dropping completion-norm bound for the rough connection Laplacian.**

For each iteration count `i` and each order `k` there is a non-negative constant `C` such that
for every smooth compactly-supported `(0, 2)`-tensor section `T`,
```
‖(Δ_∇^i T).toHs k‖ ≤ C · ‖T.toHs (k + i)‖ ,
```
where `Δ_∇^i = rawTensorConnLapIter g 0 2 i`.  The proof iterates the tight single-step bound
`exists_rawConnLapSmooth_toHs_le_toHs_succ` exactly `i` times (peeling one `Δ_∇` at each step
and raising the inner order by one), the constant being the product of the single-step
constants.  This is the rough-Laplacian mirror of `iteratedCovGrad_toHs_norm_le`. -/
theorem exists_rawConnLapIter_toHs_le_toHs
    (g : SmoothRiemannianMetric I M) (i k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g 0 2),
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
            (rawTensorConnLapIter (I := I) g 0 2 i T)‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (k + i) T‖ := by
  induction i generalizing k with
  | zero =>
      refine ⟨1, zero_le_one, fun T => ?_⟩
      simp only [rawTensorConnLapIter_zero, Nat.add_zero, one_mul, le_refl]
  | succ i ih =>
      obtain ⟨Ci, hCi_nn, hCi⟩ := ih (k + 1)
      obtain ⟨C1, hC1_nn, hC1⟩ := exists_rawConnLapSmooth_toHs_le_toHs_succ (I := I) g k
      refine ⟨C1 * Ci, mul_nonneg hC1_nn hCi_nn, fun T => ?_⟩
      -- One peel: `Δ_∇^{i+1} T = Δ_∇ (Δ_∇^i T)`, then single-step at order `k` and `ih` at
      -- order `k+1`.
      have hpeel : rawTensorConnLapIter (I := I) g 0 2 (i + 1) T
          = rawTensorConnLapSmooth (I := I) g 0 2 (rawTensorConnLapIter (I := I) g 0 2 i T) := by
        rw [rawTensorConnLapIter_succ]
      rw [hpeel]
      have hstep := hC1 (rawTensorConnLapIter (I := I) g 0 2 i T)
      have hih := hCi T
      have hord : k + 1 + i = k + (i + 1) := by ring
      rw [hord] at hih
      refine le_trans hstep ?_
      calc C1 * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (k + 1)
              (rawTensorConnLapIter (I := I) g 0 2 i T)‖
          ≤ C1 * (Ci * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2)
              (k + (i + 1)) T‖) := mul_le_mul_of_nonneg_left hih hC1_nn
        _ = C1 * Ci * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2)
              (k + (i + 1)) T‖ := by ring

/-- **Monotonicity of the order-`k` chart-Sobolev completion norm in the order `k`.**

For `m ≤ n`, the order-`m` chart-Sobolev (`toHs`) norm is dominated by the order-`n` one:
`‖T.toHs m‖ ≤ ‖T.toHs n‖`.  This is the completion-norm reflection of the monotonicity
`tensorPouSobolevHsNorm_le_succ` of the partition-of-unity chart-Sobolev `ℝ≥0∞`-norm in the
order, transported through `tensorPouSobolevHilbert_norm_eq`. -/
theorem toHs_norm_mono (g : SmoothRiemannianMetric I M) {r s : ℕ} {m n : ℕ} (hmn : m ≤ n)
    (T : Integral.L2.SmoothCcTensor g r s) :
    ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) m T‖ ≤
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) n T‖ := by
  rw [tensorPouSobolevHilbert_norm_eq, tensorPouSobolevHilbert_norm_eq]
  refine ENNReal.toReal_mono (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g n T).ne ?_
  -- Monotone in the order via the successor step, by induction on the gap `n - m`.
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero => simp
  | succ d ihd =>
      refine le_trans ihd ?_
      have : m + d + 1 = m + (d + 1) := by ring
      rw [← this]
      exact tensorPouSobolevHsNorm_le_succ (I := I) (M := M) g (m + d) T

/-- The intrinsic order-`k` chart-Sobolev completion embedding `SmoothCcTensor.toHs` is additive:
`(R₁ + R₂).toHs k = R₁.toHs k + R₂.toHs k`.  Both sides are the completion coercion of the
`SmoothCcTensorHs`-wrapper addition (`UniformSpace.Completion.coe_add`). -/
theorem SmoothCcTensor.toHs_add {g : SmoothRiemannianMetric I M} {r s : ℕ} (k : ℕ)
    (R₁ R₂ : Integral.L2.SmoothCcTensor g r s) :
    IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k (R₁ + R₂)
      = IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k R₁
        + IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k R₂ := by
  unfold IntrinsicSobolev.SmoothCcTensor.toHs
  rw [← UniformSpace.Completion.coe_add]
  rfl

/-- The intrinsic order-`k` chart-Sobolev completion embedding `SmoothCcTensor.toHs` commutes with
subtraction: `(R₁ − R₂).toHs k = R₁.toHs k − R₂.toHs k` (`UniformSpace.Completion.coe_sub`). -/
theorem SmoothCcTensor.toHs_sub {g : SmoothRiemannianMetric I M} {r s : ℕ} (k : ℕ)
    (R₁ R₂ : Integral.L2.SmoothCcTensor g r s) :
    IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k (R₁ - R₂)
      = IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k R₁
        - IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k R₂ := by
  unfold IntrinsicSobolev.SmoothCcTensor.toHs
  rw [← UniformSpace.Completion.coe_sub]
  rfl

section LinearityT2

open DifferentialGeometry.Integral.Connection Bundle Tensor0SBundle

set_option backward.isDefEq.respectTransparency false

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The unconditional smoothness witness of the total-space form of `rawTensorConnLap` applied to a
bundled smooth section `T : SmoothCcTensor g r s`. -/
private lemma rawConnLap_smooth_witness (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (T : Integral.L2.SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => Bundle.TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) y)) :=
  rawTensorConnLap_contMDiff (I := I) g r s
    (fun z : M => T.toSection z) T.toSection.contMDiff_toFun

/-- **Subtraction-linearity of the bundled rough connection Laplacian on `SmoothCcTensor`
(an atomic algebraic linearity primitive).**

`Δ_∇ (T − T') = Δ_∇ T − Δ_∇ T'`, where `Δ_∇ = rawTensorConnLapSmooth g r s`.  The rough
Laplacian is the section-level packaging of the fibrewise-linear pointwise operator
`rawTensorConnLap`, which is additive (`tensorConnLaplacian_of_contMDiff_add`) and `smul`-linear
(`tensorConnLaplacian_of_contMDiff_smul`); hence so is its bundled form.  Writing
`T − T' = T + (-1) • T'` and reducing by `SmoothCcTensor.ext`/`ContMDiffSection.ext` to the
pointwise `.toSection`, the bundled additivity and scalar-homogeneity (mirroring the on-disk
`connLaplacianL2Action.map_add'`/`map_smul'`) assemble the subtraction identity.  This splits off
the linear part of the second-order DeTurck right-hand side. -/
theorem rawTensorConnLapSmooth_sub (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T T' : Integral.L2.SmoothCcTensor g r s) :
    rawTensorConnLapSmooth (I := I) g r s (T - T')
      = rawTensorConnLapSmooth (I := I) g r s T - rawTensorConnLapSmooth (I := I) g r s T' := by
  have hsub_eq : (T - T' : Integral.L2.SmoothCcTensor g r s) = T + (-1 : ℝ) • T' := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  have h_smul : rawTensorConnLapSmooth (I := I) g r s ((-1 : ℝ) • T')
      = (-1 : ℝ) • rawTensorConnLapSmooth (I := I) g r s T' := by
    refine Integral.L2.SmoothCcTensor.ext ?_
    refine ContMDiffSection.ext (fun x => ?_)
    have hsmul := tensorConnLaplacian_of_contMDiff_smul (I := I) g r s (-1 : ℝ) T'
      (rawConnLap_smooth_witness (I := I) g T')
      (rawConnLap_smooth_witness (I := I) g ((-1 : ℝ) • T')) x
    have hLHS : (rawTensorConnLapSmooth (I := I) g r s ((-1 : ℝ) • T')).toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s ((-1 : ℝ) • T')
          (rawConnLap_smooth_witness (I := I) g ((-1 : ℝ) • T'))).toSection x := rfl
    have hRHS : (rawTensorConnLapSmooth (I := I) g r s T').toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s T'
          (rawConnLap_smooth_witness (I := I) g T')).toSection x := rfl
    rw [hLHS, Integral.L2.SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
      Pi.smul_apply, hRHS, hsmul]
  have h_add : rawTensorConnLapSmooth (I := I) g r s (T + (-1 : ℝ) • T')
      = rawTensorConnLapSmooth (I := I) g r s T
        + rawTensorConnLapSmooth (I := I) g r s ((-1 : ℝ) • T') := by
    refine Integral.L2.SmoothCcTensor.ext ?_
    refine ContMDiffSection.ext (fun x => ?_)
    have hsum := tensorConnLaplacian_of_contMDiff_add (I := I) g r s T ((-1 : ℝ) • T')
      (rawConnLap_smooth_witness (I := I) g T)
      (rawConnLap_smooth_witness (I := I) g ((-1 : ℝ) • T'))
      (rawConnLap_smooth_witness (I := I) g (T + (-1 : ℝ) • T')) x
    have hLHS : (rawTensorConnLapSmooth (I := I) g r s (T + (-1 : ℝ) • T')).toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s (T + (-1 : ℝ) • T')
          (rawConnLap_smooth_witness (I := I) g (T + (-1 : ℝ) • T'))).toSection x := rfl
    have hRHS₁ : (rawTensorConnLapSmooth (I := I) g r s T).toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s T
          (rawConnLap_smooth_witness (I := I) g T)).toSection x := rfl
    have hRHS₂ : (rawTensorConnLapSmooth (I := I) g r s ((-1 : ℝ) • T')).toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s ((-1 : ℝ) • T')
          (rawConnLap_smooth_witness (I := I) g ((-1 : ℝ) • T'))).toSection x := rfl
    rw [hLHS, Integral.L2.SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
      Pi.add_apply, hRHS₁, hRHS₂, hsum]
  rw [hsub_eq, h_add, h_smul, neg_one_smul, ← sub_eq_add_neg]

end LinearityT2

section ReverseOrderZeroBridge

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- For a real-valued function the squared `L²` seminorm equals the `lintegral` of the squared
enorm. -/
private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq'
    {β : Type*} [MeasurableSpace β] (μ : Measure β) (f : β → ℝ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

/-- The order-`0` chart-Sobolev summand integral for chart `α` and component `(Idx, Jdx)` equals
the squared chart-Euclidean `L²` norm of the chart-push of the square-root-weighted raw component
`√ρ_α · raw_{IJ}`.  This is the integrand identity underlying the order-`0` reverse comparison. -/
private lemma hsNorm_zero_summand_eq_sq_eLpNorm_chartPushedSqrtPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (basisIdx : Fin 0 → Fin (Module.finrank ℝ E)) :
    (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ 0
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        ∂(volume : Measure EuclN)) =
      (eLpNorm
          (chartPushedRaw I α
            (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx)) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))) ^ 2 := by
  classical
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq']
  rw [← MeasureTheory.lintegral_indicator
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet,
      ← MeasureTheory.lintegral_indicator
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet]
  refine MeasureTheory.lintegral_congr (fun y => ?_)
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
    have hraw_eval :
        (iteratedFDeriv ℝ 0
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ∘ (extChartAt I α).symm
                ∘ (toEuclidean (E := E)).symm) y)
            (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) =
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b := by
      rw [iteratedFDeriv_zero_apply]; rfl
    have hpush :
        chartPushedRaw I α
            (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx) y =
          tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx b :=
      chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy
    rw [hraw_eval, hpush]
    have hw_sq :
        (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 =
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 :=
      tensorChartComponentSqrtPou_sq (I := I) (M := M) g r s T α Idx Jdx b
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2]
    congr 1
    rw [sq_abs, sq_abs, hw_sq]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]

/-- The support of `√ρ_α` equals the support of `ρ_α`. -/
private lemma support_sqrt_pou_eq' (α : M) :
    Function.support
        (fun b : M => Real.sqrt
          (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)) =
      Function.support (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
  ext b
  simp only [Function.mem_support, ne_eq, Real.sqrt_eq_zero']
  constructor
  · intro hb hcontra
    exact hb (by rw [hcontra])
  · intro hb hle
    have hρ_nn : 0 ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b :=
      (chartAtlasPOU I M).nonneg α b
    exact hb (le_antisymm hle hρ_nn)

/-- The square-root-weighted raw component is supported in `tsupport ρ_α`. -/
private lemma tsupport_sqrtPou_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx) ⊆
      tsupport (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
  have h_mul : tsupport (tensorChartComponentSqrtPou (I := I) (M := M)
        g r s T α Idx Jdx) ⊆
      tsupport (fun b : M => Real.sqrt
        (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)) :=
    tsupport_mul_subset_left
      (f := fun b : M => Real.sqrt
        (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b))
      (g := tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)
  refine h_mul.trans ?_
  unfold tsupport
  rw [support_sqrt_pou_eq' (I := I) (M := M) α]

/-- The square-root-weighted raw component is globally continuous on `M`. -/
private lemma continuous_sqrtPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous
      (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx) := by
  classical
  have hSqrt_cont : Continuous
      (fun y : M => Real.sqrt
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y)) :=
    Real.continuous_sqrt.comp
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx_chart : x ∈ (chartAt H α).source
  · have hRaw_on := tensorChartComponentRaw_contMDiffOn_chart_source
      (I := I) (M := M) g r s T α Idx Jdx
    have hRaw_at : ContinuousAt
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx) x :=
      ((hRaw_on.contMDiffAt
        (IsOpen.mem_nhds (chartAt H α).open_source hx_chart)).continuousAt)
    exact (hSqrt_cont.continuousAt).mul hRaw_at
  · have hsupp_sub :
        tsupport (tensorChartComponentSqrtPou (I := I) (M := M)
            g r s T α Idx Jdx) ⊆ (chartAt H α).source :=
      (tsupport_sqrtPou_subset (I := I) (M := M)
        g r s T α Idx Jdx).trans
        (chartAtlasPOU_isSubordinate I M α)
    have hx_notin : x ∉ tsupport (tensorChartComponentSqrtPou (I := I) (M := M)
        g r s T α Idx Jdx) := fun h => hx_chart (hsupp_sub h)
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    have hopen : IsOpen
        (tsupport (tensorChartComponentSqrtPou (I := I) (M := M)
          g r s T α Idx Jdx))ᶜ :=
      isClosed_tsupport _ |>.isOpen_compl
    filter_upwards [hopen.mem_nhds hx_notin] with y hy
    have hy_notsupp : y ∉ Function.support
        (tensorChartComponentSqrtPou (I := I) (M := M)
          g r s T α Idx Jdx) := fun h_in => hy (subset_tsupport _ h_in)
    have hzero : tensorChartComponentSqrtPou (I := I) (M := M)
        g r s T α Idx Jdx y = 0 := by
      by_contra hne; exact hy_notsupp hne
    exact hzero.symm

/-- The square-root-weighted raw component is measurable. -/
private lemma measurable_sqrtPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable
      (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx) :=
  (continuous_sqrtPou (I := I) (M := M) g r s T α Idx Jdx).measurable

/-- **The per-chart-and-component reverse comparison.** For every chart `α` there is a
non-negative constant `C_α` so that for every `T`, `(Idx, Jdx)`, the squared intrinsic metric
`L²` norm of `ρ_α · raw_{IJ}` is bounded by `ofReal C_α` times the order-`0` chart-Sobolev summand
integral (at the `ℝ≥0∞` level). -/
private lemma sq_eLpNorm_scalar_le_const_mul_hsNorm_zero_summand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        (eLpNorm (tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx) 2
              (riemannianVolumeMeasure (I := I) (M := M) g)) ^ 2 ≤
          ENNReal.ofReal C *
            (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ 0
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ
                          ((default : Fin 0 → Fin (Module.finrank ℝ E)) i))| ^ 2)
                ∂(volume : Measure EuclN)) := by
  classical
  set Kα : Set M := tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source := chartAtlasPOU_isSubordinate I M α
  obtain ⟨Cbr, hCbr_pos, hCbr⟩ :=
    eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by decide : (2 : ℝ≥0∞) ≠ ⊤)
  refine ⟨Cbr ^ 2, sq_nonneg _, ?_⟩
  intro T Idx Jdx
  set w : M → ℝ := tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx with hw_def
  have hw_meas : Measurable w :=
    measurable_sqrtPou (I := I) (M := M) g r s T α Idx Jdx
  have hw_supp : tsupport w ⊆ Kα :=
    tsupport_sqrtPou_subset (I := I) (M := M) g r s T α Idx Jdx
  -- Pointwise: `|Scalar = ρ·raw| ≤ |w = √ρ·raw|`, hence `eLpNorm Scalar ≤ eLpNorm w`.
  have h_ptwise : ∀ x : M,
      ‖tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx x‖ ≤ ‖w x‖ := by
    intro x
    have hρ_nn : 0 ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
      (chartAtlasPOU I M).nonneg α x
    have hρ_le_one : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≤ 1 :=
      (chartAtlasPOU I M).le_one α x
    have hsqrt_nn : 0 ≤ Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
      Real.sqrt_nonneg _
    have hsqrt_le_one :
        Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hρ_le_one
    have hρ_eq : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x =
        Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) *
          Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
      (Real.mul_self_sqrt hρ_nn).symm
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [show tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx x =
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x from rfl,
      hw_def, tensorChartComponentSqrtPou_apply]
    rw [abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [abs_of_nonneg hρ_nn, abs_of_nonneg hsqrt_nn]
    calc ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
        = Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) *
            Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := hρ_eq
      _ ≤ 1 * Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
          mul_le_mul_of_nonneg_right hsqrt_le_one hsqrt_nn
      _ = Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := one_mul _
  have h_scalar_le_w :
      eLpNorm (tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        eLpNorm w 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    eLpNorm_mono h_ptwise
  -- Reverse measure bridge for `w`.
  have h_bridge := hCbr (u := w) hw_meas hw_supp
  rw [show DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
        = DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g
      from rfl] at h_bridge
  -- Chain at the `ℝ≥0∞` level.
  set lhsE : ℝ≥0∞ :=
    eLpNorm (tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) with hlhsE_def
  set chE : ℝ≥0∞ :=
    eLpNorm (chartPushedRaw I α w) 2
      ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) with hchE_def
  have h_lhsE_le : lhsE ≤ ENNReal.ofReal Cbr * chE :=
    le_trans h_scalar_le_w h_bridge
  have h_chE_sq :
      chE ^ 2 =
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ 0
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                      ∘ (extChartAt I α).symm
                      ∘ (toEuclidean (E := E)).symm)
                    y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ
                    ((default : Fin 0 → Fin (Module.finrank ℝ E)) i))| ^ 2)
          ∂(volume : Measure EuclN) := by
    rw [hchE_def, hw_def,
      ← hsNorm_zero_summand_eq_sq_eLpNorm_chartPushedSqrtPou
          (I := I) (M := M) g r s T α Idx Jdx (default : Fin 0 → Fin (Module.finrank ℝ E))]
  rw [← h_chE_sq]
  calc lhsE ^ 2 ≤ (ENNReal.ofReal Cbr * chE) ^ 2 := pow_le_pow_left' h_lhsE_le 2
    _ = (ENNReal.ofReal Cbr) ^ 2 * chE ^ 2 := by rw [mul_pow]
    _ = ENNReal.ofReal (Cbr ^ 2) * chE ^ 2 := by rw [← ENNReal.ofReal_pow hCbr_pos.le]

/-- **The reverse measure-bridge comparison at chart-Sobolev order `0` (the genuine atomic
analytic primitive).**

For a closed Riemannian manifold and ranks `(r, s)` there is a non-negative constant `C` such
that for every smooth compactly-supported `(r, s)`-tensor section `T`, the finite double sum,
over the active charts `α ∈ chartAtlasPOU_finset` and the component multi-index pairs
`(Idx, Jdx)`, of the squared intrinsic metric `L²` norm of the partition-of-unity-weighted raw
chart-frame scalar component `tensorChartComponentScalar = ρ_α · raw_{IJ}` is controlled by the
squared order-`0` Hilbert-Schmidt partition-of-unity-weighted chart-Sobolev norm:
```
∑_{α} ∑_{IJ} ((eLpNorm (ρ_α · raw_{IJ}) 2 dVol_g).toReal)²
  ≤ C · (tensorPouSobolevHsNormSq g 0 T).toReal .
```
This is the genuine reverse change-of-variables (intrinsic Riemannian `L²` → chart-Euclidean
`L²`) comparison: the chart-frame raw component `raw_{IJ}` is the chart-`α`-frame coordinate of
the trivialised tensor, the partition-of-unity weight `ρ_α ≤ 1` so `|ρ_α · raw|² ≤ ρ_α · |raw|²`
matches the (first-power) weight of the order-`0` chart-Sobolev integrand, and the reverse
measure bridge `eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset`
on the compact chart image of the partition-of-unity support transfers the intrinsic `L²` norm to
the chart-Euclidean `L²` norm appearing in `tensorPouSobolevHsNormSq g 0`.

It is proved by composing the pointwise weight inequality `|ρ_α · raw|² ≤ ρ_α · |raw|² =
(√ρ_α · raw)²`, the reverse measure bridge, and the order-`0` chart-Sobolev integrand identity:
each chart-component intrinsic `L²` norm squared is dominated by the corresponding order-`0`
chart-Sobolev summand integral, uniformly over the finitely many active charts. -/
theorem exists_sum_componentL2Norm_sq_le_tensorPouSobolevHsNormSq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g r s,
        (∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
            ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                ((MeasureTheory.eLpNorm
                    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
                      (I := I) (M := M) g r s T α Idx Jdx) 2
                    (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
                      (I := I) (M := M) g)).toReal) ^ 2) ≤
          C * (tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T).toReal := by
  classical
  set Sf : Finset M := DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
    (I := I) (M := M) with hSf_def
  -- A uniform constant: the finset-sum of the per-chart reverse-bridge constants.
  choose Cα hCα_nn hCα using fun α (_ : α ∈ Sf) =>
    sq_eLpNorm_scalar_le_const_mul_hsNorm_zero_summand (I := I) (M := M) (E := E) g r s α
  set Cmax : ℝ := ∑ α ∈ Sf.attach, Cα α.val α.property with hCmax_def
  have hCmax_nn : 0 ≤ Cmax :=
    Finset.sum_nonneg (fun α _ => hCα_nn α.val α.property)
  refine ⟨Cmax, hCmax_nn, fun T => ?_⟩
  -- Abbreviation for the order-`0` chart-Sobolev summand at chart `α`, component `(Idx, Jdx)`.
  set summand : M → (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → ℝ≥0∞ :=
    fun α Idx Jdx =>
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ 0
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ
                  ((default : Fin 0 → Fin (Module.finrank ℝ E)) i))| ^ 2)
        ∂(volume : Measure EuclN) with hsummand_def
  set lhsEsq : M → (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → ℝ≥0∞ :=
    fun α Idx Jdx =>
      (MeasureTheory.eLpNorm
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
            (I := I) (M := M) g r s T α Idx Jdx) 2
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
            (I := I) (M := M) g)) ^ 2 with hlhsEsq_def
  -- Per-`(α ∈ Sf, Idx, Jdx)`: `lhsEsq ≤ ofReal Cmax · summand`.
  have h_perchart : ∀ α ∈ Sf, ∀ Idx Jdx,
      lhsEsq α Idx Jdx ≤ ENNReal.ofReal Cmax * summand α Idx Jdx := by
    intro α hα Idx Jdx
    have hCα_le : Cα α hα ≤ Cmax := by
      rw [hCmax_def]
      refine Finset.single_le_sum (f := fun β : Sf => Cα β.val β.property)
        (fun β _ => hCα_nn β.val β.property) (Finset.mem_attach Sf ⟨α, hα⟩)
    calc lhsEsq α Idx Jdx
        ≤ ENNReal.ofReal (Cα α hα) * summand α Idx Jdx := hCα α hα T Idx Jdx
      _ ≤ ENNReal.ofReal Cmax * summand α Idx Jdx := by
          gcongr
  -- Sum over `(Idx, Jdx)` and `α ∈ Sf`.
  have h_sum_le :
      (∑ α ∈ Sf, ∑ Idx, ∑ Jdx, lhsEsq α Idx Jdx) ≤
        ENNReal.ofReal Cmax * ∑ α ∈ Sf, ∑ Idx, ∑ Jdx, summand α Idx Jdx := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun α hα => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun Jdx _ => h_perchart α hα Idx Jdx)
  -- The finset double sum of summands is `≤` the full `tsum` representation, which is
  -- `tensorPouSobolevHsNormSq g 0 T`.
  have h_summand_eq_normSq :
      tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T =
        ∑' α : M, ∑ Idx, ∑ Jdx, summand α Idx Jdx := by
    rw [tensorPouSobolevHsNormSq_eq_inner_sum (I := I) (M := M) g 0 T]
    refine tsum_congr (fun α => ?_)
    rw [Fintype.sum_prod_type
      (f := fun IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)) =>
        ∑ j ∈ Finset.range (2 * 0 + 1),
          ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                          ∘ (extChartAt I α).symm
                          ∘ (toEuclidean (E := E)).symm)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
              ∂(volume : Measure EuclN))]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    refine Finset.sum_congr rfl (fun Jdx _ => ?_)
    rw [show (2 * 0 + 1) = 1 from rfl, Finset.sum_range_one,
      Fintype.sum_subsingleton _ (default : Fin 0 → Fin (Module.finrank ℝ E))]
  have h_finset_le_tsum :
      (∑ α ∈ Sf, ∑ Idx, ∑ Jdx, summand α Idx Jdx) ≤
        ∑' α : M, ∑ Idx, ∑ Jdx, summand α Idx Jdx :=
    ENNReal.sum_le_tsum Sf
  have h_total_le :
      (∑ α ∈ Sf, ∑ Idx, ∑ Jdx, lhsEsq α Idx Jdx) ≤
        ENNReal.ofReal Cmax * tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T := by
    rw [h_summand_eq_normSq]
    refine h_sum_le.trans ?_
    gcongr
  -- Transport to `ℝ` via `.toReal`.
  have h_lhsEsq_ne_top : ∀ α Idx Jdx, lhsEsq α Idx Jdx ≠ ⊤ := by
    intro α Idx Jdx
    rw [hlhsEsq_def]
    refine (ENNReal.pow_ne_top ?_)
    exact (tensorChartComponentScalar_eLpNorm_two_lt_top
      (I := I) (M := M) (E := E) g r s T α Idx Jdx).ne
  have h_normSq_ne_top :
      tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T ≠ ⊤ :=
    (tensorPouSobolevHsNormSq_lt_top (I := I) (M := M) g 0 T).ne
  have h_rhs_ne_top :
      ENNReal.ofReal Cmax * tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top h_normSq_ne_top
  have h_toReal := ENNReal.toReal_mono h_rhs_ne_top h_total_le
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCmax_nn] at h_toReal
  -- Identify the `.toReal` of the finset double sum with the real-valued goal LHS.
  have h_lhs_toReal :
      (∑ α ∈ Sf, ∑ Idx, ∑ Jdx, lhsEsq α Idx Jdx).toReal =
        ∑ α ∈ Sf, ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ((MeasureTheory.eLpNorm
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
                  (I := I) (M := M) g r s T α Idx Jdx) 2
                (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
                  (I := I) (M := M) g)).toReal) ^ 2 := by
    rw [ENNReal.toReal_sum (fun α _ => ?_)]
    · refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [ENNReal.toReal_sum (fun Idx _ => ?_)]
      · refine Finset.sum_congr rfl (fun Idx _ => ?_)
        rw [ENNReal.toReal_sum (fun Jdx _ => h_lhsEsq_ne_top α Idx Jdx)]
        refine Finset.sum_congr rfl (fun Jdx _ => ?_)
        rw [hlhsEsq_def, ENNReal.toReal_pow]
      · exact ENNReal.sum_ne_top.mpr (fun Jdx _ => h_lhsEsq_ne_top α Idx Jdx)
    · exact ENNReal.sum_ne_top.mpr (fun Idx _ =>
        ENNReal.sum_ne_top.mpr (fun Jdx _ => h_lhsEsq_ne_top α Idx Jdx))
  rw [hSf_def] at h_lhs_toReal
  rw [← h_lhs_toReal]
  exact h_toReal

end ReverseOrderZeroBridge

/-- **The reverse order-`0` partition-of-unity completeness comparison (the genuine analytic
primitive).**

For a closed Riemannian manifold and ranks `(r, s)` there is a non-negative constant `C` such
that for every smooth compactly-supported `(r, s)`-tensor section `T`,
```
‖T‖ ≤ C · (tensorPouSobolevHsNorm g 0 T).toReal ,
```
where `‖T‖ = tensorL2Norm g r s T.toFun` is the global metric `L²` (semi-)norm.  This is the
reverse (lower) partition-of-unity completeness bound: the partition of unity sums to one, so the
chart-`H⁰` norm recovers the full metric `L²` norm up to the bounded metric-density factor on the
compact manifold.  It is the exact reverse of the on-disk forward comparison
`tensorPouSobolevHsNorm_zero_le_tensorL2Norm`, and is precisely the seminorm hypothesis `h_norm_le`
left open by `TensorPouSobolevHilbert.toTensorL2_continuousLinearEquiv`.

It is proved by composing the (on-disk, sorry-free) reverse fibre-norm component bound
`tensorL2Norm_sq_le_const_mul_sum_componentL2Norm_sq` (the metric `L²` norm squared is dominated
by the partition-of-unity-weighted chart-component `L²` sum) with the reverse measure-bridge
comparison `exists_sum_componentL2Norm_sq_le_tensorPouSobolevHsNormSq_zero` (that chart-component
`L²` sum is dominated by the order-`0` chart-Sobolev norm squared), then taking square roots.  The
completion-norm form `exists_l2Norm_le_toHs_zero` is proved on top of it. -/
theorem exists_l2Norm_le_tensorPouSobolevHsNorm_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g r s,
        ‖T‖ ≤ C * (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal := by
  classical
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2Norm_sq_le_const_mul_sum_componentL2Norm_sq
      (I := I) (M := M) (E := E) g r s
  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    exists_sum_componentL2Norm_sq_le_tensorPouSobolevHsNormSq_zero (I := I) (M := M) g r s
  refine ⟨Real.sqrt (C₁ * C₂), Real.sqrt_nonneg _, fun T => ?_⟩
  -- `‖T‖² ≤ C₁ · (component sum) ≤ C₁ · C₂ · ‖·‖²_{H⁰_chart}`, then take square roots.
  set L : ℝ := tensorL2Norm (I := I) (M := M) g r s T.toFun with hL_def
  have hL_eq : ‖T‖ = L := (tensorL2Norm_toFun_eq_norm (I := I) (M := M) g T).symm
  set N : ℝ := (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal with hN_def
  have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
  have hNormSq_toReal : (tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T).toReal = N ^ 2 := by
    unfold tensorPouSobolevHsNormSq
    rw [ENNReal.toReal_pow]
  set S : ℝ := ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          ((MeasureTheory.eLpNorm
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
                (I := I) (M := M) g r s T α Idx Jdx) 2
              (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
                (I := I) (M := M) g)).toReal) ^ 2 with hS_def
  have hS_le : L ^ 2 ≤ C₁ * S := hC₁ T
  have hcomp_le : S ≤ C₂ * N ^ 2 := by
    have := hC₂ T
    rwa [hNormSq_toReal] at this
  have hL_nn : 0 ≤ L := tensorL2Norm_nonneg (I := I) (M := M) g r s T.toFun
  have h_sq_le : L ^ 2 ≤ C₁ * C₂ * N ^ 2 := by
    calc L ^ 2 ≤ C₁ * S := hS_le
      _ ≤ C₁ * (C₂ * N ^ 2) := mul_le_mul_of_nonneg_left hcomp_le hC₁_nn
      _ = C₁ * C₂ * N ^ 2 := by ring
  rw [hL_eq]
  calc L = Real.sqrt (L ^ 2) := (Real.sqrt_sq hL_nn).symm
    _ ≤ Real.sqrt (C₁ * C₂ * N ^ 2) := Real.sqrt_le_sqrt h_sq_le
    _ = Real.sqrt (C₁ * C₂) * N := by
        rw [Real.sqrt_mul (mul_nonneg hC₁_nn hC₂_nn), Real.sqrt_sq hN_nn]

/-- **The reverse order-`0` comparison: the global metric `L²` norm is controlled by the
order-`0` partition-of-unity chart-Sobolev completion norm (the genuine atomic comparison
primitive).**

For a closed Riemannian manifold there is a non-negative constant `C` such that for every smooth
compactly-supported `(0, 2)`-tensor section `T`,
```
‖T.toL2‖ ≤ C · ‖T.toHs 0‖ .
```
`‖T.toL2‖ = ‖T‖` is the global metric `L²` (semi-)norm (`norm_toL2`) and `‖T.toHs 0‖` is the
order-`0` partition-of-unity chart-Sobolev completion norm.  This is the reverse of the on-disk
forward comparison `tensorPouSobolevHsNorm_zero_le_tensorL2Norm` (`H⁰_chart ≤ C · L²`): the
partition of unity sums to one, so the chart-`H⁰` norm recovers the full `L²` norm up to the
metric-density factor, bounded on the compact manifold.  It is proved on top of the underlying
seminorm primitive `exists_l2Norm_le_tensorPouSobolevHsNorm_zero` via `norm_toL2` and
`tensorPouSobolevHilbert_norm_eq`. -/
theorem exists_l2Norm_le_toHs_zero
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g 0 2,
        ‖Integral.L2.SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) T‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) 0 T‖ := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_l2Norm_le_tensorPouSobolevHsNorm_zero (I := I) (M := M) g 0 2
  refine ⟨C, hC_nn, fun T => ?_⟩
  rw [Integral.L2.SmoothCcTensor.norm_toL2, tensorPouSobolevHilbert_norm_eq]
  exact hC T

end DifferentialGeometry.PDE.RicciFlow
