import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegOpJetWindows
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SelfLowCapWindows
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindow
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.TameLieCorrJets

/-!
# The two per-arm capped windows of the zero-order self-action integrand

`SelfLowCapWindows.lean` supplies four of the six arm windows that
`selfLow_jet` consumes.  The two remaining ones are the arms whose factors live
in the low-base action module and in the Palatini refold, and they are collected
here so that neither of those two very large modules has to be touched.

* `ricciDACap` — the transferred lower Ricci Palatini arm
  `ricciDALow g₀ g₁ P`.  Both of its factors carry exactly one derivative of the
  state (`dagLowOp` is the covariant derivative of the inverse-metric-difference
  coefficient `connLowOp`, and the second factor is `∇P` itself), so the arm is
  quadratic in `∇P` and is honest only in the capped currency.
* `lieCovCap` — the difference of the DeTurck--Lie covariant-derivative arm and
  its subtracted edge pairing.  `lieCov_residual` collapses the difference to a
  single product whose right factor is the fourth-covariant normal form
  `lieCovR4 = (-(s/2))•lrCurvF T − lrQuadF g₁`; the `s`-factor in front of the
  curvature head is exactly what turns the state `T` into the perturbation
  `P = s•T`, which is what makes that head capped at all.

Everything below is assembled from the calculus of `GradCapArms.lean`; no arm
is re-estimated.  The only new pointwise inputs are `endoAtgw` (the full raised
endomorphism inserted into a slot) and `clAtgw` (the transparent Koszul
coefficient), both obtained from existing radius-free producers.

The final section re-reads the `lieCov` arm in the **marked** currency of
`TameMarkWin.lean`, where the constants are state-free and the deliverable is the
tame `L²` jet bound `lieCovJet` in the shape `ricciAAJet` fixes.  The point is
that the residual carries **no second derivative of the state at all**:
`lrCurvF g₀ T` is the fixed background curvature contracted with `T` itself
(`lrCurvF_unitModel_apply`), so it is linear and order zero, and `lieCovPair` is
a pure double moving trace.  The only quadratic part is `lrQuadF`, so the arm
splits — along the sub-linearity of `appCcRS`, `rsDomDomCongrSection` and
`slotExtendIter` — into an unmarked half handled by `markJet0` and a twice-marked
half handled by `markJet`.
-/

noncomputable section

set_option autoImplicit false
set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.LowBaseInternal
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### The inserted full raised endomorphism -/

set_option linter.unusedSectionVars false in
/-- The slot insertion of the full raised endomorphism splits into the
inverse-metric difference and the frozen identity insertion. -/
private lemma sieSplit (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) :
    slotInsertEndoCc (I := I) (M := M) g₀ s
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁) =
      slotInsertEndoCc (I := I) (M := M) g₀ s (gInvDiffRaisedEndoField (I := I) g₀ g₁) +
        slotInsertEndoCc (I := I) (M := M) g₀ s
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀) := by
  have h := CurvatureCoefficientDifferenceJetTower.fullRaisedEndoField_diff_split
    (I := I) (M := M) g₀ g₁
  have hsub : gInvDiffRaisedEndoField (I := I) g₀ g₁ =
      fullRaisedEndoField (I := I) (M := M) g₀ g₁ -
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
    rw [h]; abel
  rw [hsub, slotInsertEndoCc_sub]
  abel

set_option linter.unusedVariables false in
/-- **Radius-free pointwise grid window for the inserted full raised
endomorphism.**

`|∇ⁱ(slotInsertEndoCc g₀ s (fullRaisedEndoField g₀ g₁))|²(x) ≤ C i · atgw(bP)(i+1)`.

Offset `+1`: the endomorphism is the identity plus the inverse-metric
difference, and the difference costs no derivative of the state.  This is the
generic-`s` sibling of the insertion appearing inside `pureAtgw`. -/
private theorem endoAtgw (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (s : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
              (slotInsertEndoCc (I := I) (M := M) g₀ s
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (i + 1) := by
  classical
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  choose Sid hSid_nn hSid using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀
      (s + 1) ((s + 1) + i)
      (iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g₀ s
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀))))
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => 2 * (fr ^ s * Cb i) + 2 * Sid i, fun i => by
    have h1 : (0 : ℝ) ≤ fr ^ s * Cb i := mul_nonneg (pow_nonneg hfr_nn s) (hCb_nn i)
    have h2 := hSid_nn i
    linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ i x
  have hbnn := gridBase_nn (I := I) (M := M) g₀ P x
  have hone : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (gridBase (I := I) (M := M) g₀ P x) (i + 1) :=
    Combinatorics.one_le_antidiagonalTupleGridWindow _ hbnn (by omega)
  have hWnn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (gridBase (I := I) (M := M) g₀ P x) (i + 1) := le_trans zero_le_one hone
  rw [sieSplit (I := I) (M := M) g₀ g₁ s, iteratedCovGrad_add]
  rw [show ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g₀ s (gInvDiffRaisedEndoField (I := I) g₀ g₁)) +
      iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g₀ s
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x) =
      (iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g₀ s
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x +
        (iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g₀ s
            (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x
      from by rw [SmoothCcTensor.toSection_add]; rfl]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x _ _) ?_
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
      ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g₀ s
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
      (fr ^ s * Cb i) * Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ P x) (i + 1) := by
    have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ s
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) i x
    have h2 := hCb g₁ P htie hδ_le hδ0 hδ i x
    have hgrideq : (∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        Combinatorics.antidiagonalTupleGrid (gridBase (I := I) (M := M) g₀ P x) i := rfl
    rw [hgrideq] at h2
    have hgw : Combinatorics.antidiagonalTupleGrid (gridBase (I := I) (M := M) g₀ P x) i ≤
        Combinatorics.antidiagonalTupleGridWindow (gridBase (I := I) (M := M) g₀ P x) (i + 1) :=
      Combinatorics.antidiagonalTupleGrid_le_window _ hbnn (by omega)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
              (slotInsertEndoCc (I := I) (M := M) g₀ s
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
        ≤ fr ^ s * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) := h1
      _ ≤ fr ^ s * (Cb i * Combinatorics.antidiagonalTupleGrid
            (gridBase (I := I) (M := M) g₀ P x) i) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hfr_nn s)
      _ ≤ fr ^ s * (Cb i * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (i + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgw (hCb_nn i))
            (pow_nonneg hfr_nn s)
      _ = (fr ^ s * Cb i) * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (i + 1) := by ring
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
      ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g₀ s
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x) ≤
      Sid i * Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ P x) (i + 1) :=
    le_trans (hSid i x) (le_mul_of_one_le_right (hSid_nn i) hone)
  nlinarith [hA, hB, hWnn]

/-! ### The transparent Koszul coefficient -/

set_option linter.unusedSectionVars false in
/-- The transparent lowered connection-difference coefficient is the fixed
Koszul factor read through one endomorphism insertion and one slot
permutation.

The Koszul factor itself is `private` to the low-base action module, so it is
abstracted here rather than named: only its existence and its independence of
the moving metric are used. -/
private lemma clSplit (g₀ : SmoothRiemannianMetric I M) :
    ∃ Z : SmoothCcTensor g₀ 3 3, ∀ g₁ : SmoothRiemannianMetric I M,
      connLowOp (I := I) (M := M) g₀ g₁ =
        appCcRS (I := I) (M := M) g₀ 3 3 3 (permCoeff (I := I) (M := M) g₀ lowPerm)
          (appCcRS (I := I) (M := M) g₀ 3 3 3
            (slotInsertEndoCc (I := I) (M := M) g₀ 2
              (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) Z) :=
  ⟨_, fun _ => rfl⟩

set_option linter.unusedVariables false in
/-- **Radius-free pointwise grid window for the transparent lowered
connection-difference coefficient.**

`|∇ⁱ(connLowOp g₀ g₁)|²(x) ≤ C i · atgw(bP)(i+1)`: a fixed permutation
coefficient against the inserted full raised endomorphism against the fixed
Koszul factor, all three at offset `+1`, folded at offsets `(0,0)`. -/
private theorem clAtgw (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + i) x
            ((iteratedCovGrad (I := I) g₀ 3 3 i
              (connLowOp (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (i + 1) := by
  classical
  obtain ⟨Z, hZ⟩ := clSplit (I := I) (M := M) g₀
  obtain ⟨Ce, hCe_nn, hCe⟩ := endoAtgw (I := I) (M := M) g₀ hδ₀ 2
  choose SZ hSZ_nn hSZ using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (3 + i)
      (iteratedCovGrad (I := I) g₀ 3 3 i Z))
  choose SL hSL_nn hSL using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (3 + i)
      (iteratedCovGrad (I := I) g₀ 3 3 i (permCoeff (I := I) (M := M) g₀ lowPerm)))
  set Kin : ℕ → ℝ := foldConst (E := E) 0 0 Ce SZ with hKin_def
  have hKin_nn : ∀ i, 0 ≤ Kin i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hCe_nn hSZ_nn i
  refine ⟨foldConst (E := E) 0 0 SL Kin,
    fun i => foldConst_nn (E := E) (u := 0) (v := 0) hSL_nn hKin_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ i x
  have hconst : ∀ (c : ℕ) (S : ℕ → ℝ), (∀ j, 0 ≤ S j) →
      ∀ (X : SmoothCcTensor g₀ 3 c), (∀ (j : ℕ) (y : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (c + j) y
          ((iteratedCovGrad (I := I) g₀ 3 c j X).toSection y) ≤ S j) →
      ∀ (j : ℕ) (y : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (c + j) y
            ((iteratedCovGrad (I := I) g₀ 3 c j X).toSection y) ≤
          S j * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P y) (j + 0 + 1) := by
    intro c S hS X hX j y
    have hy : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ P y) (j + 0 + 1) :=
      Combinatorics.one_le_antidiagonalTupleGridWindow _
        (gridBase_nn (I := I) (M := M) g₀ P y) (by omega)
    exact le_trans (hX j y) (le_mul_of_one_le_right (hS j) hy)
  have hEw : ∀ (j : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + j) y
          ((iteratedCovGrad (I := I) g₀ 3 3 j
            (slotInsertEndoCc (I := I) (M := M) g₀ 2
              (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection y) ≤
        Ce j * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (j + 0 + 1) := by
    intro j y
    have h := hCe g₁ P htie hδ_le hδ0 hδ j y
    have hidx : j + 0 + 1 = j + 1 := by omega
    rw [hidx]
    exact h
  have hinner := atgwFold (I := I) (M := M) g₀ (p := 3) (a := 3) (b := 3) 0 0
    (slotInsertEndoCc (I := I) (M := M) g₀ 2
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) Z P hCe_nn hSZ_nn hEw
    (hconst 3 SZ hSZ_nn Z (fun j y => hSZ j y))
  have hinner' : ∀ (l : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) y
          ((iteratedCovGrad (I := I) g₀ 3 3 l
            (appCcRS (I := I) (M := M) g₀ 3 3 3
              (slotInsertEndoCc (I := I) (M := M) g₀ 2
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) Z)).toSection y) ≤
        Kin l * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (l + 0 + 1) := by
    intro l y
    have h := hinner l y
    have hidx : l + 0 + 0 + 1 = l + 0 + 1 := by omega
    rw [hidx] at h
    exact h
  have houter := atgwFold (I := I) (M := M) g₀ (p := 3) (a := 3) (b := 3) 0 0
    (permCoeff (I := I) (M := M) g₀ lowPerm)
    (appCcRS (I := I) (M := M) g₀ 3 3 3
      (slotInsertEndoCc (I := I) (M := M) g₀ 2
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) Z) P hSL_nn hKin_nn
    (hconst 3 SL hSL_nn (permCoeff (I := I) (M := M) g₀ lowPerm) (fun j y => hSL j y))
    hinner' i x
  rw [hZ g₁]
  have hidx : i + 0 + 0 + 1 = i + 1 := by omega
  rw [hidx] at houter
  exact houter

/-! ### The Palatini arm -/

set_option linter.unusedVariables false in
/-- **Capped window of the transferred lower Ricci Palatini arm.**

`ricciDALow g₀ g₁ P = daContr g₀ g₁ (dagLowOp g₀ g₁ ⋆ ∇P)`.  `daContr` is a
difference of two contraction monomials, and
`refoldKernelContractionMonomialField_eq_mvPairTraceRefold` factors each
monomial's head as `mvPairTraceOp ⋆ ddc (Ext² (ddc G))` for an ARBITRARY `(0,4)`
argument `G`.  Both factors of `G` carry one derivative of the state, so `G`
itself is quadratic in `∇P`; the capped currency is closed under `appCcRS`, so
the whole tree stays at level `i + 1`. -/
theorem ricciDACap (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ Λ)
        (hP1 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 1 ≤ Λ),
        HasCapWin (I := I) (M := M) g₀ P
          (ricciDALow (I := I) (M := M) g₀ g₁ P) K := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨Ccl, hCcl_nn, hcl⟩ := clAtgw (I := I) (M := M) g₀ hδ₀
  obtain ⟨Ce1, hCe1_nn, hce1⟩ := endoAtgw (I := I) (M := M) g₀ hδ₀ 1
  choose SA hSA_nn hSA using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (4 + i)
      (iteratedCovGrad (I := I) g₀ 4 4 i (permCoeff (I := I) (M := M) g₀ daPermA)))
  choose SM hSM_nn hSM using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (2 + i)
      (iteratedCovGrad (I := I) g₀ 6 2 i (mvPairTraceOp (I := I) (M := M) g₀ g₀)))
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  -- the covariant derivative of the Koszul coefficient, capped
  set KCov : ℕ → ℝ := fun i => Ccl (i + 1) * shiftConst Λ (i + 1) with hKCov_def
  have hKCov_nn : ∀ i, 0 ≤ KCov i := fun i =>
    mul_nonneg (hCcl_nn (i + 1)) (shiftConst_nn hΛ0 _)
  set KDag : ℕ → ℝ := foldConst (E := E) 0 0 SA KCov with hKDag_def
  have hKDag_nn : ∀ i, 0 ≤ KDag i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hSA_nn hKCov_nn i
  set KG : ℕ → ℝ := foldConst (E := E) 0 0 KDag (fun _ => Λ) with hKG_def
  have hKG_nn : ∀ i, 0 ≤ KG i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hKDag_nn (fun _ => hΛ0) i
  set KX : ℕ → ℝ := fun i => fr ^ 2 * KG i with hKX_def
  have hKX_nn : ∀ i, 0 ≤ KX i := fun i => mul_nonneg (pow_nonneg hfr_nn 2) (hKG_nn i)
  set KRK : ℕ → ℝ := foldConst (E := E) 0 0 SM KX with hKRK_def
  have hKRK_nn : ∀ i, 0 ≤ KRK i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hSM_nn hKX_nn i
  set KE1 : ℕ → ℝ := fun i => Ce1 i * shiftConst Λ (i + 1) with hKE1_def
  have hKE1_nn : ∀ i, 0 ≤ KE1 i := fun i =>
    mul_nonneg (hCe1_nn i) (shiftConst_nn hΛ0 _)
  set KMo : ℕ → ℝ := foldConst (E := E) 0 0 KRK KE1 with hKMo_def
  have hKMo_nn : ∀ i, 0 ≤ KMo i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hKRK_nn hKE1_nn i
  refine ⟨fun i => 2 * KMo i + 2 * KMo i, fun i => by have := hKMo_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 hP1
  -- the fixed permutation coefficient and the moving pair trace, state-free
  have hA : HasCapWin (I := I) (M := M) g₀ P
      (permCoeff (I := I) (M := M) g₀ daPermA) SA :=
    capOfBnd (I := I) (M := M) g₀ P _ hSA_nn (fun i x => hSA i x)
  have hM : HasCapWin (I := I) (M := M) g₀ P
      (mvPairTraceOp (I := I) (M := M) g₀ g₀) SM :=
    capOfBnd (I := I) (M := M) g₀ P _ hSM_nn (fun i x => hSM i x)
  -- one derivative of the Koszul coefficient
  have hCov : HasCapWin (I := I) (M := M) g₀ P
      (covGrad (I := I) (M := M) g₀ 3 3 (connLowOp (I := I) (M := M) g₀ g₁)) KCov := by
    refine capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _
      (fun i => hCcl_nn (i + 1)) (fun i y => ?_)
    rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 3 3 i
      (connLowOp (I := I) (M := M) g₀ g₁) y]
    refine le_trans (hcl g₁ P htie hδ_le hδ0 hδ (i + 1) y) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCcl_nn (i + 1))
    exact Combinatorics.antidiagonalTupleGridWindow_mono _
      (gridBase_nn (I := I) (M := M) g₀ P y) (by omega)
  have hDag : HasCapWin (I := I) (M := M) g₀ P
      (dagLowOp (I := I) (M := M) g₀ g₁) KDag :=
    capApp (I := I) (M := M) g₀ P _ _ hSA_nn hKCov_nn hA hCov
  -- the `(0,4)` argument of the contraction monomials
  have hDP : HasCapWin (I := I) (M := M) g₀ P
      (covGrad (I := I) (M := M) g₀ 0 2 P) (fun _ => Λ) :=
    capOfDP (I := I) (M := M) g₀ P hΛ1 hP1
  have hG : HasCapWin (I := I) (M := M) g₀ P
      (appCcRS (I := I) (M := M) g₀ 0 3 4
        (dagLowOp (I := I) (M := M) g₀ g₁)
        (covGrad (I := I) (M := M) g₀ 0 2 P)) KG :=
    capApp (I := I) (M := M) g₀ P _ _ hKDag_nn (fun _ => hΛ0) hDag hDP
  -- the inserted endomorphism of the monomial tail
  have hE1 : HasCapWin (I := I) (M := M) g₀ P
      (slotInsertEndoCc (I := I) (M := M) g₀ 1
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) KE1 := by
    refine capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _ hCe1_nn (fun i y => ?_)
    refine le_trans (hce1 g₁ P htie hδ_le hδ0 hδ i y) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCe1_nn i)
    exact Combinatorics.antidiagonalTupleGridWindow_mono _
      (gridBase_nn (I := I) (M := M) g₀ P y) (by omega)
  -- each contraction monomial
  have hMono : ∀ σ : Equiv.Perm (Fin 4),
      HasCapWin (I := I) (M := M) g₀ P
        (daMono (I := I) (M := M) g₀ g₁
          (appCcRS (I := I) (M := M) g₀ 0 3 4
            (dagLowOp (I := I) (M := M) g₀ g₁)
            (covGrad (I := I) (M := M) g₀ 0 2 P)) σ) KMo := by
    intro σ
    have hRK : HasCapWin (I := I) (M := M) g₀ P
        (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₀
          (appCcRS (I := I) (M := M) g₀ 0 3 4
            (dagLowOp (I := I) (M := M) g₀ g₁)
            (covGrad (I := I) (M := M) g₀ 0 2 P)) σ) KRK := by
      refine capCongr (I := I) (M := M) g₀ P
        (refoldKernelContractionMonomialField_eq_mvPairTraceRefold (I := I) (M := M) g₀ g₀
          (appCcRS (I := I) (M := M) g₀ 0 3 4
            (dagLowOp (I := I) (M := M) g₀ g₁)
            (covGrad (I := I) (M := M) g₀ 0 2 P)) σ) ?_
      exact capApp (I := I) (M := M) g₀ P _ _ hSM_nn hKX_nn hM
        (capDdc (I := I) (M := M) g₀ P sigmaE
          (capIter (I := I) (M := M) g₀ P 2
            (capDdc0 (I := I) (M := M) g₀ P _ hG)))
    exact capApp (I := I) (M := M) g₀ P _ _ hKRK_nn hKE1_nn hRK hE1
  exact capSub (I := I) (M := M) g₀ P (hMono daPermA) (hMono daPermB)

/-! ### The moving pair trace of the covariant-derivative residual -/

set_option linter.unusedVariables false in
/-- **Radius-free pointwise grid window for the moving cometric double trace.**

`|∇ⁱ(pureTrace g₀ g₁ s)|²(x) ≤ C i · atgw(bP)(i+1)`.  Offset `+1`: by
`pureTrace_split` the moving trace is the fixed parallel trace plus one
endomorphism insertion built from the inverse-metric difference, and the
difference costs no derivative of the state.  This is the generic-valence
sibling of `pureAtgw`. -/
private theorem ptAtgw (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (s : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s i
              (pureTrace (I := I) (M := M) g₀ g₁ s)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (i + 1) := by
  classical
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  choose SΦ hSΦ_nn hSΦ using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀
      (s + 2) (s + i)
      (iteratedCovGrad (I := I) g₀ (s + 2) s i (cometricDoubleTraceField (I := I) g₀ s)))
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KW : ℕ → ℝ := fun q => fr ^ (s + 1) * Cb q with hKW_def
  have hKW_nn : ∀ q, 0 ≤ KW q := fun q =>
    mul_nonneg (pow_nonneg hfr_nn (s + 1)) (hCb_nn q)
  refine ⟨fun i => 2 * SΦ i + 2 * foldConst (E := E) 0 0 SΦ KW i,
    fun i => by
      have h1 := hSΦ_nn i
      have h2 := foldConst_nn (E := E) (u := 0) (v := 0) hSΦ_nn hKW_nn i
      linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ i x
  have hbnn := gridBase_nn (I := I) (M := M) g₀ P x
  have hone : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (gridBase (I := I) (M := M) g₀ P x) (i + 1) :=
    Combinatorics.one_le_antidiagonalTupleGridWindow _ hbnn (by omega)
  have hWnn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (gridBase (I := I) (M := M) g₀ P x) (i + 1) := le_trans zero_le_one hone
  have hΦw : ∀ (i' : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i') y
          ((iteratedCovGrad (I := I) g₀ (s + 2) s i'
            (cometricDoubleTraceField (I := I) g₀ s)).toSection y) ≤
        SΦ i' * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (i' + 0 + 1) := by
    intro i' y
    have hy : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ P y) (i' + 0 + 1) :=
      Combinatorics.one_le_antidiagonalTupleGridWindow _
        (gridBase_nn (I := I) (M := M) g₀ P y) (by omega)
    exact le_trans (hSΦ i' y) (le_mul_of_one_le_right (hSΦ_nn i') hy)
  have hWw : ∀ (q : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + q) y
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) q
            (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection y) ≤
        KW q * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (q + 0 + 1) := by
    intro q y
    have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ (s + 1)
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) q y
    have h2 := hCb g₁ P htie hδ_le hδ0 hδ q y
    have hgrideq : (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
          ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) y
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection y)) =
        Combinatorics.antidiagonalTupleGrid (gridBase (I := I) (M := M) g₀ P y) q := rfl
    rw [hgrideq] at h2
    have hgw : Combinatorics.antidiagonalTupleGrid (gridBase (I := I) (M := M) g₀ P y) q ≤
        Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P y) (q + 0 + 1) :=
      Combinatorics.antidiagonalTupleGrid_le_window _
        (gridBase_nn (I := I) (M := M) g₀ P y) (by omega)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + q) y
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) q
              (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection y)
        ≤ fr ^ (s + 1) * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) y
            ((iteratedCovGrad (I := I) g₀ 1 1 q
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection y) := h1
      _ ≤ fr ^ (s + 1) * (Cb q * Combinatorics.antidiagonalTupleGrid
            (gridBase (I := I) (M := M) g₀ P y) q) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hfr_nn (s + 1))
      _ ≤ fr ^ (s + 1) * (Cb q * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P y) (q + 0 + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgw (hCb_nn q))
            (pow_nonneg hfr_nn (s + 1))
      _ = KW q * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P y) (q + 0 + 1) := by rw [hKW_def]; ring
  have hB := atgwFold (I := I) (M := M) g₀ (p := s + 2) (a := s + 2) (b := s) 0 0
    (cometricDoubleTraceField (I := I) g₀ s)
    (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
      (gInvDiffRaisedEndoField (I := I) g₀ g₁)) P hSΦ_nn hKW_nn hΦw hWw i x
  rw [pureTrace_split (I := I) (M := M) g₀ g₁ s, iteratedCovGrad_add]
  rw [show ((iteratedCovGrad (I := I) g₀ (s + 2) s i
        (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))) +
      iteratedCovGrad (I := I) g₀ (s + 2) s i
        (cometricDoubleTraceField (I := I) g₀ s)).toSection x) =
      (iteratedCovGrad (I := I) g₀ (s + 2) s i
          (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
            (cometricDoubleTraceField (I := I) g₀ s)
            (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x +
        (iteratedCovGrad (I := I) g₀ (s + 2) s i
          (cometricDoubleTraceField (I := I) g₀ s)).toSection x
      from by rw [SmoothCcTensor.toSection_add]; rfl]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ (s + 2) (s + i) x _ _) ?_
  have hidx : i + 0 + 0 + 1 = i + 1 := by omega
  rw [hidx] at hB
  have hA := hSΦ i x
  have hAw : SΦ i ≤ SΦ i * Combinatorics.antidiagonalTupleGridWindow
      (gridBase (I := I) (M := M) g₀ P x) (i + 1) :=
    le_mul_of_one_le_right (hSΦ_nn i) hone
  nlinarith [hA, hAw, hB, hWnn]

set_option linter.unusedVariables false in
/-- **Capped window of the pair-cometric contraction of the residual.**

`lieCovPair` is the double moving trace against the quadruple moving trace, so
it costs no derivative of the state at all; both factors enter through
`ptAtgw`. -/
private theorem pairCap (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ Λ)
        (hP1 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 1 ≤ Λ),
        HasCapWin (I := I) (M := M) g₀ P (lieCovPair (I := I) (M := M) g₀ g₁) K := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨C2, hC2_nn, h2⟩ := ptAtgw (I := I) (M := M) g₀ hδ₀ 2
  obtain ⟨C4, hC4_nn, h4⟩ := ptAtgw (I := I) (M := M) g₀ hδ₀ 4
  set K2 : ℕ → ℝ := fun i => C2 i * shiftConst Λ (i + 1) with hK2_def
  set K4 : ℕ → ℝ := fun i => C4 i * shiftConst Λ (i + 1) with hK4_def
  have hK2_nn : ∀ i, 0 ≤ K2 i := fun i => mul_nonneg (hC2_nn i) (shiftConst_nn hΛ0 _)
  have hK4_nn : ∀ i, 0 ≤ K4 i := fun i => mul_nonneg (hC4_nn i) (shiftConst_nn hΛ0 _)
  refine ⟨foldConst (E := E) 0 0 K2 K4,
    fun i => foldConst_nn (E := E) (u := 0) (v := 0) hK2_nn hK4_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 hP1
  have hpt : ∀ (s : ℕ) (C : ℕ → ℝ), (∀ i, 0 ≤ C i) →
      (∀ (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s i
              (pureTrace (I := I) (M := M) g₀ g₁ s)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (i + 1)) →
      HasCapWin (I := I) (M := M) g₀ P (pureTrace (I := I) (M := M) g₀ g₁ s)
        (fun i => C i * shiftConst Λ (i + 1)) := by
    intro s C hC hbd
    refine capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _ hC (fun i y => ?_)
    refine le_trans (hbd i y) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hC i)
    exact Combinatorics.antidiagonalTupleGridWindow_mono _
      (gridBase_nn (I := I) (M := M) g₀ P y) (by omega)
  have hP2 := hpt 2 C2 hC2_nn (fun i x => h2 g₁ P htie hδ_le hδ0 hδ i x)
  have hP4 := hpt 4 C4 hC4_nn (fun i x => h4 g₁ P htie hδ_le hδ0 hδ i x)
  have hpair : lieCovPair (I := I) (M := M) g₀ g₁ =
      appCcRS (I := I) (M := M) g₀ 6 4 2
        (pureTrace (I := I) (M := M) g₀ g₁ 2) (pureTrace (I := I) (M := M) g₀ g₁ 4) := rfl
  exact capCongr (I := I) (M := M) g₀ P hpair
    (capApp (I := I) (M := M) g₀ P _ _ hK2_nn hK4_nn hP2 hP4)

/-! ### The curvature head of the residual normal form -/

set_option linter.unusedSectionVars false in
/-- The curvature head of the Palatini residual is linear in the state. -/
private lemma curvSmul (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (t : ℝ) :
    lrCurvF (I := I) (M := M) g₀ (t • T) = t • lrCurvF (I := I) (M := M) g₀ T := by
  rw [lrCurvF, lrCurvF, appCcRS_smul_right, appCcRS_smul_right, smul_add]

set_option linter.unusedVariables false in
/-- **Capped window of the curvature head, read at the perturbation.**

`lrCurvF g₀ P` is the fixed background curvature paired with `P` itself, so it
costs no derivative of the state; it is capped because `capOfP` spends the two
pointwise caps on `P`.  This is why the `s`-factor in front of `lrCurvF` inside
`lieCovR4` is load-bearing rather than decorative: it is what converts the state
`T`, whose order-zero jet is uncapped, into `P = s•T`, whose is not. -/
private theorem curvCap (g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2)
        (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ Λ)
        (hP1 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 1 ≤ Λ),
        HasCapWin (I := I) (M := M) g₀ P (lrCurvF (I := I) (M := M) g₀ P) K := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  choose S1 hS1_nn hS1 using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + i)
      (iteratedCovGrad (I := I) g₀ 2 4 i (lrRiemW1 (I := I) (M := M) g₀)))
  choose S2 hS2_nn hS2 using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + i)
      (iteratedCovGrad (I := I) g₀ 2 4 i (lrRiemW2 (I := I) (M := M) g₀)))
  set F1 : ℕ → ℝ := foldConst (E := E) 0 0 S1 (fun _ => Λ) with hF1_def
  set F2 : ℕ → ℝ := foldConst (E := E) 0 0 S2 (fun _ => Λ) with hF2_def
  have hF1_nn : ∀ i, 0 ≤ F1 i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hS1_nn (fun _ => hΛ0) i
  have hF2_nn : ∀ i, 0 ≤ F2 i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hS2_nn (fun _ => hΛ0) i
  refine ⟨fun i => 2 * F1 i + 2 * F2 i, fun i => by
    have := hF1_nn i; have := hF2_nn i; linarith, ?_⟩
  intro P hP0 hP1
  have hPcap : HasCapWin (I := I) (M := M) g₀ P P (fun _ => Λ) :=
    capOfP (I := I) (M := M) g₀ P hΛ1 hP0 hP1
  have hW1 : HasCapWin (I := I) (M := M) g₀ P (lrRiemW1 (I := I) (M := M) g₀) S1 :=
    capOfBnd (I := I) (M := M) g₀ P _ hS1_nn (fun i x => hS1 i x)
  have hW2 : HasCapWin (I := I) (M := M) g₀ P (lrRiemW2 (I := I) (M := M) g₀) S2 :=
    capOfBnd (I := I) (M := M) g₀ P _ hS2_nn (fun i x => hS2 i x)
  have h1 := capApp (I := I) (M := M) g₀ P
    (lrRiemW1 (I := I) (M := M) g₀) P hS1_nn (fun _ => hΛ0) hW1 hPcap
  have h2 := capApp (I := I) (M := M) g₀ P
    (lrRiemW2 (I := I) (M := M) g₀) P hS2_nn (fun _ => hΛ0) hW2 hPcap
  exact capCongr (I := I) (M := M) g₀ P (rfl : lrCurvF (I := I) (M := M) g₀ P = _)
    (capAdd (I := I) (M := M) g₀ P h1 h2)

/-! ### The connection-difference quadratic of the residual normal form -/

open CurvatureCoefficientDifferenceJetTower in
set_option linter.unusedVariables false in
/-- **Radius-free pointwise grid window for the REVERSED raised endomorphism,
inserted into a slot.**

`|∇ⁱ(slotInsertEndoCc g₀ s (fullRaisedEndoField g₁ g₀))|²(x) ≤ C i · atgw(bP)(i+1)`.

The reversed insertion is the recovery endomorphism (`fullRev0_eq`), which is
the frozen identity plus the raised symmetric perturbation (`omRecover_add`).
The identity part has vanishing jets in every positive order, and the raised
perturbation is a fibre isometry away from `symmS P`; the order-zero exception
is covered by the fibre smallness `δ ≤ δ₀`, not by a cap. -/
private theorem revEndoAtgw (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (s : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (q : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + q) x
            ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) q
              (slotInsertEndoCc (I := I) (M := M) g₀ s
                (fullRaisedEndoField (I := I) (M := M) g₁ g₀))).toSection x) ≤
          C q * Combinatorics.antidiagonalTupleGridWindow
            (gridBase (I := I) (M := M) g₀ P x) (q + 1) := by
  classical
  obtain ⟨cid, hcid_nn, hcid⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 1 1
    (slotInsertEndoCc (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₀))
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set d0 : ℝ := max δ₀ 0 with hd0_def
  have hd0_nn : (0 : ℝ) ≤ d0 := le_max_right _ _
  refine ⟨fun q => fr ^ s * (2 * cid + 2 * (fr * d0) ^ 2 + 2), fun q => by positivity, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ q x
  have hbnn := gridBase_nn (I := I) (M := M) g₀ P x
  have hone : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (gridBase (I := I) (M := M) g₀ P x) (q + 1) :=
    Combinatorics.one_le_antidiagonalTupleGridWindow _ hbnn (by omega)
  have hWnn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (gridBase (I := I) (M := M) g₀ P x) (q + 1) := le_trans zero_le_one hone
  have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ s
    (fullRaisedEndoField (I := I) (M := M) g₁ g₀) q x
  have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) x
      ((iteratedCovGrad (I := I) g₀ 1 1 q
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₁ g₀))).toSection x) ≤
      2 * cid + 2 * ((fr * d0) ^ 2 + Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ P x) (q + 1)) := by
    rw [fullRev0_eq (I := I) (M := M) g₀ g₁,
      omRecover_add (I := I) (M := M) g₀ g₁ P htie, iteratedCovGrad_add]
    rw [show ((iteratedCovGrad (I := I) g₀ 1 1 q
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) +
        iteratedCovGrad (I := I) g₀ 1 1 q
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P))).toSection x) =
        (iteratedCovGrad (I := I) g₀ 1 1 q
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x +
          (iteratedCovGrad (I := I) g₀ 1 1 q
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (symmS (I := I) (M := M) g₀ P))).toSection x
        from by rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + q) x _ _) ?_
    have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) x
        ((iteratedCovGrad (I := I) g₀ 1 1 q
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x) ≤ cid := by
      match q with
      | 0 => rw [iteratedCovGrad_zero]; exact hcid x
      | (m + 1) =>
          have hz : (iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x = 0 := by
            rw [iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero (I := I) (M := M) g₀ m]
            simp
          rw [hz, riemannianFiberNormSq_zero]
          exact hcid_nn
    have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) x
        ((iteratedCovGrad (I := I) g₀ 1 1 q
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P))).toSection x) ≤
        (fr * d0) ^ 2 + Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P x) (q + 1) := by
      rw [rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
        (symmS (I := I) (M := M) g₀ P) q x]
      match q with
      | 0 =>
          have hz := rfns_symmS_zero_le_fibreSmall (I := I) (M := M) g₀ hd0_nn P
            (le_trans hδ_le (le_max_left _ _)) hδ0 hδ x
          have hred : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (0 + 2 + 0) x
                ((iteratedCovGrad (I := I) g₀ 0 (0 + 2) 0
                  (symmS (I := I) (M := M) g₀ P)).toSection x) =
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
                ((symmS (I := I) (M := M) g₀ P).toSection x) := rfl
          rw [hred]
          linarith [hz, hWnn]
      | (m + 1) =>
          refine le_trans
            (rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ P (m + 1) x) ?_
          have hgb : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (m + 1) P).toSection x) =
              gridBase (I := I) (M := M) g₀ P x (m + 1) := rfl
          have hsg := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le
            (gridBase (I := I) (M := M) g₀ P x) hbnn 0 (m + 1) (by omega)
          rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one, zero_add] at hsg
          have hle : gridBase (I := I) (M := M) g₀ P x (m + 1) ≤
              Combinatorics.antidiagonalTupleGridWindow
                (gridBase (I := I) (M := M) g₀ P x) (m + 1 + 1) :=
            le_trans hsg
              (Combinatorics.antidiagonalTupleGrid_le_window _ hbnn (by omega))
          have hnn : (0 : ℝ) ≤ (fr * d0) ^ 2 := by positivity
          rw [hgb]
          linarith [hle, hnn]
    linarith [hA, hB]
  have hstep : fr ^ s * (2 * cid + 2 * ((fr * d0) ^ 2 +
      Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ P x) (q + 1))) ≤
      fr ^ s * (2 * cid + 2 * (fr * d0) ^ 2 + 2) *
        Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P x) (q + 1) := by
    have hfs : (0 : ℝ) ≤ fr ^ s := pow_nonneg hfr_nn s
    have hd : (0 : ℝ) ≤ (fr * d0) ^ 2 := by positivity
    set W : ℝ := Combinatorics.antidiagonalTupleGridWindow
      (gridBase (I := I) (M := M) g₀ P x) (q + 1) with hW_def
    have hprod : (0 : ℝ) ≤ (2 * cid + 2 * (fr * d0) ^ 2) * (W - 1) :=
      mul_nonneg (by linarith) (by linarith [hone])
    have hinner : 2 * cid + 2 * ((fr * d0) ^ 2 + W) ≤
        (2 * cid + 2 * (fr * d0) ^ 2 + 2) * W := by nlinarith [hprod]
    calc fr ^ s * (2 * cid + 2 * ((fr * d0) ^ 2 + W))
        ≤ fr ^ s * ((2 * cid + 2 * (fr * d0) ^ 2 + 2) * W) :=
          mul_le_mul_of_nonneg_left hinner hfs
      _ = fr ^ s * (2 * cid + 2 * (fr * d0) ^ 2 + 2) * W := by ring
  refine le_trans h1 (le_trans ?_ hstep)
  exact mul_le_mul_of_nonneg_left h2 (pow_nonneg hfr_nn s)

set_option linter.unusedVariables false in
/-- **Capped window of the moving-lowered connection difference.**

`lrOmegaHat g₀ g₁` is the reversed endomorphism insertion against the lowered
connection difference: the first factor costs no derivative of the state, the
second exactly one, so the product is capped. -/
private theorem omegaCap (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ Λ)
        (hP1 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 1 ≤ Λ),
        HasCapWin (I := I) (M := M) g₀ P (lrOmegaHat (I := I) (M := M) g₀ g₁) K := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨Ce, hCe_nn, hce⟩ := revEndoAtgw (I := I) (M := M) g₀ hδ₀ 2
  obtain ⟨Ccd, hCcd_nn, hcd⟩ := rfns_iCG_connDiffSection_atgw_rf (I := I) (M := M) g₀ hδ₀
  set KE : ℕ → ℝ := fun i => Ce i * shiftConst Λ (i + 1) with hKE_def
  set KC : ℕ → ℝ := fun i => Ccd i * shiftConst Λ (i + 1) with hKC_def
  have hKE_nn : ∀ i, 0 ≤ KE i := fun i => mul_nonneg (hCe_nn i) (shiftConst_nn hΛ0 _)
  have hKC_nn : ∀ i, 0 ≤ KC i := fun i => mul_nonneg (hCcd_nn i) (shiftConst_nn hΛ0 _)
  refine ⟨foldConst (E := E) 0 0 KE KC,
    fun i => foldConst_nn (E := E) (u := 0) (v := 0) hKE_nn hKC_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 hP1
  have hEndo : HasCapWin (I := I) (M := M) g₀ P
      (slotInsertEndoCc (I := I) (M := M) g₀ 2
        (fullRaisedEndoField (I := I) (M := M) g₁ g₀)) KE := by
    refine capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _ hCe_nn (fun i y => ?_)
    refine le_trans (hce g₁ P htie hδ_le hδ0 hδ i y) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCe_nn i)
    exact Combinatorics.antidiagonalTupleGridWindow_mono _
      (gridBase_nn (I := I) (M := M) g₀ P y) (by omega)
  have hCL : HasCapWin (I := I) (M := M) g₀ P
      (connDiffLoweredCc (I := I) g₀ g₁) KC := by
    refine capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _ hCcd_nn (fun i y => ?_)
    rw [connLow_rfns (I := I) (M := M) g₀ g₁ i y]
    exact hcd g₁ P htie hδ_le hδ0 hδ i y
  exact capCongr (I := I) (M := M) g₀ P
    (rfl : lrOmegaHat (I := I) (M := M) g₀ g₁ = _)
    (capApp (I := I) (M := M) g₀ P _ _ hKE_nn hKC_nn hEndo
      (capDdc0 (I := I) (M := M) g₀ P (finRotate 3) hCL))

set_option linter.unusedVariables false in
/-- **Capped window of the Palatini connection-difference quadratic.**

`lrQuadF g₀ g₁` is the six-term normal form of `∇g ⋆ ∇g` contracted with the
MOVING metric.  `lrQA`/`lrQB` are `lieCovArm2 ⋆ lrOmegaHat` — the first factor
is the connection difference read as a slot-inserting arm (`lieCovArm2_l2`
transfers its jets to `connDiffSection`), the second is the moving-lowered
connection difference — and both carry exactly one derivative of the state, so
the summand is quadratic in `∇P` and lands in the capped currency exactly like
`lc0AMix`.  The six output-slot permutations are fibre isometries. -/
private theorem lrQuadCap (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ Λ)
        (hP1 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 1 ≤ Λ),
        HasCapWin (I := I) (M := M) g₀ P (lrQuadF (I := I) (M := M) g₀ g₁) K := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨Kom, hKom_nn, wom⟩ := omegaCap (I := I) (M := M) g₀ hδ₀ hΛ1
  obtain ⟨Ccd, hCcd_nn, hcd⟩ := rfns_iCG_connDiffSection_atgw_rf (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KA : ℕ → ℝ := fun i => (fr ^ 2 * Ccd i) * shiftConst Λ (i + 1) with hKA_def
  have hKA_nn : ∀ i, 0 ≤ KA i := fun i =>
    mul_nonneg (mul_nonneg (pow_nonneg hfr_nn 2) (hCcd_nn i)) (shiftConst_nn hΛ0 _)
  set KJ : ℕ → ℝ := foldConst (E := E) 0 0 KA Kom with hKJ_def
  have hKJ_nn : ∀ i, 0 ≤ KJ i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hKA_nn hKom_nn i
  refine ⟨fun i => 94 * KJ i, fun i => by have := hKJ_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 hP1
  have hArm : HasCapWin (I := I) (M := M) g₀ P
      (lieCovArm2 (I := I) (M := M) g₀ g₁) KA := by
    refine capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _
      (fun i => mul_nonneg (pow_nonneg hfr_nn 2) (hCcd_nn i)) (fun i y => ?_)
    refine le_trans (lieCovArm2_l2 (I := I) (M := M) g₀ g₁ i y) ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hcd g₁ P htie hδ_le hδ0 hδ i y) (pow_nonneg hfr_nn 2)
  have hOm := wom g₁ P htie hδ_le hδ0 hδ hP0 hP1
  have hQB : HasCapWin (I := I) (M := M) g₀ P (lrQB (I := I) (M := M) g₀ g₁) KJ :=
    capCongr (I := I) (M := M) g₀ P (rfl : lrQB (I := I) (M := M) g₀ g₁ = _)
      (capApp (I := I) (M := M) g₀ P _ _ hKA_nn hKom_nn hArm hOm)
  have hQA : HasCapWin (I := I) (M := M) g₀ P (lrQA (I := I) (M := M) g₀ g₁) KJ :=
    capCongr (I := I) (M := M) g₀ P (rfl : lrQA (I := I) (M := M) g₀ g₁ = _)
      (capApp (I := I) (M := M) g₀ P _ _ hKA_nn hKom_nn hArm
        (capDdc0 (I := I) (M := M) g₀ P (Equiv.swap (0 : Fin 3) 1) hOm))
  have hsum := capAdd (I := I) (M := M) g₀ P
    (capAdd (I := I) (M := M) g₀ P
      (capAdd (I := I) (M := M) g₀ P
        (capAdd (I := I) (M := M) g₀ P
          (capAdd (I := I) (M := M) g₀ P
            (capDdc0 (I := I) (M := M) g₀ P (Equiv.swap (0 : Fin 4) 1) hQB) hQB)
          (capDdc0 (I := I) (M := M) g₀ P lrPermA hQA))
        (capDdc0 (I := I) (M := M) g₀ P (Equiv.swap (0 : Fin 4) 2) hQA))
      (capDdc0 (I := I) (M := M) g₀ P lrPermB hQA))
    (capDdc0 (I := I) (M := M) g₀ P lrPermC hQA)
  refine capCongr (I := I) (M := M) g₀ P (rfl : lrQuadF (I := I) (M := M) g₀ g₁ = _) ?_
  refine capMono (I := I) (M := M) g₀ P (fun i => ?_) hsum
  exact le_of_eq (by ring)

/-! ### The DeTurck--Lie covariant-derivative edge -/

set_option linter.unusedVariables false in
/-- **Capped window of the Palatini covariant-derivative arm against its
subtracted edge pairing.**

Neither `deTurckLieCovDerivArmField` nor `edgeLiePairFam` carries a window at
this level on its own — the first has a `∇A` head and the second a `∇²T` head —
but their difference does: `lieCov_residual` identifies it with the single
product `(-1) • lieCovPair ⋆ rsPerm (Ext² (lieCovR4))`, whose left factor is a
pure moving double trace (no derivative of the state) and whose right factor is
the fourth-covariant normal form `(-(s/2))•lrCurvF T − lrQuadF g₁`.  The
`s`-factor is absorbed into the perturbation, `P = s•T`, which is what makes the
curvature head capped. -/
theorem lieCovCap (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδg : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
        {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
        (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀
          (convexPerturbation (I := I) g₀ T 0 s) x 0 ≤ Λ)
        (hP1 : ∀ x : M, gridBase (I := I) (M := M) g₀
          (convexPerturbation (I := I) g₀ T 0 s) x 1 ≤ Λ),
        HasCapWin (I := I) (M := M) g₀ (convexPerturbation (I := I) g₀ T 0 s)
          (deTurckLieCovDerivArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδg hδZ s) g₀ -
            edgeLiePairFam (I := I) (M := M) g₀ T hδg hδZ
              lieRefoldQ lieRefoldEps s) K := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨KP, hKP_nn, wP⟩ := pairCap (I := I) (M := M) g₀ hδ₀ hΛ1
  obtain ⟨KC, hKC_nn, wC⟩ := curvCap (I := I) (M := M) g₀ hΛ1
  obtain ⟨KQ, hKQ_nn, wQ⟩ := lrQuadCap (I := I) (M := M) g₀ hδ₀ hΛ1
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KR : ℕ → ℝ := fun i => 2 * ((1 / 2 : ℝ) ^ 2 * KC i) + 2 * KQ i with hKR_def
  have hKR_nn : ∀ i, 0 ≤ KR i := fun i => by
    have h1 := hKC_nn i; have h2 := hKQ_nn i
    have h3 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 2 := by positivity
    simp only [hKR_def]; nlinarith [h1, h2, h3]
  set KE : ℕ → ℝ := fun i => fr ^ 2 * KR i with hKE_def
  have hKE_nn : ∀ i, 0 ≤ KE i := fun i => mul_nonneg (pow_nonneg hfr_nn 2) (hKR_nn i)
  refine ⟨fun i => (-1 : ℝ) ^ 2 * foldConst (E := E) 0 0 KP KE i,
    fun i => by
      have := foldConst_nn (E := E) (u := 0) (v := 0) hKP_nn hKE_nn i
      nlinarith [this], ?_⟩
  intro T hTsymm δ hδ_le hδ0 hδg hδZ s hs hP0 hP1
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  set P : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T 0 s with hP_def
  have hPeq : P = s • T := by
    rw [hP_def, convexPerturbation, smul_zero, zero_add]
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδg hδZ s).inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδg hδZ hsmem y v w
  have hδP : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ := by
    intro y v w
    have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδg hδZ s y v w
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith only [hs1] : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rwa [heq] at hraw
  -- the curvature head, with the path parameter absorbed into the perturbation
  have hcurv : ((-(s / 2) : ℝ)) • lrCurvF (I := I) (M := M) g₀ T =
      ((-(1 / 2) : ℝ)) • lrCurvF (I := I) (M := M) g₀ P := by
    rw [hPeq, curvSmul (I := I) (M := M) g₀ T s, smul_smul]
    congr 1
    ring
  have hCw : HasCapWin (I := I) (M := M) g₀ P
      (((-(s / 2) : ℝ)) • lrCurvF (I := I) (M := M) g₀ T)
      (fun i => (1 / 2 : ℝ) ^ 2 * KC i) := by
    refine capCongr (I := I) (M := M) g₀ P hcurv ?_
    refine capMono (I := I) (M := M) g₀ P (fun i => ?_)
      (capSmul (I := I) (M := M) g₀ P ((-(1 / 2) : ℝ)) (wC P hP0 hP1))
    have := hKC_nn i
    nlinarith [this]
  have hQw : HasCapWin (I := I) (M := M) g₀ P
      (lrQuadF (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s)) KQ :=
    wQ (realizedFam (I := I) g₀ T 0 hδg hδZ s) P htie hδ_le hδ0 hδP hP0 hP1
  have hR4 : HasCapWin (I := I) (M := M) g₀ P
      (lieCovR4 (I := I) (M := M) g₀ T hδg hδZ s) KR := by
    refine capCongr (I := I) (M := M) g₀ P
      (lieCovR4_eq (I := I) (M := M) g₀ T hδg hδZ s) ?_
    exact capSub (I := I) (M := M) g₀ P hCw hQw
  have hExt : HasCapWin (I := I) (M := M) g₀ P
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (lieCovR4 (I := I) (M := M) g₀ T hδg hδZ s))) KE :=
    capDdc (I := I) (M := M) g₀ P lieCovSigma
      (capIter (I := I) (M := M) g₀ P 2 hR4)
  have hPw : HasCapWin (I := I) (M := M) g₀ P
      (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s)) KP :=
    wP (realizedFam (I := I) g₀ T 0 hδg hδZ s) P htie hδ_le hδ0 hδP hP0 hP1
  refine capCongr (I := I) (M := M) g₀ P
    (lieCov_residual (I := I) (M := M) g₀ T hδ_lt hδg hδZ hTsymm hs) ?_
  exact capSmul (I := I) (M := M) g₀ P (-1 : ℝ)
    (capApp (I := I) (M := M) g₀ P _ _ hKP_nn hKE_nn hPw hExt)

/-! ### The Palatini covariant-derivative residual in the marked currency

The capped chain above spends a `shiftConst Λ (i+1)` on every arm.  The marked
chain below spends nothing: `lieCovPair`, `lrCurvF g₀ P` and the endomorphism
insertions are all order zero in the state and enter unmarked, and the only
factors that carry a derivative are the two connection differences inside
`lrQuadF`.  Hence the residual is `(unmarked) + (twice marked)`, which is exactly
the pair of shapes `markJet0` and `markJet` consume. -/

set_option linter.unusedVariables false in
/-- **`lieCovPair` in the marked currency: no derivative of the state.**

The double moving trace against the quadruple moving trace; both factors enter
through `ptAtgw`, whose `atgw bP (i+1)` window *is* the unmarked marked window by
definition of `markGrid` at `u = 0`.  Constants are state-free — no `Λ`, no
Sobolev radius. -/
theorem pairMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        HasMarkWin (I := I) (M := M) g₀ P (lieCovPair (I := I) (M := M) g₀ g₁) 0 K := by
  classical
  obtain ⟨C2, hC2_nn, h2⟩ := ptAtgw (I := I) (M := M) g₀ hδ₀ 2
  obtain ⟨C4, hC4_nn, h4⟩ := ptAtgw (I := I) (M := M) g₀ hδ₀ 4
  refine ⟨foldConst (E := E) 0 0 C2 C4,
    fun i => foldConst_nn (E := E) (u := 0) (v := 0) hC2_nn hC4_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ
  have hP2 : HasMarkWin (I := I) (M := M) g₀ P
      (pureTrace (I := I) (M := M) g₀ g₁ 2) 0 C2 :=
    mkOfWin (I := I) (M := M) g₀ P _ (fun i x => h2 g₁ P htie hδ_le hδ0 hδ i x)
  have hP4 : HasMarkWin (I := I) (M := M) g₀ P
      (pureTrace (I := I) (M := M) g₀ g₁ 4) 0 C4 :=
    mkOfWin (I := I) (M := M) g₀ P _ (fun i x => h4 g₁ P htie hδ_le hδ0 hδ i x)
  refine mkCongr (I := I) (M := M) g₀ P
    (rfl : lieCovPair (I := I) (M := M) g₀ g₁ = _) ?_
  simpa using mkApp (I := I) (M := M) g₀ P _ _ hC2_nn hC4_nn hP2 hP4

set_option linter.unusedVariables false in
/-- **The curvature head in the marked currency: linear, order zero, unmarked.**

`lrCurvF g₀ P` is the *fixed background* Riemann tensor contracted with `P`
itself — `lrCurvF_unitModel_apply` shows there is no covariant derivative of the
state anywhere in it — so it enters at `u = 0` through `mkOfP`, and its tame
bound needs no `∇P` cap at all.  The `∇²T` one might expect from the name of the
subtracted edge does not survive `lieCov_residual`: it is cancelled there. -/
theorem curvMark (g₀ : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ 1) →
        HasMarkWin (I := I) (M := M) g₀ P (lrCurvF (I := I) (M := M) g₀ P) 0 K := by
  classical
  choose S1 hS1_nn hS1 using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + i)
      (iteratedCovGrad (I := I) g₀ 2 4 i (lrRiemW1 (I := I) (M := M) g₀)))
  choose S2 hS2_nn hS2 using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + i)
      (iteratedCovGrad (I := I) g₀ 2 4 i (lrRiemW2 (I := I) (M := M) g₀)))
  set F1 : ℕ → ℝ := foldConst (E := E) 0 0 S1 (fun _ => 1) with hF1_def
  set F2 : ℕ → ℝ := foldConst (E := E) 0 0 S2 (fun _ => 1) with hF2_def
  have hF1_nn : ∀ i, 0 ≤ F1 i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hS1_nn (fun _ => zero_le_one) i
  have hF2_nn : ∀ i, 0 ≤ F2 i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hS2_nn (fun _ => zero_le_one) i
  refine ⟨fun i => 2 * F1 i + 2 * F2 i, fun i => by
    have := hF1_nn i; have := hF2_nn i; linarith, ?_⟩
  intro P hP0
  have hPw : HasMarkWin (I := I) (M := M) g₀ P P 0 (fun _ => 1) :=
    mkOfP (I := I) (M := M) g₀ P hP0
  have hW1 : HasMarkWin (I := I) (M := M) g₀ P (lrRiemW1 (I := I) (M := M) g₀) 0 S1 :=
    mkOfBnd (I := I) (M := M) g₀ P _ hS1_nn (fun i x => hS1 i x)
  have hW2 : HasMarkWin (I := I) (M := M) g₀ P (lrRiemW2 (I := I) (M := M) g₀) 0 S2 :=
    mkOfBnd (I := I) (M := M) g₀ P _ hS2_nn (fun i x => hS2 i x)
  have h1 := mkApp (I := I) (M := M) g₀ P (lrRiemW1 (I := I) (M := M) g₀) P
    hS1_nn (fun _ => zero_le_one) hW1 hPw
  have h2 := mkApp (I := I) (M := M) g₀ P (lrRiemW2 (I := I) (M := M) g₀) P
    hS2_nn (fun _ => zero_le_one) hW2 hPw
  refine mkCongr (I := I) (M := M) g₀ P
    (rfl : lrCurvF (I := I) (M := M) g₀ P = _) ?_
  simpa using mkAdd (I := I) (M := M) g₀ P h1 h2

set_option linter.unusedVariables false in
/-- **The moving-lowered connection difference, once marked.**

`lrOmegaHat` is the reversed endomorphism insertion (order zero, `revEndoAtgw`)
against the lowered connection difference, whose jets transfer to
`connDiffSection` by `connLow_rfns` and are once marked by `connDiffMark`. -/
theorem omegaMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        HasMarkWin (I := I) (M := M) g₀ P (lrOmegaHat (I := I) (M := M) g₀ g₁) 1 K := by
  classical
  obtain ⟨Ce, hCe_nn, hce⟩ := revEndoAtgw (I := I) (M := M) g₀ hδ₀ 2
  obtain ⟨Kcd, hKcd_nn, hcd⟩ := connDiffMark (I := I) (M := M) g₀ hδ₀
  refine ⟨foldConst (E := E) 0 0 Ce Kcd,
    fun i => foldConst_nn (E := E) (u := 0) (v := 0) hCe_nn hKcd_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ
  have hEndo : HasMarkWin (I := I) (M := M) g₀ P
      (slotInsertEndoCc (I := I) (M := M) g₀ 2
        (fullRaisedEndoField (I := I) (M := M) g₁ g₀)) 0 Ce :=
    mkOfWin (I := I) (M := M) g₀ P _ (fun i y => hce g₁ P htie hδ_le hδ0 hδ i y)
  have hCL : HasMarkWin (I := I) (M := M) g₀ P
      (connDiffLoweredCc (I := I) g₀ g₁) 1 Kcd := by
    intro i y
    rw [connLow_rfns (I := I) (M := M) g₀ g₁ i y]
    exact hcd g₁ P htie hδ_le hδ0 hδ i y
  refine mkCongr (I := I) (M := M) g₀ P
    (rfl : lrOmegaHat (I := I) (M := M) g₀ g₁ = _) ?_
  simpa using mkApp (I := I) (M := M) g₀ P _ _ hCe_nn hKcd_nn hEndo
    (mkDdc0 (I := I) (M := M) g₀ P (finRotate 3) hCL)

set_option linter.unusedVariables false in
/-- **The Palatini connection-difference quadratic: two explicit `∇P` factors.**

`lrQA`/`lrQB` are `lieCovArm2 ⋆ lrOmegaHat`, each factor once marked, so the six
output-slot permutations of the normal form are all twice marked, with
**state-free** constants.  This is the only part of the covariant-derivative
residual that is quadratic in the state at all. -/
theorem lrQuadMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        HasMarkWin (I := I) (M := M) g₀ P (lrQuadF (I := I) (M := M) g₀ g₁) 2 K := by
  classical
  obtain ⟨Kom, hKom_nn, wom⟩ := omegaMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kcd, hKcd_nn, hcd⟩ := connDiffMark (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KA : ℕ → ℝ := fun i => fr ^ 2 * Kcd i with hKA_def
  have hKA_nn : ∀ i, 0 ≤ KA i := fun i =>
    mul_nonneg (pow_nonneg hfr_nn 2) (hKcd_nn i)
  set KJ : ℕ → ℝ := foldConst (E := E) 0 0 KA Kom with hKJ_def
  have hKJ_nn : ∀ i, 0 ≤ KJ i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hKA_nn hKom_nn i
  refine ⟨fun i => 94 * KJ i, fun i => by have := hKJ_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ
  have hArm : HasMarkWin (I := I) (M := M) g₀ P
      (lieCovArm2 (I := I) (M := M) g₀ g₁) 1 KA := by
    intro i y
    refine le_trans (lieCovArm2_l2 (I := I) (M := M) g₀ g₁ i y) ?_
    rw [hKA_def, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hcd g₁ P htie hδ_le hδ0 hδ i y) (pow_nonneg hfr_nn 2)
  have hOm := wom g₁ P htie hδ_le hδ0 hδ
  have hQB : HasMarkWin (I := I) (M := M) g₀ P (lrQB (I := I) (M := M) g₀ g₁) 2 KJ := by
    refine mkCongr (I := I) (M := M) g₀ P (rfl : lrQB (I := I) (M := M) g₀ g₁ = _) ?_
    simpa using mkApp (I := I) (M := M) g₀ P _ _ hKA_nn hKom_nn hArm hOm
  have hQA : HasMarkWin (I := I) (M := M) g₀ P (lrQA (I := I) (M := M) g₀ g₁) 2 KJ := by
    refine mkCongr (I := I) (M := M) g₀ P (rfl : lrQA (I := I) (M := M) g₀ g₁ = _) ?_
    simpa using mkApp (I := I) (M := M) g₀ P _ _ hKA_nn hKom_nn hArm
      (mkDdc0 (I := I) (M := M) g₀ P (Equiv.swap (0 : Fin 3) 1) hOm)
  have hsum := mkAdd (I := I) (M := M) g₀ P
    (mkAdd (I := I) (M := M) g₀ P
      (mkAdd (I := I) (M := M) g₀ P
        (mkAdd (I := I) (M := M) g₀ P
          (mkAdd (I := I) (M := M) g₀ P
            (mkDdc0 (I := I) (M := M) g₀ P (Equiv.swap (0 : Fin 4) 1) hQB) hQB)
          (mkDdc0 (I := I) (M := M) g₀ P lrPermA hQA))
        (mkDdc0 (I := I) (M := M) g₀ P (Equiv.swap (0 : Fin 4) 2) hQA))
      (mkDdc0 (I := I) (M := M) g₀ P lrPermB hQA))
    (mkDdc0 (I := I) (M := M) g₀ P lrPermC hQA)
  refine mkCongr (I := I) (M := M) g₀ P (rfl : lrQuadF (I := I) (M := M) g₀ g₁ = _) ?_
  refine mkMono (I := I) (M := M) g₀ P (fun i => ?_) hsum
  exact le_of_eq (by ring)

open CurvatureCoefficientDifferenceJetTower in
set_option linter.unusedSectionVars false in
/-- Two slot extensions of a purely covariant arm are additive on differences. -/
private lemma extSub (g₀ : SmoothRiemannianMetric I M) (X Y : SmoothCcTensor g₀ 0 4) :
    slotExtendIter (I := I) (M := M) g₀ 0 4 2 (X - Y) =
      slotExtendIter (I := I) (M := M) g₀ 0 4 2 X -
        slotExtendIter (I := I) (M := M) g₀ 0 4 2 Y := by
  have hrec : ∀ Z : SmoothCcTensor g₀ 0 4,
      slotExtendIter (I := I) (M := M) g₀ 0 4 2 Z =
        slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 Z) :=
    fun _ => rfl
  rw [hrec, hrec, hrec, slotExtend_sub_cc, slotExtend_sub_cc]

open CurvatureCoefficientDifferenceJetTower in
set_option linter.unusedVariables false in
/-- **The DeTurck--Lie covariant-derivative residual's tame `L²` jet bound.**

```
‖∇ⁱ(deTurckLieCovDerivArmField − edgeLiePairFam)‖²
    ≤ (K₀ i + K₂ i · ‖P‖²_{H³}) · (1 + ∑_{j < i+2} ‖∇ʲP‖²)
```

with `K₀, K₂` chosen before the state — background metric and order only, no
Sobolev radius, no cap, no `s`, and exactly ONE power of `‖P‖²_{H³}`.

The residual carries **no second derivative of the state**.  `lieCov_residual`
collapses the difference of the `∇A`-headed arm and the `∇²T`-headed edge to the
single product `(−1) • lieCovPair ⋆ σ(Ext²(lieCovR4))`, and there
`lieCovR4 = (−½)•lrCurvF P − lrQuadF g₁` has an order-zero curvature head
(`lrCurvF` is the *fixed background* Riemann tensor contracted with `P` itself)
and a quadratic connection-difference tail.  The two halves therefore have
different mark counts and are split along the sub-linearity of `slotExtendIter`,
`rsDomDomCongrSection` and `appCcRS`: the curvature half is unmarked and consumes
`markJet0` (no `Λ₁`, axiom-clean), the quadratic half is twice marked and
consumes `markJet`.

The `s`-factor in front of `lrCurvF` inside `lieCovR4` is load-bearing exactly as
in `lieCovCap`: it turns the state `T`, whose order-zero jet is uncontrolled,
into the perturbation `P = s•T`, whose δ-anchor `|P|_∞ ≤ 1` is the only
hypothesis on the state beyond the standard fibre-operator bound.

Compare `lieCovCap`-then-`capJet`: same left-hand side, but a constant of
`Λ`-degree growing with the order. -/
theorem lieCovJet (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w =
            ccTensorBilin (I := I) g₀ T x w v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδg : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
        {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
        (hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((convexPerturbation (I := I) g₀ T 0 s).toSection x) ≤ 1)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδg hδZ s) g₀ -
              edgeLiePairFam (I := I) (M := M) g₀ T hδg hδZ
                lieRefoldQ lieRefoldEps s)‖ ^ 2 ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j)
                (convexPerturbation (I := I) g₀ T 0 s)‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j
                (convexPerturbation (I := I) g₀ T 0 s)‖ ^ 2) := by
  classical
  obtain ⟨KP, hKP_nn, wP⟩ := pairMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨KC, hKC_nn, wC⟩ := curvMark (I := I) (M := M) g₀
  obtain ⟨KQ, hKQ_nn, wQ⟩ := lrQuadMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨K0A, hK0A_nn, hjet0⟩ := markJet0 (I := I) (M := M) g₀
  obtain ⟨K0B, hK0B_nn, hjet⟩ := markJet (I := I) (M := M) g₀
  obtain ⟨cg, hcg_nn, hcg⟩ := gradCapLin (I := I) (M := M) hDim g₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KEA : ℕ → ℝ := fun i => fr ^ 2 * ((-(1 / 2 : ℝ)) ^ 2 * KC i) with hKEA_def
  have hKEA_nn : ∀ i, 0 ≤ KEA i := fun i => by
    have := hKC_nn i
    simp only [hKEA_def]
    positivity
  set KEB : ℕ → ℝ := fun i => fr ^ 2 * KQ i with hKEB_def
  have hKEB_nn : ∀ i, 0 ≤ KEB i := fun i =>
    mul_nonneg (pow_nonneg hfr_nn 2) (hKQ_nn i)
  set KAr : ℕ → ℝ := foldConst (E := E) 0 0 KP KEA with hKAr_def
  have hKAr_nn : ∀ i, 0 ≤ KAr i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hKP_nn hKEA_nn i
  set KBr : ℕ → ℝ := foldConst (E := E) 0 0 KP KEB with hKBr_def
  have hKBr_nn : ∀ i, 0 ≤ KBr i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hKP_nn hKEB_nn i
  refine ⟨fun i => 2 * (KBr i * K0B i) + 2 * (KAr i * K0A i),
    fun i => 2 * (KBr i * K0B i) * cg,
    fun i => by
      have h1 : (0 : ℝ) ≤ KBr i * K0B i := mul_nonneg (hKBr_nn i) (hK0B_nn i)
      have h2 : (0 : ℝ) ≤ KAr i * K0A i := mul_nonneg (hKAr_nn i) (hK0A_nn i)
      linarith,
    fun i => by
      have h1 : (0 : ℝ) ≤ KBr i * K0B i := mul_nonneg (hKBr_nn i) (hK0B_nn i)
      positivity, ?_⟩
  intro T hTsymm δ hδ_le hδ0 hδg hδZ s hs hP0 i
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  set P : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T 0 s with hP_def
  have hPeq : P = s • T := by
    rw [hP_def, convexPerturbation, smul_zero, zero_add]
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδg hδZ s).inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδg hδZ hsmem y v w
  have hδP : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ := by
    intro y v w
    have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδg hδZ s y v w
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith only [hs1] : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rwa [heq] at hraw
  -- the two halves of the fourth-covariant normal form
  have hcurv : ((-(s / 2) : ℝ)) • lrCurvF (I := I) (M := M) g₀ T =
      ((-(1 / 2) : ℝ)) • lrCurvF (I := I) (M := M) g₀ P := by
    rw [hPeq, curvSmul (I := I) (M := M) g₀ T s, smul_smul]
    congr 1
    ring
  have hAw : HasMarkWin (I := I) (M := M) g₀ P
      (((-(1 / 2) : ℝ)) • lrCurvF (I := I) (M := M) g₀ P) 0
      (fun i => (-(1 / 2 : ℝ)) ^ 2 * KC i) :=
    mkSmul (I := I) (M := M) g₀ P ((-(1 / 2) : ℝ)) (wC P (fun x => hP0 x))
  have hBw : HasMarkWin (I := I) (M := M) g₀ P
      (lrQuadF (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s)) 2 KQ :=
    wQ (realizedFam (I := I) g₀ T 0 hδg hδZ s) P htie hδ_le hδ0 hδP
  have hPw : HasMarkWin (I := I) (M := M) g₀ P
      (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s)) 0 KP :=
    wP (realizedFam (I := I) g₀ T 0 hδg hδZ s) P htie hδ_le hδ0 hδP
  have hArmA : HasMarkWin (I := I) (M := M) g₀ P
      (appCcRS (I := I) (M := M) g₀ 2 6 2
        (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (((-(1 / 2) : ℝ)) • lrCurvF (I := I) (M := M) g₀ P)))) 0 KAr := by
    simpa using mkApp (I := I) (M := M) g₀ P _ _ hKP_nn hKEA_nn hPw
      (mkDdc (I := I) (M := M) g₀ P lieCovSigma
        (mkIter (I := I) (M := M) g₀ P 2 hAw))
  have hArmB : HasMarkWin (I := I) (M := M) g₀ P
      (appCcRS (I := I) (M := M) g₀ 2 6 2
        (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (lrQuadF (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδg hδZ s))))) 2 KBr := by
    simpa using mkApp (I := I) (M := M) g₀ P _ _ hKP_nn hKEB_nn hPw
      (mkDdc (I := I) (M := M) g₀ P lieCovSigma
        (mkIter (I := I) (M := M) g₀ P 2 hBw))
  -- the residual, split along the sub-linearity of the three structural maps
  have hres :
      deTurckLieCovDerivArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδg hδZ s) g₀ -
        edgeLiePairFam (I := I) (M := M) g₀ T hδg hδZ
          lieRefoldQ lieRefoldEps s =
      appCcRS (I := I) (M := M) g₀ 2 6 2
          (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (lrQuadF (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδg hδZ s)))) -
        appCcRS (I := I) (M := M) g₀ 2 6 2
          (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (((-(1 / 2) : ℝ)) • lrCurvF (I := I) (M := M) g₀ P))) := by
    have hres0 :
        deTurckLieCovDerivArmField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδg hδZ s) g₀ -
          edgeLiePairFam (I := I) (M := M) g₀ T hδg hδZ
            lieRefoldQ lieRefoldEps s =
          (-1 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 6 2
            (lieCovPair (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδg hδZ s))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (lieCovR4 (I := I) (M := M) g₀ T hδg hδZ s))) :=
      lieCov_residual (I := I) (M := M) g₀ T hδ_lt hδg hδZ hTsymm hs
    rw [hres0, lieCovR4_eq (I := I) (M := M) g₀ T hδg hδZ s, hcurv,
      extSub (I := I) (M := M) g₀, rsDomDomCongrSection_sub_cc,
      appCcRS_sub_right_cc, neg_smul, one_smul, neg_sub]
  -- the tame bounds of the two halves
  set H3 : ℝ := ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2 with hH3_def
  have hH3_nn : 0 ≤ H3 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  set Λ₁ : ℝ := Real.sqrt (cg * H3) with hΛ₁_def
  have hΛ₁0 : 0 ≤ Λ₁ := Real.sqrt_nonneg _
  have hΛ₁sq : Λ₁ ^ 2 = cg * H3 := Real.sq_sqrt (mul_nonneg hcg_nn hH3_nn)
  have hcap : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2 := by
    intro x
    rw [hΛ₁sq]
    exact hcg P x
  have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
      (P.toSection x) ≤ (1 : ℝ) ^ 2 := by
    intro x; rw [one_pow]; exact hP0 x
  set JS : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hJS_def
  have hJS_nn : 0 ≤ JS := by
    have h : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    simp only [hJS_def]; linarith
  have hbA := hjet0 P hP0 _ hKAr_nn hArmA i
  have hbB := hjet P (Λ₀ := 1) zero_le_one (le_refl _) hΛ₁0 hsup hcap _ hKBr_nn hArmB i
  -- assemble
  rw [hres, iteratedCovGrad_sub]
  have hnA : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (appCcRS (I := I) (M := M) g₀ 2 6 2
        (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (((-(1 / 2) : ℝ)) • lrCurvF (I := I) (M := M) g₀ P))))‖ := norm_nonneg _
  have hnB : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (appCcRS (I := I) (M := M) g₀ 2 6 2
        (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (lrQuadF (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδg hδZ s)))))‖ := norm_nonneg _
  have htri := norm_sub_le
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (appCcRS (I := I) (M := M) g₀ 2 6 2
        (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (lrQuadF (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδg hδZ s))))))
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (appCcRS (I := I) (M := M) g₀ 2 6 2
        (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (((-(1 / 2) : ℝ)) • lrCurvF (I := I) (M := M) g₀ P)))))
  have hsq : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 6 2
          (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (lrQuadF (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδg hδZ s))))) -
      iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 6 2
          (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (((-(1 / 2) : ℝ)) • lrCurvF (I := I) (M := M) g₀ P))))‖ ^ 2 ≤
      2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2
            (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (lrQuadF (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδg hδZ s)))))‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (appCcRS (I := I) (M := M) g₀ 2 6 2
              (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (((-(1 / 2) : ℝ)) • lrCurvF (I := I) (M := M) g₀ P))))‖ ^ 2 := by
    nlinarith [htri, hnA, hnB, norm_nonneg (iteratedCovGrad (I := I) g₀ 2 2 i
      (appCcRS (I := I) (M := M) g₀ 2 6 2
        (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (lrQuadF (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδg hδZ s))))) -
      iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 6 2
          (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (((-(1 / 2) : ℝ)) • lrCurvF (I := I) (M := M) g₀ P))))),
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2
            (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (lrQuadF (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδg hδZ s)))))‖ -
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (appCcRS (I := I) (M := M) g₀ 2 6 2
              (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (((-(1 / 2) : ℝ)) • lrCurvF (I := I) (M := M) g₀ P))))‖)]
  refine hsq.trans ?_
  have hAfin : 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (appCcRS (I := I) (M := M) g₀ 2 6 2
        (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (((-(1 / 2) : ℝ)) • lrCurvF (I := I) (M := M) g₀ P))))‖ ^ 2 ≤
      2 * (KAr i * K0A i) * JS := by
    have h := mul_le_mul_of_nonneg_left hbA (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i _‖ ^ 2
        ≤ 2 * (KAr i * K0A i * JS) := h
      _ = 2 * (KAr i * K0A i) * JS := by ring
  have hBfin : 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (appCcRS (I := I) (M := M) g₀ 2 6 2
        (lieCovPair (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (lrQuadF (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδg hδZ s)))))‖ ^ 2 ≤
      (2 * (KBr i * K0B i) + 2 * (KBr i * K0B i) * cg * H3) * JS := by
    have h := mul_le_mul_of_nonneg_left hbB (by norm_num : (0 : ℝ) ≤ 2)
    refine h.trans (le_of_eq ?_)
    rw [hΛ₁sq]
    ring
  have hgoal : 2 * (KAr i * K0A i) * JS +
      (2 * (KBr i * K0B i) + 2 * (KBr i * K0B i) * cg * H3) * JS =
      (2 * (KBr i * K0B i) + 2 * (KAr i * K0A i) +
        2 * (KBr i * K0B i) * cg * H3) * JS := by ring
  linarith [hAfin, hBfin, hgoal.le, hgoal.ge]

/-! ### The covariant derivative of the transparent Koszul coefficient

`clAtgw` reads `connLowOp` itself; the Palatini `∇A ⋆ ∇T` arm needs its
*covariant derivative* one level lower, i.e. once marked at level `i` rather than
unmarked at level `i + 1`.  What buys the level is that the two outer factors of
`connLowOp` are slot permutations and the inner endomorphism insertion is the
identity at `g₁ = g₀`: after the permutations are recognised as fibre isometries,
the derivative has nowhere to fall except on the inverse-metric difference, whose
jets are an EXACT-weight grid — the input of `mkOfAtg`. -/

set_option backward.isDefEq.respectTransparency false in
open CurvatureCoefficientDifferenceJetTower in
set_option linter.unusedSectionVars false in
/-- **The frozen endomorphism insertion is `∇`-parallel, at every slot.**

`slotInsertEndoCc g₀ s (fullRaisedEndoField g₀ g₀)` is the identity operator on
`Tensor0SSpace (s+1)`, and `endoCovariantDerivative_fullRaised_id_eq_zero` is
slot-independent, so the generic-`s` statement is the `s = 0` proof verbatim.
The `s = 0` case is the public `covGrad_slotInsert_fullRaised_id_eq_zero`. -/
private lemma sieZero (g₀ : SmoothRiemannianMetric I M) (s : ℕ) :
    covGrad (I := I) (M := M) g₀ (s + 1) (s + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ s
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ (s + 1) (s + 1)
    (slotInsertEndoCc (I := I) (M := M) g₀ s
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) x D m]
  rw [tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g₀ s
    (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x (m 0)]
  rw [show ((endoCovariantDerivative (I := I) (M := M) g₀)
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x (m 0)) =
      (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from by
    apply ContinuousLinearMap.ext
    intro w
    rw [ContinuousLinearMap.zero_apply]
    obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x w
    rw [← hY]
    exact endoCovariantDerivative_fullRaised_id_eq_zero (I := I) (M := M) g₀ Y x (m 0)]
  rw [show slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (0 : TangentSpace I x →L[ℝ] TangentSpace I x) = 0 from by
    rw [show (0 : TangentSpace I x →L[ℝ] TangentSpace I x) =
        (0 : ℝ) • (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from (zero_smul ℝ _).symm,
      slotInsertEndoFib_smul_left, zero_smul]]
  simp [SmoothCcTensor.toSection_zero]

set_option linter.unusedSectionVars false in
/-- **Applying a slot-permutation field on the source side is a source reindex.**

The right-hand companion of `permAppEqRs`: precomposition with `permCoeff g₀ ρ`
permutes the INPUT slots, which is exactly `reindexCoeffGen`.  Both sides are
fibre-norm isometries of `Φ` at every covariant jet order. -/
private lemma permRe (g₀ : SmoothRiemannianMetric I M) {d : ℕ}
    (Φ : SmoothCcTensor g₀ d d) (ρ : Equiv.Perm (Fin d)) :
    appCcRS (I := I) (M := M) g₀ d d d Φ
        (permCoeff (I := I) (M := M) g₀ ρ) =
      reindexCoeffGen (I := I) (M := M) g₀ d d Φ ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [appCcRS_toSection, ContinuousLinearMap.comp_apply, reindexCoeffGen_toSection,
    reindexCoeffFibGen_apply]
  change (show Tensor0SSpace d I x →L[ℝ] Tensor0SSpace d I x from Φ.toSection x)
      (slotPermCLM (I := I) ρ x D) = _
  rw [slotPermCLM_apply]

set_option linter.unusedSectionVars false in
/-- **The transparent Koszul coefficient, with its permutation content written
out.**

The witness of `clSplit` is here supplied explicitly — as the half-sum of three
`permCoeff` fields — rather than left opaque.  The private `koszulOp` of the
read-only low-base action module is still never named: the equation holds by
`rfl` because its body IS this combination, and writing the body is what lets the
three permutations be recognised as source reindexes. -/
private lemma clZ (g₀ g₁ : SmoothRiemannianMetric I M) :
    connLowOp (I := I) (M := M) g₀ g₁ =
      appCcRS (I := I) (M := M) g₀ 3 3 3 (permCoeff (I := I) (M := M) g₀ lowPerm)
        (appCcRS (I := I) (M := M) g₀ 3 3 3
          (slotInsertEndoCc (I := I) (M := M) g₀ 2
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))
          ((1 / 2 : ℝ) •
            (permCoeff (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 2) +
              permCoeff (I := I) (M := M) g₀ (finRotate 3) -
              permCoeff (I := I) (M := M) g₀ (Equiv.swap (1 : Fin 3) 2)))) := rfl

set_option linter.unusedSectionVars false in
private lemma icgSm (g₀ : SmoothRiemannianMetric I M) (r c j : ℕ) (k : ℝ)
    (X : SmoothCcTensor g₀ r c) :
    iteratedCovGrad (I := I) g₀ r c j (k • X) =
      k • iteratedCovGrad (I := I) g₀ r c j X := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

open CurvatureCoefficientDifferenceJetTower in
set_option linter.unusedVariables false in
/-- **Every positive-order jet of the transparent Koszul coefficient is an
EXACT-weight grid.**

`|∇^{i+1}(connLowOp g₀ g₁)|²(x) ≤ C i · grid(bP x)(i + 1)`: no constant monomial
and no bare lower-weight monomial, which is exactly what `clAtgw` — an `atgw`
*window* — cannot say.  Three facts do it: the outer permutation is a fibre
isometry (`rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr`), the inner Koszul
factor is three source reindexes (`clZ` + `permRe`), and at `g₁ = g₀` the
remaining endomorphism insertion is `∇`-parallel (`sieZero`), so the whole
derivative sits on the inverse-metric difference, whose jets the tree already
delivers at exact weight. -/
private theorem clExact (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
              (connLowOp (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGrid
            (gridBase (I := I) (M := M) g₀ P x) (i + 1) := by
  classical
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => 3 * (fr ^ 2 * Cb (i + 1)), fun i => by
    have := hCb_nn (i + 1)
    have : (0 : ℝ) ≤ fr ^ 2 * Cb (i + 1) := mul_nonneg (by positivity) (hCb_nn (i + 1))
    linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ i x
  -- the endomorphism insertion and the explicit Koszul witness
  set E₁ : SmoothCcTensor g₀ 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 2
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁) with hE₁_def
  set Zc : SmoothCcTensor g₀ 3 3 :=
    (1 / 2 : ℝ) • (permCoeff (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 2) +
      permCoeff (I := I) (M := M) g₀ (finRotate 3) -
      permCoeff (I := I) (M := M) g₀ (Equiv.swap (1 : Fin 3) 2)) with hZc_def
  set Y : SmoothCcTensor g₀ 3 3 := appCcRS (I := I) (M := M) g₀ 3 3 3 E₁ Zc with hY_def
  -- (1) the outer permutation is a fibre isometry at every jet order
  have hiso : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
      ((iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
        (connLowOp (I := I) (M := M) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 3 3 (i + 1) Y).toSection x) := by
    refine rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 3 3
      lowPerm Y (connLowOp (I := I) (M := M) g₀ g₁) (fun y d => ?_) (i + 1) x
    rw [clZ (I := I) (M := M) g₀ g₁, appCcRS_toSection, ContinuousLinearMap.comp_apply]
    change Tensor0SSpace.toModel
        (slotPermCLM (I := I) lowPerm y
          ((show Tensor0SSpace 3 I y →L[ℝ] Tensor0SSpace 3 I y from Y.toSection y) d)) = _
    rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel]
  -- (2) the Koszul witness turns the product into three source reindexes
  have hYsplit : Y = (1 / 2 : ℝ) •
      (reindexCoeffGen (I := I) (M := M) g₀ 3 3 E₁ (Equiv.swap (0 : Fin 3) 2) +
        reindexCoeffGen (I := I) (M := M) g₀ 3 3 E₁ (finRotate 3) -
        reindexCoeffGen (I := I) (M := M) g₀ 3 3 E₁ (Equiv.swap (1 : Fin 3) 2)) := by
    rw [hY_def, hZc_def, appCcRS_smul_right, appCcRS_sub_right, appCcRS_add_right,
      permRe, permRe, permRe]
  -- (3) each reindexed copy has the fibre jets of the insertion itself
  set q : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
    ((iteratedCovGrad (I := I) g₀ 3 3 (i + 1) E₁).toSection x) with hq_def
  have hq_nn : 0 ≤ q := riemannianFiberNormSq_nonneg _ _ _ _ _
  have hre : ∀ ρ : Equiv.Perm (Fin 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
          (reindexCoeffGen (I := I) (M := M) g₀ 3 3 E₁ ρ)).toSection x) = q :=
    fun ρ => rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 3 3 E₁ ρ (i + 1) x
  have hYq : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
      ((iteratedCovGrad (I := I) g₀ 3 3 (i + 1) Y).toSection x) ≤ 3 * q := by
    have hA := hre (Equiv.swap (0 : Fin 3) 2)
    have hB := hre (finRotate 3)
    have hC := hre (Equiv.swap (1 : Fin 3) 2)
    set DA : SmoothCcTensor g₀ 3 (3 + (i + 1)) := iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
      (reindexCoeffGen (I := I) (M := M) g₀ 3 3 E₁ (Equiv.swap (0 : Fin 3) 2)) with hDA_def
    set DB : SmoothCcTensor g₀ 3 (3 + (i + 1)) := iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
      (reindexCoeffGen (I := I) (M := M) g₀ 3 3 E₁ (finRotate 3)) with hDB_def
    set DC : SmoothCcTensor g₀ 3 (3 + (i + 1)) := iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
      (reindexCoeffGen (I := I) (M := M) g₀ 3 3 E₁ (Equiv.swap (1 : Fin 3) 2)) with hDC_def
    rw [hYsplit, icgSm, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
      Pi.smul_apply, riemannianFiberNormSq_smul, iteratedCovGrad_sub, iteratedCovGrad_add]
    rw [show ((DA + DB - DC).toSection x) =
        (DA.toSection x + DB.toSection x) - DC.toSection x from by
      rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add]; rfl]
    have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
      (DA.toSection x + DB.toSection x) (DC.toSection x)
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
      (DA.toSection x) (DB.toSection x)
    rw [hC] at hsub
    rw [hA, hB] at hadd
    nlinarith [hq_nn, hsub, hadd]
  -- (4) the insertion's own positive-order jets are an exact-weight grid
  have hE : q ≤ (fr ^ 2 * Cb (i + 1)) * Combinatorics.antidiagonalTupleGrid
      (gridBase (I := I) (M := M) g₀ P x) (i + 1) := by
    have hzero : iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 2
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 :=
      iteratedCovGrad_zero_of_covGrad_zero (I := I) (M := M) g₀ 3 3 _
        (sieZero (I := I) (M := M) g₀ 2) i
    have hsplit : iteratedCovGrad (I := I) g₀ 3 3 (i + 1) E₁ =
        iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)) := by
      rw [hE₁_def, sieSplit (I := I) (M := M) g₀ g₁ 2, iteratedCovGrad_add, hzero, add_zero]
    rw [hq_def, hsplit]
    have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 2
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) (i + 1) x
    have h2 := hCb g₁ P htie hδ_le hδ0 hδ (i + 1) x
    have hgrideq : (∑ n ∈ Finset.range (i + 1 + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n (i + 1),
          ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        Combinatorics.antidiagonalTupleGrid (gridBase (I := I) (M := M) g₀ P x) (i + 1) := rfl
    rw [hgrideq] at h2
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 2
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
        ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 1 1 (i + 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) := h1
      _ ≤ fr ^ 2 * (Cb (i + 1) * Combinatorics.antidiagonalTupleGrid
            (gridBase (I := I) (M := M) g₀ P x) (i + 1)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (fr ^ 2 * Cb (i + 1)) * Combinatorics.antidiagonalTupleGrid
            (gridBase (I := I) (M := M) g₀ P x) (i + 1) := by ring
  rw [hiso]
  have hgnn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGrid
      (gridBase (I := I) (M := M) g₀ P x) (i + 1) :=
    Combinatorics.antidiagonalTupleGrid_nonneg _ (gridBase_nn (I := I) (M := M) g₀ P x) _
  nlinarith [hYq, hE, hgnn]

set_option linter.unusedVariables false in
/-- **The covariant derivative of the transparent Koszul coefficient is a
once-marked arm at its own level.**

`clAtgw` says `connLowOp` is unmarked at level `i`; this says `∇(connLowOp)` is
once *marked* at level `i` — not merely unmarked at level `i + 1`, which is one
level over the tame budget and is what blocked the `∇A ⋆ ∇T` arm.  It is the
marked sibling of the `capOfArm` step inside `ricciDACap`, and the δ-anchor
`|P|²_∞ ≤ 1` is the only extra hypothesis (it is what `mkOfAtg` spends). -/
private theorem clCovMk (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ 1),
        HasMarkWin (I := I) (M := M) g₀ P
          (covGrad (I := I) (M := M) g₀ 3 3 (connLowOp (I := I) (M := M) g₀ g₁)) 1 K := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := clExact (I := I) (M := M) g₀ hδ₀
  refine ⟨fun i => C i * Combinatorics.antidiagonalTupleGridCount (i + 1), fun i =>
    mul_nonneg (hC_nn i) (Combinatorics.antidiagonalTupleGridCount_nonneg _), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0
  refine mkOfAtg (I := I) (M := M) g₀ P hP0 _ hC_nn (fun i x => ?_)
  rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 3 3 i
    (connLowOp (I := I) (M := M) g₀ g₁) x]
  exact hC g₁ P htie hδ_le hδ0 hδ i x

set_option linter.unusedVariables false in
/-- **Twice-marked window of the transferred lower Ricci Palatini arm.**

`ricciDALow g₀ g₁ P = daContr g₀ g₁ (dagLowOp g₀ g₁ ⋆ ∇P)` with
`dagLowOp = permCoeff(daPermA) ⋆ ∇(connLowOp)`.  Both factors of the `(0,4)`
argument carry exactly one derivative of the state — `∇(connLowOp)` by `clCovMk`
and `∇P` by `mkOfDP` — so the argument is TWICE marked, and every other factor of
the Palatini normal form (`permCoeff`, `mvPairTraceOp g₀ g₀`, the inserted full
raised endomorphism) is unmarked.  This is `ricciDACap` with `capOfArm ↦ clCovMk`,
`capOfDP ↦ mkOfDP` and the `cap`-calculus replaced by the marked one; the payoff
is that no constant carries a `Λ`-degree growing with the order. -/
theorem ricciDAMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ 1),
        HasMarkWin (I := I) (M := M) g₀ P
          (ricciDALow (I := I) (M := M) g₀ g₁ P) 2 K := by
  classical
  obtain ⟨KCov, hKCov_nn, hcov⟩ := clCovMk (I := I) (M := M) g₀ hδ₀
  obtain ⟨Ce1, hCe1_nn, hce1⟩ := endoAtgw (I := I) (M := M) g₀ hδ₀ 1
  choose SA hSA_nn hSA using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (4 + i)
      (iteratedCovGrad (I := I) g₀ 4 4 i (permCoeff (I := I) (M := M) g₀ daPermA)))
  choose SM hSM_nn hSM using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (2 + i)
      (iteratedCovGrad (I := I) g₀ 6 2 i (mvPairTraceOp (I := I) (M := M) g₀ g₀)))
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KDag : ℕ → ℝ := foldConst (E := E) 0 0 SA KCov with hKDag_def
  have hKDag_nn : ∀ i, 0 ≤ KDag i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hSA_nn hKCov_nn i
  set KG : ℕ → ℝ := foldConst (E := E) 0 0 KDag (fun _ => 1) with hKG_def
  have hKG_nn : ∀ i, 0 ≤ KG i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hKDag_nn (fun _ => zero_le_one) i
  set KX : ℕ → ℝ := fun i => fr ^ 2 * KG i with hKX_def
  have hKX_nn : ∀ i, 0 ≤ KX i := fun i => mul_nonneg (pow_nonneg hfr_nn 2) (hKG_nn i)
  set KRK : ℕ → ℝ := foldConst (E := E) 0 0 SM KX with hKRK_def
  have hKRK_nn : ∀ i, 0 ≤ KRK i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hSM_nn hKX_nn i
  set KMo : ℕ → ℝ := foldConst (E := E) 0 0 KRK Ce1 with hKMo_def
  have hKMo_nn : ∀ i, 0 ≤ KMo i := fun i =>
    foldConst_nn (E := E) (u := 0) (v := 0) hKRK_nn hCe1_nn i
  refine ⟨fun i => 2 * KMo i + 2 * KMo i, fun i => by have := hKMo_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0
  have hA : HasMarkWin (I := I) (M := M) g₀ P
      (permCoeff (I := I) (M := M) g₀ daPermA) 0 SA :=
    mkOfBnd (I := I) (M := M) g₀ P _ hSA_nn (fun i x => hSA i x)
  have hM : HasMarkWin (I := I) (M := M) g₀ P
      (mvPairTraceOp (I := I) (M := M) g₀ g₀) 0 SM :=
    mkOfBnd (I := I) (M := M) g₀ P _ hSM_nn (fun i x => hSM i x)
  have hCov : HasMarkWin (I := I) (M := M) g₀ P
      (covGrad (I := I) (M := M) g₀ 3 3 (connLowOp (I := I) (M := M) g₀ g₁)) 1 KCov :=
    hcov g₁ P htie hδ_le hδ0 hδ hP0
  have hDag : HasMarkWin (I := I) (M := M) g₀ P
      (dagLowOp (I := I) (M := M) g₀ g₁) 1 KDag :=
    mkApp (I := I) (M := M) g₀ P _ _ hSA_nn hKCov_nn hA hCov
  have hDP : HasMarkWin (I := I) (M := M) g₀ P
      (covGrad (I := I) (M := M) g₀ 0 2 P) 1 (fun _ => 1) :=
    mkOfDP (I := I) (M := M) g₀ P
  have hG : HasMarkWin (I := I) (M := M) g₀ P
      (appCcRS (I := I) (M := M) g₀ 0 3 4
        (dagLowOp (I := I) (M := M) g₀ g₁)
        (covGrad (I := I) (M := M) g₀ 0 2 P)) 2 KG :=
    mkApp (I := I) (M := M) g₀ P _ _ hKDag_nn (fun _ => zero_le_one) hDag hDP
  have hE1 : HasMarkWin (I := I) (M := M) g₀ P
      (slotInsertEndoCc (I := I) (M := M) g₀ 1
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) 0 Ce1 :=
    mkOfWin (I := I) (M := M) g₀ P _ (fun i y => hce1 g₁ P htie hδ_le hδ0 hδ i y)
  have hMono : ∀ σ : Equiv.Perm (Fin 4),
      HasMarkWin (I := I) (M := M) g₀ P
        (daMono (I := I) (M := M) g₀ g₁
          (appCcRS (I := I) (M := M) g₀ 0 3 4
            (dagLowOp (I := I) (M := M) g₀ g₁)
            (covGrad (I := I) (M := M) g₀ 0 2 P)) σ) 2 KMo := by
    intro σ
    have hRK : HasMarkWin (I := I) (M := M) g₀ P
        (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₀
          (appCcRS (I := I) (M := M) g₀ 0 3 4
            (dagLowOp (I := I) (M := M) g₀ g₁)
            (covGrad (I := I) (M := M) g₀ 0 2 P)) σ) 2 KRK := by
      refine mkCongr (I := I) (M := M) g₀ P
        (refoldKernelContractionMonomialField_eq_mvPairTraceRefold (I := I) (M := M) g₀ g₀
          (appCcRS (I := I) (M := M) g₀ 0 3 4
            (dagLowOp (I := I) (M := M) g₀ g₁)
            (covGrad (I := I) (M := M) g₀ 0 2 P)) σ) ?_
      exact mkApp (I := I) (M := M) g₀ P _ _ hSM_nn hKX_nn hM
        (mkDdc (I := I) (M := M) g₀ P sigmaE
          (mkIter (I := I) (M := M) g₀ P 2
            (mkDdc0 (I := I) (M := M) g₀ P _ hG)))
    exact mkApp (I := I) (M := M) g₀ P _ _ hKRK_nn hCe1_nn hRK hE1
  exact mkSub (I := I) (M := M) g₀ P (hMono daPermA) (hMono daPermB)

set_option linter.unusedVariables false in
/-- **The Palatini `∇A ⋆ ∇P` arm's tame `L²` jet bound.**

```
‖∇ⁱ(ricciDALow g₀ g₁ P)‖² ≤ (K₀ i + K₂ i · ‖P‖²_{H³}) · (1 + ∑_{j<i+2} ‖∇ʲP‖²)
```

with `K₀, K₂` chosen before the state — background metric and order only, no
Sobolev radius, no cap, and exactly ONE power of `‖P‖²_{H³}` (spelled
`∑_{j<3} ‖∇^{1+j}P‖²`, `gradCapLin`'s convention).  The δ-anchor `|P|²_∞ ≤ 1` is
the only hypothesis on the state beyond the standard fibre-operator bound.

Compare `ricciDACap`-then-`capJet`: same left-hand side, but a constant whose
`Λ`-degree grows with the order.  This is the sixth and last of the arm jets that
`selfLow_split` needs; it is the exact sibling of `ricciAAJet`. -/
theorem ricciDAJet (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciDALow (I := I) (M := M) g₀ g₁ P)‖ ^ 2 ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨KA, hKA_nn, hDA⟩ := ricciDAMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨K0', hK0'_nn, hjet⟩ := markJet (I := I) (M := M) g₀
  obtain ⟨cg, hcg_nn, hcg⟩ := gradCapLin (I := I) (M := M) hDim g₀
  refine ⟨fun i => KA i * K0' i, fun i => KA i * K0' i * cg,
    fun i => mul_nonneg (hKA_nn i) (hK0'_nn i),
    fun i => mul_nonneg (mul_nonneg (hKA_nn i) (hK0'_nn i)) hcg_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 i
  set H3 : ℝ := ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2 with hH3_def
  have hH3_nn : 0 ≤ H3 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  set Λ₁ : ℝ := Real.sqrt (cg * H3) with hΛ₁_def
  have hΛ₁0 : 0 ≤ Λ₁ := Real.sqrt_nonneg _
  have hΛ₁sq : Λ₁ ^ 2 = cg * H3 := Real.sq_sqrt (mul_nonneg hcg_nn hH3_nn)
  have hcap : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2 := by
    intro x
    rw [hΛ₁sq]
    exact hcg P x
  have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
      (P.toSection x) ≤ (1 : ℝ) ^ 2 := by
    intro x; rw [one_pow]; exact hP0 x
  have hgb : ∀ x : M, gridBase (I := I) (M := M) g₀ P x 0 ≤ 1 := by
    intro x
    simpa [gridBase] using hP0 x
  have hres := hjet P (Λ₀ := 1) zero_le_one (le_refl _) hΛ₁0 hsup hcap
    (ricciDALow (I := I) (M := M) g₀ g₁ P) hKA_nn
    (hDA g₁ P htie hδ_le hδ0 hδ hgb) i
  refine hres.trans (le_of_eq ?_)
  rw [hΛ₁sq]
  ring

end DifferentialGeometry.Integral.Connection

end
