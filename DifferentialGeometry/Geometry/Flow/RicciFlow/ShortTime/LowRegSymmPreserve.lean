import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseTime

/-!
# Spectral symmetrization is eigenblock diagonal, and the rough solution stays symmetric

The solver-side symmetry brick of the low-regularity Ricci--DeTurck lane.

`symmHs` is the continuous extension of smooth slot symmetrization to the
spectral Sobolev scale, and the maximal-regularity Duhamel machinery acts
*diagonally* on the rough-Laplacian eigenbasis (`homModeCoeff` multiplies the
`i`-th coordinate by `e^{-λᵢ t}`, `solModeCoeff` convolves it against the same
kernel).  The two therefore commute as soon as `symmHs` does not mix different
eigenvalues.  That is exactly what slot-swap equivariance of the rough
Laplacian gives (`tensorL2Coeff_toL2_swap_eigenSmooth_eq_zero_of_fst_ne`), and
eigenvalue blocks are *finite* (`TensorEigenIdx` is a sigma type with
`Fin`-fibres), so the commutation becomes a finite coefficient computation.

Main results:

* `symmHs_coeff` — the eigenbasis matrix of `symmHs` is block diagonal:
  `(symmHs u).coeff i = ∑ j ∈ eigenBlock i, symmMat i j * u.coeff j`, where the
  block sum runs only over indices carrying the same eigenvalue as `i`.
* `symmTimeL2` / `timeModeCoeff_symmTimeL2` — the pointwise action of `symmHs`
  on `L²([0,T]; Hˢ)` and its per-mode block expansion.
* `symmHs_solField_comm`, `symmHs_duhamel_comm` — spectral symmetrization
  commutes with the maximal-regularity solution field and with the affine
  Duhamel field.
* `duhamel_symm_ae` / `lowreg_sol_symm` — the Duhamel field of a spectrally
  symmetric forcing (and symmetric initial datum, in particular the zero datum
  used by `lowreg_partial_sol`) is spectrally symmetric almost everywhere.
  This is the `hsymm` input of `lowRadial_eq_self_along_sol`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable (g : SmoothRiemannianMetric I M)

/-! ## Eigenbasis helpers

The four lemmas of this section are local copies of `private` helpers of
`Analysis/Spectral/Tensor/Spectrum/SlotSwapEquivariance.lean`; they are
reproved here rather than imported because the originals are file-private. -/

omit [BoundarylessManifold I M] in
private lemma l2_ext_coeff {U V : TensorL2 0 2 g}
    (h : ∀ k, tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g) U k =
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g) V k) :
    U = V := by
  apply (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (hCompact (I := I) (M := M) g)).repr.injective
  ext k
  exact h k

omit [BoundarylessManifold I M] in
private lemma eigenbasis_toL2
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2) :
    tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
        (hCompact (I := I) (M := M) g) i =
      SmoothCcTensor.toL2 (eigenSmooth (I := I) (M := M) g i) := by
  rw [tensorResolventHilbertEigenbasisSigma_apply (I := I) (M := M)
      (hCompact (I := I) (M := M) g) i,
    SmoothCcTensor.toL2_apply (eigenSmooth (I := I) (M := M) g i)]
  exact (eigenvectorSmooth_toL2 (I := I) (M := M) g 0 2 i).symm

private lemma toL2_symmS (X : SmoothCcTensor g 0 2) :
    SmoothCcTensor.toL2 (symmS (I := I) (M := M) g X) =
      (1 / 2 : ℝ) • (SmoothCcTensor.toL2 X +
        SmoothCcTensor.toL2
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X)) := by
  simp only [symmS]
  rw [map_smul, map_add]

private lemma inner_toL2_swap (A B : SmoothCcTensor g 0 2) :
    ⟪SmoothCcTensor.toL2
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) A),
      SmoothCcTensor.toL2 B⟫_ℝ =
    ⟪SmoothCcTensor.toL2 A,
      SmoothCcTensor.toL2
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) B)⟫_ℝ := by
  rw [SmoothCcTensor.inner_toL2, SmoothCcTensor.inner_toL2]
  exact inner_domDomCongrSection_swap (I := I) (M := M) g A B

private lemma coeff_toL2_swap (X : SmoothCcTensor g 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) X)) i =
      ⟪SmoothCcTensor.toL2 (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
          (eigenSmooth (I := I) (M := M) g i)),
        SmoothCcTensor.toL2 X⟫_ℝ := by
  rw [tensorL2Coeff_eq_inner, eigenbasis_toL2 (I := I) (M := M) g i]
  exact (inner_toL2_swap (I := I) (M := M) g
    (eigenSmooth (I := I) (M := M) g i) X).symm

/-! ## The eigenvalue block and the symmetrization matrix -/

/-- The eigenvalue block of the eigen-index `i`: the (finite) set of eigen-indices
carrying the same eigenvalue label `i.1`. -/
def eigenBlock (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :=
  Finset.map ⟨Sigma.mk i.1, sigma_mk_injective⟩ Finset.univ

omit [BoundarylessManifold I M] in
@[simp] theorem mem_eigenBlock
    {i j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2} :
    j ∈ eigenBlock (I := I) (M := M) g i ↔ j.1 = i.1 := by
  classical
  simp only [eigenBlock, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨c, rfl⟩
    rfl
  · intro hj
    obtain ⟨μ, c⟩ := j
    have hμ : μ = i.1 := hj
    subst hμ
    exact ⟨c, rfl⟩

omit [BoundarylessManifold I M] in
/-- The eigenvalue is constant along an eigenvalue block. -/
theorem lambda_of_mem_eigenBlock
    {i j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2}
    (hj : j ∈ eigenBlock (I := I) (M := M) g i) :
    TensorEigenIdx.lambda (I := I) (M := M) j =
      TensorEigenIdx.lambda (I := I) (M := M) i :=
  congrArg (fun μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g 0 2 =>
    tensorLaplacianEigenvalueOf μ.val) ((mem_eigenBlock (I := I) (M := M) g).mp hj)

/-- The `(i, j)` entry of spectral symmetrization against the rough-Laplacian
eigenbasis: the `j`-th `L²` coordinate of the symmetrized `i`-th eigensection. -/
def symmMat (i j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
    (I := I) (M := M) g 0 2) : ℝ :=
  tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
    (SmoothCcTensor.toL2 (symmS (I := I) (M := M) g
      (eigenSmooth (I := I) (M := M) g i))) j

/-- **Slot symmetrization does not mix eigenvalues.**  The symmetrization matrix
vanishes off the eigenvalue block: this is slot-swap equivariance of the rough
Laplacian. -/
theorem symmMat_eq_zero
    {i j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2}
    (hij : j.1 ≠ i.1) : symmMat (I := I) (M := M) g i j = 0 := by
  have hne : j ≠ i := fun h => hij (by rw [h])
  have hdiag : tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
      (SmoothCcTensor.toL2 (eigenSmooth (I := I) (M := M) g i)) j = 0 := by
    rw [SmoothCcTensor.toL2_apply,
      tensorL2Coeff_ofCompact_eigenSmooth (I := I) (M := M) g j i, if_neg hne]
  have hswap := tensorL2Coeff_toL2_swap_eigenSmooth_eq_zero_of_fst_ne
    (I := I) (M := M) g i j (fun h => hij h.symm)
  rw [symmMat, toL2_symmS (I := I) (M := M) g, tensorL2Coeff_smul,
    tensorL2Coeff_add, hdiag, hswap]
  ring

omit [BoundarylessManifold I M] in
open scoped Classical in
private lemma coeff_block_sum
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2)
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (k : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (∑ j ∈ eigenBlock (I := I) (M := M) g i, c j •
          tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (hCompact (I := I) (M := M) g) j) k =
      (if k ∈ eigenBlock (I := I) (M := M) g i then c k else 0) := by
  classical
  rw [tensorL2Coeff_eq_inner, inner_sum]
  have h_term : ∀ j ∈ eigenBlock (I := I) (M := M) g i,
      ⟪tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
          (hCompact (I := I) (M := M) g) k,
        c j • tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
          (hCompact (I := I) (M := M) g) j⟫_ℝ =
      (if k = j then c j else 0) := by
    intro j _
    rw [inner_smul_right]
    have horth := (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
      (hCompact (I := I) (M := M) g)).orthonormal
    rw [orthonormal_iff_ite] at horth
    rw [horth k j]
    by_cases h : k = j <;> simp [h]
  rw [Finset.sum_congr rfl h_term]
  by_cases hkS : k ∈ eigenBlock (I := I) (M := M) g i
  · rw [Finset.sum_eq_single k]
    · simp [hkS]
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm)]
    · intro h
      exact absurd hkS h
  · rw [if_neg hkS, Finset.sum_eq_zero]
    intro j hj
    rw [if_neg (fun h => hkS (by rw [h]; exact hj))]

/-- The symmetrized eigensection is the finite combination of the eigenbasis
vectors of its own eigenvalue block. -/
theorem toL2_symmS_eigen_eq_sum
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2) :
    SmoothCcTensor.toL2 (symmS (I := I) (M := M) g
        (eigenSmooth (I := I) (M := M) g i)) =
      ∑ j ∈ eigenBlock (I := I) (M := M) g i,
        symmMat (I := I) (M := M) g i j •
          tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (hCompact (I := I) (M := M) g) j := by
  classical
  refine l2_ext_coeff (I := I) (M := M) g (fun k => ?_)
  rw [coeff_block_sum (I := I) (M := M) g i
    (fun j => symmMat (I := I) (M := M) g i j) k]
  by_cases hk : k ∈ eigenBlock (I := I) (M := M) g i
  · rw [if_pos hk]
    rfl
  · rw [if_neg hk]
    exact symmMat_eq_zero (I := I) (M := M) g
      (fun h => hk ((mem_eigenBlock (I := I) (M := M) g).mpr h))

/-- **Block expansion of smooth slot symmetrization in the eigenbasis.** -/
theorem symmS_toL2_coeff (X : SmoothCcTensor g 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 (symmS (I := I) (M := M) g X)) i =
      ∑ j ∈ eigenBlock (I := I) (M := M) g i,
        symmMat (I := I) (M := M) g i j *
          tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 X) j := by
  classical
  have hL : tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
      (SmoothCcTensor.toL2 (symmS (I := I) (M := M) g X)) i =
      (1 / 2 : ℝ) *
        (⟪SmoothCcTensor.toL2 (eigenSmooth (I := I) (M := M) g i),
            SmoothCcTensor.toL2 X⟫_ℝ +
          ⟪SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1) (eigenSmooth (I := I) (M := M) g i)),
            SmoothCcTensor.toL2 X⟫_ℝ) := by
    rw [toL2_symmS (I := I) (M := M) g X, tensorL2Coeff_smul, tensorL2Coeff_add,
      coeff_toL2_swap (I := I) (M := M) g X i, tensorL2Coeff_eq_inner,
      eigenbasis_toL2 (I := I) (M := M) g i]
  have hR : ⟪SmoothCcTensor.toL2 (symmS (I := I) (M := M) g
          (eigenSmooth (I := I) (M := M) g i)),
        SmoothCcTensor.toL2 X⟫_ℝ =
      (1 / 2 : ℝ) *
        (⟪SmoothCcTensor.toL2 (eigenSmooth (I := I) (M := M) g i),
            SmoothCcTensor.toL2 X⟫_ℝ +
          ⟪SmoothCcTensor.toL2 (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1) (eigenSmooth (I := I) (M := M) g i)),
            SmoothCcTensor.toL2 X⟫_ℝ) := by
    rw [toL2_symmS (I := I) (M := M) g (eigenSmooth (I := I) (M := M) g i),
      real_inner_smul_left, inner_add_left]
  rw [hL, ← hR, toL2_symmS_eigen_eq_sum (I := I) (M := M) g i, sum_inner]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [real_inner_smul_left, ← tensorL2Coeff_eq_inner]

/-- **Spectral symmetrization is block diagonal.**  For every nonnegative Sobolev
order, the `i`-th eigen-coordinate of `symmHs u` is a finite combination of the
coordinates of `u` inside the eigenvalue block of `i`. -/
theorem symmHs_coeff {σ : ℝ} (hσ : 0 ≤ σ)
    (u : tensorHs (I := I) (M := M) g 0 2 σ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2) :
    (symmHs (I := I) (M := M) g hσ u).coeff i =
      ∑ j ∈ eigenBlock (I := I) (M := M) g i,
        symmMat (I := I) (M := M) g i j * u.coeff j := by
  classical
  have hdense : DenseRange (ccToHsLin (I := I) (M := M) g 2 σ) :=
    ccToHsLin_dense (I := I) (M := M) g 2 hσ
  refine hdense.induction_on u (isClosed_eq ?_ ?_) ?_
  · exact (tensorHsCoeffL (I := I) (M := M) (a := σ) i).continuous.comp
      (symmHs (I := I) (M := M) g hσ).continuous
  · refine continuous_finset_sum _ (fun j _ => ?_)
    exact (tensorHsCoeffL (I := I) (M := M) (a := σ) j).continuous.const_mul _
  · intro X
    rw [symmHs_core (I := I) (M := M) g hσ X]
    simp only [ccToHsLin_apply, ccTensorToHs_coeff]
    exact symmS_toL2_coeff (I := I) (M := M) g X i

/-- The spectrally symmetric states form a closed set, so spectral symmetry
passes to limits.  This is what lets a nonlinearity that is symmetric on a
dense smooth core stay symmetric after continuous extension. -/
theorem isClosed_symmFixed {σ : ℝ} (hσ : 0 ≤ σ) :
    IsClosed {u : tensorHs (I := I) (M := M) g 0 2 σ |
      symmHs (I := I) (M := M) g hσ u = u} :=
  isClosed_eq (symmHs (I := I) (M := M) g hσ).continuous continuous_id

/-- **Smooth symmetry implies spectral symmetry.**  The spectral image of a
slot-symmetric smooth tensor is a fixed point of `symmHs` at every nonnegative
order. -/
theorem symmHs_smoothCc_eq_self {σ : ℝ} (hσ : 0 ≤ σ) (X : SmoothCcTensor g 0 2)
    (hX : symmS (I := I) (M := M) g X = X) :
    symmHs (I := I) (M := M) g hσ
        (smoothCcToTensorHs (I := I) (M := M) g σ X) =
      smoothCcToTensorHs (I := I) (M := M) g σ X := by
  have hEq : smoothCcToTensorHs (I := I) (M := M) g σ X =
      ccToHsLin (I := I) (M := M) g 2 σ X := by
    apply tensorHs.ext
    funext i
    rfl
  rw [hEq, symmHs_core (I := I) (M := M) g hσ X, hX]

/-! ## Pointwise symmetrization on the time-`L²` scale -/

/-- Spectral symmetrization acting pointwise in time on `L²([0,T]; Hˢ)`. -/
def symmTimeL2 {σ : ℝ} (hσ : 0 ≤ σ) (T : ℝ) :
    timeL2 (tensorHs (I := I) (M := M) g 0 2 σ) T →L[ℝ]
      timeL2 (tensorHs (I := I) (M := M) g 0 2 σ) T :=
  (symmHs (I := I) (M := M) g hσ).compLpL 2 (timeMeasure T)

/-- The pointwise-in-time symmetrization is represented a.e. by
`t ↦ symmHs (F t)`. -/
theorem symmTimeL2_coeFn {σ T : ℝ} (hσ : 0 ≤ σ)
    (F : timeL2 (tensorHs (I := I) (M := M) g 0 2 σ) T) :
    symmTimeL2 (I := I) (M := M) g hσ T F =ᵐ[timeMeasure T]
      fun t => symmHs (I := I) (M := M) g hσ (F t) :=
  (symmHs (I := I) (M := M) g hσ).coeFn_compLpL (p := 2) (μ := timeMeasure T) F

/-- A time-`L²` field is a fixed point of the pointwise symmetrization exactly
when it is spectrally symmetric almost everywhere. -/
theorem symmTimeL2_eq_self_iff {σ T : ℝ} (hσ : 0 ≤ σ)
    (F : timeL2 (tensorHs (I := I) (M := M) g 0 2 σ) T) :
    symmTimeL2 (I := I) (M := M) g hσ T F = F ↔
      ∀ᵐ t ∂timeMeasure T, symmHs (I := I) (M := M) g hσ (F t) = F t := by
  constructor
  · intro h
    filter_upwards [symmTimeL2_coeFn (I := I) (M := M) g hσ F] with t ht
    rw [← ht, h]
  · intro h
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [symmTimeL2_coeFn (I := I) (M := M) g hσ F, h] with t ht hh
    rw [ht, hh]

omit [BoundarylessManifold I M] in
private lemma coeFn_smul_sum {ι : Type*} {T : ℝ} (s : Finset ι) (c : ι → ℝ)
    (f : ι → timeL2 ℝ T) :
    ⇑(∑ k ∈ s, c k • f k) =ᵐ[timeMeasure T]
      fun t => ∑ k ∈ s, c k * (f k) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      filter_upwards [MeasureTheory.Lp.coeFn_zero ℝ 2 (timeMeasure T)] with t ht
      simpa using ht
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [MeasureTheory.Lp.coeFn_add (c a • f a) (∑ k ∈ s, c k • f k),
        MeasureTheory.Lp.coeFn_smul (c a) (f a), ih] with t ht1 ht2 ht3
      rw [ht1, Pi.add_apply, ht2, Pi.smul_apply, ht3, Finset.sum_insert ha,
        smul_eq_mul]

/-- **Per-mode block expansion of the pointwise symmetrization.** -/
theorem timeModeCoeff_symmTimeL2 {σ T : ℝ} (hσ : 0 ≤ σ)
    (F : timeL2 (tensorHs (I := I) (M := M) g 0 2 σ) T)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2) :
    timeModeCoeff (I := I) (M := M)
        (symmTimeL2 (I := I) (M := M) g hσ T F) i =
      ∑ j ∈ eigenBlock (I := I) (M := M) g i,
        symmMat (I := I) (M := M) g i j •
          timeModeCoeff (I := I) (M := M) F j := by
  refine MeasureTheory.Lp.ext ?_
  have h4 : ∀ᵐ t ∂timeMeasure T,
      ∀ j ∈ eigenBlock (I := I) (M := M) g i,
        (timeModeCoeff (I := I) (M := M) F j) t = (F t).coeff j :=
    (Filter.eventually_all_finset _).2
      (fun j _ => timeModeCoeff_coeFn (I := I) (M := M) F j)
  filter_upwards [timeModeCoeff_coeFn (I := I) (M := M)
      (symmTimeL2 (I := I) (M := M) g hσ T F) i,
    symmTimeL2_coeFn (I := I) (M := M) g hσ F,
    coeFn_smul_sum (T := T) (eigenBlock (I := I) (M := M) g i)
      (fun j => symmMat (I := I) (M := M) g i j)
      (fun j => timeModeCoeff (I := I) (M := M) F j), h4] with t ht1 ht2 ht3 ht4
  rw [ht1, ht2, ht3, symmHs_coeff (I := I) (M := M) g hσ (F t) i]
  exact Finset.sum_congr rfl (fun j hj => by rw [ht4 j hj])

/-! ## Commutation with the diagonal Duhamel machinery -/

omit [BoundarylessManifold I M] in
private lemma homModeCoeff_coeFn {a T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g 0 2 (a + 2))
    (j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2) :
    ⇑(homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ j) =ᵐ[timeMeasure T]
      fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j) * t) *
        u₀.coeff j :=
  coeFn_ofContinuousOn _

private lemma perModeConv_congr {lam lam' T : ℝ} (h : lam = lam')
    (hlam : 0 ≤ lam) (hlam' : 0 ≤ lam') (hT : 0 ≤ T) (f : timeL2 ℝ T) :
    perModeConvL2 lam hlam hT f = perModeConvL2 lam' hlam' hT f := by
  subst h
  rfl

/-- **Symmetrization commutes with the homogeneous heat-flow coordinate.** -/
theorem symmHs_homModeCoeff {a T : ℝ} (h2 : (0 : ℝ) ≤ a + 2)
    (u₀ : tensorHs (I := I) (M := M) g 0 2 (a + 2))
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2) :
    homModeCoeff (I := I) (M := M) (a := a) (T := T)
        (symmHs (I := I) (M := M) g h2 u₀) i =
      ∑ j ∈ eigenBlock (I := I) (M := M) g i,
        symmMat (I := I) (M := M) g i j •
          homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ j := by
  refine MeasureTheory.Lp.ext ?_
  have h4 : ∀ᵐ t ∂timeMeasure T,
      ∀ j ∈ eigenBlock (I := I) (M := M) g i,
        (homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ j) t =
          Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) j) * t) *
            u₀.coeff j :=
    (Filter.eventually_all_finset _).2
      (fun j _ => homModeCoeff_coeFn (I := I) (M := M) (a := a) (T := T) g u₀ j)
  filter_upwards [homModeCoeff_coeFn (I := I) (M := M) (a := a) (T := T) g
      (symmHs (I := I) (M := M) g h2 u₀) i,
    coeFn_smul_sum (T := T) (eigenBlock (I := I) (M := M) g i)
      (fun j => symmMat (I := I) (M := M) g i j)
      (fun j => homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ j),
    h4] with t ht1 ht2 ht3
  rw [ht1, ht2, symmHs_coeff (I := I) (M := M) g h2 u₀ i, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [ht3 j hj, lambda_of_mem_eigenBlock (I := I) (M := M) g hj]
  ring

/-- **Symmetrization commutes with the per-mode Duhamel coordinate.** -/
theorem symmHs_solModeCoeff {a T : ℝ} (ha : (0 : ℝ) ≤ a) (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2) :
    solModeCoeff (I := I) (M := M) (a := a) hT
        (symmTimeL2 (I := I) (M := M) g ha T f) i =
      ∑ j ∈ eigenBlock (I := I) (M := M) g i,
        symmMat (I := I) (M := M) g i j •
          solModeCoeff (I := I) (M := M) (a := a) hT f j := by
  rw [solModeCoeff, timeModeCoeff_symmTimeL2 (I := I) (M := M) g ha f i, map_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [map_smul, solModeCoeff]
  refine congrArg (fun z => symmMat (I := I) (M := M) g i j • z) ?_
  exact (perModeConv_congr
    (lambda_of_mem_eigenBlock (I := I) (M := M) g hj)
    (tensor_lambda_nonneg (I := I) (M := M) j)
    (tensor_lambda_nonneg (I := I) (M := M) i) hT
    (timeModeCoeff (I := I) (M := M) f j)).symm

/-- **Symmetrization commutes with the homogeneous heat-flow field.** -/
theorem symmHs_homField_comm {a T : ℝ} (h2 : (0 : ℝ) ≤ a + 2) (hT : 0 ≤ T)
    (u₀ : tensorHs (I := I) (M := M) g 0 2 (a + 2)) :
    symmTimeL2 (I := I) (M := M) g h2 T
        (maxRegHomogeneousSolField (I := I) (M := M) a T u₀) =
      maxRegHomogeneousSolField (I := I) (M := M) a T
        (symmHs (I := I) (M := M) g h2 u₀) := by
  refine timeModeCoeff_injective (I := I) (M := M)
    (hCompact (I := I) (M := M) g) (fun i => ?_)
  rw [timeModeCoeff_symmTimeL2 (I := I) (M := M) g h2 _ i,
    maxRegHomogeneousSolField_timeModeCoeff (I := I) (M := M) (a := a) (T := T)
      hT (symmHs (I := I) (M := M) g h2 u₀) i,
    symmHs_homModeCoeff (I := I) (M := M) (a := a) (T := T) g h2 u₀ i]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [maxRegHomogeneousSolField_timeModeCoeff (I := I) (M := M) (a := a) (T := T)
    hT u₀ j]

/-- **Symmetrization commutes with the maximal-regularity solution field.** -/
theorem symmHs_solField_comm {a T : ℝ} (ha : (0 : ℝ) ≤ a)
    (h2 : (0 : ℝ) ≤ a + 2) (hT : 0 ≤ T)
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T) :
    symmTimeL2 (I := I) (M := M) g h2 T
        (maximalRegularitySolField (I := I) (M := M) a hT f) =
      maximalRegularitySolField (I := I) (M := M) a hT
        (symmTimeL2 (I := I) (M := M) g ha T f) := by
  refine timeModeCoeff_injective (I := I) (M := M)
    (hCompact (I := I) (M := M) g) (fun i => ?_)
  rw [timeModeCoeff_symmTimeL2 (I := I) (M := M) g h2 _ i,
    maximalRegularitySolField_timeModeCoeff (I := I) (M := M) (a := a)
      hT (hCompact (I := I) (M := M) g)
      (symmTimeL2 (I := I) (M := M) g ha T f) i,
    symmHs_solModeCoeff (I := I) (M := M) g ha hT f i]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [maximalRegularitySolField_timeModeCoeff (I := I) (M := M) (a := a)
    hT (hCompact (I := I) (M := M) g) f j]

/-- **Symmetrization commutes with the affine Duhamel solution field.**  The
Duhamel field of the symmetrized data is the symmetrization of the Duhamel
field. -/
theorem symmHs_duhamel_comm {a T : ℝ} (ha : (0 : ℝ) ≤ a)
    (h2 : (0 : ℝ) ≤ a + 2) (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g 0 2 (a + 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T) :
    symmTimeL2 (I := I) (M := M) g h2 T
        (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ f) =
      maxRegDuhamelSolField (I := I) (M := M) a hT hT1
        (symmHs (I := I) (M := M) g h2 u₀)
        (symmTimeL2 (I := I) (M := M) g ha T f) := by
  rw [maxRegDuhamelSolField, maxRegDuhamelSolField, map_add,
    symmHs_homField_comm (I := I) (M := M) g h2 hT.le u₀,
    symmHs_solField_comm (I := I) (M := M) g ha h2 hT.le f]

/-! ## The symmetry input of `lowRadial_eq_self_along_sol` -/

/-- **The Duhamel field of spectrally symmetric data is spectrally symmetric.**
This is the honest solver-side statement: it consumes symmetry of the initial
datum and of the forcing, and nothing else. -/
theorem duhamel_symm_ae {a T : ℝ} (ha : (0 : ℝ) ≤ a) (h2 : (0 : ℝ) ≤ a + 2)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g 0 2 (a + 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T)
    (hu₀ : symmHs (I := I) (M := M) g h2 u₀ = u₀)
    (hf : ∀ᵐ t ∂timeMeasure T,
      symmHs (I := I) (M := M) g ha (f t) = f t) :
    ∀ᵐ t ∂timeMeasure T,
      symmHs (I := I) (M := M) g h2
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ f t) =
        maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ f t := by
  have hfL : symmTimeL2 (I := I) (M := M) g ha T f = f :=
    (symmTimeL2_eq_self_iff (I := I) (M := M) g ha f).2 hf
  refine (symmTimeL2_eq_self_iff (I := I) (M := M) g h2 _).1 ?_
  rw [symmHs_duhamel_comm (I := I) (M := M) g ha h2 hT hT1 u₀ f, hu₀, hfL]

/-- **The rough low-regularity solution stays spectrally symmetric.**  With the
zero initial datum used by `lowreg_partial_sol`, spectral symmetry of the
forcing alone makes the Duhamel solution field spectrally symmetric almost
everywhere — exactly the `hsymm` hypothesis of
`lowRadial_eq_self_along_sol`. -/
theorem lowreg_sol_symm {a T : ℝ} (ha : (0 : ℝ) ≤ a) (h2 : (0 : ℝ) ≤ a + 2)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T)
    (hf : ∀ᵐ t ∂timeMeasure T,
      symmHs (I := I) (M := M) g ha (f t) = f t) :
    ∀ᵐ t ∂timeMeasure T,
      symmHs (I := I) (M := M) g h2
          (maxRegDuhamelSolField (I := I) (M := M) a hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 (a + 2)) f t) =
        maxRegDuhamelSolField (I := I) (M := M) a hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 (a + 2)) f t :=
  duhamel_symm_ae (I := I) (M := M) g ha h2 hT hT1 0 f (map_zero _) hf

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
