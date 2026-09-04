import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.SmoothCoefWeakPartialIBP
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Defs
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section

open MeasureTheory Set Filter Topology
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem contDiff_partial
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : E => (fderiv ℝ f x) (EuclideanSpace.single i 1)) := by
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun x : E => fderiv ℝ f x) :=
    (contDiff_infty_iff_fderiv.1 hf).2
  exact ((ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.single i (1 : ℝ))).contDiff).comp hfd

omit [NeZero d] in
private theorem partial_swap
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : E) (i j : Fin d) :
    (fderiv ℝ
      (fun y : E => (fderiv ℝ f y) (EuclideanSpace.single j 1)) x)
        (EuclideanSpace.single i 1) =
      (fderiv ℝ
        (fun y : E => (fderiv ℝ f y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single j 1) := by
  have hdiff : Differentiable ℝ (fderiv ℝ f) :=
    ((contDiff_infty_iff_fderiv.1 hf).2).differentiable (by simp)
  have heval : ∀ k : Fin d,
      fderiv ℝ
          (fun y : E => (fderiv ℝ f y) (EuclideanSpace.single k 1)) x =
        (fderiv ℝ (fderiv ℝ f) x).flip (EuclideanSpace.single k 1) := by
    intro k
    have h := fderiv_clm_apply (𝕜 := ℝ)
      (c := fderiv ℝ f) (u := fun _ : E => EuclideanSpace.single k (1 : ℝ))
      (x := x) (hdiff x) (differentiableAt_const _)
    rw [h, fderiv_const_apply]
    simp
  rw [heval j, heval i]
  have hsymm : IsSymmSndFDerivAt ℝ f x := by
    have hle : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      decide
    exact hf.contDiffAt.isSymmSndFDerivAt (𝕜 := ℝ) hle
  change ((fderiv ℝ (fderiv ℝ f) x).flip (EuclideanSpace.single j 1))
      (EuclideanSpace.single i 1) =
    ((fderiv ℝ (fderiv ℝ f) x).flip (EuclideanSpace.single i 1))
      (EuclideanSpace.single j 1)
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
  exact hsymm (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

omit [NeZero d] in
private theorem second_swap_int
    {Omega : Set E} (hOmega : IsOpen Omega)
    {u : E → ℝ} (hu2 : MemWkp (d := d) 2 2 u Omega)
    (i j : Fin d) {phi : E → ℝ}
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi)
    (hphi_cpt : HasCompactSupport phi) (hphi_sub : tsupport phi ⊆ Omega) :
    (∫ x in Omega,
      chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u Omega) Omega x * phi x
        ∂(volume : Measure E)) =
      ∫ x in Omega,
        chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u Omega) Omega x * phi x
          ∂(volume : Measure E) := by
  have hu1 : DeGiorgi.MemW1p 2 u Omega := hu2.memW1p
  have hui1 : DeGiorgi.MemW1p 2 (chosenWeakPartial' 2 i u Omega) Omega := by
    rw [← MemWkp.one_iff_memW1p]
    exact hu2.chosenWeakPartial_mem i
  have huj1 : DeGiorgi.MemW1p 2 (chosenWeakPartial' 2 j u Omega) Omega := by
    rw [← MemWkp.one_iff_memW1p]
    exact hu2.chosenWeakPartial_mem j
  let phii : E → ℝ := fun x =>
    (fderiv ℝ phi x) (EuclideanSpace.single i 1)
  let phij : E → ℝ := fun x =>
    (fderiv ℝ phi x) (EuclideanSpace.single j 1)
  have hphii : ContDiff ℝ (⊤ : ℕ∞) phii := contDiff_partial hphi i
  have hphij : ContDiff ℝ (⊤ : ℕ∞) phij := contDiff_partial hphi j
  have hphii_cpt : HasCompactSupport phii :=
    hphi_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hphij_cpt : HasCompactSupport phij :=
    hphi_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
  have hphii_sub : tsupport phii ⊆ Omega :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hphi_sub
  have hphij_sub : tsupport phij ⊆ Omega :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1)).trans hphi_sub
  have houter_ij :=
    chosenWeakPartial'_isWeakPartial_of_mem hui1 j phi hphi hphi_cpt hphi_sub
  have hinner_i :=
    chosenWeakPartial'_isWeakPartial_of_mem hu1 i phij hphij hphij_cpt hphij_sub
  have houter_ji :=
    chosenWeakPartial'_isWeakPartial_of_mem huj1 i phi hphi hphi_cpt hphi_sub
  have hinner_j :=
    chosenWeakPartial'_isWeakPartial_of_mem hu1 j phii hphii hphii_cpt hphii_sub
  have hmixed :
      (∫ x in Omega, u x *
        (fderiv ℝ phij x) (EuclideanSpace.single i 1)
          ∂(volume : Measure E)) =
        ∫ x in Omega, u x *
          (fderiv ℝ phii x) (EuclideanSpace.single j 1)
            ∂(volume : Measure E) := by
    refine setIntegral_congr_fun hOmega.measurableSet (fun x _ => ?_)
    rw [partial_swap hphi x i j]
  linarith

omit [NeZero d] in
private theorem integrable_coef_partial
    {Omega : Set E} {a f psi : E → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hf : MemLp f 2 ((volume : Measure E).restrict Omega))
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpsi_cpt : HasCompactSupport psi) (i : Fin d) :
    Integrable (fun x => a x * f x *
      (fderiv ℝ psi x) (EuclideanSpace.single i 1))
      ((volume : Measure E).restrict Omega) := by
  let q : E → ℝ := fun x =>
    a x * (fderiv ℝ psi x) (EuclideanSpace.single i 1)
  have hq_cont : Continuous q :=
    ha.continuous.mul ((hpsi.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hq_cpt : HasCompactSupport q :=
    (hpsi_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)).mul_left
  have hloc := hf.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hint := hloc.integrable_smul_right_of_hasCompactSupport hq_cont hq_cpt
  simpa [q, mul_assoc, mul_comm, mul_left_comm, smul_eq_mul] using hint

private theorem diff_id_of_base
    {Omega : Set E} (hOmega : IsOpen Omega)
    (B : SmoothEllipticBilinearForm d Set.univ)
    {u : E → ℝ} (hu2 : MemWkp (d := d) 2 2 u Omega)
    (l : Fin d) {psi : E → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpsi_cpt : HasCompactSupport psi) (hpsi_sub : tsupport psi ⊆ Omega)
    {r : ℝ}
    (hbase :
      (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
        B.a x i j * chosenWeakPartial' 2 j u Omega x *
          (fderiv ℝ
            (fun y : E => (fderiv ℝ psi y) (EuclideanSpace.single l 1)) x)
            (EuclideanSpace.single i 1)
        ∂(volume : Measure E)) = r) :
    (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
      B.a x i j *
        chosenWeakPartial' 2 j (chosenWeakPartial' 2 l u Omega) Omega x *
        (fderiv ℝ psi x) (EuclideanSpace.single i 1)
      ∂(volume : Measure E)) =
      -(∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
        (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
          chosenWeakPartial' 2 j u Omega x *
          (fderiv ℝ psi x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E)) - r := by
  classical
  have hu1 : DeGiorgi.MemW1p 2 u Omega := hu2.memW1p
  have hbase_swap :
      (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
        B.a x i j * chosenWeakPartial' 2 j u Omega x *
          (fderiv ℝ
            (fun y : E => (fderiv ℝ psi y) (EuclideanSpace.single i 1)) x)
            (EuclideanSpace.single l 1)
        ∂(volume : Measure E)) = r := by
    rw [← hbase]
    refine setIntegral_congr_fun hOmega.measurableSet (fun x _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [partial_swap hpsi x i l]
  have hDu1 : ∀ j : Fin d,
      DeGiorgi.MemW1p 2 (chosenWeakPartial' 2 j u Omega) Omega := by
    intro j
    rw [← MemWkp.one_iff_memW1p]
    exact hu2.chosenWeakPartial_mem j
  have hDl1 : DeGiorgi.MemW1p 2 (chosenWeakPartial' 2 l u Omega) Omega := hDu1 l
  have hpair : ∀ i j : Fin d,
      (∫ x in Omega,
        B.a x i j * chosenWeakPartial' 2 j u Omega x *
          (fderiv ℝ
            (fun y : E => (fderiv ℝ psi y) (EuclideanSpace.single i 1)) x)
            (EuclideanSpace.single l 1)
        ∂(volume : Measure E)) =
      -((∫ x in Omega,
          (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
            chosenWeakPartial' 2 j u Omega x *
            (fderiv ℝ psi x) (EuclideanSpace.single i 1)
          ∂(volume : Measure E)) +
        ∫ x in Omega,
          B.a x i j *
            chosenWeakPartial' 2 l (chosenWeakPartial' 2 j u Omega) Omega x *
            (fderiv ℝ psi x) (EuclideanSpace.single i 1)
          ∂(volume : Measure E)) := by
    intro i j
    let psii : E → ℝ := fun x =>
      (fderiv ℝ psi x) (EuclideanSpace.single i 1)
    have hpsii : ContDiff ℝ (⊤ : ℕ∞) psii := contDiff_partial hpsi i
    have hpsii_cpt : HasCompactSupport psii :=
      hpsi_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
    have hpsii_sub : tsupport psii ⊆ Omega :=
      (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hpsi_sub
    exact integral_smul_weak_partial_eq hOmega (B.smooth_a i j)
      (fun K _ hK =>
        (chosenWeakPartial'_memLp_of_mem hu1 j).mono_measure
          (Measure.restrict_mono_set volume hK))
      (fun k K _ hK =>
        (chosenWeakPartial'_memLp_of_mem (hDu1 j) k).mono_measure
          (Measure.restrict_mono_set volume hK))
      (fun k => chosenWeakPartial'_isWeakPartial_of_mem (hDu1 j) k) l
      hpsii hpsii_cpt hpsii_sub
  have hpair_swap : ∀ i j : Fin d,
      (∫ x in Omega,
        B.a x i j *
          chosenWeakPartial' 2 l (chosenWeakPartial' 2 j u Omega) Omega x *
          (fderiv ℝ psi x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E)) =
      ∫ x in Omega,
        B.a x i j *
          chosenWeakPartial' 2 j (chosenWeakPartial' 2 l u Omega) Omega x *
          (fderiv ℝ psi x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E) := by
    intro i j
    let theta : E → ℝ := fun x =>
      B.a x i j * (fderiv ℝ psi x) (EuclideanSpace.single i 1)
    have htheta : ContDiff ℝ (⊤ : ℕ∞) theta :=
      (B.smooth_a i j).mul (contDiff_partial hpsi i)
    have htheta_cpt : HasCompactSupport theta :=
      (hpsi_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)).mul_left
    have htheta_sub : tsupport theta ⊆ Omega :=
      (tsupport_smul_subset_right (fun x : E => B.a x i j)
        (fun x : E => (fderiv ℝ psi x) (EuclideanSpace.single i 1))).trans
          ((tsupport_fderiv_apply_subset ℝ
            (EuclideanSpace.single i 1)).trans hpsi_sub)
    simpa [theta, mul_assoc, mul_comm, mul_left_comm] using
      second_swap_int hOmega hu2 j l htheta htheta_cpt htheta_sub
  have hDB : ∀ i j : Fin d,
      ContDiff ℝ (⊤ : ℕ∞)
        (fun x : E => (fderiv ℝ (fun y : E => B.a y i j) x)
          (EuclideanSpace.single l 1)) :=
    fun i j => contDiff_partial (B.smooth_a i j) l
  have hDuLp : ∀ j : Fin d,
      MemLp (chosenWeakPartial' 2 j u Omega) 2
        ((volume : Measure E).restrict Omega) :=
    fun j => chosenWeakPartial'_memLp_of_mem hu1 j
  have hDLp : ∀ j : Fin d,
      MemLp (chosenWeakPartial' 2 j (chosenWeakPartial' 2 l u Omega) Omega) 2
        ((volume : Measure E).restrict Omega) :=
    fun j => chosenWeakPartial'_memLp_of_mem hDl1 j
  have hpsii : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
      (fun x : E => (fderiv ℝ psi x) (EuclideanSpace.single i 1)) :=
    fun i => contDiff_partial hpsi i
  have hpsii_cpt : ∀ i : Fin d, HasCompactSupport
      (fun x : E => (fderiv ℝ psi x) (EuclideanSpace.single i 1)) :=
    fun i => hpsi_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hL_int : ∀ i j : Fin d, Integrable (fun x =>
      B.a x i j * chosenWeakPartial' 2 j u Omega x *
        (fderiv ℝ
          (fun y : E => (fderiv ℝ psi y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single l 1))
      ((volume : Measure E).restrict Omega) :=
    fun i j => integrable_coef_partial (B.smooth_a i j) (hDuLp j)
      (hpsii i) (hpsii_cpt i) l
  have hC_int : ∀ i j : Fin d, Integrable (fun x =>
      (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
        chosenWeakPartial' 2 j u Omega x *
        (fderiv ℝ psi x) (EuclideanSpace.single i 1))
      ((volume : Measure E).restrict Omega) :=
    fun i j => integrable_coef_partial (hDB i j) (hDuLp j)
      hpsi hpsi_cpt i
  have hH_int : ∀ i j : Fin d, Integrable (fun x =>
      B.a x i j *
        chosenWeakPartial' 2 j (chosenWeakPartial' 2 l u Omega) Omega x *
        (fderiv ℝ psi x) (EuclideanSpace.single i 1))
      ((volume : Measure E).restrict Omega) :=
    fun i j => integrable_coef_partial (B.smooth_a i j) (hDLp j)
      hpsi hpsi_cpt i
  have sum_integral : ∀
      (F : Fin d → Fin d → E → ℝ),
      (∀ i j, Integrable (F i j) ((volume : Measure E).restrict Omega)) →
      (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d, F i j x
        ∂(volume : Measure E)) =
        ∑ i : Fin d, ∑ j : Fin d,
          ∫ x in Omega, F i j x ∂(volume : Measure E) := by
    intro F hF
    rw [integral_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => hF i j))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finset_sum _ (fun j _ => hF i j)]
  have hsum_pair :
      (∑ i : Fin d, ∑ j : Fin d, ∫ x in Omega,
        B.a x i j * chosenWeakPartial' 2 j u Omega x *
          (fderiv ℝ
            (fun y : E => (fderiv ℝ psi y) (EuclideanSpace.single i 1)) x)
            (EuclideanSpace.single l 1)
        ∂(volume : Measure E)) =
      -((∑ i : Fin d, ∑ j : Fin d, ∫ x in Omega,
          (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
            chosenWeakPartial' 2 j u Omega x *
            (fderiv ℝ psi x) (EuclideanSpace.single i 1)
          ∂(volume : Measure E)) +
        ∑ i : Fin d, ∑ j : Fin d, ∫ x in Omega,
          B.a x i j *
            chosenWeakPartial' 2 l (chosenWeakPartial' 2 j u Omega) Omega x *
            (fderiv ℝ psi x) (EuclideanSpace.single i 1)
          ∂(volume : Measure E)) := by
    simp_rw [hpair]
    simp_rw [neg_add, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hL_eq : (∑ i : Fin d, ∑ j : Fin d, ∫ x in Omega,
      B.a x i j * chosenWeakPartial' 2 j u Omega x *
        (fderiv ℝ
          (fun y : E => (fderiv ℝ psi y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single l 1)
      ∂(volume : Measure E)) = r := by
    rw [← sum_integral _ hL_int]
    exact hbase_swap
  have hraw_eq :
      (∑ i : Fin d, ∑ j : Fin d, ∫ x in Omega,
        B.a x i j *
          chosenWeakPartial' 2 l (chosenWeakPartial' 2 j u Omega) Omega x *
          (fderiv ℝ psi x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E)) =
      -(∑ i : Fin d, ∑ j : Fin d, ∫ x in Omega,
        (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
          chosenWeakPartial' 2 j u Omega x *
          (fderiv ℝ psi x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E)) - r := by
    linarith [hsum_pair, hL_eq]
  have hswap_sum :
      (∑ i : Fin d, ∑ j : Fin d, ∫ x in Omega,
        B.a x i j *
          chosenWeakPartial' 2 l (chosenWeakPartial' 2 j u Omega) Omega x *
          (fderiv ℝ psi x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E)) =
      ∑ i : Fin d, ∑ j : Fin d, ∫ x in Omega,
        B.a x i j *
          chosenWeakPartial' 2 j (chosenWeakPartial' 2 l u Omega) Omega x *
          (fderiv ℝ psi x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact hpair_swap i j
  rw [sum_integral _ hH_int, sum_integral _ hC_int, ← hswap_sum]
  exact hraw_eq

private theorem coeff_scale_int
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u phi : E → ℝ}
    (B : SmoothEllipticBilinearForm d Set.univ) {rho : ℝ}
    (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d,
      A.a x i j = rho * B.a x i j) :
    (∫ x in Omega, ∑ i : Fin d,
      (∑ j : Fin d, A.a x i j * chosenWeakPartial' 2 j u Omega x) *
        (fderiv ℝ phi x) (EuclideanSpace.single i 1)
      ∂(volume : Measure E)) =
      rho * ∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
        B.a x i j * chosenWeakPartial' 2 j u Omega x *
          (fderiv ℝ phi x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E) := by
  calc
    _ = ∫ x in Omega, rho * (∑ i : Fin d, ∑ j : Fin d,
        B.a x i j * chosenWeakPartial' 2 j u Omega x *
          (fderiv ℝ phi x) (EuclideanSpace.single i 1))
        ∂(volume : Measure E) := by
          refine setIntegral_congr_fun hOmega.measurableSet (fun x hx => ?_)
          simp_rw [hcoeff x hx]
          calc
            _ = ∑ i : Fin d,
                (rho * ∑ j : Fin d,
                  B.a x i j * chosenWeakPartial' 2 j u Omega x) *
                  (fderiv ℝ phi x) (EuclideanSpace.single i 1) := by
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  congr 1
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl (fun j _ => ?_)
                  ring
            _ = ∑ i : Fin d, rho *
                ((∑ j : Fin d,
                  B.a x i j * chosenWeakPartial' 2 j u Omega x) *
                  (fderiv ℝ phi x) (EuclideanSpace.single i 1)) := by
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  ring
            _ = rho * ∑ i : Fin d,
                ((∑ j : Fin d,
                  B.a x i j * chosenWeakPartial' 2 j u Omega x) *
                  (fderiv ℝ phi x) (EuclideanSpace.single i 1)) := by
                  rw [Finset.mul_sum]
            _ = _ := by
                  congr 1
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  rw [Finset.sum_mul]
    _ = _ := integral_const_mul rho _

/-- The bilinear form of a canonical first weak partial against a smooth test
is the scaled coefficient integral with canonical second weak partials. -/
theorem diff_bilin_scaled
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u : E → ℝ}
    (B : SmoothEllipticBilinearForm d Set.univ) {rho : ℝ}
    (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d,
      A.a x i j = rho * B.a x i j)
    (hu2 : MemWkp (d := d) 2 2 u Omega) (l : Fin d)
    (hw : DeGiorgi.MemW1pWitness 2
      (chosenWeakPartial' 2 l u Omega) Omega)
    {psi : E → ℝ} (hpsi : DeGiorgi.IsSmoothTestOn Omega psi) :
    DeGiorgi.bilinFormOfCoeff A hw
        (DeGiorgi.smoothTestWitness hOmega hpsi) =
      rho * ∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
        B.a x i j *
          chosenWeakPartial' 2 j
            (chosenWeakPartial' 2 l u Omega) Omega x *
          (fderiv ℝ psi x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E) := by
  classical
  have hw_mem : DeGiorgi.MemW1p 2
      (chosenWeakPartial' 2 l u Omega) Omega := by
    rw [← MemWkp.one_iff_memW1p]
    exact hu2.chosenWeakPartial_mem l
  let hwc : DeGiorgi.MemW1pWitness 2
      (chosenWeakPartial' 2 l u Omega) Omega :=
    DeGiorgi.MemW1p.someWitness hw_mem
  have hwc_grad_ae : ∀ j : Fin d,
      (fun x => hwc.weakGrad x j) =ᵐ[(volume : Measure E).restrict Omega]
        chosenWeakPartial' 2 j
          (chosenWeakPartial' 2 l u Omega) Omega := by
    intro j
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hOmega
      (hwc.isWeakGrad j)
      (chosenWeakPartial'_isWeakPartial_of_mem hw_mem j)
      ((hwc.weakGrad_component_memLp j).locallyIntegrable (by norm_num))
      ((chosenWeakPartial'_memLp_of_mem hw_mem j).locallyIntegrable
        (by norm_num))
  have hwc_grad_all : ∀ᵐ x ∂((volume : Measure E).restrict Omega),
      ∀ j : Fin d,
        hwc.weakGrad x j =
          chosenWeakPartial' 2 j
            (chosenWeakPartial' 2 l u Omega) Omega x :=
    ae_all_iff.2 hwc_grad_ae
  have hscalar : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := by
    intro a b
    simpa using RCLike.inner_apply' a b
  have hleft :
      DeGiorgi.bilinFormOfCoeff A hwc
          (DeGiorgi.smoothTestWitness hOmega hpsi) =
        ∫ x in Omega, ∑ i : Fin d,
          (∑ j : Fin d, A.a x i j *
            chosenWeakPartial' 2 j
              (chosenWeakPartial' 2 l u Omega) Omega x) *
            (fderiv ℝ psi x) (EuclideanSpace.single i 1) := by
    rw [DeGiorgi.bilinFormOfCoeff]
    apply integral_congr_ae
    filter_upwards [hwc_grad_all] with x hx
    simp [DeGiorgi.bilinFormIntegrandOfCoeff, DeGiorgi.matMulE_apply,
      Matrix.mulVec, dotProduct, PiLp.inner_apply,
      DeGiorgi.smoothTestWitness, DeGiorgi.smoothGradField, hx, hscalar]
  calc
    DeGiorgi.bilinFormOfCoeff A hw
        (DeGiorgi.smoothTestWitness hOmega hpsi) =
        DeGiorgi.bilinFormOfCoeff A hwc
          (DeGiorgi.smoothTestWitness hOmega hpsi) :=
      DeGiorgi.bilinFormOfCoeff_eq_left hOmega A hw hwc
        (DeGiorgi.smoothTestWitness hOmega hpsi)
    _ = ∫ x in Omega, ∑ i : Fin d,
        (∑ j : Fin d, A.a x i j *
          chosenWeakPartial' 2 j
            (chosenWeakPartial' 2 l u Omega) Omega x) *
          (fderiv ℝ psi x) (EuclideanSpace.single i 1) := hleft
    _ = _ := coeff_scale_int hOmega B hcoeff

/-- Differentiating a homogeneous divergence-form weak equation gives the
variational equation for each canonical first weak partial. -/
theorem homSol_diff_id
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u : E → ℝ}
    (hsol : DeGiorgi.IsSolution A u)
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : 0 < rho)
    (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d,
      A.a x i j = rho * B.a x i j)
    (hu2 : MemWkp (d := d) 2 2 u Omega)
    (l : Fin d) {psi : E → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpsi_cpt : HasCompactSupport psi) (hpsi_sub : tsupport psi ⊆ Omega) :
    (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
      B.a x i j *
        chosenWeakPartial' 2 j (chosenWeakPartial' 2 l u Omega) Omega x *
        (fderiv ℝ psi x) (EuclideanSpace.single i 1)
      ∂(volume : Measure E)) =
      -(∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
        (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
          chosenWeakPartial' 2 j u Omega x *
          (fderiv ℝ psi x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E)) := by
  classical
  have hu1 : DeGiorgi.MemW1p 2 u Omega := hu2.memW1p
  let huw : DeGiorgi.MemW1pWitness 2 u Omega := DeGiorgi.MemW1p.someWitness hu1
  let psil : E → ℝ := fun x =>
    (fderiv ℝ psi x) (EuclideanSpace.single l 1)
  have hpsil : ContDiff ℝ (⊤ : ℕ∞) psil := contDiff_partial hpsi l
  have hpsil_cpt : HasCompactSupport psil :=
    hpsi_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)
  have hpsil_sub : tsupport psil ⊆ Omega :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single l 1)).trans hpsi_sub
  let hpsil_test : DeGiorgi.IsSmoothTestOn Omega psil :=
    ⟨hpsil, hpsil_cpt, hpsil_sub⟩
  have hzero := (hsol.to_homogeneous hOmega).2 huw psil
    (DeGiorgi.smoothTest_memH01 hOmega hpsil_test)
    (DeGiorgi.smoothTestWitness hOmega hpsil_test)
  rw [DeGiorgi.bilinFormOfCoeff] at hzero
  have hscalar : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := by
    intro a b
    simpa using RCLike.inner_apply' a b
  have hA :
      (∫ x in Omega, ∑ i : Fin d,
        (∑ j : Fin d, A.a x i j * chosenWeakPartial' 2 j u Omega x) *
          (fderiv ℝ psil x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E)) = 0 := by
    simpa [DeGiorgi.bilinFormIntegrandOfCoeff, DeGiorgi.matMulE_apply,
      Matrix.mulVec, dotProduct, PiLp.inner_apply, DeGiorgi.smoothTestWitness,
      DeGiorgi.smoothGradField, PiLp.toLp_apply, chosenWeakPartial', hu1, huw,
      hscalar] using hzero
  have hscaled := coeff_scale_int hOmega B hcoeff (u := u) (phi := psil)
  have hbase :
      (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
        B.a x i j * chosenWeakPartial' 2 j u Omega x *
          (fderiv ℝ psil x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E)) = 0 := by
    have : rho * (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
        B.a x i j * chosenWeakPartial' 2 j u Omega x *
          (fderiv ℝ psil x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E)) = 0 := by
      rw [← hscaled]
      exact hA
    exact (mul_eq_zero.mp this).resolve_left hrho.ne'
  simpa [psil] using
    (diff_id_of_base hOmega B hu2 l hpsi hpsi_cpt hpsi_sub hbase)

/-- Differentiating a scalar-source divergence-form weak equation gives the
smooth-test identity for each canonical first weak partial. -/
theorem srcSol_diff_id
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    (hweak : ∀ v, DeGiorgi.MemH01 v Omega →
      ∀ hv : DeGiorgi.MemW1pWitness 2 v Omega,
        DeGiorgi.bilinFormOfCoeff A hu hv =
          ∫ x in Omega, f x * v x ∂(volume : Measure E))
    (hf1 : MemWkp (d := d) 1 2 f Omega)
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : 0 < rho)
    (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d,
      A.a x i j = rho * B.a x i j)
    (hu2 : MemWkp (d := d) 2 2 u Omega)
    (l : Fin d) {psi : E → ℝ}
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpsi_cpt : HasCompactSupport psi) (hpsi_sub : tsupport psi ⊆ Omega) :
    (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
      B.a x i j *
        chosenWeakPartial' 2 j (chosenWeakPartial' 2 l u Omega) Omega x *
        (fderiv ℝ psi x) (EuclideanSpace.single i 1)
      ∂(volume : Measure E)) =
      rho⁻¹ * ∫ x in Omega,
        chosenWeakPartial' 2 l f Omega x * psi x
        ∂(volume : Measure E) -
      ∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
        (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
          chosenWeakPartial' 2 j u Omega x *
          (fderiv ℝ psi x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E) := by
  classical
  have hu1 : DeGiorgi.MemW1p 2 u Omega := hu2.memW1p
  let huw : DeGiorgi.MemW1pWitness 2 u Omega :=
    DeGiorgi.MemW1p.someWitness hu1
  let psil : E → ℝ := fun x =>
    (fderiv ℝ psi x) (EuclideanSpace.single l 1)
  have hpsil : ContDiff ℝ (⊤ : ℕ∞) psil := contDiff_partial hpsi l
  have hpsil_cpt : HasCompactSupport psil :=
    hpsi_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)
  have hpsil_sub : tsupport psil ⊆ Omega :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single l 1)).trans hpsi_sub
  let hpsil_test : DeGiorgi.IsSmoothTestOn Omega psil :=
    ⟨hpsil, hpsil_cpt, hpsil_sub⟩
  let hpsil_w : DeGiorgi.MemW1pWitness 2 psil Omega :=
    DeGiorgi.smoothTestWitness hOmega hpsil_test
  have hsrc : DeGiorgi.bilinFormOfCoeff A huw hpsil_w =
      ∫ x in Omega, f x * psil x ∂(volume : Measure E) := by
    calc
      DeGiorgi.bilinFormOfCoeff A huw hpsil_w =
          DeGiorgi.bilinFormOfCoeff A hu hpsil_w :=
        DeGiorgi.bilinFormOfCoeff_eq_left hOmega A huw hu hpsil_w
      _ = _ := hweak psil (DeGiorgi.smoothTest_memH01 hOmega hpsil_test) hpsil_w
  rw [DeGiorgi.bilinFormOfCoeff] at hsrc
  have hscalar : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := by
    intro a b
    simpa using RCLike.inner_apply' a b
  have hA :
      (∫ x in Omega, ∑ i : Fin d,
        (∑ j : Fin d, A.a x i j * chosenWeakPartial' 2 j u Omega x) *
          (fderiv ℝ psil x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E)) =
        ∫ x in Omega, f x * psil x ∂(volume : Measure E) := by
    simpa [DeGiorgi.bilinFormIntegrandOfCoeff, DeGiorgi.matMulE_apply,
      Matrix.mulVec, dotProduct, PiLp.inner_apply, hpsil_w,
      DeGiorgi.smoothTestWitness, DeGiorgi.smoothGradField, PiLp.toLp_apply,
      chosenWeakPartial', hu1, huw, hscalar] using hsrc
  have hscaled := coeff_scale_int hOmega B hcoeff (u := u) (phi := psil)
  have hmul :
      rho * (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
        B.a x i j * chosenWeakPartial' 2 j u Omega x *
          (fderiv ℝ psil x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E)) =
        ∫ x in Omega, f x * psil x ∂(volume : Measure E) := by
    rw [← hscaled]
    exact hA
  have hf_ibp :
      (∫ x in Omega, f x * psil x ∂(volume : Measure E)) =
        -(∫ x in Omega, chosenWeakPartial' 2 l f Omega x * psi x
          ∂(volume : Measure E)) := by
    simpa [psil] using
      (chosenWeakPartial'_isWeakPartial_of_mem hf1.memW1p l
        psi hpsi hpsi_cpt hpsi_sub)
  have hbase :
      (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
        B.a x i j * chosenWeakPartial' 2 j u Omega x *
          (fderiv ℝ psil x) (EuclideanSpace.single i 1)
        ∂(volume : Measure E)) =
        -(rho⁻¹ * ∫ x in Omega,
          chosenWeakPartial' 2 l f Omega x * psi x
          ∂(volume : Measure E)) := by
    calc
      _ = rho⁻¹ * (rho * (∫ x in Omega, ∑ i : Fin d, ∑ j : Fin d,
          B.a x i j * chosenWeakPartial' 2 j u Omega x *
            (fderiv ℝ psil x) (EuclideanSpace.single i 1)
          ∂(volume : Measure E))) := by field_simp [hrho.ne']
      _ = rho⁻¹ * (∫ x in Omega, f x * psil x
          ∂(volume : Measure E)) := by rw [hmul]
      _ = rho⁻¹ * (-(∫ x in Omega,
          chosenWeakPartial' 2 l f Omega x * psi x
          ∂(volume : Measure E))) := by rw [hf_ibp]
      _ = _ := by ring
  have hcore := diff_id_of_base hOmega B hu2 l hpsi hpsi_cpt hpsi_sub
    (r := -(rho⁻¹ * ∫ x in Omega,
      chosenWeakPartial' 2 l f Omega x * psi x
      ∂(volume : Measure E)))
    (by simpa [psil] using hbase)
  linarith [hcore]
end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
