import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.Multiply
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Defs
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.WeakDivergence

noncomputable section

open MeasureTheory Set Filter Topology
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The vector field produced by differentiating a homogeneous divergence-form
equation in direction `l`. -/
noncomputable def homDiffField
    (B : SmoothEllipticBilinearForm d (Set.univ : Set E))
    (u : E → ℝ) (Omega : Set E) (l : Fin d) : E → E :=
  fun x => WithLp.toLp 2 fun i => ∑ j : Fin d,
    (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
      chosenWeakPartial' 2 j u Omega x

/-- The canonical scalar weak divergence of `homDiffField`. -/
noncomputable def homDiffSource
    (B : SmoothEllipticBilinearForm d (Set.univ : Set E))
    (u : E → ℝ) (Omega : Set E) (l : Fin d) : E → ℝ :=
  fun x => ∑ i : Fin d, ∑ j : Fin d, (
    (fderiv ℝ
        (fun y : E =>
          (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1)) x)
        (EuclideanSpace.single i 1) * chosenWeakPartial' 2 j u Omega x +
      (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
        chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u Omega) Omega x)

omit [NeZero d] in
private theorem smooth_mul_memLp
    {Omega : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
    {a f : E → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hf : MemLp f 2 ((volume : Measure E).restrict Omega)) :
    MemLp (fun x => a x * f x) 2 ((volume : Measure E).restrict Omega) := by
  obtain ⟨C, hC⟩ :=
    hOmega_compact.exists_bound_of_continuousOn ha.continuous.continuousOn
  refine MemLp.of_le_mul (g := f) (c := max C 0) hf ?_ ?_
  · exact ha.continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable
  · refine (ae_restrict_iff' hOmega.measurableSet).mpr ?_
    exact Filter.Eventually.of_forall fun x hx => by
      rw [norm_mul]
      gcongr
      exact (hC x (subset_closure hx)).trans (le_max_left C 0)

private theorem homDiffField_term_memLp
    {Omega : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
    (B : SmoothEllipticBilinearForm d (Set.univ : Set E))
    {u : E → ℝ} (hu2 : MemWkp (d := d) 2 2 u Omega)
    (l i j : Fin d) :
    MemLp (fun x =>
      (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
        chosenWeakPartial' 2 j u Omega x)
      2 ((volume : Measure E).restrict Omega) := by
  have hcoef : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
      (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1)) :=
    contDiff_partial_eta (B.smooth_a i j) l
  exact smooth_mul_memLp hOmega hOmega_compact hcoef
    (chosenWeakPartial'_memLp_of_mem hu2.memW1p j)

private theorem homDiffField_comp_memLp
    {Omega : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
    (B : SmoothEllipticBilinearForm d (Set.univ : Set E))
    {u : E → ℝ} (hu2 : MemWkp (d := d) 2 2 u Omega)
    (l i : Fin d) :
    MemLp (fun x => ∑ j : Fin d,
      (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
        chosenWeakPartial' 2 j u Omega x)
      2 ((volume : Measure E).restrict Omega) := by
  simpa using memLp_finset_sum (Finset.univ : Finset (Fin d))
    (fun j _ => homDiffField_term_memLp hOmega hOmega_compact B hu2 l i j)

/-- The differentiated homogeneous vector field is square-integrable on a
relatively compact open set. -/
theorem homDiffField_memLp
    {Omega : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
    (B : SmoothEllipticBilinearForm d (Set.univ : Set E))
    {u : E → ℝ} (hu2 : MemWkp (d := d) 2 2 u Omega)
    (l : Fin d) :
    MemLp (homDiffField B u Omega l) 2
      ((volume : Measure E).restrict Omega) := by
  refine MemLp.of_eval_piLp ?_
  intro i
  simpa [homDiffField, PiLp.toLp_apply] using
    homDiffField_comp_memLp hOmega hOmega_compact B hu2 l i

private theorem homDiffSource_term_memLp
    {Omega : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
    (B : SmoothEllipticBilinearForm d (Set.univ : Set E))
    {u : E → ℝ} (hu2 : MemWkp (d := d) 2 2 u Omega)
    (l i j : Fin d) :
    MemLp (fun x =>
      (fderiv ℝ
          (fun y : E =>
            (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1)) x)
          (EuclideanSpace.single i 1) * chosenWeakPartial' 2 j u Omega x +
        (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
          chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u Omega) Omega x)
      2 ((volume : Measure E).restrict Omega) := by
  have huj1 : DeGiorgi.MemW1p 2 (chosenWeakPartial' 2 j u Omega) Omega := by
    rw [← MemWkp.one_iff_memW1p]
    exact hu2.chosenWeakPartial_mem j
  have hcoef : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
      (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1)) :=
    contDiff_partial_eta (B.smooth_a i j) l
  have hcoef2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
      (fderiv ℝ
        (fun y : E =>
          (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1)) x)
        (EuclideanSpace.single i 1)) :=
    contDiff_partial_eta hcoef i
  exact (smooth_mul_memLp hOmega hOmega_compact hcoef2
      (chosenWeakPartial'_memLp_of_mem hu2.memW1p j)).add
    (smooth_mul_memLp hOmega hOmega_compact hcoef
      (chosenWeakPartial'_memLp_of_mem huj1 i))

private theorem homDiffSource_comp_memLp
    {Omega : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
    (B : SmoothEllipticBilinearForm d (Set.univ : Set E))
    {u : E → ℝ} (hu2 : MemWkp (d := d) 2 2 u Omega)
    (l i : Fin d) :
    MemLp (fun x => ∑ j : Fin d, (
      (fderiv ℝ
          (fun y : E =>
            (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1)) x)
          (EuclideanSpace.single i 1) * chosenWeakPartial' 2 j u Omega x +
        (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
          chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u Omega) Omega x))
      2 ((volume : Measure E).restrict Omega) := by
  simpa using memLp_finset_sum (Finset.univ : Finset (Fin d))
    (fun j _ => homDiffSource_term_memLp hOmega hOmega_compact B hu2 l i j)

/-- The canonical scalar divergence source is square-integrable on a relatively
compact open set. -/
theorem homDiffSource_memLp
    {Omega : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
    (B : SmoothEllipticBilinearForm d (Set.univ : Set E))
    {u : E → ℝ} (hu2 : MemWkp (d := d) 2 2 u Omega)
    (l : Fin d) :
    MemLp (homDiffSource B u Omega l) 2
      ((volume : Measure E).restrict Omega) := by
  simpa [homDiffSource] using memLp_finset_sum (Finset.univ : Finset (Fin d))
    (fun i _ => homDiffSource_comp_memLp hOmega hOmega_compact B hu2 l i)

omit [NeZero d] in
private theorem hasWeakPartial_sum
    {I : Type*} [Fintype I] {Omega : Set E} {i : Fin d}
    {f g : I → E → ℝ}
    (hf_loc : ∀ j, LocallyIntegrable (f j) ((volume : Measure E).restrict Omega))
    (hg_loc : ∀ j, LocallyIntegrable (g j) ((volume : Measure E).restrict Omega))
    (hparts : ∀ j, DeGiorgi.HasWeakPartialDeriv i (g j) (f j) Omega) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => ∑ j, g j x) (fun x => ∑ j, f j x) Omega := by
  classical
  intro phi hphi hphi_cpt hphi_sub
  have hdphi_cont : Continuous
      (fun x : E => (fderiv ℝ phi x) (EuclideanSpace.single i 1)) :=
    (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdphi_cpt : HasCompactSupport
      (fun x : E => (fderiv ℝ phi x) (EuclideanSpace.single i 1)) :=
    hphi_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hleft_int : ∀ j, Integrable (fun x =>
      f j x * (fderiv ℝ phi x) (EuclideanSpace.single i 1))
      ((volume : Measure E).restrict Omega) := by
    intro j
    simpa [smul_eq_mul] using
      (hf_loc j).integrable_smul_right_of_hasCompactSupport hdphi_cont hdphi_cpt
  have hright_int : ∀ j, Integrable (fun x => g j x * phi x)
      ((volume : Measure E).restrict Omega) := by
    intro j
    simpa [smul_eq_mul] using
      (hg_loc j).integrable_smul_right_of_hasCompactSupport
        hphi.continuous hphi_cpt
  calc
    ∫ x in Omega, (∑ j, f j x) *
        (fderiv ℝ phi x) (EuclideanSpace.single i 1) =
        ∫ x in Omega, ∑ j,
          f j x * (fderiv ℝ phi x) (EuclideanSpace.single i 1) := by
            simp only [Finset.sum_mul]
    _ = ∑ j, ∫ x in Omega,
        f j x * (fderiv ℝ phi x) (EuclideanSpace.single i 1) := by
          rw [integral_finset_sum]
          exact fun j _ => hleft_int j
    _ = ∑ j, -(∫ x in Omega, g j x * phi x) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          exact hparts j phi hphi hphi_cpt hphi_sub
    _ = -(∑ j, ∫ x in Omega, g j x * phi x) := by
          rw [Finset.sum_neg_distrib]
    _ = -(∫ x in Omega, ∑ j, g j x * phi x) := by
          rw [integral_finset_sum]
          exact fun j _ => hright_int j
    _ = -(∫ x in Omega, (∑ j, g j x) * phi x) := by
          simp only [Finset.sum_mul]

private theorem homDiff_comp_hasWeakPartial
    {Omega : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
    (B : SmoothEllipticBilinearForm d (Set.univ : Set E))
    {u : E → ℝ} (hu2 : MemWkp (d := d) 2 2 u Omega)
    (l i : Fin d) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => ∑ j : Fin d, (
        (fderiv ℝ
            (fun y : E =>
              (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1)) x)
            (EuclideanSpace.single i 1) * chosenWeakPartial' 2 j u Omega x +
          (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
            chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u Omega) Omega x))
      (fun x => ∑ j : Fin d,
        (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
          chosenWeakPartial' 2 j u Omega x) Omega := by
  have huj1 : ∀ j : Fin d,
      DeGiorgi.MemW1p 2 (chosenWeakPartial' 2 j u Omega) Omega := by
    intro j
    rw [← MemWkp.one_iff_memW1p]
    exact hu2.chosenWeakPartial_mem j
  refine hasWeakPartial_sum (I := Fin d) (Omega := Omega) (i := i)
    (f := fun j x =>
      (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
        chosenWeakPartial' 2 j u Omega x)
    (g := fun j x =>
      (fderiv ℝ
          (fun y : E =>
            (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1)) x)
          (EuclideanSpace.single i 1) * chosenWeakPartial' 2 j u Omega x +
        (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
          chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u Omega) Omega x)
    ?_ ?_ ?_
  · intro j
    exact (homDiffField_term_memLp hOmega hOmega_compact B hu2 l i j).locallyIntegrable
      (by norm_num)
  · intro j
    exact (homDiffSource_term_memLp hOmega hOmega_compact B hu2 l i j).locallyIntegrable
      (by norm_num)
  · intro j
    have hcoef : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
        (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1)) :=
      contDiff_partial_eta (B.smooth_a i j) l
    have hprod := DeGiorgi.HasWeakPartialDeriv.mul_smooth hOmega
      (chosenWeakPartial'_isWeakPartial_of_mem (huj1 j) i) hcoef
      ((chosenWeakPartial'_memLp_of_mem hu2.memW1p j).locallyIntegrable
        (by norm_num))
      ((chosenWeakPartial'_memLp_of_mem (huj1 j) i).locallyIntegrable
        (by norm_num))
    simpa [add_comm] using hprod

/-- The canonical scalar source is the weak divergence of the differentiated
homogeneous vector field. -/
theorem homDiff_hasDiv
    {Omega : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
    (B : SmoothEllipticBilinearForm d (Set.univ : Set E))
    {u : E → ℝ} (hu2 : MemWkp (d := d) 2 2 u Omega)
    (l : Fin d) :
    DeGiorgi.HasWeakDiv (homDiffSource B u Omega l)
      (homDiffField B u Omega l) Omega := by
  let G : Fin d → E → ℝ := fun i x => ∑ j : Fin d, (
    (fderiv ℝ
        (fun y : E =>
          (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1)) x)
        (EuclideanSpace.single i 1) * chosenWeakPartial' 2 j u Omega x +
      (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
        chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u Omega) Omega x)
  have hdiv := DeGiorgi.hasWeakDiv_of_parts
    (F := homDiffField B u Omega l) (G := G)
    (fun i => by
      simpa [homDiffField, PiLp.toLp_apply] using
        (homDiffField_comp_memLp hOmega hOmega_compact B hu2 l i).locallyIntegrable
          (by norm_num))
    (fun i => by
      simpa [G] using
        (homDiffSource_comp_memLp hOmega hOmega_compact B hu2 l i).locallyIntegrable
          (by norm_num))
    (fun i => by
      simpa [G, homDiffField, PiLp.toLp_apply] using
        homDiff_comp_hasWeakPartial hOmega hOmega_compact B hu2 l i)
  simpa [G, homDiffSource] using hdiv

end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
