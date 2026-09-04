import DifferentialGeometry.Analysis.Calculus.IteratedFDerivProductDifferenceBound
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.DifferentiatedSource

/-!
# Higher Sobolev Regularity of the Differentiated Source

This module proves the all-order source-regularity producer for the Nirenberg
bootstrap. If a homogeneous solution has `m + 2` weak derivatives, the
canonical source obtained by differentiating its equation has `m` weak
derivatives.
-/

noncomputable section

open MeasureTheory Set Topology
open DifferentialGeometry.Analysis.Calculus.DeTurckCoefficients
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem smooth_mul_memWkp
    (m : ℕ) {Omega : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
    {a f : E → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hf : MemWkp (d := d) m 2 f Omega) :
    MemWkp (d := d) m 2 (fun x => a x * f x) Omega := by
  obtain ⟨C, _hC_nonneg, hC⟩ :=
    exists_uniform_iteratedFDerivWithin_bound_of_contDiffOn
      isOpen_univ ha.contDiffOn hOmega_compact (subset_univ _) m
  exact MemWkp.smul_smooth_bounded (d := d) m (by norm_num) hOmega ha
    (fun j hj x hx => by
      simpa only [iteratedFDerivWithin_univ] using
        hC x (subset_closure hx) j hj) hf

omit [NeZero d] in
private theorem memWkp_fin_sum
    {m : ℕ} {Omega : Set E} (hOmega : IsOpen Omega)
    {ι : Type*} (S : Finset ι) (F : ι → E → ℝ)
    (hF : ∀ a ∈ S, MemWkp (d := d) m 2 (F a) Omega) :
    MemWkp (d := d) m 2 (fun x => ∑ a ∈ S, F a x) Omega := by
  classical
  induction S using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact MemWkp_zero_fun (d := d) (by norm_num) hOmega
  | insert a S ha ih =>
      have hFa : MemWkp (d := d) m 2 (F a) Omega :=
        hF a (Finset.mem_insert_self a S)
      have hFS : ∀ b ∈ S, MemWkp (d := d) m 2 (F b) Omega :=
        fun b hb => hF b (Finset.mem_insert_of_mem hb)
      have hsum : MemWkp (d := d) m 2 (fun x => ∑ b ∈ S, F b x) Omega :=
        ih hFS
      have hadd := MemWkp.add (d := d) (by norm_num) hOmega hFa hsum
      have heq :
          (fun x => F a x + ∑ b ∈ S, F b x) =
            (fun x => ∑ b ∈ insert a S, F b x) := by
        funext x
        rw [Finset.sum_insert ha]
      rwa [heq] at hadd

omit [NeZero d] in
private theorem memWkp_univ_sum
    {m : ℕ} {Omega : Set E} (hOmega : IsOpen Omega)
    {ι : Type*} [Fintype ι] (F : ι → E → ℝ)
    (hF : ∀ a, MemWkp (d := d) m 2 (F a) Omega) :
    MemWkp (d := d) m 2 (fun x => ∑ a, F a x) Omega := by
  classical
  simpa using memWkp_fin_sum (d := d) hOmega Finset.univ F
    (fun a _ => hF a)

/-- If a homogeneous solution has `m + 2` weak derivatives, then its canonical
differentiated scalar source has `m` weak derivatives. -/
theorem homDiff_memWkp
    (m : ℕ) {Omega : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
    (B : SmoothEllipticBilinearForm d (Set.univ : Set E))
    {u : E → ℝ} (hu : MemWkp (d := d) (m + 2) 2 u Omega)
    (l : Fin d) :
    MemWkp (d := d) m 2 (homDiffSource B u Omega l) Omega := by
  classical
  have hdu : ∀ j : Fin d,
      MemWkp (d := d) m 2 (chosenWeakPartial' 2 j u Omega) Omega :=
    fun j => (hu.chosenWeakPartial_mem j).le_of_le (Nat.le_succ m)
  have hd2u : ∀ i j : Fin d,
      MemWkp (d := d) m 2
        (chosenWeakPartial' 2 i
          (chosenWeakPartial' 2 j u Omega) Omega) Omega :=
    fun i j => (hu.chosenWeakPartial_mem j).chosenWeakPartial_mem i
  have hterm : ∀ i j : Fin d,
      MemWkp (d := d) m 2 (fun x =>
        (fderiv ℝ
            (fun y : E =>
              (fderiv ℝ (fun z : E => B.a z i j) y)
                (EuclideanSpace.single l 1)) x)
            (EuclideanSpace.single i 1) *
              chosenWeakPartial' 2 j u Omega x +
          (fderiv ℝ (fun y : E => B.a y i j) x)
              (EuclideanSpace.single l 1) *
            chosenWeakPartial' 2 i
              (chosenWeakPartial' 2 j u Omega) Omega x) Omega := by
    intro i j
    have hcoef : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
        (fderiv ℝ (fun y : E => B.a y i j) x)
          (EuclideanSpace.single l 1)) :=
      contDiff_partial_eta (B.smooth_a i j) l
    have hcoef2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
        (fderiv ℝ
          (fun y : E =>
            (fderiv ℝ (fun z : E => B.a z i j) y)
              (EuclideanSpace.single l 1)) x)
          (EuclideanSpace.single i 1)) :=
      contDiff_partial_eta hcoef i
    exact MemWkp.add (d := d) (by norm_num) hOmega
      (smooth_mul_memWkp m hOmega hOmega_compact hcoef2 (hdu j))
      (smooth_mul_memWkp m hOmega hOmega_compact hcoef (hd2u i j))
  have hinner : ∀ i : Fin d,
      MemWkp (d := d) m 2 (fun x => ∑ j : Fin d, (
        (fderiv ℝ
            (fun y : E =>
              (fderiv ℝ (fun z : E => B.a z i j) y)
                (EuclideanSpace.single l 1)) x)
            (EuclideanSpace.single i 1) *
              chosenWeakPartial' 2 j u Omega x +
          (fderiv ℝ (fun y : E => B.a y i j) x)
              (EuclideanSpace.single l 1) *
            chosenWeakPartial' 2 i
              (chosenWeakPartial' 2 j u Omega) Omega x)) Omega := by
    intro i
    exact memWkp_univ_sum hOmega _ (hterm i)
  simpa only [homDiffSource] using memWkp_univ_sum hOmega _ hinner

end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
