import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import DifferentialGeometry.External.DeGiorgi.SobolevSpace
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Analytic.IteratedFDeriv

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

lemma chosenWeakPartial'_ae_eq_fderiv_of_smooth
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu_smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) u)
    (hu_supp : HasCompactSupport u) (hu_sub : tsupport u ⊆ Ω) (i : Fin d) :
    chosenWeakPartial' 2 i u Ω =ᵐ[volume.restrict Ω]
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ))) := by
  classical
  have hu_inner : ContDiff ℝ (⊤ : ℕ∞) u :=
    hu_smooth.of_le (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  have hu_mem : DeGiorgi.MemW1p 2 u Ω :=
    (DeGiorgi.memW01p_of_contDiff_hasCompactSupport_subset hΩ hu_inner hu_supp hu_sub).memW1p
  have hw : DeGiorgi.HasWeakPartialDeriv i (chosenWeakPartial' 2 i u Ω) u Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_mem i
  have hf : DeGiorgi.HasWeakPartialDeriv i
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ))) u Ω :=
    DeGiorgi.HasWeakPartialDeriv.of_contDiff hΩ (hu_smooth.of_le (by norm_num))
  have hg₁ : LocallyIntegrable (chosenWeakPartial' 2 i u Ω) (volume.restrict Ω) :=
    (chosenWeakPartial'_memLp_of_mem hu_mem i).locallyIntegrable
      (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
  have hg₂ : LocallyIntegrable (fun x => (fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ)))
      (volume.restrict Ω) := by
    have hs : ContDiff ℝ (⊤ : ℕ∞)
        (fun x => (fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ))) :=
      (hu_inner.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
    have hsupp : HasCompactSupport
        (fun x => (fderiv ℝ u x) (EuclideanSpace.single i (1 : ℝ))) :=
      hu_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ))
    exact ((hs.continuous.memLp_of_hasCompactSupport hsupp).restrict Ω).locallyIntegrable
      (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ hw hf hg₁ hg₂

omit [NeZero d] in
lemma fderiv_iteratedFDeriv_apply_const
    {u : E → ℝ} (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (j : ℕ) (v : Fin j → E) (w : E) (x : E) :
    fderiv ℝ (fun y => (iteratedFDeriv ℝ j u y) v) x w =
      (fderiv ℝ (iteratedFDeriv ℝ j u) x) w v := by
  let A : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ →L[ℝ] ℝ :=
    { toFun := fun L => L v
      map_add' := by intro L M; rfl
      map_smul' := by intro c L; rfl }
  have hg : DifferentiableAt ℝ (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ => A L)
      (iteratedFDeriv ℝ j u x) :=
    A.hasFDerivAt.differentiableAt
  have hf : DifferentiableAt ℝ (iteratedFDeriv ℝ j u) x :=
    (hu_smooth.iteratedFDeriv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (i := j)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (by exact_mod_cast (le_top : (⊤ : ℕ∞) + (j : ℕ∞) ≤ (⊤ : ℕ∞)))).contDiffAt.differentiableAt
      (by decide : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have h : fderiv ℝ (fun y => A (iteratedFDeriv ℝ j u y)) x =
      A.comp (fderiv ℝ (iteratedFDeriv ℝ j u) x) := by
    change fderiv ℝ ((fun L : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ => A L) ∘
        iteratedFDeriv ℝ j u) x = A.comp (fderiv ℝ (iteratedFDeriv ℝ j u) x)
    rw [fderiv_comp x hg hf]
    congr 1
    exact A.hasFDerivAt.fderiv
  calc
    fderiv ℝ (fun y => (iteratedFDeriv ℝ j u y) v) x w
        = fderiv ℝ (fun y => A (iteratedFDeriv ℝ j u y)) x w := rfl
    _ = (A.comp (fderiv ℝ (iteratedFDeriv ℝ j u) x)) w := by rw [h]
    _ = A ((fderiv ℝ (iteratedFDeriv ℝ j u) x) w) := rfl
    _ = (fderiv ℝ (iteratedFDeriv ℝ j u) x) w v := rfl

omit [NeZero d] in
lemma iteratedFDeriv_succ_cons_apply
    {u : E → ℝ} (hu_smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) u)
    (j : ℕ) (α : Fin j → Fin d) (i : Fin d) :
    (fun x => (fderiv ℝ
        (fun y => (iteratedFDeriv ℝ j u y) (fun i' : Fin j => EuclideanSpace.single (α i') (1 : ℝ))) x)
          (EuclideanSpace.single i (1 : ℝ))) =
      fun x => (iteratedFDeriv ℝ (j + 1) u x)
        (Fin.cons (EuclideanSpace.single i (1 : ℝ))
          (fun i' : Fin j => EuclideanSpace.single (α i') (1 : ℝ))) := by
  funext x
  have hu_inner : ContDiff ℝ (⊤ : ℕ∞) u :=
    hu_smooth.of_le (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  calc
    (fderiv ℝ (fun y => (iteratedFDeriv ℝ j u y)
          (fun i' : Fin j => EuclideanSpace.single (α i') (1 : ℝ))) x)
          (EuclideanSpace.single i (1 : ℝ))
        = (fderiv ℝ (iteratedFDeriv ℝ j u) x) (EuclideanSpace.single i (1 : ℝ))
            (fun i' : Fin j => EuclideanSpace.single (α i') (1 : ℝ)) :=
          fderiv_iteratedFDeriv_apply_const hu_inner j
            (fun i' : Fin j => EuclideanSpace.single (α i') (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) x
    _ = (iteratedFDeriv ℝ (j + 1) u x)
          (Fin.cons (EuclideanSpace.single i (1 : ℝ))
            (fun i' : Fin j => EuclideanSpace.single (α i') (1 : ℝ))) := by
      rw [iteratedFDeriv_succ_apply_left]
      rfl

omit [NeZero d] in
lemma iteratedFDeriv_fderiv_cons_eq
    {u : E → ℝ} (hu_smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) u)
    (j : ℕ) (α : Fin j → Fin d) (i : Fin d) :
    (fun x => (iteratedFDeriv ℝ j
        (fun y => (fderiv ℝ u y) (EuclideanSpace.single i (1 : ℝ))) x)
          (fun i' : Fin j => EuclideanSpace.single (α i') (1 : ℝ))) =
      fun x => (iteratedFDeriv ℝ (j + 1) u x)
        (Fin.cons (EuclideanSpace.single i (1 : ℝ))
          (fun i' : Fin j => EuclideanSpace.single (α i') (1 : ℝ))) := by
  induction j with
  | zero =>
      funext x
      simp [iteratedFDeriv_zero_apply]
  | succ j ih =>
      funext x
      have hu_inner : ContDiff ℝ (⊤ : ℕ∞) u :=
        hu_smooth.of_le (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
      have hIH := ih (fun i' : Fin j => α i'.succ)
      have hIH_fderiv :
          (fderiv ℝ (fun y => (iteratedFDeriv ℝ j
              (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ))) y)
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ))) x)
              (EuclideanSpace.single (α 0) (1 : ℝ)) =
            (fderiv ℝ (fun y => (iteratedFDeriv ℝ (j + 1) u y)
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)))) x)
              (EuclideanSpace.single (α 0) (1 : ℝ)) := by
        congr 1
        exact congrArg (fun f : E → ℝ => fderiv ℝ f x) hIH
      have hLHS :
          (iteratedFDeriv ℝ (j + 1)
              (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ))) x)
                (fun i' : Fin (j + 1) => EuclideanSpace.single (α i') (1 : ℝ)) =
            (fderiv ℝ (iteratedFDeriv ℝ j
              (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ)))) x
                (EuclideanSpace.single (α 0) (1 : ℝ)))
              (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)) := rfl
      have hw_smooth' : ContDiff ℝ (⊤ : ℕ∞)
          (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ))) :=
        (hu_inner.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
      have hclm_L :
          fderiv ℝ (fun y => (iteratedFDeriv ℝ j
              (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ))) y)
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ))) x
              (EuclideanSpace.single (α 0) (1 : ℝ)) =
            (fderiv ℝ (iteratedFDeriv ℝ j
              (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ)))) x
                (EuclideanSpace.single (α 0) (1 : ℝ)))
              (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)) :=
          fderiv_iteratedFDeriv_apply_const hw_smooth'
            j (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ))
            (EuclideanSpace.single (α 0) (1 : ℝ)) x
      have hclm_R :
          fderiv ℝ (fun y => (iteratedFDeriv ℝ (j + 1) u y)
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)))) x
              (EuclideanSpace.single (α 0) (1 : ℝ)) =
            (fderiv ℝ (iteratedFDeriv ℝ (j + 1) u) x
                (EuclideanSpace.single (α 0) (1 : ℝ)))
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ))) :=
          fderiv_iteratedFDeriv_apply_const hu_inner (j + 1)
            (Fin.cons (EuclideanSpace.single i (1 : ℝ))
              (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)))
            (EuclideanSpace.single (α 0) (1 : ℝ)) x
      have hswap :
          (fderiv ℝ (iteratedFDeriv ℝ (j + 1) u) x
                (EuclideanSpace.single (α 0) (1 : ℝ)))
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ))) =
            (fderiv ℝ (iteratedFDeriv ℝ (j + 1) u) x
                (EuclideanSpace.single i (1 : ℝ)))
              (fun i' : Fin (j + 1) => EuclideanSpace.single (α i') (1 : ℝ)) := by
        let σ : Equiv.Perm (Fin (j + 2)) := Equiv.swap (0 : Fin (j + 2)) (1 : Fin (j + 2))
        have hperm := ContDiffAt.iteratedFDeriv_comp_perm (𝕜 := ℝ) (f := u)
          (show ContDiffAt ℝ (⊤ : WithTop ℕ∞) u x from hu_smooth.contDiffAt)
          (n := j + 2)
          (v := Fin.cons (EuclideanSpace.single (α 0) (1 : ℝ))
            (Fin.cons (EuclideanSpace.single i (1 : ℝ))
              (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)))) σ
        have hperm' :
            iteratedFDeriv ℝ (j + 2) u x
                (Fin.cons (EuclideanSpace.single (α 0) (1 : ℝ))
                  (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                    (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)))) =
              iteratedFDeriv ℝ (j + 2) u x
                (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                  (fun i' : Fin (j + 1) => EuclideanSpace.single (α i') (1 : ℝ))) := by
          rw [← hperm]
          congr 1
          funext k
          cases k with
          | mk n hn =>
              cases n with
              | zero => simp [σ]
              | succ n =>
                  cases n with
                  | zero => simp [σ]
                  | succ n =>
                      have hk0 : (⟨n + 1 + 1, hn⟩ : Fin (j + 2)) ≠ 0 := by
                        intro h
                        have : n + 1 + 1 = 0 := congrArg Fin.val h
                        omega
                      have hk1 : (⟨n + 1 + 1, hn⟩ : Fin (j + 2)) ≠ 1 := by
                        intro h
                        have : n + 1 + 1 = 1 := congrArg Fin.val h
                        omega
                      simp [σ, Fin.cons, Equiv.swap_apply_of_ne_of_ne hk0 hk1]
        have hL : iteratedFDeriv ℝ (j + 2) u x
              (Fin.cons (EuclideanSpace.single (α 0) (1 : ℝ))
                (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                  (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)))) =
            (fderiv ℝ (iteratedFDeriv ℝ (j + 1) u) x
                (EuclideanSpace.single (α 0) (1 : ℝ)))
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ))) := rfl
        have hR : iteratedFDeriv ℝ (j + 2) u x
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin (j + 1) => EuclideanSpace.single (α i') (1 : ℝ))) =
            (fderiv ℝ (iteratedFDeriv ℝ (j + 1) u) x
                (EuclideanSpace.single i (1 : ℝ)))
              (fun i' : Fin (j + 1) => EuclideanSpace.single (α i') (1 : ℝ)) := rfl
        exact (hL.symm.trans hperm').trans hR
      calc
        (iteratedFDeriv ℝ (j + 1)
            (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ))) x)
              (fun i' : Fin (j + 1) => EuclideanSpace.single (α i') (1 : ℝ))
            = (fderiv ℝ (iteratedFDeriv ℝ j
                (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ)))) x
                  (EuclideanSpace.single (α 0) (1 : ℝ)))
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)) := hLHS
        _ = fderiv ℝ (fun y => (iteratedFDeriv ℝ j
              (fun z => (fderiv ℝ u z) (EuclideanSpace.single i (1 : ℝ))) y)
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ))) x
              (EuclideanSpace.single (α 0) (1 : ℝ)) := hclm_L.symm
        _ = fderiv ℝ (fun y => (iteratedFDeriv ℝ (j + 1) u y)
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ)))) x
              (EuclideanSpace.single (α 0) (1 : ℝ)) := hIH_fderiv
        _ = (fderiv ℝ (iteratedFDeriv ℝ (j + 1) u) x
                (EuclideanSpace.single (α 0) (1 : ℝ)))
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin j => EuclideanSpace.single (α i'.succ) (1 : ℝ))) := hclm_R
        _ = (fderiv ℝ (iteratedFDeriv ℝ (j + 1) u) x
                (EuclideanSpace.single i (1 : ℝ)))
              (fun i' : Fin (j + 1) => EuclideanSpace.single (α i') (1 : ℝ)) := hswap
        _ = (iteratedFDeriv ℝ (j + 2) u x)
              (Fin.cons (EuclideanSpace.single i (1 : ℝ))
                (fun i' : Fin (j + 1) => EuclideanSpace.single (α i') (1 : ℝ))) := rfl

lemma iterWeakPartial_ae_eq_iteratedFDeriv_of_smooth
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu_smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) u)
    (hu_supp : HasCompactSupport u) (hu_sub : tsupport u ⊆ Ω) :
    ∀ (j : ℕ) (α : Fin j → Fin d),
      iterWeakPartial (d := d) 2 j α u Ω =ᵐ[volume.restrict Ω]
        (fun x => (iteratedFDeriv ℝ j u x) (fun i : Fin j => EuclideanSpace.single (α i) (1 : ℝ))) := by
  intro j
  induction j generalizing u with
  | zero =>
      intro α
      simp [iterWeakPartial_zero, iteratedFDeriv_zero_apply]
  | succ j ih =>
      intro α
      rw [iterWeakPartial_succ]
      have hpart := chosenWeakPartial'_ae_eq_fderiv_of_smooth hΩ hu_smooth hu_supp hu_sub (α 0)
      have hw_smooth : ContDiff ℝ (⊤ : WithTop ℕ∞)
          (fun x => (fderiv ℝ u x) (EuclideanSpace.single (α 0) (1 : ℝ))) :=
        (hu_smooth.fderiv_right (m := (⊤ : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
      have hw_supp : HasCompactSupport
          (fun x => (fderiv ℝ u x) (EuclideanSpace.single (α 0) (1 : ℝ))) :=
        hu_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single (α 0) (1 : ℝ))
      have hw_sub : tsupport (fun x => (fderiv ℝ u x) (EuclideanSpace.single (α 0) (1 : ℝ))) ⊆ Ω :=
        (tsupport_fderiv_apply_subset (𝕜 := ℝ) (EuclideanSpace.single (α 0) (1 : ℝ))).trans hu_sub
      have hIH := ih (u := fun x => (fderiv ℝ u x) (EuclideanSpace.single (α 0) (1 : ℝ)))
        hw_smooth hw_supp hw_sub (fun i : Fin j => α i.succ)
      have htransport : iterWeakPartial (d := d) 2 j (fun i : Fin j => α i.succ)
            (chosenWeakPartial' 2 (α 0) u Ω) Ω =ᵐ[volume.restrict Ω]
          iterWeakPartial (d := d) 2 j (fun i : Fin j => α i.succ)
            (fun x => (fderiv ℝ u x) (EuclideanSpace.single (α 0) (1 : ℝ))) Ω :=
        iterWeakPartial_ae_congr (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ j
          (fun i : Fin j => α i.succ) hpart
      refine ae_eq_trans htransport ?_
      calc
        iterWeakPartial (d := d) 2 j (fun i : Fin j => α i.succ)
            (fun x => (fderiv ℝ u x) (EuclideanSpace.single (α 0) (1 : ℝ))) Ω
            =ᵐ[volume.restrict Ω]
          (fun x => (iteratedFDeriv ℝ j
            (fun y => (fderiv ℝ u y) (EuclideanSpace.single (α 0) (1 : ℝ))) x)
              (fun i : Fin j => EuclideanSpace.single (α i.succ) (1 : ℝ))) := hIH
        _ =ᵐ[volume.restrict Ω]
          (fun x => (iteratedFDeriv ℝ (j + 1) u x)
            (fun i : Fin (j + 1) => EuclideanSpace.single (α i) (1 : ℝ))) := by
          filter_upwards with x
          simpa [Fin.cons] using
            congrFun (iteratedFDeriv_fderiv_cons_eq hu_smooth j
              (fun i : Fin j => α i.succ) (α 0)) x

omit [NeZero d] in
lemma eLpNorm_iterWeakPartial_le_of_norm_le
    {Ω : Set E} {u : E → ℝ} {R : ℝ≥0∞} {k : ℕ}
    (hu : iteratedWeakSobolevNorm (d := d) (k + 1) 2 u Ω ≤ R)
    {j : ℕ} (hj : j ≤ k + 1) (α : Fin j → Fin d) :
    eLpNorm (iterWeakPartial (d := d) 2 j α u Ω) 2 (volume.restrict Ω) ≤ R := by
  classical
  have hmem_j : j ∈ Finset.range (k + 2) := by
    simp [Finset.mem_range]
    omega
  have h1 : eLpNorm (iterWeakPartial (d := d) 2 j α u Ω) 2 (volume.restrict Ω) ≤
      (∑ α' : Fin j → Fin d,
        eLpNorm (iterWeakPartial (d := d) 2 j α' u Ω) 2 (volume.restrict Ω) : ℝ≥0∞) :=
    Finset.single_le_sum
      (show ∀ x ∈ (Finset.univ : Finset (Fin j → Fin d)),
        (0 : ℝ≥0∞) ≤ eLpNorm (iterWeakPartial (d := d) 2 j x u Ω) 2 (volume.restrict Ω)
        from fun x _ => bot_le) (Finset.mem_univ α)
  have h2 : (∑ α' : Fin j → Fin d,
        eLpNorm (iterWeakPartial (d := d) 2 j α' u Ω) 2 (volume.restrict Ω) : ℝ≥0∞) ≤
      iteratedWeakSobolevNorm (d := d) (k + 1) 2 u Ω := by
    unfold iteratedWeakSobolevNorm
    exact Finset.single_le_sum
      (show ∀ x ∈ Finset.range (k + 2),
        (0 : ℝ≥0∞) ≤ (∑ α' : Fin x → Fin d,
          eLpNorm (iterWeakPartial (d := d) 2 x α' u Ω) 2 (volume.restrict Ω))
        from fun x _ => Finset.sum_nonneg (fun _ _ => bot_le)) hmem_j
  exact le_trans h1 (le_trans h2 hu)

omit [NeZero d] in
lemma exists_diagonal_extraction_lp
    {ι : Type*} [Fintype ι] {Ω : Set E}
    {s : ι → ℕ → E → ℝ}
    (h : ∀ t : ι, ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ a : E → ℝ, MemLp a 2 (volume.restrict Ω) ∧
        Tendsto (fun n => eLpNorm (fun x => s t (ψ (σ n)) x - a x) 2
          (volume.restrict Ω)) atTop (𝓝 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ t : ι, ∃ a : E → ℝ, MemLp a 2 (volume.restrict Ω) ∧
        Tendsto (fun n => eLpNorm (fun x => s t (ψ n) x - a x) 2
          (volume.restrict Ω)) atTop (𝓝 0) := by
  classical
  have hmain : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ t ∈ (Finset.univ : Finset ι), ∃ a : E → ℝ, MemLp a 2 (volume.restrict Ω) ∧
        Tendsto (fun n => eLpNorm (fun x => s t (ψ n) x - a x) 2
          (volume.restrict Ω)) atTop (𝓝 0) := by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty =>
        refine ⟨id, strictMono_id, ?_⟩
        intro t ht
        exact absurd ht (Finset.notMem_empty t)
    | insert t T' ht_notin ih =>
        rcases ih with ⟨ψ₀, hψ₀_mono, hP₀⟩
        rcases h t ψ₀ hψ₀_mono with ⟨σ, hσ_mono, a, ha_mem, ha⟩
        refine ⟨ψ₀ ∘ σ, hψ₀_mono.comp hσ_mono, ?_⟩
        intro t' ht'
        rcases Finset.mem_insert.mp ht' with rfl | ht'_T'
        · exact ⟨a, ha_mem, ha⟩
        · rcases hP₀ t' ht'_T' with ⟨a_t', ha_t'_mem, ha_t'⟩
          exact ⟨a_t', ha_t'_mem, ha_t'.comp (tendsto_atTop_atTop_of_monotone hσ_mono.monotone
            (fun n => ⟨n, hσ_mono.id_le n⟩))⟩
  rcases hmain with ⟨ψ, hψ_mono, hP⟩
  exact ⟨ψ, hψ_mono, fun t => hP t (Finset.mem_univ t)⟩

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
