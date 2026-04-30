import DifferentialGeometry.Analysis.Sobolev.EuclideanMultiply

/-!
# Quantitative `W^{1,p}` bound for multiplication by a smooth bounded function

For a smooth (`C^∞`) function `η : E → ℝ` with `‖η‖` and `‖∇η‖` both bounded by
`C` on the open set `Ω`, the operation `u ↦ η · u` admits a uniform bound on
the `W^{1,p}` seminorm with a constant depending only on `C` and the
dimension `d`:

  `‖η · u‖_{W^{1,p}} ≤ K · ‖u‖_{W^{1,p}}`

with `K = (d + 1) · (max C 0 + 1)`.

The key step is the Leibniz identity
`∂ᵢ(η · u) =ᵐ η · ∂ᵢu + (∂ᵢη) · u`
(supplied by `chosenWeakPartial'_smul_smooth_bounded_ae`), combined with the
triangle inequality for `eLpNorm` and the pointwise estimate
`‖η · v‖ ≤ C · ‖v‖`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Pointwise bound on the partial derivative `(∂ᵢη)` -/

/-- `‖(∂ᵢ η) x‖ ≤ ‖fderiv ℝ η x‖`. -/
lemma norm_partial_eta_le_fderiv
    {η : E → ℝ} (i : Fin d) (x : E) :
    ‖(fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ))‖ ≤ ‖fderiv ℝ η x‖ := by
  have h := ContinuousLinearMap.le_opNorm (fderiv ℝ η x)
    (EuclideanSpace.single i (1 : ℝ))
  have h_one : ‖(EuclideanSpace.single i (1 : ℝ))‖ = 1 := by simp
  rw [h_one, mul_one] at h
  exact h

/-! ## `eLpNorm` bound for `η · v` -/

/-- For a function `η` with `‖η x‖ ≤ C` on `Ω`, and any function `v : E → ℝ`,
we have `eLpNorm (η · v) ≤ ENNReal.ofReal C · eLpNorm v`. -/
lemma eLpNorm_eta_mul_le
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsOpen Ω)
    {η : E → ℝ}
    {C : ℝ}
    (hη_bound : ∀ x ∈ Ω, ‖η x‖ ≤ C)
    (v : E → ℝ) :
    eLpNorm (fun x => η x * v x) p (volume.restrict Ω) ≤
      ENNReal.ofReal C * eLpNorm v p (volume.restrict Ω) := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := v) (c := C) ?_ p
  refine (ae_restrict_iff' hΩ.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  calc
    ‖η x * v x‖ = ‖η x‖ * ‖v x‖ := norm_mul _ _
    _ ≤ C * ‖v x‖ := by
          gcongr
          exact hη_bound x hx

/-- For a function `η` with `‖fderiv ℝ η x‖ ≤ C` on `Ω`, and any function
`v : E → ℝ`, the `i`-th partial `(∂ᵢη)` times `v` satisfies
`eLpNorm ((∂ᵢη) · v) ≤ ENNReal.ofReal C · eLpNorm v`. -/
lemma eLpNorm_partial_eta_mul_le
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsOpen Ω)
    {η : E → ℝ}
    {C : ℝ}
    (hη_grad_bound : ∀ x ∈ Ω, ‖fderiv ℝ η x‖ ≤ C)
    (i : Fin d) (v : E → ℝ) :
    eLpNorm (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * v x)
        p (volume.restrict Ω) ≤
      ENNReal.ofReal C * eLpNorm v p (volume.restrict Ω) := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := v) (c := C) ?_ p
  refine (ae_restrict_iff' hΩ.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  calc
    ‖(fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * v x‖
        = ‖(fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ))‖ * ‖v x‖ := norm_mul _ _
    _ ≤ ‖fderiv ℝ η x‖ * ‖v x‖ := by
          gcongr
          exact norm_partial_eta_le_fderiv i x
    _ ≤ C * ‖v x‖ := by
          gcongr
          exact hη_grad_bound x hx

/-! ## `eLpNorm` bound on the chosen weak partial of `η · u` -/

/-- The chosen weak partial of `η · u`, evaluated in `eLpNorm`, is bounded by
`C · eLpNorm (∂ᵢu) + C · eLpNorm u`. -/
lemma eLpNorm_chosenWeakPartial'_smul_smooth_bounded_le
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {η : E → ℝ}
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    {C : ℝ}
    (hη_bound : ∀ x ∈ Ω, ‖η x‖ ≤ C)
    (hη_grad_bound : ∀ x ∈ Ω, ‖fderiv ℝ η x‖ ≤ C)
    {u : E → ℝ} (hu : DeGiorgi.MemW1p (d := d) p u Ω) (i : Fin d) :
    eLpNorm (chosenWeakPartial' (d := d) p i (fun x => η x * u x) Ω) p
        (volume.restrict Ω) ≤
      ENNReal.ofReal C *
        eLpNorm (chosenWeakPartial' (d := d) p i u Ω) p (volume.restrict Ω) +
      ENNReal.ofReal C * eLpNorm u p (volume.restrict Ω) := by
  classical
  -- The chosen weak partial of η · u is a.e. equal to η · (∂ᵢu) + (∂ᵢη) · u.
  have hae := chosenWeakPartial'_smul_smooth_bounded_ae (d := d) hp_one hΩ
    hη_smooth hη_bound hη_grad_bound hu i
  -- AE strong measurability of the two summands.
  have hηcwp_meas : AEStronglyMeasurable
      (fun x => η x * chosenWeakPartial' (d := d) p i u Ω x)
      (volume.restrict Ω) :=
    hη_smooth.continuous.aestronglyMeasurable.mul
      (chosenWeakPartial'_memLp_of_mem hu i).aestronglyMeasurable
  have hderiv_cont : Continuous
      (fun x : E => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ))) :=
    (hη_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const
  have hdηu_meas : AEStronglyMeasurable
      (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x)
      (volume.restrict Ω) :=
    hderiv_cont.aestronglyMeasurable.mul hu.1.aestronglyMeasurable
  -- Replace the chosen partial by the explicit a.e.-equal sum.
  rw [eLpNorm_congr_ae hae]
  -- Convert lambda-form into the pointwise sum so we can apply the triangle.
  have hSumEq :
      (fun x => η x * chosenWeakPartial' (d := d) p i u Ω x +
        (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x) =
      (fun x => η x * chosenWeakPartial' (d := d) p i u Ω x) +
      (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x) := by
    funext x
    simp [Pi.add_apply]
  rw [hSumEq]
  have htriangle :
      eLpNorm
          ((fun x => η x * chosenWeakPartial' (d := d) p i u Ω x) +
            fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x)
          p (volume.restrict Ω)
        ≤ eLpNorm (fun x => η x * chosenWeakPartial' (d := d) p i u Ω x)
            p (volume.restrict Ω) +
          eLpNorm
            (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x)
            p (volume.restrict Ω) :=
    eLpNorm_add_le hηcwp_meas hdηu_meas hp_one
  refine htriangle.trans ?_
  -- Bound each summand.
  have hbnd1 :
      eLpNorm (fun x => η x * chosenWeakPartial' (d := d) p i u Ω x)
          p (volume.restrict Ω)
        ≤ ENNReal.ofReal C *
          eLpNorm (chosenWeakPartial' (d := d) p i u Ω) p (volume.restrict Ω) :=
    eLpNorm_eta_mul_le (d := d) hΩ hη_bound (chosenWeakPartial' p i u Ω)
  have hbnd2 :
      eLpNorm (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x)
          p (volume.restrict Ω)
        ≤ ENNReal.ofReal C * eLpNorm u p (volume.restrict Ω) :=
    eLpNorm_partial_eta_mul_le (d := d) hΩ hη_grad_bound i u
  exact add_le_add hbnd1 hbnd2

/-! ## Helpers for ENNReal arithmetic on the constant `K` -/

/-- `ENNReal.ofReal C = ENNReal.ofReal (max C 0)`: the unsigned-real coercion
already truncates negative values. -/
lemma ofReal_eq_ofReal_max_zero (C : ℝ) :
    ENNReal.ofReal C = ENNReal.ofReal (max C 0) := by
  rcases lt_or_ge C 0 with hC | hC
  · have hmax : max C 0 = 0 := max_eq_right hC.le
    rw [hmax, ENNReal.ofReal_of_nonpos hC.le]
    simp
  · have hmax : max C 0 = C := max_eq_left hC
    rw [hmax]

/-- The natural-number cast `(1 + d : ℝ≥0∞)` equals `ENNReal.ofReal ((d : ℝ) + 1)`. -/
lemma natCast_one_add_d_eq_ofReal (d : ℕ) :
    ((1 + d : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((1 + d : ℕ) : ℝ) := by
  rw [ENNReal.ofReal_natCast]

/-- `(1 + d : ℝ≥0∞) · ENNReal.ofReal C` equals `ENNReal.ofReal ((1 + d) · max C 0)`. -/
lemma natCast_one_add_d_mul_ofReal (d : ℕ) (C : ℝ) :
    (((1 + d : ℕ) : ℝ≥0∞) * ENNReal.ofReal C) =
      ENNReal.ofReal (((1 + d : ℕ) : ℝ) * max C 0) := by
  have hnn : (0 : ℝ) ≤ ((1 + d : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [natCast_one_add_d_eq_ofReal d, ofReal_eq_ofReal_max_zero C,
      ← ENNReal.ofReal_mul hnn]

/-! ## The main quantitative bound -/

/-- For a smooth function `η : E → ℝ` with `‖η‖ ≤ C` and `‖∇η‖ ≤ C` on the open
set `Ω`, the multiplication operation `u ↦ η · u` is uniformly bounded on
`W^{1,p}(Ω)` by a constant depending only on `C` and the dimension `d`.

Formally, there exists `K > 0` (depending only on `C` and `d`) such that for
every `u ∈ W^{1,p}(Ω)`,
`wkpNorm 1 p (η · u) Ω ≤ ENNReal.ofReal K · wkpNorm 1 p u Ω`. -/
theorem wkpNorm_smul_smooth_bounded_le_one
    {d : ℕ} [NeZero d]
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ_open : IsOpen Ω)
    {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    {C : ℝ}
    (hη_bound : ∀ x ∈ Ω, ‖η x‖ ≤ C)
    (hη_grad_bound : ∀ x ∈ Ω, ‖fderiv ℝ η x‖ ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : MemWkp 1 p u Ω) :
    ∃ K : ℝ, 0 < K ∧ ∀ {u : EuclideanSpace ℝ (Fin d) → ℝ}, MemWkp 1 p u Ω →
      wkpNorm 1 p (fun x => η x * u x) Ω ≤ ENNReal.ofReal K * wkpNorm 1 p u Ω := by
  classical
  -- Discard the unused outer `(hu)` witness; the bound is uniform in `u`.
  let _ := hu
  let _ := hp_top
  -- The hypothesis is already at the smooth level.
  have hη_smooth' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η := hη_smooth
  -- Choose `K := (1 + d) * (max C 0 + 1)`.
  set K : ℝ := ((1 + d : ℕ) : ℝ) * (max C 0 + 1) with hK_def
  have h_natpos : (0 : ℝ) < ((1 + d : ℕ) : ℝ) := by
    have h : (0 : ℕ) < 1 + d := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right _ _)
    exact_mod_cast h
  have hK_pos : 0 < K := by
    have hMaxNonneg : (0 : ℝ) ≤ max C 0 := le_max_right _ _
    have h1 : (0 : ℝ) < max C 0 + 1 := by linarith
    exact mul_pos h_natpos h1
  refine ⟨K, hK_pos, ?_⟩
  intro v hv
  have hv_W1p : DeGiorgi.MemW1p (d := d) p v Ω := hv.memW1p
  -- Useful abbreviations.
  set Au : ℝ≥0∞ := eLpNorm v p (volume.restrict Ω) with hAu_def
  set Bu : Fin d → ℝ≥0∞ :=
    fun i => eLpNorm (chosenWeakPartial' p i v Ω) p (volume.restrict Ω)
    with hBu_def
  set OC : ℝ≥0∞ := ENNReal.ofReal C with hOC_def
  set OK : ℝ≥0∞ := ENNReal.ofReal K with hOK_def
  -- Pointwise bounds for the LHS pieces.
  have h_eta_v_bnd :
      eLpNorm (fun x => η x * v x) p (volume.restrict Ω) ≤ OC * Au :=
    eLpNorm_eta_mul_le (d := d) hΩ_open hη_bound v
  have h_chosen_bnd : ∀ i : Fin d,
      eLpNorm (chosenWeakPartial' p i (fun x => η x * v x) Ω) p
          (volume.restrict Ω)
        ≤ OC * Bu i + OC * Au := fun i =>
    eLpNorm_chosenWeakPartial'_smul_smooth_bounded_le (d := d) hp_one hΩ_open
      hη_smooth' hη_bound hη_grad_bound hv_W1p i
  -- Expand `wkpNorm 1 p _ Ω`.
  -- Use `Finset.sum_range_succ` (with `range (1+1) = range 2 = range 1 + {1}`)
  -- and `Finset.sum_range_one` (the j=0 term is a singleton sum).
  have hLHS_unfold : wkpNorm (d := d) 1 p (fun x => η x * v x) Ω =
      eLpNorm (fun x => η x * v x) p (volume.restrict Ω) +
      ∑ α : Fin 1 → Fin d,
        eLpNorm (iterWeakPartial (d := d) p 1 α (fun x => η x * v x) Ω) p
          (volume.restrict Ω) := by
    unfold wkpNorm
    rw [show (1 : ℕ) + 1 = 1 + 1 from rfl]
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    -- The `j=0` term collapses to `eLpNorm (η·v)`.
    have h0_unique : ∀ α : Fin 0 → Fin d, α = (fun i : Fin 0 => i.elim0) :=
      fun α => by funext i; exact i.elim0
    haveI : Unique (Fin 0 → Fin d) :=
      { default := fun i : Fin 0 => i.elim0
        uniq := fun α => (h0_unique α).symm ▸ rfl }
    rw [Fintype.sum_unique
          (f := fun α : Fin 0 → Fin d =>
            eLpNorm (iterWeakPartial (d := d) p 0 α (fun x => η x * v x) Ω) p
              (volume.restrict Ω))]
    simp [iterWeakPartial_zero]
  have hRHS_unfold : wkpNorm (d := d) 1 p v Ω =
      Au +
      ∑ α : Fin 1 → Fin d,
        eLpNorm (iterWeakPartial (d := d) p 1 α v Ω) p (volume.restrict Ω) := by
    unfold wkpNorm
    rw [show (1 : ℕ) + 1 = 1 + 1 from rfl]
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have h0_unique : ∀ α : Fin 0 → Fin d, α = (fun i : Fin 0 => i.elim0) :=
      fun α => by funext i; exact i.elim0
    haveI : Unique (Fin 0 → Fin d) :=
      { default := fun i : Fin 0 => i.elim0
        uniq := fun α => (h0_unique α).symm ▸ rfl }
    rw [Fintype.sum_unique
          (f := fun α : Fin 0 → Fin d =>
            eLpNorm (iterWeakPartial (d := d) p 0 α v Ω) p (volume.restrict Ω))]
    simp [iterWeakPartial_zero, hAu_def]
  -- Reduce iterWeakPartial p 1 α to chosenWeakPartial' p (α 0).
  have hIter1_eta_v : ∀ α : Fin 1 → Fin d,
      iterWeakPartial (d := d) p 1 α (fun x => η x * v x) Ω =
        chosenWeakPartial' (d := d) p (α 0) (fun x => η x * v x) Ω := by
    intro α
    rw [iterWeakPartial_succ]
    rfl
  have hIter1_v : ∀ α : Fin 1 → Fin d,
      iterWeakPartial (d := d) p 1 α v Ω =
        chosenWeakPartial' (d := d) p (α 0) v Ω := by
    intro α
    rw [iterWeakPartial_succ]
    rfl
  have hLHS_unfold' : wkpNorm (d := d) 1 p (fun x => η x * v x) Ω =
      eLpNorm (fun x => η x * v x) p (volume.restrict Ω) +
      ∑ α : Fin 1 → Fin d,
        eLpNorm (chosenWeakPartial' (d := d) p (α 0) (fun x => η x * v x) Ω) p
          (volume.restrict Ω) := by
    rw [hLHS_unfold]
    refine congrArg (eLpNorm (fun x => η x * v x) p (volume.restrict Ω) + ·) ?_
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [hIter1_eta_v α]
  have hRHS_unfold' : wkpNorm (d := d) 1 p v Ω =
      Au +
      ∑ α : Fin 1 → Fin d,
        eLpNorm (chosenWeakPartial' (d := d) p (α 0) v Ω) p (volume.restrict Ω) := by
    rw [hRHS_unfold]
    refine congrArg (Au + ·) ?_
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [hIter1_v α]
  -- Rewrite the gradient sum as `Σ α, Bu (α 0)`.
  have hSumBu :
      ∑ α : Fin 1 → Fin d,
          eLpNorm (chosenWeakPartial' (d := d) p (α 0) v Ω) p
            (volume.restrict Ω) =
        ∑ α : Fin 1 → Fin d, Bu (α 0) := by
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [hBu_def]
  rw [hLHS_unfold', hRHS_unfold', hSumBu]
  -- Bound the gradient sum using `h_chosen_bnd`.
  have hSum_chosen_bnd :
      ∑ α : Fin 1 → Fin d,
          eLpNorm (chosenWeakPartial' (d := d) p (α 0) (fun x => η x * v x) Ω) p
            (volume.restrict Ω)
        ≤ ∑ α : Fin 1 → Fin d, (OC * Bu (α 0) + OC * Au) :=
    Finset.sum_le_sum (fun α _ => h_chosen_bnd (α 0))
  -- Combined LHS bound.
  refine (add_le_add h_eta_v_bnd hSum_chosen_bnd).trans ?_
  -- Now we want:
  -- OC * Au + Σ_α (OC * Bu (α 0) + OC * Au) ≤ OK * (Au + Σ_α Bu (α 0))
  -- Use `Finset.sum_add_distrib` to split the Σ.
  have hSum_split :
      ∑ α : Fin 1 → Fin d, (OC * Bu (α 0) + OC * Au) =
        (∑ α : Fin 1 → Fin d, OC * Bu (α 0)) +
        ∑ _α : Fin 1 → Fin d, OC * Au := Finset.sum_add_distrib
  rw [hSum_split]
  -- Σ_α OC * Au = (card Fin 1 → Fin d : ℕ) * (OC * Au) = d * (OC * Au).
  have hCard : (Finset.univ : Finset (Fin 1 → Fin d)).card = d := by
    rw [Finset.card_univ]
    simp
  have hSum_const :
      ∑ _α : Fin 1 → Fin d, OC * Au = (d : ℝ≥0∞) * (OC * Au) := by
    rw [Finset.sum_const, hCard, nsmul_eq_mul]
  rw [hSum_const]
  -- Σ_α OC * Bu (α 0) = OC * Σ_α Bu (α 0).
  have hSum_factor :
      ∑ α : Fin 1 → Fin d, OC * Bu (α 0) = OC * ∑ α : Fin 1 → Fin d, Bu (α 0) := by
    rw [Finset.mul_sum]
  rw [hSum_factor]
  -- Now: LHS = OC * Au + (OC * Σ Bu + d * (OC * Au))
  --        = (1 + d) * OC * Au + OC * Σ Bu (after rearrangement).
  -- Distribute (mul_add, add_mul) for OK.
  -- We bound:
  --   OC * Au + (OC * Σ Bu + d * (OC * Au)) ≤ OK * Au + OK * Σ Bu = OK * (Au + Σ Bu).
  -- For this, use:
  --   (a) OC * Au + d * (OC * Au) = (1 + d) * OC * Au ≤ OK * Au.
  --   (b) OC * Σ Bu ≤ OK * Σ Bu.
  set SBu : ℝ≥0∞ := ∑ α : Fin 1 → Fin d, Bu (α 0) with hSBu_def
  -- Step (a): (1 + d) * OC ≤ OK.
  have h_one_plus_d_OC_le_OK : ((1 + d : ℕ) : ℝ≥0∞) * OC ≤ OK := by
    rw [hOC_def, hOK_def, natCast_one_add_d_mul_ofReal]
    apply ENNReal.ofReal_le_ofReal
    -- Goal: ((1 + d : ℕ) : ℝ) * max C 0 ≤ K = (1 + d : ℕ) * (max C 0 + 1).
    have hMaxNonneg : (0 : ℝ) ≤ max C 0 := le_max_right _ _
    have : max C 0 ≤ max C 0 + 1 := by linarith
    have hMul := mul_le_mul_of_nonneg_left this h_natpos.le
    -- hMul : ((1 + d : ℕ) : ℝ) * max C 0 ≤ ((1 + d : ℕ) : ℝ) * (max C 0 + 1) = K.
    exact hMul
  -- Step (b): OC ≤ OK.
  have h_OC_le_OK : OC ≤ OK := by
    rw [hOC_def, hOK_def, ofReal_eq_ofReal_max_zero]
    apply ENNReal.ofReal_le_ofReal
    -- Goal: max C 0 ≤ K = (1 + d : ℕ) * (max C 0 + 1).
    have hMaxNonneg : (0 : ℝ) ≤ max C 0 := le_max_right _ _
    have h1 : max C 0 ≤ max C 0 + 1 := by linarith
    have h2 : (0 : ℝ) < (1 + d : ℕ) := h_natpos
    have h3 : (1 : ℝ) ≤ ((1 + d : ℕ) : ℝ) := by
      have h : (1 : ℕ) ≤ 1 + d := Nat.le_add_right _ _
      exact_mod_cast h
    -- (max C 0) ≤ max C 0 + 1 ≤ ((1+d):ℝ) * (max C 0 + 1)
    have h4 : max C 0 + 1 ≤ ((1 + d : ℕ) : ℝ) * (max C 0 + 1) := by
      have hPos : 0 ≤ max C 0 + 1 := by linarith
      have := mul_le_mul_of_nonneg_right h3 hPos
      simpa [one_mul] using this
    linarith
  -- Now do the final algebra.
  -- LHS expression: OC * Au + (OC * SBu + d * (OC * Au))
  --   = OC * Au + d * OC * Au + OC * SBu
  --   = (1 + d) * OC * Au + OC * SBu  [factor]
  --   ≤ OK * Au + OK * SBu             [using (a) and (b)]
  --   = OK * (Au + SBu)
  change OC * Au + (OC * SBu + (d : ℝ≥0∞) * (OC * Au)) ≤ OK * (Au + SBu)
  -- Convert (a) into useful form: OC + d * OC = (1 + d) * OC.
  have h_factor_one_plus_d :
      OC + (d : ℝ≥0∞) * OC = ((1 + d : ℕ) : ℝ≥0∞) * OC := by
    rw [show ((1 + d : ℕ) : ℝ≥0∞) = 1 + (d : ℝ≥0∞) by push_cast; ring]
    rw [add_mul, one_mul]
  -- Rearrange LHS: OC * Au + (OC * SBu + d * (OC * Au))
  --              = (OC + d * OC) * Au + OC * SBu.
  have h_lhs_factor :
      OC * Au + (OC * SBu + (d : ℝ≥0∞) * (OC * Au)) =
        ((1 + d : ℕ) : ℝ≥0∞) * OC * Au + OC * SBu := by
    rw [← h_factor_one_plus_d, add_mul]
    -- (OC + d * OC) * Au = OC * Au + d * OC * Au
    -- We need to align with: OC * Au + (OC * SBu + d * (OC * Au)).
    -- (OC * Au + d * OC * Au) + OC * SBu = OC * Au + d * OC * Au + OC * SBu.
    -- Compare: OC * Au + (OC * SBu + d * (OC * Au)) = OC * Au + OC * SBu + d * (OC * Au).
    -- Both are commutative re-orderings.
    ring
  rw [h_lhs_factor]
  -- Now: LHS = (1 + d) * OC * Au + OC * SBu ≤ OK * Au + OK * SBu = OK * (Au + SBu).
  -- Bound each term.
  have hbnd_Au : ((1 + d : ℕ) : ℝ≥0∞) * OC * Au ≤ OK * Au :=
    mul_le_mul_left h_one_plus_d_OC_le_OK Au
  have hbnd_SBu : OC * SBu ≤ OK * SBu :=
    mul_le_mul_left h_OC_le_OK SBu
  calc
    ((1 + d : ℕ) : ℝ≥0∞) * OC * Au + OC * SBu
        ≤ OK * Au + OK * SBu := add_le_add hbnd_Au hbnd_SBu
    _ = OK * (Au + SBu) := by rw [mul_add]

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
