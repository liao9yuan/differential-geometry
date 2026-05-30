import DifferentialGeometry.Geometry.Riemannian.AlongCurve
import DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Riemannian.Variation.ParallelTransport

/-!
# Parallel orthonormal perpendicular frame along a geodesic

For a `C^∞` unit-speed geodesic `γ : ℝ → M` on `Icc 0 L` with `L > 0`, this
file isolates the construction and supporting bridges for a parallel
orthonormal frame `e : Fin (finrank E - 1) → SectionAlongCurve I M γ` of the
`g`-orthogonal complement of the velocity `t ↦ dγ_t(1)`:

* `exists_parallel_orthonormal_perp_frame` — existence of the frame: each
  `e i` is differentiable, parallel along `γ` (moving-foot
  `chartCovDerivAlong g (γ t) γ (e i) t = 0`), the frame is `g`-orthonormal
  pointwise, and each `e i` is `g`-orthogonal to the velocity.
* `perp_to_velocity_preserved` — a parallel section that is `g`-orthogonal to
  the velocity at `t = 0` stays `g`-orthogonal to the velocity for all `t`.
* `chartCovDerivAlong_movingFoot_eq_zero_of_isParallelChart_centered` — the
  foot bridge from `IsParallelChart` to the moving-foot `chartCovDerivAlong`.

The foot identity relating a section's value to the inverse-trivialisation of
its chart representation is already available as `symmL_chartRepAt_self`
(`CovariantDerivativeAlong`), so it is consumed directly rather than restated here.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation

/-! ## Abstract `g`-Gram–Schmidt of a `g`-linearly-independent family

For a positive-definite symmetric bilinear form `B : E →L[ℝ] E →L[ℝ] ℝ` and a
`B`-linearly-independent family `v : Fin m → E`, the hand-rolled Gram–Schmidt
recursion produces a `B`-orthonormal family `bGramSchmidt B v : Fin m → E`. This
is the pointwise algebraic core (no smoothness, no chart data) underlying the
parallel perpendicular frame; it is the inner-product `B := g.inner (γ 0)`
specialisation of the established chart-frame orthonormalisation, written
abstractly so it applies to a basis of the `g`-orthogonal complement of the
geodesic velocity. -/

namespace PerpFrameAux

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The normalised Gram–Schmidt vector at index `i` for the `B`-bilinear form
applied to the family `v`. Defined by well-founded recursion on `i.val`. -/
private noncomputable def bGramSchmidt
    (B : F →L[ℝ] F →L[ℝ] ℝ) {m : ℕ} (v : Fin m → F) (i : Fin m) : F :=
  let raw : F :=
    v i - ∑ j : Fin i.val,
      (B (v i) (bGramSchmidt B v ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
        bGramSchmidt B v ⟨j.val, lt_trans j.isLt i.isLt⟩
  (Real.sqrt (B raw raw))⁻¹ • raw
termination_by i.val
decreasing_by exact j.isLt

/-- The unnormalised Gram–Schmidt vector at index `i`:
`raw_i = v i - ∑_{j < i} B(v i, e_j) • e_j`. -/
private noncomputable def bGramSchmidtRaw
    (B : F →L[ℝ] F →L[ℝ] ℝ) {m : ℕ} (v : Fin m → F) (i : Fin m) : F :=
  v i - ∑ j : Fin i.val,
    (B (v i) (bGramSchmidt B v ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
      bGramSchmidt B v ⟨j.val, lt_trans j.isLt i.isLt⟩

private lemma bGramSchmidt_eq
    (B : F →L[ℝ] F →L[ℝ] ℝ) {m : ℕ} (v : Fin m → F) (i : Fin m) :
    bGramSchmidt B v i =
      (Real.sqrt (B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i)))⁻¹ •
        bGramSchmidtRaw B v i := by
  unfold bGramSchmidt bGramSchmidtRaw
  rfl

/-- Bilinear distribution in the right slot. -/
private lemma B_sum_right
    (B : F →L[ℝ] F →L[ℝ] ℝ) (x : F)
    {ι : Type*} (s : Finset ι) (w : ι → F) (c : ι → ℝ) :
    B x (∑ k ∈ s, c k • w k) = ∑ k ∈ s, c k * B x (w k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has, map_add,
      show (B x) (c a • w a) = c a * B x (w a) from by
        rw [map_smul, smul_eq_mul], ih]

/-- The self `B`-norm of the `i`-th Gram–Schmidt vector is `1`, provided the
raw vector is nonzero (and `B` is positive-definite). -/
private lemma bGramSchmidt_self_norm
    (B : F →L[ℝ] F →L[ℝ] ℝ)
    (Bpos : ∀ x : F, x ≠ 0 → 0 < B x x)
    {m : ℕ} (v : Fin m → F) (i : Fin m)
    (hne : bGramSchmidtRaw B v i ≠ 0) :
    B (bGramSchmidt B v i) (bGramSchmidt B v i) = 1 := by
  have hpos : 0 < B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i) := Bpos _ hne
  have hs_sq : Real.sqrt (B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i)) *
      Real.sqrt (B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i)) =
      B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i) :=
    Real.mul_self_sqrt (le_of_lt hpos)
  set s : ℝ := Real.sqrt (B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i)) with hs_def
  have hei_eq : bGramSchmidt B v i = s⁻¹ • bGramSchmidtRaw B v i := by
    rw [bGramSchmidt_eq B v i, ← hs_def]
  rw [hei_eq]
  have hsmul : B (s⁻¹ • bGramSchmidtRaw B v i) (s⁻¹ • bGramSchmidtRaw B v i) =
      s⁻¹ * (s⁻¹ * B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i)) := by
    have h1 : B (s⁻¹ • bGramSchmidtRaw B v i) = s⁻¹ • B (bGramSchmidtRaw B v i) := by
      rw [map_smul]
    rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show (B (bGramSchmidtRaw B v i)) (s⁻¹ • bGramSchmidtRaw B v i) =
        s⁻¹ * B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i) from by
      rw [map_smul, smul_eq_mul]]
  rw [hsmul]
  rw [show s⁻¹ * (s⁻¹ * B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i)) =
      (s * s)⁻¹ * B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i) from by
    rw [mul_inv]; ring]
  rw [hs_sq]; exact inv_mul_cancel₀ (ne_of_gt hpos)

set_option maxHeartbeats 4000000 in
/-- Strong-induction package: for a `B`-linearly-independent family `v`,
the Gram–Schmidt recursion is well-defined (raw vectors nonzero) and
`B`-orthonormal. `B` is assumed symmetric and positive-definite. -/
private theorem bGramSchmidt_orth_strong_aux
    (B : F →L[ℝ] F →L[ℝ] ℝ)
    (Bsymm : ∀ x y : F, B x y = B y x)
    (Bpos : ∀ x : F, x ≠ 0 → 0 < B x x)
    {m : ℕ} (v : Fin m → F) (hLI : LinearIndependent ℝ v) :
    ∀ k : ℕ, ∀ i : Fin m, i.val ≤ k →
      bGramSchmidtRaw B v i ≠ 0 ∧
      (∀ j : Fin m, j.val < i.val →
        B (bGramSchmidt B v j) (bGramSchmidt B v i) = 0) ∧
      B (bGramSchmidt B v i) (bGramSchmidt B v i) = 1 := by
  classical
  intro k
  induction k with
  | zero =>
    intro i hi_le
    have hi_val : i.val = 0 := Nat.le_zero.mp hi_le
    have hempty : IsEmpty (Fin i.val) := by rw [hi_val]; exact Fin.isEmpty
    have hraw : bGramSchmidtRaw B v i = v i := by
      unfold bGramSchmidtRaw
      rw [Finset.sum_eq_zero (fun j _ => hempty.elim j)]
      simp
    have hne : bGramSchmidtRaw B v i ≠ 0 := by rw [hraw]; exact hLI.ne_zero i
    refine ⟨hne, ?_, ?_⟩
    · intro j hj; rw [hi_val] at hj; omega
    · -- ⟨e_i, e_i⟩ = 1, with raw_i = v i ≠ 0.
      exact bGramSchmidt_self_norm B Bpos v i hne
  | succ k ih =>
    intro i hi_le
    by_cases hi_lt : i.val ≤ k
    · exact ih i hi_lt
    · have hi_eq : i.val = k + 1 := by omega
      have ih_below : ∀ j : Fin m, j.val < i.val →
          bGramSchmidtRaw B v j ≠ 0 ∧
          (∀ j' : Fin m, j'.val < j.val →
            B (bGramSchmidt B v j') (bGramSchmidt B v j) = 0) ∧
          B (bGramSchmidt B v j) (bGramSchmidt B v j) = 1 :=
        fun j hj => ih j (by omega)
      -- Step 1: orthogonality of raw_i to each e_j with j.val < i.val.
      have horth_raw : ∀ j : Fin m, j.val < i.val →
          B (bGramSchmidt B v j) (bGramSchmidtRaw B v i) = 0 := by
        intro j hj_lt
        rw [show bGramSchmidtRaw B v i =
            v i - ∑ j' : Fin i.val,
              (B (v i) (bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩ from rfl]
        rw [map_sub]
        rw [B_sum_right B (bGramSchmidt B v j) (Finset.univ : Finset (Fin i.val))
            (fun j' => bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩)
            (fun j' => B (v i)
              (bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩))]
        have hsum_eq :
            ∑ j' ∈ (Finset.univ : Finset (Fin i.val)),
                B (v i) (bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩) *
                  B (bGramSchmidt B v j)
                    (bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩) =
              B (bGramSchmidt B v j) (v i) := by
          set j_inFin : Fin i.val := ⟨j.val, hj_lt⟩
          rw [Finset.sum_eq_single j_inFin]
          · -- the j' = j term: B(v i, e_j) * B(e_j, e_j) = B(v i, e_j) = B(e_j, v i).
            have hj_eq : (⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩ : Fin m) = j :=
              Fin.ext rfl
            rw [hj_eq, (ih_below j hj_lt).2.2, mul_one, Bsymm]
          · intro j' _ hj'
            have hj'_neq : j'.val ≠ j.val := fun h => hj' (Fin.ext h)
            by_cases hcompare : j'.val < j.val
            · have hzero := (ih_below j hj_lt).2.1
                ⟨j'.val, lt_trans hcompare j.isLt⟩ hcompare
              rw [show B (bGramSchmidt B v j)
                  (bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩) =
                  B (bGramSchmidt B v ⟨j'.val, lt_trans hcompare j.isLt⟩)
                    (bGramSchmidt B v j) from by rw [Bsymm]]
              rw [hzero, mul_zero]
            · have hcompare' : j.val < j'.val :=
                lt_of_le_of_ne (Nat.le_of_not_lt hcompare) hj'_neq.symm
              have hzero := (ih_below ⟨j'.val, lt_trans j'.isLt i.isLt⟩ j'.isLt).2.1
                j hcompare'
              rw [hzero, mul_zero]
          · intro h; exact absurd (Finset.mem_univ j_inFin) h
        rw [hsum_eq, Bsymm (bGramSchmidt B v j) (v i)]; ring
      -- Step 2: raw_i ≠ 0 (else v i ∈ span of earlier e's ⊆ span of earlier v's).
      have hraw_ne : bGramSchmidtRaw B v i ≠ 0 := by
        intro hraw_zero
        have hv_eq : v i =
            ∑ j' : Fin i.val,
              (B (v i) (bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := by
          have h_eq : v i -
              ∑ j' : Fin i.val,
                (B (v i) (bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                  bGramSchmidt B v ⟨j'.val, lt_trans j'.isLt i.isLt⟩ = 0 := by
            simpa [bGramSchmidtRaw] using hraw_zero
          exact sub_eq_zero.mp h_eq
        -- e_j ∈ span {v 0, …, v (i-1)} for all j < i.
        have h_e_in_span : ∀ kk : ℕ, ∀ mm : Fin m, mm.val ≤ kk → mm.val < i.val →
            bGramSchmidt B v mm ∈
              Submodule.span ℝ
                ((fun n : Fin i.val => v ⟨n.val, lt_trans n.isLt i.isLt⟩) '' Set.univ) := by
          intro kk
          induction kk with
          | zero =>
            intro mm hm_le hm_lt
            have hm_val : mm.val = 0 := Nat.le_zero.mp hm_le
            have hempty : IsEmpty (Fin mm.val) := by rw [hm_val]; exact Fin.isEmpty
            rw [bGramSchmidt_eq B v mm]
            apply Submodule.smul_mem
            have hraw_mm : bGramSchmidtRaw B v mm = v mm := by
              unfold bGramSchmidtRaw
              rw [Finset.sum_eq_zero (fun j _ => hempty.elim j)]; simp
            rw [hraw_mm]
            apply Submodule.subset_span
            exact ⟨⟨mm.val, hm_lt⟩, Set.mem_univ _, rfl⟩
          | succ kk ih_kk =>
            intro mm hm_le hm_lt
            by_cases hcase : mm.val ≤ kk
            · exact ih_kk mm hcase hm_lt
            · rw [bGramSchmidt_eq B v mm]
              apply Submodule.smul_mem
              unfold bGramSchmidtRaw
              apply Submodule.sub_mem
              · apply Submodule.subset_span
                exact ⟨⟨mm.val, hm_lt⟩, Set.mem_univ _, rfl⟩
              · apply Submodule.sum_mem
                intro j _
                apply Submodule.smul_mem
                have hj_in : j.val < i.val := lt_trans j.isLt hm_lt
                have hj_le : j.val ≤ kk := by have := j.isLt; omega
                exact ih_kk ⟨j.val, lt_trans j.isLt mm.isLt⟩ hj_le hj_in
        have hvi_in_span : v i ∈
            Submodule.span ℝ
              ((fun n : Fin i.val => v ⟨n.val, lt_trans n.isLt i.isLt⟩) '' Set.univ) := by
          rw [hv_eq]
          apply Submodule.sum_mem
          intro j' _
          apply Submodule.smul_mem
          have hj'_le : j'.val ≤ k := by have := j'.isLt; omega
          exact h_e_in_span k ⟨j'.val, lt_trans j'.isLt i.isLt⟩ hj'_le j'.isLt
        -- Contradiction with LI.
        have hset_eq :
            ((fun n : Fin i.val => v ⟨n.val, lt_trans n.isLt i.isLt⟩) '' Set.univ) =
              (v '' {n : Fin m | n.val < i.val}) := by
          ext x
          constructor
          · rintro ⟨n, _, rfl⟩
            exact ⟨⟨n.val, lt_trans n.isLt i.isLt⟩, n.isLt, rfl⟩
          · rintro ⟨n, hn, rfl⟩
            exact ⟨⟨n.val, hn⟩, Set.mem_univ _, rfl⟩
        rw [hset_eq] at hvi_in_span
        have hi_notin : i ∉ {n : Fin m | n.val < i.val} := by simp [Set.mem_setOf_eq]
        exact hLI.notMem_span_image hi_notin hvi_in_span
      -- Step 3: orthogonality + unit-norm of e_i.
      set s : ℝ := Real.sqrt (B (bGramSchmidtRaw B v i) (bGramSchmidtRaw B v i))
        with hs_def
      have hei_eq : bGramSchmidt B v i = s⁻¹ • bGramSchmidtRaw B v i := by
        rw [bGramSchmidt_eq B v i, ← hs_def]
      refine ⟨hraw_ne, ?_, ?_⟩
      · intro j hj_lt
        rw [hei_eq,
          show (B (bGramSchmidt B v j)) (s⁻¹ • bGramSchmidtRaw B v i) =
            s⁻¹ * B (bGramSchmidt B v j) (bGramSchmidtRaw B v i) from by
          rw [map_smul, smul_eq_mul]]
        rw [horth_raw j hj_lt, mul_zero]
      · exact bGramSchmidt_self_norm B Bpos v i hraw_ne

/-- **`B`-orthonormality of the abstract Gram–Schmidt family.** For a symmetric
positive-definite bilinear form `B` and a `B`-linearly-independent family `v`,
`bGramSchmidt B v` is `B`-orthonormal: `B (e i) (e j) = δ_{ij}`. -/
private theorem bGramSchmidt_orthonormal
    (B : F →L[ℝ] F →L[ℝ] ℝ)
    (Bsymm : ∀ x y : F, B x y = B y x)
    (Bpos : ∀ x : F, x ≠ 0 → 0 < B x x)
    {m : ℕ} (v : Fin m → F) (hLI : LinearIndependent ℝ v) (i j : Fin m) :
    B (bGramSchmidt B v i) (bGramSchmidt B v j) = if i = j then 1 else 0 := by
  classical
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · have h := bGramSchmidt_orth_strong_aux B Bsymm Bpos v hLI j.val j (le_refl _)
    have hne : i ≠ j := fun h_eq => by rw [h_eq] at hlt; omega
    rw [if_neg hne]; exact h.2.1 i hlt
  · have hij : i = j := Fin.ext heq
    rw [if_pos hij, ← hij]
    exact (bGramSchmidt_orth_strong_aux B Bsymm Bpos v hLI i.val i (le_refl _)).2.2
  · have h := bGramSchmidt_orth_strong_aux B Bsymm Bpos v hLI i.val i (le_refl _)
    have hne : i ≠ j := fun h_eq => by rw [h_eq] at hgt; omega
    rw [if_neg hne, Bsymm]; exact h.2.1 j hgt

/-- Each Gram–Schmidt output lies in the submodule spanned by the input family
(in fact in the span of `v`); hence if every `v k` lies in a submodule `W`, so
does every `bGramSchmidt B v i`. -/
private theorem bGramSchmidt_mem
    (B : F →L[ℝ] F →L[ℝ] ℝ) {m : ℕ} (v : Fin m → F)
    (W : Submodule ℝ F) (hv : ∀ k, v k ∈ W) (i : Fin m) :
    bGramSchmidt B v i ∈ W := by
  classical
  -- Strong recursion on `i.val`.
  induction hk : i.val using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    subst hk
    rw [bGramSchmidt_eq B v i]
    apply Submodule.smul_mem
    unfold bGramSchmidtRaw
    refine W.sub_mem (hv i) (Submodule.sum_mem _ ?_)
    intro j _
    exact Submodule.smul_mem _ _ (ih j.val j.isLt ⟨j.val, lt_trans j.isLt i.isLt⟩ rfl)

end PerpFrameAux

section PerpFrame

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

set_option linter.unusedVariables false in
/-- **Perpendicularity to the velocity is preserved.** If a section `V` along a
`C^∞` geodesic `γ` is parallel (the intrinsic covariant derivative
`covDerivAlong g γ V` vanishes on `Icc 0 L`) and `V 0` is `g`-orthogonal to the
velocity `dγ_0(1)` at the basepoint, then `V t` is `g`-orthogonal to the
velocity `dγ_t(1)` for every `t ∈ Icc 0 L`. The mechanism is constancy of the
genuine Riemannian inner product `t ↦ g(γ t)(V t, dγ_t(1))`: at every point its
derivative is computed in the chart pinned at the foot `γ t` by the
covariant-derivative product rule
(`chartGramAlongCurve_hasDerivAt_covariant`), and both correction terms vanish
— the `V`-term because `V` is parallel (the foot-chart covariant derivative is
the chart-coordinate of `covDerivAlong g γ V`, which is `0`), the velocity-term
because `γ` is a geodesic (the velocity field is parallel,
`covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt`).

The regularity hypothesis `hVdiff` (the chart-coordinate representation
`chartRepAt γ V t` is differentiable at the foot `t`) is the standard
"`V` varies differentiably along `γ`" assumption shared with
`covDerivAlong_add` / `covDerivAlong_smulFun`; without it the chart-Gram form
is not differentiable and `covDerivAlong = 0` (which reads `deriv` of a possibly
non-differentiable representation) carries no propagation content. -/
theorem perp_to_velocity_preserved
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hgeo : IsGeodesic (I := I) g γ)
    {L : ℝ} (hL : 0 < L) (V : ∀ t, TangentSpace I (γ t))
    (hVdiff : ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t)
    (hVpar : ∀ t ∈ Set.Icc (0 : ℝ) L, covDerivAlong (I := I) g γ V t = 0)
    (hPerp0 : g.inner (γ 0) (V 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (V t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 0 := by
  classical
  -- The genuine Riemannian inner product as a function of the parameter.
  set vel : ℝ → ∀ s, TangentSpace I (γ s) :=
    fun _ s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E) with hvel_def
  set f : ℝ → ℝ := fun t => g.inner (γ t) (V t)
    (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) with hf_def
  -- We show: `f` is constant on `Icc 0 L`, equal to `f 0 = 0`.
  -- For the constancy engine we need: (a) `f` continuous on `Icc 0 L`,
  -- (b) `HasDerivWithinAt f 0 (Ici t) t` for every `t ∈ Ico 0 L`.
  -- Both follow from a local computation in the chart pinned at the foot `γ t`.
  --
  -- ### Local statement at a foot time `t₀ ∈ Icc 0 L`.
  -- In the chart at `α := γ t₀`, the chart-coordinate representations of `V` and
  -- the velocity field are `Vrep := chartRepAt γ V t₀` and
  -- `urep := chartRepAt γ (velocity) t₀`. On a neighbourhood of `t₀` (where `γ s`
  -- stays in the chart's base set) the round-trip `symmL ∘ continuousLinearMapAt`
  -- is the identity, so `f` agrees with the chart-Gram form of `Vrep`, `urep`.
  have hlocal : ∀ t₀ ∈ Set.Icc (0 : ℝ) L, HasDerivAt f 0 t₀ := by
    intro t₀ ht₀
    set α : M := γ t₀ with hα_def
    set Vrep : ℝ → E := chartRepAt (I := I) γ V t₀ with hVrep_def
    set urep : ℝ → E :=
      chartRepAt (I := I) γ (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E)) t₀ with hurep_def
    -- `γ t₀ = α` lies in the base set of the trivialisation/chart at `α`.
    have hbase_t₀ : γ t₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source H (γ t₀)
    -- The base set is an open neighbourhood of times whose curve point sits in it.
    have hbaseSet_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
      (trivializationAt E (TangentSpace I) α).open_baseSet
    have hsrc_open : IsOpen {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet} :=
      hbaseSet_open.preimage hγ.continuous
    have hsrc_mem : {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet} ∈ 𝓝 t₀ :=
      hsrc_open.mem_nhds hbase_t₀
    -- ### Round trip: on this neighbourhood, the section equals `symmL ∘ rep`.
    have hVround : ∀ s ∈ {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet},
        (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Vrep s) = V s := by
      intro s hs
      simpa [hVrep_def, chartRepAt_apply] using
        (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
          (R := ℝ) hs (V s)
    have huround : ∀ s ∈ {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet},
        (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (urep s) =
          (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E) := by
      intro s hs
      simpa [hurep_def, chartRepAt_apply] using
        (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
          (R := ℝ) hs ((mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E))
    -- ### `f` agrees with the chart-Gram form of `Vrep`, `urep` near `t₀`.
    have hf_eq : f =ᶠ[𝓝 t₀]
        fun s => AlongCurve.chartGramAlongCurve (I := I) g α γ Vrep urep s := by
      filter_upwards [hsrc_mem] with s hs
      have hVs := hVround s hs
      have hus := huround s hs
      -- `f s = g.inner (γ s) (symmL (γ s) (Vrep s)) (symmL (γ s) (urep s))`.
      have : f s = g.inner (γ s)
          ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Vrep s))
          ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (urep s)) := by
        rw [hf_def]; rw [hVs, hus]
      rw [this, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α (Vrep s) (urep s)]
      rw [AlongCurve.chartGramAlongCurve_def]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      -- `chartGramMatrix g α (γ s) = chartGramOnE g α · (chartCurve α γ s)`.
      have hinv : (extChartAt I α).symm (chartCurve (I := I) α γ s) = γ s := by
        rw [chartCurve_def]
        refine (extChartAt I α).left_inv ?_
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        rw [TangentBundle.trivializationAt_baseSet] at hs
        exact hs
      rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_def, hinv]
    -- ### The chart trajectory has the prescribed velocity at `t₀`.
    -- `u := chartCurve α γ`, with `u(t₀) ∈ interior target`.
    have hu_hasDerivAt :
        HasDerivAt (chartCurve (I := I) α γ)
          (deriv (chartCurve (I := I) α γ) t₀) t₀ := by
      have hcd : ContDiffAt ℝ ∞ (chartCurve (I := I) α γ) t₀ := by
        have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
            ((extChartAt I α) ∘ γ) t₀ := by
          have hφ : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) (γ t₀) :=
            contMDiffAt_extChartAt (I := I) (x := α) (n := ∞)
          exact hφ.comp t₀ (hγ.contMDiffAt)
        exact contMDiffAt_iff_contDiffAt.mp hmdiff
      exact (hcd.differentiableAt (by simp)).hasDerivAt
    have hmem_int : chartCurve (I := I) α γ t₀ ∈ interior (extChartAt I α).target := by
      have hxsrc : γ t₀ ∈ (extChartAt I α).source := by
        rw [extChartAt_source]; exact mem_chart_source H (γ t₀)
      exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
        (I := I) α ((extChartAt I α).map_source hxsrc)
    -- ### `Vrep` is differentiable at `t₀` (foot regularity hypothesis).
    have hVrep_hasDerivAt : HasDerivAt Vrep (deriv Vrep t₀) t₀ :=
      ((hVdiff t₀ ht₀).hasDerivAt)
    -- ### The open neighbourhood of times whose curve point sits in the chart source.
    set U : Set ℝ := γ ⁻¹' (chartAt H α).source with hU_def
    have hU_open : IsOpen U := (chartAt H α).open_source.preimage hγ.continuous
    have ht₀_U : t₀ ∈ U := by
      rw [hU_def, Set.mem_preimage]; exact mem_chart_source H (γ t₀)
    have hU_nhds : U ∈ 𝓝 t₀ := hU_open.mem_nhds ht₀_U
    -- The chart trajectory `chartCurve α γ = extChartAt I α ∘ γ` is `C^∞` on `U`.
    have hu_cdiffOn : ContDiffOn ℝ ∞ (chartCurve (I := I) α γ) U := by
      have h_comp_mdiff :
          ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ((extChartAt I α) ∘ γ) U := by
        have hφ : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
          contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
        have hγU : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ U := hγ.contMDiffOn
        have hmaps : Set.MapsTo γ U (chartAt H α).source := fun s hs => hs
        exact hφ.comp hγU hmaps
      have hfun : (chartCurve (I := I) α γ) = ((extChartAt I α) ∘ γ) := rfl
      rw [hfun]
      exact contMDiffOn_iff_contDiffOn.mp h_comp_mdiff
    -- ### `urep` equals `deriv u` on `U` (chain-rule identity for the velocity coordinate).
    have hurep_eqOn : Set.EqOn urep (deriv (chartCurve (I := I) α γ)) U := by
      intro s hs
      have hs' : γ s ∈ (chartAt H α).source := hs
      rw [hurep_def, chartRepAt_apply]
      rw [MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
        (I := I) (M := M) (γ := γ) hγ α (t := s) hs']
      rfl
    have hurep_eq : urep =ᶠ[𝓝 t₀] deriv (chartCurve (I := I) α γ) :=
      hurep_eqOn.eventuallyEq_of_mem hU_nhds
    -- `deriv u` is `C^∞` on `U`, hence differentiable at `t₀`.
    have hu_deriv_hasDerivAt :
        HasDerivAt (deriv (chartCurve (I := I) α γ))
          (deriv (deriv (chartCurve (I := I) α γ)) t₀) t₀ := by
      have hderiv_u_cdiffOn :
          ContDiffOn ℝ ∞ (deriv (chartCurve (I := I) α γ)) U :=
        hu_cdiffOn.deriv_of_isOpen hU_open (by exact_mod_cast (le_refl (∞ : WithTop ℕ∞)))
      exact ((hderiv_u_cdiffOn.differentiableOn (by simp) t₀ ht₀_U).differentiableAt
        hU_nhds).hasDerivAt
    have hurep_hasDerivAt : HasDerivAt urep (deriv (deriv (chartCurve (I := I) α γ)) t₀) t₀ :=
      hu_deriv_hasDerivAt.congr_of_eventuallyEq hurep_eq
    -- ### The chart-Gram form has derivative `0` at `t₀` by the covariant product rule.
    have hgram :=
      AlongCurve.chartGramAlongCurve_hasDerivAt_covariant (I := I) g α γ Vrep urep
        (uPrime := fun _ => deriv (chartCurve (I := I) α γ) t₀)
        (Vprime := fun _ => deriv Vrep t₀)
        (Wprime := fun _ => deriv (deriv (chartCurve (I := I) α γ)) t₀)
        hu_hasDerivAt hmem_int hVrep_hasDerivAt hurep_hasDerivAt
    -- The two covariant correction terms equal the foot-chart covariant derivatives.
    -- For `Vrep`: `chartCovDerivAlong g α γ Vrep t₀ = covDerivAlong's chart coord = 0`.
    have hcorrV :
        deriv Vrep t₀ +
          chartChristoffelContraction (I := I) g α
            (deriv (chartCurve (I := I) α γ) t₀) (Vrep t₀)
            (chartCurve (I := I) α γ t₀) = 0 := by
      have : chartCovDerivAlong (I := I) g α γ Vrep t₀ = 0 := by
        rw [hα_def, hVrep_def]
        exact (covDerivAlong_eq_zero_iff (I := I) g γ V t₀).mp (hVpar t₀ ht₀)
      rw [chartCovDerivAlong_def] at this
      exact this
    -- For `urep`: the velocity field is parallel because `γ` is a geodesic.
    have hcorru :
        deriv (deriv (chartCurve (I := I) α γ)) t₀ +
          chartChristoffelContraction (I := I) g α
            (deriv (chartCurve (I := I) α γ) t₀) (urep t₀)
            (chartCurve (I := I) α γ t₀) = 0 := by
      have hgeoeq := hgeo.hasGeodesicEquationAt t₀
      have hvel0 :
          covDerivAlong (I := I) g γ
            (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E)) t₀ = 0 :=
        (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt (I := I) g γ t₀ hγ).mpr hgeoeq
      have hchart0 : chartCovDerivAlong (I := I) g α γ urep t₀ = 0 := by
        rw [hα_def, hurep_def]
        exact (covDerivAlong_eq_zero_iff (I := I) g γ
          (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) : E)) t₀).mp hvel0
      rw [chartCovDerivAlong_def] at hchart0
      -- `deriv urep t₀ = deriv (deriv u) t₀` since `urep =ᶠ deriv u` near `t₀`.
      rw [hurep_eq.deriv_eq] at hchart0
      exact hchart0
    -- Substitute the vanishing corrections into the derivative value: it is `0`.
    have hderiv0 : HasDerivAt
        (fun s => AlongCurve.chartGramAlongCurve (I := I) g α γ Vrep urep s) 0 t₀ := by
      -- The two covariant-correction terms (`Vprime + Γ(u', V)` and
      -- `Wprime + Γ(u', W)`) vanish at `t₀`, so the whole derivative value is `0`.
      convert hgram using 1
      simp only [hcorrV, hcorru]
      simp
    -- Transfer the derivative back to `f`.
    exact hderiv0.congr_of_eventuallyEq hf_eq
  -- ### `f` is continuous on `Icc 0 L` and has zero right-derivative on `Ico 0 L`.
  have hcont : ContinuousOn f (Set.Icc 0 L) :=
    fun t ht => ((hlocal t ht).continuousAt).continuousWithinAt
  have hderivWithin : ∀ x ∈ Set.Ico (0 : ℝ) L, HasDerivWithinAt f 0 (Set.Ici x) x := by
    intro x hx
    exact (hlocal x (Set.mem_Icc_of_Ico hx)).hasDerivWithinAt
  -- ### Constancy on `Icc 0 L`.
  have hconst : ∀ x ∈ Set.Icc (0 : ℝ) L, f x = f 0 :=
    constant_of_has_deriv_right_zero hcont hderivWithin
  -- ### Conclude: `f t = f 0 = 0`.
  intro t ht
  have hft := hconst t ht
  -- `f t = f 0` and `f 0 = g.inner (γ 0) (V 0) (dγ_0 1) = 0` by hypothesis.
  rw [hf_def] at hft
  simp only at hft
  rw [hft]
  exact hPerp0

/-- **Existence of a parallel orthonormal perpendicular frame.** For a `C^∞`
unit-speed geodesic `γ` on `Icc 0 L` (`L > 0`), there is a frame
`e : Fin (finrank E - 1) → SectionAlongCurve I M γ` such that each `e i` is
differentiable on `Icc 0 L`, parallel along `γ` (the *intrinsic* covariant
derivative `covDerivAlong g γ (e i) t` vanishes), the frame is pointwise
`g`-orthonormal, and each frame vector is `g`-orthogonal to the velocity
`dγ_t(1)`. This is the standalone form of the frame package consumed in the
Bonnet–Myers second-variation contradiction.

The construction is the genuine Gram–Schmidt-of-an-orthonormal-basis-of
`(γ'(0))^⊥`-then-parallel-transport: seed an orthonormal basis of the
`g`-orthogonal complement of `dγ_0(1)` at the basepoint `γ 0` and parallel
transport each seed along `γ` (`parallelTransport`); the transported sections
are parallel by construction (`parallelTransport_isParallel`, bridged to the
intrinsic `covDerivAlong` via `covDerivAlong_eq_zero_iff` /
`chartCovDerivAlong_movingFoot_eq_zero_of_isParallelChart_centered`),
`g`-orthonormality is preserved by parallel transport
(`parallelTransport_preserves_inner_product`), and perpendicularity to the
velocity is preserved because the velocity field of a geodesic is itself
parallel (`perp_to_velocity_preserved`). -/
theorem exists_parallel_orthonormal_perp_frame
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hgeo : IsGeodesic (I := I) g γ)
    {L : ℝ} (hL : 0 < L)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 1) :
    ∃ e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ,
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (e i).toFun t) t) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        covDerivAlong (I := I) g γ (e i).toFun t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) ((e i).toFun t) ((e j).toFun t) =
          if i = j then 1 else 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
        g.inner (γ t) ((e i).toFun t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 0) := by
  classical
  -- The base point, velocity, and the bilinear form `B := g.inner (γ 0)`.
  set u₀ : E := (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) with hu₀_def
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (γ 0) with hB_def
  have hBsymm : ∀ x y : E, B x y = B y x := fun x y => g.symm (γ 0) x y
  have hBpos : ∀ x : E, x ≠ 0 → 0 < B x x := fun x hx => g.pos (γ 0) x hx
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_refl _, hL.le⟩
  -- `u₀` is `B`-unit, hence nonzero, and the functional `B u₀` is nonzero.
  have hu₀_unit : B u₀ u₀ = 1 := hUnit 0 h0mem
  have hu₀_ne : u₀ ≠ 0 := by
    intro h; rw [h] at hu₀_unit; simp at hu₀_unit
  -- The `g`-orthogonal complement of `u₀`: the kernel of the functional `B u₀`.
  set φ : E →ₗ[ℝ] ℝ := (B u₀).toLinearMap with hφ_def
  set W : Submodule ℝ E := LinearMap.ker φ with hW_def
  -- `φ` is surjective (since `φ u₀ = 1 ≠ 0`), so `finrank W = finrank E - 1`.
  have hφ_u₀ : φ u₀ = 1 := hu₀_unit
  have hφ_surj : Function.Surjective φ := by
    intro c
    refine ⟨c • u₀, ?_⟩
    rw [map_smul, hφ_u₀, smul_eq_mul, mul_one]
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ_surj
  have hfr_range : Module.finrank ℝ ↥(LinearMap.range φ) = 1 := by
    rw [hrange]; simp
  have hfinrankW : Module.finrank ℝ ↥W = Module.finrank ℝ E - 1 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker φ
    rw [hfr_range] at hsum
    have : Module.finrank ℝ ↥W = Module.finrank ℝ ↥(LinearMap.ker φ) := rfl
    rw [this]; omega
  -- A basis of `W`, indexed by `Fin (finrank E - 1)`.
  letI : Module.Finite ℝ ↥W := inferInstance
  set bW : Module.Basis (Fin (Module.finrank ℝ E - 1)) ℝ ↥W :=
    Module.finBasisOfFinrankEq ℝ ↥W hfinrankW with hbW_def
  -- The basis vectors as a `B`-linearly-independent family of `E`-vectors in `W`.
  set vfam : Fin (Module.finrank ℝ E - 1) → E := fun i => (bW i : E) with hvfam_def
  have hvfam_mem : ∀ i, vfam i ∈ W := fun i => (bW i).2
  have hvfam_LI : LinearIndependent ℝ vfam := by
    have hbWLI : LinearIndependent ℝ (fun i => bW i) := bW.linearIndependent
    have := hbWLI.map' (W.subtype) (Submodule.ker_subtype W)
    exact this
  -- The `B`-orthonormal Gram–Schmidt seed of the perpendicular subspace.
  set seed : Fin (Module.finrank ℝ E - 1) → E :=
    fun i => PerpFrameAux.bGramSchmidt B vfam i with hseed_def
  have hseed_ON : ∀ i j, B (seed i) (seed j) = if i = j then 1 else 0 :=
    fun i j => PerpFrameAux.bGramSchmidt_orthonormal B hBsymm hBpos vfam hvfam_LI i j
  have hseed_mem : ∀ i, seed i ∈ W :=
    fun i => PerpFrameAux.bGramSchmidt_mem B vfam W hvfam_mem i
  -- Each seed vector is `g`-orthogonal to `u₀` (it lies in `W = ker (B u₀)`).
  have hseed_perp : ∀ i, B (seed i) u₀ = 0 := by
    intro i
    have hker : φ (seed i) = 0 := (LinearMap.mem_ker).mp (hseed_mem i)
    have : B u₀ (seed i) = 0 := hker
    rw [hBsymm (seed i) u₀]; exact this
  -- Parallel-transport each seed vector along `γ` over `Icc 0 L`.
  have htransport : ∀ i, ∃ V : ∀ t, TangentSpace I (γ t),
      V 0 = seed i ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, covDerivAlong (I := I) g γ V t = 0) := by
    intro i
    exact DifferentialGeometry.Geometry.Riemannian.Variation.exists_global_parallel_transport_on_Icc
      (I := I) g γ hγ hL (seed i)
  choose Vfun hV0 hVdiff hVpar using htransport
  -- The frame: each transported section, wrapped as a `SectionAlongCurve`.
  refine ⟨fun i => ⟨fun t => Vfun i t⟩, ?_, ?_, ?_, ?_⟩
  · -- Chart-representation differentiability (from the global transport).
    intro i t ht; exact hVdiff i t ht
  · -- Parallelism: intrinsic covariant derivative vanishes (from the transport).
    intro i t ht; exact hVpar i t ht
  · -- `g`-orthonormality: transport is a `g`-isometry, seed is `g`-orthonormal.
    intro t ht i j
    have hconst :=
      DifferentialGeometry.Geometry.Riemannian.Variation.global_parallel_transport_preserves_inner
        (I := I) g γ hγ hL.le (Vfun i) (Vfun j)
        (hVdiff i) (hVdiff j) (hVpar i) (hVpar j) t ht
    -- `g.inner (γ t) (Vi t) (Vj t) = g.inner (γ 0) (seed i) (seed j) = B (seed i)(seed j)`.
    rw [show ((fun i => (⟨fun t => Vfun i t⟩ : SectionAlongCurve I M γ)) i).toFun t = Vfun i t
        from rfl,
      show ((fun i => (⟨fun t => Vfun i t⟩ : SectionAlongCurve I M γ)) j).toFun t = Vfun j t
        from rfl]
    rw [hconst, hV0 i, hV0 j]
    exact hseed_ON i j
  · -- `g`-perpendicularity to the velocity (from `perp_to_velocity_preserved`).
    intro t ht i
    have hperp :=
      perp_to_velocity_preserved (I := I) g γ hγ hgeo hL (Vfun i)
        (hVdiff i) (hVpar i)
        (by
          -- `g.inner (γ 0) (Vi 0) (dγ_0 1) = B (seed i) u₀ = 0`.
          rw [hV0 i]
          exact hseed_perp i)
        t ht
    rw [show ((fun i => (⟨fun t => Vfun i t⟩ : SectionAlongCurve I M γ)) i).toFun t = Vfun i t
        from rfl]
    exact hperp

/-- **Parallel orthonormal frame perpendicular to the geodesic velocity field.**
For a unit-speed geodesic `γ` on `[0, L]` with velocity `uPrime t = γ'(t)`
(`huPrimeEq` pins `uPrime t = mfderiv γ t (1)` and `hUnit` records unit speed),
there is a frame `e : Fin (finrank E - 1) → SectionAlongCurve I M γ` whose every
member is differentiable (in its chart representation), parallel along `γ` (the
intrinsic `covDerivAlong g γ (e i) t = 0`), pointwise `g`-orthonormal, and
`g`-orthogonal to the velocity `uPrime t`.

This is the velocity-field-indexed restatement of
`exists_parallel_orthonormal_perp_frame`: the only difference is that the
perpendicularity clause is phrased against the supplied `uPrime` rather than
the bare `mfderiv γ t (1)`; the two coincide by `huPrimeEq`, so the result is a
direct reduction to the underlying frame. -/
theorem parallel_on_frame_perp_to_geodesic
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hgeo : IsGeodesic (I := I) g γ) {L : ℝ} (hL : 0 < L)
    (uPrime : ℝ → E)
    (huPrimeEq : ∀ t ∈ Set.Icc (0 : ℝ) L,
      (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ) : E) = uPrime t)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (uPrime t) (uPrime t) = 1) :
    ∃ e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ,
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (e i).toFun t) t) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        covDerivAlong (I := I) g γ (e i).toFun t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) ((e i).toFun t) ((e j).toFun t) =
          if i = j then 1 else 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
        g.inner (γ t) ((e i).toFun t) (uPrime t) = 0) := by
  -- Feed the proven frame's `hUnit` (phrased on `mfderiv γ t 1`) by rewriting
  -- the supplied unit-speed hypothesis through `huPrimeEq`.
  have hUnit' : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 1 := by
    intro t ht
    rw [huPrimeEq t ht]; exact hUnit t ht
  obtain ⟨e, hdiff, hpar, hON, hperp⟩ :=
    exists_parallel_orthonormal_perp_frame (I := I) g γ hγ hgeo hL hUnit'
  refine ⟨e, hdiff, hpar, hON, ?_⟩
  -- Transfer the perpendicularity clause: the proven frame is `g`-orthogonal to
  -- `mfderiv γ t 1`; rewrite to `uPrime t` via `huPrimeEq`.
  intro t ht i
  have := hperp t ht i
  rwa [huPrimeEq t ht] at this

/-- **Foot bridge: chart parallelism implies moving-foot covariant vanishing.**
If a section's `E`-valued representation `X` is parallel along `γ` in the chart
centred at the foot `γ t` (the predicate `IsParallelChart` for the foot-centred
chart curve velocity, on a neighbourhood `s` of `t`), then the moving-foot
chart-local covariant derivative `chartCovDerivAlong g (γ t) γ X t` vanishes. -/
theorem chartCovDerivAlong_movingFoot_eq_zero_of_isParallelChart_centered
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {X : ℝ → E} {s : Set ℝ} {t : ℝ}
    (hX : IsParallelChart (I := I) g (γ t) γ
      (fun τ => deriv (AlongCurve.chartCurve (I := I) (γ t) γ) τ) X s)
    (ht : t ∈ s) :
    chartCovDerivAlong (I := I) g (γ t) γ X t = 0 := by
  -- The parallel-transport ODE at `t` gives the time-derivative of `X`.
  have hd := hX.hasDerivAt ht
  -- Extract `deriv X t` from `HasDerivAt`.
  have hderiv := hd.deriv
  -- Unfold the covariant-derivative formula and substitute.
  rw [chartCovDerivAlong_def, hderiv]
  abel

end PerpFrame

end DifferentialGeometry.Geometry.Riemannian

end
