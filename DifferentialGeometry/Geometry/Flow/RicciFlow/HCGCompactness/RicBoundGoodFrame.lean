import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.Claim1Wiring
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.QuadraticForm.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The good-frame producer for `ric_bound` (brick 1 + brick 2 wiring)

For the keystone frame (`exists_trivFrame_orthonormal_basis`: the trivialization
frame `e₀.localFrame basisE`, `gRef`-orthonormal at the centre `x`), this file
produces the data that converts intrinsic `gRef`-norm bounds over a small domain
into raw frame-component `ℓ²` bounds:

* `gramInv_inverse` — the inverse Gram matrix realizes the inverse metric in the
  frame basis at every point of the trivialization domain
  (`MetricInverseInBasis_gen`).
* `gramInv_symm` — the inverse Gram is symmetric.
* `gramE_eq_one` — at a point where the frame is `g`-orthonormal the Gram is `1`.

Downstream, `quad_lb_of_near_id` + `sum_comp_sq_le_pow_normSq0S`
(`KroneckerQuadForm.lean` / `Comparison.lean`) turn entrywise closeness of the
inverse Gram to `1` (continuity near the centre) into
`∑ comp² ≤ 2^s · normSq0S gRef`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- The inverse Gram matrix realizes the inverse metric of `g` in the
trivialization-frame basis, at every point of the trivialization domain. -/
theorem gramInv_inverse
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    {y : M} (hy : y ∈ e₀.baseSet) :
    Tensor0SBundle.MetricInverseInBasis_gen (I := I) g y
      ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hy)
      (fun i j => (gramE (I := I) e₀ g basisE y)⁻¹ i j) := by
  classical
  have hdet : IsUnit (gramE (I := I) e₀ g basisE y).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (gramE_posDef (I := I) e₀ g basisE hy).det_pos)
  have hco : ∀ k l : Idx,
      g.inner y
        (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hy) k)
        (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hy) l) =
      gramE (I := I) e₀ g basisE y k l := by
    intro k l
    rw [IsLocalFrameOn.toBasisAt_coe, IsLocalFrameOn.toBasisAt_coe]
    rfl
  intro i j
  constructor
  · have h := congrArg (fun A : Matrix Idx Idx Real => A i j)
      (Matrix.nonsing_inv_mul (gramE (I := I) e₀ g basisE y) hdet)
    simp only [Matrix.mul_apply, Matrix.one_apply] at h
    calc (∑ k : Idx, (gramE (I := I) e₀ g basisE y)⁻¹ i k *
            g.inner y
              (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hy) k)
              (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hy) j))
        = ∑ k : Idx, (gramE (I := I) e₀ g basisE y)⁻¹ i k *
            gramE (I := I) e₀ g basisE y k j :=
          Finset.sum_congr rfl fun k _ => by rw [hco]
      _ = if i = j then 1 else 0 := h
  · have h := congrArg (fun A : Matrix Idx Idx Real => A i j)
      (Matrix.mul_nonsing_inv (gramE (I := I) e₀ g basisE y) hdet)
    simp only [Matrix.mul_apply, Matrix.one_apply] at h
    calc (∑ k : Idx,
            g.inner y
              (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hy) i)
              (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hy) k) *
            (gramE (I := I) e₀ g basisE y)⁻¹ k j)
        = ∑ k : Idx, gramE (I := I) e₀ g basisE y i k *
            (gramE (I := I) e₀ g basisE y)⁻¹ k j :=
          Finset.sum_congr rfl fun k _ => by rw [hco]
      _ = if i = j then 1 else 0 := h

/-- The inverse Gram matrix is symmetric. -/
theorem gramInv_symm
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E) (y : M)
    (i j : Idx) :
    (gramE (I := I) e₀ g basisE y)⁻¹ i j = (gramE (I := I) e₀ g basisE y)⁻¹ j i := by
  have h := congr_fun (congr_fun ((gramE_herm (I := I) e₀ g basisE y).inv.eq) i) j
  simpa [Matrix.conjTranspose_apply] using h.symm

/-- At a point where the trivialization frame is `g`-orthonormal, the Gram
matrix is the identity. -/
theorem gramE_eq_one
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E) {x : M}
    (hON : ∀ i j : Idx,
      g.inner x (e₀.localFrame basisE i x) (e₀.localFrame basisE j x) =
        if i = j then 1 else 0) :
    gramE (I := I) e₀ g basisE x = 1 := by
  ext i j
  simp only [gramE, Matrix.of_apply, Matrix.one_apply]
  exact hON i j

/-- **The entrywise-continuity producer.**  Near a point of the trivialization
domain where the frame is `g`-orthonormal (`gramE = 1`), the inverse Gram is
entrywise within `ε` of the identity kernel on an open sub-neighborhood. -/
theorem gramInv_near_id
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    {x : M} (hx : x ∈ e₀.baseSet)
    (hONx : gramE (I := I) e₀ g basisE x = 1)
    {ε : Real} (hε : 0 < ε) :
    ∃ u' : Set M, IsOpen u' ∧ x ∈ u' ∧ u' ⊆ e₀.baseSet ∧
      ∀ z ∈ u', ∀ i j : Idx,
        |(gramE (I := I) e₀ g basisE z)⁻¹ i j - (if i = j then 1 else 0)| ≤ ε := by
  classical
  -- entrywise continuity of the Gram on the trivialization domain
  have hentry : ∀ i j : Idx, ContinuousWithinAt
      (fun z => gramE (I := I) e₀ g basisE z i j) e₀.baseSet x := by
    intro i j
    have h := (gCompField_mdiffOn (I := I) e₀ g basisE
      (Fin.snoc (fun _ : Fin 1 => i) j)).continuousOn
    have heq : ∀ z : M,
        gramE (I := I) e₀ g basisE z i j =
          frameComp0S (I := I) (metricTensorField (I := I) g)
            (fun a y' => e₀.localFrame basisE a y') z
            (Fin.snoc (fun _ : Fin 1 => i) j) := by
      intro z
      have h0 : (Fin.snoc (fun _ : Fin 1 => i) j : Fin 2 → Idx) 0 = i := by simp [Fin.snoc]
      have h1 : (Fin.snoc (fun _ : Fin 1 => i) j : Fin 2 → Idx) 1 = j := by simp [Fin.snoc]
      rw [frameComp0S_apply, metricTensorField_apply, h0, h1]
      rfl
    exact ((h.congr fun z _ => (heq z)).continuousWithinAt hx)
  -- the matrix-valued Gram map is continuous-within at `x`
  have hmat : ContinuousWithinAt
      (fun z => gramE (I := I) e₀ g basisE z) e₀.baseSet x := by
    have hpi : ContinuousWithinAt
        (fun z => (fun i j => gramE (I := I) e₀ g basisE z i j : Idx → Idx → Real))
        e₀.baseSet x := by
      rw [continuousWithinAt_pi]
      intro i
      rw [continuousWithinAt_pi]
      intro j
      exact hentry i j
    exact hpi
  -- the matrix inverse is continuous at `gramE x = 1`
  have hdet1 : (gramE (I := I) e₀ g basisE x).det = 1 := by
    rw [hONx, Matrix.det_one]
  have hinvc : ContinuousAt Inv.inv (gramE (I := I) e₀ g basisE x) := by
    apply continuousAt_matrix_inv
    rw [hdet1, Ring.inverse_eq_inv']
    exact continuousAt_inv₀ one_ne_zero
  have hinv_cwa : ContinuousWithinAt
      (fun z => (gramE (I := I) e₀ g basisE z)⁻¹) e₀.baseSet x :=
    hinvc.comp_continuousWithinAt hmat
  have hone : (gramE (I := I) e₀ g basisE x)⁻¹ = 1 := by
    rw [hONx]
    exact Matrix.inv_eq_left_inv (by rw [one_mul])
  -- per-entry eventual closeness
  have hev1 : ∀ i j : Idx, ∀ᶠ z in nhdsWithin x e₀.baseSet,
      |(gramE (I := I) e₀ g basisE z)⁻¹ i j - (if i = j then 1 else 0)| ≤ ε := by
    intro i j
    have hcwa : ContinuousWithinAt
        (fun z => (gramE (I := I) e₀ g basisE z)⁻¹ i j) e₀.baseSet x := by
      have h1 := (continuousWithinAt_pi.mp hinv_cwa) i
      exact (continuousWithinAt_pi.mp h1) j
    have hval : (gramE (I := I) e₀ g basisE x)⁻¹ i j = (if i = j then (1 : Real) else 0) := by
      rw [hone, Matrix.one_apply]
    have hb : ∀ᶠ t in nhds ((gramE (I := I) e₀ g basisE x)⁻¹ i j),
        |t - (if i = j then (1 : Real) else 0)| ≤ ε := by
      rw [hval]
      have hball := Metric.closedBall_mem_nhds (x := (if i = j then (1 : Real) else 0)) hε
      refine Filter.eventually_of_mem hball fun t ht => ?_
      simpa [Metric.mem_closedBall, Real.dist_eq] using ht
    exact hcwa.eventually hb
  -- combine the finitely many entries and extract an open neighborhood
  have hev : ∀ᶠ z in nhdsWithin x e₀.baseSet, ∀ i j : Idx,
      |(gramE (I := I) e₀ g basisE z)⁻¹ i j - (if i = j then 1 else 0)| ≤ ε := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact hev1 i j
  obtain ⟨t, htopen, hxt, hsub⟩ := mem_nhdsWithin.mp hev
  exact ⟨t ∩ e₀.baseSet, htopen.inter e₀.open_baseSet, ⟨hxt, hx⟩,
    Set.inter_subset_right, fun z hz => hsub hz⟩

/-- A finite-dimensional real vector space carrying a symmetric positive-definite
bilinear form admits a basis orthonormal for that form.  (Ported from
`ApproximateIsometry.lean`, which is currently not buildable against the tree;
dedup once that file is repaired.) -/
private theorem exists_orthonormalBasis_of_posDef
    {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    (B : LinearMap.BilinForm Real V) (hsymm : LinearMap.IsSymm B)
    (hpos : ∀ v : V, v ≠ 0 → 0 < B v v) :
    ∃ b : Module.Basis (Fin (Module.finrank Real V)) Real V,
      ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
  classical
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B) hsymm
  have hdpos : ∀ i, 0 < B (v i) (v i) := fun i => hpos (v i) (v.ne_zero i)
  set w : Fin (Module.finrank Real V) → Real :=
    fun i => (Real.sqrt (B (v i) (v i)))⁻¹ with hw
  have hwunit : ∀ i, IsUnit (w i) := by
    intro i
    refine isUnit_iff_ne_zero.mpr ?_
    simp only [hw]
    exact inv_ne_zero (Real.sqrt_pos.mpr (hdpos i)).ne'
  refine ⟨v.isUnitSMul hwunit, ?_⟩
  intro i j
  have hreduce :
      B ((v.isUnitSMul hwunit) i) ((v.isUnitSMul hwunit) j) =
        (w i * w j) * B (v i) (v j) := by
    simp only [Module.Basis.isUnitSMul_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    ring
  rw [hreduce]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hd : 0 < B (v i) (v i) := hdpos i
    have hroot :
        Real.sqrt (B (v i) (v i)) * Real.sqrt (B (v i) (v i)) = B (v i) (v i) :=
      Real.mul_self_sqrt hd.le
    simp only [hw]
    rw [← mul_inv, hroot, inv_mul_cancel₀ hd.ne']
  · rw [if_neg hij]
    have horth : B (v i) (v j) = 0 := (LinearMap.isOrthoᵢ_def.mp hv) i j hij
    rw [horth, mul_zero]

/-- **The keystone**: at each point, the canonical tangent trivialization carries
a model-fibre basis whose induced local frame is `g`-orthonormal at that point.
(Raw-values restatement of `exists_trivFrame_orthonormal_basis` from
`ApproximateIsometry.lean`, ported because that file is currently not buildable;
dedup once it is repaired.) -/
theorem exists_trivONBasis
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ basisE : Module.Basis (Fin (Module.finrank Real E)) Real E,
      ∀ i j : Fin (Module.finrank Real E),
        g.inner x
          ((trivializationAt E (TangentSpace I : M → Type _) x).localFrame basisE i x)
          ((trivializationAt E (TangentSpace I : M → Type _) x).localFrame basisE j x) =
        if i = j then 1 else 0 := by
  classical
  set e₀ := trivializationAt E (TangentSpace I : M → Type _) x with he₀
  have hxu0 : x ∈ e₀.baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x
  let Q : LinearMap.BilinForm Real E :=
    LinearMap.mk₂ Real
      (fun v w => g.inner x (e₀.symmL Real x v) (e₀.symmL Real x w))
      (fun _ _ _ => by simp [map_add, ContinuousLinearMap.add_apply])
      (fun _ _ _ => by simp [map_smul, ContinuousLinearMap.smul_apply])
      (fun _ _ _ => by simp [map_add])
      (fun _ _ _ => by simp [map_smul])
  have hsymm : LinearMap.IsSymm Q :=
    ⟨fun v w => by
      simp only [Q, LinearMap.mk₂_apply, RingHom.id_apply]
      exact g.symm x (e₀.symmL Real x v) (e₀.symmL Real x w)⟩
  have hpos : ∀ v : E, v ≠ 0 → 0 < Q v v := by
    intro v hv
    have hSv : e₀.symmL Real x v ≠ 0 := by
      intro h0
      apply hv
      have hself := e₀.continuousLinearMapAt_symmL (R := Real) hxu0 v
      rw [h0, map_zero] at hself
      exact hself.symm
    simp only [Q, LinearMap.mk₂_apply]
    exact g.pos x (e₀.symmL Real x v) hSv
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_of_posDef Q hsymm hpos
  have hsymmL : ∀ k, e₀.symmL Real x (b k) = e₀.localFrame b k x := fun k => by
    rw [e₀.localFrame_apply_of_mem_baseSet (b := b) hxu0]
    simp [Bundle.Trivialization.basisAt]
  refine ⟨b, fun i j => ?_⟩
  rw [← hsymmL i, ← hsymmL j]
  simpa [Q, LinearMap.mk₂_apply] using hb i j

/-- **The good-frame producer** (the per-point input of the `ric_bound`
assembly).  Every `x` has a basis `basisE` of the model fibre whose tangent
trivialization frame is `gRef`-orthonormal at `x`, together with an open
`u' ∋ x` inside the trivialization domain on which the raw frame-component `ℓ²`
of every `(0,s)`-tensor is bounded by `2^s` times its intrinsic squared
`gRef`-norm.  Chain: `exists_trivONBasis` (keystone) →
`gramE_eq_one` → `gramInv_near_id` (continuity) → `quad_lb_of_near_id` →
`sum_comp_sq_le_pow_normSq0S`. -/
theorem exists_goodFrame_compBound
    (gRef : SmoothRiemannianMetric I M) (x : M) :
    ∃ basisE : Module.Basis (Fin (Module.finrank Real E)) Real E,
      ∃ u' : Set M, IsOpen u' ∧ x ∈ u' ∧
        u' ⊆ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet ∧
        (∀ i j : Fin (Module.finrank Real E),
          gRef.inner x
            ((trivializationAt E (TangentSpace I : M → Type _) x).localFrame basisE i x)
            ((trivializationAt E (TangentSpace I : M → Type _) x).localFrame basisE j x) =
          if i = j then 1 else 0) ∧
        ∀ z, ∀ hz : z ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet,
          z ∈ u' → ∀ (s : ℕ) (A : Tensor0SSpace s I z),
            (∑ I0 : Fin s → Fin (Module.finrank Real E),
              Tensor0SBundle.component0S (I := I)
                (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).toBasisAt hz) A I0 ^ 2) ≤
              2 ^ s * Tensor0SBundle.normSq0S (I := I) gRef z s A := by
  classical
  obtain ⟨basisE, hONraw⟩ := exists_trivONBasis (I := I) gRef x
  set e₀ := trivializationAt E (TangentSpace I : M → Type _) x with he₀
  have hxbase : x ∈ e₀.baseSet := mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x
  have hONx : gramE (I := I) e₀ gRef basisE x = 1 :=
    gramE_eq_one (I := I) e₀ gRef basisE hONraw
  -- the entrywise-closeness radius
  set n : ℕ := Fintype.card (Fin (Module.finrank Real E)) with hn
  set ε : Real := 1 / (2 * ((n : Real) + 1)) with hε_def
  have hε : 0 < ε := by
    rw [hε_def]
    positivity
  have hsmall : (n : Real) * ε ≤ 1 / 2 := by
    rw [hε_def, mul_one_div, div_le_iff₀ (by positivity : (0 : Real) < 2 * ((n : Real) + 1))]
    have : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
    linarith
  obtain ⟨u', hopen, hxu', hsub, hnear⟩ :=
    gramInv_near_id (I := I) e₀ gRef basisE hxbase hONx hε
  refine ⟨basisE, u', hopen, hxu', hsub, hONraw, ?_⟩
  intro z hz hzu' s A
  -- the quadratic-form lower bound for the inverse Gram at `z`
  have hQlb := quad_lb_of_near_id
    (fun i j => (gramE (I := I) e₀ gRef basisE z)⁻¹ i j) ε hε.le
    (fun i j => hnear z hzu' i j) hsmall
  -- the component-versus-norm bound from `Comparison.lean`
  have hkey := Tensor0SBundle.sum_comp_sq_le_pow_normSq0S (I := I) gRef z s
    (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE)).toBasisAt hz)
    (fun i j => (gramE (I := I) e₀ gRef basisE z)⁻¹ i j) 2 two_pos
    (gramInv_inverse (I := I) e₀ gRef basisE hz)
    (fun i j => gramInv_symm (I := I) e₀ gRef basisE z i j)
    hQlb A
  -- bridge `component0S` ↔ `tensor0SComponent`
  calc (∑ I0 : Fin s → Fin (Module.finrank Real E),
        Tensor0SBundle.component0S (I := I)
          (((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE)).toBasisAt hz) A I0 ^ 2)
      = ∑ I0 : Fin s → Fin (Module.finrank Real E),
          Tensor0SBundle.tensor0SComponent (I := I) A
            (fun i => ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE)).toBasisAt hz i)
            I0 ^ 2 := by
        refine Finset.sum_congr rfl fun I0 _ => ?_
        rw [Tensor0SBundle.component0S_apply, Tensor0SBundle.tensor0SComponent_apply]
    _ ≤ 2 ^ s * Tensor0SBundle.normSq0S (I := I) gRef z s A := hkey

end DifferentialGeometry.PDE.RicciFlow
