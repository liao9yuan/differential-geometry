import RicciFlower.Tensor.RSTensor.Tensor0SRiemannian
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Riemannian Metrics on Mixed Tensor Fibers

`TensorRSSpace r s I x` is modeled as
`Tensor0SSpace r I x ->L Tensor0SSpace s I x`.  Once the metric-induced inner
products on the covariant tensor fibers are supplied, a mixed tensor gets its
inner product by the Hilbert-Schmidt formula

`<A, B> = tr(A^† B)`.

The construction below is fiberwise and metric-bound.  It uses the covariant
tensor metrics constructed recursively from the Riemannian metric.
-/

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

/-- Adjoint of an `(r,s)` tensor in the Hom model
`Tensor0SSpace r ->L Tensor0SSpace s`, using the supplied metric data on the
source and target covariant tensor fibers. -/
def adjointRS
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A : TensorRSSpace r s I x) :
    Tensor0SSpace s I x →ₗ[Real] Tensor0SSpace r I x :=
  MetricFiberData.adjoint
    (tensor0SMetricData (I := I) g x r)
    (tensor0SMetricData (I := I) g x s)
    A.toLinearMap

/-- The Hom-model adjoint is adjoint with respect to the metric-induced
inner products on the covariant source and target fibers. -/
theorem adjointRS_inner
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A : TensorRSSpace r s I x)
    (Y : Tensor0SSpace s I x) (X : Tensor0SSpace r I x) :
    inner0S (I := I) g x r (adjointRS (I := I) (g := g) (x := x) r s A Y) X =
      inner0S (I := I) g x s Y (A X) := by
  simpa [adjointRS, inner0S] using
    MetricFiberData.adjoint_inner
      (tensor0SMetricData (I := I) g x r)
      (tensor0SMetricData (I := I) g x s)
      A.toLinearMap Y X

/-- Metric-induced inner product on all `(r,s)` tensors in the realized
`TensorRSSpace` Hom model. -/
def innerRS
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A B : TensorRSSpace r s I x) : Real :=
  LinearMap.trace Real (Tensor0SSpace r I x)
    ((adjointRS (I := I) (g := g) (x := x) r s A).comp B.toLinearMap)

@[simp] theorem innerRS_eq_trace
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A B : TensorRSSpace r s I x) :
    innerRS (I := I) (g := g) (x := x) r s A B =
      LinearMap.trace Real (Tensor0SSpace r I x)
        ((adjointRS (I := I) (g := g) (x := x) r s A).comp B.toLinearMap) := by
  rfl

/-- Squared norm of a realized `(r,s)` tensor. -/
def normSqRS
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A : TensorRSSpace r s I x) : Real :=
  innerRS (I := I) (g := g) (x := x) r s A A

@[simp] theorem normSqRS_eq_inner
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A : TensorRSSpace r s I x) :
    normSqRS (I := I) (g := g) (x := x) r s A =
      innerRS (I := I) (g := g) (x := x) r s A A := by
  rfl

/-- Squared component size of a mixed `(r,s)` tensor in a tangent basis. -/
def componentL2SqRS
    {x : M} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    {r s : Nat} (A : TensorRSSpace r s I x) : Real :=
  ∑ upper : Fin r -> Idx, ∑ lower : Fin s -> Idx,
    (componentRS (I := I) basis A upper lower) ^ 2

private theorem slots_prod_nonneg
    {Idx : Type*} {s : Nat} {w : Idx -> Real}
    (hw_nonneg : forall i : Idx, 0 <= w i)
    (slots : Fin s -> Idx) :
    0 <= ∏ a : Fin s, w (slots a) := by
  exact Finset.prod_nonneg (fun a _ => hw_nonneg (slots a))

private theorem slots_prod_le_pow
    {Idx : Type*} {s : Nat} {w : Idx -> Real} {C : Real}
    (hw_nonneg : forall i : Idx, 0 <= w i)
    (hw_le : forall i : Idx, w i <= C)
    (slots : Fin s -> Idx) :
    (∏ a : Fin s, w (slots a)) <= C ^ s := by
  calc
    (∏ a : Fin s, w (slots a)) <= ∏ _a : Fin s, C := by
      exact Finset.prod_le_prod
        (fun a _ => hw_nonneg (slots a))
        (fun a _ => hw_le (slots a))
    _ = C ^ s := by simp

private theorem slots_prod_mul_eq_one
    {Idx : Type*} {s : Nat} {lam μ : Idx -> Real}
    (hlamμ : forall i : Idx, lam i * μ i = 1)
    (slots : Fin s -> Idx) :
    (∏ a : Fin s, lam (slots a)) * (∏ a : Fin s, μ (slots a)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  simp [hlamμ]

private theorem prod_diagonalInvMetric_eq_zero_of_ne
    {Idx : Type*} [DecidableEq Idx]
    {s : Nat} {μ : Idx -> Real} {I0 J0 : Fin s -> Idx}
    (hIJ : I0 ≠ J0) :
    (∏ a : Fin s, diagonalInvMetric μ (I0 a) (J0 a)) = 0 := by
  classical
  have hsome : exists a : Fin s, I0 a ≠ J0 a := by
    by_contra hnone
    apply hIJ
    funext a
    by_contra ha
    exact hnone ⟨a, ha⟩
  rcases hsome with ⟨a, ha⟩
  exact Finset.prod_eq_zero (Finset.mem_univ a)
    (diagonalInvMetric_eq_zero_of_ne (μ := μ) ha)

private theorem coordInner0S_diagonal_eq_sum_mul
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {x : M}
    (s : Nat) (μ : Idx -> Real)
    (A B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s (diagonalInvMetric μ) A B basis =
      ∑ I0 : Fin s -> Idx,
        (∏ a : Fin s, μ (I0 a)) *
          tensor0SComponent (I := I) A (fun i => basis i) I0 *
            tensor0SComponent (I := I) B (fun i => basis i) I0 := by
  classical
  unfold coordInner0S
  apply Finset.sum_congr rfl
  intro I0 _
  rw [Finset.sum_eq_single I0]
  · simp [diagonalInvMetric]
  · intro J0 _ hJ0
    have hprod :
        (∏ a : Fin s, diagonalInvMetric μ (I0 a) (J0 a)) = 0 :=
      prod_diagonalInvMetric_eq_zero_of_ne (μ := μ) (Ne.symm hJ0)
    rw [hprod]
    ring
  · intro hnotmem
    exact False.elim (hnotmem (Finset.mem_univ I0))

private theorem coord_eq_prod_mul_inner_diag_right
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h : SmoothMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (lam μ : Idx -> Real)
    (hhinv :
      MetricInverseInBasis (I := I) h x basis (diagonalInvMetric μ))
    (hlamμ : forall i : Idx, lam i * μ i = 1)
    (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    (tensor0SBasis (I := I) basis s).repr A slots =
      (∏ a : Fin s, lam (slots a)) *
        inner0S (I := I) h x s A (basisTensor0S (I := I) basis slots) := by
  classical
  rw [inner0S_eq_coord (I := I) h x s basis (diagonalInvMetric μ) hhinv]
  rw [coordInner0S_diagonal_eq_sum_mul (I := I) (x := x) s μ A
    (basisTensor0S (I := I) basis slots) basis]
  rw [Finset.sum_eq_single slots]
  · change
      (tensor0SBasis (I := I) basis s).repr A slots =
        (∏ a : Fin s, lam (slots a)) *
          ((∏ a : Fin s, μ (slots a)) *
            tensor0SComponent (I := I) A (fun i => basis i) slots *
              component0S (I := I) basis (basisTensor0S (I := I) basis slots) slots)
    rw [basisTensor0S_component]
    rw [tensor0SBasis_repr]
    have hprod := slots_prod_mul_eq_one hlamμ slots
    ring_nf at hprod ⊢
    rw [hprod]
    simp [component0S_apply]
  · intro slots' _ hslots'
    have hcomp :
        tensor0SComponent (I := I) (basisTensor0S (I := I) basis slots)
          (fun i => basis i) slots' = 0 := by
      change component0S (I := I) basis
        (basisTensor0S (I := I) basis slots) slots' = 0
      rw [basisTensor0S_component]
      simp [Ne.symm hslots']
    rw [hcomp]
    ring
  · intro hnotmem
    exact False.elim (hnotmem (Finset.mem_univ slots))

/-- In an orthonormal-coordinate basis, the Hilbert-Schmidt squared norm of a
mixed tensor is the sum of squares of its components. -/
theorem normSqRS_identity_eq_componentL2SqRS
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (r s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : TensorRSSpace r s I x) :
    normSqRS (I := I) (g := g) (x := x) r s A =
      componentL2SqRS (I := I) basis A := by
  classical
  rw [normSqRS_eq_inner, innerRS_eq_trace]
  rw [LinearMap.trace_eq_matrix_trace Real (tensor0SBasis (I := I) basis r)
    ((adjointRS (I := I) (g := g) (x := x) r s A).comp A.toLinearMap)]
  rw [Matrix.trace]
  unfold componentL2SqRS
  apply Finset.sum_congr rfl
  intro upper _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change
    (tensor0SBasis (I := I) basis r).repr
        ((adjointRS (I := I) (g := g) (x := x) r s A)
          (A (basisTensor0S (I := I) basis upper))) upper =
      ∑ lower : Fin s -> Idx,
        (componentRS (I := I) basis A upper lower) ^ 2
  rw [tensor0SBasis_repr]
  rw [← inner0S_basisTensor_right_identity (I := I) g x r basis hinv
    ((adjointRS (I := I) (g := g) (x := x) r s A)
      (A (basisTensor0S (I := I) basis upper))) upper]
  rw [adjointRS_inner]
  rw [inner0S_eq_coord (I := I) g x s basis
    (identityInvMetric (Idx := Idx)) hinv,
    coordInner0S_identity_eq_sum (I := I) (x := x) s
      (A (basisTensor0S (I := I) basis upper))
      (A (basisTensor0S (I := I) basis upper)) basis]
  apply Finset.sum_congr rfl
  intro lower _
  change
    componentRS (I := I) basis A upper lower *
        componentRS (I := I) basis A upper lower =
      (componentRS (I := I) basis A upper lower) ^ 2
  ring

/-- Mixed-tensor squared norm in a basis where the inverse metric is diagonal.

The factors `lam` are the diagonal metric components and `μ` are the diagonal
inverse-metric components, related by `lam i * μ i = 1`.  Upper indices
contribute `lam`; lower indices contribute `μ`. -/
theorem normSqRS_diag_eq_sum
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h : SmoothMetric I M) (x : M) (r s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (lam μ : Idx -> Real)
    (hhinv :
      MetricInverseInBasis (I := I) h x basis (diagonalInvMetric μ))
    (hlamμ : forall i : Idx, lam i * μ i = 1)
    (A : TensorRSSpace r s I x) :
    normSqRS (I := I) (g := h) (x := x) r s A =
      ∑ upper : Fin r -> Idx, ∑ lower : Fin s -> Idx,
        ((∏ a : Fin r, lam (upper a)) *
          (∏ b : Fin s, μ (lower b))) *
            (componentRS (I := I) basis A upper lower) ^ 2 := by
  classical
  rw [normSqRS_eq_inner, innerRS_eq_trace]
  rw [LinearMap.trace_eq_matrix_trace Real (tensor0SBasis (I := I) basis r)
    ((adjointRS (I := I) (g := h) (x := x) r s A).comp A.toLinearMap)]
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro upper _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change
    (tensor0SBasis (I := I) basis r).repr
        ((adjointRS (I := I) (g := h) (x := x) r s A)
          (A (basisTensor0S (I := I) basis upper))) upper =
      ∑ lower : Fin s -> Idx,
        ((∏ a : Fin r, lam (upper a)) *
          (∏ b : Fin s, μ (lower b))) *
            (componentRS (I := I) basis A upper lower) ^ 2
  rw [coord_eq_prod_mul_inner_diag_right
    (I := I) h x r basis lam μ hhinv hlamμ
    ((adjointRS (I := I) (g := h) (x := x) r s A)
      (A (basisTensor0S (I := I) basis upper))) upper]
  rw [adjointRS_inner]
  rw [inner0S_eq_coord (I := I) h x s basis (diagonalInvMetric μ) hhinv]
  rw [coordInner0S_diagonal_eq_sum_mul (I := I) (x := x) s μ
    (A (basisTensor0S (I := I) basis upper))
    (A (basisTensor0S (I := I) basis upper)) basis]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lower _
  change
    (∏ a : Fin r, lam (upper a)) *
        ((∏ b : Fin s, μ (lower b)) *
          componentRS (I := I) basis A upper lower *
            componentRS (I := I) basis A upper lower) =
      ((∏ a : Fin r, lam (upper a)) *
        (∏ b : Fin s, μ (lower b))) *
          (componentRS (I := I) basis A upper lower) ^ 2
  ring

/-- Upper squared-norm comparison for mixed tensors in a diagonal comparison
basis.  This is the finite-dimensional algebra behind MSM135 Lemma 3.13 for
mixed `(r,s)` tensors. -/
theorem normSqRS_diag_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g h : SmoothMetric I M) (x : M) (r s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (lam μ : Idx -> Real) (C : Real)
    (hginv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (hhinv :
      MetricInverseInBasis (I := I) h x basis (diagonalInvMetric μ))
    (hlamμ : forall i : Idx, lam i * μ i = 1)
    (hC_nonneg : 0 <= C)
    (hlam_nonneg : forall i : Idx, 0 <= lam i)
    (hμ_nonneg : forall i : Idx, 0 <= μ i)
    (hlam_le : forall i : Idx, lam i <= C)
    (hμ_le : forall i : Idx, μ i <= C)
    (A : TensorRSSpace r s I x) :
    normSqRS (I := I) (g := h) (x := x) r s A <=
      C ^ (r + s) * normSqRS (I := I) (g := g) (x := x) r s A := by
  classical
  rw [normSqRS_diag_eq_sum (I := I) h x r s basis lam μ hhinv hlamμ A]
  rw [normSqRS_identity_eq_componentL2SqRS (I := I) g x r s basis hginv A]
  unfold componentL2SqRS
  calc
    (∑ upper : Fin r -> Idx, ∑ lower : Fin s -> Idx,
        ((∏ a : Fin r, lam (upper a)) *
          (∏ b : Fin s, μ (lower b))) *
            (componentRS (I := I) basis A upper lower) ^ 2)
        <= ∑ upper : Fin r -> Idx, ∑ lower : Fin s -> Idx,
          C ^ (r + s) *
            (componentRS (I := I) basis A upper lower) ^ 2 := by
          apply Finset.sum_le_sum
          intro upper _
          apply Finset.sum_le_sum
          intro lower _
          have hup :
              (∏ a : Fin r, lam (upper a)) <= C ^ r :=
            slots_prod_le_pow hlam_nonneg hlam_le upper
          have hlow :
              (∏ b : Fin s, μ (lower b)) <= C ^ s :=
            slots_prod_le_pow hμ_nonneg hμ_le lower
          have hprod_lower_nonneg :
              0 <= ∏ b : Fin s, μ (lower b) :=
            slots_prod_nonneg hμ_nonneg lower
          have hCr_nonneg : 0 <= C ^ r := pow_nonneg hC_nonneg r
          have hweight :
              (∏ a : Fin r, lam (upper a)) *
                  (∏ b : Fin s, μ (lower b)) <= C ^ (r + s) := by
            calc
              (∏ a : Fin r, lam (upper a)) *
                  (∏ b : Fin s, μ (lower b)) <= C ^ r * C ^ s :=
                mul_le_mul hup hlow hprod_lower_nonneg hCr_nonneg
              _ = C ^ (r + s) := by rw [pow_add]
          exact mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
    _ = C ^ (r + s) *
        (∑ upper : Fin r -> Idx, ∑ lower : Fin s -> Idx,
          (componentRS (I := I) basis A upper lower) ^ 2) := by
          simp [Finset.mul_sum]

private theorem inner_self_eq_one_of_identityInv
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hginv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (i : Idx) :
    g.inner x (basis i) (basis i) = 1 := by
  have h := (hginv i i).1
  rw [Finset.sum_eq_single i] at h
  · simpa [identityInvMetric, diagonalInvMetric] using h
  · intro k _ hk
    simp [identityInvMetric, diagonalInvMetric, Ne.symm hk]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

private theorem diagonalInv_mul_inner_self_eq_one
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (μ : Idx -> Real)
    (hhinv :
      MetricInverseInBasis (I := I) h x basis (diagonalInvMetric μ))
    (i : Idx) :
    μ i * h.inner x (basis i) (basis i) = 1 := by
  have hsum := (hhinv i i).1
  rw [Finset.sum_eq_single i] at hsum
  · simpa [diagonalInvMetric] using hsum
  · intro k _ hk
    simp [diagonalInvMetric, Ne.symm hk]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Upper squared-norm comparison for mixed tensors under pointwise tangent
metric equivalence. -/
theorem normSqRS_upper_le_of_equiv
    (g h : SmoothMetric I M) (x : M) (r s : Nat) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v)
    (A : TensorRSSpace r s I x) :
    normSqRS (I := I) (g := h) (x := x) r s A <=
      C ^ (r + s) * normSqRS (I := I) (g := g) (x := x) r s A := by
  classical
  obtain ⟨μ, basis, hginv, hhinv, hμ_nonneg, hμ_le⟩ :=
    exists_diagInv_of_equiv (I := I) g h x hC hequiv
  let lam : Fin (Module.finrank Real (TangentSpace I x)) -> Real :=
    fun i => (μ i)⁻¹
  have hμinner :
      forall i : Fin (Module.finrank Real (TangentSpace I x)),
        μ i * h.inner x (basis i) (basis i) = 1 := by
    intro i
    exact diagonalInv_mul_inner_self_eq_one (I := I) h x basis μ hhinv i
  have hμ_ne :
      forall i : Fin (Module.finrank Real (TangentSpace I x)), μ i ≠ 0 := by
    intro i hzero
    have h := hμinner i
    rw [hzero] at h
    norm_num at h
  have hlamμ :
      forall i : Fin (Module.finrank Real (TangentSpace I x)), lam i * μ i = 1 := by
    intro i
    exact inv_mul_cancel₀ (hμ_ne i)
  have hlam_nonneg :
      forall i : Fin (Module.finrank Real (TangentSpace I x)), 0 <= lam i := by
    intro i
    exact inv_nonneg.mpr (hμ_nonneg i)
  have hlam_eq_inner :
      forall i : Fin (Module.finrank Real (TangentSpace I x)),
        lam i = h.inner x (basis i) (basis i) := by
    intro i
    have hprod := hμinner i
    unfold lam
    calc
      (μ i)⁻¹ = (μ i)⁻¹ * (μ i * h.inner x (basis i) (basis i)) := by
        rw [hprod, mul_one]
      _ = h.inner x (basis i) (basis i) := by
        field_simp [hμ_ne i]
  have hlam_le :
      forall i : Fin (Module.finrank Real (TangentSpace I x)), lam i <= C := by
    intro i
    have hupper := (hequiv (basis i)).2
    have hgii : g.inner x (basis i) (basis i) = 1 :=
      inner_self_eq_one_of_identityInv (I := I) g x basis hginv i
    have hle : h.inner x (basis i) (basis i) <= C := by
      simpa [hgii] using hupper
    simpa [hlam_eq_inner i] using hle
  exact normSqRS_diag_le
    (I := I) g h x r s basis lam μ C hginv hhinv hlamμ
    (le_trans (by norm_num) hC) hlam_nonneg hμ_nonneg hlam_le hμ_le A

/-- Lower squared-norm comparison for mixed tensors under pointwise tangent
metric equivalence. -/
theorem normSqRS_lower_le_of_equiv
    (g h : SmoothMetric I M) (x : M) (r s : Nat) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v)
    (A : TensorRSSpace r s I x) :
    (C ^ (r + s))⁻¹ * normSqRS (I := I) (g := g) (x := x) r s A <=
      normSqRS (I := I) (g := h) (x := x) r s A := by
  have hsymm := metric_equiv_symm (I := I) g h x hC hequiv
  have hupper :=
    normSqRS_upper_le_of_equiv
      (I := I) h g x r s hC hsymm A
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hpow_pos : 0 < C ^ (r + s) := pow_pos hC_pos (r + s)
  rw [inv_mul_le_iff₀ hpow_pos]
  exact hupper

/-- Two-sided squared-norm comparison for mixed tensors under pointwise metric
equivalence. -/
theorem normSqRS_le_of_metric_equiv
    (g h : SmoothMetric I M) (x : M) (r s : Nat) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v)
    (A : TensorRSSpace r s I x) :
    (C ^ (r + s))⁻¹ * normSqRS (I := I) (g := g) (x := x) r s A <=
      normSqRS (I := I) (g := h) (x := x) r s A /\
    normSqRS (I := I) (g := h) (x := x) r s A <=
      C ^ (r + s) * normSqRS (I := I) (g := g) (x := x) r s A := by
  have hlower :=
    normSqRS_lower_le_of_equiv
      (I := I) g h x r s hC hequiv A
  have hupper :=
    normSqRS_upper_le_of_equiv
      (I := I) g h x r s hC hequiv A
  constructor
  · exact hlower
  · exact hupper

/-- Square-root upper norm comparison for mixed tensors under pointwise tangent
metric equivalence. -/
theorem sqrt_normRS_upper_le_of_equiv
    (g h : SmoothMetric I M) (x : M) (r s : Nat) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v)
    (A : TensorRSSpace r s I x) :
    Real.sqrt (normSqRS (I := I) (g := h) (x := x) r s A) <=
      Real.sqrt (C ^ (r + s)) *
        Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A) := by
  have hupper :=
    normSqRS_upper_le_of_equiv (I := I) g h x r s hC hequiv A
  have hC_nonneg : 0 <= C := le_trans (by norm_num) hC
  have hpow_nonneg : 0 <= C ^ (r + s) := pow_nonneg hC_nonneg (r + s)
  calc
    Real.sqrt (normSqRS (I := I) (g := h) (x := x) r s A)
        <= Real.sqrt
          (C ^ (r + s) *
            normSqRS (I := I) (g := g) (x := x) r s A) :=
          by exact Real.sqrt_le_sqrt hupper
    _ = Real.sqrt (C ^ (r + s)) *
          Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A) := by
            rw [Real.sqrt_mul hpow_nonneg]

/-- Reverse square-root mixed-tensor norm comparison under the same pointwise
metric equivalence constant. -/
theorem sqrt_normRS_lower_le_of_equiv
    (g h : SmoothMetric I M) (x : M) (r s : Nat) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v)
    (A : TensorRSSpace r s I x) :
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A) <=
      Real.sqrt (C ^ (r + s)) *
        Real.sqrt (normSqRS (I := I) (g := h) (x := x) r s A) := by
  exact sqrt_normRS_upper_le_of_equiv
    (I := I) h g x r s hC
    (metric_equiv_symm (I := I) g h x hC hequiv) A

/-- The `(1,2)` specialization of
`normSqRS_identity_eq_componentL2SqRS`, written as a three-index sum. -/
theorem normSqRS_one_two_identity_eq_sum
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : TensorRSSpace 1 2 I x) :
    normSqRS (I := I) (g := g) (x := x) 1 2 A =
      ∑ k : Idx, ∑ i : Idx, ∑ j : Idx,
        (componentRS (I := I) basis A (fun _ : Fin 1 => k)
          (fun q : Fin 2 => if q = 0 then i else j)) ^ 2 := by
  rw [normSqRS_identity_eq_componentL2SqRS (I := I) g x 1 2 basis hinv A]
  unfold componentL2SqRS
  rw [sum_fin_one_fun]
  apply Finset.sum_congr rfl
  intro k _
  rw [sum_fin_two_fun]

/-- A single mixed-tensor component is bounded by the full component `l^2`
sum in the same basis. -/
theorem componentRS_sq_le_componentL2SqRS
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} {r s : Nat}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (A : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    (componentRS (I := I) basis A upper lower) ^ 2 <=
      componentL2SqRS (I := I) basis A := by
  classical
  unfold componentL2SqRS
  have h_lower :
      (componentRS (I := I) basis A upper lower) ^ 2 <=
        ∑ lower' : Fin s -> Idx,
          (componentRS (I := I) basis A upper lower') ^ 2 := by
    exact Finset.single_le_sum
      (fun lower' _ => sq_nonneg
        (componentRS (I := I) basis A upper lower'))
      (by simp)
  have h_upper :
      (∑ lower' : Fin s -> Idx,
          (componentRS (I := I) basis A upper lower') ^ 2) <=
        ∑ upper' : Fin r -> Idx, ∑ lower' : Fin s -> Idx,
          (componentRS (I := I) basis A upper' lower') ^ 2 := by
    exact Finset.single_le_sum
      (fun upper' _ =>
        Finset.sum_nonneg
          (fun lower' _ => sq_nonneg
            (componentRS (I := I) basis A upper' lower')))
      (by simp)
  exact h_lower.trans h_upper

/-- In an orthonormal-coordinate basis, the absolute value of a single
mixed-tensor component is bounded by the metric-induced tensor norm. -/
theorem abs_componentRS_le_sqrt_normSqRS
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (r s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    |componentRS (I := I) basis A upper lower| <=
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A) := by
  classical
  have hcomp_nonneg :
      0 <= componentL2SqRS (I := I) basis A := by
    unfold componentL2SqRS
    exact Finset.sum_nonneg
      (fun upper' _ =>
        Finset.sum_nonneg
          (fun lower' _ => sq_nonneg
            (componentRS (I := I) basis A upper' lower')))
  have hnorm_nonneg :
      0 <= normSqRS (I := I) (g := g) (x := x) r s A := by
    rw [normSqRS_identity_eq_componentL2SqRS
      (I := I) g x r s basis hinv A]
    exact hcomp_nonneg
  have hsq :
      |componentRS (I := I) basis A upper lower| ^ 2 <=
        (Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A)) ^ 2 := by
    rw [sq_abs, Real.sq_sqrt hnorm_nonneg,
      normSqRS_identity_eq_componentL2SqRS
        (I := I) g x r s basis hinv A]
    exact componentRS_sq_le_componentL2SqRS
      (I := I) basis A upper lower
  have hsq_no_abs :
      (componentRS (I := I) basis A upper lower) ^ 2 <=
        (Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A)) ^ 2 := by
    simpa [sq_abs] using hsq
  exact abs_le_of_sq_le_sq hsq_no_abs (Real.sqrt_nonneg _)

/-- If every component of a mixed tensor in an orthonormal basis is bounded by
`B`, then its squared Hilbert--Schmidt norm is bounded by the number of
components times `B^2`. -/
theorem normSqRS_le_comps
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (r s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : TensorRSSpace r s I x) {B : Real} (hB : 0 <= B)
    (hcomp : forall upper : Fin r -> Idx, forall lower : Fin s -> Idx,
      |componentRS (I := I) basis A upper lower| <= B) :
    normSqRS (I := I) (g := g) (x := x) r s A <=
      (Fintype.card (Fin r -> Idx) : Real) *
        ((Fintype.card (Fin s -> Idx) : Real) * B ^ 2) := by
  classical
  rw [normSqRS_identity_eq_componentL2SqRS (I := I) g x r s basis hinv A]
  unfold componentL2SqRS
  calc
    (∑ upper : Fin r -> Idx, ∑ lower : Fin s -> Idx,
        (componentRS (I := I) basis A upper lower) ^ 2)
        <= ∑ _upper : Fin r -> Idx, ∑ _lower : Fin s -> Idx, B ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro upper _
          refine Finset.sum_le_sum ?_
          intro lower _
          have hsq :
              |componentRS (I := I) basis A upper lower| ^ 2 <= B ^ 2 :=
            (sq_le_sq₀ (abs_nonneg _) hB).2 (hcomp upper lower)
          simpa [sq_abs] using hsq
    _ = (Fintype.card (Fin r -> Idx) : Real) *
        ((Fintype.card (Fin s -> Idx) : Real) * B ^ 2) := by
          simp

/-- Square-root form of `normSqRS_le_comps`. -/
theorem sqrt_normRS_le_comps
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (r s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : TensorRSSpace r s I x) {B : Real} (hB : 0 <= B)
    (hcomp : forall upper : Fin r -> Idx, forall lower : Fin s -> Idx,
      |componentRS (I := I) basis A upper lower| <= B) :
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A) <=
      Real.sqrt
        ((Fintype.card (Fin r -> Idx) : Real) *
          ((Fintype.card (Fin s -> Idx) : Real) * B ^ 2)) := by
  exact Real.sqrt_le_sqrt
    (normSqRS_le_comps (I := I) g x r s basis hinv A hB hcomp)

theorem normSqRS_nonneg
    {g : SmoothMetric I M} {x : M} (r s : Nat)
    (A : TensorRSSpace r s I x) :
    0 <= normSqRS (I := I) (g := g) (x := x) r s A := by
  simpa [normSqRS, innerRS, adjointRS, MetricFiberData.homFlatLinear] using
    MetricFiberData.homFlatLinear_nonneg
      (tensor0SMetricData (I := I) g x r)
      (tensor0SMetricData (I := I) g x s)
      A.toLinearMap

set_option backward.isDefEq.respectTransparency false in
private theorem sqrt_normRS_eq_metricNorm
    {g : SmoothMetric I M} {x : M} (r s : Nat)
    (A : TensorRSSpace r s I x) :
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A) =
      let D : MetricFiberData (TensorRSSpace r s I x) :=
        MetricFiberData.homCLM
          (tensor0SMetricData (I := I) g x r)
          (tensor0SMetricData (I := I) g x s)
      letI : InnerProductSpace.Core Real (TensorRSSpace r s I x) := D.toCore
      letI : NormedAddCommGroup (TensorRSSpace r s I x) :=
        @InnerProductSpace.Core.toNormedAddCommGroup Real
          (TensorRSSpace r s I x) _ _ _ D.toCore
      letI : InnerProductSpace Real (TensorRSSpace r s I x) :=
        @InnerProductSpace.ofCore Real (TensorRSSpace r s I x) _ _ _ D.toCore.toCore
      ‖A‖ := by
  let D : MetricFiberData (TensorRSSpace r s I x) :=
    MetricFiberData.homCLM
      (tensor0SMetricData (I := I) g x r)
      (tensor0SMetricData (I := I) g x s)
  letI : InnerProductSpace.Core Real (TensorRSSpace r s I x) := D.toCore
  letI : NormedAddCommGroup (TensorRSSpace r s I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real
      (TensorRSSpace r s I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TensorRSSpace r s I x) :=
    @InnerProductSpace.ofCore Real (TensorRSSpace r s I x) _ _ _ D.toCore.toCore
  have hmetric :
      D.inner A A = normSqRS (I := I) (g := g) (x := x) r s A := by
    unfold D
    unfold MetricFiberData.inner normSqRS innerRS adjointRS MetricFiberData.homCLM
      MetricFiberData.pullback MetricFiberData.hom MetricFiberData.homFlatLinear
      MetricFiberData.ofFlat
    simp [LinearMap.linearEquivOfInjective_apply]
  have hnormsq :
      normSqRS (I := I) (g := g) (x := x) r s A = ‖A‖ ^ 2 := by
    rw [← hmetric]
    rw [← MetricFiberData.toCore_inner D A A]
    exact real_inner_self_eq_norm_sq A
  rw [hnormsq]
  exact Real.sqrt_sq (norm_nonneg A)

set_option backward.isDefEq.respectTransparency false in
/-- Difference in the additive structure used by the metric-induced norm on
mixed tensor fibers.  This avoids ambiguity between the `ContinuousLinearMap`
subtraction instance and the normed-additive-group subtraction instance. -/
def metricSubRS
    {g : SmoothMetric I M} {x : M} (r s : Nat)
    (A B : TensorRSSpace r s I x) : TensorRSSpace r s I x :=
  let D : MetricFiberData (TensorRSSpace r s I x) :=
    MetricFiberData.homCLM
      (tensor0SMetricData (I := I) g x r)
      (tensor0SMetricData (I := I) g x s)
  letI : InnerProductSpace.Core Real (TensorRSSpace r s I x) := D.toCore
  letI : NormedAddCommGroup (TensorRSSpace r s I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real
      (TensorRSSpace r s I x) _ _ _ D.toCore
  A - B

set_option backward.isDefEq.respectTransparency false in
/-- Triangle inequality for the square-root mixed-tensor norm induced by a
Riemannian metric. -/
theorem sqrt_normRS_add_le
    {g : SmoothMetric I M} {x : M} (r s : Nat)
    (A B : TensorRSSpace r s I x) :
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s (A + B)) <=
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A) +
        Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s B) := by
  let D : MetricFiberData (TensorRSSpace r s I x) :=
    MetricFiberData.homCLM
      (tensor0SMetricData (I := I) g x r)
      (tensor0SMetricData (I := I) g x s)
  letI : InnerProductSpace.Core Real (TensorRSSpace r s I x) := D.toCore
  letI : NormedAddCommGroup (TensorRSSpace r s I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real
      (TensorRSSpace r s I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TensorRSSpace r s I x) :=
    @InnerProductSpace.ofCore Real (TensorRSSpace r s I x) _ _ _ D.toCore.toCore
  calc
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s (A + B))
        = ‖A + B‖ := sqrt_normRS_eq_metricNorm (I := I) r s (A + B)
    _ <= ‖A‖ + ‖B‖ := norm_add_le A B
    _ = Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A) +
          Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s B) := by
        rw [sqrt_normRS_eq_metricNorm (I := I) r s A,
          sqrt_normRS_eq_metricNorm (I := I) r s B]

set_option backward.isDefEq.respectTransparency false in
/-- Difference form of the square-root mixed-tensor triangle inequality. -/
theorem sqrt_normRS_sub_le_add
    {g : SmoothMetric I M} {x : M} (r s : Nat)
    (A B : TensorRSSpace r s I x) :
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s (A - B)) <=
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A) +
        Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s B) := by
  let D : MetricFiberData (TensorRSSpace r s I x) :=
    MetricFiberData.homCLM
      (tensor0SMetricData (I := I) g x r)
      (tensor0SMetricData (I := I) g x s)
  letI : InnerProductSpace.Core Real (TensorRSSpace r s I x) := D.toCore
  letI : NormedAddCommGroup (TensorRSSpace r s I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real
      (TensorRSSpace r s I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TensorRSSpace r s I x) :=
    @InnerProductSpace.ofCore Real (TensorRSSpace r s I x) _ _ _ D.toCore.toCore
  calc
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s (A - B))
        = ‖A - B‖ := sqrt_normRS_eq_metricNorm (I := I) r s (A - B)
    _ <= ‖A‖ + ‖B‖ := norm_sub_le A B
    _ = Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A) +
          Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s B) := by
        rw [sqrt_normRS_eq_metricNorm (I := I) r s A,
          sqrt_normRS_eq_metricNorm (I := I) r s B]

set_option backward.isDefEq.respectTransparency false in
/-- Triangle inequality arranged as `|B| <= |A| + |A - B|`.  This is the form
used when comparing two covariant derivatives. -/
theorem sqrt_normRS_le_add_sub
    {g : SmoothMetric I M} {x : M} (r s : Nat)
    (A B : TensorRSSpace r s I x) :
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s B) <=
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A) +
        Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s (A - B)) := by
  let D : MetricFiberData (TensorRSSpace r s I x) :=
    MetricFiberData.homCLM
      (tensor0SMetricData (I := I) g x r)
      (tensor0SMetricData (I := I) g x s)
  letI : InnerProductSpace.Core Real (TensorRSSpace r s I x) := D.toCore
  letI : NormedAddCommGroup (TensorRSSpace r s I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real
      (TensorRSSpace r s I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TensorRSSpace r s I x) :=
    @InnerProductSpace.ofCore Real (TensorRSSpace r s I x) _ _ _ D.toCore.toCore
  calc
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s B)
        = ‖B‖ := sqrt_normRS_eq_metricNorm (I := I) r s B
    _ = ‖A - (A - B)‖ := by
        rw [sub_sub_cancel]
    _ <= ‖A‖ + ‖A - B‖ := norm_sub_le A (A - B)
    _ = Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A) +
          Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s (A - B)) := by
        rw [sqrt_normRS_eq_metricNorm (I := I) r s A,
          sqrt_normRS_eq_metricNorm (I := I) r s (A - B)]

set_option backward.isDefEq.respectTransparency false in
/-- Triangle inequality arranged as `|B| <= |A| + |A - B|`, using the explicit
metric-induced subtraction term. -/
theorem sqrt_normRS_le_add_metricSub
    {g : SmoothMetric I M} {x : M} (r s : Nat)
    (A B : TensorRSSpace r s I x) :
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s B) <=
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A) +
        Real.sqrt
          (normSqRS (I := I) (g := g) (x := x) r s
            (metricSubRS (I := I) (g := g) (x := x) r s A B)) := by
  let D : MetricFiberData (TensorRSSpace r s I x) :=
    MetricFiberData.homCLM
      (tensor0SMetricData (I := I) g x r)
      (tensor0SMetricData (I := I) g x s)
  letI : InnerProductSpace.Core Real (TensorRSSpace r s I x) := D.toCore
  letI : NormedAddCommGroup (TensorRSSpace r s I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real
      (TensorRSSpace r s I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TensorRSSpace r s I x) :=
    @InnerProductSpace.ofCore Real (TensorRSSpace r s I x) _ _ _ D.toCore.toCore
  calc
    Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s B)
        = ‖B‖ := sqrt_normRS_eq_metricNorm (I := I) r s B
    _ = ‖A - (A - B)‖ := by
        rw [sub_sub_cancel]
    _ <= ‖A‖ + ‖A - B‖ := norm_sub_le A (A - B)
    _ = Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A) +
          Real.sqrt
            (normSqRS (I := I) (g := g) (x := x) r s
              (metricSubRS (I := I) (g := g) (x := x) r s A B)) := by
        unfold metricSubRS
        rw [sqrt_normRS_eq_metricNorm (I := I) r s A,
          sqrt_normRS_eq_metricNorm (I := I) r s (A - B)]

/-- A time-dependent pointwise realized `(r,s)` tensor field. -/
abbrev TensorRSTimeField
    (I : ModelWithCorners Real E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (Time : Type*) (r s : Nat) :=
  Time -> (x : M) -> TensorRSSpace r s I x

/-- Pointwise squared norm of a time-dependent realized `(r,s)` tensor field. -/
def tensorNormSqRS
    (g : Time -> SmoothMetric I M)
    {r s : Nat}
    (A : TensorRSTimeField I M Time r s) :
    Time -> M -> Real :=
  fun t x => normSqRS (I := I) (g := g t) (x := x) r s (A t x)

end

end Tensor0SBundle
