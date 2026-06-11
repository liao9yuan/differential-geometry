import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Kronecker-power quadratic-form bound (brick 2 of `ric_bound`)

Pure linear algebra.  The endpoint is `quadForm_id_le_pow`: for any index function
family `c : (Fin s → Idx) → ℝ` and a symmetric `Q : Idx → Idx → ℝ` bounded below
by `(1/C)` (as a quadratic form), the raw `ℓ²` sum `∑_I c_I²` is bounded by `C^s`
times the `Q`-contracted `s`-fold form `∑_{I,J} (∏_a Q (I a) (J a)) c_I c_J`.

This is the non-diagonal generalization of
`coordInner0S_diagonal_le_pow_identity`; `coordInner0S` unfolds to exactly the
`∑_{I,J} (∏ Q) c c` form, so this lemma converts an intrinsic `gRef`-norm into the
raw frame-component `ℓ²` once the frame Gram's inverse-eigenvalues are bounded
below.

The crux is the PSD-pairing inequality `sum_posSemidef_mul_posSemidef_nonneg`,
proved by the spectral decomposition of one factor.
-/

namespace DifferentialGeometry.HCGCompactness

open scoped BigOperators
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Spectral entry formula for a real Hermitian matrix:
`A i j = ∑ k, U i k * λ k * U j k`. -/
private lemma isHermitian_entry
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (i j : n) :
    A i j = ∑ k : n,
        (hA.eigenvectorUnitary : Matrix n n ℝ) i k *
          hA.eigenvalues k *
          (hA.eigenvectorUnitary : Matrix n n ℝ) j k := by
  classical
  have hspec : A = ((hA.eigenvectorUnitary : Matrix n n ℝ) *
      (Matrix.diagonal hA.eigenvalues) *
        star (hA.eigenvectorUnitary : Matrix n n ℝ)) := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hcomp : (RCLike.ofReal (K := ℝ)) ∘ hA.eigenvalues = hA.eigenvalues := by
      funext k; simp
    rw [hcomp] at h
    exact h
  have h := congr_fun (congr_fun hspec i) j
  rw [h, Matrix.mul_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · rw [Matrix.diagonal_apply_eq]
    have hstar : (star (hA.eigenvectorUnitary : Matrix n n ℝ)) k j =
        (hA.eigenvectorUnitary : Matrix n n ℝ) j k := by
      change star ((hA.eigenvectorUnitary : Matrix n n ℝ) j k) = _
      exact star_trivial _
    rw [hstar]
  · intro ℓ _ hℓ
    rw [Matrix.diagonal_apply_ne _ hℓ]
    ring
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- **PSD-pairing.** For positive semi-definite real matrices `M` and `G`, the
contracted sum `∑ i j, M i j * G i j` is non-negative. -/
theorem sum_posSemidef_mul_posSemidef_nonneg
    {M G : Matrix n n ℝ} (hM : M.PosSemidef) (hG : G.PosSemidef) :
    0 ≤ ∑ i, ∑ j, M i j * G i j := by
  classical
  set U : Matrix n n ℝ := (hM.isHermitian.eigenvectorUnitary : Matrix n n ℝ) with hU
  have hexp : ∀ i j : n, M i j * G i j =
      ∑ k, hM.isHermitian.eigenvalues k * (U i k * U j k * G i j) := by
    intro i j
    rw [isHermitian_entry hM.isHermitian i j, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by rw [hU]; ring)
  have hreorder : ∑ i, ∑ j, M i j * G i j =
      ∑ k, hM.isHermitian.eigenvalues k * (∑ i, ∑ j, U i k * U j k * G i j) := by
    have h1 : ∑ i, ∑ j, M i j * G i j =
        ∑ i, ∑ j, ∑ k,
          hM.isHermitian.eigenvalues k * (U i k * U j k * G i j) :=
      Finset.sum_congr rfl (fun i _ =>
        Finset.sum_congr rfl (fun j _ => hexp i j))
    rw [h1]
    rw [show (∑ i, ∑ j, ∑ k,
          hM.isHermitian.eigenvalues k * (U i k * U j k * G i j))
        = ∑ i, ∑ k, ∑ j,
          hM.isHermitian.eigenvalues k * (U i k * U j k * G i j)
      from Finset.sum_congr rfl fun i _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [hreorder]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (Matrix.PosSemidef.eigenvalues_nonneg hM k)
  have hquad : ∑ i, ∑ j, U i k * U j k * G i j
      = (fun i => U i k) ⬝ᵥ (G *ᵥ fun i => U i k) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  rw [hquad]
  exact hG.dotProduct_mulVec_nonneg _

end DifferentialGeometry.HCGCompactness
