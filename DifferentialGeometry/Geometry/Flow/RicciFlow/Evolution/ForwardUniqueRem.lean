import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueSdec
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRmBounds

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Tensorial evaluation of the forward-uniqueness remainder

This file removes the two raw component carriers from `sdecRem`.  The componentwise
`rmDotRem` is reconstructed as a genuine `(0,4)` tensor, while `gapDot` at the bundled
Uhlenbeck speed is rewritten as two explicitly lowered tensor products.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
variable [BoundarylessManifold I M]

section Fiber

variable {Idx : Type*} [Fintype Idx] {x : M}

/-- A `(0,4)` tensor is recovered from its components in any basis by `lowOfComp`. -/
theorem lowOfComp_ext (g : SmoothRiemannianMetric I M)
    (b : Module.Basis Idx Real (TangentSpace I x))
    (c : Idx → Idx → Idx → Idx → Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (hcomp : ∀ i j k l,
      T (vec4 (I := I) (b i) (b j) (b k) (b l)) = c i j k l) :
    lowOfComp (I := I) g b c = T := by
  classical
  refine ContinuousMultilinearMap.toMultilinearMap_injective
    (Module.Basis.ext_multilinear (fun _ : Fin 4 => b) fun w => ?_)
  have hw : (fun p : Fin 4 => b (w p)) =
      vec4 (I := I) (b (w 0)) (b (w 1)) (b (w 2)) (b (w 3)) := by
    funext p
    fin_cases p <;> simp [vec4]
  simp only [ContinuousMultilinearMap.coe_coe, hw]
  rw [lowOfComp_eval]
  exact (hcomp (w 0) (w 1) (w 2) (w 3)).symm

/-- Lowering a trilinear vector-valued map is the tensor reconstructed from its basis
components.  The reconstruction metric is auxiliary; the resulting tensor is intrinsic. -/
theorem lowerTri_low (g : SmoothRiemannianMetric I M)
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    (b : Module.Basis Idx Real (TangentSpace I x)) :
    lowOfComp (I := I) g b
        (fun i j k l =>
          q (fun a : Fin 2 => if a = 0 then ((A (b i)) (b j)) (b k) else b l)) =
      lowerTri (I := I) q A := by
  apply lowOfComp_ext (I := I)
  intro i j k l
  exact lowerTri_apply (I := I) q A
    (vec4 (I := I) (b i) (b j) (b k) (b l))

end Fiber

section ComponentRemainder

variable {Idx : Type*} [Fintype Idx]

/-- The tensor reconstructed from `rmDotRem` splits into the intrinsic spatial remainder,
the difference of the two quadratic blocks, and the difference of the two Ricci drifts. -/
theorem rmDotRem_low
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (T₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (basisAt : (y : M) → Module.Basis Idx Real (TangentSpace I y))
    (Rm₁ Rm₂ B₁ B₂ : FourComp M Idx) (Ric₁ Ric₂ : MatrixComp M Idx)
    (t : Real) (x : M) :
    lowOfComp (I := I) g₁ (basisAt x)
        (rmDotRem (I := I) g₁ g₂ T₂ Rm₁ Rm₂ B₁ B₂ Ric₁ Ric₂
          (fun m z => basisAt z m) t x) =
      lapDiffRem (I := I) g₁ g₂ T₂ x -
        (2 : Real) • lowOfComp (I := I) g₁ (basisAt x)
          (fun i j k l =>
            (B₁ t x i j k l - B₂ t x i j k l) -
              (B₁ t x i j l k - B₂ t x i j l k) +
            (B₁ t x i k j l - B₂ t x i k j l) -
              (B₁ t x i l j k - B₂ t x i l j k)) -
        lowOfComp (I := I) g₁ (basisAt x)
          (fun i j k l =>
            riemann04RicciDriftInFrame Ric₁ Rm₁ t x i j k l -
              riemann04RicciDriftInFrame Ric₂ Rm₂ t x i j k l) := by
  apply lowOfComp_ext (I := I)
  intro i j k l
  rw [Tensor0SSpace.sub_apply (I := I) 4 x,
    Tensor0SSpace.sub_apply (I := I) 4 x,
    Tensor0SSpace.smul_apply (I := I) 4 x,
    lowOfComp_eval, lowOfComp_eval]
  rfl

variable [NeZero (Module.finrank Real E)]

set_option maxHeartbeats 1000000 in
/-- Pointwise squared-norm bound for the tensorized `rmDotRem`.

The spatial term is bounded by `rmRemNormSq_le`; in particular its background inputs are
the rank-`5` norm of `∇Rm₂` and the rank-`6` norm of the full `∇²Rm₂`.  The remaining
arguments bound the already tensorized quadratic and drift differences. -/
theorem rmDotRemSq_le
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (T₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (basisAt : (y : M) → Module.Basis Idx Real (TangentSpace I y))
    (Rm₁ Rm₂ B₁ B₂ : FourComp M Idx) (Ric₁ Ric₂ : MatrixComp M Idx)
    (t : Real) (x : M) {Λ B₅ B₆ BQ BD : Real}
    (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    (hB₅ : normSq0S (I := I) g₁ x 5 (metricNabla0S (I := I) g₂ T₂ x) ≤ B₅)
    (hB₆ : normSq0S (I := I) g₁ x 6
      (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T₂) x) ≤ B₆)
    (hBQ : normSq0S (I := I) g₁ x 4
      (lowOfComp (I := I) g₁ (basisAt x)
        (fun i j k l =>
          (B₁ t x i j k l - B₂ t x i j k l) -
            (B₁ t x i j l k - B₂ t x i j l k) +
          (B₁ t x i k j l - B₂ t x i k j l) -
            (B₁ t x i l j k - B₂ t x i l j k))) ≤ BQ)
    (hBD : normSq0S (I := I) g₁ x 4
      (lowOfComp (I := I) g₁ (basisAt x)
        (fun i j k l =>
          riemann04RicciDriftInFrame Ric₁ Rm₁ t x i j k l -
            riemann04RicciDriftInFrame Ric₂ Rm₂ t x i j k l)) ≤ BD) :
    normSq0S (I := I) g₁ x 4
      (lowOfComp (I := I) g₁ (basisAt x)
        (rmDotRem (I := I) g₁ g₂ T₂ Rm₁ Rm₂ B₁ B₂ Ric₁ Ric₂
          (fun m z => basisAt z m) t x)) ≤
      4 * (50 * (Module.finrank Real E : Real) ^ 12 *
          connDiffSq (I := I) g₁ g₂ x * B₅ +
        2 * (Module.finrank Real E : Real) ^ 10 * Λ ^ 2 *
          metricDiffSq (I := I) g₁ g₂ x * B₆) +
      16 * BQ + 2 * BD := by
  let Q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    lowOfComp (I := I) g₁ (basisAt x)
      (fun i j k l =>
        (B₁ t x i j k l - B₂ t x i j k l) -
          (B₁ t x i j l k - B₂ t x i j l k) +
        (B₁ t x i k j l - B₂ t x i k j l) -
          (B₁ t x i l j k - B₂ t x i l j k))
  let D : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    lowOfComp (I := I) g₁ (basisAt x)
      (fun i j k l =>
        riemann04RicciDriftInFrame Ric₁ Rm₁ t x i j k l -
          riemann04RicciDriftInFrame Ric₂ Rm₂ t x i j k l)
  have hL := rmRemNormSq_le (I := I) g₁ g₂ T₂ x hΛ0 hΛ hB₅ hB₆
  have houter := normSq0S_sub_le (I := I) g₁ x 4
    (lapDiffRem (I := I) g₁ g₂ T₂ x - (2 : Real) • Q) D
  have hinner := normSq0S_sub_le (I := I) g₁ x 4
    (lapDiffRem (I := I) g₁ g₂ T₂ x) ((2 : Real) • Q)
  have hscale :
      normSq0S (I := I) g₁ x 4 ((2 : Real) • Q) =
        4 * normSq0S (I := I) g₁ x 4 Q := by
    rw [normSq0S_eq_inner, inner0S_smul_left, inner0S_smul_right,
      ← normSq0S_eq_inner]
    ring
  rw [rmDotRem_low (I := I) g₁ g₂ T₂ basisAt Rm₁ Rm₂ B₁ B₂ Ric₁ Ric₂ t x]
  change normSq0S (I := I) g₁ x 4
      (lapDiffRem (I := I) g₁ g₂ T₂ x - (2 : Real) • Q - D) ≤ _
  calc
    normSq0S (I := I) g₁ x 4
        (lapDiffRem (I := I) g₁ g₂ T₂ x - (2 : Real) • Q - D)
        ≤ 2 * normSq0S (I := I) g₁ x 4
            (lapDiffRem (I := I) g₁ g₂ T₂ x - (2 : Real) • Q) +
          2 * normSq0S (I := I) g₁ x 4 D := houter
    _ ≤ 4 * normSq0S (I := I) g₁ x 4 (lapDiffRem (I := I) g₁ g₂ T₂ x) +
          4 * normSq0S (I := I) g₁ x 4 ((2 : Real) • Q) +
          2 * normSq0S (I := I) g₁ x 4 D := by linarith
    _ = 4 * normSq0S (I := I) g₁ x 4 (lapDiffRem (I := I) g₁ g₂ T₂ x) +
          16 * normSq0S (I := I) g₁ x 4 Q +
          2 * normSq0S (I := I) g₁ x 4 D := by rw [hscale]; ring
    _ ≤ 4 * (50 * (Module.finrank Real E : Real) ^ 12 *
            connDiffSq (I := I) g₁ g₂ x * B₅ +
          2 * (Module.finrank Real E : Real) ^ 10 * Λ ^ 2 *
            metricDiffSq (I := I) g₁ g₂ x * B₆) +
        16 * BQ + 2 * BD := by
      dsimp [Q, D] at hBQ hBD ⊢
      gcongr

end ComponentRemainder

section GapRemainder

variable {Idx : Type*} [Fintype Idx]

/-- At the real Uhlenbeck speed, `gapDot` is a sum of two genuine `(0,4)` tensors:
`2 (Ric₁ - Ric₂) * Rm₂` and the metric difference paired with the explicit raised
Uhlenbeck right-hand side.  In particular no bare `uhlRm2Vec` remains. -/
theorem gapDot_uhl
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (basisAt : (y : M) → Module.Basis Idx Real (TangentSpace I y))
    (Rm04₂ roughLapRm04₂ B₂ : FourComp M Idx) (ricciOneUp₂ : MatrixComp M Idx)
    (t : Real) (x : M) :
    gapDot (I := I) (g₁ t) (g₂ t)
        (uhlRm2Vec (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t x) =
      (2 : Real) • lowOfComp (I := I) (g₁ t) (basisAt x)
        (fun i j k l =>
          (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x)
            (fun a : Fin 2 =>
              if a = 0 then
                riemannOp (metricCov (I := I) (g₂ t)) x
                  (basisAt x i) (basisAt x j) (basisAt x k)
              else basisAt x l)) -
      lowOfComp (I := I) (g₁ t) (basisAt x)
        (fun i j k l =>
          metricDiffAt (I := I) (g₁ t) (g₂ t) x
            (fun a : Fin 2 =>
              if a = 0 then
                uhlRaisedDeriv (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂
                  t x i j k
              else basisAt x l)) := by
  have hRic :
      lowOfComp (I := I) (g₁ t) (basisAt x)
          (fun i j k l =>
            (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x)
              (fun a : Fin 2 =>
                if a = 0 then
                  riemannOp (metricCov (I := I) (g₂ t)) x
                    (basisAt x i) (basisAt x j) (basisAt x k)
                else basisAt x l)) =
        lowerTri (I := I)
          (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x)
          (riemannOp (metricCov (I := I) (g₂ t)) x) :=
    lowerTri_low (I := I) (g₁ t)
      (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x)
      (riemannOp (metricCov (I := I) (g₂ t)) x) (basisAt x)
  have hSpeed :
      lowOfComp (I := I) (g₁ t) (basisAt x)
          (fun i j k l =>
            metricDiffAt (I := I) (g₁ t) (g₂ t) x
              (fun a : Fin 2 =>
                if a = 0 then
                  uhlRaisedDeriv (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂
                    t x i j k
                else basisAt x l)) =
        lowerTri (I := I) (metricDiffAt (I := I) (g₁ t) (g₂ t) x)
          (uhlRm2Vec (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t x) := by
    apply lowOfComp_ext (I := I)
    intro i j k l
    rw [lowerTri_apply]
    have hv :
        ((uhlRm2Vec (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t x
          (basisAt x i)) (basisAt x j)) (basisAt x k) =
            uhlRaisedDeriv (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂
              t x i j k :=
      quadOfComp_vec (I := I) (basisAt x) _ i j k
    congr 1
    funext a
    fin_cases a <;> simp [vec4, hv]
  rw [gapDot, ← hRic, ← hSpeed]

end GapRemainder

end DifferentialGeometry.PDE.RicciFlow
