import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueConnDot
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRmDiff
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Uhlenbeck

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option backward.isDefEq.respectTransparency false

/-!
# The invariant speed of the curvature-difference carrier `S₀₄` (Route-K brick K2.1)

`ForwardUniqueEnergy.lean` (K3) consumes a completely invariant fact about the third
Kotschwar carrier `S₀₄ = g₁(Rm¹ − Rm², ·)` of `ForwardUniqueFields.lean`: a `(0,4)`-tensor
speed `Sdot` together with

`∀ x v, HasDerivAt (fun r => rmDiffLowAt (g₁ r) (g₂ r) x v) (Sdot t x v) t`.

This file produces that fact, mirroring `ForwardUniqueConnDot.lean` (K1C-a) one rank up.
The lowering carrier `g₁(t)` is again moving, so the invariant speed of `S₀₄` is a *sum of
two* terms (`FORWARD_UNIQUE_PRO_RULING.md` §5: "lowering with `g₁` adds only terms involving
`∂ₜg₁ = −2Ric₁`"):

`∂ₜS₀₄ = −2 Ric₁((Rm¹−Rm²)(X, Y)Z, W) + g₁((∂ₜ(Rm¹−Rm²))(X, Y)Z, W)`.

## Main definitions

* `lowerTri q A` — the `(0,4)` tensor `(X, Y, Z, W) ↦ q (A X Y Z, W)` obtained by lowering
  the upper index of a trilinear vector-valued map `A` against an **arbitrary** `(0,2)`
  fiber tensor `q` (not only a metric: the reaction term lowers with `Ric₁`).  Built on
  `ForwardUniqueConnDot.lowerBilin` by one `uncurryLeft` and one slot transposition.
* `rmDiffVec g₁ g₂ x` — the raised curvature difference `Rm¹ − Rm²` as a genuine trilinear
  continuous map, the canonical `riemannOp` of the two Levi-Civita connections subtracted.
  This is the exact analogue of K1C's `CovariantDerivative.difference`.
* `rmDiffDot g₁ g₂ Sdot t x` — the invariant speed of `S₀₄`, the two-term sum above.
* `rmDotRem` — the componentwise remainder of the divergence-form evolution: the `K2.3`
  spatial remainder of the background field plus the two flows' `B`-quadratic and
  Ricci-drift differences.

## Main results

* `rmDiffLowAt_eq_lowerTri` — the carrier `S₀₄` *is* the `g₁`-lowering of `rmDiffVec`; this
  is what lets the moving-carrier product rule see a scalar sum of products.
* `rmDiffLow_hasDerivAt` — the `hS` hypothesis of `forwardUniqueEnergy_hasDerivAt`, produced
  from the Ricci-flow equation of the *carrier* `g₁` alone (the second flow's metric PDE is
  not needed: only `g₁` lowers, exactly as in K1C-a) plus the time derivative of the raised
  curvature difference.
* `rmDiffComp_deriv` — **K2.6-core**: taking the single-flow tensor Riemann evolution
  (`Uhlenbeck.lean`'s `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`) as a hypothesis
  once per flow (planner ruling R1), the difference of the two flows' curvature components
  evolves in divergence form `∂ₜ(Rm₁ − Rm₂) = Δ_{g₁}(T₁ − T₂) + div_{g₁}U₀₅ + R`.  The
  supplied-versus-intrinsic rough Laplacian is reconciled by two explicit realization
  hypotheses.
* `rmLowComp_deriv` — the same statement read on the Kotschwar carrier `S₀₄`, under the
  realization hypothesis that the two component families differ by the frame reading of
  `rmDiffLowAt` (the `g₁`-lowered representative, `rm2Low_eq_sub`).
* `roughLap0SField_sub`, `roughLapSub_apply`, `lapDiffFlux_apply_vec`, `driftDiff_split` —
  the small algebra the capstone runs on.

## Relocation TODO

`lowerTri` and the three slot-`0` multilinearity helpers are generic fiber algebra with a
canonical home next to `lowerBilin` (`Tensor/RSTensor/NablaOnTensors/ConnectionDifference.lean`);
`roughLap0SField_sub`/`roughLapSub_apply`/`lapDiffFlux_apply_vec` belong in the operator
layer of `ForwardUniqueRmDiff.lean`.  They live here only because the brick protocol forbids
editing existing files.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

section Lowering

variable {x : M}

/-- Additivity of a `(0,2)` fiber tensor in slot `0`. -/
private theorem tensor02_add_left
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (u₁ u₂ Z : TangentSpace I x) :
    q (fun a : Fin 2 => if a = 0 then u₁ + u₂ else Z) =
      q (fun a : Fin 2 => if a = 0 then u₁ else Z) +
        q (fun a : Fin 2 => if a = 0 then u₂ else Z) := by
  classical
  set m : Fin 2 -> TangentSpace I x := fun a => if a = 0 then u₁ else Z with hm
  have hupd : ∀ u : TangentSpace I x,
      Function.update m 0 u = (fun a : Fin 2 => if a = 0 then u else Z) := by
    intro u
    funext a
    fin_cases a <;> simp [hm]
  calc q (fun a : Fin 2 => if a = 0 then u₁ + u₂ else Z)
      = q (Function.update m 0 (u₁ + u₂)) := by rw [hupd]
    _ = q (Function.update m 0 u₁) + q (Function.update m 0 u₂) := q.map_update_add m 0 u₁ u₂
    _ = q (fun a : Fin 2 => if a = 0 then u₁ else Z) +
          q (fun a : Fin 2 => if a = 0 then u₂ else Z) := by rw [hupd, hupd]

/-- Homogeneity of a `(0,2)` fiber tensor in slot `0`. -/
private theorem tensor02_smul_left
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (c : Real) (u Z : TangentSpace I x) :
    q (fun a : Fin 2 => if a = 0 then c • u else Z) =
      c * q (fun a : Fin 2 => if a = 0 then u else Z) := by
  classical
  set m : Fin 2 -> TangentSpace I x := fun a => if a = 0 then u else Z with hm
  have hupd : ∀ u' : TangentSpace I x,
      Function.update m 0 u' = (fun a : Fin 2 => if a = 0 then u' else Z) := by
    intro u'
    funext a
    fin_cases a <;> simp [hm]
  calc q (fun a : Fin 2 => if a = 0 then c • u else Z)
      = q (Function.update m 0 (c • u)) := by rw [hupd]
    _ = c • q (Function.update m 0 u) := q.map_update_smul m 0 c u
    _ = c * q (fun a : Fin 2 => if a = 0 then u else Z) := by rw [hupd, smul_eq_mul]

/-- `lowerBilin q` is additive in the bilinear map it lowers. -/
private theorem lowerBilin_add
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A B : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    lowerBilin (I := I) q (A + B) =
      lowerBilin (I := I) q A + lowerBilin (I := I) q B := by
  refine ContinuousMultilinearMap.ext fun v => ?_
  have hsum : (lowerBilin (I := I) q A + lowerBilin (I := I) q B) v =
      lowerBilin (I := I) q A v + lowerBilin (I := I) q B v :=
    Tensor0SSpace.add_apply (I := I) 3 x _ _ v
  rw [hsum, lowerBilin_apply, lowerBilin_apply, lowerBilin_apply]
  have hAB : ((A + B) (v 1)) (v 0) = (A (v 1)) (v 0) + (B (v 1)) (v 0) := rfl
  rw [hAB, tensor02_add_left]

/-- `lowerBilin q` is homogeneous in the bilinear map it lowers. -/
private theorem lowerBilin_smul
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (c : Real)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    lowerBilin (I := I) q (c • A) = c • lowerBilin (I := I) q A := by
  refine ContinuousMultilinearMap.ext fun v => ?_
  have hsmul : (c • lowerBilin (I := I) q A) v = c • (lowerBilin (I := I) q A v) :=
    Tensor0SSpace.smul_apply (I := I) 3 x c _ v
  rw [hsmul, lowerBilin_apply, lowerBilin_apply]
  have hA : ((c • A) (v 1)) (v 0) = c • ((A (v 1)) (v 0)) := rfl
  rw [hA, tensor02_smul_left, smul_eq_mul]

/-- Auxiliary lowering with the free (lowered) slot in position `3` but the curvature
inputs transposed: `w ↦ q (A (w 0) (w 2) (w 1), w 3)`. -/
private def lowerTriOut
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  ContinuousLinearMap.uncurryLeft (𝕜 := Real) (n := 3)
    (Ei := fun _ : Fin 4 => TangentSpace I x) (G := Real)
    (LinearMap.toContinuousLinearMap
      { toFun := fun X =>
          (lowerBilin (I := I) q (A X) :
            ContinuousMultilinearMap Real (fun _ : Fin 3 => TangentSpace I x) Real)
        map_add' := by
          intro X₁ X₂
          rw [map_add]
          exact lowerBilin_add (I := I) q (A X₁) (A X₂)
        map_smul' := by
          intro c X
          rw [map_smul]
          exact lowerBilin_smul (I := I) q c (A X) })

private theorem lowerTriOut_apply
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    (w : Fin 4 -> TangentSpace I x) :
    lowerTriOut (I := I) q A w =
      q (fun a : Fin 2 => if a = 0 then ((A (w 0)) (w 2)) (w 1) else w 3) := by
  have h : lowerTriOut (I := I) q A w =
      lowerBilin (I := I) q (A (w 0)) (Fin.tail w) := by
    rw [lowerTriOut, ContinuousLinearMap.uncurryLeft_apply]
    exact rfl
  rw [h, lowerBilin_apply]
  congr 1

/-- **Lowering the upper index of a trilinear vector-valued map against a `(0,2)` tensor.**
`lowerTri q A` is the `(0,4)` fiber tensor `(X, Y, Z, W) ↦ q (A X Y Z, W)`.  As for
`lowerBilin`, the lowering tensor `q` is arbitrary: the moving-carrier reaction term of
`∂ₜS₀₄` lowers with `Ric₁`, not with a metric. -/
def lowerTri
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 4) 2)
    (lowerTriOut (I := I) q A)

theorem lowerTri_apply
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    (v : Fin 4 -> TangentSpace I x) :
    lowerTri (I := I) q A v =
      q (fun a : Fin 2 => if a = 0 then ((A (v 0)) (v 1)) (v 2) else v 3) := by
  have h : lowerTri (I := I) q A v =
      lowerTriOut (I := I) q A (fun i : Fin 4 => v (Equiv.swap (1 : Fin 4) 2 i)) := rfl
  rw [h, lowerTriOut_apply]
  congr 1

end Lowering
section RaisedDifference

variable {x : M}

/-- Subtraction in slot `0` of a `(0,2)` fiber tensor. -/
private theorem tensor02_sub_left
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (u₁ u₂ Z : TangentSpace I x) :
    q (fun a : Fin 2 => if a = 0 then u₁ - u₂ else Z) =
      q (fun a : Fin 2 => if a = 0 then u₁ else Z) -
        q (fun a : Fin 2 => if a = 0 then u₂ else Z) := by
  have h := tensor02_add_left (I := I) q (u₁ - u₂) u₂ Z
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

/-- The metric `(0,2)` tensor field read in the slot-`0` convention. -/
private theorem metricField_slot0 (g : SmoothRiemannianMetric I M) (x : M)
    (u Z : TangentSpace I x) :
    metricTensorField (I := I) g x (fun a : Fin 2 => if a = 0 then u else Z) =
      g.inner x u Z := by
  rw [metricTensorField_apply]; simp

/-- Locally smooth covariant derivatives are smooth: specialize the local statement to
`Set.univ`.  This bridges `metricCov_smooth` to the `ContMDiffCovariantDerivative` instance
that `riemannOp` requires, without going through the `InnerProductSpace ℝ E`-tainted
producer `LeviCivita_isContMDiff`. -/
private instance instContMDiffMetricCov (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivative (metricCov (I := I) g) ∞ :=
  CovariantDerivative.contMDiffCovariantDerivativeOn_univ_iff.mp
    (metricCov_smooth (I := I) g isOpen_univ)

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The raised curvature difference `Rm¹ − Rm²` at a point**, as a genuine trilinear
continuous map `(X, Y, Z) ↦ Rm¹(X, Y)Z − Rm²(X, Y)Z`.  This is the exact `(1,3)` analogue
of K1C's `CovariantDerivative.difference`: the canonical bundled curvature operator
`riemannOp` of the two Levi-Civita connections, subtracted. -/
def rmDiffVec (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x :=
  DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) g₁) x -
    DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) g₂) x

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- Equal metrics give a vanishing raised curvature difference. -/
@[simp]
theorem rmDiffVec_self (g : SmoothRiemannianMetric I M) (x : M) :
    rmDiffVec (I := I) g g x = 0 := by
  rw [rmDiffVec]
  exact sub_self (DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) g) x)

set_option synthInstance.maxHeartbeats 1000000 in
/-- **`S₀₄` is the `g₁`-lowering of the raised curvature difference.**  This is the shape
the moving-carrier product rule needs: the lowering metric contracted against a vector that
moves with time. -/
theorem rmDiffLowAt_eq_lowerTri (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    rmDiffLowAt (I := I) g₁ g₂ x =
      lowerTri (I := I) (metricTensorField (I := I) g₁ x) (rmDiffVec (I := I) g₁ g₂ x) := by
  classical
  refine ContinuousMultilinearMap.ext fun v => ?_
  have hv : DifferentialGeometry.Integral.Connection.vec4 (I := I) (v 0) (v 1) (v 2) (v 3) = v := by
    funext i
    fin_cases i <;> simp [DifferentialGeometry.Integral.Connection.vec4]
  have h₁ :
      DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
          (I := I) g₁ (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) x v =
        g₁.inner x (v 3)
          (DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) g₁) x
            (v 0) (v 1) (v 2)) := by
    have h :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At_apply_const
        (I := I) g₁ (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) (v 0) (v 1) (v 2) (v 3)
    rw [DifferentialGeometry.riemannCurvatureAux_tangentConst_eq_riemannOp
      (I := I) (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) x (v 0) (v 1) (v 2),
      hv] at h
    exact h
  have h₂ :
      DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
          (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x v =
        g₁.inner x (v 3)
          (DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) g₂) x
            (v 0) (v 1) (v 2)) := by
    have h :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At_apply_const
        (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) (v 0) (v 1) (v 2) (v 3)
    rw [DifferentialGeometry.riemannCurvatureAux_tangentConst_eq_riemannOp
      (I := I) (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x (v 0) (v 1) (v 2),
      hv] at h
    exact h
  have hsub : rmDiffLowAt (I := I) g₁ g₂ x v =
      DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
          (I := I) g₁ (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) x v -
        DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
          (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x v :=
    Tensor0SSpace.sub_apply (I := I) 4 x _ _ v
  have hvec : ((rmDiffVec (I := I) g₁ g₂ x (v 0)) (v 1)) (v 2) =
      DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) g₁) x
          (v 0) (v 1) (v 2) -
        DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) g₂) x
          (v 0) (v 1) (v 2) := rfl
  have hlin : ∀ u₁ u₂ : TangentSpace I x,
      g₁.inner x (u₁ - u₂) (v 3) = g₁.inner x u₁ (v 3) - g₁.inner x u₂ (v 3) := by
    intro u₁ u₂
    rw [← metricField_slot0 (I := I) g₁ x u₁ (v 3), ← metricField_slot0 (I := I) g₁ x u₂ (v 3),
      ← metricField_slot0 (I := I) g₁ x (u₁ - u₂) (v 3), tensor02_sub_left]
  rw [hsub, h₁, h₂, lowerTri_apply, metricField_slot0, hvec, hlin,
    g₁.symm x (v 3)
      (DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) g₁) x
        (v 0) (v 1) (v 2)),
    g₁.symm x (v 3)
      (DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) g₂) x
        (v 0) (v 1) (v 2))]

end RaisedDifference

section Speed

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The invariant speed of the curvature-difference carrier `S₀₄`.**

`rmDiffDot g₁ g₂ Sdot t x` is the `(0,4)` fiber tensor

`(X, Y, Z, W) ↦ −2 Ric₁((Rm¹−Rm²)(X, Y)Z, W) + g₁(t)(Sdot x X Y Z, W)`,

where `Sdot x` is the invariant speed of the `(1,3)` curvature difference `Rm¹ − Rm²` at
`x`.  The first summand is the moving-carrier reaction created by `∂ₜg₁ = −2Ric₁`. -/
def rmDiffDot (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Sdot : (x : M) →
      TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
        TangentSpace I x)
    (t : Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  (-2 : Real) •
      lowerTri (I := I) (metricRicciAt (I := I) (g₁ t) x)
        (rmDiffVec (I := I) (g₁ t) (g₂ t) x) +
    lowerTri (I := I) (metricTensorField (I := I) (g₁ t) x) (Sdot x)

set_option synthInstance.maxHeartbeats 1000000 in
theorem rmDiffDot_apply (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Sdot : (x : M) →
      TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
        TangentSpace I x)
    (t : Real) (x : M) (v : Fin 4 -> TangentSpace I x) :
    rmDiffDot (I := I) g₁ g₂ Sdot t x v =
      (-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then
            ((rmDiffVec (I := I) (g₁ t) (g₂ t) x (v 0)) (v 1)) (v 2) else v 3) +
        (g₁ t).inner x (((Sdot x (v 0)) (v 1)) (v 2)) (v 3) := by
  have hadd :
      rmDiffDot (I := I) g₁ g₂ Sdot t x v =
        ((-2 : Real) •
            lowerTri (I := I) (metricRicciAt (I := I) (g₁ t) x)
              (rmDiffVec (I := I) (g₁ t) (g₂ t) x)) v +
          lowerTri (I := I) (metricTensorField (I := I) (g₁ t) x) (Sdot x) v :=
    Tensor0SSpace.add_apply (I := I) 4 x _ _ v
  have hsmul :
      ((-2 : Real) •
          lowerTri (I := I) (metricRicciAt (I := I) (g₁ t) x)
            (rmDiffVec (I := I) (g₁ t) (g₂ t) x)) v =
        (-2 : Real) •
          lowerTri (I := I) (metricRicciAt (I := I) (g₁ t) x)
            (rmDiffVec (I := I) (g₁ t) (g₂ t) x) v :=
    Tensor0SSpace.smul_apply (I := I) 4 x (-2 : Real) _ v
  rw [hadd, hsmul, lowerTri_apply, lowerTri_apply, smul_eq_mul, metricField_slot0]

end Speed

section Adapter

variable {x : M}

set_option synthInstance.maxHeartbeats 1000000 in
/-- **K2.1, invariant core.**  If the carrier `g₁` solves the Ricci-flow equation at `x`
and the `(1,3)` curvature difference `Rm¹ − Rm²` has invariant time derivative `Sdot x`,
then the lowered carrier `S₀₄` has time derivative `rmDiffDot`.  This is exactly the `hS`
hypothesis of `forwardUniqueEnergy_hasDerivAt`.

As in K1C-a, the *second* flow's metric PDE is not needed: only `g₁` lowers. -/
theorem rmDiffLow_hasDerivAt
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Sdot : (x : M) →
      TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
        TangentSpace I x)
    {t : Real}
    (hPDE₁ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hRm : ∀ X Y Z : TangentSpace I x,
      HasDerivAt
        (fun r : Real => ((rmDiffVec (I := I) (g₁ r) (g₂ r) x X) Y) Z)
        (((Sdot x X) Y) Z) t)
    (v : Fin 4 -> TangentSpace I x) :
    HasDerivAt (fun r : Real => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x v)
      (rmDiffDot (I := I) g₁ g₂ Sdot t x v) t := by
  classical
  set b : Module.Basis
      (Fin (Module.finrank Real (TangentSpace I x))) Real (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x) with hb
  set F : Real → TangentSpace I x := fun r =>
    ((rmDiffVec (I := I) (g₁ r) (g₂ r) x (v 0)) (v 1)) (v 2) with hF
  set Fdot : TangentSpace I x := ((Sdot x (v 0)) (v 1)) (v 2) with hFdot
  have hFderiv : HasDerivAt F Fdot t := hRm (v 0) (v 1) (v 2)
  -- componentwise derivative of the moving vector
  have hcomp : ∀ k, HasDerivAt (fun r : Real => b.repr (F r) k) (b.repr Fdot k) t := by
    intro k
    have hL : HasDerivAt (fun r : Real =>
        (LinearMap.toContinuousLinearMap (b.coord k)) (F r))
        ((LinearMap.toContinuousLinearMap (b.coord k)) Fdot) t :=
      (LinearMap.toContinuousLinearMap (b.coord k)).hasFDerivAt.comp_hasDerivAt t hFderiv
    simpa using hL
  -- derivative of the moving metric components
  have hmet : ∀ k, HasDerivAt
      (fun r : Real => (g₁ r).inner x (b k) (v 3))
      ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
        (fun a : Fin 2 => if a = 0 then b k else v 3)) t := fun k => hPDE₁ (b k) (v 3)
  -- the integrand as a finite sum of products
  have hsum : ∀ r : Real,
      rmDiffLowAt (I := I) (g₁ r) (g₂ r) x v =
        ∑ k, b.repr (F r) k * (g₁ r).inner x (b k) (v 3) := by
    intro r
    rw [rmDiffLowAt_eq_lowerTri, lowerTri_apply,
      show ((rmDiffVec (I := I) (g₁ r) (g₂ r) x (v 0)) (v 1)) (v 2) = F r from rfl,
      tensor02_expand (I := I) (metricTensorField (I := I) (g₁ r) x) b (F r) (v 3)]
    exact Finset.sum_congr rfl fun k _ => by rw [metricField_slot0]
  have hderiv : HasDerivAt (fun r : Real => ∑ k, b.repr (F r) k * (g₁ r).inner x (b k) (v 3))
      (∑ k, (b.repr Fdot k * (g₁ t).inner x (b k) (v 3) +
        b.repr (F t) k * ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then b k else v 3)))) t :=
    HasDerivAt.fun_sum fun k _ => (hcomp k).mul (hmet k)
  have hval :
      (∑ k, (b.repr Fdot k * (g₁ t).inner x (b k) (v 3) +
        b.repr (F t) k * ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then b k else v 3)))) =
        rmDiffDot (I := I) g₁ g₂ Sdot t x v := by
    rw [Finset.sum_add_distrib, rmDiffDot_apply]
    have hg : (∑ k, b.repr Fdot k * (g₁ t).inner x (b k) (v 3)) =
        (g₁ t).inner x Fdot (v 3) := by
      rw [← metricField_slot0 (I := I) (g₁ t) x Fdot (v 3),
        tensor02_expand (I := I) (metricTensorField (I := I) (g₁ t) x) b Fdot (v 3)]
      exact Finset.sum_congr rfl fun k _ => by rw [metricField_slot0]
    have hr : (∑ k, b.repr (F t) k * ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then b k else v 3))) =
        (-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then F t else v 3) := by
      rw [tensor02_expand (I := I) (metricRicciAt (I := I) (g₁ t) x) b (F t) (v 3),
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hg, hr]
    ring
  have := hderiv.congr_deriv hval
  simpa only [hsum] using this

end Adapter

section DivergenceForm

variable {Idx : Type*} [Fintype Idx]

/-- The four frame vectors at `x`, in the `(0,4)` slot order of `riemannCurvature04At`. -/
def frameVec4 (frame : Idx -> (y : M) -> TangentSpace I y) (x : M) (i j k l : Idx) :
    Fin 4 -> TangentSpace I x :=
  DifferentialGeometry.Integral.Connection.vec4 (I := I)
    (frame i x) (frame j x) (frame k x) (frame l x)

/-- Bilinear splitting of the Ricci-drift difference of the two flows into a
`Ric`-difference term and a curvature-difference term, each against a background factor.
This is the shape a `K2.5`-pattern norm bound consumes. -/
theorem driftDiff_split (Ric₁ Ric₂ : MatrixComp M Idx) (Rm₁ Rm₂ : FourComp M Idx)
    (t : Real) (x : M) (i j k l : Idx) :
    riemann04RicciDriftInFrame Ric₁ Rm₁ t x i j k l -
        riemann04RicciDriftInFrame Ric₂ Rm₂ t x i j k l =
      riemann04RicciDriftInFrame (fun s y a b => Ric₁ s y a b - Ric₂ s y a b) Rm₁ t x i j k l +
        riemann04RicciDriftInFrame Ric₂
          (fun s y a b c d => Rm₁ s y a b c d - Rm₂ s y a b c d) t x i j k l := by
  classical
  simp only [riemann04RicciDriftInFrame, sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- **The componentwise remainder of the divergence-form curvature-difference evolution.**

Three manifest differences: the `K2.3` spatial remainder `lapDiffRem` of the *background*
field `T₂` (connection-difference and inverse-metric-difference terms), the difference of
the two flows' `B`-quadratics, and the difference of the two flows' Ricci drifts.  Each
summand vanishes when the two flows coincide; `driftDiff_split` exhibits the last one as
`(Ric₁ − Ric₂) ∗ Rm₁ + Ric₂ ∗ (Rm₁ − Rm₂)`.  Bounding its norm is not this brick: that is
the `K2.5` pattern. -/
def rmDotRem (g₁ g₂ : SmoothRiemannianMetric I M)
    (T₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Rm₁ Rm₂ B₁ B₂ : FourComp M Idx) (Ric₁ Ric₂ : MatrixComp M Idx)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (t : Real) (x : M) (i j k l : Idx) : Real :=
  lapDiffRem (I := I) g₁ g₂ T₂ x (frameVec4 (I := I) frame x i j k l) -
    2 * ((B₁ t x i j k l - B₂ t x i j k l) - (B₁ t x i j l k - B₂ t x i j l k) +
      (B₁ t x i k j l - B₂ t x i k j l) - (B₁ t x i l j k - B₂ t x i l j k)) -
    (riemann04RicciDriftInFrame Ric₁ Rm₁ t x i j k l -
      riemann04RicciDriftInFrame Ric₂ Rm₂ t x i j k l)

end DivergenceForm

section LaplacianAlgebra

variable {s : ℕ}

/-- The rough Laplacian of a `(0,s)` field subtracts. -/
theorem roughLap0SField_sub (g : SmoothRiemannianMetric I M)
    (T U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    roughLap0SField (I := I) g (T - U) =
      roughLap0SField (I := I) g T - roughLap0SField (I := I) g U := by
  rw [roughLap0SField, roughLap0SField, roughLap0SField, metricNabla0S_sub,
    covDiv0SField_sub]

/-- Pointwise, slot-evaluated form of `roughLap0SField_sub`. -/
theorem roughLapSub_apply (g : SmoothRiemannianMetric I M)
    (T U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) (v : Fin s -> TangentSpace I x) :
    roughLap0SField (I := I) g (T - U) x v =
      roughLap0SField (I := I) g T x v - roughLap0SField (I := I) g U x v := by
  have hfield : roughLap0SField (I := I) g (T - U) x =
      roughLap0SField (I := I) g T x - roughLap0SField (I := I) g U x := by
    rw [roughLap0SField_sub]; rfl
  rw [hfield]
  exact Tensor0SSpace.sub_apply (I := I) s x _ _ v

/-- Pointwise, slot-evaluated form of the `K2.3` divergence-form identity
`Δ_{g₁}T − Δ_{g₂}T = div_{g₁}U + R`. -/
theorem lapDiffFlux_apply_vec (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) (v : Fin s -> TangentSpace I x) :
    roughLap0SField (I := I) g₁ T x v - roughLap0SField (I := I) g₂ T x v =
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) x v +
        lapDiffRem (I := I) g₁ g₂ T x v := by
  have hf := lapDiff_eq_div_flux (I := I) g₁ g₂ T
  have hx₁ : (roughLap0SField (I := I) g₁ T - roughLap0SField (I := I) g₂ T) x =
      roughLap0SField (I := I) g₁ T x - roughLap0SField (I := I) g₂ T x := rfl
  have hx₂ : (covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) +
      lapDiffRem (I := I) g₁ g₂ T) x =
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) x +
        lapDiffRem (I := I) g₁ g₂ T x := rfl
  have h : roughLap0SField (I := I) g₁ T x - roughLap0SField (I := I) g₂ T x =
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) x +
        lapDiffRem (I := I) g₁ g₂ T x := by
    rw [← hx₁, ← hx₂, hf]
  have hl : (roughLap0SField (I := I) g₁ T x -
      roughLap0SField (I := I) g₂ T x) v =
      roughLap0SField (I := I) g₁ T x v - roughLap0SField (I := I) g₂ T x v :=
    Tensor0SSpace.sub_apply (I := I) s x _ _ v
  have hr : (covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) x +
      lapDiffRem (I := I) g₁ g₂ T x) v =
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) x v +
        lapDiffRem (I := I) g₁ g₂ T x v :=
    Tensor0SSpace.add_apply (I := I) s x _ _ v
  rw [← hl, ← hr, h]

end LaplacianAlgebra

section Capstone

variable {Idx : Type*} [Fintype Idx]

/-- **K2.6-core: the divergence-form curvature-difference evolution, componentwise.**

Taking the single-flow tensor Riemann evolution as a hypothesis *once per flow* (planner
ruling R1 of `ShortTime/FORWARD_UNIQUE_PLAN.md` №2: `Uhlenbeck.lean`'s
`Riemann04BTensorWithRicciDriftEvolutionInFrameOn` is the repo's own named frontier), the
difference of the two flows' curvature components evolves in divergence form:

`∂ₜ(Rm₁ − Rm₂) = Δ_{g₁}(T₁ − T₂) + div_{g₁}U₀₅ + R`,

with `U₀₅ = lapDiffFlux g₁ g₂ T₂` carrying **no** derivative of the difference (that is the
divergence-form point of `K2.3`) and `R = rmDotRem` an explicit sum of manifest differences.

The reconciliation between the interface's *supplied* `roughLapRm04` component families and
the *intrinsic* `roughLap0SField` of the realized fields is carried by the two explicit
realization hypotheses `hL₁`, `hL₂`: each flow's supplied family is the frame reading of the
intrinsic rough Laplacian of that flow's own metric and curvature field.  No smoothness or
frame regularity is used: everything outside the two evolution hypotheses is pointwise
algebra at the fixed time `t`. -/
theorem rmDiffComp_deriv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (T₁ T₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Rm₁ Rm₂ roughLapRm₁ roughLapRm₂ B₁ B₂ : FourComp M Idx)
    (Ric₁ Ric₂ : MatrixComp M Idx)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hev₁ : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D) Rm₁ roughLapRm₁ B₁ Ric₁)
    (hev₂ : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D) Rm₂ roughLapRm₂ B₂ Ric₂)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (i j k l : Idx)
    (hL₁ : roughLapRm₁ (t : Real) x i j k l =
      roughLap0SField (I := I) g₁ T₁ x (frameVec4 (I := I) frame x i j k l))
    (hL₂ : roughLapRm₂ (t : Real) x i j k l =
      roughLap0SField (I := I) g₂ T₂ x (frameVec4 (I := I) frame x i j k l)) :
    HasDerivWithinAt (fun r : Real => Rm₁ r x i j k l - Rm₂ r x i j k l)
      (roughLap0SField (I := I) g₁ (T₁ - T₂) x (frameVec4 (I := I) frame x i j k l) +
        covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T₂) x
          (frameVec4 (I := I) frame x i j k l) +
        rmDotRem (I := I) g₁ g₂ T₂ Rm₁ Rm₂ B₁ B₂ Ric₁ Ric₂ frame (t : Real) x i j k l)
      D.carrier (t : Real) := by
  have hsub := (hev₁ t x i j k l).sub (hev₂ t x i j k l)
  refine hsub.congr_deriv ?_
  have hlap :
      roughLapRm₁ (t : Real) x i j k l - roughLapRm₂ (t : Real) x i j k l =
        roughLap0SField (I := I) g₁ (T₁ - T₂) x (frameVec4 (I := I) frame x i j k l) +
          covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T₂) x
            (frameVec4 (I := I) frame x i j k l) +
          lapDiffRem (I := I) g₁ g₂ T₂ x (frameVec4 (I := I) frame x i j k l) := by
    rw [hL₁, hL₂]
    have hk := lapDiffFlux_apply_vec (I := I) g₁ g₂ T₂ x
      (frameVec4 (I := I) frame x i j k l)
    have hd := roughLapSub_apply (I := I) g₁ T₁ T₂ x (frameVec4 (I := I) frame x i j k l)
    linarith [hk, hd]
  rw [rmDotRem]
  linarith [hlap]

/-- **K2.6-core, read on the Kotschwar carrier `S₀₄`.**

If the two supplied component families realize the curvature difference of the two flows in
the *common* `g₁(r)`-lowered representation at every time — that is, if their difference is
the frame reading of `rmDiffLowAt` (`hreal`) — then the frame components of `S₀₄` satisfy
the divergence-form evolution

`∂ₜS₀₄ = Δ_{g₁}S₀₄ + div_{g₁}U₀₅ + R`

in the componentwise `HasDerivWithinAt` convention.

`hreal` is a plain realization hypothesis, not a proof obligation discharged here: it is the
statement that the flow-`2` interface is applied to the `g₁`-lowered representative of
`Rm²` (`rm2Low_eq_sub`), which is *not* the own-metric-lowered `Rm04₂` that the standard
Uhlenbeck evolution describes.  See the file note for the classification of this input. -/
theorem rmLowComp_deriv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (T₁ T₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Rm₁ Rm₂ roughLapRm₁ roughLapRm₂ B₁ B₂ : FourComp M Idx)
    (Ric₁ Ric₂ : MatrixComp M Idx)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hev₁ : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D) Rm₁ roughLapRm₁ B₁ Ric₁)
    (hev₂ : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D) Rm₂ roughLapRm₂ B₂ Ric₂)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (i j k l : Idx)
    (hL₁ : roughLapRm₁ (t : Real) x i j k l =
      roughLap0SField (I := I) (g₁ (t : Real)) T₁ x (frameVec4 (I := I) frame x i j k l))
    (hL₂ : roughLapRm₂ (t : Real) x i j k l =
      roughLap0SField (I := I) (g₂ (t : Real)) T₂ x (frameVec4 (I := I) frame x i j k l))
    (hreal : ∀ r : Real, Rm₁ r x i j k l - Rm₂ r x i j k l =
      rmDiffLowAt (I := I) (g₁ r) (g₂ r) x (frameVec4 (I := I) frame x i j k l)) :
    HasDerivWithinAt
      (fun r : Real =>
        rmDiffLowAt (I := I) (g₁ r) (g₂ r) x (frameVec4 (I := I) frame x i j k l))
      (roughLap0SField (I := I) (g₁ (t : Real)) (T₁ - T₂) x
          (frameVec4 (I := I) frame x i j k l) +
        covDiv0SField (I := I) (g₁ (t : Real))
          (lapDiffFlux (I := I) (g₁ (t : Real)) (g₂ (t : Real)) T₂) x
          (frameVec4 (I := I) frame x i j k l) +
        rmDotRem (I := I) (g₁ (t : Real)) (g₂ (t : Real)) T₂ Rm₁ Rm₂ B₁ B₂ Ric₁ Ric₂ frame
          (t : Real) x i j k l)
      D.carrier (t : Real) := by
  have h := rmDiffComp_deriv (I := I) (g₁ (t : Real)) (g₂ (t : Real)) T₁ T₂
    Rm₁ Rm₂ roughLapRm₁ roughLapRm₂ B₁ B₂ Ric₁ Ric₂ frame hev₁ hev₂ t x i j k l hL₁ hL₂
  have hfun : (fun r : Real => Rm₁ r x i j k l - Rm₂ r x i j k l) =
      (fun r : Real =>
        rmDiffLowAt (I := I) (g₁ r) (g₂ r) x (frameVec4 (I := I) frame x i j k l)) :=
    funext hreal
  rw [← hfun]
  exact h

end Capstone

end DifferentialGeometry.PDE.RicciFlow

end
