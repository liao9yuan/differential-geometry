import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueLifts
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueReLower

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option backward.isDefEq.respectTransparency false

/-!
# The Kotschwar `S`-equation in divergence form (Route-K brick K6c)

`Evolution/ForwardUniqueAssembly.lean` (K6a) reduced black box (B) to the standing bundle
`ForwardUniqueInputs`; `Evolution/ForwardUniqueLifts.lean` (K6b) collapsed its `rm` and
`gamma` members.  This file collapses the remaining K2-B member, `sdec`:

```
∂ₜS₀₄ = Δ₁S₀₄ + div₁U′ + rem′
```

from **exactly** the ruling-R1 standing inputs (the two per-flow *own-lowered* Uhlenbeck
interfaces `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`), the two per-flow Ricci-flow
equations, and the same benign realization/continuity inputs `rm_of_uhlenbeck` and
`rmDiffComp_deriv` already carry.

## The route (planner ruling R7)

`S₀₄ = rmDiffLowAt g₁ g₂` lowers *both* curvatures with `g₁`, while the honest interfaces
describe each flow's own-lowered `(0,4)` curvature.  Split

```
S₀₄ = D + G,      D = Rm04₁ − Rm04₂,      G = Rm04₂ − g₁♭Rm¹³₂,
```

so that `D` is exactly the object the two interfaces difference (`rmDiffComp_deriv`, K2.6-core)
and `G` is the lowering gap.  Writing `P = g₁♭Rm¹³₂ = Rm04₁ − S₀₄` (a *field*, since both
summands are fields) the gap is `G = reLower g₂ g₁ P − P`: the K2.6c re-lowering operator with
its two metric arguments **swapped**, so that its trace metric and its connection are both
`g₁`.  With that orientation the banked commutator `lapComm_reLower_eq` produces a `g₁`
divergence — the divergence the Kotschwar energy integrates by parts against — and the key
identity is the mirror of `nabla2_metric1`:

```
∇¹g₂ = (∇¹ − ∇²)g₂ = lapDiffFlux g₁ g₂ g₂        (`nabla1_metric2`)
```

i.e. `∇¹g₂` is `A₀₃`-algebraic, exactly as `∇²g₁` is.  Both defect carriers of the commutator
are therefore `A₀₃`-flux algebra against the background `P`.

The time derivative of the gap is the moving-carrier product rule `∂ₜ(−h₀₂(Rm¹³₂ ·, ·))`:

```
∂ₜG = 2(Ric₁ − Ric₂)(Rm¹³₂ ·, ·) − h₀₂(∂ₜRm¹³₂ ·, ·)        (`gap_deriv`)
```

— manifestly (difference × background), with `∂ₜRm¹³₂` the raised flow-`2` speed that
`rmVecComp_deriv` already produces from that flow's own interface.

Assembling, and using `Δ₁D = Δ₁S₀₄ − Δ₁G`,

```
U′ = lapDiffFlux g₁ g₂ Rm04₂ − reLowerPair g₁ P (lapDiffFlux g₁ g₂ g₂)      (`sdecFlux`)
rem′ = rmDotRem + ∂ₜG − (reLower g₂ g₁ − id)(Δ₁P) − tr₁(reLowerPair g₁ (∇¹P) (∇¹g₂))
```

(`sdecRem`), every summand of which is either `A₀₃`-flux algebra against a background factor
or a difference carrier against a bounded background.  Norm bounds are **not** in scope here
(the bundle's `bounds` field covers them); the shapes are kept bound-statable.

## Main definitions

* `nabla1_metric2` — the key identity `∇¹g₂ = lapDiffFlux g₁ g₂ g₂`.
* `lowOfComp` — the `(0,4)` fiber tensor with prescribed frame components (the `(0,4)`
  analogue of `quadOfComp`, obtained by lowering the raised component family).
* `gapAt`, `gapDot`, `gap_deriv` — the lowering gap and its time derivative.
* `sdecFlux`, `sdecRem` — the explicit `U′` and `rem′`.
* `sdec_core`, `sdec_of_uhlenbeck` — the `sdec` member of `ForwardUniqueInputs`, verbatim.

## Relocation TODO

`inner_raiseAt` belongs next to `raiseAt_lower` (`ForwardUniqueRmBridge.lean`);
`vec3_deriv_basis` is the generic form of `rmDiffVec_hasDerivAt_of_basis`
(`ForwardUniqueLifts.lean`); `innerCurve_deriv` is the invariant core already inlined in
`rmDiffLow_hasDerivAt` (`ForwardUniqueRmDot.lean`).  The brick protocol forbade editing those
files.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators Topology

/-! ## Part 1: the `NormedSpace` core

Everything below the final restatement lives in the `NormedSpace ℝ E` context of
`ForwardUniqueRmDot.lean` / `ForwardUniqueReLower.lean`; only the last theorem, which mentions
`rmSpeed`, needs the `InnerProductSpace ℝ E` context of `ForwardUniqueAssembly.lean`, and it
gets its own section (the `IPS`/`NormedSpace` split must be a *section* split). -/

section NormedBase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
variable [BoundarylessManifold I M]

section Algebra

variable {s : ℕ}

/-- Pointwise evaluation of a field difference. -/
private theorem fieldSub_eval
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) (v : Fin s -> TangentSpace I x) :
    (A - B) x v = A x v - B x v := by
  have h : (A - B) x = A x - B x := rfl
  rw [h]
  exact Tensor0SSpace.sub_apply (I := I) s x _ _ v

/-- Pointwise evaluation of a field sum. -/
private theorem fieldAdd_eval
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) (v : Fin s -> TangentSpace I x) :
    (A + B) x v = A x v + B x v := by
  have h : (A + B) x = A x + B x := rfl
  rw [h]
  exact Tensor0SSpace.add_apply (I := I) s x _ _ v

/-- The metric `(0,2)` tensor field read in the slot-`0` convention. -/
private theorem metField0 (g : SmoothRiemannianMetric I M) (x : M)
    (u Z : TangentSpace I x) :
    metricTensorField (I := I) g x (fun a : Fin 2 => if a = 0 then u else Z) =
      g.inner x u Z := by
  rw [metricTensorField_apply]; simp

end Algebra

/-! ## The key identity: `∇¹g₂` is `A₀₃`-algebraic -/

section KeyIdentity

/-- **`∇¹g₂ = (∇¹ − ∇²)g₂ = lapDiffFlux g₁ g₂ g₂`** — the mirror of `nabla2_metric1`.  Since
`∇²g₂ = 0`, the covariant derivative of the *other* metric taken with the `g₁` connection is
exactly the connection-difference flux applied to `g₂`: no derivative of the metric difference
appears, so `∇¹h₀₂ = −lapDiffFlux g₁ g₂ g₂` is `A₀₃`-algebraic as well.  This is the identity
that makes the swapped re-lowering commutator (`lapComm_reLower_eq g₂ g₁`) produce a `g₁`
divergence with `A₀₃`-algebraic carriers. -/
theorem nabla1_metric2 (g₁ g₂ : SmoothRiemannianMetric I M) :
    metricNabla0S (I := I) g₁ (metricTensorField (I := I) g₂) =
      lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂) := by
  rw [lapDiffFlux, metricNabla0S_self]
  abel

end KeyIdentity

/-! ## Fiber algebra: prescribed components, and the two metric pairings -/

section Fiber

variable {Idx : Type*} [Fintype Idx] {x : M}

/-- **Lowering undoes raising.**  The `g`-pairing of `raiseAt g x basis a` against a basis
vector returns the prescribed component.  (Companion of `raiseAt_lower`.) -/
theorem inner_raiseAt (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) (a : Idx -> Real) (m : Idx) :
    g.inner x (raiseAt (I := I) g x basis a) (basis m) = a m := by
  classical
  have hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis
      (basisInvMetric (I := I) g x basis) := basisInvMetric_real (I := I) g x basis
  have hrepr : ∀ p : Idx,
      basis.repr (raiseAt (I := I) g x basis a) p =
        ∑ l : Idx, basisInvMetric (I := I) g x basis p l * a l := by
    intro p
    rw [raiseAt_eq]
    simp [Finsupp.single_apply]
  rw [← metField0 (I := I) g x (raiseAt (I := I) g x basis a) (basis m),
    tensor02_expand (I := I) (metricTensorField (I := I) g x) basis
      (raiseAt (I := I) g x basis a) (basis m)]
  have hstep : ∀ p : Idx,
      basis.repr (raiseAt (I := I) g x basis a) p *
          metricTensorField (I := I) g x
            (fun c : Fin 2 => if c = 0 then basis p else basis m) =
        ∑ l : Idx, basisInvMetric (I := I) g x basis l p * a l *
          g.inner x (basis p) (basis m) := by
    intro p
    rw [metField0, hrepr p, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [basisInvMetric_symm (I := I) g x basis p l]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) => hstep p, Finset.sum_comm]
  have hrow : ∀ l : Idx,
      (∑ p : Idx, basisInvMetric (I := I) g x basis l p * a l * g.inner x (basis p) (basis m)) =
        a l * (if l = m then (1 : Real) else 0) := by
    intro l
    rw [← (hinv l m).1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => by ring
  rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hrow l]
  simp

/-- **The re-lowering endomorphism moves the metric.**  `sharpFlat g₂ g₁ = g₁♯ ∘ g₂♭` turns a
`g₁`-pairing into a `g₂`-pairing.  This is the pointwise content of `mixLow_eq_rm04`, stated
for an arbitrary vector rather than for a curvature value. -/
theorem inner_sharpFlat (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (V W : TangentSpace I x) :
    g₁.inner x V (sharpFlat (I := I) g₂ g₁ x W) = g₂.inner x V W := by
  have hflat : tangentFlatEquiv_gen (I := I) g₁ x (sharpFlat (I := I) g₂ g₁ x W) =
      tangentFlatEquiv_gen (I := I) g₂ x W := by
    change tangentFlatEquiv_gen (I := I) g₁ x
      ((tangentFlatEquiv_gen (I := I) g₁ x).symm
        ((tangentFlatEquiv_gen (I := I) g₂ x) W)) = _
    exact (tangentFlatEquiv_gen (I := I) g₁ x).apply_symm_apply _
  calc g₁.inner x V (sharpFlat (I := I) g₂ g₁ x W)
      = g₁.inner x (sharpFlat (I := I) g₂ g₁ x W) V :=
        g₁.symm x V (sharpFlat (I := I) g₂ g₁ x W)
    _ = tangentFlatEquiv_gen (I := I) g₁ x (sharpFlat (I := I) g₂ g₁ x W) V :=
        (tangentFlatEquiv_apply_gen (I := I) g₁ x _ V).symm
    _ = tangentFlatEquiv_gen (I := I) g₂ x W V := by rw [hflat]
    _ = g₂.inner x W V := tangentFlatEquiv_apply_gen (I := I) g₂ x W V
    _ = g₂.inner x V W := g₂.symm x W V

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The mixed lowering, read on the curvature operator.**  The `g₁`-lowered `(0,4)` Riemann
tensor of `g₂` is the `g₁`-pairing of `riemannOp (metricCov g₂)` with the last slot.  (The
own-metric case is `metricRm04At_inner`.) -/
theorem rm04mix_inner (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
        (metricCov_smooth (I := I) g₂) x (vec4 (I := I) X Y Z W) =
      g₁.inner x (riemannOp (metricCov (I := I) g₂) x X Y Z) W := by
  have h := CovariantDerivative.riemannCurvature04At_apply_const
    (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) X Y Z W
  rw [DifferentialGeometry.riemannCurvatureAux_tangentConst_eq_riemannOp
    (I := I) (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x X Y Z] at h
  rw [h]
  exact g₁.symm x W _

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The `(0,4)` fiber tensor with prescribed frame components.**  The `(0,4)` analogue of
`quadOfComp`: raise the component family with `g`, package it as a trilinear map, and lower
the result again.  `lowOfComp_eval` reads the components back. -/
def lowOfComp (g : SmoothRiemannianMetric I M) {x : M}
    (b : Module.Basis Idx Real (TangentSpace I x))
    (c : Idx -> Idx -> Idx -> Idx -> Real) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  lowerTri (I := I) (metricTensorField (I := I) g x)
    (quadOfComp (I := I) b
      (fun i j k l => b.repr (raiseAt (I := I) g x b (fun m : Idx => c i j k m)) l))

set_option synthInstance.maxHeartbeats 1000000 in
/-- The frame components of `lowOfComp` are the prescribed ones. -/
theorem lowOfComp_eval (g : SmoothRiemannianMetric I M) {x : M}
    (b : Module.Basis Idx Real (TangentSpace I x))
    (c : Idx -> Idx -> Idx -> Idx -> Real) (i j k l : Idx) :
    lowOfComp (I := I) g b c (vec4 (I := I) (b i) (b j) (b k) (b l)) = c i j k l := by
  rw [lowOfComp, lowerTri_apply]
  have hv0 : (vec4 (I := I) (b i) (b j) (b k) (b l)) 0 = b i := rfl
  have hv1 : (vec4 (I := I) (b i) (b j) (b k) (b l)) 1 = b j := rfl
  have hv2 : (vec4 (I := I) (b i) (b j) (b k) (b l)) 2 = b k := rfl
  have hv3 : (vec4 (I := I) (b i) (b j) (b k) (b l)) 3 = b l := rfl
  rw [hv0, hv1, hv2, hv3, quadOfComp_vec (I := I) b
    (fun i' j' k' => raiseAt (I := I) g x b (fun m : Idx => c i' j' k' m)) i j k,
    metField0, inner_raiseAt]

end Fiber

/-! ## The lowering gap and its time derivative -/

section Gap

variable {x : M}

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The lowering gap `G`.**  The difference between the own-lowered `(0,4)` curvature of
`g₂` and its `g₁`-lowered representative: `G(X,Y,Z,W) = −h₀₂(Rm¹³₂(X,Y)Z, W)`.  Adding it to
`Rm04₁ − Rm04₂` — the object the two honest interfaces difference — gives `S₀₄`. -/
def gapAt (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  metricRm04At (I := I) g₂ x -
    CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
      (metricCov_smooth (I := I) g₂) x

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The `S₀₄` split.**  `S₀₄ = (Rm04₁ − Rm04₂) + G`: pure algebra, since both sides are
`Rm04₁` minus the `g₁`-lowered curvature of `g₂`. -/
theorem rmDiffLow_split (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 4 -> TangentSpace I x) :
    rmDiffLowAt (I := I) g₁ g₂ x v =
      (metricRm04At (I := I) g₁ x - metricRm04At (I := I) g₂ x) v +
        gapAt (I := I) g₁ g₂ x v := by
  rw [rmDiffLowAt_apply, gapAt,
    Tensor0SSpace.sub_apply (I := I) 4 x (metricRm04At (I := I) g₁ x)
      (metricRm04At (I := I) g₂ x) v,
    Tensor0SSpace.sub_apply (I := I) 4 x (metricRm04At (I := I) g₂ x) _ v]
  ring

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The time derivative of the lowering gap**, in the shape ruling R7 asks for: a
`(Ric₁ − Ric₂)`-difference against the background curvature, plus the metric difference `h₀₂`
against the background curvature speed. -/
def gapDot (g₁ g₂ : SmoothRiemannianMetric I M) {x : M}
    (Rm2dot : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  (2 : Real) •
      lowerTri (I := I) (metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x)
        (riemannOp (metricCov (I := I) g₂) x) -
    lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) Rm2dot

end Gap

/-! ## Derivative machinery for the gap -/

section Deriv

variable {x : M}

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Frame → invariant lift for a curve of trilinear maps.**  The generic form of
`rmDiffVec_hasDerivAt_of_basis`: basis-triple derivatives determine the derivative at every
triple. -/
theorem vec3_deriv_basis {Idx : Type*} [Fintype Idx]
    (F : Real -> (TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x))
    (b : Module.Basis Idx Real (TangentSpace I x))
    (Sdot : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    {t : Real}
    (hbasis : ∀ i j k : Idx,
      HasDerivAt (fun r : Real => ((F r (b i)) (b j)) (b k)) (((Sdot (b i)) (b j)) (b k)) t)
    (X Y Z : TangentSpace I x) :
    HasDerivAt (fun r : Real => ((F r X) Y) Z) (((Sdot X) Y) Z) t := by
  classical
  have hexp : ∀ r : Real, ((F r X) Y) Z =
      ∑ i, ∑ j, ∑ k, (b.repr X i * b.repr Y j * b.repr Z k) • ((F r (b i)) (b j)) (b k) :=
    fun r => tri_expand (I := I) _ b X Y Z
  have htgt : ((Sdot X) Y) Z =
      ∑ i, ∑ j, ∑ k, (b.repr X i * b.repr Y j * b.repr Z k) • ((Sdot (b i)) (b j)) (b k) :=
    tri_expand (I := I) Sdot b X Y Z
  rw [htgt]
  have hstep : HasDerivAt
      (fun r : Real =>
        ∑ i, ∑ j, ∑ k, (b.repr X i * b.repr Y j * b.repr Z k) • ((F r (b i)) (b j)) (b k))
      (∑ i, ∑ j, ∑ k, (b.repr X i * b.repr Y j * b.repr Z k) • ((Sdot (b i)) (b j)) (b k)) t :=
    HasDerivAt.fun_sum fun i _ =>
      HasDerivAt.fun_sum fun j _ =>
        HasDerivAt.fun_sum fun k _ => (hbasis i j k).const_smul _
  simpa only [← hexp] using hstep

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Moving-metric pairing of a moving vector.**  The invariant product rule already inlined
in `rmDiffLow_hasDerivAt`, isolated: if the vector curve `V` is differentiable and the metric
family solves the Ricci-flow equation at `x`, then the pairing is differentiable with the
`∂ₜg = −2Ric` reaction term. -/
theorem innerCurve_deriv (g : Real -> SmoothRiemannianMetric I M)
    (V : Real -> TangentSpace I x) (Vdot Z : TangentSpace I x) {t : Real}
    (hV : HasDerivAt V Vdot t)
    (hPDE : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t) :
    HasDerivAt (fun r : Real => (g r).inner x (V r) Z)
      ((g t).inner x Vdot Z +
        (-2 : Real) * metricRicciAt (I := I) (g t) x
          (fun a : Fin 2 => if a = 0 then V t else Z)) t := by
  classical
  set b : Module.Basis
      (Fin (Module.finrank Real (TangentSpace I x))) Real (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x) with hb
  have hcomp : ∀ k, HasDerivAt (fun r : Real => b.repr (V r) k) (b.repr Vdot k) t := by
    intro k
    have hL : HasDerivAt (fun r : Real =>
        (LinearMap.toContinuousLinearMap (b.coord k)) (V r))
        ((LinearMap.toContinuousLinearMap (b.coord k)) Vdot) t :=
      (LinearMap.toContinuousLinearMap (b.coord k)).hasFDerivAt.comp_hasDerivAt t hV
    simpa using hL
  have hsum : ∀ r : Real,
      (g r).inner x (V r) Z = ∑ k, b.repr (V r) k * (g r).inner x (b k) Z := by
    intro r
    rw [← metField0 (I := I) (g r) x (V r) Z,
      tensor02_expand (I := I) (metricTensorField (I := I) (g r) x) b (V r) Z]
    exact Finset.sum_congr rfl fun k _ => by rw [metField0]
  have hderiv : HasDerivAt (fun r : Real => ∑ k, b.repr (V r) k * (g r).inner x (b k) Z)
      (∑ k, (b.repr Vdot k * (g t).inner x (b k) Z +
        b.repr (V t) k * ((-2 : Real) * metricRicciAt (I := I) (g t) x
          (fun a : Fin 2 => if a = 0 then b k else Z)))) t :=
    HasDerivAt.fun_sum fun k _ => (hcomp k).mul (hPDE (b k) Z)
  have hval :
      (∑ k, (b.repr Vdot k * (g t).inner x (b k) Z +
        b.repr (V t) k * ((-2 : Real) * metricRicciAt (I := I) (g t) x
          (fun a : Fin 2 => if a = 0 then b k else Z)))) =
        (g t).inner x Vdot Z +
          (-2 : Real) * metricRicciAt (I := I) (g t) x
            (fun a : Fin 2 => if a = 0 then V t else Z) := by
    rw [Finset.sum_add_distrib]
    have hg : (∑ k, b.repr Vdot k * (g t).inner x (b k) Z) = (g t).inner x Vdot Z := by
      rw [← metField0 (I := I) (g t) x Vdot Z,
        tensor02_expand (I := I) (metricTensorField (I := I) (g t) x) b Vdot Z]
      exact Finset.sum_congr rfl fun k _ => by rw [metField0]
    have hr : (∑ k, b.repr (V t) k * ((-2 : Real) * metricRicciAt (I := I) (g t) x
          (fun a : Fin 2 => if a = 0 then b k else Z))) =
        (-2 : Real) * metricRicciAt (I := I) (g t) x
          (fun a : Fin 2 => if a = 0 then V t else Z) := by
      rw [tensor02_expand (I := I) (metricRicciAt (I := I) (g t) x) b (V t) Z, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hg, hr]
  have hfin := hderiv.congr_deriv hval
  simpa only [hsum] using hfin

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The time derivative of the lowering gap.**  `∂ₜG = 2(Ric₁ − Ric₂)(Rm¹³₂ ·, ·) −
h₀₂(∂ₜRm¹³₂ ·, ·)`: both summands are a *difference* carrier against a background factor,
which is the shape the bundle's `bounds` field consumes.  Only each flow's own metric PDE and
the flow-`2` curvature speed enter. -/
theorem gap_deriv (g₁ g₂ : Real -> SmoothRiemannianMetric I M)
    (Rm2dot : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    {t : Real}
    (hPDE₁ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hPDE₂ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₂ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₂ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hRm2 : ∀ X Y Z : TangentSpace I x,
      HasDerivAt (fun r : Real => riemannOp (metricCov (I := I) (g₂ r)) x X Y Z)
        (((Rm2dot X) Y) Z) t)
    (v : Fin 4 -> TangentSpace I x) :
    HasDerivAt (fun r : Real => gapAt (I := I) (g₁ r) (g₂ r) x v)
      (gapDot (I := I) (g₁ t) (g₂ t) Rm2dot v) t := by
  classical
  have hv : vec4 (I := I) (v 0) (v 1) (v 2) (v 3) = v := by
    funext i
    fin_cases i <;> simp [vec4]
  set V : Real -> TangentSpace I x :=
    fun r => riemannOp (metricCov (I := I) (g₂ r)) x (v 0) (v 1) (v 2) with hV
  have hVd : HasDerivAt V (((Rm2dot (v 0)) (v 1)) (v 2)) t := hRm2 (v 0) (v 1) (v 2)
  have h2 : ∀ r : Real, metricRm04At (I := I) (g₂ r) x v = (g₂ r).inner x (V r) (v 3) := by
    intro r
    have h := metricRm04At_inner (I := I) (g₂ r) x (v 0) (v 1) (v 2) (v 3)
    rw [hv] at h
    exact h
  have h1 : ∀ r : Real,
      CovariantDerivative.riemannCurvature04At (I := I) (g₁ r) (metricCov (I := I) (g₂ r))
          (metricCov_smooth (I := I) (g₂ r)) x v = (g₁ r).inner x (V r) (v 3) := by
    intro r
    have h := rm04mix_inner (I := I) (g₁ r) (g₂ r) x (v 0) (v 1) (v 2) (v 3)
    rw [hv] at h
    exact h
  have hgap : ∀ r : Real,
      gapAt (I := I) (g₁ r) (g₂ r) x v =
        (g₂ r).inner x (V r) (v 3) - (g₁ r).inner x (V r) (v 3) := by
    intro r
    rw [gapAt, Tensor0SSpace.sub_apply (I := I) 4 x _ _ v, h2 r, h1 r]
  have hd₂ := innerCurve_deriv (I := I) g₂ V (((Rm2dot (v 0)) (v 1)) (v 2)) (v 3) hVd hPDE₂
  have hd₁ := innerCurve_deriv (I := I) g₁ V (((Rm2dot (v 0)) (v 1)) (v 2)) (v 3) hVd hPDE₁
  have hmain := hd₂.sub hd₁
  have hval :
      ((g₂ t).inner x (((Rm2dot (v 0)) (v 1)) (v 2)) (v 3) +
          (-2 : Real) * metricRicciAt (I := I) (g₂ t) x
            (fun a : Fin 2 => if a = 0 then V t else v 3)) -
        ((g₁ t).inner x (((Rm2dot (v 0)) (v 1)) (v 2)) (v 3) +
          (-2 : Real) * metricRicciAt (I := I) (g₁ t) x
            (fun a : Fin 2 => if a = 0 then V t else v 3)) =
        gapDot (I := I) (g₁ t) (g₂ t) Rm2dot v := by
    rw [gapDot, Tensor0SSpace.sub_apply (I := I) 4 x _ _ v,
      Tensor0SSpace.smul_apply (I := I) 4 x (2 : Real) _ v,
      lowerTri_apply, lowerTri_apply,
      Tensor0SSpace.sub_apply (I := I) 2 x (metricRicciAt (I := I) (g₁ t) x)
        (metricRicciAt (I := I) (g₂ t) x) _,
      metricDiffAt]
    have hmet : (metricTensorField (I := I) (g₁ t) x - metricTensorField (I := I) (g₂ t) x)
        (fun a : Fin 2 => if a = 0 then ((Rm2dot (v 0)) (v 1)) (v 2) else v 3) =
        (g₁ t).inner x (((Rm2dot (v 0)) (v 1)) (v 2)) (v 3) -
          (g₂ t).inner x (((Rm2dot (v 0)) (v 1)) (v 2)) (v 3) := by
      rw [Tensor0SSpace.sub_apply (I := I) 2 x _ _ _, metField0, metField0]
    rw [hmet, smul_eq_mul]
    have hVt : V t = riemannOp (metricCov (I := I) (g₂ t)) x (v 0) (v 1) (v 2) := rfl
    rw [hVt]
    ring
  have hfin := hmain.congr_deriv hval
  simpa only [hgap] using hfin

end Deriv

/-! ## The gap as a re-lowering, and its rough Laplacian -/

section LapGap

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The gap is the swapped re-lowering.**  If the field `P` realizes the `g₁`-lowered
curvature of `g₂`, then `reLower g₂ g₁ P` — the K2.6c re-lowering with its two metric
arguments **swapped**, so that its trace metric and its connection are both `g₁` — realizes
the own-lowered `Rm04₂`.  Hence `G = reLower g₂ g₁ P − P`. -/
theorem reLower_rm2Low (g₁ g₂ : SmoothRiemannianMetric I M)
    (P : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M)
    (hP : P x = CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
      (metricCov_smooth (I := I) g₂) x) :
    reLower (I := I) g₂ g₁ P x = metricRm04At (I := I) g₂ x := by
  classical
  refine ContinuousMultilinearMap.ext fun tail => ?_
  have hl3 : (Fin.last 3 : Fin 4) = (3 : Fin 4) := rfl
  have hupd : Function.update tail (Fin.last 3)
      (sharpFlat (I := I) g₂ g₁ x (tail (Fin.last 3))) =
      vec4 (I := I) (tail 0) (tail 1) (tail 2)
        (sharpFlat (I := I) g₂ g₁ x (tail (Fin.last 3))) := by
    funext i
    fin_cases i <;> simp [vec4, Function.update]
  have htail : tail = vec4 (I := I) (tail 0) (tail 1) (tail 2) (tail (Fin.last 3)) := by
    funext i
    fin_cases i <;> simp [vec4, hl3]
  rw [reLower_apply (I := I) g₂ g₁ P x tail, hP, hupd, rm04mix_inner, inner_sharpFlat]
  conv_rhs => rw [htail]
  rw [metricRm04At_inner]

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The rough Laplacian of the gap, in divergence form.**

```
Δ₁(reLower g₂ g₁ P − P) = (reLower g₂ g₁ − id)(Δ₁P) + div₁Q + tr₁Q′,
Q  = reLowerPair g₁ P (∇¹g₂),        Q′ = reLowerPair g₁ (∇¹P) (∇¹g₂),
```

with `∇¹g₂ = lapDiffFlux g₁ g₂ g₂` (`nabla1_metric2`), so both carriers are `A₀₃`-flux algebra
against the background `P`.  The divergence is the **`g₁`** divergence — the one the Kotschwar
energy integrates by parts against — which is exactly what the swapped argument order buys.
The leading term is `(id − g₁♯h₀₂♭)` applied to the last slot of `Δ₁P`: a difference carrier
against a bounded background. -/
theorem lapGap_eq (g₁ g₂ : SmoothRiemannianMetric I M)
    (P : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) :
    roughLap0SField (I := I) g₁ (reLower (I := I) g₂ g₁ P - P) =
      (reLower (I := I) g₂ g₁ (roughLap0SField (I := I) g₁ P) -
          roughLap0SField (I := I) g₁ P) +
        (covDiv0SField (I := I) g₁
            (reLowerPair (I := I) g₁ P
              (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂))) +
          metricTraceFirstTwoField (I := I) (M := M) (s := 4) g₁
            (reLowerPair (I := I) g₁ (metricNabla0S (I := I) g₁ P)
              (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂)))) := by
  have h := lapComm_reLower_eq (I := I) g₂ g₁ (k := 3) P
  rw [nabla1_metric2 (I := I) g₁ g₂] at h
  have h' : roughLap0SField (I := I) g₁ (reLower (I := I) g₂ g₁ P) =
      reLower (I := I) g₂ g₁ (roughLap0SField (I := I) g₁ P) +
        (covDiv0SField (I := I) g₁
            (reLowerPair (I := I) g₁ P
              (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂))) +
          metricTraceFirstTwoField (I := I) (M := M) (s := 4) g₁
            (reLowerPair (I := I) g₁ (metricNabla0S (I := I) g₁ P)
              (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂)))) := by
    rw [← h]; abel
  rw [roughLap0SField_sub, h']
  abel

end LapGap

/-! ## The flow-`2` curvature speed as an invariant trilinear map -/

section Rm2Speed

variable {Idx : Type*} [Fintype Idx]

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The bundled `(1,3)` speed of one flow's curvature.**  The `quadOfComp` package of
`uhlRaisedDeriv`: the invariant form of the raised right-hand side that `rmVecComp_deriv`
produces from that flow's own-lowered Uhlenbeck interface. -/
def uhlRm2Vec (g : Real -> SmoothRiemannianMetric I M)
    (basisAt : (y : M) -> Module.Basis Idx Real (TangentSpace I y))
    (Rm04 roughLapRm04 B : FourComp M Idx) (ricciOneUp : MatrixComp M Idx)
    (t : Real) (y : M) :
    TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y →L[Real]
      TangentSpace I y :=
  quadOfComp (I := I) (basisAt y)
    (fun i j k l => (basisAt y).repr
      (uhlRaisedDeriv (I := I) g basisAt Rm04 roughLapRm04 B ricciOneUp t y i j k) l)

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The flow's curvature speed at every triple**, from its own-lowered interface, its own
metric PDE and the two benign realization/continuity inputs of `rmVecComp_deriv`. -/
theorem uhlRm2_deriv
    {D : RealTimeInterval}
    (g : Real -> SmoothRiemannianMetric I M)
    (basisAt : (y : M) -> Module.Basis Idx Real (TangentSpace I y))
    (Rm04 roughLapRm04 B : FourComp M Idx) (ricciOneUp : MatrixComp M Idx)
    {a b : Real} (hreg : Set.Ioo a b ⊆ D.regular)
    (hev : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D)
      Rm04 roughLapRm04 B ricciOneUp)
    (hreal : ∀ (r : Real) (y : M) (i j k l : Idx),
      Rm04 r y i j k l =
        metricRm04At (I := I) (g r) y
          (vec4 (I := I) (basisAt y i) (basisAt y j) (basisAt y k) (basisAt y l)))
    (hcont : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (i j k : Idx),
      ContinuousWithinAt
        (fun r : Real =>
          riemannOp (metricCov (I := I) (g r)) y (basisAt y i) (basisAt y j) (basisAt y k))
        D.carrier t)
    (hPDE : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (U W : TangentSpace I y),
      HasDerivWithinAt (fun r : Real => (g r).inner y U W)
        ((-2 : Real) * metricRicciAt (I := I) (g t) y
          (fun q : Fin 2 => if q = 0 then U else W)) D.carrier t)
    {t : Real} (ht : t ∈ Set.Ioo a b) (y : M) (X Y Z : TangentSpace I y) :
    HasDerivAt (fun r : Real => riemannOp (metricCov (I := I) (g r)) y X Y Z)
      (((uhlRm2Vec (I := I) g basisAt Rm04 roughLapRm04 B ricciOneUp t y X) Y) Z) t := by
  have hnhds : D.carrier ∈ 𝓝 t := D.regular_mem_nhds (hreg ht)
  refine vec3_deriv_basis (I := I)
    (fun r : Real => riemannOp (metricCov (I := I) (g r)) y) (basisAt y) _ ?_ X Y Z
  intro i j k
  have hval :
      ((uhlRm2Vec (I := I) g basisAt Rm04 roughLapRm04 B ricciOneUp t y (basisAt y i))
          (basisAt y j)) (basisAt y k) =
        uhlRaisedDeriv (I := I) g basisAt Rm04 roughLapRm04 B ricciOneUp t y i j k :=
    quadOfComp_vec (I := I) (basisAt y) _ i j k
  rw [hval]
  have h := rmVecComp_deriv (I := I) (D := D) g (basisAt y)
    Rm04 roughLapRm04 B ricciOneUp (metricRicciAt (I := I) (g t) y) hev
    ⟨t, hreg ht⟩ i j k (hcont t ht y i j k) (hPDE t ht y) (fun r l => hreal r y i j k l)
  exact h.hasDerivAt hnhds

end Rm2Speed

/-! ## The `S`-equation -/

section Assembly

variable {Idx : Type*} [Fintype Idx]

/-- **`U′`: the flux of the `S`-equation.**  The K2.3 flux of the *background* field `Rm04₂`
minus the re-lowering commutator flux; both carriers are the connection-difference flux `A₀₃`
acting algebraically on a background factor, and neither differentiates a difference carrier —
that is the divergence-form property the energy estimate consumes. -/
def sdecFlux (g₁ g₂ : SmoothRiemannianMetric I M)
    (Tf₂ P : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5 :=
  lapDiffFlux (I := I) g₁ g₂ Tf₂ -
    reLowerPair (I := I) g₁ P (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂))

/-- **`rem′`: the remainder of the `S`-equation.**  Four manifest shapes:

* `lowOfComp g₁ b R₀` — the K2.6-core componentwise remainder `rmDotRem`, tensorised: the K2.3
  spatial remainder of the background plus the two flows' `B`-quadratic and Ricci-drift
  *differences* (`driftDiff_split` exhibits the last one as a difference against a background);
* `gapDot` — `2(Ric₁ − Ric₂)(Rm¹³₂ ·, ·) − h₀₂(∂ₜRm¹³₂ ·, ·)`;
* `(reLower g₂ g₁ − id)(Δ₁P)` — the metric difference against the bounded background `Δ₁P`;
* `tr₁(reLowerPair g₁ (∇¹P) (∇¹g₂))` — `A₀₃`-flux algebra against `∇¹P`.

No derivative of a difference carrier appears outside the divergence. -/
def sdecRem (g₁ g₂ : SmoothRiemannianMetric I M) {x : M}
    (P : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (b : Module.Basis Idx Real (TangentSpace I x))
    (R₀ : Idx -> Idx -> Idx -> Idx -> Real)
    (Rm2dot : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  lowOfComp (I := I) g₁ b R₀ + gapDot (I := I) g₁ g₂ Rm2dot -
      (reLower (I := I) g₂ g₁ (roughLap0SField (I := I) g₁ P) -
        roughLap0SField (I := I) g₁ P) x -
    metricTraceFirstTwoField (I := I) (M := M) (s := 4) g₁
      (reLowerPair (I := I) g₁ (metricNabla0S (I := I) g₁ P)
        (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂))) x

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **K6c: the Kotschwar `S`-equation in divergence form** (`ForwardUniqueAssembly`'s `sdec`
member, in the `NormedSpace` currency of `rmDiffDot`).

The invariant speed of `S₀₄` splits as `Δ₁S₀₄ + div₁U′ + rem′` with `U′ = sdecFlux` and
`rem′ = sdecRem` explicit.  Inputs: the two per-flow **own-lowered** Uhlenbeck interfaces
(ruling R1), the two per-flow Ricci-flow equations, and the realization/continuity inputs that
`rm_of_uhlenbeck` and `rmDiffComp_deriv` already carry — the supplied `(0,4)` fields realize
each flow's own curvature (`hT₁`, `hT₂`) and the carrier (`hcar`, the bundle's own `car`
field), and the supplied rough-Laplacian families realize the intrinsic ones (`hL₁`, `hL₂`).
No cross-metric lowering is ever assumed. -/
theorem sdec_core
    {D : RealTimeInterval}
    (g₁ g₂ : Real -> SmoothRiemannianMetric I M)
    (basisAt : (y : M) -> Module.Basis Idx Real (TangentSpace I y))
    (Rm04₁ roughLapRm04₁ B₁ : FourComp M Idx) (ricciOneUp₁ : MatrixComp M Idx)
    (Rm04₂ roughLapRm04₂ B₂ : FourComp M Idx) (ricciOneUp₂ : MatrixComp M Idx)
    (Tf₁ Tf₂ Sfield : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    {a b : Real} (hreg : Set.Ioo a b ⊆ D.regular)
    (hev₁ : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D)
      Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁)
    (hev₂ : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D)
      Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂)
    (hreal₁ : ∀ (r : Real) (y : M) (i j k l : Idx),
      Rm04₁ r y i j k l =
        metricRm04At (I := I) (g₁ r) y
          (vec4 (I := I) (basisAt y i) (basisAt y j) (basisAt y k) (basisAt y l)))
    (hreal₂ : ∀ (r : Real) (y : M) (i j k l : Idx),
      Rm04₂ r y i j k l =
        metricRm04At (I := I) (g₂ r) y
          (vec4 (I := I) (basisAt y i) (basisAt y j) (basisAt y k) (basisAt y l)))
    (hcont₁ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (i j k : Idx),
      ContinuousWithinAt
        (fun r : Real =>
          riemannOp (metricCov (I := I) (g₁ r)) y (basisAt y i) (basisAt y j) (basisAt y k))
        D.carrier t)
    (hcont₂ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (i j k : Idx),
      ContinuousWithinAt
        (fun r : Real =>
          riemannOp (metricCov (I := I) (g₂ r)) y (basisAt y i) (basisAt y j) (basisAt y k))
        D.carrier t)
    (hPDE₁ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (U W : TangentSpace I y),
      HasDerivWithinAt (fun r : Real => (g₁ r).inner y U W)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) y
          (fun q : Fin 2 => if q = 0 then U else W)) D.carrier t)
    (hPDE₂ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (U W : TangentSpace I y),
      HasDerivWithinAt (fun r : Real => (g₂ r).inner y U W)
        ((-2 : Real) * metricRicciAt (I := I) (g₂ t) y
          (fun q : Fin 2 => if q = 0 then U else W)) D.carrier t)
    (hT₁ : ∀ t ∈ Set.Ioo a b, ∀ y : M, Tf₁ t y = metricRm04At (I := I) (g₁ t) y)
    (hT₂ : ∀ t ∈ Set.Ioo a b, ∀ y : M, Tf₂ t y = metricRm04At (I := I) (g₂ t) y)
    (hcar : ∀ t ∈ Set.Ioo a b, ∀ y : M, Sfield t y = rmDiffLowAt (I := I) (g₁ t) (g₂ t) y)
    (hL₁ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (i j k l : Idx),
      roughLapRm04₁ t y i j k l =
        roughLap0SField (I := I) (g₁ t) (Tf₁ t) y
          (frameVec4 (I := I) (fun m z => basisAt z m) y i j k l))
    (hL₂ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (i j k l : Idx),
      roughLapRm04₂ t y i j k l =
        roughLap0SField (I := I) (g₂ t) (Tf₂ t) y
          (frameVec4 (I := I) (fun m z => basisAt z m) y i j k l)) :
    ∀ t ∈ Set.Ioo a b, ∀ x : M,
      rmDiffDot (I := I) g₁ g₂
          (uhlRmDiffSpeed (I := I) g₁ g₂ basisAt Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁
            Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t) t x =
        roughLap0SField (I := I) (g₁ t) (Sfield t) x +
          covDiv0SField (I := I) (g₁ t)
            (sdecFlux (I := I) (g₁ t) (g₂ t) (Tf₂ t) (Tf₁ t - Sfield t)) x +
          sdecRem (I := I) (g₁ t) (g₂ t) (Tf₁ t - Sfield t) (basisAt x)
            (rmDotRem (I := I) (g₁ t) (g₂ t) (Tf₂ t) Rm04₁ Rm04₂ B₁ B₂
              ricciOneUp₁ ricciOneUp₂ (fun m z => basisAt z m) t x)
            (uhlRm2Vec (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t x) := by
  classical
  intro t ht x
  have hnhds : D.carrier ∈ 𝓝 t := D.regular_mem_nhds (hreg ht)
  set P : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) 4 := Tf₁ t - Sfield t with hPdef
  -- `P` realizes the `g₁`-lowered curvature of `g₂`.
  have hPreal : ∀ y : M, P y =
      CovariantDerivative.riemannCurvature04At (I := I) (g₁ t) (metricCov (I := I) (g₂ t))
        (metricCov_smooth (I := I) (g₂ t)) y := by
    intro y
    have hval : P y = Tf₁ t y - Sfield t y := rfl
    rw [hval, hT₁ t ht y, hcar t ht y, ← rm2Low_eq_sub]
  -- the swapped re-lowering of `P` is the own-lowered curvature of `g₂`
  have hRl : reLower (I := I) (g₂ t) (g₁ t) P = Tf₂ t := by
    refine DFunLike.ext _ _ fun y => ?_
    rw [reLower_rm2Low (I := I) (g₁ t) (g₂ t) P y (hPreal y)]
    exact (hT₂ t ht y).symm
  -- the field split `Rm04₁ − Rm04₂ = S₀₄ − G`
  have hsplit : Tf₁ t - Tf₂ t = Sfield t - (reLower (I := I) (g₂ t) (g₁ t) P - P) := by
    rw [hRl, hPdef]; abel
  have hlapD : roughLap0SField (I := I) (g₁ t) (Tf₁ t - Tf₂ t) =
      roughLap0SField (I := I) (g₁ t) (Sfield t) -
        roughLap0SField (I := I) (g₁ t) (reLower (I := I) (g₂ t) (g₁ t) P - P) := by
    rw [hsplit, roughLap0SField_sub]
  have hlapG := lapGap_eq (I := I) (g₁ t) (g₂ t) P
  -- reduce the tensor identity to frame tuples
  refine ContinuousMultilinearMap.toMultilinearMap_injective
    (Module.Basis.ext_multilinear (fun _ : Fin 4 => basisAt x) fun w => ?_)
  have hw : (fun p : Fin 4 => (basisAt x) (w p)) =
      frameVec4 (I := I) (fun m z => basisAt z m) x (w 0) (w 1) (w 2) (w 3) := by
    funext p
    fin_cases p <;> simp [frameVec4, vec4]
  simp only [ContinuousMultilinearMap.coe_coe, hw]
  set i : Idx := w 0 with hi
  set j : Idx := w 1 with hj
  set k : Idx := w 2 with hk
  set l : Idx := w 3 with hl
  set v : Fin 4 -> TangentSpace I x :=
    frameVec4 (I := I) (fun m z => basisAt z m) x i j k l with hvdef
  have hvv : v = vec4 (I := I) (basisAt x i) (basisAt x j) (basisAt x k) (basisAt x l) := rfl
  -- the three derivative facts
  have hPDE₁' : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun q : Fin 2 => if q = 0 then X else Y)) t :=
    fun X Y => (hPDE₁ t ht x X Y).hasDerivAt hnhds
  have hPDE₂' : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₂ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₂ t) x
          (fun q : Fin 2 => if q = 0 then X else Y)) t :=
    fun X Y => (hPDE₂ t ht x X Y).hasDerivAt hnhds
  have hrm := rm_of_uhlenbeck (I := I) (D := D) g₁ g₂ basisAt
    Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁ Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂
    hreg hev₁ hev₂ hreal₁ hreal₂ hcont₁ hcont₂ hPDE₁ hPDE₂ t ht x
  have hS := rmDiffLow_hasDerivAt (I := I) g₁ g₂
    (uhlRmDiffSpeed (I := I) g₁ g₂ basisAt Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁
      Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t) hPDE₁' hrm v
  have hD0 := rmDiffComp_deriv (I := I) (D := D) (g₁ t) (g₂ t) (Tf₁ t) (Tf₂ t)
    Rm04₁ Rm04₂ roughLapRm04₁ roughLapRm04₂ B₁ B₂ ricciOneUp₁ ricciOneUp₂
    (fun m z => basisAt z m) hev₁ hev₂ ⟨t, hreg ht⟩ x i j k l
    (hL₁ t ht x i j k l) (hL₂ t ht x i j k l)
  have hfunD : (fun r : Real => Rm04₁ r x i j k l - Rm04₂ r x i j k l) =
      (fun r : Real =>
        (metricRm04At (I := I) (g₁ r) x - metricRm04At (I := I) (g₂ r) x) v) := by
    funext r
    rw [hreal₁ r x i j k l, hreal₂ r x i j k l, hvv,
      Tensor0SSpace.sub_apply (I := I) 4 x _ _ _]
  rw [hfunD] at hD0
  have hD := hD0.hasDerivAt hnhds
  have hRm2 : ∀ X Y Z : TangentSpace I x,
      HasDerivAt (fun r : Real => riemannOp (metricCov (I := I) (g₂ r)) x X Y Z)
        (((uhlRm2Vec (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t x X) Y) Z) t :=
    fun X Y Z => uhlRm2_deriv (I := I) (D := D) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂
      hreg hev₂ hreal₂ hcont₂ hPDE₂ ht x X Y Z
  have hG := gap_deriv (I := I) g₁ g₂
    (uhlRm2Vec (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t x)
    hPDE₁' hPDE₂' hRm2 v
  have hfunS : (fun r : Real => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x v) =
      (fun r : Real =>
        (metricRm04At (I := I) (g₁ r) x - metricRm04At (I := I) (g₂ r) x) v +
          gapAt (I := I) (g₁ r) (g₂ r) x v) :=
    funext fun r => rmDiffLow_split (I := I) (g₁ r) (g₂ r) x v
  rw [hfunS] at hS
  have huniq := hS.unique (hD.add hG)
  -- pointwise evaluation of the three field identities
  have e1 : roughLap0SField (I := I) (g₁ t) (Tf₁ t - Tf₂ t) x v =
      roughLap0SField (I := I) (g₁ t) (Sfield t) x v -
        roughLap0SField (I := I) (g₁ t) (reLower (I := I) (g₂ t) (g₁ t) P - P) x v := by
    rw [hlapD]
    exact fieldSub_eval (I := I) _ _ x v
  have e2 : roughLap0SField (I := I) (g₁ t) (reLower (I := I) (g₂ t) (g₁ t) P - P) x v =
      (reLower (I := I) (g₂ t) (g₁ t) (roughLap0SField (I := I) (g₁ t) P) -
          roughLap0SField (I := I) (g₁ t) P) x v +
        (covDiv0SField (I := I) (g₁ t)
            (reLowerPair (I := I) (g₁ t) P
              (lapDiffFlux (I := I) (g₁ t) (g₂ t) (metricTensorField (I := I) (g₂ t)))) x v +
          metricTraceFirstTwoField (I := I) (M := M) (s := 4) (g₁ t)
            (reLowerPair (I := I) (g₁ t) (metricNabla0S (I := I) (g₁ t) P)
              (lapDiffFlux (I := I) (g₁ t) (g₂ t) (metricTensorField (I := I) (g₂ t)))) x v) := by
    rw [hlapG, fieldAdd_eval, fieldAdd_eval]
  have e3 : covDiv0SField (I := I) (g₁ t)
        (sdecFlux (I := I) (g₁ t) (g₂ t) (Tf₂ t) P) x v =
      covDiv0SField (I := I) (g₁ t) (lapDiffFlux (I := I) (g₁ t) (g₂ t) (Tf₂ t)) x v -
        covDiv0SField (I := I) (g₁ t)
          (reLowerPair (I := I) (g₁ t) P
            (lapDiffFlux (I := I) (g₁ t) (g₂ t) (metricTensorField (I := I) (g₂ t)))) x v := by
    rw [sdecFlux, covDiv0SField_sub]
    exact fieldSub_eval (I := I) _ _ x v
  have e4 : sdecRem (I := I) (g₁ t) (g₂ t) P (basisAt x)
        (rmDotRem (I := I) (g₁ t) (g₂ t) (Tf₂ t) Rm04₁ Rm04₂ B₁ B₂
          ricciOneUp₁ ricciOneUp₂ (fun m z => basisAt z m) t x)
        (uhlRm2Vec (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t x) v =
      rmDotRem (I := I) (g₁ t) (g₂ t) (Tf₂ t) Rm04₁ Rm04₂ B₁ B₂
          ricciOneUp₁ ricciOneUp₂ (fun m z => basisAt z m) t x i j k l +
        gapDot (I := I) (g₁ t) (g₂ t)
          (uhlRm2Vec (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t x) v -
        (reLower (I := I) (g₂ t) (g₁ t) (roughLap0SField (I := I) (g₁ t) P) -
          roughLap0SField (I := I) (g₁ t) P) x v -
        metricTraceFirstTwoField (I := I) (M := M) (s := 4) (g₁ t)
          (reLowerPair (I := I) (g₁ t) (metricNabla0S (I := I) (g₁ t) P)
            (lapDiffFlux (I := I) (g₁ t) (g₂ t) (metricTensorField (I := I) (g₂ t)))) x v := by
    rw [sdecRem, Tensor0SSpace.sub_apply (I := I) 4 x _ _ v,
      Tensor0SSpace.sub_apply (I := I) 4 x _ _ v,
      Tensor0SSpace.add_apply (I := I) 4 x _ _ v, hvv, lowOfComp_eval]
  rw [Tensor0SSpace.add_apply (I := I) 4 x _ _ v, Tensor0SSpace.add_apply (I := I) 4 x _ _ v,
    e3, e4]
  rw [huniq, e1, e2]
  ring

/-- **The `Uflux` datum of `ForwardUniqueInputs`**, as a time-indexed family. -/
def sdecUflux (g₁ g₂ : Real -> SmoothRiemannianMetric I M)
    (Tf₁ Tf₂ Sfield : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5 :=
  sdecFlux (I := I) (g₁ t) (g₂ t) (Tf₂ t) (Tf₁ t - Sfield t)

/-- **The `rem` datum of `ForwardUniqueInputs`**, as a time-indexed pointwise family. -/
def sdecRemFam (g₁ g₂ : Real -> SmoothRiemannianMetric I M)
    (basisAt : (y : M) -> Module.Basis Idx Real (TangentSpace I y))
    (Rm04₁ B₁ : FourComp M Idx) (ricciOneUp₁ : MatrixComp M Idx)
    (Rm04₂ roughLapRm04₂ B₂ : FourComp M Idx) (ricciOneUp₂ : MatrixComp M Idx)
    (Tf₁ Tf₂ Sfield : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (t : Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  sdecRem (I := I) (g₁ t) (g₂ t) (Tf₁ t - Sfield t) (basisAt x)
    (rmDotRem (I := I) (g₁ t) (g₂ t) (Tf₂ t) Rm04₁ Rm04₂ B₁ B₂
      ricciOneUp₁ ricciOneUp₂ (fun m z => basisAt z m) t x)
    (uhlRm2Vec (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t x)

end Assembly

end NormedBase

/-! ## Part 2: the bundle's `sdec` member

`rmSpeed` is defined in the `InnerProductSpace ℝ E` context of
`Evolution/ForwardUniqueAssembly.lean`, so the restatement gets its own section; the proof is
`sdec_core` across the instance diamond (`rmSpeed g₁ g₂ Svec t x = rmDiffDot g₁ g₂ (Svec t) t x`
definitionally). -/

section Bundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
variable {Idx : Type*} [Fintype Idx]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **K6c collapse of the bundle's `sdec` member.**

The `sdec` field of `ForwardUniqueAssembly.ForwardUniqueInputs`, verbatim, for the same speed
carrier `Svec = uhlRmDiffSpeed` that `rm_of_uhlenbeck` (K6b) produces for the `rm` field, with
`Uflux = sdecUflux` and `rem = sdecRemFam` **constructed**, not assumed.

Residual inputs, all shared with `rm_of_uhlenbeck` / `rmDiffComp_deriv`:

* `hev₁`, `hev₂` — the two per-flow **own-lowered** Uhlenbeck interfaces (ruling R1);
* `hPDE₁`, `hPDE₂` — the two per-flow Ricci-flow equations in the lane's `metricRicciAt`
  currency, one-sided within the interval carrier;
* `hreal₁`, `hreal₂`, `hcont₁`, `hcont₂` — the realization/continuity inputs of
  `rmVecComp_deriv` (each flow's **own** lowering only);
* `hT₁`, `hT₂`, `hL₁`, `hL₂` — the supplied `(0,4)` fields realize each flow's own curvature
  and the supplied rough-Laplacian families realize the intrinsic ones;
* `hcar` — the bundle's own `car` field.

No cross-metric lowering, no new carrier and no norm bound is assumed here. -/
theorem sdec_of_uhlenbeck
    {D : RealTimeInterval}
    (g₁ g₂ : Real -> SmoothRiemannianMetric I M)
    (basisAt : (y : M) -> Module.Basis Idx Real (TangentSpace I y))
    (Rm04₁ roughLapRm04₁ B₁ : FourComp M Idx) (ricciOneUp₁ : MatrixComp M Idx)
    (Rm04₂ roughLapRm04₂ B₂ : FourComp M Idx) (ricciOneUp₂ : MatrixComp M Idx)
    (Tf₁ Tf₂ Sfield : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    {a b : Real} (hreg : Set.Ioo a b ⊆ D.regular)
    (hev₁ : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D)
      Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁)
    (hev₂ : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D)
      Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂)
    (hreal₁ : ∀ (r : Real) (y : M) (i j k l : Idx),
      Rm04₁ r y i j k l =
        metricRm04At (I := I) (g₁ r) y
          (vec4 (I := I) (basisAt y i) (basisAt y j) (basisAt y k) (basisAt y l)))
    (hreal₂ : ∀ (r : Real) (y : M) (i j k l : Idx),
      Rm04₂ r y i j k l =
        metricRm04At (I := I) (g₂ r) y
          (vec4 (I := I) (basisAt y i) (basisAt y j) (basisAt y k) (basisAt y l)))
    (hcont₁ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (i j k : Idx),
      ContinuousWithinAt
        (fun r : Real =>
          riemannOp (metricCov (I := I) (g₁ r)) y (basisAt y i) (basisAt y j) (basisAt y k))
        D.carrier t)
    (hcont₂ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (i j k : Idx),
      ContinuousWithinAt
        (fun r : Real =>
          riemannOp (metricCov (I := I) (g₂ r)) y (basisAt y i) (basisAt y j) (basisAt y k))
        D.carrier t)
    (hPDE₁ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (U W : TangentSpace I y),
      HasDerivWithinAt (fun r : Real => (g₁ r).inner y U W)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) y
          (fun q : Fin 2 => if q = 0 then U else W)) D.carrier t)
    (hPDE₂ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (U W : TangentSpace I y),
      HasDerivWithinAt (fun r : Real => (g₂ r).inner y U W)
        ((-2 : Real) * metricRicciAt (I := I) (g₂ t) y
          (fun q : Fin 2 => if q = 0 then U else W)) D.carrier t)
    (hT₁ : ∀ t ∈ Set.Ioo a b, ∀ y : M, Tf₁ t y = metricRm04At (I := I) (g₁ t) y)
    (hT₂ : ∀ t ∈ Set.Ioo a b, ∀ y : M, Tf₂ t y = metricRm04At (I := I) (g₂ t) y)
    (hcar : ∀ t ∈ Set.Ioo a b, ∀ y : M, Sfield t y = rmDiffLowAt (I := I) (g₁ t) (g₂ t) y)
    (hL₁ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (i j k l : Idx),
      roughLapRm04₁ t y i j k l =
        roughLap0SField (I := I) (g₁ t) (Tf₁ t) y
          (frameVec4 (I := I) (fun m z => basisAt z m) y i j k l))
    (hL₂ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (i j k l : Idx),
      roughLapRm04₂ t y i j k l =
        roughLap0SField (I := I) (g₂ t) (Tf₂ t) y
          (frameVec4 (I := I) (fun m z => basisAt z m) y i j k l)) :
    ∀ t ∈ Set.Ioo a b, ∀ x : M,
      rmSpeed (I := I) g₁ g₂
          (uhlRmDiffSpeed (I := I) g₁ g₂ basisAt Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁
            Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂) t x =
        roughLap0SField (I := I) (g₁ t) (Sfield t) x +
          covDiv0SField (I := I) (g₁ t)
            (sdecUflux (I := I) g₁ g₂ Tf₁ Tf₂ Sfield t) x +
          sdecRemFam (I := I) g₁ g₂ basisAt Rm04₁ B₁ ricciOneUp₁
            Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ Tf₁ Tf₂ Sfield t x :=
  sdec_core (I := I) (D := D) g₁ g₂ basisAt Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁
    Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ Tf₁ Tf₂ Sfield hreg hev₁ hev₂ hreal₁ hreal₂
    hcont₁ hcont₂ hPDE₁ hPDE₂ hT₁ hT₂ hcar hL₁ hL₂

end Bundle

end DifferentialGeometry.PDE.RicciFlow

end
