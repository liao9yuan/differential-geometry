import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRmDot

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option backward.isDefEq.respectTransparency false

/-!
# The R4 bridge: own-lowered interfaces to the `S₀₄` carrier organization

Route-K brick **K2.6b** (`ShortTime/FORWARD_UNIQUE_PLAN.md` №13, planner ruling **R4**).

The two honest per-flow curvature-evolution interfaces
(`Riemann04BTensorWithRicciDriftEvolutionInFrameOn`, `Evolution/Uhlenbeck.lean`) describe
each flow's **own-metric-lowered** curvature `Rm04ᵢ = gᵢ(Rm¹³ᵢ ·, ·)`.  Their difference is
`metricRm04At g₁ − metricRm04At g₂`, which is *not* the Kotschwar carrier
`S₀₄ = rmDiffLowAt g₁ g₂` (both terms of which lower with `g₁`).  Ruling R4 keeps the `S₀₄`
carrier and bridges on the interface side.  This file supplies the first half of that
bridge, plus the parallelism identities that the second half consumes.

## Part 1 — own-metric raise (`(0,4)` interface ⟹ `(1,3)` evolution)

The `(1,3)` curvature `riemannOp (metricCov g)` is recovered from the own-lowered `(0,4)`
tensor by raising with `g`, and raising commutes with `∂ₜ` **up to the `∂ₜg` reaction**.
The content is isolated at the level of an arbitrary curve of tangent vectors:

* `raiseAt g x basis a` — the vector whose `g`-lowered components along `basis` are `a`;
* `raiseAt_lower` — the reconstruction `raiseAt g x basis (fun l => g(V, basis l)) = V`
  (this is the only place the inverse metric appears, and it is used at the **frozen**
  time `t` only, so no derivative of `g⁻¹` is ever needed);
* `vecCurve_deriv` — **the analytic core**: if the *moving*-metric lowered components
  `r ↦ g(r)(V r, basis l)` have derivatives `a l`, the metric solves `∂ₜg = −2Ric` at `x`,
  and `V` is merely *continuous* at `t`, then `V` itself is differentiable with
  `∂ₜV = g(t)♯(a + 2Ric(V t, ·))`;
* `metricRm04At_inner` — `Rm04(X,Y,Z,W) = g(Rm¹³(X,Y)Z, W)` for the own metric;
* `rmVec_deriv`, `rmVecComp_deriv` — the curvature instances: the second consumes the
  Uhlenbeck interface verbatim and produces the `(1,3)`-level `HasDerivWithinAt` with
  right-hand side the own-raise of `roughLap − 2·B-comb − Ricci drift`, plus the reaction;
* `rmDiffVec_deriv` — the endpoint: differencing the two per-flow conversions gives the
  speed of `rmDiffVec` (`ForwardUniqueRmDot.lean`), i.e. exactly the `hRm` input of
  `rmDiffLow_hasDerivAt`, with only each flow's own metric PDE and own-lowered interface.

Differentiability of the raised object is *not* assumed: it is produced.  The only extra
input beyond the interface and the metric PDE is `ContinuousWithinAt` of the `(1,3)` curve,
which is strictly weaker than the differentiability being concluded.

## Part 2 — the `∇²g₁` parallelism identities

The second half of the R4 bridge is the commutator `[g₁♭, Δ_{g₂}]`.  Its whole content is
that `∇²g₁` is *algebraic* in the connection difference.  That is proved here:

* `metricNabla0S_self` — `∇^g g = 0` at the field level (own metric, own connection);
* `nabla2_metric1` — `∇²g₁ = −(∇¹ − ∇²)g₁ = −lapDiffFlux g₁ g₂ g₁`, so the algebraicity of
  `∇²g₁` in `A₀₃` is exactly the already-proved algebraicity of `lapDiffFlux`
  (`ForwardUniqueRmBounds.lean`'s `lapDiffFlux_eval` / `fluxNormSq_le`);
* `sharpFlat`, `mixLow_eq_rm04` — the carrier mismatch identified: the `g₁`-lowered
  curvature of `g₂` is the own-lowered `Rm04₂` with its last slot precomposed by the
  re-lowering endomorphism `Φ = g₂♯ ∘ g₁♭`;
* `lapComm_eq_div_flux` — the **divergence-form organization of the commutator**: for any
  rank-indexed field-level operator `L`,
  `Δ₂(L T) − L(Δ₂ T) = div₂(F) + G`, with `F = ∇²(LT) − L(∇²T)` the first-order
  `∇`-commutator and `G = div₂(L ∇²T) − L(div₂ ∇²T)` the first-order `div`-commutator.
  Both are first-order in `L`'s Leibniz defect, i.e. `A`-algebraic × (≤ 1-derivative
  background) once `L` is the `g₁`-re-lowering.  See the companion `.md` for the status of
  the remaining step (the concrete Leibniz defect of the re-lowering operator).

Relocation TODO (protocol forbade editing existing files): `raiseAt` / `raiseAt_lower` are
generic fiber-metric algebra and belong next to `basisInvMetric` in
`Tensor/RSTensor/CotangentRiemannian.lean`; `metricNabla0S_self` belongs next to
`nabla_metric_zero` in `Tensor/RSTensor/MetricCompatibility.lean`; `mulVanish_deriv` is
generic one-variable calculus.
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
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

section Raise

variable {Idx : Type*} [Fintype Idx] {x : M}

/-- The metric `(0,2)` tensor field read in the slot-`0` convention. -/
private theorem metField0 (g : SmoothRiemannianMetric I M) (x : M)
    (u Z : TangentSpace I x) :
    metricTensorField (I := I) g x (fun i : Fin 2 => if i = 0 then u else Z) =
      g.inner x u Z := by
  rw [metricTensorField_apply]; simp

/-- Basis expansion of a metric pairing in its **first** slot. -/
private theorem inner_expand (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) (W Z : TangentSpace I x) :
    g.inner x W Z = ∑ p : Idx, basis.repr W p * g.inner x (basis p) Z := by
  classical
  rw [← metField0 (I := I) g x W Z,
    tensor02_expand (I := I) (metricTensorField (I := I) g x) basis W Z]
  exact Finset.sum_congr rfl fun p _ => by rw [metField0]

/-- **The vector with prescribed `g`-lowered components.**  `raiseAt g x basis a` is the
`g`-sharp of the covector whose values on `basis` are `a`, written in the basis through the
canonical inverse-metric components `basisInvMetric`. -/
def raiseAt (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) (a : Idx -> Real) :
    TangentSpace I x :=
  ∑ p : Idx, (∑ l : Idx, basisInvMetric (I := I) g x basis p l * a l) • basis p

theorem raiseAt_eq (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) (a : Idx -> Real) :
    raiseAt (I := I) g x basis a =
      ∑ p : Idx, (∑ l : Idx, basisInvMetric (I := I) g x basis p l * a l) • basis p := rfl

/-- **Raising undoes lowering.**  The vector whose `g`-lowered components are those of `V`
is `V` itself.  This is the only place the inverse metric enters the bridge, and it is used
at a single frozen time, so no derivative of `g⁻¹` is ever required. -/
theorem raiseAt_lower (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) (V : TangentSpace I x) :
    raiseAt (I := I) g x basis (fun l : Idx => g.inner x V (basis l)) = V := by
  classical
  have hcoord : ∀ p : Idx,
      (∑ l : Idx, basisInvMetric (I := I) g x basis p l * g.inner x V (basis l)) =
        basis.repr V p := by
    intro p
    set S : TangentSpace I x :=
      (tangentFlatEquiv_gen (I := I) g x).symm (basis.coord p) with hS
    have hb : ∀ l : Idx, basisInvMetric (I := I) g x basis p l = basis.repr S l := by
      intro l
      rw [hS]
      exact basis.coord_apply l _
    have hsum : (∑ l : Idx, basis.repr S l * g.inner x V (basis l)) = g.inner x V S := by
      conv_rhs => rw [← basis.sum_repr S]
      rw [map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul]
    have hflat : g.inner x V S = basis.repr V p := by
      have h1 : g.inner x V S = g.inner x S V := g.symm x V S
      have h2 : g.inner x S V = tangentFlatEquiv_gen (I := I) g x S V :=
        (tangentFlatEquiv_apply_gen (I := I) g x S V).symm
      have h3 : tangentFlatEquiv_gen (I := I) g x S = basis.coord p := by
        rw [hS]
        exact (tangentFlatEquiv_gen (I := I) g x).apply_symm_apply _
      rw [h1, h2, h3]
      exact basis.coord_apply p V
    calc (∑ l : Idx, basisInvMetric (I := I) g x basis p l * g.inner x V (basis l))
        = ∑ l : Idx, basis.repr S l * g.inner x V (basis l) :=
          Finset.sum_congr rfl fun l _ => by rw [hb l]
      _ = g.inner x V S := hsum
      _ = basis.repr V p := hflat
  rw [raiseAt_eq]
  calc (∑ p : Idx,
        (∑ l : Idx, basisInvMetric (I := I) g x basis p l * g.inner x V (basis l)) • basis p)
      = ∑ p : Idx, basis.repr V p • basis p :=
        Finset.sum_congr rfl fun p _ => by rw [hcoord p]
    _ = V := basis.sum_repr V

/-- Product rule when the second factor vanishes at the base point: only continuity of the
first factor is needed.  (Generic one-variable calculus; see the relocation TODO.) -/
private theorem mulVanish_deriv {f A : Real -> Real} {A' : Real} {s : Set Real} {t : Real}
    (hf : ContinuousWithinAt f s t) (hA : HasDerivWithinAt A A' s t) (hA0 : A t = 0) :
    HasDerivWithinAt (fun r : Real => f r * A r) (f t * A') s t := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at hA ⊢
  have hslope : ∀ r : Real,
      slope (fun y : Real => f y * A y) t r = f r * slope A t r := by
    intro r
    simp only [slope_def_field, hA0]
    ring
  refine Filter.Tendsto.congr (fun r => (hslope r).symm) ?_
  exact Filter.Tendsto.mul (hf.mono Set.diff_subset) hA

/-- **Own-metric raising commutes with `∂ₜ` up to the `∂ₜg` reaction.**

For a curve of tangent vectors `V` at a fixed point `x`, if

* the *moving*-metric lowered components `r ↦ g(r)(V r, basis l)` have derivatives `a l`,
* the metric family satisfies the Ricci-flow equation `∂ₜg = −2 Ric` at `x`, and
* `V` is continuous at `t` (strictly weaker than the conclusion),

then `V` is differentiable at `t` with `∂ₜV = g(t)♯(a + 2 Ric(V t, ·))`.

This is the algebraic heart of the R4 bridge: `g♯` commutes with `∂ₜ` exactly up to the
reaction created by the metric PDE. -/
theorem vecCurve_deriv
    (g : Real -> SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (V : Real -> TangentSpace I x) (a : Idx -> Real)
    (Ric : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {s : Set Real} {t : Real}
    (hcont : ContinuousWithinAt V s t)
    (hPDE : ∀ X Y : TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Ric (fun i : Fin 2 => if i = 0 then X else Y)) s t)
    (hlow : ∀ l : Idx,
      HasDerivWithinAt (fun r : Real => (g r).inner x (V r) (basis l)) (a l) s t) :
    HasDerivWithinAt V
      (raiseAt (I := I) (g t) x basis
        (fun l : Idx => a l +
          2 * Ric (fun i : Fin 2 => if i = 0 then V t else basis l))) s t := by
  classical
  -- Coefficient curves of `V` in the basis are continuous at `t`.
  have hc : ∀ p : Idx, ContinuousWithinAt (fun r : Real => basis.repr (V r) p) s t := by
    intro p
    have h := (LinearMap.toContinuousLinearMap
      (basis.coord p)).continuous.continuousAt.comp_continuousWithinAt hcont
    simpa [Function.comp_def, Module.Basis.coord_apply] using h
  -- The components lowered with the *frozen* metric `g t` differentiate.
  have hfroz : ∀ l : Idx,
      HasDerivWithinAt (fun r : Real => (g t).inner x (V r) (basis l))
        (a l + 2 * Ric (fun i : Fin 2 => if i = 0 then V t else basis l)) s t := by
    intro l
    have hsplit : ∀ r : Real,
        (g t).inner x (V r) (basis l) =
          (g r).inner x (V r) (basis l) +
            ∑ p : Idx, basis.repr (V r) p *
              ((g t).inner x (basis p) (basis l) - (g r).inner x (basis p) (basis l)) := by
      intro r
      have hd : (∑ p : Idx, basis.repr (V r) p *
            ((g t).inner x (basis p) (basis l) - (g r).inner x (basis p) (basis l))) =
          (g t).inner x (V r) (basis l) - (g r).inner x (V r) (basis l) := by
        rw [inner_expand (I := I) (g t) basis (V r) (basis l),
          inner_expand (I := I) (g r) basis (V r) (basis l), ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun p _ => by ring
      rw [hd]; ring
    have hterm : ∀ p : Idx, HasDerivWithinAt
        (fun r : Real => basis.repr (V r) p *
          ((g t).inner x (basis p) (basis l) - (g r).inner x (basis p) (basis l)))
        (basis.repr (V t) p *
          (2 * Ric (fun i : Fin 2 => if i = 0 then basis p else basis l))) s t := by
      intro p
      refine mulVanish_deriv (hc p) ?_ (sub_self _)
      have hsub := (hasDerivWithinAt_const t s
        ((g t).inner x (basis p) (basis l))).sub (hPDE (basis p) (basis l))
      exact hsub.congr_deriv (by ring)
    have hsum : HasDerivWithinAt
        (fun r : Real => ∑ p : Idx, basis.repr (V r) p *
          ((g t).inner x (basis p) (basis l) - (g r).inner x (basis p) (basis l)))
        (∑ p : Idx, basis.repr (V t) p *
          (2 * Ric (fun i : Fin 2 => if i = 0 then basis p else basis l))) s t :=
      HasDerivWithinAt.fun_sum fun p _ => hterm p
    have hval : (∑ p : Idx, basis.repr (V t) p *
          (2 * Ric (fun i : Fin 2 => if i = 0 then basis p else basis l))) =
        2 * Ric (fun i : Fin 2 => if i = 0 then V t else basis l) := by
      rw [tensor02_expand (I := I) Ric basis (V t) (basis l), Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    have hfun : (fun r : Real => (g t).inner x (V r) (basis l)) =
        (fun r : Real => (g r).inner x (V r) (basis l) +
          ∑ p : Idx, basis.repr (V r) p *
            ((g t).inner x (basis p) (basis l) - (g r).inner x (basis p) (basis l))) :=
      funext hsplit
    rw [hfun, ← hval]
    exact (hlow l).add hsum
  -- Reassemble the vector from its frozen-metric components.
  have hV : ∀ r : Real,
      V r = ∑ p : Idx, (∑ l : Idx, basisInvMetric (I := I) (g t) x basis p l *
        ((g t).inner x (V r) (basis l))) • basis p := by
    intro r
    have h := raiseAt_lower (I := I) (g t) x basis (V r)
    rw [raiseAt_eq] at h
    exact h.symm
  have hderiv : HasDerivWithinAt
      (fun r : Real => ∑ p : Idx, (∑ l : Idx, basisInvMetric (I := I) (g t) x basis p l *
          ((g t).inner x (V r) (basis l))) • basis p)
      (∑ p : Idx, (∑ l : Idx, basisInvMetric (I := I) (g t) x basis p l *
          (a l + 2 * Ric (fun i : Fin 2 => if i = 0 then V t else basis l))) • basis p) s t :=
    HasDerivWithinAt.fun_sum fun p _ =>
      (HasDerivWithinAt.fun_sum fun l _ => (hfroz l).const_mul _).smul_const (basis p)
  rw [raiseAt_eq]
  exact hderiv.congr (fun y _ => hV y) (hV t)

end Raise

section Curvature

variable {Idx : Type*} [Fintype Idx] {x : M}

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Own-metric lowering of the canonical curvature operator**: the `(0,4)` curvature
tensor of `g` is the `g`-pairing of the bundled `(1,3)` operator `riemannOp (metricCov g)`
with the last slot. -/
theorem metricRm04At_inner (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    metricRm04At (I := I) g x
        (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W) =
      g.inner x
        (DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) g) x X Y Z)
        W := by
  have h :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At_apply_const
      (I := I) g (metricCov (I := I) g) (metricCov_smooth (I := I) g) X Y Z W
  rw [DifferentialGeometry.riemannCurvatureAux_tangentConst_eq_riemannOp
    (I := I) (metricCov (I := I) g) (metricCov_smooth (I := I) g) x X Y Z] at h
  rw [show metricRm04At (I := I) g x =
      DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
        (I := I) g (metricCov (I := I) g) (metricCov_smooth (I := I) g) x from rfl, h]
  exact g.symm x W _

set_option synthInstance.maxHeartbeats 1000000 in
/-- **R4 bridge, Part 1 (invariant form).**  The own-lowered `(0,4)` evolution of one flow
converts, algebraically, into the `(1,3)`-level evolution of `riemannOp (metricCov g)`: the
speed is the own-raise of the `(0,4)` speed plus the `∂ₜg = −2Ric` reaction. -/
theorem rmVec_deriv
    (g : Real -> SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (X Y Z : TangentSpace I x) (rhs : Idx -> Real)
    (Ric : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {s : Set Real} {t : Real}
    (hcont : ContinuousWithinAt
      (fun r : Real =>
        DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) (g r)) x X Y Z)
      s t)
    (hPDE : ∀ U W : TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (g r).inner x U W)
        ((-2 : Real) * Ric (fun i : Fin 2 => if i = 0 then U else W)) s t)
    (hev : ∀ l : Idx,
      HasDerivWithinAt
        (fun r : Real => metricRm04At (I := I) (g r) x
          (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z (basis l)))
        (rhs l) s t) :
    HasDerivWithinAt
      (fun r : Real =>
        DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) (g r)) x X Y Z)
      (raiseAt (I := I) (g t) x basis
        (fun l : Idx => rhs l +
          2 * Ric (fun i : Fin 2 => if i = 0 then
            DifferentialGeometry.Integral.Connection.riemannOp
              (metricCov (I := I) (g t)) x X Y Z
            else basis l))) s t := by
  refine vecCurve_deriv (I := I) g basis _ rhs Ric hcont hPDE ?_
  intro l
  have h := hev l
  simpa only [metricRm04At_inner (I := I)] using h

set_option synthInstance.maxHeartbeats 1000000 in
/-- **R4 bridge, Part 1 at the interface.**  The repo's own per-flow curvature-evolution
interface `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` (`Evolution/Uhlenbeck.lean`),
whose component family is the *own-metric-lowered* curvature (`hreal`), converts into the
`(1,3)`-level evolution of `riemannOp (metricCov g)`: the speed of the raised curvature is
the own-raise of `roughLap − 2·B-comb − Ricci drift`, plus the `∂ₜg = −2Ric` reaction.

This is the per-flow half of ruling R4: no cross-metric lowering appears, and the two flows'
`(1,3)` speeds may now be subtracted to feed `rmDiffLow_hasDerivAt`'s `hRm` (whose object
`rmDiffVec` is exactly the difference of the two `riemannOp`s). -/
theorem rmVecComp_deriv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (g : Real -> SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 roughLapRm04 B : FourComp M Idx) (ricciOneUp : MatrixComp M Idx)
    (Ric : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hev : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D)
      Rm04 roughLapRm04 B ricciOneUp)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (i j k : Idx)
    (hcont : ContinuousWithinAt
      (fun r : Real =>
        DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) (g r)) x
          (basis i) (basis j) (basis k))
      D.carrier (t : Real))
    (hPDE : ∀ U W : TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (g r).inner x U W)
        ((-2 : Real) * Ric (fun q : Fin 2 => if q = 0 then U else W))
        D.carrier (t : Real))
    (hreal : ∀ (r : Real) (l : Idx),
      Rm04 r x i j k l =
        metricRm04At (I := I) (g r) x
          (DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (basis i) (basis j) (basis k) (basis l))) :
    HasDerivWithinAt
      (fun r : Real =>
        DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) (g r)) x
          (basis i) (basis j) (basis k))
      (raiseAt (I := I) (g (t : Real)) x basis
        (fun l : Idx =>
          (roughLapRm04 (t : Real) x i j k l -
              2 * (B (t : Real) x i j k l - B (t : Real) x i j l k +
                B (t : Real) x i k j l - B (t : Real) x i l j k) -
              riemann04RicciDriftInFrame ricciOneUp Rm04 (t : Real) x i j k l) +
            2 * Ric (fun q : Fin 2 => if q = 0 then
              DifferentialGeometry.Integral.Connection.riemannOp
                (metricCov (I := I) (g (t : Real))) x (basis i) (basis j) (basis k)
              else basis l)))
      D.carrier (t : Real) := by
  refine rmVec_deriv (I := I) g basis (basis i) (basis j) (basis k) _ Ric hcont hPDE ?_
  intro l
  have h := hev t x i j k l
  have hfun : (fun r : Real => Rm04 r x i j k l) =
      (fun r : Real => metricRm04At (I := I) (g r) x
        (DifferentialGeometry.Integral.Connection.vec4 (I := I)
          (basis i) (basis j) (basis k) (basis l))) :=
    funext fun r => hreal r l
  rw [hfun] at h
  exact h

set_option synthInstance.maxHeartbeats 1000000 in
/-- **R4 bridge, Part 1 endpoint: the `(1,3)` difference speed.**

Differencing the two per-flow conversions produces the derivative of `rmDiffVec` — the
`(1,3)` curvature difference of `ForwardUniqueRmDot.lean` — which is exactly the `hRm` input
of `rmDiffLow_hasDerivAt`, hence (after that adapter) K3's `hS`.  Each flow contributes only
its **own** metric PDE and its **own**-lowered `(0,4)` evolution: no cross-metric lowering
appears anywhere, which is the point of ruling R4. -/
theorem rmDiffVec_deriv
    (g₁ g₂ : Real -> SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (X Y Z : TangentSpace I x) (rhs₁ rhs₂ : Idx -> Real)
    (Ric₁ Ric₂ : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {s : Set Real} {t : Real}
    (hcont₁ : ContinuousWithinAt
      (fun r : Real =>
        DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) (g₁ r)) x X Y Z)
      s t)
    (hcont₂ : ContinuousWithinAt
      (fun r : Real =>
        DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) (g₂ r)) x X Y Z)
      s t)
    (hPDE₁ : ∀ U W : TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (g₁ r).inner x U W)
        ((-2 : Real) * Ric₁ (fun q : Fin 2 => if q = 0 then U else W)) s t)
    (hPDE₂ : ∀ U W : TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (g₂ r).inner x U W)
        ((-2 : Real) * Ric₂ (fun q : Fin 2 => if q = 0 then U else W)) s t)
    (hev₁ : ∀ l : Idx,
      HasDerivWithinAt
        (fun r : Real => metricRm04At (I := I) (g₁ r) x
          (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z (basis l)))
        (rhs₁ l) s t)
    (hev₂ : ∀ l : Idx,
      HasDerivWithinAt
        (fun r : Real => metricRm04At (I := I) (g₂ r) x
          (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z (basis l)))
        (rhs₂ l) s t) :
    HasDerivWithinAt (fun r : Real => rmDiffVec (I := I) (g₁ r) (g₂ r) x X Y Z)
      (raiseAt (I := I) (g₁ t) x basis
          (fun l : Idx => rhs₁ l +
            2 * Ric₁ (fun q : Fin 2 => if q = 0 then
              DifferentialGeometry.Integral.Connection.riemannOp
                (metricCov (I := I) (g₁ t)) x X Y Z
              else basis l)) -
        raiseAt (I := I) (g₂ t) x basis
          (fun l : Idx => rhs₂ l +
            2 * Ric₂ (fun q : Fin 2 => if q = 0 then
              DifferentialGeometry.Integral.Connection.riemannOp
                (metricCov (I := I) (g₂ t)) x X Y Z
              else basis l))) s t := by
  have hfun : (fun r : Real => rmDiffVec (I := I) (g₁ r) (g₂ r) x X Y Z) =
      (fun r : Real =>
        DifferentialGeometry.Integral.Connection.riemannOp
            (metricCov (I := I) (g₁ r)) x X Y Z -
          DifferentialGeometry.Integral.Connection.riemannOp
            (metricCov (I := I) (g₂ r)) x X Y Z) := rfl
  rw [hfun]
  exact (rmVec_deriv (I := I) g₁ basis X Y Z rhs₁ Ric₁ hcont₁ hPDE₁ hev₁).sub
    (rmVec_deriv (I := I) g₂ basis X Y Z rhs₂ Ric₂ hcont₂ hPDE₂ hev₂)

end Curvature

section Parallel

/-- **`∇^g g = 0` at the field level.**  The metric `(0,2)` tensor field is parallel for its
own Levi-Civita connection.  (Field-level form of `nabla_metric_zero`; see the relocation
TODO.) -/
theorem metricNabla0S_self (g : SmoothRiemannianMetric I M) :
    metricNabla0S (I := I) g (metricTensorField (I := I) g) =
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3) := by
  classical
  have hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen
      (I := I) (metricCov (I := I) g) g :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) g
  refine DFunLike.ext _ _ fun x => ?_
  have hfib : metricNabla0S (I := I) g (metricTensorField (I := I) g) x = 0 := by
    refine ContinuousMultilinearMap.ext fun v => ?_
    obtain ⟨Xsec, hXx⟩ :=
      ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v 0)
    have hv : Fin.cons (Xsec x) (Fin.tail v) = v := by
      rw [hXx]
      exact Fin.cons_self_tail v
    have hsec := totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (metricCov (I := I) g) Xsec (metricTensorField (I := I) g) x
      (Fin.tail v)
    rw [hv] at hsec
    have hzero := nabla_metric_zero (I := I) (metricCov (I := I) g) g hmc Xsec x
    rw [metricNabla0S_apply, hsec, hzero]
    simp
  rw [hfib]
  rfl

/-- **`∇²g₁ = −(∇¹ − ∇²)g₁`**, the R4 algebraicity identity: the covariant derivative of the
*other* metric is minus the connection-difference flux applied to it.  Since
`lapDiffFlux g₁ g₂ T = ∇¹T − ∇²T` is the algebraic action of the connection difference `A₀₃`
on `T` (`ForwardUniqueRmDiff.lean`, with the quantitative form
`lapDiffFlux_eval`/`fluxNormSq_le` in `ForwardUniqueRmBounds.lean`), this says exactly that
`∇²g₁` is `A₀₃`-algebraic — no derivative of the metric difference appears. -/
theorem nabla2_metric1 (g₁ g₂ : SmoothRiemannianMetric I M) :
    metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁) =
      -lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁) := by
  rw [lapDiffFlux, metricNabla0S_self]
  abel

end Parallel

section ReLower

variable {x : M}

/-- **The re-lowering endomorphism `Φ = g₂♯ ∘ g₁♭`.**  Precomposing the last slot of the
own-`g₂`-lowered curvature with `Φ` produces the `g₁`-lowered representative — this is the
exact bookkeeping of the R4 carrier mismatch. -/
def sharpFlat (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[Real] TangentSpace I x :=
  (tangentFlatEquiv_gen (I := I) g₂ x).symm.toLinearMap ∘ₗ
    (tangentFlatEquiv_gen (I := I) g₁ x).toLinearMap

/-- Equal metrics give the identity re-lowering. -/
@[simp]
theorem sharpFlat_self (g : SmoothRiemannianMetric I M) (x : M) (W : TangentSpace I x) :
    sharpFlat (I := I) g g x W = W := by
  change (tangentFlatEquiv_gen (I := I) g x).symm
    ((tangentFlatEquiv_gen (I := I) g x) W) = W
  exact (tangentFlatEquiv_gen (I := I) g x).symm_apply_apply W

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The R4 carrier mismatch, identified.**  The `g₁`-lowered Riemann tensor of `g₂` — the
background field `T₂` of the Kotschwar organization, which the honest Uhlenbeck interface
does *not* describe — is the own-lowered `Rm04₂` with its last slot precomposed by the
re-lowering endomorphism `Φ = g₂♯ ∘ g₁♭`.

Consequently the outstanding half of the R4 bridge is exactly the Leibniz defect of that
last-slot precomposition, i.e. `∇²Φ`, which `nabla2_metric1` shows is `A₀₃`-algebraic. -/
theorem mixLow_eq_rm04 (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    metricRm04At (I := I) g₂ x
        (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z
          (sharpFlat (I := I) g₁ g₂ x W)) =
      g₁.inner x
        (DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) g₂) x X Y Z)
        W := by
  set V : TangentSpace I x :=
    DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) g₂) x X Y Z with hV
  set S : TangentSpace I x := sharpFlat (I := I) g₁ g₂ x W with hSdef
  have hflat : tangentFlatEquiv_gen (I := I) g₂ x S = tangentFlatEquiv_gen (I := I) g₁ x W := by
    rw [hSdef]
    change tangentFlatEquiv_gen (I := I) g₂ x
      ((tangentFlatEquiv_gen (I := I) g₂ x).symm
        ((tangentFlatEquiv_gen (I := I) g₁ x) W)) = _
    exact (tangentFlatEquiv_gen (I := I) g₂ x).apply_symm_apply _
  calc metricRm04At (I := I) g₂ x
        (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z S)
      = g₂.inner x V S := metricRm04At_inner (I := I) g₂ x X Y Z S
    _ = g₂.inner x S V := g₂.symm x V S
    _ = tangentFlatEquiv_gen (I := I) g₂ x S V :=
        (tangentFlatEquiv_apply_gen (I := I) g₂ x S V).symm
    _ = tangentFlatEquiv_gen (I := I) g₁ x W V := by rw [hflat]
    _ = g₁.inner x W V := tangentFlatEquiv_apply_gen (I := I) g₁ x W V
    _ = g₁.inner x V W := g₁.symm x W V

end ReLower

section Commutator

variable {s : ℕ}

/-- **First-order `∇`-commutator (the commutator flux).**  For a rank-indexed field operator
`L`, this is the Leibniz defect `∇^g(L T) − L(∇^g T)` — a `(0,s+1)` field carrying **no**
second derivative of anything.  For the R4 re-lowering (`mixLow_eq_rm04`) it is the
`∇²g₁`-action, hence `A₀₃`-algebraic by `nabla2_metric1`. -/
def lapCommFlux (g : SmoothRiemannianMetric I M)
    (L : ∀ k : ℕ, Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  metricNabla0S (I := I) g (L s T) - L (s + 1) (metricNabla0S (I := I) g T)

/-- **First-order `div`-commutator (the commutator remainder).**  The Leibniz defect of `L`
against the divergence, evaluated on the *background* field `∇^g T`: it carries at most one
covariant derivative of the background and no derivative of the difference carrier. -/
def lapCommRem (g : SmoothRiemannianMetric I M)
    (L : ∀ k : ℕ, Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
  covDiv0SField (I := I) g (L (s + 1) (metricNabla0S (I := I) g T)) -
    L s (covDiv0SField (I := I) g (metricNabla0S (I := I) g T))

/-- **Divergence-form organization of a `[L, Δ_g]` commutator** (R4, second half — structural
half).  For any rank-indexed field operator `L`,

```
Δ_g(L T) − L(Δ_g T) = div_g(lapCommFlux) + lapCommRem,
```

where both `lapCommFlux` and `lapCommRem` are **first-order** Leibniz defects of `L`: the
flux differentiates `T` once, the remainder acts on the once-differentiated background.  No
second derivative of `L`'s defect and no derivative of the difference carrier appears, which
is precisely the divergence-form property ruling R4 asked for.  Structurally identical to
`lapDiff_eq_div_flux` (K2.3): the identity is the regrouping, and the mathematical content
is the algebraicity of the two defects, which for the R4 re-lowering is `nabla2_metric1`. -/
theorem lapComm_eq_div_flux (g : SmoothRiemannianMetric I M)
    (L : ∀ k : ℕ, Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    roughLap0SField (I := I) g (L s T) - L s (roughLap0SField (I := I) g T) =
      covDiv0SField (I := I) g (lapCommFlux (I := I) g L T) +
        lapCommRem (I := I) g L T := by
  rw [lapCommFlux, covDiv0SField_sub, lapCommRem, roughLap0SField, roughLap0SField]
  abel

/-- A field operator with vanishing first-order defects commutes with the rough Laplacian.
The non-vacuity check for the organization above: both carriers vanish exactly when `L` is
`∇`- and `div`-parallel. -/
theorem lapComm_self (g : SmoothRiemannianMetric I M)
    (L : ∀ k : ℕ, Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hflux : lapCommFlux (I := I) g L T = 0) (hrem : lapCommRem (I := I) g L T = 0) :
    roughLap0SField (I := I) g (L s T) = L s (roughLap0SField (I := I) g T) := by
  have h := lapComm_eq_div_flux (I := I) g L T
  rw [hflux, hrem, add_zero] at h
  have hz : covDiv0SField (I := I) g
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1)) = 0 := by
    have := covDiv0SField_sub (I := I) g
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1)) 0
    simpa using this
  rw [hz] at h
  exact sub_eq_zero.mp h

end Commutator

end DifferentialGeometry.PDE.RicciFlow

end
