import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRmBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.TailChristoffel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ExtendedSolutionRegularity

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option backward.isDefEq.respectTransparency false

/-!
# Frame → invariant lifts for the forward-uniqueness endgame (Route-K brick K6b)

`Evolution/ForwardUniqueAssembly.lean` (K6a) reduced black box (B) to one standing bundle
`ForwardUniqueInputs`.  Two of its members were flagged **missing-API**, not missing
mathematics: the producers exist, but their conclusions are stated *componentwise in a frame*
while the bundle wants an *invariant bundled speed*.  This file supplies the rank-3 lift and
uses it to collapse the `rm` member.

## The lift

`ForwardUniqueConnDot.lean` already has the rank-2 template: `bilinOfComp` packages a
component family `c i j k` into a continuous bilinear vector-valued map, and
`coeff_bilinOfComp` reads the components back.  Here the same construction is done one rank
up (`quadOfComp`, four indices: three inputs and one output), together with the trilinear
basis expansion `tri_expand` that turns basis-triple derivative facts into derivative facts
at *arbitrary* tangent vectors.

## Main definitions

* `quadOfComp b c` — the continuous trilinear vector-valued map with prescribed basis
  components, `quadOfComp b c (b i) (b j) (b k) = ∑ l, c i j k l • b l`.
* `uhlRaisedDeriv g basisAt Rm04 roughLapRm04 B ricciOneUp t y i j k` — the raised time
  derivative of one flow's `(1,3)` curvature at a basis triple, i.e. the right-hand side that
  `rmVecComp_deriv` (`ForwardUniqueRmBridge.lean`) produces from that flow's own-lowered
  Uhlenbeck interface.
* `uhlRmDiffSpeed` — the bundled trilinear speed `Svec` of the curvature difference: the
  `quadOfComp` package of the difference of the two `uhlRaisedDeriv` families.

## Main results

* `tri_expand` — trilinear expansion of a `TangentSpace →L →L →L TangentSpace` map in a basis.
* `quadOfComp_basis`, `coeff_quadOfComp`, `quadOfComp_vec` — the component/coefficient
  read-back lemmas, mirroring `bilinOfComp_basis` / `coeff_bilinOfComp`.
* `rmDiffVec_hasDerivAt_of_basis` — **the lift**: basis-triple derivatives of the raised
  curvature difference give the derivative at every `(X, Y, Z)`, with the invariant speed.
* `rm_of_uhlenbeck` — **the collapse**: the `rm` member of
  `ForwardUniqueAssembly.ForwardUniqueInputs`, verbatim, from the two per-flow own-lowered
  Uhlenbeck interfaces, the two per-flow Ricci-flow equations, and the two (benign)
  realization/continuity inputs that `rmVecComp_deriv` already requires.

## Relocation TODO

`tri_expand`, `quadOfComp` and its read-back lemmas are generic fiber algebra whose canonical
home is next to `bilin_expand` / `bilinOfComp`; they live here only because the brick protocol
forbids editing existing files.  Move them when `ForwardUniqueConnDot.lean` is next touched.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators Topology

/-! ## Part 1: the rank-3 lift and the `rm` collapse

This part is `NormedSpace`-only, matching `ForwardUniqueRmDot.lean` /
`ForwardUniqueRmBridge.lean`; the `gamma` part below needs the `InnerProductSpace` context of
`ForwardUniqueAssembly.lean` and therefore opens its own section rather than mixing the two
`NormedSpace ℝ E` instance paths. -/

section NormedBase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

section Quad

variable {Idx : Type*} [Fintype Idx] {u : Set M} {x : M}

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Trilinear basis expansion.**  The rank-3 analogue of `bilin_expand`: a continuous
trilinear vector-valued map is determined by its values on basis triples. -/
theorem tri_expand {ι : Type*} [Fintype ι]
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    (b : Module.Basis ι Real (TangentSpace I x)) (X Y Z : TangentSpace I x) :
    ((A X) Y) Z =
      ∑ i, ∑ j, ∑ k, (b.repr X i * b.repr Y j * b.repr Z k) • ((A (b i)) (b j)) (b k) := by
  classical
  have hX : (∑ i, b.repr X i • b i) = X := b.sum_repr X
  have hY : (∑ j, b.repr Y j • b j) = Y := b.sum_repr Y
  have hZ : (∑ k, b.repr Z k • b k) = Z := b.sum_repr Z
  have step1 : ((A X) Y) Z = ∑ i, b.repr X i • (((A (b i)) Y) Z) := by
    conv_lhs => rw [← hX]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply]
  have step2 : ∀ i : ι, ((A (b i)) Y) Z = ∑ j, b.repr Y j • (((A (b i)) (b j)) Z) := by
    intro i
    conv_lhs => rw [← hY]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply]
  have step3 : ∀ i j : ι, ((A (b i)) (b j)) Z =
      ∑ k, b.repr Z k • (((A (b i)) (b j)) (b k)) := by
    intro i j
    conv_lhs => rw [← hZ]
    simp only [map_sum, map_smul]
  rw [step1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [step2 i, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [step3 i j, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, smul_smul]

set_option synthInstance.maxHeartbeats 1000000 in
/-- The continuous trilinear vector-valued map with prescribed basis components:
`quadOfComp b c (b i) (b j) (b k) = ∑ l, c i j k l • b l`.  This is the rank-3 analogue of
`bilinOfComp`; it turns a *componentwise* curvature-difference speed into the invariant
trilinear speed `Svec` that the forward-uniqueness bundle consumes. -/
def quadOfComp (b : Module.Basis Idx Real (TangentSpace I x))
    (c : Idx -> Idx -> Idx -> Idx -> Real) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    (b.constr Real fun i =>
      LinearMap.toContinuousLinearMap
        (b.constr Real fun j =>
          LinearMap.toContinuousLinearMap (b.constr Real fun k => ∑ l, c i j k l • b l)))

set_option synthInstance.maxHeartbeats 1000000 in
@[simp]
theorem quadOfComp_basis (b : Module.Basis Idx Real (TangentSpace I x))
    (c : Idx -> Idx -> Idx -> Idx -> Real) (i j k : Idx) :
    ((quadOfComp (I := I) b c (b i)) (b j)) (b k) = ∑ l, c i j k l • b l := by
  have h1 : quadOfComp (I := I) b c (b i) =
      LinearMap.toContinuousLinearMap
        (b.constr Real fun j =>
          LinearMap.toContinuousLinearMap (b.constr Real fun k => ∑ l, c i j k l • b l)) := by
    change (b.constr Real fun i' =>
      LinearMap.toContinuousLinearMap
        (b.constr Real fun j =>
          LinearMap.toContinuousLinearMap
            (b.constr Real fun k => ∑ l, c i' j k l • b l))) (b i) = _
    rw [Module.Basis.constr_basis]
  rw [h1]
  have h2 : (LinearMap.toContinuousLinearMap
      (b.constr Real fun j' =>
        LinearMap.toContinuousLinearMap
          (b.constr Real fun k => ∑ l, c i j' k l • b l)) : TangentSpace I x →L[Real] _) (b j) =
      LinearMap.toContinuousLinearMap (b.constr Real fun k => ∑ l, c i j k l • b l) := by
    change (b.constr Real fun j' =>
      LinearMap.toContinuousLinearMap
        (b.constr Real fun k => ∑ l, c i j' k l • b l)) (b j) = _
    rw [Module.Basis.constr_basis]
  rw [h2]
  change (b.constr Real fun k' => ∑ l, c i j k' l • b l) (b k) = _
  rw [Module.Basis.constr_basis]

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Prescribed vector values.**  Feeding `quadOfComp` the basis coordinates of a vector
family reproduces that family at basis triples.  This is the form the collapse lemma uses:
the producer supplies vectors, not components. -/
theorem quadOfComp_vec (b : Module.Basis Idx Real (TangentSpace I x))
    (V : Idx -> Idx -> Idx -> TangentSpace I x) (i j k : Idx) :
    ((quadOfComp (I := I) b (fun i j k l => b.repr (V i j k) l) (b i)) (b j)) (b k) =
      V i j k := by
  rw [quadOfComp_basis]
  exact b.sum_repr (V i j k)

set_option synthInstance.maxHeartbeats 1000000 in
/-- The frame coefficients of `quadOfComp` are the prescribed components: the rank-3
analogue of `coeff_bilinOfComp`. -/
theorem coeff_quadOfComp (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u) (hx : x ∈ u)
    (c : Idx -> Idx -> Idx -> Idx -> Real) (i j k l : Idx) :
    hframe.coeff l x
        (((quadOfComp (I := I) (hframe.toBasisAt hx) c (frame i x)) (frame j x))
          (frame k x)) =
      c i j k l := by
  classical
  set b : Module.Basis Idx Real (TangentSpace I x) := hframe.toBasisAt hx with hbdef
  have hbcoe : ∀ m : Idx, b m = frame m x := fun m =>
    IsLocalFrameOn.toBasisAt_coe hframe hx m
  have hcoeff : ∀ (m : Idx) (w : TangentSpace I x),
      hframe.coeff m x w = b.repr w m := by
    intro m w
    simp [IsLocalFrameOn.coeff, hx, hbdef, Module.Basis.coord_apply]
  rw [← hbcoe i, ← hbcoe j, ← hbcoe k, hcoeff l, quadOfComp_basis]
  simp [Finsupp.single_apply]

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The frame → invariant lift for the curvature-difference speed.**

If the raised curvature difference `Rm¹ − Rm²` has, at every basis triple, the time
derivative prescribed by the trilinear map `Sdot`, then it has that derivative at *every*
triple of tangent vectors.  This is exactly the `hRm` hypothesis of `rmDiffLow_hasDerivAt`
(hence, through `rmSpeed_hasDerivAt`, K3's `hS`).

The rank-2 analogue is `connDiffVec_hasDerivAt`; here the producer already supplies
vector-valued facts, so no coefficient bookkeeping is needed. -/
theorem rmDiffVec_hasDerivAt_of_basis
    (g₁ g₂ : Real -> SmoothRiemannianMetric I M)
    (b : Module.Basis Idx Real (TangentSpace I x))
    (Sdot : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    {t : Real}
    (hbasis : ∀ i j k : Idx,
      HasDerivAt (fun r : Real => ((rmDiffVec (I := I) (g₁ r) (g₂ r) x (b i)) (b j)) (b k))
        (((Sdot (b i)) (b j)) (b k)) t)
    (X Y Z : TangentSpace I x) :
    HasDerivAt (fun r : Real => ((rmDiffVec (I := I) (g₁ r) (g₂ r) x X) Y) Z)
      (((Sdot X) Y) Z) t := by
  classical
  have hexp : ∀ r : Real,
      ((rmDiffVec (I := I) (g₁ r) (g₂ r) x X) Y) Z =
        ∑ i, ∑ j, ∑ k, (b.repr X i * b.repr Y j * b.repr Z k) •
          ((rmDiffVec (I := I) (g₁ r) (g₂ r) x (b i)) (b j)) (b k) := fun r =>
    tri_expand (I := I) _ b X Y Z
  have htgt : ((Sdot X) Y) Z =
      ∑ i, ∑ j, ∑ k, (b.repr X i * b.repr Y j * b.repr Z k) • ((Sdot (b i)) (b j)) (b k) :=
    tri_expand (I := I) Sdot b X Y Z
  rw [htgt]
  have hstep : HasDerivAt
      (fun r : Real =>
        ∑ i, ∑ j, ∑ k, (b.repr X i * b.repr Y j * b.repr Z k) •
          ((rmDiffVec (I := I) (g₁ r) (g₂ r) x (b i)) (b j)) (b k))
      (∑ i, ∑ j, ∑ k, (b.repr X i * b.repr Y j * b.repr Z k) •
        ((Sdot (b i)) (b j)) (b k)) t :=
    HasDerivAt.fun_sum fun i _ =>
      HasDerivAt.fun_sum fun j _ =>
        HasDerivAt.fun_sum fun k _ => (hbasis i j k).const_smul _
  simpa only [← hexp] using hstep

end Quad

section Collapse

variable {Idx : Type*} [Fintype Idx]

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The raised curvature speed of one flow at a basis triple.**

This is the right-hand side that `rmVecComp_deriv` produces from that flow's own-lowered
Uhlenbeck interface `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`: the own-metric raise
of `roughLap − 2·(B-combination) − Ricci drift`, plus the reaction created by the moving
lowering metric `∂ₜg = −2Ric`. -/
def uhlRaisedDeriv (g : Real -> SmoothRiemannianMetric I M)
    (basisAt : (y : M) -> Module.Basis Idx Real (TangentSpace I y))
    (Rm04 roughLapRm04 B : FourComp M Idx) (ricciOneUp : MatrixComp M Idx)
    (t : Real) (y : M) (i j k : Idx) : TangentSpace I y :=
  raiseAt (I := I) (g t) y (basisAt y)
    (fun l : Idx =>
      (roughLapRm04 t y i j k l -
          2 * (B t y i j k l - B t y i j l k + B t y i k j l - B t y i l j k) -
          riemann04RicciDriftInFrame ricciOneUp Rm04 t y i j k l) +
        2 * metricRicciAt (I := I) (g t) y
          (fun q : Fin 2 => if q = 0 then
            DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) (g t)) y
              (basisAt y i) (basisAt y j) (basisAt y k)
            else basisAt y l))

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The bundled trilinear speed `Svec` of the curvature difference.**

The `quadOfComp` package of the difference of the two per-flow raised speeds.  This is the
data carrier that `ForwardUniqueAssembly.ForwardUniqueInputs` takes as `Svec`, and
`rm_of_uhlenbeck` proves it satisfies the bundle's `rm` member. -/
def uhlRmDiffSpeed (g₁ g₂ : Real -> SmoothRiemannianMetric I M)
    (basisAt : (y : M) -> Module.Basis Idx Real (TangentSpace I y))
    (Rm04₁ roughLapRm04₁ B₁ : FourComp M Idx) (ricciOneUp₁ : MatrixComp M Idx)
    (Rm04₂ roughLapRm04₂ B₂ : FourComp M Idx) (ricciOneUp₂ : MatrixComp M Idx)
    (t : Real) (y : M) :
    TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y →L[Real]
      TangentSpace I y :=
  quadOfComp (I := I) (basisAt y)
    (fun i j k l =>
      (basisAt y).repr
        (uhlRaisedDeriv (I := I) g₁ basisAt Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁ t y i j k -
          uhlRaisedDeriv (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t y i j k) l)

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **K6b collapse of the bundle's `rm` member.**

The `rm` field of `ForwardUniqueAssembly.ForwardUniqueInputs`, verbatim, produced from:

* the two per-flow **own-lowered** Uhlenbeck interfaces `hev₁`, `hev₂`
  (`Riemann04BTensorWithRicciDriftEvolutionInFrameOn`, `Evolution/Uhlenbeck.lean`) — the
  standing inputs of planner ruling R1;
* the two per-flow Ricci-flow equations `hPDE₁`, `hPDE₂` in the lane's `metricRicciAt`
  currency, one-sided within the interval carrier;
* the two realization inputs `hreal₁`, `hreal₂` saying which curvature the supplied
  component families are (each flow's **own** lowering — no cross-metric lowering appears);
* the two continuity inputs `hcont₁`, `hcont₂`, strictly weaker than the differentiability
  concluded.

The speed is not assumed: it is the constructed `uhlRmDiffSpeed`.  Every hypothesis is
per-flow, matching ruling R4. -/
theorem rm_of_uhlenbeck
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (g₁ g₂ : Real -> SmoothRiemannianMetric I M)
    (basisAt : (y : M) -> Module.Basis Idx Real (TangentSpace I y))
    (Rm04₁ roughLapRm04₁ B₁ : FourComp M Idx) (ricciOneUp₁ : MatrixComp M Idx)
    (Rm04₂ roughLapRm04₂ B₂ : FourComp M Idx) (ricciOneUp₂ : MatrixComp M Idx)
    {a b : Real} (hreg : Set.Ioo a b ⊆ D.regular)
    (hev₁ : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D)
      Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁)
    (hev₂ : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D)
      Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂)
    (hreal₁ : ∀ (r : Real) (y : M) (i j k l : Idx),
      Rm04₁ r y i j k l =
        metricRm04At (I := I) (g₁ r) y
          (DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (basisAt y i) (basisAt y j) (basisAt y k) (basisAt y l)))
    (hreal₂ : ∀ (r : Real) (y : M) (i j k l : Idx),
      Rm04₂ r y i j k l =
        metricRm04At (I := I) (g₂ r) y
          (DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (basisAt y i) (basisAt y j) (basisAt y k) (basisAt y l)))
    (hcont₁ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (i j k : Idx),
      ContinuousWithinAt
        (fun r : Real =>
          DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) (g₁ r)) y
            (basisAt y i) (basisAt y j) (basisAt y k))
        D.carrier t)
    (hcont₂ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (i j k : Idx),
      ContinuousWithinAt
        (fun r : Real =>
          DifferentialGeometry.Integral.Connection.riemannOp (metricCov (I := I) (g₂ r)) y
            (basisAt y i) (basisAt y j) (basisAt y k))
        D.carrier t)
    (hPDE₁ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (U W : TangentSpace I y),
      HasDerivWithinAt (fun r : Real => (g₁ r).inner y U W)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) y
          (fun q : Fin 2 => if q = 0 then U else W)) D.carrier t)
    (hPDE₂ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (U W : TangentSpace I y),
      HasDerivWithinAt (fun r : Real => (g₂ r).inner y U W)
        ((-2 : Real) * metricRicciAt (I := I) (g₂ t) y
          (fun q : Fin 2 => if q = 0 then U else W)) D.carrier t) :
    ∀ t ∈ Set.Ioo a b, ∀ (y : M) (X Y Z : TangentSpace I y),
      HasDerivAt (fun r : Real => ((rmDiffVec (I := I) (g₁ r) (g₂ r) y X) Y) Z)
        (((uhlRmDiffSpeed (I := I) g₁ g₂ basisAt Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁
            Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t y X) Y) Z) t := by
  intro t ht y X Y Z
  have hnhds : D.carrier ∈ 𝓝 t := D.regular_mem_nhds (hreg ht)
  refine rmDiffVec_hasDerivAt_of_basis (I := I) g₁ g₂ (basisAt y) _ ?_ X Y Z
  intro i j k
  have hval :
      ((uhlRmDiffSpeed (I := I) g₁ g₂ basisAt Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁
          Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t y (basisAt y i)) (basisAt y j)) (basisAt y k) =
        uhlRaisedDeriv (I := I) g₁ basisAt Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁ t y i j k -
          uhlRaisedDeriv (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t y i j k :=
    quadOfComp_vec (I := I) (basisAt y) _ i j k
  rw [hval]
  have h₁ := rmVecComp_deriv (I := I) (D := D) g₁ (basisAt y)
    Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁ (metricRicciAt (I := I) (g₁ t) y) hev₁
    ⟨t, hreg ht⟩ i j k (hcont₁ t ht y i j k) (hPDE₁ t ht y) (fun r l => hreal₁ r y i j k l)
  have h₂ := rmVecComp_deriv (I := I) (D := D) g₂ (basisAt y)
    Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ (metricRicciAt (I := I) (g₂ t) y) hev₂
    ⟨t, hreg ht⟩ i j k (hcont₂ t ht y i j k) (hPDE₂ t ht y) (fun r l => hreal₂ r y i j k l)
  have hsub := (h₁.sub h₂).hasDerivAt hnhds
  exact hsub

end Collapse

end NormedBase

section Gamma

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]

/-! ## Part 2: the `SolutionOn`-package bridge and the `gamma` collapse

`ForwardUniqueConnectionDiff.lean` (K1) states the Christoffel-difference evolution for a pair
of `SolutionOn` packages, while the forward-uniqueness lane works with bare metric families.
The bridge is trivial by construction: `SolutionFamily` has a single field `metric`, and
`SolutionOn` a single field `base`, so a metric family *is* a solution candidate, and its
connection is definitionally the Levi-Civita connection of its metric.  Nothing analytic is
hidden here — this is the whole content of the "K1 solution-package bridge" recorded as
missing in `ForwardUniqueAssembly.md`. -/

/-- **The `SolutionOn` package of a metric family.**  `SolutionFamily`'s only field is the
metric, so this is a pure repackaging; the Ricci-flow equation is *not* part of it. -/
def solOfMetric {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (g : Real -> SmoothRiemannianMetric I M) : SolutionOn (I := I) (M := M) D :=
  ⟨⟨g⟩⟩

@[simp]
theorem solOfMetric_metric {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (g : Real -> SmoothRiemannianMetric I M) (s : Real) :
    (solOfMetric (I := I) (D := D) g).base.metric s = g s := rfl

/-- The Christoffel symbols of `solOfMetric g` in a frame are those of `metricCov (g s)`. -/
theorem christoffelInFrame_solOfMetric
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {Idx : Type*} {u : Set M}
    (g : Real -> SmoothRiemannianMetric I M)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (s : Real) (x : M) (i j k : Idx) :
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        ((solOfMetric (I := I) (D := D) g).family.connection s) frame hframe x i j k =
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (metricCov (I := I) (g s)) frame hframe x i j k := rfl

/-- **The bundled bilinear speed `Avec` of the connection difference.**

The `bilinOfComp` package, in the chart frame centred at each point, of the difference of the
two per-flow Christoffel evolution right-hand sides.  This is the data carrier that
`ForwardUniqueAssembly.ForwardUniqueInputs` takes as `Avec`, and `gamma_of_fields` proves it
satisfies the bundle's `gamma` member. -/
def christoffelDiffSpeed
    (gInv₁ gInv₂ : M -> Real ->
      DifferentialGeometry.Integral.Connection.InverseMetricComponents M
        (Fin (Module.finrank Real E)))
    (nablaRic₁ nablaRic₂ : M -> Real -> M -> Fin (Module.finrank Real E) ->
      Fin (Module.finrank Real E) -> Fin (Module.finrank Real E) -> Real)
    (t : Real) (x : M) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x :=
  bilinOfComp (I := I) ((chartFrame_isFrame I x).toBasisAt (chartFrame_mem I x))
    (fun i j k =>
      christoffelEvolutionRHSInFrame (M := M) (gInv₁ x) (nablaRic₁ x) t x i j k -
        christoffelEvolutionRHSInFrame (M := M) (gInv₂ x) (nablaRic₂ x) t x i j k)

/-- **K6b collapse of the bundle's `gamma` member.**

The `gamma` field of `ForwardUniqueAssembly.ForwardUniqueInputs`, verbatim, produced from the
two per-flow Christoffel evolution interfaces `ChristoffelEvolutionEquationInFrameOn` — one
per flow, in the chart frame centred at each point — through
`christoffelEvolutionDiffInFrameOn` (K1) and `coeff_bilinOfComp`.

The `SolutionOn` packages are built here by `solOfMetric`, so the caller supplies only metric
families: the residual input is exactly the two per-flow Christoffel evolution equations,
which is the K2-B standing input of planner ruling R1, at the same level as `rm`'s Uhlenbeck
interfaces.  No smoothness, inverse-metric or pairing hypothesis leaks out. -/
theorem gamma_of_fields
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (g₁ g₂ : Real -> SmoothRiemannianMetric I M)
    (gInv₁ gInv₂ : M -> Real ->
      DifferentialGeometry.Integral.Connection.InverseMetricComponents M
        (Fin (Module.finrank Real E)))
    (nablaRic₁ nablaRic₂ : M -> Real -> M -> Fin (Module.finrank Real E) ->
      Fin (Module.finrank Real E) -> Fin (Module.finrank Real E) -> Real)
    {a b : Real} (hreg : Set.Ioo a b ⊆ D.regular)
    (hΓ₁ : ∀ x₀ : M, ChristoffelEvolutionEquationInFrameOn (I := I) (D := D)
      (solOfMetric (I := I) (D := D) g₁) (gInv₁ x₀)
      (chartFrame I x₀) (chartFrame_isFrame I x₀) (nablaRic₁ x₀))
    (hΓ₂ : ∀ x₀ : M, ChristoffelEvolutionEquationInFrameOn (I := I) (D := D)
      (solOfMetric (I := I) (D := D) g₂) (gInv₂ x₀)
      (chartFrame I x₀) (chartFrame_isFrame I x₀) (nablaRic₂ x₀)) :
    ∀ t ∈ Set.Ioo a b, ∀ x : M, ∀ i j k : Fin (Module.finrank Real E),
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k)
        ((chartFrame_isFrame I x).coeff k x
          ((christoffelDiffSpeed (I := I) gInv₁ gInv₂ nablaRic₁ nablaRic₂ t x
            (chartFrame I x j x)) (chartFrame I x i x))) t := by
  intro t ht x i j k
  have hnhds : D.carrier ∈ 𝓝 t := D.regular_mem_nhds (hreg ht)
  have hval :
      (chartFrame_isFrame I x).coeff k x
          ((christoffelDiffSpeed (I := I) gInv₁ gInv₂ nablaRic₁ nablaRic₂ t x
            (chartFrame I x j x)) (chartFrame I x i x)) =
        christoffelEvolutionRHSInFrame (M := M) (gInv₁ x) (nablaRic₁ x) t x i j k -
          christoffelEvolutionRHSInFrame (M := M) (gInv₂ x) (nablaRic₂ x) t x i j k :=
    coeff_bilinOfComp (I := I) (chartFrame I x) (chartFrame_isFrame I x) (chartFrame_mem I x) _
      i j k
  rw [hval]
  have hdiff := christoffelEvolutionDiffInFrameOn (I := I) (D := D)
    (solOfMetric (I := I) (D := D) g₁) (solOfMetric (I := I) (D := D) g₂)
    (gInv₁ x) (gInv₂ x) (chartFrame I x) (chartFrame_isFrame I x)
    (nablaRic₁ x) (nablaRic₂ x) (hΓ₁ x) (hΓ₂ x) ⟨t, hreg ht⟩ x (chartFrame_mem I x) i j k
  exact hdiff.hasDerivAt hnhds

/-! ### The `gamma` member from (B)'s own fields

The two per-flow Christoffel evolution equations consumed by `gamma_of_fields` are *not* a
standing input: the repo already produces them from a metric family together with its
Ricci-flow PDE and joint chart-Gram smoothness, via `solutionOn_of_joint`
(`Evolution/ExtendedSolutionRegularity.lean`) followed by `tailChristoffel`
(`Evolution/Connection/TailChristoffel.lean`).  The only cost is a *strictly positive-time
tail*: `tailChristoffel` is stated on `Ico t₀ b` with `a < t₀`, which is harmless here because
the `gamma` member is only ever needed at interior times, and `t₀ := (a+t)/2` works for each. -/

variable (I) in
/-- The chart frame is a `C^∞` local frame on the base set of its trivialization. -/
theorem chartFrame_isFrameTop (x₀ : M) :
    IsLocalFrameOn I E (∞ : WithTop ℕ∞) (chartFrame I x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
  (trivializationAt E (TangentSpace I) x₀).isLocalFrameOn_localFrame_baseSet I ∞
    (DifferentialGeometry.Integral.Measure.chartModelBasis E)

/-- Reference interval used only to *name* the frame-inverse and `∇Ric` component families
below.  Both depend on the solution package solely through its metric family, so the choice of
interval is immaterial (the uses in `gamma_of_gram` are definitionally the restricted ones). -/
private def refInterval : DifferentialGeometry.Integral.Connection.RealTimeInterval :=
  DifferentialGeometry.Integral.Connection.RealTimeInterval.univ 0

/-- The inverse chart-frame Gram components of a metric family: the `gInv` that
`tailChristoffel` constructs. -/
def chartFrameInv (g : Real -> SmoothRiemannianMetric I M) (x₀ : M) :
    Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M
      (Fin (Module.finrank Real E)) :=
  localFrameInv (E := E) (I := I) (D := refInterval) (solOfMetric (I := I) g)
    (chartFrame I x₀) (chartFrame_isFrameTop I x₀)

/-- The chart-frame components of `∇Ric` of a metric family: the `nablaRic` that
`tailChristoffel` constructs. -/
def chartNablaRic (g : Real -> SmoothRiemannianMetric I M) (x₀ : M) :
    Real -> M -> Fin (Module.finrank Real E) -> Fin (Module.finrank Real E) ->
      Fin (Module.finrank Real E) -> Real :=
  fun t x d p q =>
    ricciCovDerivCompInFrame (I := I) (D := refInterval) (solOfMetric (I := I) g)
      (chartFrame I x₀) t x d p q

/-- **The per-flow Christoffel evolution equation from (B)'s fields.**  Joint chart-Gram
`C^∞` regularity plus the Ricci-flow equation give, on every strictly positive-time tail, the
Christoffel evolution equation in the chart frame centred at any point. -/
theorem chrEvo_of_gram (g : Real -> SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (hjoint : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M =>
          DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde : ∀ t ∈ Set.Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g s).inner x v w)
        ((-2 : Real) * DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g t) x v w)
        (Set.Ici a) t)
    (x₀ : M) {t₀ : Real} (ha : a < t₀) (hb : t₀ < b) :
    ChristoffelEvolutionEquationInFrameOn (I := I)
      (D := DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen t₀ b hb)
      (solOfMetric (I := I) g) (chartFrameInv (I := I) g x₀) (chartFrame I x₀)
      (chartFrame_isFrame I x₀) (chartNablaRic (I := I) g x₀) := by
  have hS : IsSolutionOn (I := I)
      (solOfMetric (I := I)
        (D := DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen a b hab) g) :=
    solutionOn_of_joint (I := I) hab g hjoint hpde
  obtain ⟨_, h⟩ := tailChristoffel (I := I) (Idx := Fin (Module.finrank Real E)) hS ha hb
    (chartFrame I x₀) (chartFrame_isFrameTop I x₀)
    (trivializationAt E (TangentSpace I) x₀).open_baseSet
  exact h

/-- **K6b, full discharge of the bundle's `gamma` member.**

The `gamma` field of `ForwardUniqueAssembly.ForwardUniqueInputs`, verbatim, from black box
(B)'s own fields only: the two flows' joint chart-Gram `C^∞` regularity on `Ico a b` and their
two Ricci-flow equations.  No standing input remains, and the bundled speed `Avec` is the
constructed `christoffelDiffSpeed`.

At an interior time `t` the tail parameter is `t₀ = (a+t)/2`, so the tail restriction of
`tailChristoffel` costs nothing. -/
theorem gamma_of_gram (g₁ g₂ : Real -> SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (hjoint₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M =>
          DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hjoint₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M =>
          DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde₁ : ∀ t ∈ Set.Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g₁ t) x v w)
        (Set.Ici a) t)
    (hpde₂ : ∀ t ∈ Set.Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g₂ t) x v w)
        (Set.Ici a) t) :
    ∀ t ∈ Set.Ioo a b, ∀ x : M, ∀ i j k : Fin (Module.finrank Real E),
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k)
        ((chartFrame_isFrame I x).coeff k x
          ((christoffelDiffSpeed (I := I) (chartFrameInv (I := I) g₁)
            (chartFrameInv (I := I) g₂) (chartNablaRic (I := I) g₁) (chartNablaRic (I := I) g₂)
            t x (chartFrame I x j x)) (chartFrame I x i x))) t := by
  intro t ht x i j k
  have hat : a < t := ht.1
  have ha : a < (a + t) / 2 := by linarith
  have htt₀ : (a + t) / 2 < t := by linarith
  have hb : (a + t) / 2 < b := lt_trans htt₀ ht.2
  have hval :
      (chartFrame_isFrame I x).coeff k x
          ((christoffelDiffSpeed (I := I) (chartFrameInv (I := I) g₁)
            (chartFrameInv (I := I) g₂) (chartNablaRic (I := I) g₁) (chartNablaRic (I := I) g₂)
            t x (chartFrame I x j x)) (chartFrame I x i x)) =
        christoffelEvolutionRHSInFrame (M := M) (chartFrameInv (I := I) g₁ x)
            (chartNablaRic (I := I) g₁ x) t x i j k -
          christoffelEvolutionRHSInFrame (M := M) (chartFrameInv (I := I) g₂ x)
            (chartNablaRic (I := I) g₂ x) t x i j k :=
    coeff_bilinOfComp (I := I) (chartFrame I x) (chartFrame_isFrame I x) (chartFrame_mem I x) _
      i j k
  rw [hval]
  have hdiff := christoffelEvolutionDiffInFrameOn (I := I)
    (D := DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
      ((a + t) / 2) b hb)
    (solOfMetric (I := I) g₁) (solOfMetric (I := I) g₂)
    (chartFrameInv (I := I) g₁ x) (chartFrameInv (I := I) g₂ x)
    (chartFrame I x) (chartFrame_isFrame I x)
    (chartNablaRic (I := I) g₁ x) (chartNablaRic (I := I) g₂ x)
    (chrEvo_of_gram (I := I) g₁ hab hjoint₁ hpde₁ x ha hb)
    (chrEvo_of_gram (I := I) g₂ hab hjoint₂ hpde₂ x ha hb)
    ⟨t, ⟨htt₀, ht.2⟩⟩ x (chartFrame_mem I x) i j k
  exact hdiff.hasDerivAt
    (DifferentialGeometry.Integral.Connection.RealTimeInterval.regular_mem_nhds _
      (⟨htt₀, ht.2⟩ : t ∈ (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        ((a + t) / 2) b hb).regular))

end Gamma

end DifferentialGeometry.PDE.RicciFlow

end
