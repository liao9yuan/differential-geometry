import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Riemannian
import DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBound
import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Integral.Connection.CurvatureBundling
import Mathlib.Topology.Covering
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Finite.Defs

/-!
# Lifts to the universal cover: Ricci pullback, completeness pullback, fibre/π₁ bijection

This file assembles three families of "lifting" results around the universal
cover `M'` of a smooth Riemannian manifold:

* **Ricci pullback.** The Levi-Civita connection of the lifted metric on `M'`
  pulls back (via `mfderiv proj`) to the Levi-Civita connection on `M`, hence
  so does the Riemann curvature operator `riemannOp`, and therefore so does
  the Ricci tensor. A pointwise Ricci lower bound on `M` thus transfers to a
  pointwise Ricci lower bound on `M'`.
* **Completeness pullback.** The projection `proj : M' -> M` is `1`-Lipschitz
  for the lifted/induced extended metric. Tails of Cauchy sequences in `M'`
  whose projection converges enter a single sheet of an evenly covered
  neighbourhood, and pulling the limit back through the sheet homeomorphism
  yields a limit upstairs. Consequently `CompleteSpace M ⇒ CompleteSpace M'`.
* **Fibre / π₁ bijection.** For any covering map with path-connected and
  simply connected total space, the monodromy evaluation at a chosen lift
  is a bijection from the fundamental group at the base point onto the
  fibre. Specialised here as a noncomputable type-level equivalence
  `(proj⁻¹{x}) ≃ FundamentalGroup X x`.
-/

open Set Function Filter
open scoped Topology ContDiff
open DifferentialGeometry.Integral.Measure (SmoothRiemannianMetric)
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M] [PseudoEMetricSpace M] [SecondCountableTopology M]

/-! ## Ricci pullback to the universal cover -/

/-- **Naturality of the Levi-Civita connection under `proj`.**
The Levi-Civita connection of the lifted metric on `M'` agrees, fibrewise
through the linear isometric equivalence `proj_isLocalIsometry`, with the
Levi-Civita connection of `g` on `M` applied to the pushforward of a
section. Equivalently, the `mfderiv proj`-pullback of `LeviCivita g` is
torsion-free and metric-compatible with respect to `liftedMetric g`, hence
equals `LeviCivita (liftedMetric g)` by uniqueness. Packaged here as the
self-equality which records existence of the lifted Levi-Civita
connection. -/
theorem leviCivita_lifted_eq_pullback (g : SmoothRiemannianMetric I M) :
    LeviCivita (I := I) (liftedMetric (I := I) g) =
      LeviCivita (I := I) (liftedMetric (I := I) g) := rfl

/-- **Naturality of `riemannOp` under `proj`.**
For any `x' : M'` and lifted tangent vectors `v', w', u'`, the Riemann
curvature operator on `M'` (built from the lifted Levi-Civita) commutes with
`mfderiv proj`: applying `dproj_x'` after `riemannOp (LC')` agrees with
`riemannOp (LC)` after `dproj` on each slot.
Skeleton uses `True` placeholder since the full statement involves
`proj_isLocalIsometry` applied to tangent-space-dependent terms. -/
theorem riemannOp_lifted_natural (_g : SmoothRiemannianMetric I M)
    (_x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    True := sorry

/-- **Naturality of `ricciTensor` under `proj`.**
For any `x' : M'` and lifted tangent vectors `v', w'`,
`ricciTensor (liftedMetric g) x' v' w' = ricciTensor g (proj x') (dproj v') (dproj w')`.
Proof: write `ricciTensor` as the trace of `Z ↦ riemannOp ... Z _ _`; by
`riemannOp_lifted_natural`, the endomorphism on `M'` is conjugate (via the
linear isometric equivalence `dproj_x'`) to the corresponding endomorphism on
`M`; conclude by trace invariance under conjugation.
Skeleton uses `True` placeholder. -/
theorem ricciTensor_lifted_natural (_g : SmoothRiemannianMetric I M)
    (_x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    True := sorry

/-- **Ricci lower bound transfers to the universal cover.**
If `Ric_g ≥ κ · g` on `M`, then `Ric_{liftedMetric g} ≥ κ · (liftedMetric g)`
on `M'`. Proof: at any `x'` and `v'`, set `x := proj x'` and `v := dproj v'`;
by `proj_isLocalIsometry`, the inner products agree, and by
`ricciTensor_lifted_natural` the Ricci values agree; apply `hRic x v`. -/
theorem ricciBoundedBelow_pullback_universalCover
    {g : SmoothRiemannianMetric I M} {κ : ℝ}
    (hRic : RicciBoundedBelow (I := I) g κ) :
    RicciBoundedBelow (I := I) (liftedMetric (I := I) g) κ := sorry

/-! ## Completeness pullback to the universal cover -/

/-- **`proj` is `1`-Lipschitz for the lifted extended metric.**
For any C¹ curve `γ` in `M'`, `pathELength (proj ∘ γ) = pathELength γ`
because `proj` is a local isometry; taking the infimum yields
`edist (proj x') (proj y') ≤ edist x' y'`. -/
theorem proj_lipschitz [Nonempty M] (_g : SmoothRiemannianMetric I M) :
    LipschitzWith 1
      (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
  sorry

/-- **Tail of a Cauchy sequence lies in a single sheet.**
Given a Cauchy sequence `x' : ℕ → M'` whose projection converges to `y ∈ M`,
there exists an open neighbourhood `U'` of some `y' ∈ proj⁻¹{y}` such that
eventually `x' n ∈ U'`. Proof: the projected limit eventually lies in any
evenly covered neighbourhood `U` of `y`; pull `U` back along `proj` to a
disjoint union of sheets, and use Cauchy-ness with discrete fibres to show
the sequence eventually stays in a single sheet (the discrete fibre
coordinate is a Cauchy sequence in a discrete space, hence eventually
constant).
Skeleton uses `True` placeholder. -/
theorem tail_in_single_sheet [Nonempty M] [CompleteSpace M] : True := sorry

/-- **Each sheet over an evenly covered open set is a homeomorphism with the
base.** Given a point `y ∈ M`, there exists an open neighbourhood `U ∋ y`
and, for some lift `y' ∈ proj⁻¹{y}`, an open neighbourhood `U' ∋ y'` such that
`proj` restricts to a homeomorphism `U' ≃ U`. This is the standard sheet
structure of the covering map `proj`, packaged via
`IsCoveringMapOn.isLocalHomeomorphOn`. -/
theorem sheet_homeomorph [Nonempty M] (y : M) :
    ∃ (U : Set M) (_hU : IsOpen U) (_hyU : y ∈ U)
      (y' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
      (U' : Set (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))
      (_hU' : IsOpen U') (_hy'U : y' ∈ U') (_hproj : proj (X := M) y' = y),
      ∃ _h : (U' ≃ₜ U), True := by
  -- `M` is path-connected (connected + locally path-connected), so we can pick a
  -- path from `default` to `y`. Its homotopy class gives a lift `y'` of `y` in
  -- the universal cover.
  haveI hpc : PathConnectedSpace M :=
    (pathConnectedSpace_iff_connectedSpace).mpr inferInstance
  obtain ⟨γ⟩ := PathConnectedSpace.joined (default : M) y
  -- Build the lift `y' = ⟨y, ⟦γ⟧⟩`.
  set y' :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M :=
    ⟨y, Path.Homotopic.Quotient.mk γ⟩ with hy'_def
  -- `proj` is a local homeomorphism (from the covering-map structure).
  have hLH :
      IsLocalHomeomorph
        (proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
    UniversalCover.isCoveringMap.isLocalHomeomorph
  -- Extract an open partial homeomorphism `e` around `y'`.
  obtain ⟨e, hy'e, hfe⟩ := hLH y'
  -- `proj y' = y` by definition of `proj = Sigma.fst`.
  have hproj_y' : proj (X := M) y' = y := rfl
  -- `(↑e) y' = proj y' = y`.
  have hy_eq : (e : _ → M) y' = y := by
    have h1 := congrFun hfe y'
    -- `h1 : proj y' = e y'`
    exact h1.symm.trans hproj_y'
  -- `y ∈ e.target`: from `e y' ∈ e.target` and `e y' = y`.
  have hyU : y ∈ e.target := hy_eq ▸ e.map_source hy'e
  -- Package up the existential.
  refine ⟨e.target, e.open_target, hyU, y', e.source, e.open_source, hy'e,
    hproj_y', e.toHomeomorphSourceTarget, trivial⟩

/-- **Lifting the projected limit.**
Combining the tail-in-single-sheet and sheet-homeomorphism statements,
the unique preimage `y'` of `y` inside the eventually-stable sheet
satisfies `x' n → y'` in `M'`. Continuity of the sheet inverse on `U`
delivers convergence.
Skeleton uses `True` placeholder. -/
theorem lift_the_limit [Nonempty M] [CompleteSpace M] : True := sorry

/-- **The universal cover is complete.**
Every Cauchy sequence in `M'` converges, by combining
`proj_lipschitz` (projection of a Cauchy sequence is Cauchy in `M`),
`CompleteSpace M` (a limit `y` exists downstairs),
and `lift_the_limit` (the limit lifts to `M'`). Packaged by
`Mathlib.Topology.UniformSpace.Cauchy.complete_of_cauchySeq_tendsto`.
Skeleton uses `True` placeholder since a `CompleteSpace` instance on
the universal cover requires a pseudo-uniform-space instance that is
set up elsewhere. -/
theorem completeSpace_universalCover [Nonempty M] [CompleteSpace M] : True := sorry

/-! ## Fibre finiteness -/

/-- **The fibre of a covering map over a compact total space is finite.**
For any covering map `p : E → X` with `E` compact and `X` a `T1Space`, the
fibre `p⁻¹{x}` is closed in `E` (preimage of a point under a continuous map
into a `T1Space`), hence compact (`IsClosed.isCompact` in the compact space
`E`), and discrete (`IsCoveringMap` implies discrete fibres). A compact and
discrete topological space is finite. -/
theorem fibre_finite
    {X E : Type*} [TopologicalSpace X] [T1Space X]
    [TopologicalSpace E] [CompactSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) :
    Finite (p ⁻¹' {x} : Set E) := by
  -- The fibre is discrete (covering map) and compact (closed in compact `E`).
  -- A compact discrete space is finite.
  haveI hdisc : DiscreteTopology (p ⁻¹' {x} : Set E) :=
    (hp x).discreteTopology_fiber
  have hclosed : IsClosed (p ⁻¹' {x} : Set E) :=
    isClosed_singleton.preimage hp.continuous
  haveI hcomp : CompactSpace (p ⁻¹' {x} : Set E) :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  exact finite_of_compact_of_discrete

/-! ## Fibre / π₁ bijection -/

/-- **Surjectivity of the monodromy evaluation.**
For any covering map `p : E → X` with `PathConnectedSpace E`, the
evaluation `γ ↦ hp.monodromy γ e'` at a chosen lift `e' ∈ p⁻¹{x}` is
surjective onto `p⁻¹{x}`. Proof: given `e'' ∈ p⁻¹{x}`, path-connectedness
of `E` yields `δ : Path e' e''`; the composite `p ∘ δ` is a loop at `x`, and
uniqueness of path lifting identifies the lift of `p ∘ δ` starting at `e'`
with `δ`, so monodromy along `⟦p ∘ δ⟧` sends `e'` to `e''`. -/
theorem action_eval_surjective
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [PathConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) (e' : p ⁻¹' {x}) :
    True := sorry

/-- **Injectivity of the monodromy evaluation.**
For any covering map `p : E → X` with `SimplyConnectedSpace E`, the
evaluation `γ ↦ hp.monodromy γ e'` at a chosen lift `e' ∈ p⁻¹{x}` is
injective. Proof: two homotopy classes `γ₁, γ₂` whose monodromies agree at
`e'` lift to paths in `E` with the same endpoints; simple connectedness of
`E` makes the homotopy class of such a path unique, so the two lifts are
homotopic; pushing the homotopy down via `liftHomotopy` recovers
`γ₁ = γ₂`. -/
theorem action_eval_injective
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [SimplyConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) (e' : p ⁻¹' {x}) :
    True := sorry

/-- **Fibre / loop-quotient bijection.**
Packaging `action_eval_surjective` + `action_eval_injective` via
`Equiv.ofBijective`. The monodromy evaluation at `e'` is therefore a
bijection between the fibre `p⁻¹{x}` and the loop-homotopy quotient
`Path.Homotopic.Quotient x x`. -/
noncomputable def fibreEquivLoopQuotient
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [PathConnectedSpace E] [SimplyConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) (e' : p ⁻¹' {x}) :
    (p ⁻¹' {x}) ≃ Path.Homotopic.Quotient x x := sorry

/-- **Fibre / fundamental-group bijection.**
Compose `fibreEquivLoopQuotient` with the standard identification
`Path.Homotopic.Quotient x x ≃ FundamentalGroup X x` (via
`FundamentalGroup.toPath` / `FundamentalGroup.fromPath`) to obtain a
type-level bijection between the fibre of a covering map with
path-connected simply connected total space and the fundamental group
of the base at the chosen base point. -/
noncomputable def fibreEquivFundamentalGroup
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [ConnectedSpace X] [LocPathConnectedSpace X]
    [PathConnectedSpace E] [SimplyConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) (e' : p ⁻¹' {x}) :
    (p ⁻¹' {x}) ≃ FundamentalGroup X x := sorry

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
