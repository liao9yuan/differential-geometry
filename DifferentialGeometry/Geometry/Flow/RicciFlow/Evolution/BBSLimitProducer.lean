import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CinftyLimitGlue
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedRmTowerHeatEq
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.TowerProducer

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# BBSLimitProducer — Dispatch C: `cinftyLimitData_of_solution`

**STATUS (2026-07-04): DEAD CODE.** `extends_of_rmBounded` was rewired (Y2) onto the
interior-restart + forward-uniqueness route and no longer consumes `CinftyLimitData` or this
producer; both sorries below are off every critical path (do NOT count them as live frontiers).
The Shi-content successor is `shiCovBound_of_soln` (`ExtendShiInputs.lean`), whose discharge plan
(`ExtendShiInputs.md` §SHI DISCHARGE PLAN) unifies the citation with the HCG `MovingShiBoundOn`
interface. Kept for reference per the transitions rule.

Producer for the (now-deleted) `hLimit` sorry in `MaximalTime.lean` (the `extends_of_rmBounded`
BBS/long-time pillar of Hamilton 3D): from a **bounded-curvature** Ricci-flow solution on
`[α, ω)` in **dimension 3**, produce the smooth limit data `CinftyLimitData g_fam α ω hαω`
at the right endpoint `ω`.

The full plan, interface map, and standing-input ledger are in `BBSLimitProducer.md`.

## Architecture (two precise frontiers + a sorry-free composition)

`cinftyLimitData_of_solution` is `cinftyLimitData_of_allMBounds ∘ bbsAllMBounds`, splitting the
old monolithic `hLimit` into two genuinely-different, separately-attackable mathematical frontiers:

* **`bbsAllMBounds`** (bricks C1+C2): the Bernstein–Bando–Shi **all-`m` derivative estimate**
  `‖∇ᵐRm‖² ≤ Cₘ` on slabs bounded away from the start.  This is `sorry` because brick C1 routes
  through `resStarBoundLF` (`StarSum/TowerHeat.lean`), which is itself sorry-free but carries the
  **irreducible DeTurck time-regularity standing inputs** `hbase` (Lemma 6.1 `∂ₜRm04 = Δ+2B−drift`)
  and `hswap` (time/space derivative swap), together with the metric-frame regularity boxes
  (`MetricFrameTimeRegularityInFrameOnLocal`).  These are **not** derivable from `IsSolutionOn` —
  they are the coworker's DeTurck lane, the same frontier `extends_of_rmBounded` already defers via
  its `hglue` sorry (`DeTurckHandoff.md`).  The route, once those inputs are available:
  `nablaKRm04NormHeatEquationOn_intrinsic` (`IteratedRmTowerHeatEq.lean:185`) at per-`(t,x)`
  `g_t`-orthonormal frames + `resStarBoundLF` → `nablaKReaction_le` + `towerHeatBoundOn_of_heatReact`
  (`StarSum/TowerProducer.lean`, GREEN) → `∀k, TowerHeatBoundOn` → `BernsteinTower.estimate_div`
  (`BernsteinShiHigher.lean:1311`) → specialise to the slab `[(α+ω)/2, ω)`.

* **`cinftyLimitData_of_allMBounds`** (brick C3): the limit-extraction **analysis** — from the
  all-`m` bounds, build the `C∞` limit metric and prove Ricci continuity across `ω`.  This is
  `sorry` pending two named analysis frontiers:
  - **G3** (`limitMetric`/`tendsto_left`): construct a `SmoothRiemannianMetric` from the pointwise
    chart-Gram `C⁰` limits (via `chartGramMatrix_tendsto_nhdsLT_of_bounded_deriv`,
    `CinftyLimitGlue.lean:176`, driven by the `m=0` bound `|∂ₜg| = 2|Ric| ≤ C·K`) together with the
    uniform spatial `Cᵐ` bounds — i.e. a *“smooth limit object from uniform `Cᵐ` bounds”* builder,
    which is **missing infrastructure** (no banked constructor fills `CinftyLimitData`).
  - **G4** (`ricci_match`): Ricci continuity from the `m ≤ 2` bounds via **Arzelà–Ascoli /
    equicontinuity** on chart-Gram and its `≤ 2` spatial derivatives — likely needs
    Sobolev/interpolation infrastructure not yet present.

Both `sorry`s are mathematically-correct, narrow, named frontiers (per `important_lesson.md`
“keep producer and consumer frontiers explicit”): each is a real theorem with a precise statement,
not a hypotheses-only adapter.

## Dimension and bound conventions

* `hdim : Module.finrank ℝ E = 3` — the whole residual stack is dim-3 (the Uhlenbeck KN identity
  `Rm04 = KN(Ric,S,g)` needs `Weyl = 0`).  This matches `extends_of_rmBounded`'s purpose
  (`ham3_main`).  The per-fibre `finrank (TangentSpace I x) = 3` is derived internally.
* The curvature bound is stated on the **intrinsic** squared norm `nablaKRm04NormSqIntrinsic S 0`
  ( `= normSq0S (g t) x 4 (∇⁰Rm)` , frame-independent), via the realizing `Rm04`.  The hypotheses
  `hRm`/`hbound` are the *unfolded* forms of `MaximalTime`'s `Rm04RealizesSolutionConnectionOn` /
  `Rm04NormSqBoundedAt` (defeq), so `extends_of_rmBounded` wires them with no translation and this
  file does not import `MaximalTime` (avoiding an import cycle).
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Connection
open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [BoundarylessManifold I M]

/-- **Brick C1 + C2 (the Bernstein–Bando–Shi all-`m` derivative estimate).**  On a dimension-3
bounded-curvature Ricci-flow solution, every covariant-derivative level of the curvature is
uniformly bounded on the half-open slab `[(α+ω)/2, ω)` (bounded away from the start, where the
Shi `1/tᵐ` blow-up is harmless).

`w m := nablaKRm04NormSqIntrinsic S m` is the intrinsic `‖∇ᵐRm‖²`.  `hbound` is the `m = 0`
curvature bound (the realizing `Rm04`'s squared norm, `= w 0`).

**Status: `sorry` — the DeTurck-gated brick.**  The proof route is fully scoped (`BBSLimitProducer.md`
§2 C1/C2): the GREEN reaction machinery (`nablaKReaction_le`, `towerHeatBoundOn_of_heatReact` in
`StarSum/TowerProducer.lean`) fed by `nablaKRm04NormHeatEquationOn_intrinsic` +
`resStarBoundLF`, then `BernsteinTower.estimate_div`.  It bottoms out on the irreducible DeTurck
time-regularity standing inputs (`hbase`, `hswap`, the metric-frame boxes) carried by
`resStarBoundLF` — not derivable from `IsSolutionOn`, the coworker's lane (`DeTurckHandoff.md`),
already deferred by `extends_of_rmBounded`'s `hglue`. -/
theorem bbsAllMBounds
    {alpha omega : ℝ} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hαω))
    (hS : IsSolutionOn (I := I) S)
    (hdim : Module.finrank ℝ E = 3)
    (Rm04 : ℝ → Tensor04Section (I := I) (M := M))
    (hRm : ∀ t : RealTimeInterval.FlowTime (RealTimeInterval.closedOpen alpha omega hαω),
      Rm04RealizesConnection (I := I)
        (S.family.metric (t : ℝ)) (S.family.connection (t : ℝ)) (Rm04 (t : ℝ)))
    (hbound : ∃ K : ℝ, ∀ (t : ℝ) (x : M),
        alpha ≤ t → t < omega →
          Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (Rm04 t x) ≤ K) :
    ∀ m : ℕ, ∃ C : ℝ, ∀ (t : ℝ) (x : M),
      (alpha + omega) / 2 ≤ t → t < omega →
        nablaKRm04NormSqIntrinsic (I := I) S m t x ≤ C := by
  sorry

/-- **Brick C3 (the limit-extraction analysis).**  From the Bernstein–Bando–Shi all-`m` bounds
near `ω`, produce the smooth limit data `CinftyLimitData g_fam α ω`.

**Status: `sorry` — pending two named analysis frontiers** (`BBSLimitProducer.md` §2 C3):
* **G3** — `limitMetric`/`tendsto_left`: build a `SmoothRiemannianMetric` from the pointwise
  chart-Gram `C⁰` limits (`chartGramMatrix_tendsto_nhdsLT_of_bounded_deriv`) + the uniform spatial
  `Cᵐ` bounds.  No banked constructor produces `CinftyLimitData`; this *“smooth limit from uniform
  bounds”* builder is the missing infrastructure.
* **G4** — `ricci_match`: Ricci continuity across `ω` from the `m ≤ 2` bounds via
  **Arzelà–Ascoli / equicontinuity** on chart-Gram and its `≤ 2` derivatives. -/
def cinftyLimitData_of_allMBounds
    {alpha omega : ℝ} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hαω))
    (hS : IsSolutionOn (I := I) S)
    (hdim : Module.finrank ℝ E = 3)
    (hbounds : ∀ m : ℕ, ∃ C : ℝ, ∀ (t : ℝ) (x : M),
        (alpha + omega) / 2 ≤ t → t < omega →
          nablaKRm04NormSqIntrinsic (I := I) S m t x ≤ C) :
    CinftyLimitData (I := I) S.base.metric alpha omega hαω := by
  sorry

/-- **Dispatch C target — `CinftyLimitData` from a bounded-curvature dim-3 solution.**  This
discharges the `hLimit` leaf of `extends_of_rmBounded` (`MaximalTime.lean`).  It is the sorry-free
composition `cinftyLimitData_of_allMBounds ∘ bbsAllMBounds`; the two remaining frontiers live in
those named lemmas (the DeTurck-gated all-`m` bounds, and the C3 limit-extraction analysis).

`hRm`/`hbound` are the unfolded forms of `MaximalTime.Rm04RealizesSolutionConnectionOn` /
`Rm04NormSqBoundedAt` (definitionally equal), so the call site wires them directly. -/
def cinftyLimitData_of_solution
    {alpha omega : ℝ} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hαω))
    (hS : IsSolutionOn (I := I) S)
    (hdim : Module.finrank ℝ E = 3)
    (Rm04 : ℝ → Tensor04Section (I := I) (M := M))
    (hRm : ∀ t : RealTimeInterval.FlowTime (RealTimeInterval.closedOpen alpha omega hαω),
      Rm04RealizesConnection (I := I)
        (S.family.metric (t : ℝ)) (S.family.connection (t : ℝ)) (Rm04 (t : ℝ)))
    (hbound : ∃ K : ℝ, ∀ (t : ℝ) (x : M),
        alpha ≤ t → t < omega →
          Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (Rm04 t x) ≤ K) :
    CinftyLimitData (I := I) S.base.metric alpha omega hαω :=
  cinftyLimitData_of_allMBounds (I := I) S hS hdim
    (bbsAllMBounds (I := I) S hS hdim Rm04 hRm hbound)

end DifferentialGeometry.PDE.RicciFlow
