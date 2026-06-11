import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# `ric_bound` — the open `(A_N)` endpoint of MSM135 Lemma 3.11 (eq. 3.4 input)

THE target theorem of the ric_bound track, stated intrinsically: on a compact
set `K` and a time window, for a sequence of metrics `gSeq i t` that is
uniformly equivalent to the fixed reference `gRef` (eq. 3.3), has uniformly
bounded lower-order `gRef`-derivatives (`(B_r)`, `r < N`), and satisfies the
Shi-type bounds on the moving-metric covariant derivatives of its Ricci tensor
up to order `N`, the `N`-th `gRef`-covariant derivative of the Ricci tensor is
bounded by the `N`-th `gRef`-covariant derivative of the metric:

`|∇_gRef^N Ric(g)|_gRef ≤ Cpp · |∇_gRef^N g|_gRef + Cppp`  on `K × [β, ψ]`.

This is exactly the `ric_bound` field of `MetricCovOrderEvolutionInput`
(`AllTimesBounds.lean`), whose Grönwall assembly
(`metricCovOrderWindow_of_evolution`) converts it into the `(B_N)` window
bound — the stage-`N` step of MSM135 Lemma 3.11, Step 4.

## Discharge plan (the `sorry` below)

The component-level analytic core is PROVEN (`RicBoundClaims.lean`, sorry-free):
`mixed_descent` gives `|∇_H^N T| ≤ C·(1 + |∇_{H,U}^{N-1} D|)` pointwise on a
local-frame domain from `hDlow`/`hmix`/`hShiN`, with `claim1_LC` bounding the
top difference factor by `C·(1 + |∇_H^N g|)` and `claim2_component` supplying
the mixed bounds.  What remains to assemble this statement:

1. a smooth local-frame covering of the compact `K` with per-domain frame
   constants (bounded frame gram and inverse against `gRef`);
2. the component ↔ intrinsic norm bridge on each frame domain
   (`iterCovComp_eq_iterCov` + `normSq0S_identity_eq_sum_sq` at a
   `gRef`-orthonormal frame, or the bounded-gram norm equivalence);
3. the moving-norm ↔ fixed-norm conversion of the Shi inputs through the
   metric equivalence `hequiv` (eq. 3.3);
4. the Ricci-component identification: the frame components of
   `ricCovTower g gRef` form the `iterCovComp` tower of the Ricci component
   field (the `frameComp0S`-naturality of `iterCov`, which is
   `iterCovComp_eq_iterCov` applied to `ricciSection`).
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

/-- The `s`-fold `gRef`-covariant derivative tower of the Ricci tensor of `g`:
`∇_gRef^s Ric(g)` as a smooth `(0, 2+s)`-tensor field.  The base is the
realized Ricci section of the Levi-Civita connection of `g`; the steps are the
background Levi-Civita derivative of `gRef` (`iterCov`). -/
noncomputable def ricCovTower
    (g gRef : SmoothRiemannianMetric I M) (s : Nat) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (2 + s) :=
  iterCov (I := I) gRef 2
    (DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
      (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)) s

/-- **`ric_bound` — MSM135 Lemma 3.11, Step 4 `(A_N)` (the eq. 3.4 engine; OPEN).**

At stage `N ≥ 1`: if on the window the sequence is uniformly `gRef`-equivalent
(eq. 3.3, `hequiv`), the lower-order `gRef`-derivative bounds `(B_r)` hold for
`1 ≤ r < N` (`hBprev`), and the moving-metric Shi bounds hold for the Ricci
towers up to order `N` (`hShi`), then there are constants `Cpp, Cppp ≥ 0` with

`|∇_gRef^N Ric(gSeq i t)|_gRef ≤ Cpp · |∇_gRef^N (gSeq i t)|_gRef + Cppp`

at every `x ∈ K`, `t ∈ [β, ψ]`, uniformly in `i`.  This is the `ric_bound`
field of `MetricCovOrderEvolutionInput` with `nablaRic` realized by
`ricCovTower`; `metricCovOrderWindow_of_evolution` then yields `(B_N)`. -/
theorem ric_bound
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (hKc : IsCompact K)
    (N : Nat) (hN : 1 <= N)
    (B : Real -> Real)
    (hequiv : MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B)
    (Cg : Nat -> Real)
    (hBprev : forall r : Nat, 1 <= r -> r < N ->
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef r (Cg r))
    (KShi : Real)
    (hShi : forall s : Nat, s <= N -> forall i : Nat,
      forall t : Real, t ∈ Set.Icc β ψ -> forall x : M, x ∈ K ->
        Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) (gSeq i t) x (2 + s)
            (ricCovTower (I := I) (gSeq i t) (gSeq i t) s x)) <= KShi) :
    exists Cpp Cppp : Real, 0 <= Cpp ∧ 0 <= Cppp ∧
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall x : M, x ∈ K ->
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (2 + N)
              (ricCovTower (I := I) (gSeq i t) gRef N x)) <=
            Cpp * metricCovDerivNorm (I := I) N (gSeq i t) gRef x + Cppp := by
  sorry

end HCGCompactness
end DifferentialGeometry
