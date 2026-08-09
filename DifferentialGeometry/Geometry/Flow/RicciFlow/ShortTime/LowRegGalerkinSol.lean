import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifClassBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinTameSol

/-!
# The order-one `V_N` Galerkin system for `lowregNfun`

The Galerkin route to the missing a-priori bound on the order-one
Ricci--DeTurck forcing (`lowreg_loMass`, `ShortTime/LowRegAllOrderJet.lean`)
needs three pieces at base order `a = 1`: the `V_N` ODE system, the
identification of its coordinates with the projected forcing, and the
per-scale energy closure.  This file is the **first**.

The tree already has the `V_N` system for the Ricci--DeTurck nonlinearity, but
only above the Lipschitz gate `2·finrank ℝ E + 10 ≤ a`
(`deTurckGalerkin_solution_existsSymm`).  That gate is about a different
object: at `a = 1` the nonlinearity is *provably* not globally Lipschitz, since
the third arm of its tame estimate carries the ambient `H³` norm, which
`lowerState g₀ 1 R` does not bound.

`HeatSemigroup/GalerkinTameSol.lean` dissolves the obstruction on a truncation:
`V_N` is finite dimensional, so `‖u‖_{H³} ≤ √(N+1)·‖u‖_{H²}` there
(`galTopNormLe`), the state ball becomes bounded for the top norm, and
`tame_lip_balls` supplies the Lipschitz constant Picard--Lindelöf needs.  This
file feeds it the six-number data of `lowreg_partial_sol_of_bounds` — the same
data `IsLowSolve` carries — at `a = 1`.

## Main result

* `lowregGalSol` — for every truncation level `N` a `V_N`-valued solution with
  zero seed, on the **whole** horizon, of
  `U' = −Λ U + Π_N (lowregNfun (retract U))`.

The retraction is inert exactly on the state ball (`galTameForce_eq`), which is
an `H²` condition, uniform in `N`; supplying that bound is the business of the
per-scale energy closure, not of this file.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

open scoped Classical in
/-- **The order-one `V_N` Galerkin system of the low-regularity
Ricci--DeTurck nonlinearity.**

The hypotheses are the six-number producer certificates of
`lowreg_partial_sol_of_bounds`: a metric realization bound at radius `P` and
the critical three-arm tame estimate on the closed state ball
`lowerState g₀ 1 (lowregStateRad Ctop B1 ρ P)`, with coefficients
`Ctop · lowregOuterRad Ctop ρ P`, `B0` and `B1`.  These are exactly the fields
`IsLowSolve` carries, so a consumer that has destructured a low solve feeds
this theorem for free — and no continuity, zero-state bound, horizon cap or
forcing-ball hypothesis is needed here.

For every truncation level `N` the theorem produces a coefficient family
`U N` supported on `eigenIdxFinset g₀ N`, continuous on `[0, T]`, starting at
zero, and solving

  `d/dt (U N t i) = −λᵢ · U N t i + galTameForce … (U N t) i`

on `[0, T)`.  Existence is on the **whole** interval, for every `T`: the
retraction caps the nonlinearity, so the coordinate field is globally Lipschitz
with a global affine bound, and `forward_solution_of_lipschitzWith_affineBound`
applies with no smallness at all.

`galTameForce` evaluates `lowregNfun` at the *retracted* state.  By
`galTameForce_eq` the retraction is inert exactly where the `H²` view of the
Galerkin state has norm at most the state radius — an `N`-uniform condition,
which is the one an energy estimate can hope to produce. -/
theorem lowregGalSol (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 ρ P : ℝ} (hδ : δ < 1) (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0)
    (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
        (lowregStateRad Ctop B1 ρ P),
      ‖lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal u -
          lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal v‖ ≤
        Ctop * lowregOuterRad Ctop ρ P *
            ‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
          B0 *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
          B1 *
              (‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(v.1 : tensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
    {T : ℝ} (hT : 0 < T) :
    ∃ U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ,
      (∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T)) ∧
      (∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
        ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            galTameForce (I := I) (M := M) g₀ 1
              (lowregStateRad_pos hCtop hB1 hρ hP).le
              (lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i)
          (Set.Ici t) t) ∧
      (∀ N, ∀ i, U N 0 i = 0) ∧
      (∀ N, ∀ t, ∀ i, i ∉ eigenIdxFinset (I := I) (M := M) g₀ N →
        U N t i = 0) := by
  classical
  have hRpos : 0 < lowregStateRad Ctop B1 ρ P :=
    lowregStateRad_pos hCtop hB1 hρ hP
  have hQnn : 0 ≤ lowregOuterRad Ctop ρ P :=
    (lowregOuterRad_pos hCtop hρ hP).le
  have hstep : ∀ N : ℕ,
      ∃ V : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ,
        (∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          ContinuousOn (fun t => V t i) (Set.Icc (0 : ℝ) T)) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T,
          ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          HasDerivWithinAt (fun r => V r i)
            (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V t i +
              galTameForce (I := I) (M := M) g₀ 1 hRpos.le
                (lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
                (eigenIdxFinset (I := I) (M := M) g₀ N) (V t) i)
            (Set.Ici t) t) ∧
        (∀ i, V 0 i = 0) ∧
        (∀ t, ∀ i, i ∉ eigenIdxFinset (I := I) (M := M) g₀ N → V t i = 0) := by
    intro N
    have hκ0 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
    have hκ : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        1 + TensorEigenIdx.lambda (I := I) (M := M) i ≤ (N : ℝ) + 1 := by
      intro i hi
      rw [mem_eigenIdxFinset] at hi
      linarith
    exact galTameSolOne (I := I) (M := M) g₀ 1 hRpos.le
      (lowregNfun (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
      hCtop hB0 hB1 hQnn htame
      (eigenIdxFinset (I := I) (M := M) g₀ N) hκ0 hκ hT
  choose U hUcont hUderiv hUinit hUsupp using hstep
  exact ⟨U, hUcont, hUderiv, hUinit, hUsupp⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
