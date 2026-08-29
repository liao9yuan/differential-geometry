import DifferentialGeometry.Geometry.Comparison.DistanceCalabi

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry

open Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]

/-- `u` satisfies `Δ u ≤ c` at `x` in the epsilon-relaxed upper-barrier sense.

For every positive `ε`, a smooth function touches `u` from above at `x` and
has Laplacian at most `c + ε` there.  This is the producer-facing barrier
predicate.  It does not itself assert stability under limits or a weak /
distributional inequality; those belong to a subsequent
barrier-to-viscosity-to-weak layer. -/
def IsLapLEBarrierAt
    (g : SmoothRiemannianMetric I M) (u : M → Real) (c : Real) (x : M) : Prop :=
  ∀ ε : Real, 0 < ε →
    ∃ φ : M → Real,
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞) φ x ∧
      φ x = u x ∧
      (∀ᶠ y in 𝓝 x, u y ≤ φ y) ∧
      laplacian (I := I) (LeviCivita (I := I) g) g φ x ≤ c + ε

/-- Pointwise epsilon-relaxed upper-barrier Laplacian inequality on a set. -/
def IsLapLEBarrierOn
    (g : SmoothRiemannianMetric I M) (u b : M → Real) (s : Set M) : Prop :=
  ∀ x ∈ s, IsLapLEBarrierAt (I := I) g u (b x) x

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
/-- An exact smooth upper support produces an epsilon-relaxed upper barrier. -/
theorem lapBarAt_of_support
    (g : SmoothRiemannianMetric I M)
    {u φ : M → Real} {c : Real} {x : M}
    (hφ : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞) φ x)
    (hφx : φ x = u x)
    (huφ : ∀ᶠ y in 𝓝 x, u y ≤ φ y)
    (hlap : laplacian (I := I) (LeviCivita (I := I) g) g φ x ≤ c) :
    IsLapLEBarrierAt (I := I) g u c x := by
  intro ε hε
  exact ⟨φ, hφ, hφx, huφ,
    le_trans hlap (le_add_of_nonneg_right (le_of_lt hε))⟩

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
/-- A barrier upper bound remains valid after increasing its right-hand side. -/
theorem IsLapLEBarrierAt.mono
    {g : SmoothRiemannianMetric I M} {u : M → Real}
    {c d : Real} {x : M}
    (h : IsLapLEBarrierAt (I := I) g u c x) (hcd : c ≤ d) :
    IsLapLEBarrierAt (I := I) g u d x := by
  intro ε hε
  obtain ⟨φ, hφ, hφx, huφ, hlap⟩ := h ε hε
  exact ⟨φ, hφ, hφx, huφ, le_trans hlap (add_le_add_left hcd ε)⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Calabi's smooth upper support gives the distance Laplacian comparison in
epsilon-relaxed barrier sense away from the pole. -/
theorem dist_lap_barrier
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (q : Real) (hq : 0 ≤ q)
    (hRic : Geometry.Riemannian.BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2)))
    {O x : M} (hOx : O ≠ x)
    (hfin : riemannianEDist I O x ≠ (⊤ : ENNReal)) :
    let r := (riemannianEDist I O x).toReal
    IsLapLEBarrierAt (I := I) g
      (fun y : M => (riemannianEDist I O y).toReal)
      (2 * ((Module.finrank Real E - 1 : Nat) : Real) / r +
        ((Module.finrank Real E - 1 : Nat) : Real) * q) x := by
  dsimp only
  obtain ⟨φ, hφ, hφx, huφ, _hgrad, hlap⟩ :=
    calabiDist_support (I := I) (M := M) g hEnorm q hq hRic hOx hfin
  exact lapBarAt_of_support (I := I) (M := M) g hφ hφx huφ hlap

end DifferentialGeometry
