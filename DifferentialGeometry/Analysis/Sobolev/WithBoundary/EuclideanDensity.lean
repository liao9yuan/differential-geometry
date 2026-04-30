import DifferentialGeometry.Analysis.Sobolev.EuclideanDensity
import DifferentialGeometry.Analysis.Sobolev.EuclideanIteratedSobolevHalfSpace

/-!
# Density of smooth compactly-supported functions in `W^{k,p}_0` on
half-space-friendly domains

This module is the half-space-friendly companion of
`Analysis/Sobolev/EuclideanDensity.lean`. It establishes that any function
in the Dirichlet (zero-trace) iterated Sobolev space
`MemWkpHalfSpace k p u Ω` whose compact support sits *strictly inside* the
open interior part `interiorHalfSpace Ω` is approximated, in
`wkpNormHalfSpace`, by smooth compactly-supported functions whose own
support also sits strictly inside the open interior part.

## Strategy

Recall from `EuclideanIteratedSobolevHalfSpace.lean`:

* `MemWkpHalfSpace k p u Ω = MemWkp k p u (interiorHalfSpace Ω)`,
* `wkpNormHalfSpace k p u Ω = wkpNorm k p u (interiorHalfSpace Ω)`,
* `interiorHalfSpace_isOpen` shows that `interiorHalfSpace Ω` is open in `E`
  for half-space-friendly `Ω`.

The half-space density theorem reduces by definitional unfolding to the
boundaryless density theorem `MemWkp.exists_smooth_compactSupport_approx`
applied with `Ω` set to `interiorHalfSpace Ω` (which is open).

## Main result

* `MemWkpHalfSpace.exists_smooth_compactSupport_approx` — given
  `u ∈ W^{k,p}_0(Ω)` with `tsupport u ⊆ interiorHalfSpace Ω` and `ε > 0`,
  there exists a smooth compactly-supported `φ` with
  `tsupport φ ⊆ interiorHalfSpace Ω` and
  `wkpNormHalfSpace k p (u - φ) Ω ≤ ENNReal.ofReal ε`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Density of smooth compactly-supported functions in `W^{k,p}_0(Ω)` -/

/-- **Density of smooth compactly-supported functions in
`W^{k,p}_0(Ω)`** for a half-space-friendly carrier `Ω`. For
`u ∈ W^{k,p}_0(Ω)` with compact support strictly inside the open interior
part `interiorHalfSpace Ω`, mollification produces smooth compactly-
supported approximants `φ` whose support also sits inside
`interiorHalfSpace Ω` and which approximate `u` arbitrarily well in
`wkpNormHalfSpace`.

The proof reduces by definitional unfolding to the boundaryless density
theorem `MemWkp.exists_smooth_compactSupport_approx`, applied with the
ambient open set taken to be `interiorHalfSpace Ω` (open in `E` since
`Ω` is half-space-friendly). -/
theorem MemWkpHalfSpace.exists_smooth_compactSupport_approx
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsHalfSpaceRelOpen Ω)
    (k : ℕ) (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : MemWkpHalfSpace k p u Ω)
    (hu_compactSupport : HasCompactSupport u)
    (hu_supp : tsupport u ⊆ interiorHalfSpace Ω)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
        tsupport φ ⊆ interiorHalfSpace Ω ∧
        wkpNormHalfSpace k p (fun x => u x - φ x) Ω ≤ ENNReal.ofReal ε := by
  -- The interior part is open in `E`.
  have hΩ_open : IsOpen (interiorHalfSpace (d := d) Ω) :=
    interiorHalfSpace_isOpen hΩ
  -- `MemWkpHalfSpace k p u Ω` is by definition `MemWkp k p u (interiorHalfSpace Ω)`.
  have hu' : MemWkp (d := d) k p u (interiorHalfSpace Ω) := hu
  -- Apply the boundaryless density theorem on the open set
  -- `interiorHalfSpace Ω`.
  obtain ⟨φ, hφ_smooth, hφ_compact, hφ_supp, hφ_norm⟩ :=
    MemWkp.exists_smooth_compactSupport_approx (d := d)
      hΩ_open k p hp_one hp_top hu' hu_compactSupport hu_supp ε hε
  -- Unfold `wkpNormHalfSpace` to expose the boundaryless `wkpNorm` on the
  -- interior part, which is exactly what the boundaryless theorem gives us.
  refine ⟨φ, hφ_smooth, hφ_compact, hφ_supp, ?_⟩
  change wkpNorm (d := d) k p (fun x => u x - φ x) (interiorHalfSpace Ω) ≤
    ENNReal.ofReal ε
  exact hφ_norm

/-! ## Special-case re-export: open carriers contained in `openHalfSpace`

When the carrier is itself open in `E` and contained in `openHalfSpace`,
`MemWkpHalfSpace` coincides with the boundaryless `MemWkp` on `Ω` (see
`MemWkpHalfSpace_iff_memWkp_of_subset_openHalfSpace`). For convenience we
record the directly-typed density statement in this case. -/

/-- Specialised density theorem when the half-space-friendly carrier
happens to coincide with an open set contained in the open half-space. The
conclusion is phrased in terms of the carrier itself rather than the
interior part, because the two coincide here.

This is a thin corollary of `MemWkpHalfSpace.exists_smooth_compactSupport_approx`
that may be more ergonomic to apply on chart targets that the user has
already verified to live strictly above the boundary hyperplane. -/
theorem MemWkpHalfSpace.exists_smooth_compactSupport_approx_of_subset_openHalfSpace
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ_open : IsOpen Ω) (hsub : Ω ⊆ openHalfSpace)
    (k : ℕ) (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : MemWkpHalfSpace k p u Ω)
    (hu_compactSupport : HasCompactSupport u) (hu_supp : tsupport u ⊆ Ω)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω ∧
        wkpNormHalfSpace k p (fun x => u x - φ x) Ω ≤ ENNReal.ofReal ε := by
  -- The carrier is half-space-friendly, since it is open and contained in
  -- the open half-space.
  have hΩ : IsHalfSpaceRelOpen (d := d) Ω :=
    IsHalfSpaceRelOpen.of_isOpen_subset_open hΩ_open hsub
  -- `interiorHalfSpace Ω = Ω ∩ openHalfSpace = Ω` here.
  have h_int_eq : interiorHalfSpace (d := d) Ω = Ω :=
    inter_eq_self_of_subset_left hsub
  -- `tsupport u ⊆ interiorHalfSpace Ω` follows from `tsupport u ⊆ Ω`.
  have hu_supp' : tsupport u ⊆ interiorHalfSpace (d := d) Ω := by
    rw [h_int_eq]
    exact hu_supp
  obtain ⟨φ, hφ_smooth, hφ_compact, hφ_supp, hφ_norm⟩ :=
    MemWkpHalfSpace.exists_smooth_compactSupport_approx
      hΩ k p hp_one hp_top hu hu_compactSupport hu_supp' ε hε
  refine ⟨φ, hφ_smooth, hφ_compact, ?_, hφ_norm⟩
  -- Translate `tsupport φ ⊆ interiorHalfSpace Ω` to `tsupport φ ⊆ Ω` via
  -- the equality `interiorHalfSpace Ω = Ω`.
  rw [← h_int_eq]
  exact hφ_supp

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
