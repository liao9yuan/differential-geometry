/-
Authors: Jack McCarthy
-/
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Extension of Local Frames to Global Sections

Given a local frame of a smooth vector bundle on a neighborhood of a point, the frame sections
can be extended to smooth global sections that agree with the frame near the point.

## Main Results

* `IsLocalFrameOn.exists_contMDiffSection_eqOn_nhd` : given a C^n local frame `{sᵢ}` on an
  open neighborhood `u` of `p`, there exist C^n global sections `{sᵢ'}` that agree with `{sᵢ}`
  on a neighborhood of `p`.

## Tags

local frame, vector bundle, smooth section, extension
-/

set_option autoImplicit false

open scoped Manifold Topology ContDiff
open Bundle Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ∞}
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]

variable {ι : Type*} {s : ι → (x : M) → V x} {u : Set M} {p : M}

/-- Given a C^n local frame `{sᵢ}` on an open neighborhood `u` of `p`, there exist
C^n global sections `{sᵢ'}` that agree with `{sᵢ}` on a neighborhood of `p`.

The proof multiplies each frame section by a smooth bump function that equals `1`
near `p` and has compact support inside `u`. -/
theorem IsLocalFrameOn.exists_contMDiffSection_eqOn_nhd
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle n F V I] [IsManifold I ∞ M] [T2Space M]
    (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u) (hp : p ∈ u) :
    ∃ (s' : ι → Cₛ^n⟮I; F, V⟯), ∀ᶠ x in 𝓝 p, ∀ i, s' i x = s i x := by
  -- Obtain a smooth bump function χ at p with tsupport χ ⊆ u
  obtain ⟨χ, -, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp (hu.mem_nhds hp)
  -- Define global sections: s'ᵢ(x) = χ(x) • sᵢ(x)
  refine ⟨fun i => ⟨fun x => χ x • s i x, ?_⟩, ?_⟩
  · -- Smoothness: χ is C^∞ globally, sᵢ is C^n on u, and tsupport χ ⊆ u
    exact (χ.contMDiff.of_le (by exact_mod_cast le_top)).contMDiffOn.smul_section_of_tsupport
      hu hχ (hs.contMDiffOn i)
  · -- χ = 1 near p, so s'ᵢ = sᵢ near p
    filter_upwards [χ.eventuallyEq_one] with x hx i
    simp [hx]
