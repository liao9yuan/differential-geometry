import DifferentialGeometry.Geometry.Coordinates.ChartRegistration
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.LocallyClosed

open Set Topology
open scoped ContDiff Manifold Set.Notation

noncomputable section

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def IsEmbeddedSlice (I : ModelWithCorners ℝ E H) (d : ℕ) (N : Set M) : Prop :=
  ∀ x ∈ N,
    ∃ (Φ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
      (A : AffineSubspace ℝ E),
      FiniteDimensional ℝ A.direction ∧
        x ∈ Φ.source ∧
        Module.finrank ℝ A.direction = d ∧
        Φ.toPartialEquiv.IsImage N (A : Set E)

private noncomputable def extChartPD [I.Boundaryless] [IsManifold I ∞ M]
    (x : M) : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using
      (contMDiffOn_extChartAt (I := I) (x := x))
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

namespace IsEmbeddedSlice

theorem of_affine_subspace (A : AffineSubspace ℝ E)
    [FiniteDimensional ℝ A.direction] :
    IsEmbeddedSlice 𝓘(ℝ, E) (Module.finrank ℝ A.direction) (A : Set E) := by
  intro x hx
  let Φ := (Diffeomorph.refl 𝓘(ℝ, E) E ∞).toPartialDiffeomorph
  refine ⟨Φ, A, inferInstance, ?_, rfl, ?_⟩
  · exact Set.mem_univ x
  · intro y _
    change (y ∈ (A : Set E) ↔ y ∈ (A : Set E))
    exact Iff.rfl

theorem of_is_open [I.Boundaryless] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] {N : Set M} (hN : IsOpen N) :
    IsEmbeddedSlice I (Module.finrank ℝ E) N := by
  intro x hx
  let c := extChartPD (I := I) x
  let e := c.toOpenPartialHomeomorph
  let s := e.source ∩ N
  have hs : IsOpen s := c.open_source.inter hN
  have hse : s ⊆ e.source := inter_subset_left
  let Φ :=
    DifferentialGeometry.Tensor.Coordinates.PartialDiffeomorph.ofOpenPartialHomeomorphRestr
      e s hs hse (c.contMDiffOn_toFun.mono inter_subset_left)
        (c.contMDiffOn_invFun.mono (by
          rintro y ⟨z, hz, rfl⟩
          exact c.map_source' hz.1))
  refine ⟨Φ, ⊤, inferInstance, ?_, ?_, ?_⟩
  · exact ⟨mem_extChartAt_source x, hx⟩
  · rw [AffineSubspace.direction_top, finrank_top]
  · intro y hy
    change ((Φ : M → E) y ∈ (⊤ : AffineSubspace ℝ E) ↔ y ∈ N)
    constructor
    · intro _
      exact hy.2
    · intro _
      exact AffineSubspace.mem_top ℝ E (Φ y)

theorem is_open [FiniteDimensional ℝ E] {N : Set M}
    (hN : IsEmbeddedSlice I (Module.finrank ℝ E) N) : IsOpen N := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨Φ, A, _, hxΦ, hdim, himage⟩ := hN x hx
  have hxA : Φ x ∈ A := (himage.apply_mem_iff hxΦ).2 hx
  have hdir : A.direction = ⊤ := Submodule.eq_top_of_finrank_eq hdim
  have hA : A = ⊤ :=
    (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨Φ x, hxA⟩).1 hdir
  refine Filter.mem_of_superset (Φ.open_source.mem_nhds hxΦ) ?_
  intro y hy
  exact (himage.apply_mem_iff hy).1 (by
    rw [hA]
    exact AffineSubspace.mem_top ℝ E (Φ y))

theorem is_locally_closed {N : Set M} {d : ℕ}
    (hN : IsEmbeddedSlice I d N) : IsLocallyClosed N := by
  refine ((isLocallyClosed_tfae N).out 2 0).mp ?_
  intro x hx
  obtain ⟨Φ, A, hAfin, hxΦ, _, himage⟩ := hN x hx
  refine ⟨Φ.source, Φ.open_source.mem_nhds hxΦ, ?_⟩
  letI : FiniteDimensional ℝ A.direction := hAfin
  have hcont : Continuous (Φ.source.restrict (Φ : M → E)) :=
    Φ.contMDiffOn_toFun.continuousOn.restrict
  have heq : Φ.source ↓∩ N =
      (Φ.source.restrict (Φ : M → E)) ⁻¹' (A : Set E) := by
    ext y
    exact (himage.apply_mem_iff y.property).symm
  rw [heq]
  exact A.closed_of_finiteDimensional.preimage hcont

end IsEmbeddedSlice
end Geometry
end DifferentialGeometry
