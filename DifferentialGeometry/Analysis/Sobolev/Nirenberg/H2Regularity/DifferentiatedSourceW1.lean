import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.DifferentiatedSourceK

/-!
# First Sobolev Regularity of the Differentiated Source

This compatibility module records the first-order specialization of the
all-order differentiated-source regularity theorem.
-/

noncomputable section

open Set
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- If a homogeneous solution has three weak derivatives, then its canonical
differentiated scalar source has one weak derivative. -/
theorem homDiff_memW1
    {Omega : Set E} (hOmega : IsOpen Omega)
    (hOmega_compact : IsCompact (closure Omega))
    (B : SmoothEllipticBilinearForm d (Set.univ : Set E))
    {u : E → ℝ} (hu3 : MemWkp (d := d) 3 2 u Omega)
    (l : Fin d) :
    MemWkp (d := d) 1 2 (homDiffSource B u Omega l) Omega := by
  exact homDiff_memWkp 1 hOmega hOmega_compact B hu3 l

end DifferentialGeometry.Analysis.Sobolev.NirenbergHomogeneous
