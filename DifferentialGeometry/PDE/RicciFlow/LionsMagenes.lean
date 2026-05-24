import Mathlib.Analysis.InnerProductSpace.Basic
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2

namespace DifferentialGeometry.PDE.RicciFlow

theorem lions_magenes_intermediate_trace
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (ι : X →L[ℝ] Y) (T : ℝ) (hT : 0 < T) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow
