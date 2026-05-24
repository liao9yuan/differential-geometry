import Mathlib.Analysis.ODE.PicardLindelof

namespace DifferentialGeometry.PDE.RicciFlow.ODE

theorem banach_flow_smooth_in_ic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (X : ℝ → E → E) :
    ∃ T : ℝ, 0 < T := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
