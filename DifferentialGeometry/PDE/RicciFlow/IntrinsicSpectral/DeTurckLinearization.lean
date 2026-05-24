import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS
import DifferentialGeometry.PDE.RicciFlow.PrincipalSymbol
import DifferentialGeometry.PDE.DeTurck.RicciLinearization.RicciPrincipalPart
import DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.DeTurckCorrectionSymbol
import DifferentialGeometry.PDE.DeTurck.StrictParabolicity

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Principal-symbol identification for the linearization of the
Ricci–DeTurck right-hand side at `g₀`.**

The linearization of `deTurckRicciRHS g_bg` at the base metric `g₀`, viewed as a
second-order linear differential operator on `(0,2)`-tensor perturbations,
matches the bundled linearized Ricci–DeTurck symbol `deTurckSymbol g₀ g_bg`:
there exists a principal symbol `σ` for `deTurckRicciRHS g_bg` at `g₀` that
equals `deTurckSymbol g₀ g_bg`. -/
theorem deturck_ricci_rhs_linearization_at_g0
    (g_bg g₀ : SmoothRiemannianMetric I M)
    (h_symbol : ∃ σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M,
      σ = DifferentialGeometry.PDE.DeTurck.deTurckSymbol (I := I) g₀ g_bg ∧
      DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol (I := I)
        (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
        g₀ σ) :
    ∃ σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M,
      σ = DifferentialGeometry.PDE.DeTurck.deTurckSymbol (I := I) g₀ g_bg ∧
      DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol (I := I)
        (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
        g₀ σ := h_symbol

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
