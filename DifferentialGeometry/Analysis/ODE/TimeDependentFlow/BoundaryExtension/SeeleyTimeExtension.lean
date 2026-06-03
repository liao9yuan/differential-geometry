import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge

/-!
# Smooth time-extension of a field smooth on a closed time slab

A time-dependent field `X` that is jointly `C∞` (as a tangent-bundle section) on the *closed*
time slab `Icc 0 T ×ˢ univ` is extended to a field `Xext` that is jointly `C∞` on all of
`ℝ × M` and agrees with `X` on `Icc 0 T`.  This is the Seeley/Whitney smooth-extension-across-a-
boundary statement at the level of the joint tangent-bundle section: unlike the merely-continuous
time-clamp `field_time_clamp_extension`, the extension is smooth across the slab endpoints
`t = 0` and `t = T`, so the autonomised flow field `(1, Xext)` is `C∞` on all of `ℝ × M`.

The construction is the standard Seeley reflection/extension applied in the time variable, fibre
by fibre over `M`; it is recorded here as an isolated deferred input (its body is a later wave's
work), so consumers transitively depend on `sorryAx`.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Smooth time-extension across the slab endpoints.** A field `X` whose joint tangent-bundle
section is `C∞` on the closed time slab `Icc 0 T ×ˢ univ` admits a field `Xext` whose joint
section is `C∞` on all of `ℝ × M` and which agrees with `X` on `Icc 0 T`.

The body is a deferred Seeley/Whitney smooth-extension construction (filled by a later worker);
this theorem therefore transitively depends on `sorryAx`. -/
theorem seeley_time_extend
    (X : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hsmooth0 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Icc 0 T ×ˢ univ)) :
    ∃ Xext : ℝ → ∀ x : M, TangentSpace I x,
      ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xext q.1 q.2) : TangentBundle I M)) ∧
      (∀ t ∈ Set.Icc 0 T, ∀ x : M, Xext t x = X t x) := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
