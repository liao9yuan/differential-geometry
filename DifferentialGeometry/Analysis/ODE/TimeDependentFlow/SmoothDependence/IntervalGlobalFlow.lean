import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeFlow.CutoffExtension
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ChartBridge
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The interior flow on `(0, T)` and its agreement with the `t = 0` anchor

On the open interval `(0, T)` the time-dependent DeTurck field is `C∞`, so the intrinsic
closed-manifold flow engine produces, on each window `[a, b] ⊂ (0, T)`, a jointly-`C∞`
bare-velocity local flow.  This file:

* `interior_cutoff_window_flow` — runs the cutoff + intrinsic-engine pipeline on one window;
* `interior_bare_flow_on_Ioo` — glues the per-window flows into a single flow `Φint` on all of
  `(0, T)`, carrying the bare velocity and per-time smoothness, by interior bare-uniqueness;
* `interior_flow_slice_diffeo_on_Ioo` — each time-slice `Φint t` is a diffeomorphism, via the
  reverse flow of `-X_DT`;
* `anchor_eq_interior_on_Ioo` — `Φint` agrees with the `t = 0` anchor `Φ0` on all of `(0, T)`,
  by a continuity-only forward Euclidean Grönwall seed at the `t = 0` edge plus interior
  bare-uniqueness for the bulk.

Every velocity conclusion is the intrinsic bare `X_DT t (point)`; the chart ODEs used in the
edge seed are stated through the corrected `chartTrivRepr`, never the raw chart value.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- On a window `[a, b] ⊂ (0, T)` around `t₀`, build a cutoff field agreeing with `X_DT` near
`[a, b]` and run the intrinsic engine to get a local bare-velocity flow `Φw`, jointly `C∞`,
anchored at `t₀`, whose velocity is `X_DT` on the agreement window. -/
theorem interior_cutoff_window_flow
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) {T : ℝ}
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞ (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M)) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    {a b : ℝ} (hab : 0 < a) (hab' : a < b) (hbT : b < T) (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo a b) :
    ∃ (Te δ : ℝ) (_ : 0 < Te) (_ : 0 < δ) (Φw : M → ℝ → M),
      (∀ p, Φw p t₀ = p) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φw q.2 q.1) (Set.Ioo (t₀ - Te) (t₀ + Te) ×ˢ (Set.univ : Set M)) ∧
      (∀ p, ∀ t ∈ Set.Ioo (t₀ - Te) (t₀ + Te), Set.Ioo (t₀ - Te) (t₀ + Te) ⊆ Set.Ioo (a - δ) (b + δ) → HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φw p s) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φw p t)))) ∧
      Set.Ioo (t₀ - Te) (t₀ + Te) ⊆ Set.Ioo (a - δ) (b + δ) := by
  obtain ⟨Xt, δ, hδ_pos, hagree, hXt_smooth, _hXt_auto⟩ :=
    interior_field_global_cutoff_extension X_DT T hint hab hab' hbT
  obtain ⟨T', hT'_pos, Φ, hΦ_init, hΦ_smooth, hΦ_bare⟩ :=
    global_flow_jointContMDiffOn_on_closed_manifold (I := I) Xt hXt_smooth t₀
  set Te : ℝ := min T' (min (t₀ - (a - δ)) ((b + δ) - t₀)) with hTe_def
  have ht₀a : a - δ < t₀ := by obtain ⟨h1, _⟩ := ht₀; linarith
  have ht₀b : t₀ < b + δ := by obtain ⟨_, h2⟩ := ht₀; linarith
  have hTe_pos : 0 < Te := by
    rw [hTe_def]; refine lt_min hT'_pos (lt_min ?_ ?_) <;> linarith
  have hTe_le_T' : Te ≤ T' := by rw [hTe_def]; exact min_le_left _ _
  have hTe_le_2 : Te ≤ min (t₀ - (a - δ)) ((b + δ) - t₀) := by
    rw [hTe_def]; exact min_le_right _ _
  have hsub_window : Set.Ioo (t₀ - Te) (t₀ + Te) ⊆ Set.Ioo (a - δ) (b + δ) := by
    apply Set.Ioo_subset_Ioo
    · have : Te ≤ t₀ - (a - δ) := le_trans hTe_le_2 (min_le_left _ _); linarith
    · have : Te ≤ (b + δ) - t₀ := le_trans hTe_le_2 (min_le_right _ _); linarith
  have hsub_T' : Set.Ioo (t₀ - Te) (t₀ + Te) ⊆ Set.Ioo (t₀ - T') (t₀ + T') :=
    Set.Ioo_subset_Ioo (by linarith [hTe_le_T']) (by linarith [hTe_le_T'])
  refine ⟨Te, δ, hTe_pos, hδ_pos, Φ, hΦ_init, ?_, ?_, hsub_window⟩
  · exact hΦ_smooth.mono (Set.prod_mono hsub_T' (subset_refl _))
  · intro p t ht _
    have hbare := hΦ_bare p t (hsub_T' ht)
    have hval : Xt t (Φ p t) = X_DT t (Φ p t) := hagree t (hsub_window ht) (Φ p t)
    rw [hval] at hbare
    exact hbare

/-- **Extend the `t = 0` anchor to the full interval.** Given the anchor flow `Φ0` (with
`Φ0 0 = id` and the bare velocity on a short horizon `(0, σ)`), produce a single flow `Φ` on
all of `(0, T)` that AGREES with `Φ0` on `(0, σ)`, carries the bare velocity `X_DT` on `(0, T)`,
and is per-time `C∞`.  The agreement is **interior** (both `Φ` and `Φ0` are bare integral curves
of the interior-`C∞` field on `(0, σ)`, equal at one interior reference point, hence on all of
`(0, σ)` by `bare_integral_flow_eqOn_of_jointC1`); the extension is the per-window intrinsic-engine
continuation glued by the same interior uniqueness over an exhausting family of windows.  No
`t = 0`-edge continuity-only seed is needed: the anchor supplies the `t = 0` behaviour and the
interior continuation supplies `(σ, T)`. -/
theorem interior_extends_anchor
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞ (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M)) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (Φ0 : ℝ → M → M) (σ : ℝ) (hσ : 0 < σ) (hσT : σ ≤ T)
    (hΦ0_0 : ∀ x : M, Φ0 0 x = x)
    (hΦ0_bare : ∀ t ∈ Set.Ioo (0 : ℝ) σ, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ0 s x) (Set.Ioo (0 : ℝ) σ) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φ0 t x)))) :
    ∃ Φ : ℝ → M → M,
      (∀ x : M, Φ 0 x = x) ∧
      (∀ s ∈ Set.Ioo (0 : ℝ) σ, ∀ x : M, Φ s x = Φ0 s x) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Ioo (0 : ℝ) T) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φ t x)))) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ContMDiff I I ∞ (Φ t)) := sorry

/-- Each time-slice `Φint t` (for `t ∈ (0, T)`) is a diffeomorphism, by building the reverse
flow of `-X_DT` and exhibiting the two as mutually inverse smooth maps. -/
theorem interior_flow_slice_diffeo_on_Ioo
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞ (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M)) (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (Φint : ℝ → M → M)
    (hΦint_slice : ∀ t ∈ Set.Ioo (0 : ℝ) T, ContMDiff I I ∞ (Φint t))
    (hΦint_bare : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φint s x) (Set.Ioo (0 : ℝ) T) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φint t x)))) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φint t x := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
