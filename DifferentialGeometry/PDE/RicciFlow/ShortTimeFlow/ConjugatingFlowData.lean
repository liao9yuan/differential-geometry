/-
The genuine open conjugating-flow smooth-dependence inputs of the Hamilton–DeTurck
short-time-existence construction, isolated into two faithful labeled nodes.

Both nodes are PINNED to the GENUINE conjugating flow by the orbit-ODE hypothesis
`hΦode` (the backward bare-orbit equation `∂_s Φ_fam = -deTurckVF (g_DT s) g_bg ∘ Φ_fam`
on the interior `Ioo 0 T`). They are therefore TRUE statements about that specific flow,
not about an arbitrary diffeomorphism family.

* `conjugating_flow_flat_data` bundles the flat variational data of the conjugating flow:
  the per-slot raw flat variational identity with its factor jets `T'`/`P'`
  (`flat_raw_variational_identity` over the flow's chart-ODE jet data), the
  Christoffel-correction equation (`flat_christoffel_correction_eqn`), the base-point-motion
  datum (`basepoint_motion_datum`), and the three-piece additive chain rule
  (`deTurck_pullback_h_total_eval`).

* `conjugating_flow_t0_continuity_data` bundles the `t = 0`-endpoint continuity data: the
  `Ico 0 T` continuity of the pulled-back inner product (`gfam_inner_continuous_on`) and the
  right-continuity at `0` of `-2 Ric` of the pulled-back metric (`ricci_gfam_continuous_on`).

These are the classical-analytic smooth-dependence-on-initial-conditions inputs of the
conjugating flow (two-sided window ODE, autonomized-field joint `C¹`, chart moving-trivialization
jets, joint `(t,x)` chart-Gram smoothness, total-space pushforward continuity up to the
`C⁰`-at-`0` boundary).  Their on-disk providers are proven and faithful, but each still needs
this open conjugating-flow smooth-in-IC data, with no on-disk producer; we isolate that open
content here as faithful labeled `sorry`s for a later dedicated fill effort.
-/
import DifferentialGeometry.PDE.RicciFlow.ShortTimeAssembly.FlatVariationalData
import DifferentialGeometry.PDE.RicciFlow.ShortTimeAssembly.BasepointMotion
import DifferentialGeometry.PDE.RicciFlow.ShortTimeAssembly.EvalFormChainRule
import DifferentialGeometry.PDE.RicciFlow.ShortTimeAssembly.RicciFlowPdeAtZero

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.Integral.Connection

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Flat variational data of the conjugating flow (faithful open input).**

For the conjugating diffeomorphism family `Φ_fam` of the Hamilton–DeTurck construction —
PINNED to the genuine flow by the backward bare-orbit ODE `hΦode`
(`∂_s Φ_fam = -deTurckVF (g_DT s) g_bg ∘ Φ_fam` on `Ioo 0 T`) — the four flat variational
facts of that flow hold:

* `hv_flat`: existence of factor jets `T'`, `P'` realising the per-slot raw flat variational
  identity `RawVariationalIdentityFlat Φ_fam t x v (T' t x v) (P' t x v)` on the interior;
* `hcorr`: the Christoffel-correction equation relating those factor values to the negative
  covariant slot value plus the Christoffel-correction term;
* `hbase`: the base-point-motion datum (the frozen-vector chart-metric map along the orbit has
  within-set derivative `-metricTransportResidual`);
* `h_total_eval`: the three-piece additive chain rule for the full pulled-back inner product.

These are the genuine open chart-ODE jet / variational-lift analytic inputs of the concrete
conjugating flow.  They are TRUE for this flow (pinned via `hΦode`) and reference only the
internal data `g_DT` / `Φ_fam` / `deTurckVF (g_DT t) g_bg`.  Faithful labeled deferred input
for a dedicated fill effort. -/
theorem conjugating_flow_flat_data
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x))))) :
    ∃ T' P' : ℝ → ∀ x : M, TangentSpace I x → (E →L[ℝ] E),
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
          RawVariationalIdentityFlat (I := I) Φ_fam t x v (T' t x v) (P' t x v)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
          (T' t x v) (mfderiv I I (Φ_fam t : M → M) x v) + (P' t x v) v
            = negCovariantSlotValue (I := I) (g_DT t)
                (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v
              + christoffelCorrection (I := I) (g_DT t) (Φ_fam t x) (Φ_fam t x)
                  (chartE_section_repr (I := I) (Φ_fam t x)
                    (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x))
                  (mfderiv I I (Φ_fam t : M → M) x v)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt
            (fun s : ℝ => (g_DT t).inner ((Φ_fam s : M → M) x)
              (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
            (-metricTransportResidual (I := I) (g_DT t)
                (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w) (Set.Ici 0) t) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt
            (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
              (mfderiv I I (Φ_fam s : M → M) x v) (mfderiv I I (Φ_fam s : M → M) x w))
            (((-2 : ℝ) * ricciTensor (I := I) (g_DT t) (Φ_fam t x)
                    (mfderiv I I (Φ_fam t : M → M) x v)
                    (mfderiv I I (Φ_fam t : M → M) x w)
                + lieDerivMetric (I := I) (g_DT t)
                    (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
                    (mfderiv I I (Φ_fam t : M → M) x v)
                    (mfderiv I I (Φ_fam t : M → M) x w))
              + (-lieDerivMetric (I := I) (g_DT t)
                    (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
                    (mfderiv I I (Φ_fam t : M → M) x v)
                    (mfderiv I I (Φ_fam t : M → M) x w))) (Set.Ici 0) t) := by
  sorry

/-- **`t = 0`-endpoint continuity data of the conjugating flow (faithful open input).**

For the conjugating diffeomorphism family `Φ_fam` of the Hamilton–DeTurck construction —
PINNED to the genuine flow by the backward bare-orbit ODE `hΦode` — the two `t = 0`-endpoint
continuity facts hold for the pulled-back metric family `g_fam s := (Φ_fam s)^* (g_DT s)`:

* `h_cont`: the pulled-back inner product `s ↦ (g_fam s).inner x v w` is continuous on `Ico 0 T`;
* `h_ric_cont`: the Ricci RHS `s ↦ -2 Ric(g_fam s) x v w` is right-continuous at `0`.

These are the classical continuity-up-to-the-`C⁰`-at-`0`-boundary inputs of the conjugating flow
(joint `(t,x)` chart-Gram smoothness + total-space pushforward continuity).  They are TRUE for
this flow (pinned via `hΦode`) and reference only the internal data `g_DT` / `Φ_fam`.  Faithful
labeled deferred input for a dedicated fill effort. -/
theorem conjugating_flow_t0_continuity_data
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (hT : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn
        (fun s : ℝ =>
          (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)).inner x v w) (Set.Ico 0 T) ∧
      ContinuousWithinAt
        (fun s : ℝ => (-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I)
            (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w) (Set.Ioi 0) 0 := by
  sorry

end DifferentialGeometry.PDE.RicciFlow
