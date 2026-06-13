import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ComponentConvTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvBridge

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# P3 final assembly — Gap B → `metricPreconvInf` (MSM135 Ch3 `lbl351`)

This file assembles the covariant-tower component convergence into the spatial P3
endpoint `metricPreconvInf`.  It consumes (does NOT edit):

* `bumpTowerCarrier_all`, `hbase_of_framePairs`, `exists_frameData`,
  `exists_chart_engineInput_family` (`ComponentConvTower.lean`) — the all-orders
  bump-carrier convergence induction and its frame/base inputs;
* `metricPreconv_gInf`, `exists_engine_frameCInfConv(_eq_gm)`,
  `componentConv_covDeriv_zero`, `exists_diag_subseq` (`MetricPreconvDiag.lean`) —
  the limit metric `gInf` and the engine frame-component convergence;
* `metricDerivNorm_le_compSq_uniform`, `metricCInfConvOnCompacts_of_normConv`
  (`MetricPreconvBridge.lean`) — the norm bridge and the spatial endpoint.

The four assembly steps (ComponentConvTower.md "REMAINING"): (1) diagonal → one `φ`;
(2) limit-pinning; (3) feed `hbase_of_framePairs` → `bumpTowerCarrier_all`;
(4) finite-cover extraction → `componentConv_covDeriv_of_chartCInf` → `metricPreconvInf`.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection
open Tensor0SBundle TensorLieDeriv
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- **Finite-family `C∞`-on-compacts diagonal.**  Given a finite family of Euclidean
section sequences, each `ContDiff ⊤` with uniform iterated-derivative bounds on every
compact, one subsequence `φ` makes every member converge `C∞`-on-compacts (each to its
own limit).  Finite fold of `exists_cInf_subseq`, keeping earlier members convergent
under the further refinement via `MapCInfConvOnCompacts.comp_subseq`. -/
theorem exists_cInf_subseq_finiteFamily
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F]
    {ι : Type*} (s : Finset ι) (Φ : ι → ℕ → E → F)
    (hΦ : ∀ p ∈ s, ∀ k, ContDiff Real (⊤ : ℕ∞) (Φ p k))
    (hbdd : ∀ p ∈ s, ∀ r : ℕ, ∀ K : Set E, IsCompact K →
        ∃ Mr : Real, ∀ k, ∀ x ∈ K, ‖iteratedFDeriv Real r (Φ p k) x‖ ≤ Mr) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∀ p ∈ s,
      ∃ Φinf : E → F, MapCInfConvOnCompacts (Set.univ : Set E) (fun k => Φ p (φ k)) Φinf := by
  classical
  revert hΦ hbdd
  induction s using Finset.induction with
  | empty =>
    intro _ _
    exact ⟨id, strictMono_id, fun p hp => by simp at hp⟩
  | @insert a s ha IH =>
    intro hΦ hbdd
    obtain ⟨φ, hφ, hconv⟩ := IH (fun p hp => hΦ p (Finset.mem_insert_of_mem hp))
      (fun p hp => hbdd p (Finset.mem_insert_of_mem hp))
    obtain ⟨ψ, Φa, hψ, -, hΦaconv⟩ :=
      exists_cInf_subseq (fun k => Φ a (φ k))
        (fun k => hΦ a (Finset.mem_insert_self a s) (φ k))
        (fun r K hK => by
          obtain ⟨Mr, hMr⟩ := hbdd a (Finset.mem_insert_self a s) r K hK
          exact ⟨Mr, fun k x hx => hMr (φ k) x hx⟩)
    refine ⟨φ ∘ ψ, hφ.comp hψ, fun p hp => ?_⟩
    rcases Finset.mem_insert.mp hp with rfl | hps
    · exact ⟨Φa, hΦaconv⟩
    · obtain ⟨Φinf, hΦinf⟩ := hconv p hps
      exact ⟨Φinf, hΦinf.comp_subseq hψ⟩

end HCGCompactness
end DifferentialGeometry
