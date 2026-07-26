import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueClosure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ExtendedSolutionRegularity
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Connection
import DifferentialGeometry.Geometry.Connection.ChartBridge.MetricInverse

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Joint `(t, x)`-regularity of the forward-uniqueness energy density (brick TOWER)

`Evolution/ForwardUniqueClosure.lean` (K5) closes the Kotschwar forward-uniqueness argument
modulo one regularity package: the density
`forwardUniqueDensity g₁ g₂ t x = |h₀₂|² + |A₀₃|² + |S₀₄|²` must be jointly `C∞` in `(t, x)`
on `Ioo a c ×ˢ univ` (`hdens`), continuous in `x` at each fixed time (`hdcont`), and
integrable against the moving Riemannian volume (`hidens`, and the six companion slots).

This file supplies that layer.  The mathematical content is a **single structural brick**:

> the intrinsic fibre squared norm `normSq0S (g t) x s (A t x)` of a moving metric and a
> moving `(0,s)` tensor is jointly `C∞` as soon as (i) the chart inverse-Gram entries of the
> carrier are jointly `C∞` and (ii) the chart-frame components of `A` are jointly `C∞`.

Everything else is instantiation.  The brick is the joint-in-time upgrade of the spatial
`normSq0S_smooth` (`Tensor/RSTensor/MetricTrace/Connection.lean`): the same coordinate
expansion `normSq0S_eq_coord` against the chart basis `chartBasisFamily`, but with the
inverse metric supplied by `chartInvGramMatrix` (whose joint smoothness is proved here by
Cramer) rather than by the flat-model chart inverse.

## Main results

* `chartInvGram_jointContMDiffOn` — joint `C∞` of the chart inverse-Gram entries of a metric
  family, from the chart-Gram joint smoothness `hgram` (Cramer: `det⁻¹ · adjugate`).
* `normSq0S_jointContMDiffOn` — **the brick**.
* `metricDiffSq_jointContMDiffOn` — joint `C∞` of `|h₀₂|²_{g₁}`, unconditional in the two
  chart-Gram packages of `g₁` and `g₂`.  This is the metric third of `hdens`.
* `dens_jointContMDiffOn` — joint `C∞` of `forwardUniqueDensity`, i.e. K5's `hdens`, from the
  two chart-Gram packages plus the chart-frame component smoothness of the `A₀₃` and `S₀₄`
  carriers.
* `integrable_of_continuous` / `dens_integrable` / `dens_continuous` — K5's `hidens`,
  `hdcont` and the companion `Integrable` slots, from spatial continuity on the compact `M`.

## Honest status of the two remaining inputs

`dens_jointContMDiffOn` consumes the chart-frame component smoothness of `A₀₃` and `S₀₄`
(`hconn`, `hrm`) rather than deriving it.  These are *scalar chart-component* statements, one
level below the intrinsic goal, and the producing chain is identified but not built:

* `A₀₃`: `connDiffLowAt g₁ g₂ x (e_i, e_j, e_k) = ∑_m (Γ¹ − Γ²)^m_{ji} · G¹_{m k}` via
  `LeviCivita_chartBasisVec_alpha_basis_apply`
  (`Analysis/Elliptic/ConnectionLaplacian/ChartCoordinateExpansion/…`, valid on
  `chartLeviCivitaGoodSet`) plus `CovariantDerivative.difference` evaluated on the chart
  frame; the joint smoothness of `Γ` itself is `gen_joint_christoffel`
  (`Analysis/Parabolic/RicciLinearization/RicciDifferenceMeanValue.lean`), which needs the
  `GenJointGram` repackaging of `hgram` and a transport from `ℝ × E` back to `ℝ × M`.
* `S₀₄`: the same chain one derivative higher, through `gen_joint_riemann`, plus a chart
  reading of the *mixed* object `riemannCurvature04At g₁ (metricCov g₂)`.

See `ForwardUniqueDensReg.md`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]

/-! ## The joint chart inverse-Gram

Cramer's rule, transcribed from the spatial `chartInvGramMatrix_entry_contMDiffOn`
(`Geometry/Operator/Gradient.lean`) to the product source `ℝ × M`.  Only the entry
smoothness input changes: the spatial `chartGramMatrix_entry_contMDiffOn` is replaced by the
hypothesis `hgram`, which is exactly K5's chart-Gram package. -/

section JointInvGram

variable (g : ℝ → SmoothRiemannianMetric I M)

/-- **Joint `C∞` of the chart-Gram determinant** of a metric family. -/
theorem chartGramDet_jointContMDiffOn {J : Set ℝ} (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (chartGramMatrix (I := I) (g p.1) x₀ p.2).det)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  have hexp : (fun p : ℝ × M => (chartGramMatrix (I := I) (g p.1) x₀ p.2).det) =
      (fun p : ℝ × M => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        (Equiv.Perm.sign σ : ℝ) *
          ∏ k, chartGramMatrix (I := I) (g p.1) x₀ p.2 (σ k) k) := by
    funext p
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  exact contMDiffOn_finset_prod (fun k _ => hgram (σ k) k)

/-- **Joint `C∞` of the chart-Gram adjugate entries** of a metric family: an adjugate entry is
the determinant of a row-updated matrix, hence a polynomial in the Gram entries. -/
theorem chartGramAdj_jointContMDiffOn {J : Set ℝ} (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (chartGramMatrix (I := I) (g p.1) x₀ p.2).adjugate i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  have hexp : (fun p : ℝ × M => (chartGramMatrix (I := I) (g p.1) x₀ p.2).adjugate i j) =
      (fun p : ℝ × M => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        (Equiv.Perm.sign σ : ℝ) *
          ∏ k, (chartGramMatrix (I := I) (g p.1) x₀ p.2).updateRow j
              (Pi.single i (1 : ℝ)) (σ k) k) := by
    funext p
    rw [Matrix.adjugate_apply, Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finset_prod (fun k _ => ?_)
  by_cases hσk : σ k = j
  · have heq : (fun p : ℝ × M => (chartGramMatrix (I := I) (g p.1) x₀ p.2).updateRow j
        (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun _ : ℝ × M => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) i
          (1 : ℝ)) k) := by
      funext p
      rw [hσk, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · have heq : (fun p : ℝ × M => (chartGramMatrix (I := I) (g p.1) x₀ p.2).updateRow j
        (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 (σ k) k) := by
      funext p
      rw [Matrix.updateRow_ne hσk]
    rw [heq]
    exact hgram (σ k) k

/-- **Joint `C∞` of the chart inverse-Gram entries** of a metric family, from the chart-Gram
package.  Cramer's rule `G⁻¹ = (det G)⁻¹ · adj G`; the determinant is positive on the
trivialization base set because each `g t` is Riemannian. -/
theorem chartInvGram_jointContMDiffOn {J : Set ℝ} (x₀ : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => chartInvGramMatrix (I := I) (g p.1) x₀ p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  have hcongr : ∀ p ∈ J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet,
      chartInvGramMatrix (I := I) (g p.1) x₀ p.2 i j =
        ((chartGramMatrix (I := I) (g p.1) x₀ p.2).det)⁻¹ *
          (chartGramMatrix (I := I) (g p.1) x₀ p.2).adjugate i j := by
    rintro p ⟨-, hp⟩
    unfold chartInvGramMatrix
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) (g p.1) x₀ p.2).det •
            (chartGramMatrix (I := I) (g p.1) x₀ p.2).adjugate) i j = _
    rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    exact Ring.inverse_eq_inv _
  refine ContMDiffOn.congr ?_ hcongr
  refine ContMDiffOn.mul ?_ (chartGramAdj_jointContMDiffOn (I := I) g x₀ hgram i j)
  have hdet := chartGramDet_jointContMDiffOn (I := I) g x₀ hgram
  rintro p ⟨hpJ, hp⟩
  have hdet_ne : (chartGramMatrix (I := I) (g p.1) x₀ p.2).det ≠ 0 :=
    ne_of_gt (chartGramMatrix_det_pos (I := I) (g p.1) x₀ hp)
  exact (contDiffAt_inv _ hdet_ne).contMDiffAt.comp_contMDiffWithinAt p (hdet p ⟨hpJ, hp⟩)

end JointInvGram

/-! ## The structural brick: joint smoothness of a moving fibre norm -/

section JointNormSq

variable (g : ℝ → SmoothRiemannianMetric I M)

/-- **Joint `(t, x)`-smoothness of an intrinsic moving fibre squared norm.**

For a metric family `g` with jointly `C∞` chart-Gram entries and a `(0,s)`-tensor family `A`
whose chart-frame components are jointly `C∞`, the scalar `(t, x) ↦ |A t x|²_{g t}` is jointly
`C∞` on `J ×ˢ univ` (`J` open).

The proof is local: around any `(t₀, x₀)` the intrinsic norm agrees with the coordinate
contraction of `normSq0S_eq_coord` against the chart basis at `x₀`, whose inverse-metric
coefficients are the chart inverse-Gram entries (`chartInvGram_inverse`).  Both factors of
that finite sum are jointly `C∞` by hypothesis, so the sum is, and the eventual equality
transports smoothness back to the intrinsic norm.  This is the joint-in-time analogue of the
spatial `normSq0S_smooth`. -/
theorem normSq0S_jointContMDiffOn {J : Set ℝ} (hJ : IsOpen J) {s : ℕ}
    (A : ℝ → (x : M) → Tensor0SSpace s I x)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hA : ∀ (x₀ : M) (K : Fin s → Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M =>
          A p.1 p.2 (fun a : Fin s => chartBasisVecFiber (I := I) x₀ (K a) p.2))
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => normSq0S (I := I) (g p.1) p.2 s (A p.1 p.2))
      (J ×ˢ (Set.univ : Set M)) := by
  classical
  rintro q ⟨hqJ, -⟩
  set x₀ : M := q.2 with hx₀
  set e := trivializationAt E (TangentSpace I) x₀ with he
  have hqbase : q.2 ∈ e.baseSet := by
    rw [he, hx₀]
    exact FiberBundle.mem_baseSet_trivializationAt' q.2
  have hopen : IsOpen (J ×ˢ e.baseSet) := hJ.prod e.open_baseSet
  have hnhd : J ×ˢ e.baseSet ∈ nhds q := hopen.mem_nhds ⟨hqJ, hqbase⟩
  -- the coordinate contraction is jointly smooth at `q`
  have hsum : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        ∑ K : Fin s → Fin (Module.finrank ℝ E),
          ∑ L : Fin s → Fin (Module.finrank ℝ E),
            (∏ a : Fin s, chartInvGramMatrix (I := I) (g p.1) x₀ p.2 (K a) (L a)) *
              A p.1 p.2 (fun a : Fin s => chartBasisVecFiber (I := I) x₀ (K a) p.2) *
              A p.1 p.2 (fun a : Fin s => chartBasisVecFiber (I := I) x₀ (L a) p.2)) q := by
    refine ContMDiffAt.sum fun K _ => ContMDiffAt.sum fun L _ => ?_
    have hinvAt : ∀ k l : Fin (Module.finrank ℝ E),
        ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => chartInvGramMatrix (I := I) (g p.1) x₀ p.2 k l) q :=
      fun k l => (chartInvGram_jointContMDiffOn (I := I) g x₀ (hgram x₀) k l).contMDiffAt hnhd
    have hAAt : ∀ N : Fin s → Fin (Module.finrank ℝ E),
        ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M =>
            A p.1 p.2 (fun a : Fin s => chartBasisVecFiber (I := I) x₀ (N a) p.2)) q :=
      fun N => (hA x₀ N).contMDiffAt hnhd
    exact ((ContMDiffAt.prod fun a _ => hinvAt (K a) (L a)).mul (hAAt K)).mul (hAAt L)
  -- and it agrees with the intrinsic norm near `q`
  have heq : (fun p : ℝ × M => normSq0S (I := I) (g p.1) p.2 s (A p.1 p.2)) =ᶠ[nhds q]
      fun p : ℝ × M =>
        ∑ K : Fin s → Fin (Module.finrank ℝ E),
          ∑ L : Fin s → Fin (Module.finrank ℝ E),
            (∏ a : Fin s, chartInvGramMatrix (I := I) (g p.1) x₀ p.2 (K a) (L a)) *
              A p.1 p.2 (fun a : Fin s => chartBasisVecFiber (I := I) x₀ (K a) p.2) *
              A p.1 p.2 (fun a : Fin s => chartBasisVecFiber (I := I) x₀ (L a) p.2) := by
    filter_upwards [hnhd] with p hp
    have hpb : p.2 ∈ e.baseSet := hp.2
    rw [normSq0S_eq_coord (I := I) (g p.1) p.2 s (chartBasisFamily (I := I) x₀ hpb)
      (fun k l => chartInvGramMatrix (I := I) (g p.1) x₀ p.2 k l)
      (chartInvGram_inverse (I := I) (g p.1) x₀ hpb) (A p.1 p.2)]
    unfold coordInner0S
    refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun L _ => ?_
    rw [tensor0SComponent_apply, tensor0SComponent_apply]
    have hbas : ∀ N : Fin s → Fin (Module.finrank ℝ E),
        (fun a : Fin s => (chartBasisFamily (I := I) x₀ hpb) (N a)) =
          fun a : Fin s => chartBasisVecFiber (I := I) x₀ (N a) p.2 := by
      intro N
      funext a
      exact chartBasisFamily_apply (I := I) x₀ hpb (N a)
    rw [hbas K, hbas L]
  exact (hsum.congr_of_eventuallyEq heq).contMDiffWithinAt

end JointNormSq

/-! ## The metric third of the density

The chart-frame components of `h₀₂ = g₁ − g₂` are literally differences of chart-frame metric
components, so `metricFrameComp_jointContMDiffOn_of_chartGram` (`ExtendedSolutionRegularity`)
discharges the brick's second hypothesis outright. -/

section MetricDiff

variable (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)

/-- Chart-frame components of a metric family are jointly `C∞`: the chart basis vectors
`chartBasisVecFiber x₀` form a `C∞` local frame on the trivialization base set, so this is
`metricFrameComp_jointContMDiffOn_of_chartGram` read through
`Trivialization.localFrame_apply_of_mem_baseSet`. -/
theorem metricChartComp_jointContMDiffOn (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ}
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (g p.1).inner p.2
        (chartBasisVecFiber (I := I) x₀ i p.2) (chartBasisVecFiber (I := I) x₀ j p.2))
      (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  set e := trivializationAt E (TangentSpace I) x₀ with he
  have hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞)
      (e.localFrame (chartModelBasis E)) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) (chartModelBasis E)
  have hbridge : ∀ {x : M}, x ∈ e.baseSet → ∀ k : Fin (Module.finrank ℝ E),
      e.localFrame (chartModelBasis E) k x = chartBasisVecFiber (I := I) x₀ k x := by
    intro x hx k
    rw [e.localFrame_apply_of_mem_baseSet (chartModelBasis E) hx]
    rfl
  refine (metricFrameComp_jointContMDiffOn_of_chartGram (I := I) g a b hgram
    (e.localFrame (chartModelBasis E)) hframe i j).congr ?_
  intro p hp
  rw [hbridge hp.2 i, hbridge hp.2 j]

/-- **The metric third of `hdens`.**  `(t, x) ↦ |h₀₂|²_{g₁(t)}` is jointly `C∞` on
`Ioo a b ×ˢ univ` under the chart-Gram packages of the two flows.  Unconditional: the brick's
component hypothesis is discharged by `metricChartComp_jointContMDiffOn` on both metrics. -/
theorem metricDiffSq_jointContMDiffOn {a b : ℝ}
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => metricDiffSq (I := I) (g₁ p.1) (g₂ p.1) p.2)
      (Set.Ioo a b ×ˢ (Set.univ : Set M)) := by
  simp only [metricDiffSq_def]
  refine normSq0S_jointContMDiffOn (I := I) g₁ isOpen_Ioo
    (fun t x => metricDiffAt (I := I) (g₁ t) (g₂ t) x) hgram₁ ?_
  intro x₀ K
  have hsub : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        (g₁ p.1).inner p.2 (chartBasisVecFiber (I := I) x₀ (K 0) p.2)
            (chartBasisVecFiber (I := I) x₀ (K 1) p.2) -
          (g₂ p.1).inner p.2 (chartBasisVecFiber (I := I) x₀ (K 0) p.2)
            (chartBasisVecFiber (I := I) x₀ (K 1) p.2))
      (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    (metricChartComp_jointContMDiffOn (I := I) g₁ hgram₁ x₀ (K 0) (K 1)).sub
      (metricChartComp_jointContMDiffOn (I := I) g₂ hgram₂ x₀ (K 0) (K 1))
  refine hsub.congr ?_
  intro p _
  exact (metricDiffAt_apply (I := I) (g₁ p.1) (g₂ p.1) p.2
    (fun a : Fin 2 => chartBasisVecFiber (I := I) x₀ (K a) p.2)).symm

end MetricDiff

/-! ## The full density

The two remaining thirds consume chart-frame component smoothness of the connection- and
curvature-difference carriers.  See the module docstring for the identified producing chain. -/

section Density

variable (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)

/-- **The connection third of `hdens`,** conditional on the chart-frame component smoothness
of the `A₀₃` carrier. -/
theorem connDiffSq_jointContMDiffOn {a b : ℝ}
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hconn : ∀ (x₀ : M) (K : Fin 3 → Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => connDiffLowAt (I := I) (g₁ p.1) (g₂ p.1) p.2
          (fun a : Fin 3 => chartBasisVecFiber (I := I) x₀ (K a) p.2))
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => connDiffSq (I := I) (g₁ p.1) (g₂ p.1) p.2)
      (Set.Ioo a b ×ˢ (Set.univ : Set M)) := by
  simp only [connDiffSq_def]
  exact normSq0S_jointContMDiffOn (I := I) g₁ isOpen_Ioo
    (fun t x => connDiffLowAt (I := I) (g₁ t) (g₂ t) x) hgram₁ hconn

/-- **The curvature third of `hdens`,** conditional on the chart-frame component smoothness
of the `S₀₄` carrier. -/
theorem rmDiffSq_jointContMDiffOn {a b : ℝ}
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hrm : ∀ (x₀ : M) (K : Fin 4 → Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => rmDiffLowAt (I := I) (g₁ p.1) (g₂ p.1) p.2
          (fun a : Fin 4 => chartBasisVecFiber (I := I) x₀ (K a) p.2))
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => rmDiffSq (I := I) (g₁ p.1) (g₂ p.1) p.2)
      (Set.Ioo a b ×ˢ (Set.univ : Set M)) := by
  simp only [rmDiffSq_def]
  exact normSq0S_jointContMDiffOn (I := I) g₁ isOpen_Ioo
    (fun t x => rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) hgram₁ hrm

/-- **K5's `hdens`.**  Joint `C∞` of the Kotschwar energy density on `Ioo a b ×ˢ univ`.

The metric third is unconditional; the connection and curvature thirds consume the joint
`C∞` of the *chart-frame components* of `A₀₃` and `S₀₄` (`hconn`, `hrm`) — scalar statements
one level below the intrinsic goal, whose producing chain is recorded in the module
docstring and in `ForwardUniqueDensReg.md`. -/
theorem dens_jointContMDiffOn {a b : ℝ}
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hconn : ∀ (x₀ : M) (K : Fin 3 → Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => connDiffLowAt (I := I) (g₁ p.1) (g₂ p.1) p.2
          (fun a : Fin 3 => chartBasisVecFiber (I := I) x₀ (K a) p.2))
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hrm : ∀ (x₀ : M) (K : Fin 4 → Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => rmDiffLowAt (I := I) (g₁ p.1) (g₂ p.1) p.2
          (fun a : Fin 4 => chartBasisVecFiber (I := I) x₀ (K a) p.2))
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (Set.Ioo a b ×ˢ (Set.univ : Set M)) := by
  have h := ((metricDiffSq_jointContMDiffOn (I := I) g₁ g₂ hgram₁ hgram₂).add
    (connDiffSq_jointContMDiffOn (I := I) g₁ g₂ hgram₁ hconn)).add
    (rmDiffSq_jointContMDiffOn (I := I) g₁ g₂ hgram₁ hrm)
  exact h.congr fun p _ => rfl

end Density

/-! ## Spatial continuity and integrability

`M` is compact, so a continuous scalar is integrable against every Riemannian volume measure.
The density is a sum of three intrinsic fibre norms of *smooth* tensor fields, so the
`normSq0S_smooth` layer gives its spatial smoothness — hence continuity — directly. -/

section Integrability

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **The integrability producer.**  On a compact manifold every continuous scalar is
integrable against the moving Riemannian volume measure: the measure is finite on compacts
and the support is automatically compact.  This discharges every `Integrable …
(riemannianMeasureFamily g₁ t)` slot of K4/K5 from spatial continuity of the integrand. -/
theorem integrable_of_continuous (g : ℝ → SmoothRiemannianMetric I M) (t : ℝ)
    {f : M → ℝ} (hf : Continuous f) :
    Integrable f (riemannianMeasureFamily (I := I) (M := M) g t) := by
  haveI : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I) (M := M) (g t)) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) (g t)
  rw [riemannianMeasureFamily_def]
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Spatial smoothness of a fibre squared norm of a smooth `(0,s)` field, restated at the
`Continuous` level for the integrability slots. -/
theorem normSq0S_continuous {s : ℕ} (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Continuous (fun x : M => normSq0S (I := I) g x s (A x)) :=
  (normSq0S_smooth (I := I) g A).continuous

/-- **Spatial smoothness of the fibre pairing of two smooth `(0,s)` fields.**  Polarization
off `normSq0S_smooth`: `2⟨A, B⟩ = |A + B|² − |A|² − |B|²`.  This is the companion the
integrability slots need, since every one of them pairs two smooth carriers. -/
theorem inner0S_smooth {s : ℕ} (g : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun x : M => inner0S (I := I) g x s (A x) (B x)) := by
  have hfun : (fun x : M => inner0S (I := I) g x s (A x) (B x)) =
      fun x : M => (normSq0S (I := I) g x s ((A + B) x) -
        normSq0S (I := I) g x s (A x) - normSq0S (I := I) g x s (B x)) * (1 / 2 : ℝ) := by
    funext x
    have hsplit : (A + B) x = A x + B x := rfl
    rw [hsplit, normSq0S_add]
    ring
  rw [hfun]
  exact (((normSq0S_smooth (I := I) g (A + B)).sub (normSq0S_smooth (I := I) g A)).sub
    (normSq0S_smooth (I := I) g B)).mul contMDiff_const

/-- Fibre pairing of two smooth `(0,s)` fields, at the `Continuous` level. -/
theorem inner0S_continuous {s : ℕ} (g : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Continuous (fun x : M => inner0S (I := I) g x s (A x) (B x)) :=
  (inner0S_smooth (I := I) g A B).continuous

/-! ### The unconditional `Integrable` slots of K4/K5

Four of K5's eight integrability side conditions pair carriers that are `Tensor0SField`s —
smooth *by type* — so they need no extra hypothesis at all: `roughLap0SField`,
`covDiv0SField` and `metricNabla0S` all land back in `Tensor0SField … ∞`
(`Evolution/ForwardUniqueRmDiff.lean`).  The remaining four (`hipair`, `hirem`, `hirest`,
`hidens`) pair a bare pointwise family (`Sdot`, `rem`, `Adot`) or the density carriers, and
still need a continuity input. -/

section Slots

variable (g₁ : ℝ → SmoothRiemannianMetric I M)

/-- **K5's `hilap` slot**, unconditional. -/
theorem ilap_integrable (t : ℝ)
    (Sfield : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) :
    Integrable (fun x : M => inner0S (I := I) (g₁ t) x 4
        (roughLap0SField (I := I) (g₁ t) Sfield x) (Sfield x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t) :=
  integrable_of_continuous (I := I) g₁ t
    (inner0S_continuous (I := I) (g₁ t) (roughLap0SField (I := I) (g₁ t) Sfield) Sfield)

/-- **K5's `hidiv` slot**, unconditional. -/
theorem idiv_integrable (t : ℝ)
    (Sfield : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Uflux : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5) :
    Integrable (fun x : M => inner0S (I := I) (g₁ t) x 4
        (covDiv0SField (I := I) (g₁ t) Uflux x) (Sfield x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t) :=
  integrable_of_continuous (I := I) g₁ t
    (inner0S_continuous (I := I) (g₁ t) (covDiv0SField (I := I) (g₁ t) Uflux) Sfield)

/-- **K5's `hinab` slot**, unconditional. -/
theorem inab_integrable (t : ℝ)
    (Sfield : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Uflux : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5) :
    Integrable (fun x : M => inner0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) Sfield x) (Uflux x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t) :=
  integrable_of_continuous (I := I) g₁ t
    (inner0S_continuous (I := I) (g₁ t) (metricNabla0S (I := I) (g₁ t) Sfield) Uflux)

/-- **K5's `hidis` slot** (the dissipation integrand), unconditional. -/
theorem idis_integrable (t : ℝ)
    (Sfield : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) :
    Integrable (fun x : M => normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) Sfield x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t) :=
  integrable_of_continuous (I := I) g₁ t
    (normSq0S_continuous (I := I) (g₁ t) (metricNabla0S (I := I) (g₁ t) Sfield))

end Slots

/-- **K5's `hidens` from `hdcont`.**  Spatial continuity of the density at a fixed time makes
it integrable against the moving volume, on a compact manifold. -/
theorem dens_integrable (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ)
    (hdcont : Continuous (fun x : M => forwardUniqueDensity (I := I) g₁ g₂ t x)) :
    Integrable (fun x : M => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t) :=
  integrable_of_continuous (I := I) g₁ t hdcont

/-- **K5's `hdcont` from the joint package.**  A jointly `C∞` density on `Ioo a b ×ˢ univ` is
continuous in `x` at each interior time: restrict along the smooth slice `x ↦ (t, x)`. -/
theorem dens_continuous_of_joint (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {a b t : ℝ}
    (ht : t ∈ Set.Ioo a b)
    (hdens : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (Set.Ioo a b ×ˢ (Set.univ : Set M))) :
    Continuous (fun x : M => forwardUniqueDensity (I := I) g₁ g₂ t x) := by
  have hslice : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (fun x : M => (t, x)) :=
    contMDiff_const.prodMk contMDiff_id
  have hmaps : Set.MapsTo (fun x : M => (t, x)) Set.univ
      (Set.Ioo a b ×ˢ (Set.univ : Set M)) :=
    fun x _ => ⟨ht, Set.mem_univ x⟩
  have hcomp := hdens.comp hslice.contMDiffOn hmaps
  rw [contMDiffOn_univ] at hcomp
  exact hcomp.continuous

/-- **K5's `hdcont` and `hidens` on the open window, from `hdens` alone.**  Both edge inputs
of `metrics_eq_on` are consequences of the joint package at every *interior* time; the two
closed-edge times `a` and `c` are not covered and remain tied to a closed-slab version of
`hdens`. -/
theorem dcont_idens_of_joint (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {a b : ℝ}
    (hdens : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (Set.Ioo a b ×ˢ (Set.univ : Set M))) :
    (∀ t ∈ Set.Ioo a b, Continuous (fun x : M => forwardUniqueDensity (I := I) g₁ g₂ t x)) ∧
      ∀ t ∈ Set.Ioo a b, Integrable (fun x : M => forwardUniqueDensity (I := I) g₁ g₂ t x)
        (riemannianMeasureFamily (I := I) (M := M) g₁ t) :=
  ⟨fun _t ht => dens_continuous_of_joint (I := I) g₁ g₂ ht hdens,
    fun t ht => dens_integrable (I := I) g₁ g₂ t
      (dens_continuous_of_joint (I := I) g₁ g₂ ht hdens)⟩

end Integrability

end DifferentialGeometry.PDE.RicciFlow

end
