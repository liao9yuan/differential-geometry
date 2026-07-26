import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueClosure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ExtendedSolutionRegularity
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Connection
import DifferentialGeometry.Geometry.Connection.ChartBridge.MetricInverse
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue

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

The two carrier thirds `|A₀₃|²` and `|S₀₄|²` need one more layer: the *chart-frame scalar
components* of the connection- and curvature-difference carriers.  Those are supplied here by
composing the intrinsic chart bridges `LeviCivita_chartBasisVec_alpha_basis_apply` and
`riemannOp_chartBasisVec_alpha_eq` (valid on `chartLeviCivitaGoodSet α`) with the generic joint
Christoffel/Riemann tower `gen_joint_christoffel` / `gen_joint_riemann`
(`Analysis/Parabolic/RicciLinearization/RicciDifferenceMeanValue.lean`), transported from
`ℝ × E` back to `ℝ × M`.

## Main results

* `chartInvGram_jointContMDiffOn` — joint `C∞` of the chart inverse-Gram entries of a metric
  family, from the chart-Gram joint smoothness `hgram` (Cramer: `det⁻¹ · adjugate`).
* `normSq0S_jointContMDiffOn` — **the brick**.
* `connChartComp` / `rm04ChartComp` / `rmChartComp` — the chart-frame readings of `A₀₃`, of the
  *mixed* lowered curvature `riemannCurvature04At g₁ (metricCov g₂)`, and of `S₀₄`, all valid
  on `chartLeviCivitaGoodSet α`.
* `connChartJoint` / `rmChartJoint` — joint `(t, x)`-`C∞` of those chart-frame components,
  from the chart-Gram packages of the two flows alone.
* `metricDiffSq_jointContMDiffOn`, `connDiffSq_jointContMDiffOn`, `rmDiffSq_jointContMDiffOn`,
  `dens_jointContMDiffOn` — the three thirds and K5's `hdens`, each consuming **only** the two
  chart-Gram packages.
* `integrable_of_continuous` / `dens_continuous` / `dcont_idens` — K5's `hdcont` and `hidens`
  at *every* time (closed edges included), unconditionally, plus the companion `Integrable`
  slots.

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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

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

The proof is local: around any `(t, x₀)` the intrinsic norm agrees with the coordinate
contraction of `normSq0S_eq_coord` against the chart basis at `x₀`, whose inverse-metric
coefficients are the chart inverse-Gram entries (`chartInvGram_inverse`).  Both factors of
that finite sum are jointly `C∞` by hypothesis, so the sum is, and the eventual equality
transports smoothness back to the intrinsic norm.  This is the joint-in-time analogue of the
spatial `normSq0S_smooth`.

The component hypothesis `hA` is only ever used *at the diagonal point* `(t, x₀)` with the
chart centred at `x₀`, so it is stated in that (weakest) pointwise form: producers whose chart
identity is valid only on a neighbourhood of the chart centre — such as the connection- and
curvature-difference carriers, valid on `chartLeviCivitaGoodSet x₀` rather than on the whole
trivialization base set — feed it without any restriction juggling. -/
theorem normSq0S_jointContMDiffOn {J : Set ℝ} (hJ : IsOpen J) {s : ℕ}
    (A : ℝ → (x : M) → Tensor0SSpace s I x)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hA : ∀ (x₀ : M) (K : Fin s → Fin (Module.finrank ℝ E)) {t : ℝ}, t ∈ J →
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M =>
          A p.1 p.2 (fun a : Fin s => chartBasisVecFiber (I := I) x₀ (K a) p.2)) (t, x₀)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => normSq0S (I := I) (g p.1) p.2 s (A p.1 p.2))
      (J ×ˢ (Set.univ : Set M)) := by
  classical
  rintro ⟨t, x₀⟩ ⟨htJ, -⟩
  set e := trivializationAt E (TangentSpace I) x₀ with he
  have hqbase : x₀ ∈ e.baseSet := by
    rw [he]
    exact FiberBundle.mem_baseSet_trivializationAt' x₀
  have hopen : IsOpen (J ×ˢ e.baseSet) := hJ.prod e.open_baseSet
  have hnhd : J ×ˢ e.baseSet ∈ nhds ((t, x₀) : ℝ × M) := hopen.mem_nhds ⟨htJ, hqbase⟩
  -- the coordinate contraction is jointly smooth at `(t, x₀)`
  have hsum : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        ∑ K : Fin s → Fin (Module.finrank ℝ E),
          ∑ L : Fin s → Fin (Module.finrank ℝ E),
            (∏ a : Fin s, chartInvGramMatrix (I := I) (g p.1) x₀ p.2 (K a) (L a)) *
              A p.1 p.2 (fun a : Fin s => chartBasisVecFiber (I := I) x₀ (K a) p.2) *
              A p.1 p.2 (fun a : Fin s => chartBasisVecFiber (I := I) x₀ (L a) p.2))
      ((t, x₀) : ℝ × M) := by
    refine ContMDiffAt.sum fun K _ => ContMDiffAt.sum fun L _ => ?_
    have hinvAt : ∀ k l : Fin (Module.finrank ℝ E),
        ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => chartInvGramMatrix (I := I) (g p.1) x₀ p.2 k l)
          ((t, x₀) : ℝ × M) :=
      fun k l => (chartInvGram_jointContMDiffOn (I := I) g x₀ (hgram x₀) k l).contMDiffAt hnhd
    have hAAt : ∀ N : Fin s → Fin (Module.finrank ℝ E),
        ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M =>
            A p.1 p.2 (fun a : Fin s => chartBasisVecFiber (I := I) x₀ (N a) p.2))
          ((t, x₀) : ℝ × M) :=
      fun N => hA x₀ N htJ
    exact ((ContMDiffAt.prod fun a _ => hinvAt (K a) (L a)).mul (hAAt K)).mul (hAAt L)
  -- and it agrees with the intrinsic norm near `(t, x₀)`
  have heq : (fun p : ℝ × M => normSq0S (I := I) (g p.1) p.2 s (A p.1 p.2))
      =ᶠ[nhds ((t, x₀) : ℝ × M)]
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
  intro x₀ K t ht
  have hsub : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        (g₁ p.1).inner p.2 (chartBasisVecFiber (I := I) x₀ (K 0) p.2)
            (chartBasisVecFiber (I := I) x₀ (K 1) p.2) -
          (g₂ p.1).inner p.2 (chartBasisVecFiber (I := I) x₀ (K 0) p.2)
            (chartBasisVecFiber (I := I) x₀ (K 1) p.2))
      (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    (metricChartComp_jointContMDiffOn (I := I) g₁ hgram₁ x₀ (K 0) (K 1)).sub
      (metricChartComp_jointContMDiffOn (I := I) g₂ hgram₂ x₀ (K 0) (K 1))
  have hnhd : Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet ∈
      nhds ((t, x₀) : ℝ × M) :=
    (isOpen_Ioo.prod (trivializationAt E (TangentSpace I) x₀).open_baseSet).mem_nhds
      ⟨ht, FiberBundle.mem_baseSet_trivializationAt' x₀⟩
  refine ContMDiffOn.contMDiffAt (hsub.congr ?_) hnhd
  intro p _
  exact (metricDiffAt_apply (I := I) (g₁ p.1) (g₂ p.1) p.2
    (fun a : Fin 2 => chartBasisVecFiber (I := I) x₀ (K a) p.2)).symm

end MetricDiff

/-! ## Chart-frame components of the connection- and curvature-difference carriers

The two carrier thirds are read on the chart-`α` frame `e^α_· x` through the intrinsic chart
bridges, which are valid on `chartLeviCivitaGoodSet α` (an open neighbourhood of `α`, contained
in the trivialization base set).  All three identities below are generic: an arbitrary point,
an arbitrary pair of metrics. -/

section ChartComponents

/-- Linearity of the fibre metric in its first slot, over a finite `smul`-sum. -/
private theorem inner_sum_left (g : SmoothRiemannianMetric I M) (x : M)
    (c : Fin (Module.finrank ℝ E) → ℝ) (w : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (u : TangentSpace I x) :
    g.inner x (∑ m, c m • w m) u = ∑ m, c m * g.inner x (w m) u := by
  classical
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Linearity of the fibre metric in its second slot, over a finite `smul`-sum. -/
private theorem inner_sum_right (g : SmoothRiemannianMetric I M) (x : M)
    (u : TangentSpace I x)
    (c : Fin (Module.finrank ℝ E) → ℝ) (w : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    g.inner x u (∑ m, c m • w m) = ∑ m, c m * g.inner x u (w m) := by
  classical
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, smul_eq_mul]

/-- **Chart-frame components of `A₀₃`.**  On `chartLeviCivitaGoodSet α`, the `g₁`-lowered
connection difference read on the chart-`α` frame is the Christoffel difference contracted with
the chart Gram of the lowering metric:
`A₀₃(e_{K0}, e_{K1}, e_{K2}) = ∑_m (Γ¹ − Γ²)^m_{K0 K1}(ϕ_α x) · G¹_{m, K2}(x)`. -/
theorem connChartComp (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (K : Fin 3 → Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    connDiffLowAt (I := I) g₁ g₂ x
        (fun a : Fin 3 => chartBasisVecFiber (I := I) α (K a) x) =
      ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g₁ α (K 0) (K 1) m (extChartAt I α x) -
            chartChristoffel (I := I) g₂ α (K 0) (K 1) m (extChartAt I α x)) *
          chartGramMatrix (I := I) g₁ α x m (K 2) := by
  classical
  have hd := IsCovariantDerivativeOn.difference_apply
    (hcov := (metricCov (I := I) g₁).isCovariantDerivativeOnUniv)
    (hcov' := (metricCov (I := I) g₂).isCovariantDerivativeOnUniv)
    (σ := fun b : M => chartBasisVecFiber (I := I) α (K 1) b) (x := x) (hx := by trivial)
    (chartBasisVec_alpha_mdifferentiableAt (I := I) α (K 1) hx)
  have hd' :
      CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x
          (chartBasisVecFiber (I := I) α (K 1) x)
          (chartBasisVecFiber (I := I) α (K 0) x) =
        (metricCov (I := I) g₁) (fun b : M => chartBasisVecFiber (I := I) α (K 1) b) x
            (chartBasisVecFiber (I := I) α (K 0) x) -
          (metricCov (I := I) g₂) (fun b : M => chartBasisVecFiber (I := I) α (K 1) b) x
            (chartBasisVecFiber (I := I) α (K 0) x) := by
    have h := congrArg
      (fun L : TangentSpace I x →L[ℝ] TangentSpace I x =>
        L (chartBasisVecFiber (I := I) α (K 0) x)) hd
    simpa using h
  have hLC₁ : metricCov (I := I) g₁ = LeviCivita (I := I) g₁ := rfl
  have hLC₂ : metricCov (I := I) g₂ = LeviCivita (I := I) g₂ := rfl
  simp only [connDiffLowAt_apply]
  rw [hd', hLC₁, hLC₂,
    LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g₁ α (K 0) (K 1) hx,
    LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g₂ α (K 0) (K 1) hx,
    ← Finset.sum_sub_distrib]
  rw [show (∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g₁ α (K 0) (K 1) m (extChartAt I α x) •
            chartBasisVecFiber (I := I) α m x -
          chartChristoffel (I := I) g₂ α (K 0) (K 1) m (extChartAt I α x) •
            chartBasisVecFiber (I := I) α m x)) =
      ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g₁ α (K 0) (K 1) m (extChartAt I α x) -
            chartChristoffel (I := I) g₂ α (K 0) (K 1) m (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α m x from
    Finset.sum_congr rfl fun m _ => (sub_smul _ _ _).symm]
  rw [inner_sum_left]
  exact Finset.sum_congr rfl fun m _ => by rw [chartGramMatrix_apply]

/-- **Chart-frame components of the mixed lowered curvature.**  The Riemann tensor of the
*second* metric's Levi-Civita connection, lowered by the *first* metric, read on the chart-`α`
frame:
`⟨Rm(∇²)(e_j, e_k) e_i, e_n⟩_{g₁} = ∑_l R²^l{}_{ijk}(ϕ_α x) · G¹_{n, l}(x)`.
This is the one carrier reading with no pre-existing chart lemma; taking `g₂ := g₁` also gives
the diagonal case `metricRm04At g₁`. -/
theorem rm04ChartComp (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i j k n : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
        (metricCov_smooth (I := I) g₂) x
        (vec4 (I := I) (chartBasisVecFiber (I := I) α j x) (chartBasisVecFiber (I := I) α k x)
          (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α n x)) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) g₂ α i j k l (extChartAt I α x) *
          chartGramMatrix (I := I) g₁ α x n l := by
  classical
  haveI : CovariantDerivative.ContMDiffCovariantDerivative
      (metricCov (I := I) g₂) (∞ : WithTop ℕ∞) := LeviCivita_isContMDiff (I := I) g₂
  rw [CovariantDerivative.riemannCurvature04At_apply_const,
    riemannCurvatureAux_tangentConst_eq_riemannOp (metricCov (I := I) g₂)
      (metricCov_smooth (I := I) g₂) x _ _ _,
    show riemannOp (cov := metricCov (I := I) g₂) x
          (chartBasisVecFiber (I := I) α j x) (chartBasisVecFiber (I := I) α k x)
          (chartBasisVecFiber (I := I) α i x)
        = riemannOp (cov := LeviCivita (I := I) g₂) x
          (chartBasisVecFiber (I := I) α j x) (chartBasisVecFiber (I := I) α k x)
          (chartBasisVecFiber (I := I) α i x) from rfl,
    riemannOp_chartBasisVec_alpha_eq (I := I) g₂ α i j k hx, inner_sum_right]
  exact Finset.sum_congr rfl fun l _ => by rw [chartGramMatrix_apply]

/-- **Chart-frame components of `S₀₄`.**  Both terms of the curvature difference are read by
`rm04ChartComp`, the first with `g₂ := g₁`. -/
theorem rmChartComp (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (K : Fin 4 → Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    rmDiffLowAt (I := I) g₁ g₂ x
        (fun a : Fin 4 => chartBasisVecFiber (I := I) α (K a) x) =
      ∑ l : Fin (Module.finrank ℝ E),
        (chartRiemannTensor (I := I) g₁ α (K 2) (K 0) (K 1) l (extChartAt I α x) -
            chartRiemannTensor (I := I) g₂ α (K 2) (K 0) (K 1) l (extChartAt I α x)) *
          chartGramMatrix (I := I) g₁ α x (K 3) l := by
  classical
  have hvec : (fun a : Fin 4 => chartBasisVecFiber (I := I) α (K a) x) =
      vec4 (I := I) (chartBasisVecFiber (I := I) α (K 0) x)
        (chartBasisVecFiber (I := I) α (K 1) x) (chartBasisVecFiber (I := I) α (K 2) x)
        (chartBasisVecFiber (I := I) α (K 3) x) := by
    funext a
    fin_cases a <;> rfl
  rw [hvec, rmDiffLowAt_apply,
    show metricRm04At (I := I) g₁ x =
        CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₁)
          (metricCov_smooth (I := I) g₁) x from rfl,
    rm04ChartComp (I := I) g₁ g₁ α (K 2) (K 0) (K 1) (K 3) hx,
    rm04ChartComp (I := I) g₁ g₂ α (K 2) (K 0) (K 1) (K 3) hx,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun l _ => (sub_mul _ _ _).symm

end ChartComponents

/-! ## Joint smoothness of the carrier components

The chart-frame components are finite polynomials in the chart Christoffel/Riemann symbols of
the two flows and in the chart Gram of the lowering metric.  The joint `(t, x)`-smoothness of
the former is the generic tower `gen_joint_christoffel` / `gen_joint_riemann`, living on
`ℝ × E`; it is fed by repackaging the chart-Gram hypothesis as `GenJointGram` and transported
back to `ℝ × M` along `extChartAt`. -/

section JointChart

/-- The chart-Gram package of a metric family, repackaged as the `GenJointGram` hypothesis
bundle of the generic joint Christoffel/Riemann tower.  Only the transport `ℝ × M → ℝ × E` is
performed here; the Gram determinant positivity is unconditional. -/
private theorem genGram_of_joint (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hJ : IsOpen J) (α : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) α p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    GenJointGram (I := I) g α J := by
  classical
  refine ⟨?_, ?_⟩
  · intro i j s₀ y₀ hs hy
    set e := trivializationAt E (TangentSpace I) α with he
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm (extChartAt I α).target :=
      contMDiffOn_extChartAt_symm (I := I) α
    have hsubset : (extChartAt I α).target ⊆ (extChartAt I α).symm ⁻¹' e.baseSet := by
      intro y hy'
      have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy'
      rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
      rw [he, trivializationAt_baseSet_eq_chartAt_source]
      exact hsource
    have hσ1 : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => p.1) (J ×ˢ interior (extChartAt I α).target) :=
      (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffOn
    have hsnd : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) ∞
        (fun p : ℝ × E => p.2) (J ×ˢ interior (extChartAt I α).target) :=
      (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffOn
    have hmaps2 : Set.MapsTo (fun p : ℝ × E => p.2)
        (J ×ˢ interior (extChartAt I α).target) (extChartAt I α).target :=
      fun p hp => interior_subset hp.2
    have hσ2 : ContMDiffOn 𝓘(ℝ, ℝ × E) I ∞
        (fun p : ℝ × E => (extChartAt I α).symm p.2)
        (J ×ˢ interior (extChartAt I α).target) :=
      hsymm.comp hsnd hmaps2
    have hσ : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : ℝ × E => (p.1, (extChartAt I α).symm p.2))
        (J ×ˢ interior (extChartAt I α).target) :=
      hσ1.prodMk hσ2
    have hcomp : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => chartGramOnE (I := I) (g p.1) α i j p.2)
        (J ×ˢ interior (extChartAt I α).target) := by
      refine ((hgram i j).comp hσ (fun p hp => ⟨hp.1, hsubset (interior_subset hp.2)⟩)).congr ?_
      intro p _
      rfl
    exact hcomp.contDiffOn.contDiffAt
      (prod_mem_nhds (hJ.mem_nhds hs) (isOpen_interior.mem_nhds hy))
  · intro s₀ _ x hx
    exact chartGramMatrix_det_pos (I := I) (g s₀) α hx

/-- Transport of a joint `ℝ × E` chart-scalar smoothness statement back to the manifold source
`ℝ × M`, along `(t, x) ↦ (t, ϕ_α x)`. -/
private theorem jointOnM (α : M) (F : ℝ → E → ℝ) {t : ℝ} {x : M}
    (hF : ContDiffAt ℝ ∞ (fun r : ℝ × E => F r.1 r.2) (t, extChartAt I α x))
    (hx : x ∈ (chartAt H α).source) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => F p.1 (extChartAt I α p.2)) (t, x) := by
  have hchart : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun y : M => extChartAt I α y) x :=
    (contMDiffOn_extChartAt (I := I) (x := α) (n := ∞)).contMDiffAt
      ((chartAt H α).open_source.mem_nhds hx)
  have hmove : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞
      (fun p : ℝ × M => (p.1, extChartAt I α p.2)) (t, x) := by
    have hfst : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => p.1) ((t, x) : ℝ × M) := contMDiffAt_fst
    have h := hfst.prodMk (hchart.comp ((t, x) : ℝ × M) contMDiffAt_snd)
    rwa [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  simpa using hF.contMDiffAt.comp ((t, x) : ℝ × M) hmove

/-- Joint `(t, x)`-`C∞` of a chart Christoffel symbol of a metric family, on `ℝ × M`. -/
private theorem christJoint (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (α : M) (hG : GenJointGram (I := I) g α J)
    (i j k : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ J) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => chartChristoffel (I := I) (g p.1) α i j k (extChartAt I α p.2))
      (t, x) :=
  jointOnM (I := I) α (fun s y => chartChristoffel (I := I) (g s) α i j k y)
    (gen_joint_christoffel (I := I) g α hG i j k ht
      (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx))
    (by
      have h := (mem_chartLeviCivitaGoodSet_iff.mp hx).1
      rwa [extChartAt_source] at h)

/-- Joint `(t, x)`-`C∞` of a chart Riemann coefficient of a metric family, on `ℝ × M`. -/
private theorem riemJoint (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (α : M) (hG : GenJointGram (I := I) g α J)
    (i j k l : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ J) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => chartRiemannTensor (I := I) (g p.1) α i j k l (extChartAt I α p.2))
      (t, x) :=
  jointOnM (I := I) α (fun s y => chartRiemannTensor (I := I) (g s) α i j k l y)
    (gen_joint_riemann (I := I) g α hG i j k l ht
      (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx))
    (by
      have h := (mem_chartLeviCivitaGoodSet_iff.mp hx).1
      rwa [extChartAt_source] at h)

/-- **The `A₀₃` component input of the brick**, discharged: the chart-frame components of the
connection-difference carrier are jointly `C∞` at `(t, x₀)`, from the two chart-Gram packages
at `x₀`. -/
theorem connChartJoint (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (hJ : IsOpen J)
    (x₀ : M)
    (hgram₁ : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (K : Fin 3 → Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ J) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => connDiffLowAt (I := I) (g₁ p.1) (g₂ p.1) p.2
        (fun a : Fin 3 => chartBasisVecFiber (I := I) x₀ (K a) p.2)) (t, x₀) := by
  classical
  have hG₁ := genGram_of_joint (I := I) g₁ hJ x₀ hgram₁
  have hG₂ := genGram_of_joint (I := I) g₂ hJ x₀ hgram₂
  have hgood : x₀ ∈ chartLeviCivitaGoodSet (I := I) x₀ :=
    self_mem_chartLeviCivitaGoodSet (I := I) x₀
  have hnhdB : J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet ∈ nhds ((t, x₀) : ℝ × M) :=
    (hJ.prod (trivializationAt E (TangentSpace I) x₀).open_baseSet).mem_nhds
      ⟨ht, FiberBundle.mem_baseSet_trivializationAt' x₀⟩
  have hΦ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) (g₁ p.1) x₀ (K 0) (K 1) m (extChartAt I x₀ p.2) -
            chartChristoffel (I := I) (g₂ p.1) x₀ (K 0) (K 1) m (extChartAt I x₀ p.2)) *
          chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 m (K 2)) ((t, x₀) : ℝ × M) := by
    refine ContMDiffAt.sum fun m _ => ?_
    exact ((christJoint (I := I) g₁ x₀ hG₁ (K 0) (K 1) m ht hgood).sub
      (christJoint (I := I) g₂ x₀ hG₂ (K 0) (K 1) m ht hgood)).mul
      ((hgram₁ m (K 2)).contMDiffAt hnhdB)
  refine hΦ.congr_of_eventuallyEq ?_
  have hnhdG : (Set.univ : Set ℝ) ×ˢ chartLeviCivitaGoodSet (I := I) x₀ ∈
      nhds ((t, x₀) : ℝ × M) :=
    (isOpen_univ.prod (chartLeviCivitaGoodSet_isOpen (I := I) x₀)).mem_nhds
      ⟨Set.mem_univ t, hgood⟩
  filter_upwards [hnhdG] with p hp
  exact connChartComp (I := I) (g₁ p.1) (g₂ p.1) x₀ K hp.2

/-- **The `S₀₄` component input of the brick**, discharged: the chart-frame components of the
curvature-difference carrier are jointly `C∞` at `(t, x₀)`, from the two chart-Gram packages
at `x₀`. -/
theorem rmChartJoint (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (hJ : IsOpen J)
    (x₀ : M)
    (hgram₁ : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (K : Fin 4 → Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ J) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => rmDiffLowAt (I := I) (g₁ p.1) (g₂ p.1) p.2
        (fun a : Fin 4 => chartBasisVecFiber (I := I) x₀ (K a) p.2)) (t, x₀) := by
  classical
  have hG₁ := genGram_of_joint (I := I) g₁ hJ x₀ hgram₁
  have hG₂ := genGram_of_joint (I := I) g₂ hJ x₀ hgram₂
  have hgood : x₀ ∈ chartLeviCivitaGoodSet (I := I) x₀ :=
    self_mem_chartLeviCivitaGoodSet (I := I) x₀
  have hnhdB : J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet ∈ nhds ((t, x₀) : ℝ × M) :=
    (hJ.prod (trivializationAt E (TangentSpace I) x₀).open_baseSet).mem_nhds
      ⟨ht, FiberBundle.mem_baseSet_trivializationAt' x₀⟩
  have hΦ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ∑ l : Fin (Module.finrank ℝ E),
        (chartRiemannTensor (I := I) (g₁ p.1) x₀ (K 2) (K 0) (K 1) l (extChartAt I x₀ p.2) -
            chartRiemannTensor (I := I) (g₂ p.1) x₀ (K 2) (K 0) (K 1) l
              (extChartAt I x₀ p.2)) *
          chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 (K 3) l) ((t, x₀) : ℝ × M) := by
    refine ContMDiffAt.sum fun l _ => ?_
    exact ((riemJoint (I := I) g₁ x₀ hG₁ (K 2) (K 0) (K 1) l ht hgood).sub
      (riemJoint (I := I) g₂ x₀ hG₂ (K 2) (K 0) (K 1) l ht hgood)).mul
      ((hgram₁ (K 3) l).contMDiffAt hnhdB)
  refine hΦ.congr_of_eventuallyEq ?_
  have hnhdG : (Set.univ : Set ℝ) ×ˢ chartLeviCivitaGoodSet (I := I) x₀ ∈
      nhds ((t, x₀) : ℝ × M) :=
    (isOpen_univ.prod (chartLeviCivitaGoodSet_isOpen (I := I) x₀)).mem_nhds
      ⟨Set.mem_univ t, hgood⟩
  filter_upwards [hnhdG] with p hp
  exact rmChartComp (I := I) (g₁ p.1) (g₂ p.1) x₀ K hp.2

end JointChart

/-! ## The full density

All three thirds now consume exactly the two chart-Gram packages. -/

section Density

variable (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)

/-- **The connection third of `hdens`.**  Joint `C∞` of `|A₀₃|²_{g₁(t)}` on `Ioo a b ×ˢ univ`
under the chart-Gram packages of the two flows. -/
theorem connDiffSq_jointContMDiffOn {a b : ℝ}
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => connDiffSq (I := I) (g₁ p.1) (g₂ p.1) p.2)
      (Set.Ioo a b ×ˢ (Set.univ : Set M)) := by
  simp only [connDiffSq_def]
  refine normSq0S_jointContMDiffOn (I := I) g₁ isOpen_Ioo
    (fun t x => connDiffLowAt (I := I) (g₁ t) (g₂ t) x) hgram₁ ?_
  intro x₀ K t ht
  exact connChartJoint (I := I) g₁ g₂ isOpen_Ioo x₀ (hgram₁ x₀) (hgram₂ x₀) K ht

/-- **The curvature third of `hdens`.**  Joint `C∞` of `|S₀₄|²_{g₁(t)}` on `Ioo a b ×ˢ univ`
under the chart-Gram packages of the two flows. -/
theorem rmDiffSq_jointContMDiffOn {a b : ℝ}
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => rmDiffSq (I := I) (g₁ p.1) (g₂ p.1) p.2)
      (Set.Ioo a b ×ˢ (Set.univ : Set M)) := by
  simp only [rmDiffSq_def]
  refine normSq0S_jointContMDiffOn (I := I) g₁ isOpen_Ioo
    (fun t x => rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) hgram₁ ?_
  intro x₀ K t ht
  exact rmChartJoint (I := I) g₁ g₂ isOpen_Ioo x₀ (hgram₁ x₀) (hgram₂ x₀) K ht

/-- **K5's `hdens`.**  Joint `C∞` of the Kotschwar energy density on `Ioo a b ×ˢ univ`, from
the chart-Gram packages of the two flows and nothing else. -/
theorem dens_jointContMDiffOn {a b : ℝ}
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (Set.Ioo a b ×ˢ (Set.univ : Set M)) := by
  have h := ((metricDiffSq_jointContMDiffOn (I := I) g₁ g₂ hgram₁ hgram₂).add
    (connDiffSq_jointContMDiffOn (I := I) g₁ g₂ hgram₁ hgram₂)).add
    (rmDiffSq_jointContMDiffOn (I := I) g₁ g₂ hgram₁ hgram₂)
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

/-- **K5's `hdcont` at every time, unconditionally.**  At a *fixed* time the density depends
only on the two static metrics `g₁ t`, `g₂ t`, so the joint package applied to the two constant
families needs no time-regularity input at all: the chart-Gram hypothesis degenerates to the
spatial `chartGramMatrix_entry_contMDiffOn`.  This covers the closed edges that the joint
statement on `Ioo a b` misses. -/
theorem dens_continuous (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ) :
    Continuous (fun x : M => forwardUniqueDensity (I := I) g₁ g₂ t x) := by
  have hconst : ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) g x₀ p.2 i j)
        (Set.Ioo (t - 1) (t + 1) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro g x₀ i j
    have hsnd : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => p.2)
        (Set.Ioo (t - 1) (t + 1) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
      contMDiffOn_snd
    exact (chartGramMatrix_entry_contMDiffOn (I := I) g x₀ i j).comp hsnd fun p hp => hp.2
  have ht : t ∈ Set.Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hcont := dens_continuous_of_joint (I := I) (fun _ => g₁ t) (fun _ => g₂ t) ht
    (dens_jointContMDiffOn (I := I) (fun _ => g₁ t) (fun _ => g₂ t)
      (fun x₀ i j => hconst (g₁ t) x₀ i j) (fun x₀ i j => hconst (g₂ t) x₀ i j))
  have hfun :
      (fun x : M => forwardUniqueDensity (I := I) (fun _ => g₁ t) (fun _ => g₂ t) t x) =
        fun x : M => forwardUniqueDensity (I := I) g₁ g₂ t x := rfl
  rwa [hfun] at hcont

/-- **K5's `hdcont` and `hidens` at every time, unconditionally.**  Both edge inputs of
`metrics_eq_on` — including the closed-edge times that the `Ioo` joint statement misses. -/
theorem dcont_idens (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ) :
    Continuous (fun x : M => forwardUniqueDensity (I := I) g₁ g₂ t x) ∧
      Integrable (fun x : M => forwardUniqueDensity (I := I) g₁ g₂ t x)
        (riemannianMeasureFamily (I := I) (M := M) g₁ t) :=
  ⟨dens_continuous (I := I) g₁ g₂ t,
    dens_integrable (I := I) g₁ g₂ t (dens_continuous (I := I) g₁ g₂ t)⟩

end Integrability

end DifferentialGeometry.PDE.RicciFlow

end
