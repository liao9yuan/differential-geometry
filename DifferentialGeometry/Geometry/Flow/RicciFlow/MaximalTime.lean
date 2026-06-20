import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CinftyLimitGlue
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BBSLimitProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ExtendedSolutionRegularity
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Basic
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Coordinate
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Product
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Smooth
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import Mathlib.Analysis.Calculus.FDeriv.Extend

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Maximal and Singular Times for Ricci Flow

This file records the interval-changing definitions needed for the appendix
maximal-time discussion.  The genuine theorem that singularity is equivalent
to maximality remains a global extension-criterion frontier.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]

/-- Two interval solutions agree on `U` when their stored metric, connection,
and Ricci data agree at every time in `U`.  Ricci equality is explicit because
the current solution predicate does not prove Ricci is uniquely reconstructed
from the metric. -/
def SolutionAgreesOn
    {D Dhat : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Shat : SolutionOn (I := I) (M := M) Dhat)
    (U : Set Real) : Prop :=
  forall t : Real, t ∈ U ->
    S.family.metric t = Shat.family.metric t ∧
      S.family.connection t = Shat.family.connection t ∧
        S.ricci t = Shat.ricci t

/-- The solution on `[alpha, omega)` extends as a Ricci flow past `omega`. -/
def ExtendsPastEndpoint
    {alpha omega : Real} (hαω : alpha < omega)
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)) : Prop :=
  ∃ eps : Real, 0 < eps ∧
    ∃ hwide : alpha < omega + eps,
      ∃ Shat : SolutionOn (I := I) (M := M)
        (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha (omega + eps) hwide),
        IsSolutionOn (I := I) Shat ∧
          SolutionAgreesOn (I := I) S Shat (Set.Ico alpha omega)

/-- The solution on `[alpha, omega)` is maximal at its finite endpoint. -/
def IsMaximalAtEndpoint
    {alpha omega : Real} (hαω : alpha < omega)
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)) : Prop :=
  ¬ ExtendsPastEndpoint (I := I) hαω S

/-- A time-indexed lowered Riemann tensor realizes the solution curvature on
the interval where the solution is defined. -/
def Rm04RealizesSolutionConnectionOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M)) : Prop :=
  forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D,
    DifferentialGeometry.Integral.Connection.Rm04RealizesConnection (I := I)
      (S.family.metric (t : Real)) (S.family.connection (t : Real))
      (Rm04 (t : Real))

/-- The canonical lowered Riemann section of a solution's metric realizes its
Levi-Civita connection curvature. -/
theorem rm04Realizes_metric
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Rm04RealizesSolutionConnectionOn (I := I) S S.base.rm04 := by
  intro t
  simpa [SolutionOn.family, SolutionFamily.rm04, SolutionFamily.connection,
    metricCov] using
    (DifferentialGeometry.Integral.Connection.rm04Section_realizes (I := I) (M := M)
      (S.base.metric (t : Real))
      (metricCov (I := I) (M := M) (S.base.metric (t : Real)))
      (metricCov_smooth (I := I) (M := M) (S.base.metric (t : Real))))

/-- Metric-induced squared norm of a time-indexed lowered Riemann tensor. -/
def curvatureNormSq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M)) :
    Real -> M -> Real :=
  fun t x =>
    Tensor0SBundle.normSq0S (I := I) (S.family.metric t) x 4 ((Rm04 t) x)

@[simp] theorem curvatureNormSq_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (t : Real) (x : M) :
    curvatureNormSq (I := I) S Rm04 t x =
      Tensor0SBundle.normSq0S (I := I) (S.family.metric t) x 4 ((Rm04 t) x) := by
  rfl

/-- The metric-induced squared norm of a supplied lowered Riemann tensor is
unbounded on `M × [alpha, omega)`. -/
def Rm04NormSqUnboundedAt
    {alpha omega : Real} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M)) : Prop :=
  forall K : Real, ∃ t : Real, ∃ x : M,
    alpha <= t ∧ t < omega ∧ K < curvatureNormSq (I := I) S Rm04 t x

/-- The metric-induced squared norm of a supplied lowered Riemann tensor is
bounded above on `M × [alpha, omega)`. -/
def Rm04NormSqBoundedAt
    {alpha omega : Real} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M)) : Prop :=
  ∃ K : Real, forall t : Real, forall x : M,
    alpha <= t -> t < omega ->
      curvatureNormSq (I := I) S Rm04 t x <= K

/-- Failure of unboundedness gives a finite bound.  This is just classical
logic for the chosen squared-norm formulation. -/
theorem rmBounded_of_not_unbounded
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)}
    {Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M)}
    (hnot : ¬ Rm04NormSqUnboundedAt (I := I) S Rm04) :
    Rm04NormSqBoundedAt (I := I) S Rm04 := by
  classical
  unfold Rm04NormSqUnboundedAt at hnot
  simp only [not_forall, not_exists, not_and, not_lt] at hnot
  rcases hnot with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro t x ht hT
  exact hK t x ht hT

/-- Generic one-sided boundary right-derivative: interior right-derivatives (`Set.Ici α`) on
`Ioo α ω`, plus boundary continuity of `f` (on `Ico α ω`) and of the value field `e` (within
`Ioi α` at `α`), give the right-derivative of `f` at the closed endpoint `α`.  This is the
general-`α`, generic-`(f, e)` core of `ricci_flow_pde_at_zero`, kept here (no `ricciTensor`
specialisation) to avoid importing the DeTurck-heavy short-time-assembly file. -/
private theorem hasDerivWithinAt_Ici_boundary {a b : ℝ} (hab : a < b) (f e : ℝ → ℝ)
    (h_cont : ContinuousOn f (Set.Ico a b))
    (h_e_cont : ContinuousWithinAt e (Set.Ioi a) a)
    (h_int : ∀ t ∈ Set.Ioo a b, HasDerivWithinAt f (e t) (Set.Ici a) t) :
    HasDerivWithinAt f (e a) (Set.Ici a) a := by
  have hopen : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have hsub : Set.Ioo a b ⊆ Set.Ici a := fun y hy => le_of_lt hy.1
  have h_within : ∀ t ∈ Set.Ioo a b, HasDerivWithinAt f (e t) (Set.Ioo a b) t :=
    fun t ht => (h_int t ht).mono hsub
  have h_diff : DifferentiableOn ℝ f (Set.Ioo a b) :=
    fun t ht => (h_within t ht).differentiableWithinAt
  have h_derivEq : ∀ t ∈ Set.Ioo a b, deriv f t = e t := by
    intro t ht
    rw [← derivWithin_of_isOpen hopen ht]
    exact (h_within t ht).derivWithin (hopen.uniqueDiffWithinAt ht)
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioo a b) h_diff ?_ ?_ ?_
  · exact (h_cont.continuousWithinAt ⟨le_rfl, hab⟩).mono Set.Ioo_subset_Ico_self
  · exact Ioo_mem_nhdsGT hab
  · exact (h_e_cont.tendsto).congr'
      (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT hab) h_derivEq).symm

/-- Scalar continuity of a continuous `(0,2)`-tensor time-family `A`, evaluated against two fixed
tangent vectors at a fixed base point, on the family's time set `K`. -/
private theorem tensor2_eval_contOn {K : Set ℝ}
    {A : (t : ℝ) → (x : M) →
      Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 x}
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K A)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun s : ℝ => A s x (vec2 v w)) K := by
  rw [continuousOn_iff_continuous_restrict]
  exact hA.eval_continuous (P := {s : ℝ // s ∈ K}) (τ := Subtype.val)
    (b := fun _ => x) continuous_subtype_val (fun p => p.2) continuous_const
    (v := fun i _ => vec2 v w i) (fun _ => continuous_const)

/-- **`hleft` for `extends_of_rmBounded`.**  The Ricci-flow metric PDE of a solution, restated as a
right-derivative `HasDerivWithinAt … (Set.Ici α)` on the closed-left carrier `Ico α ω` — the form the
banked `ricci_flow_extends_construction` consumes — extracted from `hS` (whose `.equation` lives only
on the open regular times `Ioo α ω`) via `metricDerivAt` on the interior and `hasDerivWithinAt_Ici_boundary`
at the closed endpoint `α`.  The Ricci-name change `metricRicciAt ↔ ricciTensor` is the now-free
`metricRicciAt_apply_eq_ricciTensor`. -/
private theorem ricciFlowPDE_Ici_of_solution
    {alpha omega : ℝ} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen alpha omega hαω)}
    (hS : IsSolutionOn (I := I) S) :
    ∀ t ∈ Set.Ico alpha omega, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (S.base.metric s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (S.base.metric t) x v w) (Set.Ici alpha) t := by
  -- interior right-derivative, available at every regular time `t ∈ Ioo α ω`
  have hinterior : ∀ t ∈ Set.Ioo alpha omega, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (S.base.metric s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (S.base.metric t) x v w) (Set.Ici alpha) t := by
    intro t ht x v w
    have hval : S.ricciAt t x (vec2 v w) = ricciTensor (I := I) (S.base.metric t) x v w :=
      metricRicciAt_apply_eq_ricciTensor (S.base.metric t) x v w
    have h := metricDerivAt (I := I) S hS ⟨t, ht⟩ x v w
    rw [hval] at h
    exact h.hasDerivWithinAt
  -- scalar continuity of `s ↦ ricciTensor (g s) x v w`, on the carrier
  have hric_cont : ∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun s : ℝ => ricciTensor (I := I) (S.base.metric s) x v w)
        (Set.Ico alpha omega) := by
    intro x v w
    refine (tensor2_eval_contOn hS.ricciCont x v w).congr (fun s _ => ?_)
    have e1 : S.ricci s x = metricRicciAt (S.base.metric s) x := by
      simp only [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt]
    rw [e1]
    exact (metricRicciAt_apply_eq_ricciTensor (S.base.metric s) x v w).symm
  intro t ht x v w
  rcases eq_or_lt_of_le ht.1 with rfl | hlt
  · refine hasDerivWithinAt_Ici_boundary hαω
      (fun s => (S.base.metric s).inner x v w)
      (fun s => (-2 : ℝ) * ricciTensor (I := I) (S.base.metric s) x v w) ?_ ?_
      (fun s hs => hinterior s hs x v w)
    · -- h_cont : metric scalar continuity
      refine (tensor2_eval_contOn hS.smoothMetric.metricTensor_cont x v w).congr
        (fun s _ => ?_)
      simp [Tensor0SBundle.metricTensorField_apply, vec2]
    · -- h_e_cont : ricci scalar continuity within `Ioi α` at `α`
      have hmem : Set.Ico alpha omega ∈ nhdsWithin alpha (Set.Ioi alpha) :=
        Filter.mem_of_superset (Ioo_mem_nhdsGT hαω) Set.Ioo_subset_Ico_self
      exact (((hric_cont x v w).continuousWithinAt ⟨le_rfl, hαω⟩).mono_of_mem_nhdsWithin
        hmem).const_mul (-2)
  · exact hinterior t ⟨hlt, ht.2⟩ x v w

/-- Black Box 11.2: bounded curvature on a closed finite-endpoint Ricci flow
lets the flow extend smoothly past the endpoint.  This is global PDE theory,
not local tensor algebra. -/
theorem extends_of_rmBounded
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)}
    {Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M)}
    (hdim : Module.finrank ℝ E = 3)
    (_hS : IsSolutionOn (I := I) S)
    (_hRm : Rm04RealizesSolutionConnectionOn (I := I) S Rm04)
    (_hbound : Rm04NormSqBoundedAt (I := I) S Rm04) :
    ExtendsPastEndpoint (I := I) hαω S := by
  let g_fam := S.base.metric
  -- Leaf 1: Ricci-flow PDE on [α, ω) in the form ricci_flow_extends_construction needs,
  -- extracted from the solution's `MetricVariationEquationOn` (regular times) + boundary lemma.
  have hleft : ∀ t ∈ Set.Ico alpha omega, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
        ((-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g_fam t) x v w)
        (Set.Ici alpha) t :=
    ricciFlowPDE_Ici_of_solution (I := I) _hS
  -- Leaf 2: C∞ limit data from BBS all-m derivative bounds (dim-3 BBS producer)
  have hLimit : DifferentialGeometry.PDE.RicciFlow.CinftyLimitData (I := I)
      g_fam alpha omega hαω :=
    cinftyLimitData_of_solution (I := I) S _hS hdim Rm04 _hRm _hbound
  -- Leaf 3: short-time glue (DeTurck — collaborator's work)
  have hglue : ∀ (r : ℝ → SmoothRiemannianMetric I M) (T : ℝ),
      r 0 = hLimit.limitMetric → 0 < T →
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (r p.1) x₀ p.2 i j)
          (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
        HasDerivWithinAt (fun u : ℝ => (r u).inner x v w)
          ((-2 : ℝ) *
            DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (r t) x v w)
          (Set.Ici 0) t) →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ T ∧
        DifferentialGeometry.PDE.RicciFlow.CinftyGlueData (I := I) g_fam r alpha omega ε := by
    -- Gate-R is now AVAILABLE as `hr_smooth_closed`: the restart `r`'s joint chart-Gram `C∞`
    -- up to the CLOSED initial endpoint, on `[0, T)`.  The remaining obstructions for the
    -- `gram_smooth` field of `CinftyGlueData` are **Gate-L** (the left family's `C∞`-up-to-`ω`
    -- from BBS, via a strengthened `CinftyLimitData`) and the **jet compatibility** (Lemma 2/3)
    -- feeding the frozen splice `Analysis.…SmoothExtension.contDiffOn_glue_of_jet_param`.
    -- These are left as explicit obstructions temporarily.
    intro r T hr0 hT hr_smooth_closed hr_pde
    sorry
  -- Leaf 4: apply the banked construction
  obtain ⟨ε, hε, g_ext, hagree, _hsmooth, _hcont, hpde⟩ :=
    DifferentialGeometry.PDE.RicciFlow.ricci_flow_extends_construction (I := I)
      g_fam hαω hleft hLimit hglue
  -- Leaf 5: wrap the raw metric data into ExtendsPastEndpoint
  have hwide : alpha < omega + ε := by linarith
  let Shat : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha (omega + ε) hwide) :=
    { base := { metric := g_ext } }
  refine ⟨ε, hε, hwide, Shat, ?_, ?_⟩
  · -- IsSolutionOn for the extended solution (banked builder; nablaRicCont field removed as vestigial)
    exact DifferentialGeometry.PDE.RicciFlow.isSolutionOn_of_extendData
      hwide hαω g_ext S _hS hagree _hsmooth _hcont hpde
  · -- SolutionAgreesOn on [α, ω)
    intro t ht
    have htlt : t < omega := ht.2
    have hteq : g_ext t = g_fam t := hagree t htlt
    refine ⟨?_, ?_, ?_⟩
    · -- metric agreement: g_ext t = S.base.metric t
      show S.family.metric t = Shat.family.metric t
      change S.base.metric t = g_ext t
      exact hteq.symm
    · -- connection agreement (follows from metric agreement)
      show S.family.connection t = Shat.family.connection t
      change S.base.connection t = (SolutionFamily.connection { metric := g_ext }) t
      simp only [SolutionFamily.connection]
      congr 1; exact hteq.symm
    · -- Ricci agreement (follows from metric agreement)
      show S.ricci t = Shat.ricci t
      change S.base.ricci t = SolutionFamily.ricci { metric := g_ext } t
      simp only [SolutionFamily.ricci]
      congr 1; exact hteq.symm

/-- Lemma 11.3: a maximal finite-endpoint Ricci flow has unbounded curvature.

This is the consumer proof from Black Box 11.2: if curvature were bounded, the
extension criterion would extend the solution past the endpoint, contradicting
maximality. -/
theorem rmUnbounded_of_maximal
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)}
    {Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M)}
    (hdim : Module.finrank ℝ E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hmax : IsMaximalAtEndpoint (I := I) hαω S)
    (hRm : Rm04RealizesSolutionConnectionOn (I := I) S Rm04) :
    Rm04NormSqUnboundedAt (I := I) S Rm04 := by
  by_contra hnot
  exact hmax (extends_of_rmBounded (I := I) hdim hS hRm
    (rmBounded_of_not_unbounded (I := I) hnot))

/-- A Ricci flow forms a singularity at the finite endpoint when some lowered
Riemann tensor realizing the solution curvature has metric-induced squared
norm unbounded on `M × [alpha, omega)`. -/
def FormsSingularityAt
    {alpha omega : Real} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)) : Prop :=
  ∃ Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M),
    Rm04RealizesSolutionConnectionOn (I := I) S Rm04 ∧
      Rm04NormSqUnboundedAt (I := I) S Rm04

/-- Existential version of Lemma 11.3 matching `FormsSingularityAt`.  A
separate curvature-realization producer supplies the realizing `Rm04`. -/
theorem formsSing_of_maximal
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)}
    (hdim : Module.finrank ℝ E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hmax : IsMaximalAtEndpoint (I := I) hαω S)
    (hRmEx :
      ∃ Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M),
        Rm04RealizesSolutionConnectionOn (I := I) S Rm04) :
    FormsSingularityAt (I := I) S := by
  rcases hRmEx with ⟨Rm04, hRm⟩
  exact ⟨Rm04, hRm, rmUnbounded_of_maximal (I := I) hdim hS hmax hRm⟩

/-- Canonical metric-curvature version of Lemma 11.3. -/
theorem formsSing_of_maximal_metric
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)}
    (hdim : Module.finrank ℝ E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hmax : IsMaximalAtEndpoint (I := I) hαω S) :
    FormsSingularityAt (I := I) S := by
  exact formsSing_of_maximal (I := I) hdim hS hmax
    ⟨S.base.rm04, rm04Realizes_metric (I := I) S⟩

/-- Interface for Lemma 14.27.  Proving this requires the global extension
criterion and compactness/regularity inputs; this file only exposes the target
shape. -/
def SingularIffMaximalAtEndpoint
    {alpha omega : Real} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)) : Prop :=
  FormsSingularityAt (I := I) S ↔
    IsMaximalAtEndpoint (I := I) hαω S

end DifferentialGeometry.PDE.RicciFlow
