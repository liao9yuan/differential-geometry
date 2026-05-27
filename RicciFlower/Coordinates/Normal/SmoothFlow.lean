import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import RicciFlower.Coordinates.Normal.Flow

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Smooth dependence for the fixed-chart model flow

This file starts the variational-equation route toward smooth dependence of the
fixed-chart geodesic model flow on its initial phase.
-/

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle Filter
open scoped Manifold ContDiff Topology Uniformity
open RicciFlower.GlobalGeometry.Lecture07

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [SigmaCompactSpace M] [T2Space M]

abbrev ModelPhase := E × E

abbrev ModelLin := ModelPhase (E := E) →L[Real] ModelPhase (E := E)

/-- Formal Taylor jet of a model-phase map at one initial phase. -/
abbrev ModelJet := FormalMultilinearSeries Real
  (ModelPhase (E := E)) (ModelPhase (E := E))

/-- Zeroth coefficient of a formal model-phase jet. -/
def jetBase (J : ModelJet (E := E)) : ModelPhase (E := E) :=
  (J 0).curry0

/-- Taylor jet in the initial phase of a model flow at a fixed time. -/
def flowJet
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (z : ModelPhase (E := E)) (t : Real) : ModelJet (E := E) :=
  ftaylorSeries Real (fun z' : ModelPhase (E := E) => Φ z' t) z

/-- Initial Taylor jet of the identity flow. -/
def idJet (z : ModelPhase (E := E)) : ModelJet (E := E) :=
  ftaylorSeries Real (fun z' : ModelPhase (E := E) => z') z

/-- Faà di Bruno right-hand side for the formal Taylor jet of `z' = F z`. -/
def jetRHS
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (J : ModelJet (E := E)) : ModelJet (E := E) :=
  (ftaylorSeries Real F (jetBase (E := E) J)).taylorComp J

/-- Specialized jet right-hand side for the fixed-chart model spray. -/
def sprayJetRHS
    (g : SmoothRiemannianMetric I M) (x : M)
    (J : ModelJet (E := E)) : ModelJet (E := E) :=
  jetRHS (E := E) (modelSpray (I := I) g x) J

@[simp] theorem flowJet_base
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (z : ModelPhase (E := E)) (t : Real) :
    jetBase (E := E) (flowJet (E := E) Φ z t) = Φ z t := by
  simp [jetBase, flowJet, ftaylorSeries]

@[simp] theorem idJet_base (z : ModelPhase (E := E)) :
    jetBase (E := E) (idJet (E := E) z) = z := by
  simp [jetBase, idJet, ftaylorSeries]

set_option linter.flexible false in
@[simp] theorem jetRHS_base
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (J : ModelJet (E := E)) :
    jetBase (E := E) (jetRHS (E := E) F J) = F (jetBase (E := E) J) := by
  simp [jetBase, jetRHS, FormalMultilinearSeries.taylorComp, ftaylorSeries]
  exact iteratedFDeriv_zero_apply (𝕜 := Real) (f := F) (x := (J 0) ![])
    ((OrderedFinpartition.atomic 0).applyOrderedFinpartition (fun m => J 1) ![])

@[simp] theorem flowJet_zero
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (z : ModelPhase (E := E)) (t : Real) :
    flowJet (E := E) Φ z t 0 =
      ContinuousMultilinearMap.uncurry0 Real (ModelPhase (E := E)) (Φ z t) := by
  apply (continuousMultilinearCurryFin0 Real
    (ModelPhase (E := E)) (ModelPhase (E := E))).injective
  simp [flowJet, ftaylorSeries]

@[simp] theorem idJet_zero (z : ModelPhase (E := E)) :
    idJet (E := E) z 0 =
      ContinuousMultilinearMap.uncurry0 Real (ModelPhase (E := E)) z := by
  apply (continuousMultilinearCurryFin0 Real
    (ModelPhase (E := E)) (ModelPhase (E := E))).injective
  simp [idJet, ftaylorSeries]

@[simp] theorem jetRHS_zero
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (J : ModelJet (E := E)) :
    jetRHS (E := E) F J 0 =
      ContinuousMultilinearMap.uncurry0 Real (ModelPhase (E := E))
        (F (jetBase (E := E) J)) := by
  apply (continuousMultilinearCurryFin0 Real
    (ModelPhase (E := E)) (ModelPhase (E := E))).injective
  simpa [jetBase] using jetRHS_base (E := E) F J

/-- The first jet coefficient recovers the Frechet derivative. -/
theorem flowJet_one
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (z : ModelPhase (E := E)) (t : Real) {A : ModelLin (E := E)}
    (hA : HasFDerivAt (fun z' : ModelPhase (E := E) => Φ z' t) A z) :
    continuousMultilinearCurryFin1 Real
        (ModelPhase (E := E)) (ModelPhase (E := E))
        (flowJet (E := E) Φ z t 1) =
      A := by
  apply ContinuousLinearMap.ext
  intro h
  rw [continuousMultilinearCurryFin1_apply]
  simp [flowJet, ftaylorSeries, hA.fderiv]

set_option linter.flexible false in
/-- First jet coefficient of the Faà di Bruno RHS. -/
theorem jetRHS_one
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (J : ModelJet (E := E)) :
    continuousMultilinearCurryFin1 Real
        (ModelPhase (E := E)) (ModelPhase (E := E))
        (jetRHS (E := E) F J 1) =
      (fderiv Real F (jetBase (E := E) J)).comp
        (continuousMultilinearCurryFin1 Real
          (ModelPhase (E := E)) (ModelPhase (E := E)) (J 1)) := by
  apply ContinuousLinearMap.ext
  intro h
  rw [continuousMultilinearCurryFin1_apply, ContinuousLinearMap.comp_apply,
    continuousMultilinearCurryFin1_apply]
  simp [jetRHS, jetBase, FormalMultilinearSeries.taylorComp, ftaylorSeries]
  have hiter :=
    iteratedFDeriv_one_apply (𝕜 := Real) (f := F) (x := (J 0) ![])
      (m := (OrderedFinpartition.atomic 1).applyOrderedFinpartition (fun m => J 1) ![h])
  refine hiter.trans ?_
  apply congrArg (fderiv Real F ((J 0) ![]))
  change J 1
      (![h] ∘ (OrderedFinpartition.atomic 1).emb
        ⟨0, by simp [OrderedFinpartition.atomic]⟩) =
    J 1 ![h]
  apply congrArg (J 1)
  funext i
  fin_cases i
  rfl

/-- Finite-order jet ODE target.  A future induction should construct `J`
from the model flow and prove this predicate for every finite `N`. -/
def IsFlowJetUpTo
    (N : Nat)
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (J : ModelPhase (E := E) -> Real -> ModelJet (E := E))
    (T : Set Real) : Prop :=
  (∀ z t, t ∈ T -> jetBase (E := E) (J z t) = Φ z t) ∧
    (∀ z, J z 0 = idJet (E := E) z) ∧
      ∀ n ≤ N, ∀ z t, t ∈ T ->
        HasDerivWithinAt (fun τ : Real => J z τ n)
          (jetRHS (E := E) F (J z t) n) T t

/-- Finite-order jet ODE target specialized to the fixed-chart model spray. -/
def IsModelFlowJetUpTo
    (N : Nat)
    (g : SmoothRiemannianMetric I M) (x : M)
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (J : ModelPhase (E := E) -> Real -> ModelJet (E := E))
    (T : Set Real) : Prop :=
  IsFlowJetUpTo (E := E) N (modelSpray (I := I) g x) Φ J T

/-- Zeroth-order case of the jet ODE: it is just the original flow equation. -/
theorem flowJetUpTo_zero
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    {T : Set Real}
    (hzero : ∀ z : ModelPhase (E := E), Φ z 0 = z)
    (hderiv :
      ∀ z : ModelPhase (E := E), ∀ t ∈ T,
        HasDerivWithinAt (Φ z) (F (Φ z t)) T t) :
    IsFlowJetUpTo (E := E) 0 F Φ
      (fun z t => flowJet (E := E) Φ z t) T := by
  refine ⟨?_, ?_, ?_⟩
  · intro z t _ht
    simp
  · intro z
    apply FormalMultilinearSeries.ext
    intro n
    simp [flowJet, idJet, hzero]
  · intro n hn z t ht
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    let L :
        ModelPhase (E := E) →L[Real]
          ContinuousMultilinearMap Real
            (fun _ : Fin 0 => ModelPhase (E := E)) (ModelPhase (E := E)) :=
      (continuousMultilinearCurryFin0 Real
        (ModelPhase (E := E)) (ModelPhase (E := E))).symm.toContinuousLinearMap
    have hcomp :
        HasDerivWithinAt (fun τ : Real => L (Φ z τ))
          (L (F (Φ z t))) T t :=
      L.hasFDerivAt.comp_hasDerivWithinAt t (hderiv z t ht)
    simpa [L] using hcomp

/-- First-order jet ODE bridge from a Frechet-derivative field satisfying the
variational equation. -/
theorem flowJetUpTo_one
    (F : ModelPhase (E := E) -> ModelPhase (E := E))
    (Φ : ModelPhase (E := E) -> Real -> ModelPhase (E := E))
    (A : ModelPhase (E := E) -> Real -> ModelLin (E := E))
    {T : Set Real}
    (hzero : ∀ z : ModelPhase (E := E), Φ z 0 = z)
    (hderiv :
      ∀ z : ModelPhase (E := E), ∀ t ∈ T,
        HasDerivWithinAt (Φ z) (F (Φ z t)) T t)
    (hF :
      ∀ z : ModelPhase (E := E), ∀ t ∈ T,
        HasFDerivAt (fun z' : ModelPhase (E := E) => Φ z' t) (A z t) z)
    (hA :
      ∀ z : ModelPhase (E := E), ∀ t ∈ T,
        HasDerivWithinAt (A z)
          ((fderiv Real F (Φ z t)).comp (A z t)) T t) :
    IsFlowJetUpTo (E := E) 1 F Φ
      (fun z t => flowJet (E := E) Φ z t) T := by
  refine ⟨?_, ?_, ?_⟩
  · intro z t _ht
    simp
  · intro z
    apply FormalMultilinearSeries.ext
    intro n
    simp [flowJet, idJet, hzero]
  · intro n hn z t ht
    interval_cases n
    · exact (flowJetUpTo_zero (E := E) F Φ hzero hderiv).2.2 0 le_rfl z t ht
    · let L :
          ModelLin (E := E) →L[Real]
            ContinuousMultilinearMap Real
              (fun _ : Fin 1 => ModelPhase (E := E)) (ModelPhase (E := E)) :=
        (continuousMultilinearCurryFin1 Real
          (ModelPhase (E := E)) (ModelPhase (E := E))).symm.toContinuousLinearMap
      have hcomp :
          HasDerivWithinAt (fun τ : Real => L (A z τ))
            (L ((fderiv Real F (Φ z t)).comp (A z t))) T t :=
        L.hasFDerivAt.comp_hasDerivWithinAt t (hA z t ht)
      have hfun :
          ∀ τ ∈ T,
            flowJet (E := E) Φ z τ 1 = L (A z τ) := by
        intro τ hτ
        apply (continuousMultilinearCurryFin1 Real
          (ModelPhase (E := E)) (ModelPhase (E := E))).injective
        simp [L, flowJet_one (E := E) Φ z τ (hF z τ hτ)]
      have hrhs :
          jetRHS (E := E) F (flowJet (E := E) Φ z t) 1 =
            L ((fderiv Real F (Φ z t)).comp (A z t)) := by
        apply (continuousMultilinearCurryFin1 Real
          (ModelPhase (E := E)) (ModelPhase (E := E))).injective
        rw [jetRHS_one]
        simp [L, flowJet_one (E := E) Φ z t (hF z t ht)]
      exact (hcomp.congr hfun (hfun t ht)).congr_deriv hrhs.symm

/-- The coefficient of the forcing term in `gronwallBound 0 K ε t`. -/
private def gronwallCoeff (K t : Real) : Real :=
  if K = 0 then t else (Real.exp (K * t) - 1) / K

private theorem gronwallBound_zero_eq_mul (K ε t : Real) :
    gronwallBound 0 K ε t = ε * gronwallCoeff K t := by
  by_cases hK : K = 0
  · subst K
    simp [gronwallBound, gronwallCoeff]
  · simp [gronwallBound, gronwallCoeff, hK, div_eq_mul_inv]
    ring

/-- If the Taylor-residual coefficient tends to zero, then the corresponding
Gronwall forcing term is little-o in the perturbation. -/
private theorem gronwall_forcing_isLittleO
    {X : Type*} [NormedAddCommGroup X] {l : Filter X}
    {C : X -> Real} {B L T : Real}
    (hC : Tendsto C l (𝓝 0)) :
    (fun h : X => gronwallBound 0 B (C h * (L * ‖h‖)) T)
      =o[l] (fun h : X => h) := by
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  let A : Real := |L| * |gronwallCoeff B T| + 1
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hsmall : ∀ᶠ h in l, |C h| ≤ c / A := by
    have hAbs : Tendsto (fun h : X => |C h|) l (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : Real)).comp hC
    have hball :=
      hAbs.eventually (Metric.ball_mem_nhds (0 : Real) (div_pos hc hApos))
    filter_upwards [hball] with h hh
    have hlt : |C h| < c / A := by
      simpa [Real.dist_eq, abs_of_nonneg (abs_nonneg (C h))] using hh
    exact le_of_lt hlt
  filter_upwards [hsmall] with h hh
  have hnorm : 0 ≤ ‖h‖ := norm_nonneg _
  have hP_nonneg : 0 ≤ |L| * |gronwallCoeff B T| := by positivity
  have hP_le_A : |L| * |gronwallCoeff B T| ≤ A := by
    dsimp [A]
    linarith
  have hdiv_nonneg : 0 ≤ c / A := by positivity
  have hcoef :
      (c / A) * (|L| * |gronwallCoeff B T|) ≤ c := by
    calc
      (c / A) * (|L| * |gronwallCoeff B T|)
          ≤ (c / A) * A := by
            exact mul_le_mul_of_nonneg_left hP_le_A hdiv_nonneg
      _ = c := by
        field_simp [ne_of_gt hApos]
  calc
    ‖gronwallBound 0 B (C h * (L * ‖h‖)) T‖
        = |C h| * (|L| * |gronwallCoeff B T|) * ‖h‖ := by
          rw [gronwallBound_zero_eq_mul]
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hnorm]
          ring
    _ ≤ (c / A) * (|L| * |gronwallCoeff B T|) * ‖h‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hh hP_nonneg) hnorm
    _ ≤ c * ‖h‖ := by
          exact mul_le_mul_of_nonneg_right hcoef hnorm

/-- Turn a Gronwall forcing bound with a vanishing coefficient into a little-o
estimate for a vector-valued error. -/
private theorem isLittleO_of_gronwall_bound
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {l : Filter X} {f : X -> Y} {C : X -> Real} {B L T : Real}
    (hC : Tendsto C l (𝓝 0))
    (hbound : ∀ᶠ h in l,
      ‖f h‖ ≤ gronwallBound 0 B (C h * (L * ‖h‖)) T) :
    f =o[l] (fun h : X => h) := by
  have hg :=
    gronwall_forcing_isLittleO (X := X) (l := l)
      (C := C) (B := B) (L := L) (T := T) hC
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  filter_upwards [hbound, hg.bound hc] with h hf hg'
  exact hf.trans ((le_abs_self _).trans hg')

/-- A variant of `isLittleO_of_gronwall_bound` avoiding a chosen residual
coefficient: an eventual Gronwall bound with every positive constant is enough. -/
private theorem isLittleO_of_gronwall_bound_eventually
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {l : Filter X} {f : X -> Y} {B L T : Real}
    (hbound : ∀ η > 0, ∀ᶠ h in l,
      ‖f h‖ ≤ gronwallBound 0 B (η * (L * ‖h‖)) T) :
    f =o[l] (fun h : X => h) := by
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  let A : Real := |L| * |gronwallCoeff B T| + 1
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  let η : Real := c / A
  have hηpos : 0 < η := by
    dsimp [η]
    positivity
  have hP_nonneg : 0 ≤ |L| * |gronwallCoeff B T| := by positivity
  have hP_le_A : |L| * |gronwallCoeff B T| ≤ A := by
    dsimp [A]
    linarith
  have hη_nonneg : 0 ≤ η := le_of_lt hηpos
  have hcoef : η * (|L| * |gronwallCoeff B T|) ≤ c := by
    calc
      η * (|L| * |gronwallCoeff B T|) ≤ η * A := by
        exact mul_le_mul_of_nonneg_left hP_le_A hη_nonneg
      _ = c := by
        dsimp [η, A]
        field_simp [ne_of_gt hApos]
  filter_upwards [hbound η hηpos] with h hf
  have hnorm : 0 ≤ ‖h‖ := norm_nonneg _
  have hgr :
      ‖gronwallBound 0 B (η * (L * ‖h‖)) T‖
        = η * (|L| * |gronwallCoeff B T|) * ‖h‖ := by
    rw [gronwallBound_zero_eq_mul]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hη_nonneg,
      abs_of_nonneg hnorm]
    ring
  calc
    ‖f h‖ ≤ gronwallBound 0 B (η * (L * ‖h‖)) T := hf
    _ ≤ ‖gronwallBound 0 B (η * (L * ‖h‖)) T‖ := le_abs_self _
    _ = η * (|L| * |gronwallCoeff B T|) * ‖h‖ := hgr
    _ ≤ c * ‖h‖ := by
      exact mul_le_mul_of_nonneg_right hcoef hnorm

/-- The zero point for the variational equation: zero phase and identity
linearized initial data. -/
def varPhaseZero (x : M) : ModelPhase (E := E) × ModelLin (E := E) :=
  (extChartAt I.tangent (phaseZero (I := I) x)
    (phaseZero (I := I) x),
    ContinuousLinearMap.id Real (ModelPhase (E := E)))

/-- The augmented vector field for the variational equation.

The first component is the model spray.  The second component is the linear ODE
`A' = DF(z) ∘ A` for derivatives with respect to the initial phase. -/
def varSpray
    (g : SmoothRiemannianMetric I M) (x : M)
    (p : ModelPhase (E := E) × ModelLin (E := E)) :
    ModelPhase (E := E) × ModelLin (E := E) :=
  (modelSpray (I := I) g x p.1,
    (fderiv Real (modelSpray (I := I) g x) p.1).comp p.2)

@[simp] theorem varSpray_fst
    (g : SmoothRiemannianMetric I M) (x : M)
    (p : ModelPhase (E := E) × ModelLin (E := E)) :
    (varSpray (I := I) g x p).1 = modelSpray (I := I) g x p.1 := rfl

@[simp] theorem varSpray_snd
    (g : SmoothRiemannianMetric I M) (x : M)
    (p : ModelPhase (E := E) × ModelLin (E := E)) :
    (varSpray (I := I) g x p).2 =
      (fderiv Real (modelSpray (I := I) g x) p.1).comp p.2 := rfl

/-- The augmented variational vector field is `C¹` at `(0_x, id)`.

This is the first checked regularity input for the variational-equation proof
of smooth dependence. -/
theorem varSpray_cdAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real 1
      (varSpray (I := I) g x)
      (varPhaseZero (I := I) (E := E) x) := by
  let Z := ModelPhase (E := E)
  let L := ModelLin (E := E)
  let z0 : Z :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  let p0 : Z × L := (z0, ContinuousLinearMap.id Real Z)
  have hF :
      ContDiffAt Real 1
        (fun p : Z × L => modelSpray (I := I) g x p.1)
        p0 := by
    exact (modelSpray_cdAt (I := I) g x).comp p0 contDiffAt_fst
  have hDF0 :
      ContDiffAt Real 1
        (fderiv Real (modelSpray (I := I) g x))
        z0 := by
    exact (modelSpray_contDiffAt (I := I) g x).fderiv_right (by
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hDF :
      ContDiffAt Real 1
        (fun p : Z × L => fderiv Real (modelSpray (I := I) g x) p.1)
        p0 := by
    exact hDF0.comp p0 contDiffAt_fst
  have hA :
      ContDiffAt Real 1 (fun p : Z × L => p.2) p0 :=
    contDiffAt_snd
  have hcomp :
      ContDiffAt Real 1
        (fun p : Z × L =>
          (fderiv Real (modelSpray (I := I) g x) p.1).comp p.2)
        p0 := by
    exact hDF.clm_comp hA
  simpa [varSpray, varPhaseZero, z0, p0, Z, L] using hF.prodMk hcomp

/-- The augmented variational vector field is `C¹` at every controlled phase
point. -/
theorem varSpray_cdAt_of_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {p : ModelPhase (E := E) × ModelLin (E := E)}
    (hztarget : p.1 ∈
      (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc : (phaseOfModel (I := I) x p.1).proj ∈
      (extChartAt I x).source) :
    ContDiffAt Real 1 (varSpray (I := I) g x) p := by
  let Z := ModelPhase (E := E)
  let L := ModelLin (E := E)
  have hF0 :
      ContDiffAt Real 1 (modelSpray (I := I) g x) p.1 := by
    exact (modelSpray_contDiffAt_of_mem (I := I) g x hztarget hsrc).of_le
      (by simp)
  have hF :
      ContDiffAt Real 1
        (fun p : Z × L => modelSpray (I := I) g x p.1)
        p := by
    exact hF0.comp p contDiffAt_fst
  have hDF0 :
      ContDiffAt Real 1
        (fderiv Real (modelSpray (I := I) g x))
        p.1 := by
    exact (modelSpray_contDiffAt_of_mem (I := I) g x hztarget hsrc).fderiv_right
      (by
        exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hDF :
      ContDiffAt Real 1
        (fun p : Z × L => fderiv Real (modelSpray (I := I) g x) p.1)
        p := by
    exact hDF0.comp p contDiffAt_fst
  have hA :
      ContDiffAt Real 1 (fun p : Z × L => p.2) p :=
    contDiffAt_snd
  have hcomp :
      ContDiffAt Real 1
        (fun p : Z × L =>
          (fderiv Real (modelSpray (I := I) g x) p.1).comp p.2)
        p := by
    exact hDF.clm_comp hA
  simpa [varSpray, Z, L] using hF.prodMk hcomp

/-- Local Picard-Lindelof data for the augmented variational equation. -/
theorem varSpray_pl
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal), ∃ (_hr : 0 < r),
        ∀ t0 : Real,
          IsPicardLindelof
            (fun _ : Real => varSpray (I := I) g x)
            (tmin := t0 - ε) (tmax := t0 + ε)
            ⟨t0, by simp [le_of_lt hε]⟩
            (varPhaseZero (I := I) (E := E) x)
            a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one
      (varSpray_cdAt (I := I) g x)
  exact ⟨ε, hε, a, r, L, K, hr, hpl⟩

/-- The augmented variational phase is source-controlled near `(0_x, id)` as
soon as its base phase is source-controlled. -/
theorem varSrc_nhds
    [I.Boundaryless] (x : M) :
    {p : ModelPhase (E := E) × ModelLin (E := E) |
      p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source} ∈
      𝓝 (varPhaseZero (I := I) (E := E) x) := by
  have hsrc := modelSrc_nhds (I := I) (E := E) x
  have hfst :
      ContinuousAt (fun p : ModelPhase (E := E) × ModelLin (E := E) => p.1)
        (varPhaseZero (I := I) (E := E) x) :=
    continuousAt_fst
  simpa [varPhaseZero, Set.preimage] using hfst.preimage_mem_nhds hsrc

/-- Picard-Lindelof data for the augmented variational equation, shrunk so the
whole controlling augmented ball keeps the base phase in the fixed chart
source. -/
theorem varSpray_pl0_src
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal),
      0 < r ∧
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
          {p : ModelPhase (E := E) × ModelLin (E := E) |
            p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
              (phaseOfModel (I := I) x p.1).proj ∈
                (extChartAt I x).source} ∧
        IsPicardLindelof
          (fun _ : Real => varSpray (I := I) g x)
          (tmin := 0 - ε) (tmax := 0 + ε)
          ⟨0, by simp [le_of_lt hε]⟩
          (varPhaseZero (I := I) (E := E) x)
          a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := varSpray_pl (I := I) g x
  let p0 : ModelPhase (E := E) × ModelLin (E := E) :=
    varPhaseZero (I := I) (E := E) x
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (varSrc_nhds (I := I) (E := E) x)
  have hpl0 := hpl 0
  have hrR : (0 : Real) < (r : Real) := by exact_mod_cast hr
  have hnonneg :
      (0 : Real) ≤
        (L : Real) * max ((0 + ε) - 0) (0 - (0 - ε)) := by
    exact mul_nonneg (NNReal.coe_nonneg L)
      (le_max_of_le_left (by linarith))
  have hra : (r : Real) ≤ (a : Real) := by
    have hmul := hpl0.mul_max_le
    nlinarith [hmul, hnonneg]
  have ha : 0 < a := by
    exact_mod_cast (lt_of_lt_of_le hrR hra)
  let δnn : NNReal := ⟨δ / 2, le_of_lt (half_pos hδ)⟩
  let a' : NNReal := min a δnn
  have hδnn : 0 < δnn := by
    change (0 : Real) < δ / 2
    exact half_pos hδ
  have ha' : 0 < a' := by
    exact lt_min ha hδnn
  let r' : NNReal := a' / 2
  have hr' : 0 < r' := by
    simp [r', ha']
  have hrlt : r' < a' := by
    simpa [r'] using half_lt_self ha'
  obtain ⟨ε', hε', hpl'⟩ :=
    IsPicardLindelof.exists_shrink_radius
      (f := fun _ : Real => varSpray (I := I) g x)
      (t₀ := (0 : Real)) (ε := ε) hε hpl0
      (a' := a') (r' := r') (by exact min_le_left _ _) hrlt
  refine ⟨ε', hε', a', r', L, K, hr', ?_, hpl'⟩
  intro p hp
  apply hδsub
  rw [Metric.mem_ball]
  have hdist : dist p p0 ≤ (a' : Real) := by
    simpa [p0] using Metric.mem_closedBall.mp hp
  have haδ : (a' : Real) ≤ δ / 2 := by
    have : a' ≤ δnn := min_le_right _ _
    exact_mod_cast this
  calc
    dist p p0 ≤ (a' : Real) := hdist
    _ ≤ δ / 2 := haδ
    _ < δ := half_lt_self hδ

/-- Uniform short-time augmented variational flow with Lipschitz dependence on
the augmented initial phase. -/
theorem varFlow_lipschitz
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
          Ψ p 0 = p ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ψ p)
                (varSpray (I := I) g x (Ψ p t))
                (Set.Icc (-ε) ε) t) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) := by
  obtain ⟨ε, hε, _a, r, _L, _K, hr, hpl⟩ := varSpray_pl (I := I) g x
  obtain ⟨Ψ, hΨ, L', hLip⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  refine ⟨ε, hε, r, hr, Ψ, ?_, L', ?_⟩
  · intro p hp
    refine ⟨(hΨ p hp).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hΨ p hp).2 t ht'
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using hLip t ht'

/-- Uniform short-time augmented variational flow with Lipschitz dependence and
the closed-ball bound for the same chosen flow. -/
theorem varFlow_bound
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
          Ψ p 0 = p ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ψ p)
                (varSpray (I := I) g x (Ψ p t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ψ p t ∈
                Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) := by
  obtain ⟨ε, hε, a, r, _L, _K, hr, hpl⟩ := varSpray_pl (I := I) g x
  obtain ⟨Ψ, hΨ, hbound, _hpicard, L', hLip⟩ :=
    plFlow_bound (F := ModelPhase (E := E) × ModelLin (E := E))
      (f := fun _ : Real => varSpray (I := I) g x) (hpl 0)
  refine ⟨ε, hε, a, r, hr, Ψ, ?_, ?_, L', ?_⟩
  · intro p hp
    refine ⟨(hΨ p hp).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hΨ p hp).2 t ht'
  · intro p hp t
    simpa using hbound p hp t
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using hLip t ht'

/-- Uniform short-time augmented variational flow with Lipschitz dependence,
closed-ball bound, and base-phase source control for the same chosen flow. -/
theorem varFlow_src_bound
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
          Ψ p 0 = p ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ψ p)
                (varSpray (I := I) g x (Ψ p t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ψ p t ∈
                Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) ∧
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
            {p : ModelPhase (E := E) × ModelLin (E := E) |
              p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x p.1).proj ∈
                  (extChartAt I x).source}) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              (Ψ p t).1 ∈
                (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (Ψ p t).1).proj ∈
                  (extChartAt I x).source) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) := by
  obtain ⟨ε, hε, a, r, _L, _K, hr, hsrc, hpl⟩ :=
    varSpray_pl0_src (I := I) g x
  obtain ⟨Ψ, hΨ, hbound, _hpicard, L', hLip⟩ :=
    plFlow_bound (F := ModelPhase (E := E) × ModelLin (E := E))
      (f := fun _ : Real => varSpray (I := I) g x) hpl
  refine ⟨ε, hε, a, r, hr, Ψ, ?_, ?_, hsrc, ?_, L', ?_⟩
  · intro p hp
    refine ⟨(hΨ p hp).1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hΨ p hp).2 t ht'
  · intro p hp t
    simpa using hbound p hp t
  · intro p hp t
    exact hsrc (hbound p hp t)
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using hLip t ht'

/-- Source control descends from a convex augmented closed ball to base-phase
segments. -/
theorem varBase_segment_src_of_bound
    [I.Boundaryless]
    (x : M) {a : NNReal}
    {p q : ModelPhase (E := E) × ModelLin (E := E)}
    (hp : p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hq : q ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    {u : ModelPhase (E := E)}
    (hu : u ∈ segment Real p.1 q.1) :
    u ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
      (phaseOfModel (I := I) x u).proj ∈ (extChartAt I x).source := by
  rcases hu with ⟨c, d, hc, hd, hcd, hu⟩
  let w : ModelPhase (E := E) × ModelLin (E := E) := c • p + d • q
  have hwseg : w ∈ segment Real p q := by
    refine ⟨c, d, hc, hd, hcd, ?_⟩
    rfl
  have hwball :
      w ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a :=
    (convex_closedBall (varPhaseZero (I := I) (E := E) x) (a : Real)).segment_subset
      hp hq hwseg
  have hwsrc := hsrc hwball
  rw [← hu]
  simpa [w]
    using hwsrc

/-- Base component of an augmented variational flow. -/
def varBaseFlow
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E)) (t : Real) : ModelPhase (E := E) :=
  (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t).1

/-- Source control for the segment between two base trajectories, obtained from
the source-controlled augmented flow bound. -/
theorem varBase_segment_src_of_flow_bound
    [I.Boundaryless]
    (x : M)
    {a r : NNReal}
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z h : ModelPhase (E := E)} {t : Real}
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ u ∈ segment Real
        (varBaseFlow (E := E) Ψ z t)
        (varBaseFlow (E := E) Ψ (z + h) t),
      u ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x u).proj ∈ (extChartAt I x).source := by
  intro u hu
  exact
    varBase_segment_src_of_bound (I := I) (E := E) x
      (hbound (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) hz0 t)
      (hbound (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) hzh0 t)
      hsrc hu

/-- Linearized component of an augmented variational flow. -/
def varDerivFlow
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E)) (t : Real) : ModelLin (E := E) :=
  (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t).2

/-- The base trajectory of an augmented solution is continuous on any smaller
time interval. -/
theorem varBaseFlow_continuousOn_of_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {g : SmoothRiemannianMetric I M} {x : M}
    {z : ModelPhase (E := E)} {ε b : Real}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨ :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t) :
    ContinuousOn (fun t => varBaseFlow (E := E) Ψ z t)
      (Set.Icc (0 : Real) b) := by
  have hcont :
      ContinuousOn
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (Set.Icc (0 : Real) b) :=
    (HasDerivWithinAt.continuousOn hΨ).mono hb
  simpa [varBaseFlow] using continuous_fst.comp_continuousOn hcont

/-- The linearized trajectory of an augmented solution is continuous on any
smaller time interval. -/
theorem varDerivFlow_continuousOn_of_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {g : SmoothRiemannianMetric I M} {x : M}
    {z : ModelPhase (E := E)} {ε b : Real}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨ :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t) :
    ContinuousOn (fun t => varDerivFlow (E := E) Ψ z t)
      (Set.Icc (0 : Real) b) := by
  have hcont :
      ContinuousOn
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (Set.Icc (0 : Real) b) :=
    (HasDerivWithinAt.continuousOn hΨ).mono hb
  simpa [varDerivFlow] using continuous_snd.comp_continuousOn hcont

/-- The derivative of the model spray is bounded along a source-controlled base
trajectory on a compact time interval. -/
theorem modelSpray_fderiv_bound_on_baseFlow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {ε b : Real}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨz :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t)
    (hsrc : ∀ t ∈ Set.Icc (0 : Real) b,
      varBaseFlow (E := E) Ψ z t ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (varBaseFlow (E := E) Ψ z t)).proj ∈
          (extChartAt I x).source) :
    ∃ B : Real, ∀ t ∈ Set.Icc (0 : Real) b,
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B := by
  have hbase :
      ContinuousOn (fun t => varBaseFlow (E := E) Ψ z t)
        (Set.Icc (0 : Real) b) :=
    varBaseFlow_continuousOn_of_flow (E := E) hb hΨz
  have hDF :
      ContinuousOn
        (fun t =>
          fderiv Real (modelSpray (I := I) g x)
            (varBaseFlow (E := E) Ψ z t))
        (Set.Icc (0 : Real) b) := by
    intro t ht
    have hDFat :
        ContinuousAt
          (fderiv Real (modelSpray (I := I) g x))
          (varBaseFlow (E := E) Ψ z t) := by
      exact
        ((modelSpray_contDiffAt_of_mem (I := I) g x
          (hsrc t ht).1 (hsrc t ht).2).fderiv_right (m := 1)
          (by
            exact WithTop.coe_le_coe.2
              (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))).continuousAt
    exact hDFat.comp_continuousWithinAt (hbase.continuousWithinAt ht)
  exact isCompact_Icc.exists_bound_of_continuousOn hDF

/-- Uniform continuity of `D(modelSpray)` in a tube around a compact,
source-controlled base trajectory. -/
theorem modelSpray_fderiv_uniform_tube
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {K : Set Real} (hK : IsCompact K)
    {γ : Real -> ModelPhase (E := E)}
    (hγ : ContinuousOn γ K)
    (hsrc : ∀ t ∈ K,
      γ t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (γ t)).proj ∈ (extChartAt I x).source) :
    ∀ c > 0, ∃ δ > 0, ∀ t ∈ K, ∀ u : ModelPhase (E := E),
      dist u (γ t) < δ ->
        ‖fderiv Real (modelSpray (I := I) g x) u -
          fderiv Real (modelSpray (I := I) g x) (γ t)‖ ≤ c := by
  intro c hc
  let D : ModelPhase (E := E) -> ModelLin (E := E) :=
    fderiv Real (modelSpray (I := I) g x)
  have hcomp : IsCompact (γ '' K) :=
    hK.image_of_continuousOn hγ
  have hDcont : ∀ y ∈ γ '' K, ContinuousAt D y := by
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    exact
      ((modelSpray_contDiffAt_of_mem (I := I) g x
        (hsrc t ht).1 (hsrc t ht).2).fderiv_right (m := 1)
        (by
          exact WithTop.coe_le_coe.2
            (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))).continuousAt
  have hU :
      {p : ModelPhase (E := E) × ModelPhase (E := E) |
        p.1 ∈ γ '' K ->
          (D p.1, D p.2) ∈
            {q : ModelLin (E := E) × ModelLin (E := E) |
              dist q.1 q.2 < c}} ∈
        𝓤 (ModelPhase (E := E)) :=
    hcomp.uniformContinuousAt_of_continuousAt D hDcont
      (Metric.dist_mem_uniformity hc)
  rcases Metric.mem_uniformity_dist.mp hU with ⟨δ, hδ, hδsub⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht u hu
  have hpair :
      ((γ t, u) : ModelPhase (E := E) × ModelPhase (E := E)) ∈
        {p : ModelPhase (E := E) × ModelPhase (E := E) |
          p.1 ∈ γ '' K ->
            (D p.1, D p.2) ∈
              {q : ModelLin (E := E) × ModelLin (E := E) |
                dist q.1 q.2 < c}} :=
    hδsub (by simpa [dist_comm] using hu)
  have hγmem : γ t ∈ γ '' K := ⟨t, ht, rfl⟩
  have hdist : dist (D (γ t)) (D u) < c := hpair hγmem
  have hnorm : ‖D u - D (γ t)‖ < c := by
    have hdist' : dist (D u) (D (γ t)) < c := by
      simpa [dist_comm] using hdist
    simpa [D, dist_eq_norm] using hdist'
  simpa [D] using le_of_lt hnorm

@[simp] theorem varBaseFlow_zero_of_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)}
    (hΨ0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E)))) :
    varBaseFlow (E := E) Ψ z 0 = z := by
  simpa [varBaseFlow] using congrArg Prod.fst hΨ0

@[simp] theorem varDerivFlow_zero_of_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)}
    (hΨ0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E)))) :
    varDerivFlow (E := E) Ψ z 0 =
      ContinuousLinearMap.id Real (ModelPhase (E := E)) := by
  simpa [varDerivFlow] using congrArg Prod.snd hΨ0

/-- The base component of an augmented flow solves the original model ODE. -/
theorem varBaseFlow_hasDerivWithinAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (g : SmoothRiemannianMetric I M) (x : M)
    {z : ModelPhase (E := E)} {ε t : Real}
    (hΨ :
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t) :
    HasDerivWithinAt
      (varBaseFlow (E := E) Ψ z)
      (modelSpray (I := I) g x (varBaseFlow (E := E) Ψ z t))
      (Set.Icc (-ε) ε) t := by
  let Z := ModelPhase (E := E)
  let L := ModelLin (E := E)
  let p : Z := z
  let A : L := ContinuousLinearMap.id Real Z
  have hfst :
      HasFDerivWithinAt (fun q : Z × L => q.1)
        (ContinuousLinearMap.fst Real Z L) Set.univ
        (Ψ (p, A) t) :=
    (hasFDerivAt_fst (𝕜 := Real) (E := Z) (F := L)
      (p := Ψ (p, A) t)).hasFDerivWithinAt
  have hmaps : Set.MapsTo (Ψ (p, A)) (Set.Icc (-ε) ε) Set.univ := by
    intro y hy
    trivial
  have hcomp := hfst.comp_hasDerivWithinAt t hΨ hmaps
  simpa [Function.comp_def, varBaseFlow, varSpray, Z, L, p, A] using hcomp

/-- The linear component of an augmented flow solves the variational equation. -/
theorem varDerivFlow_hasDerivWithinAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (g : SmoothRiemannianMetric I M) (x : M)
    {z : ModelPhase (E := E)} {ε t : Real}
    (hΨ :
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t) :
    HasDerivWithinAt
      (varDerivFlow (E := E) Ψ z)
      ((fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)).comp
        (varDerivFlow (E := E) Ψ z t))
      (Set.Icc (-ε) ε) t := by
  let Z := ModelPhase (E := E)
  let L := ModelLin (E := E)
  let p : Z := z
  let A : L := ContinuousLinearMap.id Real Z
  have hsnd :
      HasFDerivWithinAt (fun q : Z × L => q.2)
        (ContinuousLinearMap.snd Real Z L) Set.univ
        (Ψ (p, A) t) :=
    (hasFDerivAt_snd (𝕜 := Real) (E := Z) (F := L)
      (p := Ψ (p, A) t)).hasFDerivWithinAt
  have hmaps : Set.MapsTo (Ψ (p, A)) (Set.Icc (-ε) ε) Set.univ := by
    intro y hy
    trivial
  have hcomp := hsnd.comp_hasDerivWithinAt t hΨ hmaps
  simpa [Function.comp_def, varBaseFlow, varDerivFlow, varSpray, Z, L, p, A] using hcomp

/-- Error between the base flow at `z + h` and the linearized approximation
from the augmented flow at `z`. -/
def varError
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real) : ModelPhase (E := E) :=
  varBaseFlow (E := E) Ψ (z + h) t -
    varBaseFlow (E := E) Ψ z t -
    varDerivFlow (E := E) Ψ z t h

/-- The variational approximation error is continuous on any smaller time
interval where both augmented trajectories solve the ODE. -/
theorem varError_continuousOn_of_flow
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {g : SmoothRiemannianMetric I M} {x : M}
    {z h : ModelPhase (E := E)} {ε b : Real}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨzh :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t)
    (hΨz :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t) :
    ContinuousOn (varError (E := E) Ψ z h) (Set.Icc (0 : Real) b) := by
  have hbase_zh :
      ContinuousOn (fun t => varBaseFlow (E := E) Ψ (z + h) t)
        (Set.Icc (0 : Real) b) :=
    varBaseFlow_continuousOn_of_flow (E := E) hb hΨzh
  have hbase_z :
      ContinuousOn (fun t => varBaseFlow (E := E) Ψ z t)
        (Set.Icc (0 : Real) b) :=
    varBaseFlow_continuousOn_of_flow (E := E) hb hΨz
  have hder_z :
      ContinuousOn (fun t => varDerivFlow (E := E) Ψ z t)
        (Set.Icc (0 : Real) b) :=
    varDerivFlow_continuousOn_of_flow (E := E) hb hΨz
  have happ :
      ContinuousOn (fun t => varDerivFlow (E := E) Ψ z t h)
        (Set.Icc (0 : Real) b) :=
    hder_z.clm_apply continuousOn_const
  simpa [varError] using (hbase_zh.sub hbase_z).sub happ

/-- Raw right-hand side of the error equation. -/
def varErrorRHS
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real) : ModelPhase (E := E) :=
  modelSpray (I := I) g x (varBaseFlow (E := E) Ψ (z + h) t) -
    modelSpray (I := I) g x (varBaseFlow (E := E) Ψ z t) -
    fderiv Real (modelSpray (I := I) g x)
      (varBaseFlow (E := E) Ψ z t)
      (varDerivFlow (E := E) Ψ z t h)

/-- Taylor residual part of the error equation. -/
def varTaylorRem
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real) : ModelPhase (E := E) :=
  modelSpray (I := I) g x (varBaseFlow (E := E) Ψ (z + h) t) -
    modelSpray (I := I) g x (varBaseFlow (E := E) Ψ z t) -
    fderiv Real (modelSpray (I := I) g x)
      (varBaseFlow (E := E) Ψ z t)
      (varBaseFlow (E := E) Ψ (z + h) t -
        varBaseFlow (E := E) Ψ z t)

/-- Pointwise Taylor-residual estimate for the error equation. -/
theorem varTaylorRem_norm_le
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real)
    {s : Set (ModelPhase (E := E))} (hs : Convex Real s)
    (hctrl : ∀ q ∈ s,
      q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hz : varBaseFlow (E := E) Ψ z t ∈ s)
    (hzh : varBaseFlow (E := E) Ψ (z + h) t ∈ s)
    {C : Real}
    (hD : ∀ u ∈ s,
      ‖fderiv Real (modelSpray (I := I) g x) u -
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ C) :
    ‖varTaylorRem (I := I) g x Ψ z h t‖ ≤
      C * ‖varBaseFlow (E := E) Ψ (z + h) t -
        varBaseFlow (E := E) Ψ z t‖ := by
  simpa [varTaylorRem] using
    modelSpray_taylor_bound (I := I) g x hs hctrl hz hzh hD

/-- Lipschitz dependence of the augmented flow controls the separation of the
base components. -/
theorem varBaseFlow_dist_le_of_lipschitz
    (x : M)
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {r L' : NNReal} {z h : ModelPhase (E := E)} {t : Real}
    (hLip :
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    dist (varBaseFlow (E := E) Ψ (z + h) t)
      (varBaseFlow (E := E) Ψ z t) ≤ (L' : Real) * ‖h‖ := by
  let Z := ModelPhase (E := E)
  let L := ModelLin (E := E)
  let pzh : Z × L := (z + h, ContinuousLinearMap.id Real Z)
  let pz : Z × L := (z, ContinuousLinearMap.id Real Z)
  have hdist := hLip.dist_le_mul pzh hzh pz hz
  have hfst :
      dist (varBaseFlow (E := E) Ψ (z + h) t)
        (varBaseFlow (E := E) Ψ z t) ≤
          dist (Ψ pzh t) (Ψ pz t) := by
    change dist (Ψ pzh t).1 (Ψ pz t).1 ≤ dist (Ψ pzh t) (Ψ pz t)
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hpdist : dist pzh pz = ‖h‖ := by
    have hzdist : dist (z + h) z = ‖h‖ := by
      rw [dist_eq_norm]
      have hsub : z + h - z = h := by
        abel
      rw [hsub]
    simp [pzh, pz, dist_prod_same_right, hzdist]
  exact hfst.trans (by simpa [hpdist] using hdist)

/-- The Lipschitz flow estimate turns the compact tube continuity of
`D(modelSpray)` into a uniform derivative-difference bound on trajectory
segments for sufficiently small initial perturbations. -/
theorem modelSpray_fderiv_segment_small_of_lipschitz
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {ε b : Real} {r L' : NNReal}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨz :
      ∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
          (varSpray (I := I) g x
            (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
          (Set.Icc (-ε) ε) t)
    (hsrc_base : ∀ t ∈ Set.Icc (0 : Real) b,
      varBaseFlow (E := E) Ψ z t ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (varBaseFlow (E := E) Ψ z t)).proj ∈
          (extChartAt I x).source)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ η > 0, ∃ ρ > 0, ∀ h : ModelPhase (E := E),
      (L' : Real) * ‖h‖ < ρ ->
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r ->
      ∀ t ∈ Set.Ico (0 : Real) b,
        ∀ u ∈ segment Real
            (varBaseFlow (E := E) Ψ z t)
            (varBaseFlow (E := E) Ψ (z + h) t),
          ‖fderiv Real (modelSpray (I := I) g x) u -
            fderiv Real (modelSpray (I := I) g x)
              (varBaseFlow (E := E) Ψ z t)‖ ≤ η := by
  intro η hη
  have hbase :
      ContinuousOn (fun t => varBaseFlow (E := E) Ψ z t)
        (Set.Icc (0 : Real) b) :=
    varBaseFlow_continuousOn_of_flow (E := E) hb hΨz
  obtain ⟨ρ, hρ, hρsmall⟩ :=
    modelSpray_fderiv_uniform_tube (I := I) g x
      (K := Set.Icc (0 : Real) b) isCompact_Icc hbase hsrc_base η hη
  refine ⟨ρ, hρ, ?_⟩
  intro h hsmall hzh0 t ht u hu
  have htcc : t ∈ Set.Icc (0 : Real) b := ⟨ht.1, le_of_lt ht.2⟩
  have hsegball :
      u ∈ Metric.closedBall
          (varBaseFlow (E := E) Ψ z t)
          (dist (varBaseFlow (E := E) Ψ z t)
            (varBaseFlow (E := E) Ψ (z + h) t)) :=
    segment_subset_closedBall_left
      (varBaseFlow (E := E) Ψ z t)
      (varBaseFlow (E := E) Ψ (z + h) t) hu
  have hbase_dist :
      dist (varBaseFlow (E := E) Ψ z t)
        (varBaseFlow (E := E) Ψ (z + h) t) ≤ (L' : Real) * ‖h‖ := by
    simpa [dist_comm] using
      varBaseFlow_dist_le_of_lipschitz (E := E) x (hLip t ht) hz0 hzh0
  have hu_dist :
      dist u (varBaseFlow (E := E) Ψ z t) < ρ := by
    have hle :
        dist u (varBaseFlow (E := E) Ψ z t) ≤
          dist (varBaseFlow (E := E) Ψ z t)
            (varBaseFlow (E := E) Ψ (z + h) t) := by
      simpa [Metric.mem_closedBall] using hsegball
    exact lt_of_le_of_lt (hle.trans hbase_dist) hsmall
  exact hρsmall t htcc u hu_dist

/-- Taylor residual estimate after applying the augmented-flow Lipschitz bound
to the base separation. -/
theorem varTaylorRem_norm_le_of_lipschitz
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real)
    {s : Set (ModelPhase (E := E))} (hs : Convex Real s)
    (hctrl : ∀ q ∈ s,
      q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hz : varBaseFlow (E := E) Ψ z t ∈ s)
    (hzh : varBaseFlow (E := E) Ψ (z + h) t ∈ s)
    {C : Real}
    (hD : ∀ u ∈ s,
      ‖fderiv Real (modelSpray (I := I) g x) u -
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    {r L' : NNReal}
    (hLip :
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ‖varTaylorRem (I := I) g x Ψ z h t‖ ≤
      C * ((L' : Real) * ‖h‖) := by
  have hTaylor :=
    varTaylorRem_norm_le (I := I) g x Ψ z h t hs hctrl hz hzh hD
  have hsep :=
    varBaseFlow_dist_le_of_lipschitz (I := I) (E := E) x hLip hz0 hzh0
  rw [dist_eq_norm] at hsep
  have hC : 0 ≤ C := (norm_nonneg _).trans (hD _ hz)
  exact hTaylor.trans (mul_le_mul_of_nonneg_left hsep hC)

/-- Gronwall-ready pointwise estimate for the approximation-error RHS. -/
theorem varErrorRHS_norm_le
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real)
    {s : Set (ModelPhase (E := E))} (hs : Convex Real s)
    (hctrl : ∀ q ∈ s,
      q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hz : varBaseFlow (E := E) Ψ z t ∈ s)
    (hzh : varBaseFlow (E := E) Ψ (z + h) t ∈ s)
    {B C : Real}
    (hB :
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B)
    (hD : ∀ u ∈ s,
      ‖fderiv Real (modelSpray (I := I) g x) u -
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    {r L' : NNReal}
    (hLip :
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ‖varErrorRHS (I := I) g x Ψ z h t‖ ≤
      B * ‖varError (E := E) Ψ z h t‖ +
        C * ((L' : Real) * ‖h‖) := by
  let D :=
    fderiv Real (modelSpray (I := I) g x)
      (varBaseFlow (E := E) Ψ z t)
  have hRem :
      ‖varTaylorRem (I := I) g x Ψ z h t‖ ≤
        C * ((L' : Real) * ‖h‖) :=
    varTaylorRem_norm_le_of_lipschitz (I := I) g x Ψ z h t
      hs hctrl hz hzh hD hLip hz0 hzh0
  have hLin0 :
      ‖D (varError (E := E) Ψ z h t)‖ ≤
        ‖D‖ * ‖varError (E := E) Ψ z h t‖ :=
    D.le_opNorm _
  have hLin :
      ‖D (varError (E := E) Ψ z h t)‖ ≤
        B * ‖varError (E := E) Ψ z h t‖ := by
    exact hLin0.trans
      (mul_le_mul_of_nonneg_right (by simpa [D] using hB) (norm_nonneg _))
  have hEq :
      varErrorRHS (I := I) g x Ψ z h t =
        varTaylorRem (I := I) g x Ψ z h t +
          D (varError (E := E) Ψ z h t) := by
    simp only [varErrorRHS, varTaylorRem, varError, D]
    simp only [map_sub]
    abel
  rw [hEq]
  calc
    ‖varTaylorRem (I := I) g x Ψ z h t +
        D (varError (E := E) Ψ z h t)‖
        ≤ ‖D (varError (E := E) Ψ z h t)‖ +
            ‖varTaylorRem (I := I) g x Ψ z h t‖ := by
          simpa [add_comm] using
            norm_add_le
              (varTaylorRem (I := I) g x Ψ z h t)
              (D (varError (E := E) Ψ z h t))
    _ ≤ B * ‖varError (E := E) Ψ z h t‖ +
        C * ((L' : Real) * ‖h‖) :=
      add_le_add hLin hRem

/-- The raw error RHS is the Taylor residual plus the linearized equation
applied to the current error. -/
theorem varErrorRHS_eq_taylorRem_add
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E)) (t : Real) :
    varErrorRHS (I := I) g x Ψ z h t =
      varTaylorRem (I := I) g x Ψ z h t +
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)
          (varError (E := E) Ψ z h t) := by
  simp only [varErrorRHS, varTaylorRem, varError]
  simp only [map_sub]
  abel

/-- The approximation error satisfies the expected inhomogeneous linear ODE. -/
theorem varError_hasDerivWithinAt
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (g : SmoothRiemannianMetric I M) (x : M)
    {z h : ModelPhase (E := E)} {ε t : Real}
    (hΨzh :
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz :
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t) :
    HasDerivWithinAt
      (varError (E := E) Ψ z h)
      (varErrorRHS (I := I) g x Ψ z h t)
      (Set.Icc (-ε) ε) t := by
  let Z := ModelPhase (E := E)
  have hbase_zh :
      HasDerivWithinAt
        (varBaseFlow (E := E) Ψ (z + h))
        (modelSpray (I := I) g x
          (varBaseFlow (E := E) Ψ (z + h) t))
        (Set.Icc (-ε) ε) t :=
    varBaseFlow_hasDerivWithinAt (I := I) (E := E) g x hΨzh
  have hbase_z :
      HasDerivWithinAt
        (varBaseFlow (E := E) Ψ z)
        (modelSpray (I := I) g x
          (varBaseFlow (E := E) Ψ z t))
        (Set.Icc (-ε) ε) t :=
    varBaseFlow_hasDerivWithinAt (I := I) (E := E) g x hΨz
  have hA :
      HasDerivWithinAt
        (varDerivFlow (E := E) Ψ z)
        ((fderiv Real (modelSpray (I := I) g x)
            (varBaseFlow (E := E) Ψ z t)).comp
          (varDerivFlow (E := E) Ψ z t))
        (Set.Icc (-ε) ε) t :=
    varDerivFlow_hasDerivWithinAt (I := I) (E := E) g x hΨz
  have hh :
      HasDerivWithinAt (fun _ : Real => h) (0 : Z) (Set.Icc (-ε) ε) t := by
    simpa using (hasDerivWithinAt_const (c := h) (s := Set.Icc (-ε) ε) (x := t))
  have hAh :
      HasDerivWithinAt
        (fun t : Real => varDerivFlow (E := E) Ψ z t h)
        (((fderiv Real (modelSpray (I := I) g x)
            (varBaseFlow (E := E) Ψ z t)).comp
          (varDerivFlow (E := E) Ψ z t)) h)
        (Set.Icc (-ε) ε) t := by
    simpa [ContinuousLinearMap.comp_apply] using hA.clm_apply hh
  have herr := (hbase_zh.sub hbase_z).sub hAh
  simpa [varError, varErrorRHS, ContinuousLinearMap.comp_apply, Z] using herr

/-- Restrict the approximation-error ODE from the Picard time interval to a
smaller closed interval. -/
theorem varError_hasDerivWithinAt_Icc
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (g : SmoothRiemannianMetric I M) (x : M)
    {z h : ModelPhase (E := E)} {ε a b t : Real}
    (hab : Set.Icc a b ⊆ Set.Icc (-ε) ε)
    (hΨzh :
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz :
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t) :
    HasDerivWithinAt
      (varError (E := E) Ψ z h)
      (varErrorRHS (I := I) g x Ψ z h t)
      (Set.Icc a b) t :=
  (varError_hasDerivWithinAt (I := I) g x hΨzh hΨz).mono hab

/-- The approximation error is zero at the initial time for a flow with the
expected augmented initial conditions. -/
theorem varError_zero
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    (z h : ModelPhase (E := E))
    (hΨzh :
      Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hΨz :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E)))) :
    varError (E := E) Ψ z h 0 = 0 := by
  simp [varError, varBaseFlow, varDerivFlow, hΨzh, hΨz]

/-- If the variational approximation error is little-o in the initial
perturbation, then the linear component of the augmented flow is the Frechet
derivative of the base flow at the fixed time. -/
theorem varBaseFlow_hasFDerivAt_of_error
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {t : Real}
    (herr :
      (fun h : ModelPhase (E := E) => varError (E := E) Ψ z h t)
        =o[𝓝 0] (fun h : ModelPhase (E := E) => h)) :
    HasFDerivAt
      (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' t)
      (varDerivFlow (E := E) Ψ z t)
      z := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa [varError] using herr

/-- Fixed-time C1-dependence checkpoint from an eventual Gronwall bound with a
vanishing Taylor-residual coefficient. -/
theorem varBaseFlow_hasFDerivAt_of_gronwall
    {Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E)}
    {z : ModelPhase (E := E)} {t B L T : Real}
    {C : ModelPhase (E := E) -> Real}
    (hC : Tendsto C (𝓝 0) (𝓝 0))
    (hbound : ∀ᶠ h in 𝓝 (0 : ModelPhase (E := E)),
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound 0 B (C h * (L * ‖h‖)) T) :
    HasFDerivAt
      (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' t)
      (varDerivFlow (E := E) Ψ z t)
      z := by
  apply varBaseFlow_hasFDerivAt_of_error (E := E)
  exact isLittleO_of_gronwall_bound
    (f := fun h : ModelPhase (E := E) => varError (E := E) Ψ z h t)
    (C := C) (B := B) (L := L) (T := T) hC hbound

/-- Gronwall bound for the approximation error once the error RHS has the
standard linear-plus-forcing estimate. -/
theorem varError_norm_le_gronwall
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {a b δ K ε : Real}
    (hcont : ContinuousOn (varError (E := E) Ψ z h) (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt
        (varError (E := E) Ψ z h)
        (varErrorRHS (I := I) g x Ψ z h t)
        (Set.Ici t) t)
    (ha : ‖varError (E := E) Ψ z h a‖ ≤ δ)
    (hbound : ∀ t ∈ Set.Ico a b,
      ‖varErrorRHS (I := I) g x Ψ z h t‖ ≤
        K * ‖varError (E := E) Ψ z h t‖ + ε) :
    ∀ t ∈ Set.Icc a b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound δ K ε (t - a) :=
  norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv ha hbound

/-- Version of `varError_norm_le_gronwall` for derivatives known on the
closed interval itself. -/
theorem varError_norm_le_gronwall_Icc
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {a b δ K ε : Real}
    (hcont : ContinuousOn (varError (E := E) Ψ z h) (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt
        (varError (E := E) Ψ z h)
        (varErrorRHS (I := I) g x Ψ z h t)
        (Set.Icc a b) t)
    (ha : ‖varError (E := E) Ψ z h a‖ ≤ δ)
    (hbound : ∀ t ∈ Set.Ico a b,
      ‖varErrorRHS (I := I) g x Ψ z h t‖ ≤
        K * ‖varError (E := E) Ψ z h t‖ + ε) :
    ∀ t ∈ Set.Icc a b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound δ K ε (t - a) :=
  varError_norm_le_gronwall (I := I) g x Ψ z h hcont
    (fun t ht =>
      (hderiv t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht))
    ha hbound

/-- Main checked Gronwall estimate for the variational approximation error on
a fixed forward time interval. -/
theorem varError_norm_le_gronwall_of_flow_bounds
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {ε b B C : Real} {r L' : NNReal} {s : Set (ModelPhase (E := E))}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hcont : ContinuousOn (varError (E := E) Ψ z h) (Set.Icc (0 : Real) b))
    (hΨzh : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨzh0 :
      Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hΨz0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hs : Convex Real s)
    (hctrl : ∀ q ∈ s,
      q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hz : ∀ t ∈ Set.Ico (0 : Real) b, varBaseFlow (E := E) Ψ z t ∈ s)
    (hzh : ∀ t ∈ Set.Ico (0 : Real) b,
      varBaseFlow (E := E) Ψ (z + h) t ∈ s)
    (hB : ∀ t ∈ Set.Ico (0 : Real) b,
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B)
    (hD : ∀ t ∈ Set.Ico (0 : Real) b, ∀ u ∈ s,
      ‖fderiv Real (modelSpray (I := I) g x) u -
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ t ∈ Set.Icc (0 : Real) b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound 0 B (C * ((L' : Real) * ‖h‖)) (t - 0) := by
  refine
    varError_norm_le_gronwall_Icc (I := I) g x Ψ z h hcont
      (fun t ht => varError_hasDerivWithinAt_Icc (I := I) g x hb
        (hΨzh t ht) (hΨz t ht))
      ?_ ?_
  · have hzero := varError_zero (E := E) z h hΨzh0 hΨz0
    simp [hzero]
  · intro t ht
    exact
      varErrorRHS_norm_le (I := I) g x Ψ z h t hs hctrl
        (hz t ht) (hzh t ht) (hB t ht) (hD t ht)
        (hLip t ht) hz0 hzh0

/-- Time-dependent convex-set version of
`varError_norm_le_gronwall_of_flow_bounds`.

This is the useful form for the C1-dependence proof: at each time the Taylor
estimate can be taken on the segment between the two base trajectories. -/
theorem varError_norm_le_gronwall_of_time_sets
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {ε b B C : Real} {r L' : NNReal}
    {s : Real -> Set (ModelPhase (E := E))}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hcont : ContinuousOn (varError (E := E) Ψ z h) (Set.Icc (0 : Real) b))
    (hΨzh : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨzh0 :
      Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hΨz0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hs : ∀ t ∈ Set.Ico (0 : Real) b, Convex Real (s t))
    (hctrl : ∀ t ∈ Set.Ico (0 : Real) b, ∀ q ∈ s t,
      q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hz : ∀ t ∈ Set.Ico (0 : Real) b, varBaseFlow (E := E) Ψ z t ∈ s t)
    (hzh : ∀ t ∈ Set.Ico (0 : Real) b,
      varBaseFlow (E := E) Ψ (z + h) t ∈ s t)
    (hB : ∀ t ∈ Set.Ico (0 : Real) b,
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B)
    (hD : ∀ t ∈ Set.Ico (0 : Real) b, ∀ u ∈ s t,
      ‖fderiv Real (modelSpray (I := I) g x) u -
        fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ t ∈ Set.Icc (0 : Real) b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound 0 B (C * ((L' : Real) * ‖h‖)) (t - 0) := by
  refine
    varError_norm_le_gronwall_Icc (I := I) g x Ψ z h hcont
      (fun t ht => varError_hasDerivWithinAt_Icc (I := I) g x hb
        (hΨzh t ht) (hΨz t ht))
      ?_ ?_
  · have hzero := varError_zero (E := E) z h hΨzh0 hΨz0
    simp [hzero]
  · intro t ht
    exact
      varErrorRHS_norm_le (I := I) g x Ψ z h t (hs t ht) (hctrl t ht)
        (hz t ht) (hzh t ht) (hB t ht) (hD t ht)
        (hLip t ht) hz0 hzh0

/-- Segment-specialized Gronwall estimate for the variational approximation
error.

This is the form closest to the differentiability proof: the Taylor estimate is
taken on the segment from `Phi z t` to `Phi (z + h) t`. -/
theorem varError_norm_le_gronwall_of_segment_bounds
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {ε b B C : Real} {r L' : NNReal}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hcont : ContinuousOn (varError (E := E) Ψ z h) (Set.Icc (0 : Real) b))
    (hΨzh : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz : ∀ t ∈ Set.Icc (0 : Real) b,
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨzh0 :
      Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hΨz0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hctrl : ∀ t ∈ Set.Ico (0 : Real) b,
      ∀ q ∈ segment Real
          (varBaseFlow (E := E) Ψ z t)
          (varBaseFlow (E := E) Ψ (z + h) t),
        q ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
          (phaseOfModel (I := I) x q).proj ∈ (extChartAt I x).source)
    (hB : ∀ t ∈ Set.Ico (0 : Real) b,
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B)
    (hD : ∀ t ∈ Set.Ico (0 : Real) b,
      ∀ u ∈ segment Real
          (varBaseFlow (E := E) Ψ z t)
          (varBaseFlow (E := E) Ψ (z + h) t),
        ‖fderiv Real (modelSpray (I := I) g x) u -
          fderiv Real (modelSpray (I := I) g x)
            (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ t ∈ Set.Icc (0 : Real) b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound 0 B (C * ((L' : Real) * ‖h‖)) (t - 0) := by
  refine
    varError_norm_le_gronwall_of_time_sets (I := I) g x Ψ z h hb
      hcont hΨzh hΨz hΨzh0 hΨz0 ?_ hctrl ?_ ?_ hB hD hLip hz0 hzh0
  · intro t _ht
    exact convex_segment (𝕜 := Real)
      (varBaseFlow (E := E) Ψ z t)
      (varBaseFlow (E := E) Ψ (z + h) t)
  · intro t _ht
    exact left_mem_segment Real
      (varBaseFlow (E := E) Ψ z t)
      (varBaseFlow (E := E) Ψ (z + h) t)
  · intro t _ht
    exact right_mem_segment Real
      (varBaseFlow (E := E) Ψ z t)
      (varBaseFlow (E := E) Ψ (z + h) t)

/-- Segment-specialized Gronwall estimate using source control and continuity
directly from the bounded augmented flow. -/
theorem varError_norm_le_gronwall_of_segment_bounds_flow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z h : ModelPhase (E := E))
    {a r : NNReal} {ε b B C : Real} {L' : NNReal}
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hΨzh : ∀ t ∈ Set.Icc (-ε) ε,
      HasDerivWithinAt
        (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨz : ∀ t ∈ Set.Icc (-ε) ε,
      HasDerivWithinAt
        (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        (varSpray (I := I) g x
          (Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) t))
        (Set.Icc (-ε) ε) t)
    (hΨzh0 :
      Ψ (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hΨz0 :
      Ψ (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 =
        (z, ContinuousLinearMap.id Real (ModelPhase (E := E))))
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hB : ∀ t ∈ Set.Ico (0 : Real) b,
      ‖fderiv Real (modelSpray (I := I) g x)
          (varBaseFlow (E := E) Ψ z t)‖ ≤ B)
    (hD : ∀ t ∈ Set.Ico (0 : Real) b,
      ∀ u ∈ segment Real
          (varBaseFlow (E := E) Ψ z t)
          (varBaseFlow (E := E) Ψ (z + h) t),
        ‖fderiv Real (modelSpray (I := I) g x) u -
          fderiv Real (modelSpray (I := I) g x)
            (varBaseFlow (E := E) Ψ z t)‖ ≤ C)
    (hLip : ∀ t ∈ Set.Ico (0 : Real) b,
      LipschitzOnWith L'
        (fun p => Ψ p t)
        (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hz0 :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)
    (hzh0 :
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.closedBall (varPhaseZero (I := I) (E := E) x) r) :
    ∀ t ∈ Set.Icc (0 : Real) b,
      ‖varError (E := E) Ψ z h t‖ ≤
        gronwallBound 0 B (C * ((L' : Real) * ‖h‖)) (t - 0) := by
  refine
    varError_norm_le_gronwall_of_segment_bounds (I := I) g x Ψ z h hb
      ?_ (fun t ht => hΨzh t (hb ht)) (fun t ht => hΨz t (hb ht))
      hΨzh0 hΨz0 ?_ hB hD hLip hz0 hzh0
  · exact varError_continuousOn_of_flow (E := E) hb hΨzh hΨz
  · intro t _ht
    exact
      varBase_segment_src_of_flow_bound (I := I) (E := E) x
        hbound hsrc hz0 hzh0

/-- C1-dependence checkpoint: for a source-controlled augmented flow, the
linearized component is the Frechet derivative of the fixed-time base flow at
any interior initial phase. -/
theorem varBaseFlow_hasFDerivAt_of_flow
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ψ :
      (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
        ModelPhase (E := E) × ModelLin (E := E))
    (z : ModelPhase (E := E))
    {a r L' : NNReal} {ε b : Real}
    (hb0 : 0 ≤ b)
    (hb : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε)
    (hflow :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        Ψ p 0 = p ∧
          ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (Ψ p)
              (varSpray (I := I) g x (Ψ p t))
              (Set.Icc (-ε) ε) t)
    (hbound :
      ∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
        ∀ t : Real,
          Ψ p t ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) a)
    (hsrc :
      Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
        {p : ModelPhase (E := E) × ModelLin (E := E) |
          p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x p.1).proj ∈ (extChartAt I x).source})
    (hLip :
      ∀ t ∈ Set.Icc (-ε) ε,
        LipschitzOnWith L'
          (fun p => Ψ p t)
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r))
    (hzopen :
      (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
        Metric.ball (varPhaseZero (I := I) (E := E) x) r) :
    HasFDerivAt
      (fun z' : ModelPhase (E := E) => varBaseFlow (E := E) Ψ z' b)
      (varDerivFlow (E := E) Ψ z b)
      z := by
  let pz : ModelPhase (E := E) × ModelLin (E := E) :=
    (z, ContinuousLinearMap.id Real (ModelPhase (E := E)))
  have hz0 : pz ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r :=
    Metric.ball_subset_closedBall hzopen
  have hsrc_base : ∀ t ∈ Set.Icc (0 : Real) b,
      varBaseFlow (E := E) Ψ z t ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (varBaseFlow (E := E) Ψ z t)).proj ∈
          (extChartAt I x).source := by
    intro t ht
    have hs := hsrc (hbound pz hz0 t)
    simpa [pz, varBaseFlow] using hs
  obtain ⟨B, hBcc⟩ :=
    modelSpray_fderiv_bound_on_baseFlow (I := I) g x hb
      (hflow pz hz0).2 hsrc_base
  have hDsmall :=
    modelSpray_fderiv_segment_small_of_lipschitz (I := I) g x
      (Ψ := Ψ) (z := z) (ε := ε) (b := b) (r := r) (L' := L') hb
      (hflow pz hz0).2 hsrc_base
      (fun t ht => hLip t (hb ⟨ht.1, le_of_lt ht.2⟩)) hz0
  have hinit_cont :
      ContinuousAt
        (fun h : ModelPhase (E := E) =>
          (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))))
        0 := by
    have hleft : ContinuousAt (fun h : ModelPhase (E := E) => z + h) 0 := by
      simpa using (continuousAt_const.add continuousAt_id :
        ContinuousAt (fun h : ModelPhase (E := E) => z + h) 0)
    have hright :
        ContinuousAt
          (fun _h : ModelPhase (E := E) =>
            ContinuousLinearMap.id Real (ModelPhase (E := E))) 0 :=
      continuousAt_const
    exact hleft.prodMk_nhds hright
  have hzh_eventually :
      ∀ᶠ h : ModelPhase (E := E) in 𝓝 0,
        (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
          Metric.closedBall (varPhaseZero (I := I) (E := E) x) r := by
    have hzopen0 :
        (fun h : ModelPhase (E := E) =>
          (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E)))) 0 ∈
            Metric.ball (varPhaseZero (I := I) (E := E) x) r := by
      simpa using hzopen
    filter_upwards
      [hinit_cont.eventually (Metric.isOpen_ball.mem_nhds hzopen0)] with h hh
    exact Metric.ball_subset_closedBall hh
  have herr :
      (fun h : ModelPhase (E := E) => varError (E := E) Ψ z h b)
        =o[𝓝 0] (fun h : ModelPhase (E := E) => h) := by
    refine
      isLittleO_of_gronwall_bound_eventually
        (X := ModelPhase (E := E)) (Y := ModelPhase (E := E))
        (B := B) (L := (L' : Real)) (T := b) ?_
    intro η hη
    obtain ⟨ρ, hρ, hDρ⟩ := hDsmall η hη
    have hmul_cont :
        Continuous
          (fun h : ModelPhase (E := E) => (L' : Real) * ‖h‖) :=
      continuous_const.mul continuous_norm
    have hsmall_eventually :
        ∀ᶠ h : ModelPhase (E := E) in 𝓝 0, (L' : Real) * ‖h‖ < ρ := by
      have hball :=
        (hmul_cont.continuousAt (x := (0 : ModelPhase (E := E)))).eventually
          (Metric.ball_mem_nhds
            ((L' : Real) * ‖(0 : ModelPhase (E := E))‖) hρ)
      filter_upwards [hball] with h hh
      have habs : |(L' : Real) * ‖h‖| < ρ := by
        simpa [Real.dist_eq] using hh
      exact (abs_lt.1 habs).2
    filter_upwards [hzh_eventually, hsmall_eventually] with h hzh0 hsmall
    let pzh : ModelPhase (E := E) × ModelLin (E := E) :=
      (z + h, ContinuousLinearMap.id Real (ModelPhase (E := E)))
    have hD : ∀ t ∈ Set.Ico (0 : Real) b,
      ∀ u ∈ segment Real
          (varBaseFlow (E := E) Ψ z t)
          (varBaseFlow (E := E) Ψ (z + h) t),
        ‖fderiv Real (modelSpray (I := I) g x) u -
          fderiv Real (modelSpray (I := I) g x)
            (varBaseFlow (E := E) Ψ z t)‖ ≤ η :=
      hDρ h hsmall hzh0
    have hgr :=
      varError_norm_le_gronwall_of_segment_bounds_flow (I := I) g x Ψ z h
        (a := a) (r := r) (L' := L') hb
        (hflow pzh hzh0).2 (hflow pz hz0).2
        (hflow pzh hzh0).1 (hflow pz hz0).1
        hbound hsrc
        (fun t ht => hBcc t ⟨ht.1, le_of_lt ht.2⟩)
        hD
        (fun t ht => hLip t (hb ⟨ht.1, le_of_lt ht.2⟩))
        hz0 hzh0
    simpa using hgr b ⟨hb0, le_rfl⟩
  exact varBaseFlow_hasFDerivAt_of_error (E := E) herr

/-- Local augmented variational flow whose base component has the variational
component as Frechet derivative at every interior initial phase, for forward
times in the Picard interval. -/
theorem varFlow_hasFDerivAt
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (a r : NNReal), ∃ (_hr : 0 < r),
      ∃ Ψ :
          (ModelPhase (E := E) × ModelLin (E := E)) -> Real ->
            ModelPhase (E := E) × ModelLin (E := E),
        (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
          Ψ p 0 = p ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (Ψ p)
                (varSpray (I := I) g x (Ψ p t))
                (Set.Icc (-ε) ε) t) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              Ψ p t ∈
                Metric.closedBall (varPhaseZero (I := I) (E := E) x) a) ∧
          (Metric.closedBall (varPhaseZero (I := I) (E := E) x) a ⊆
            {p : ModelPhase (E := E) × ModelLin (E := E) |
              p.1 ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x p.1).proj ∈
                  (extChartAt I x).source}) ∧
          (∀ p ∈ Metric.closedBall (varPhaseZero (I := I) (E := E) x) r,
            ∀ t : Real,
              (Ψ p t).1 ∈
                (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (Ψ p t).1).proj ∈
                  (extChartAt I x).source) ∧
          ∃ L' : NNReal,
            (∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun p => Ψ p t)
                (Metric.closedBall (varPhaseZero (I := I) (E := E) x) r)) ∧
            ∀ b ∈ Set.Icc (0 : Real) ε,
              ∀ z : ModelPhase (E := E),
                (z, ContinuousLinearMap.id Real (ModelPhase (E := E))) ∈
                  Metric.ball (varPhaseZero (I := I) (E := E) x) r ->
                HasFDerivAt
                  (fun z' : ModelPhase (E := E) =>
                    varBaseFlow (E := E) Ψ z' b)
                  (varDerivFlow (E := E) Ψ z b)
                  z := by
  obtain ⟨ε, hε, a, r, hr, Ψ, hflow, hbound, hsrc_ball, hsrc_flow, L', hLip⟩ :=
    varFlow_src_bound (I := I) g x
  refine ⟨ε, hε, a, r, hr, Ψ, hflow, hbound, hsrc_ball, hsrc_flow, L', hLip, ?_⟩
  intro b hb z hzopen
  have hbsub : Set.Icc (0 : Real) b ⊆ Set.Icc (-ε) ε := by
    intro t ht
    constructor
    · linarith [hε, ht.1]
    · exact le_trans ht.2 hb.2
  exact
    varBaseFlow_hasFDerivAt_of_flow (I := I) g x Ψ z
      hb.1 hbsub hflow hbound hsrc_ball hLip hzopen

end Coordinates
end RicciFlower
