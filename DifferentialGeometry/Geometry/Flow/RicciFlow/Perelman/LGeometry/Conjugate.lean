import DifferentialGeometry.Geometry.Coordinates.LocalDiffeoIFT
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobi

set_option autoImplicit false

/-!
# L-conjugate points

This file defines L-conjugacy through singularity of the initial-tangent
differential of Perelman's L-exponential map.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem written_fderiv_inv
    {f : E → M} {u : E}
    (hf : MDifferentiableAt 𝓘(Real, E) I f u)
    (hinv : (mfderiv 𝓘(Real, E) I f u).IsInvertible) :
    (fderiv Real
      (writtenInExtChartAt 𝓘(Real, E) I u f)
      (extChartAt 𝓘(Real, E) u u)).IsInvertible := by
  have hf' : HasMFDerivAt 𝓘(Real, E) I f u
      (mfderiv 𝓘(Real, E) I f u) :=
    hf.hasMFDerivAt
  have hchart : HasMFDerivAt I 𝓘(Real, E) (extChartAt I (f u)) (f u)
      (ContinuousLinearMap.id Real E) := by
    have h :=
      (mdifferentiableAt_extChartAt (I := I)
        (mem_chart_source H (f u))).hasMFDerivAt
    rw [mfderiv_extChartAt_self (I := I) (x := f u)] at h
    exact h
  have hcomp : HasMFDerivAt 𝓘(Real, E) 𝓘(Real, E)
      ((extChartAt I (f u)) ∘ f) u
      ((ContinuousLinearMap.id Real E).comp
        (mfderiv 𝓘(Real, E) I f u)) :=
    hchart.comp u hf'
  rw [ContinuousLinearMap.id_comp] at hcomp
  have hwritten : HasFDerivAt
      (writtenInExtChartAt 𝓘(Real, E) I u f)
      (mfderiv 𝓘(Real, E) I f u)
      (extChartAt 𝓘(Real, E) u u) := by
    simpa only [writtenInExtChartAt, extChartAt_self_eq,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id_eq] using hasMFDerivAt_iff_hasFDerivAt.mp hcomp
  rw [hwritten.fderiv]
  exact hinv

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
/-- A positive backward time is L-conjugate along an initial tangent when the
initial-tangent differential of the L-exponential map is not injective. -/
def IsLConj
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) : Prop :=
  (Z, tau) ∈ lExpPosDom S T x ∧
    ¬ Function.Injective fun V : E =>
      mfderiv 𝓘(Real, E) I (fun W : E => lExp S T x W tau) Z V

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
/-- L-conjugacy is equivalent to a nonzero vector in the kernel of the
initial-tangent differential of the L-exponential map. -/
theorem isLConj_iff
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) :
    IsLConj S T x Z tau ↔
      (Z, tau) ∈ lExpPosDom S T x ∧
        ∃ V : E, V ≠ 0 ∧
          mfderiv 𝓘(Real, E) I
            (fun W : E => lExp S T x W tau) Z V = 0 := by
  unfold IsLConj
  set f := mfderiv 𝓘(Real, E) I
    (fun W : E => lExp S T x W tau) Z
  refine and_congr_right fun _ => ?_
  have hker : Function.Injective (fun V : E => f V) ↔
      ∀ V : E, f V = 0 → V = 0 := by
    constructor
    · intro hinj V hV
      exact hinj (hV.trans (map_zero f).symm)
    · intro hzero V W hVW
      apply sub_eq_zero.mp
      apply hzero
      change f V = f W at hVW
      calc
        f (V - W) = f V - f W := map_sub f V W
        _ = 0 := sub_eq_zero.mpr hVW
  rw [hker]
  push Not
  constructor
  · rintro ⟨V, hVzero, hVne⟩
    exact ⟨V, hVne, hVzero⟩
  · rintro ⟨V, hVne, hVzero⟩
    exact ⟨V, hVzero, hVne⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
/-- L-conjugacy is equivalent to a nonzero initial-tangent Jacobi field that
vanishes at the specified square-root time. -/
theorem isLConj_iff_jac
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) :
    IsLConj S T x Z tau ↔
      (Z, tau) ∈ lExpPosDom S T x ∧
        ∃ V : E, V ≠ 0 ∧
          lRegJacobiField S T x Z V (Real.sqrt tau) = 0 := by
  rw [isLConj_iff]
  refine and_congr_right fun _ => ?_
  refine exists_congr fun V => and_congr_right fun _ => ?_
  rw [← lExpJacobi_eq]
  rfl

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
/-- At a positive-domain point that is not L-conjugate, the initial-tangent
differential of the L-exponential map is injective. -/
theorem lExpDeriv_inj
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    Function.Injective fun V : E =>
      mfderiv 𝓘(Real, E) I (fun W : E => lExp S T x W tau) Z V := by
  by_contra hinj
  exact hconj ⟨hdom, hinj⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
/-- In finite dimension, the nonconjugate initial-tangent differential of the
L-exponential map is surjective. -/
theorem lExpDeriv_surj
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    Function.Surjective fun V : E =>
      mfderiv 𝓘(Real, E) I (fun W : E => lExp S T x W tau) Z V := by
  exact LinearMap.surjective_of_injective
    (lExpDeriv_inj S T x Z tau hdom hconj)

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
/-- At a positive-domain point that is not L-conjugate, the fixed-time
L-exponential map is a smooth local diffeomorphism in its initial tangent. -/
theorem lExp_localDiffeo
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    IsLocalDiffeomorphAt 𝓘(Real, E) I ∞
      (fun W : E => lExp S T x W tau) Z := by
  let f : E → M := fun W => lExp S T x W tau
  let U : Set E := (fun W : E => (W, tau)) ⁻¹' lExpPosDom S T x
  have hpair : ContMDiff 𝓘(Real, E)
      (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
      (fun W : E => (W, tau)) :=
    contMDiff_id.prodMk contMDiff_const
  have hUopen : IsOpen U :=
    (lExpPosDom_open S hS T x).preimage hpair.continuous
  have hZU : Z ∈ U := hdom
  have hfU : ContMDiffOn 𝓘(Real, E) I ∞ f U := by
    apply (lExp_smoothOn S hS T x).comp hpair.contMDiffOn
    intro W hW
    exact hW
  have hfinj : Function.Injective (mfderiv 𝓘(Real, E) I f Z) := by
    simpa only [f] using lExpDeriv_inj S T x Z tau hdom hconj
  have hfsurj : Function.Surjective (mfderiv 𝓘(Real, E) I f Z) := by
    simpa only [f] using lExpDeriv_surj S T x Z tau hdom hconj
  let Df : E ≃L[Real] E :=
    ContinuousLinearEquiv.ofBijective (mfderiv 𝓘(Real, E) I f Z)
      (LinearMap.ker_eq_bot.mpr hfinj)
      (LinearMap.range_eq_top.mpr hfsurj)
  have hDinv : (mfderiv 𝓘(Real, E) I f Z).IsInvertible := by
    refine ⟨Df, ?_⟩
    rfl
  have hfZ : MDifferentiableAt 𝓘(Real, E) I f Z :=
    (hfU.contMDiffAt (hUopen.mem_nhds hZU)).mdifferentiableAt
      (by simp)
  have hfdinv := written_fderiv_inv (I := I) hfZ hDinv
  obtain ⟨Psi, hZPsi, hPsiU, hEqPsi⟩ :=
    DifferentialGeometry.Coordinates.isLocalDiffeomorphAt_of_contMDiffOn'
      (I := 𝓘(Real, E)) (J := I) (n := 1) le_rfl
      (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤))
      hUopen hZU (hfU.of_le (by exact_mod_cast le_top)) hfdinv
  have hfPsi : ContMDiffOn 𝓘(Real, E) I ∞ f Psi.source :=
    hfU.mono hPsiU
  have hinvPsi : ∀ W ∈ Psi.source,
      (fderiv Real
        (writtenInExtChartAt 𝓘(Real, E) I W f)
        (extChartAt 𝓘(Real, E) W W)).IsInvertible := by
    intro W hW
    have hloc : IsLocalDiffeomorphAt 𝓘(Real, E) I 1 f W :=
      ⟨Psi, hW, hEqPsi⟩
    have hmfdinv : (mfderiv 𝓘(Real, E) I f W).IsInvertible :=
      ⟨hloc.mfderivToContinuousLinearEquiv one_ne_zero,
        hloc.mfderivToContinuousLinearEquiv_coe one_ne_zero⟩
    have hfW : MDifferentiableAt 𝓘(Real, E) I f W :=
      (hfPsi.contMDiffAt (Psi.open_source.mem_nhds hW)).mdifferentiableAt
        (by simp)
    exact written_fderiv_inv (I := I) hfW hmfdinv
  obtain ⟨Phi, hZPhi, _hPhiPsi, hEqPhi⟩ :=
    DifferentialGeometry.Coordinates.hlocAt_infty'
      (I := 𝓘(Real, E)) (J := I) Psi.open_source hZPsi hfPsi hinvPsi
  exact ⟨Phi, hZPhi, hEqPhi⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
