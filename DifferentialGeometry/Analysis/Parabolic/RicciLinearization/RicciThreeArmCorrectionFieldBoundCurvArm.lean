import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Geometry.Curvature.RealizedFamCurvatureJetBound
import DifferentialGeometry.Geometry.Curvature.PerturbedRiemannOpDifferenceBound
import DifferentialGeometry.Geometry.Curvature.CovDerivConnDiffQuadraticBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseMetricPerturbationFibreBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Sobolev.Embedding.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private noncomputable def fiveSlotCometricCoeff (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) : ℝ :=
  g₀.inner x
    (inverseMetricSharpFib (I := I) g₁ x
      (g0FlatCLM (I := I) g₀ x (smoothOrthoFrame (I := I) g₀ x a x)))
    (smoothOrthoFrame (I := I) g₀ x b x)

private noncomputable def fiveSlotEvalCLM (x : M) (u : Fin 3 → E) :
    Tensor0SSpace 3 I x →L[ℝ] ℝ :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => E) ℝ u).comp
    (Tensor0SSpace.toModelL 3 x)

private lemma fiveSlotEvalCLM_apply (x : M) (u : Fin 3 → E) (D : Tensor0SSpace 3 I x) :
    fiveSlotEvalCLM (I := I) x u D = Tensor0SSpace.toModel D u := rfl

private noncomputable def fiveSlotKernelBilin (g₀ : SmoothRiemannianMetric I M) (x : M)
    (c d : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  ((g₀.inner x).flip (smoothOrthoFrame (I := I) g₀ x c x)).smulRight
    ((g₀.inner x).flip (smoothOrthoFrame (I := I) g₀ x d x))

private lemma fiveSlotKernelBilin_apply (g₀ : SmoothRiemannianMetric I M) (x : M)
    (c d : Fin (Module.finrank ℝ E)) (v0 v1 : TangentSpace I x) :
    fiveSlotKernelBilin (I := I) g₀ x c d v0 v1 =
      g₀.inner x v0 (smoothOrthoFrame (I := I) g₀ x c x) *
        g₀.inner x v1 (smoothOrthoFrame (I := I) g₀ x d x) := by
  rw [fiveSlotKernelBilin, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]

private noncomputable def fiveSlotTriple (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) (call : Fin 4) (contrib : Fin 5) : Fin 3 → E :=
  let va := smoothOrthoFrame (I := I) g₀ x a x
  let vb := smoothOrthoFrame (I := I) g₀ x b x
  let vc := smoothOrthoFrame (I := I) g₀ x c x
  let vd := smoothOrthoFrame (I := I) g₀ x d x
  let args : Fin 4 →
      TangentSpace I x × TangentSpace I x × TangentSpace I x × TangentSpace I x :=
    ![(va, vc, vb, vd), (va, vd, vb, vc), (va, vb, vc, vd), (vc, vd, va, vb)]
  let α := (args call).1
  let β := (args call).2.1
  let γ := (args call).2.2.1
  let δ := (args call).2.2.2
  let cd : TangentSpace I x → TangentSpace I x → TangentSpace I x :=
    fun p q => PDE.DeTurck.connDiff (I := I) g₁ g₀ x p q
  (![ ![(α : E), (cd β γ : E), (δ : E)],
      ![(α : E), (γ : E), (cd β δ : E)],
      ![(cd α β : E), (γ : E), (δ : E)],
      ![(β : E), (cd α γ : E), (δ : E)],
      ![(β : E), (γ : E), (cd α δ : E)] ] : Fin 5 → Fin 3 → E) contrib

private def fiveSlotSign (call : Fin 4) : ℝ := if (call : ℕ) < 2 then 1 else -1

private noncomputable def fiveSlotAtom (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) (call : Fin 4) (contrib : Fin 5) :
    Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (((-(1 : ℝ) / 2) * fiveSlotCometricCoeff (I := I) g₀ g₁ x a b * fiveSlotSign call) •
      fiveSlotEvalCLM (I := I) x
        (fiveSlotTriple (I := I) g₀ g₁ x a b c d call contrib)).smulRight
    (Tensor0SSpace.ofModel (I := I) (x := x)
      (bilinFormToModel E (fiveSlotKernelBilin (I := I) g₀ x c d)))

set_option linter.unusedVariables false in
def arm1FiveSlotFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ i : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) × Fin 4 × Fin 5,
    fiveSlotAtom (I := I) g₀ g₁ x i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2

private lemma fiveSlotAtom_component (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) (call : Fin 4) (contrib : Fin 5)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 3 → Fin n) (J : Fin 2 → Fin n) :
    Tensor0SSpace.toModel
        (fiveSlotAtom (I := I) g₀ g₁ x a b c d call contrib
          (coframeS (I := I) (M := M) g₀ x 3 e K))
        (fun j => e (J j)) =
      ((-(1 : ℝ) / 2) * fiveSlotCometricCoeff (I := I) g₀ g₁ x a b * fiveSlotSign call) *
          Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 3 e K)
            (fiveSlotTriple (I := I) g₀ g₁ x a b c d call contrib) *
        fiveSlotKernelBilin (I := I) g₀ x c d (e (J 0)) (e (J 1)) := by
  simp only [fiveSlotAtom, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    fiveSlotEvalCLM_apply, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul, Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply]
  rfl

private noncomputable def fiveSlotCometricCoeffVec (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (va vb : TangentSpace I x) : ℝ :=
  g₀.inner x
    (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x va)) vb

private noncomputable def fiveSlotKernelBilinVec (g₀ : SmoothRiemannianMetric I M) (x : M)
    (vc vd : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  ((g₀.inner x).flip vc).smulRight ((g₀.inner x).flip vd)

private lemma fiveSlotKernelBilinVec_apply (g₀ : SmoothRiemannianMetric I M) (x : M)
    (vc vd : TangentSpace I x) (v0 v1 : TangentSpace I x) :
    fiveSlotKernelBilinVec (I := I) g₀ x vc vd v0 v1 =
      g₀.inner x v0 vc * g₀.inner x v1 vd := by
  rw [fiveSlotKernelBilinVec, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]

set_option linter.unusedVariables false in
private noncomputable def fiveSlotTripleVec (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (va vb vc vd : TangentSpace I x) (call : Fin 4) (contrib : Fin 5) : Fin 3 → E :=
  let args : Fin 4 →
      TangentSpace I x × TangentSpace I x × TangentSpace I x × TangentSpace I x :=
    ![(va, vc, vb, vd), (va, vd, vb, vc), (va, vb, vc, vd), (vc, vd, va, vb)]
  let α := (args call).1
  let β := (args call).2.1
  let γ := (args call).2.2.1
  let δ := (args call).2.2.2
  let cd : TangentSpace I x → TangentSpace I x → TangentSpace I x :=
    fun p q => PDE.DeTurck.connDiff (I := I) g₁ g₀ x p q
  (![ ![(α : E), (cd β γ : E), (δ : E)],
      ![(α : E), (γ : E), (cd β δ : E)],
      ![(cd α β : E), (γ : E), (δ : E)],
      ![(β : E), (cd α γ : E), (δ : E)],
      ![(β : E), (γ : E), (cd α δ : E)] ] : Fin 5 → Fin 3 → E) contrib

private noncomputable def fiveSlotAtomVec (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (va vb vc vd : TangentSpace I x) (call : Fin 4) (contrib : Fin 5) :
    Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (((-(1 : ℝ) / 2) * fiveSlotCometricCoeffVec (I := I) g₀ g₁ x va vb * fiveSlotSign call) •
      fiveSlotEvalCLM (I := I) x
        (fiveSlotTripleVec (I := I) g₀ g₁ x va vb vc vd call contrib)).smulRight
    (Tensor0SSpace.ofModel (I := I) (x := x)
      (bilinFormToModel E (fiveSlotKernelBilinVec (I := I) g₀ x vc vd)))

private lemma fiveSlotAtomVec_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (va vb vc vd : TangentSpace I x) (call : Fin 4) (contrib : Fin 5)
    (D : Tensor0SSpace 3 I x) :
    fiveSlotAtomVec (I := I) g₀ g₁ x va vb vc vd call contrib D =
      (((-(1 : ℝ) / 2) * fiveSlotCometricCoeffVec (I := I) g₀ g₁ x va vb * fiveSlotSign call) *
          Tensor0SSpace.toModel D
            (fiveSlotTripleVec (I := I) g₀ g₁ x va vb vc vd call contrib)) •
        Tensor0SSpace.ofModel (I := I) (x := x)
          (bilinFormToModel E (fiveSlotKernelBilinVec (I := I) g₀ x vc vd)) := by
  rw [fiveSlotAtomVec, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    fiveSlotEvalCLM_apply, smul_eq_mul]

private lemma fiveSlotAtomVec_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (va vb vc vd : TangentSpace I x) (call : Fin 4) (contrib : Fin 5)
    (D : Tensor0SSpace 3 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (fiveSlotAtomVec (I := I) g₀ g₁ x va vb vc vd call contrib D) v =
      ((-(1 : ℝ) / 2) * fiveSlotCometricCoeffVec (I := I) g₀ g₁ x va vb * fiveSlotSign call) *
          Tensor0SSpace.toModel D
            (fiveSlotTripleVec (I := I) g₀ g₁ x va vb vc vd call contrib) *
        fiveSlotKernelBilinVec (I := I) g₀ x vc vd (v 0) (v 1) := by
  simp only [fiveSlotAtomVec, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    fiveSlotEvalCLM_apply, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul, Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply]
  rfl

private noncomputable def arm1FiveSlotFibVec (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ i : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) × Fin 4 × Fin 5,
    fiveSlotAtomVec (I := I) g₀ g₁ x (F i.1) (F i.2.1) (F i.2.2.1) (F i.2.2.2.1)
      i.2.2.2.2.1 i.2.2.2.2.2

private lemma arm1FiveSlotFib_eq_fibVec_diag (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    arm1FiveSlotFib (I := I) g₀ g₁ x =
      arm1FiveSlotFibVec (I := I) g₀ g₁ x
        (fun a => smoothOrthoFrame (I := I) g₀ x a x) := rfl

private lemma arm1FiveSlotFibVec_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (D : Tensor0SSpace 3 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (arm1FiveSlotFibVec (I := I) g₀ g₁ x F D) v =
      ∑ i : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
            Fin (Module.finrank ℝ E) × Fin 4 × Fin 5,
        ((-(1 : ℝ) / 2) * fiveSlotCometricCoeffVec (I := I) g₀ g₁ x (F i.1) (F i.2.1) *
              fiveSlotSign i.2.2.2.2.1) *
            Tensor0SSpace.toModel D
              (fiveSlotTripleVec (I := I) g₀ g₁ x (F i.1) (F i.2.1) (F i.2.2.1) (F i.2.2.2.1)
                i.2.2.2.2.1 i.2.2.2.2.2) *
          fiveSlotKernelBilinVec (I := I) g₀ x (F i.2.2.1) (F i.2.2.2.1) (v 0) (v 1) := by
  classical
  rw [arm1FiveSlotFibVec, ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Tensor0SSpace.toModelL_apply]
  exact fiveSlotAtomVec_toModel (I := I) g₀ g₁ x (F i.1) (F i.2.1) (F i.2.2.1) (F i.2.2.2.1)
    i.2.2.2.2.1 i.2.2.2.2.2 D v

private lemma frame_basis_of_orthonormal (g₀ : SmoothRiemannianMetric I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hF : ∀ a b, g₀.inner x (F a) (F b) = if a = b then (1 : ℝ) else 0) :
    ∃ bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ i, bse i = F i := by
  classical
  have he_li : LinearIndependent ℝ F := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g₀.inner x (F k) (∑ j ∈ fs, c j • F j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g₀.inner x (F k) (c j • F j) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g₀.inner x (F k)).map_smul (c j), smul_eq_mul, hF k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E :=
    Fintype.card_fin _
  exact ⟨basisOfLinearIndependentOfCardEqFinrank he_li hcard,
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i⟩

private lemma ortho_expand (g₀ : SmoothRiemannianMetric I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hF : ∀ a b, g₀.inner x (F a) (F b) = if a = b then (1 : ℝ) else 0)
    (u : TangentSpace I x) :
    u = ∑ i : Fin (Module.finrank ℝ E), g₀.inner x u (F i) • F i := by
  classical
  obtain ⟨bse, hbse⟩ := frame_basis_of_orthonormal (I := I) g₀ x F hF
  have hcoeff : ∀ j : Fin (Module.finrank ℝ E),
      g₀.inner x u (F j) = bse.repr u j := by
    intro j
    rw [g₀.symm x u (F j)]
    conv_lhs => rw [← bse.sum_repr u]
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [(g₀.inner x (F j)).map_smul (bse.repr u i), smul_eq_mul, hbse i, hF j i])]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [if_pos rfl, mul_one]
    · intro i _ hij; rw [if_neg (fun h => hij h.symm), mul_zero]
  calc u = ∑ i : Fin (Module.finrank ℝ E), bse.repr u i • bse i := (bse.sum_repr u).symm
    _ = ∑ i : Fin (Module.finrank ℝ E), g₀.inner x u (F i) • F i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcoeff i, hbse i]

set_option linter.unusedVariables false in
private lemma tripleVec_entry_section_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π z : M, TangentSpace I z)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (a b c d : Fin (Module.finrank ℝ E)) (call : Fin 4) (contrib : Fin 5) (i : Fin 3) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (fiveSlotTripleVec (E := E) (I := I) g₀ g₁ x (B a x) (B b x) (B c x) (B d x)
          call contrib i)) := by
  fin_cases call <;> fin_cases contrib <;> fin_cases i <;>
    simp only [fiveSlotTripleVec, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta,
      Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.head_fin_const] <;>
    first
      | exact hB a
      | exact hB b
      | exact hB c
      | exact hB d
      | (refine PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ ?_ ?_ <;>
          first | exact hB a | exact hB b | exact hB c | exact hB d)

private lemma fiveSlotKernelBilinVec_homSection_contMDiff (g₀ : SmoothRiemannianMetric I M)
    {pc pd : Π z : M, TangentSpace I z}
    (hpc : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% pc))
    (hpd : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% pd)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (fiveSlotKernelBilinVec (I := I) g₀ x (pc x) (pd x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => fiveSlotKernelBilinVec (I := I) g₀ x (pc x) (pd x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => fiveSlotKernelBilinVec (I := I) g₀ x (pc x) (pd x) (V0 x))
  intro W
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => fiveSlotKernelBilinVec (I := I) g₀ x (pc x) (pd x) (V0 x) (W x)) := by
    have hprod : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => g₀.inner x (V0 x) (pc x) * g₀.inner x (W x) (pd x)) :=
      (contMDiff_g_inner_of_smooth_sections (I := I) g₀
        ⟨fun x => V0 x, V0.contMDiff⟩ ⟨fun x => pc x, hpc⟩).mul
      (contMDiff_g_inner_of_smooth_sections (I := I) g₀
        ⟨fun x => W x, W.contMDiff⟩ ⟨fun x => pd x, hpd⟩)
    refine hprod.congr (fun x => ?_)
    rw [fiveSlotKernelBilinVec_apply]
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change fiveSlotKernelBilinVec (I := I) g₀ y (pc y) (pd y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rfl

set_option linter.unusedVariables false in
private lemma fiveSlotAtomVec_section_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π z : M, TangentSpace I z)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (a b c d : Fin (Module.finrank ℝ E)) (call : Fin 4) (contrib : Fin 5)
    (Y : Cₛ^∞⟮I; Tensor0SModel 3 ℝ E, fun z : M => Tensor0SSpace 3 I z⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (fiveSlotAtomVec (I := I) g₀ g₁ x (B a x) (B b x) (B c x) (B d x) call contrib (Y x))) := by
  classical
  have hflat_a := ContMDiff.clm_bundle_apply (b := id) (g0FlatField_contMDiff (I := I) g₀) (hB a)
  have hsharp_a := ContMDiff.clm_bundle_apply (b := id)
    (inverseMetricSharpField_contMDiff (I := I) g₁) hflat_a
  have hcometric : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => fiveSlotCometricCoeffVec (I := I) g₀ g₁ x (B a x) (B b x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₀
      ⟨fun x => inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (B a x)), hsharp_a⟩
      ⟨fun x => B b x, hB b⟩
  have htriple : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => Tensor0SSpace.toModel (Y x)
        (fiveSlotTripleVec (I := I) g₀ g₁ x (B a x) (B b x) (B c x) (B d x) call contrib)) :=
    TensorMultilinear.contMDiff_section_apply (n := 3) (fun z => Y z) Y.contMDiff
      (fun i x => (fiveSlotTripleVec (E := E) (I := I) g₀ g₁ x (B a x) (B b x) (B c x) (B d x)
        call contrib i : TangentSpace I x))
      (fun i => tripleVec_entry_section_contMDiff (I := I) g₀ g₁ B hB a b c d call contrib i)
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => (-(1 : ℝ) / 2) * fiveSlotCometricCoeffVec (I := I) g₀ g₁ x (B a x) (B b x) *
          fiveSlotSign call *
        Tensor0SSpace.toModel (Y x)
          (fiveSlotTripleVec (I := I) g₀ g₁ x (B a x) (B b x) (B c x) (B d x) call contrib)) :=
    (((contMDiff_const.mul hcometric).mul contMDiff_const).mul htriple)
  have hbilin : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (Tensor0SSpace.ofModel (I := I) (x := x)
          (bilinFormToModel E (fiveSlotKernelBilinVec (I := I) g₀ x (B c x) (B d x))))) :=
    contMDiff_bilinSection_of_homSection (I := I)
      (fun x => fiveSlotKernelBilinVec (I := I) g₀ x (B c x) (B d x))
      (fiveSlotKernelBilinVec_homSection_contMDiff (I := I) g₀ (hB c) (hB d))
  have hsmul := ContMDiff.smul_section
    (f := fun x : M => (-(1 : ℝ) / 2) * fiveSlotCometricCoeffVec (I := I) g₀ g₁ x (B a x) (B b x) *
        fiveSlotSign call *
      Tensor0SSpace.toModel (Y x)
        (fiveSlotTripleVec (I := I) g₀ g₁ x (B a x) (B b x) (B c x) (B d x) call contrib))
    (s := fun x : M => Tensor0SSpace.ofModel (I := I) (x := x)
      (bilinFormToModel E (fiveSlotKernelBilinVec (I := I) g₀ x (B c x) (B d x))))
    hscalar hbilin
  refine hsmul.congr (fun x => ?_)
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [fiveSlotAtomVec_apply]
  rfl

private theorem arm1FiveSlotFibVec_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π z : M, TangentSpace I z)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) x
        (arm1FiveSlotFibVec (I := I) g₀ g₁ x (fun a => B a x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun x => arm1FiveSlotFibVec (I := I) g₀ g₁ x (fun a => B a x))
  intro Y
  set S : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) × Fin 4 × Fin 5 →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun i =>
      { toFun := fun x : M =>
          fiveSlotAtomVec (I := I) g₀ g₁ x (B i.1 x) (B i.2.1 x) (B i.2.2.1 x) (B i.2.2.2.1 x)
            i.2.2.2.2.1 i.2.2.2.2.2 (Y x)
        contMDiff_toFun := fiveSlotAtomVec_section_contMDiff (I := I) g₀ g₁ B hB
          i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2 Y } with hS
  have hStot := (∑ i, S i).contMDiff
  refine hStot.congr (fun x => ?_)
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [ContMDiffSection.finset_sum_apply, arm1FiveSlotFibVec, ContinuousLinearMap.sum_apply]
  rfl

private lemma toModel3_smul_matrix0 (x : M) (D : Tensor0SSpace 3 I x) (c : ℝ) (u q r : E) :
    Tensor0SSpace.toModel D ![c • u, q, r] = c * Tensor0SSpace.toModel D ![u, q, r] := by
  have h1 : (![c • u, q, r] : Fin 3 → E) = Function.update ![u, q, r] 0 (c • u) := by
    funext j; fin_cases j <;> simp
  have h2 : Function.update (![u, q, r] : Fin 3 → E) 0 u = ![u, q, r] := by
    funext j; fin_cases j <;> simp
  rw [h1, (Tensor0SSpace.toModel D).map_update_smul ![u, q, r] 0 c u, h2, smul_eq_mul]

private lemma toModel3_smul_matrix1 (x : M) (D : Tensor0SSpace 3 I x) (c : ℝ) (p u r : E) :
    Tensor0SSpace.toModel D ![p, c • u, r] = c * Tensor0SSpace.toModel D ![p, u, r] := by
  have h1 : (![p, c • u, r] : Fin 3 → E) = Function.update ![p, u, r] 1 (c • u) := by
    funext j; fin_cases j <;> simp
  have h2 : Function.update (![p, u, r] : Fin 3 → E) 1 u = ![p, u, r] := by
    funext j; fin_cases j <;> simp
  rw [h1, (Tensor0SSpace.toModel D).map_update_smul ![p, u, r] 1 c u, h2, smul_eq_mul]

private lemma toModel3_smul_matrix2 (x : M) (D : Tensor0SSpace 3 I x) (c : ℝ) (p q u : E) :
    Tensor0SSpace.toModel D ![p, q, c • u] = c * Tensor0SSpace.toModel D ![p, q, u] := by
  have h1 : (![p, q, c • u] : Fin 3 → E) = Function.update ![p, q, u] 2 (c • u) := by
    funext j; fin_cases j <;> simp
  have h2 : Function.update (![p, q, u] : Fin 3 → E) 2 u = ![p, q, u] := by
    funext j; fin_cases j <;> simp
  rw [h1, (Tensor0SSpace.toModel D).map_update_smul ![p, q, u] 2 c u, h2, smul_eq_mul]

private lemma toModel3_add_matrix0 (x : M) (D : Tensor0SSpace 3 I x) (u u' q r : E) :
    Tensor0SSpace.toModel D ![u + u', q, r] =
      Tensor0SSpace.toModel D ![u, q, r] + Tensor0SSpace.toModel D ![u', q, r] := by
  have h1 : (![u + u', q, r] : Fin 3 → E) = Function.update ![u, q, r] 0 (u + u') := by
    funext j; fin_cases j <;> simp
  have h2 : Function.update (![u, q, r] : Fin 3 → E) 0 u = ![u, q, r] := by
    funext j; fin_cases j <;> simp
  have h3 : Function.update (![u, q, r] : Fin 3 → E) 0 u' = ![u', q, r] := by
    funext j; fin_cases j <;> simp
  rw [h1, (Tensor0SSpace.toModel D).map_update_add ![u, q, r] 0 u u', h2, h3]

private lemma toModel3_add_matrix1 (x : M) (D : Tensor0SSpace 3 I x) (p u u' r : E) :
    Tensor0SSpace.toModel D ![p, u + u', r] =
      Tensor0SSpace.toModel D ![p, u, r] + Tensor0SSpace.toModel D ![p, u', r] := by
  have h1 : (![p, u + u', r] : Fin 3 → E) = Function.update ![p, u, r] 1 (u + u') := by
    funext j; fin_cases j <;> simp
  have h2 : Function.update (![p, u, r] : Fin 3 → E) 1 u = ![p, u, r] := by
    funext j; fin_cases j <;> simp
  have h3 : Function.update (![p, u, r] : Fin 3 → E) 1 u' = ![p, u', r] := by
    funext j; fin_cases j <;> simp
  rw [h1, (Tensor0SSpace.toModel D).map_update_add ![p, u, r] 1 u u', h2, h3]

private lemma toModel3_add_matrix2 (x : M) (D : Tensor0SSpace 3 I x) (p q u u' : E) :
    Tensor0SSpace.toModel D ![p, q, u + u'] =
      Tensor0SSpace.toModel D ![p, q, u] + Tensor0SSpace.toModel D ![p, q, u'] := by
  have h1 : (![p, q, u + u'] : Fin 3 → E) = Function.update ![p, q, u] 2 (u + u') := by
    funext j; fin_cases j <;> simp
  have h2 : Function.update (![p, q, u] : Fin 3 → E) 2 u = ![p, q, u] := by
    funext j; fin_cases j <;> simp
  have h3 : Function.update (![p, q, u] : Fin 3 → E) 2 u' = ![p, q, u'] := by
    funext j; fin_cases j <;> simp
  rw [h1, (Tensor0SSpace.toModel D).map_update_add ![p, q, u] 2 u u', h2, h3]

private lemma toModel3_finsetSum_matrix0 (x : M) (D : Tensor0SSpace 3 I x) {ι : Type*}
    (s : Finset ι) (cf : ι → ℝ) (G : ι → E) (q r : E) :
    Tensor0SSpace.toModel D ![∑ j ∈ s, cf j • G j, q, r] =
      ∑ j ∈ s, cf j * Tensor0SSpace.toModel D ![G j, q, r] := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact (Tensor0SSpace.toModel D).map_coord_zero 0 (by simp)
  | cons k s hk ih =>
    rw [Finset.sum_cons, Finset.sum_cons, toModel3_add_matrix0, toModel3_smul_matrix0, ih]

private lemma toModel3_finsetSum_matrix1 (x : M) (D : Tensor0SSpace 3 I x) {ι : Type*}
    (s : Finset ι) (cf : ι → ℝ) (G : ι → E) (p r : E) :
    Tensor0SSpace.toModel D ![p, ∑ j ∈ s, cf j • G j, r] =
      ∑ j ∈ s, cf j * Tensor0SSpace.toModel D ![p, G j, r] := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact (Tensor0SSpace.toModel D).map_coord_zero 1 (by simp)
  | cons k s hk ih =>
    rw [Finset.sum_cons, Finset.sum_cons, toModel3_add_matrix1, toModel3_smul_matrix1, ih]

private lemma toModel3_finsetSum_matrix2 (x : M) (D : Tensor0SSpace 3 I x) {ι : Type*}
    (s : Finset ι) (cf : ι → ℝ) (G : ι → E) (p q : E) :
    Tensor0SSpace.toModel D ![p, q, ∑ j ∈ s, cf j • G j] =
      ∑ j ∈ s, cf j * Tensor0SSpace.toModel D ![p, q, G j] := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact (Tensor0SSpace.toModel D).map_coord_zero 2 (by simp)
  | cons k s hk ih =>
    rw [Finset.sum_cons, Finset.sum_cons, toModel3_add_matrix2, toModel3_smul_matrix2, ih]

set_option linter.unusedVariables false in
private lemma tripleVec_add_a (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (va va' vb vc vd : TangentSpace I x) (call : Fin 4) (contrib : Fin 5) :
    Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x (va + va') vb vc vd call contrib) =
      Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va vb vc vd call contrib) +
        Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va' vb vc vd call contrib) := by
  fin_cases call <;> fin_cases contrib <;>
    simp only [fiveSlotTripleVec, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta,
      Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, map_add, ContinuousLinearMap.add_apply,
      toModel3_add_matrix0, toModel3_add_matrix1, toModel3_add_matrix2]

set_option linter.unusedVariables false in
private lemma tripleVec_smul_a (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (c : ℝ) (va vb vc vd : TangentSpace I x) (call : Fin 4)
    (contrib : Fin 5) :
    Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x (c • va) vb vc vd call contrib) =
      c * Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va vb vc vd call contrib) := by
  fin_cases call <;> fin_cases contrib <;>
    simp only [fiveSlotTripleVec, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta,
      Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, map_smul, ContinuousLinearMap.smul_apply,
      toModel3_smul_matrix0, toModel3_smul_matrix1, toModel3_smul_matrix2]

set_option linter.unusedVariables false in
private lemma tripleVec_add_b (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (va vb vb' vc vd : TangentSpace I x) (call : Fin 4) (contrib : Fin 5) :
    Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va (vb + vb') vc vd call contrib) =
      Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va vb vc vd call contrib) +
        Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va vb' vc vd call contrib) := by
  fin_cases call <;> fin_cases contrib <;>
    simp only [fiveSlotTripleVec, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta,
      Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, map_add, ContinuousLinearMap.add_apply,
      toModel3_add_matrix0, toModel3_add_matrix1, toModel3_add_matrix2]

set_option linter.unusedVariables false in
private lemma tripleVec_smul_b (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (c : ℝ) (va vb vc vd : TangentSpace I x) (call : Fin 4)
    (contrib : Fin 5) :
    Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va (c • vb) vc vd call contrib) =
      c * Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va vb vc vd call contrib) := by
  fin_cases call <;> fin_cases contrib <;>
    simp only [fiveSlotTripleVec, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta,
      Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, map_smul, ContinuousLinearMap.smul_apply,
      toModel3_smul_matrix0, toModel3_smul_matrix1, toModel3_smul_matrix2]

set_option linter.unusedVariables false in
private lemma tripleVec_finsetSum_c (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (va vb vd : TangentSpace I x) {ι : Type*} (s : Finset ι)
    (cf : ι → ℝ) (G : ι → TangentSpace I x) (call : Fin 4) (contrib : Fin 5) :
    Tensor0SSpace.toModel D
        (fiveSlotTripleVec (I := I) g₀ g₁ x va vb (∑ j ∈ s, cf j • G j) vd call contrib) =
      ∑ j ∈ s, cf j *
        Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va vb (G j) vd call contrib) := by
  fin_cases call <;> fin_cases contrib <;>
    simp only [fiveSlotTripleVec, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta,
      Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, map_sum, ContinuousLinearMap.sum_apply,
      map_smul, ContinuousLinearMap.smul_apply, toModel3_finsetSum_matrix0,
      toModel3_finsetSum_matrix1, toModel3_finsetSum_matrix2]

set_option linter.unusedVariables false in
private lemma tripleVec_finsetSum_d (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (va vb vc : TangentSpace I x) {ι : Type*} (s : Finset ι)
    (cf : ι → ℝ) (G : ι → TangentSpace I x) (call : Fin 4) (contrib : Fin 5) :
    Tensor0SSpace.toModel D
        (fiveSlotTripleVec (I := I) g₀ g₁ x va vb vc (∑ j ∈ s, cf j • G j) call contrib) =
      ∑ j ∈ s, cf j *
        Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va vb vc (G j) call contrib) := by
  fin_cases call <;> fin_cases contrib <;>
    simp only [fiveSlotTripleVec, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta,
      Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, map_sum, ContinuousLinearMap.sum_apply,
      map_smul, ContinuousLinearMap.smul_apply, toModel3_finsetSum_matrix0,
      toModel3_finsetSum_matrix1, toModel3_finsetSum_matrix2]

private lemma collapse_d (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (D : Tensor0SSpace 3 I x)
    (va vb vc w : TangentSpace I x)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hF : ∀ a b, g₀.inner x (F a) (F b) = if a = b then (1 : ℝ) else 0)
    (call : Fin 4) (contrib : Fin 5) :
    ∑ j : Fin (Module.finrank ℝ E), g₀.inner x w (F j) *
        Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va vb vc (F j) call contrib) =
      Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va vb vc w call contrib) := by
  conv_rhs => rw [ortho_expand (I := I) g₀ x F hF w]
  rw [tripleVec_finsetSum_d (I := I) g₀ g₁ x D va vb vc Finset.univ
    (fun j => g₀.inner x w (F j)) F call contrib]

private lemma collapse_c (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (D : Tensor0SSpace 3 I x)
    (va vb vd w : TangentSpace I x)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hF : ∀ a b, g₀.inner x (F a) (F b) = if a = b then (1 : ℝ) else 0)
    (call : Fin 4) (contrib : Fin 5) :
    ∑ j : Fin (Module.finrank ℝ E), g₀.inner x w (F j) *
        Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va vb (F j) vd call contrib) =
      Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va vb w vd call contrib) := by
  conv_rhs => rw [ortho_expand (I := I) g₀ x F hF w]
  rw [tripleVec_finsetSum_c (I := I) g₀ g₁ x D va vb vd Finset.univ
    (fun j => g₀.inner x w (F j)) F call contrib]

private noncomputable def fiveSlotDdCLM (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (v0 v1 : TangentSpace I x) (call : Fin 4) (contrib : Fin 5) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
          (TangentSpace I x →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ)).toLinearMap.comp
      (LinearMap.mk₂ ℝ
        (fun wa wb : TangentSpace I x =>
          Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x wa wb v0 v1 call contrib))
        (fun wa wa' wb => tripleVec_add_a (I := I) g₀ g₁ x D wa wa' wb v0 v1 call contrib)
        (fun c wa wb =>
          (tripleVec_smul_a (I := I) g₀ g₁ x D c wa wb v0 v1 call contrib).trans
            (smul_eq_mul c _).symm)
        (fun wa wb wb' => tripleVec_add_b (I := I) g₀ g₁ x D wa wb wb' v0 v1 call contrib)
        (fun c wa wb =>
          (tripleVec_smul_b (I := I) g₀ g₁ x D c wa wb v0 v1 call contrib).trans
            (smul_eq_mul c _).symm)))

private lemma fiveSlotDdCLM_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (v0 v1 : TangentSpace I x) (call : Fin 4) (contrib : Fin 5)
    (wa wb : TangentSpace I x) :
    fiveSlotDdCLM (I := I) g₀ g₁ x D v0 v1 call contrib wa wb =
      Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x wa wb v0 v1 call contrib) := by
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  simp only [fiveSlotDdCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.mk₂_apply]

private lemma collapse_cd (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (D : Tensor0SSpace 3 I x)
    (va vb v0 v1 : TangentSpace I x) (F : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hF : ∀ a b, g₀.inner x (F a) (F b) = if a = b then (1 : ℝ) else 0)
    (call : Fin 4) (contrib : Fin 5) :
    ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va vb (F c) (F d) call contrib) *
          fiveSlotKernelBilinVec (I := I) g₀ x (F c) (F d) v0 v1 =
      Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va vb v0 v1 call contrib) := by
  have inner_d : ∀ c : Fin (Module.finrank ℝ E),
      ∑ d : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel D
              (fiveSlotTripleVec (I := I) g₀ g₁ x va vb (F c) (F d) call contrib) *
            fiveSlotKernelBilinVec (I := I) g₀ x (F c) (F d) v0 v1 =
        g₀.inner x v0 (F c) *
          Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x va vb (F c) v1 call contrib) := by
    intro c
    have hreorder : ∀ d : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            (fiveSlotTripleVec (I := I) g₀ g₁ x va vb (F c) (F d) call contrib) *
          fiveSlotKernelBilinVec (I := I) g₀ x (F c) (F d) v0 v1 =
          g₀.inner x v0 (F c) *
            (g₀.inner x v1 (F d) *
              Tensor0SSpace.toModel D
                (fiveSlotTripleVec (I := I) g₀ g₁ x va vb (F c) (F d) call contrib)) := by
      intro d; rw [fiveSlotKernelBilinVec_apply]; ring
    rw [Finset.sum_congr rfl (fun d _ => hreorder d), ← Finset.mul_sum,
      collapse_d (I := I) g₀ g₁ x D va vb (F c) v1 F hF call contrib]
  rw [Finset.sum_congr rfl (fun c _ => inner_d c),
    collapse_c (I := I) g₀ g₁ x D va vb v1 v0 F hF call contrib]

set_option linter.unusedVariables false in
private lemma fiveSlot_inner_indep (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 3 I x) (v0 v1 : TangentSpace I x) (call : Fin 4) (contrib : Fin 5)
    (F F' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hF : ∀ a b, g₀.inner x (F a) (F b) = if a = b then (1 : ℝ) else 0)
    (hF' : ∀ a b, g₀.inner x (F' a) (F' b) = if a = b then (1 : ℝ) else 0) :
    (∑ a, ∑ b, ∑ c, ∑ d,
        (-(1 : ℝ) / 2 * fiveSlotCometricCoeffVec (I := I) g₀ g₁ x (F a) (F b) * fiveSlotSign call) *
            Tensor0SSpace.toModel D
              (fiveSlotTripleVec (I := I) g₀ g₁ x (F a) (F b) (F c) (F d) call contrib) *
          fiveSlotKernelBilinVec (I := I) g₀ x (F c) (F d) v0 v1) =
      (∑ a, ∑ b, ∑ c, ∑ d,
        (-(1 : ℝ) / 2 * fiveSlotCometricCoeffVec (I := I) g₀ g₁ x (F' a) (F' b) * fiveSlotSign call) *
            Tensor0SSpace.toModel D
              (fiveSlotTripleVec (I := I) g₀ g₁ x (F' a) (F' b) (F' c) (F' d) call contrib) *
          fiveSlotKernelBilinVec (I := I) g₀ x (F' c) (F' d) v0 v1) := by
  set Dd := fiveSlotDdCLM (I := I) g₀ g₁ x D v0 v1 call contrib with hDd_def
  set Kc : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    (g₀.inner x).comp ((inverseMetricSharpFib (I := I) g₁ x).comp (g0FlatCLM (I := I) g₀ x))
    with hKc_def
  have hK : ∀ wa wb, Kc wa wb = fiveSlotCometricCoeffVec (I := I) g₀ g₁ x wa wb := fun _ _ => rfl
  have hDdv : ∀ wa wb,
      Dd wa wb = Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x wa wb v0 v1 call contrib) :=
    fun wa wb => fiveSlotDdCLM_apply (I := I) g₀ g₁ x D v0 v1 call contrib wa wb
  have reduce : ∀ (G : Fin (Module.finrank ℝ E) → TangentSpace I x),
      (∀ a b, g₀.inner x (G a) (G b) = if a = b then (1 : ℝ) else 0) →
      (∑ a, ∑ b, ∑ c, ∑ d,
        (-(1 : ℝ) / 2 * fiveSlotCometricCoeffVec (I := I) g₀ g₁ x (G a) (G b) * fiveSlotSign call) *
            Tensor0SSpace.toModel D
              (fiveSlotTripleVec (I := I) g₀ g₁ x (G a) (G b) (G c) (G d) call contrib) *
          fiveSlotKernelBilinVec (I := I) g₀ x (G c) (G d) v0 v1) =
        (-(1 : ℝ) / 2 * fiveSlotSign call) * ∑ a, ∑ b, Kc (G a) (G b) * Dd (G a) (G b) := by
    intro G hG
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hAB : (∑ c, ∑ d,
          (-(1 : ℝ) / 2 * fiveSlotCometricCoeffVec (I := I) g₀ g₁ x (G a) (G b) * fiveSlotSign call) *
              Tensor0SSpace.toModel D
                (fiveSlotTripleVec (I := I) g₀ g₁ x (G a) (G b) (G c) (G d) call contrib) *
            fiveSlotKernelBilinVec (I := I) g₀ x (G c) (G d) v0 v1) =
        (-(1 : ℝ) / 2 * fiveSlotCometricCoeffVec (I := I) g₀ g₁ x (G a) (G b) * fiveSlotSign call) *
          Tensor0SSpace.toModel D (fiveSlotTripleVec (I := I) g₀ g₁ x (G a) (G b) v0 v1 call contrib) := by
      rw [← collapse_cd (I := I) g₀ g₁ x D (G a) (G b) v0 v1 G hG call contrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    rw [hAB, hK, hDdv]
    ring
  rw [reduce F hF, reduce F' hF', double_frame_bilin_trace_indep (I := I) g₀ x Kc Dd F F' hF hF']

private lemma tuple_sum_reindex {α : Type*} [AddCommMonoid α]
    (f : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) × Fin 4 × Fin 5 → α) :
    (∑ i, f i) =
      ∑ call : Fin 4, ∑ contrib : Fin 5, ∑ a, ∑ b, ∑ c, ∑ d,
        f (a, b, c, d, call, contrib) := by
  let e : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E) × Fin 4 × Fin 5) ≃
      ((Fin 4 × Fin 5) × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))) :=
    { toFun := fun i => ((i.2.2.2.2.1, i.2.2.2.2.2), (i.1, i.2.1, i.2.2.1, i.2.2.2.1))
      invFun := fun p => (p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2, p.1.1, p.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.sum_equiv e f (fun p => f (e.symm p))
    (fun i => (congrArg f (e.symm_apply_apply i)).symm)]
  simp only [Fintype.sum_prod_type]
  rfl

private lemma arm1FiveSlotFibVec_frame_indep (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (F F' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hF : ∀ a b, g₀.inner x (F a) (F b) = if a = b then (1 : ℝ) else 0)
    (hF' : ∀ a b, g₀.inner x (F' a) (F' b) = if a = b then (1 : ℝ) else 0) :
    arm1FiveSlotFibVec (I := I) g₀ g₁ x F = arm1FiveSlotFibVec (I := I) g₀ g₁ x F' := by
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [arm1FiveSlotFibVec_toModel, arm1FiveSlotFibVec_toModel, tuple_sum_reindex, tuple_sum_reindex]
  refine Finset.sum_congr rfl fun call _ => Finset.sum_congr rfl fun contrib _ => ?_
  exact fiveSlot_inner_indep (I := I) g₀ g₁ x D (v 0) (v 1) call contrib F F' hF hF'

set_option linter.unusedVariables false in
theorem arm1FiveSlotFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) x
        (arm1FiveSlotFib (I := I) g₀ g₁ x)) := by
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) x
        (arm1FiveSlotFibVec (I := I) g₀ g₁ x
          (fun a => smoothOrthoFrame (I := I) g₀ x₀ a x))) x₀ :=
    arm1FiveSlotFibVec_contMDiff (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₀ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₀ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  refine congrArg (TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) y) ?_
  rw [arm1FiveSlotFib_eq_fibVec_diag]
  exact arm1FiveSlotFibVec_frame_indep (I := I) g₀ g₁ y
    (fun a => smoothOrthoFrame (I := I) g₀ y a y)
    (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)
    (fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ y a b)
    (fun a b => smoothOrthoFrame_orthonormal (I := I) g₀ x₀ hy a b)

def arm1FiveSlotCoeff (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 3 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x)
      contMDiff_toFun := arm1FiveSlotFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem arm1FiveSlotCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (arm1FiveSlotCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x) := rfl

def arm1FiveSlotField (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 3 2 :=
  arm1FiveSlotCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)

private lemma fiberNormSqComponent_arm1FiveSlotFib
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x) (K : Fin 3 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 3 2
        (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x)
        n e K J =
      ∑ i : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
            Fin (Module.finrank ℝ E) × Fin 4 × Fin 5,
        ((-(1 : ℝ) / 2) * fiveSlotCometricCoeff (I := I) g₀ g₁ x i.1 i.2.1 *
              fiveSlotSign i.2.2.2.2.1) *
            Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 3 e K)
              (fiveSlotTriple (I := I) g₀ g₁ x i.1 i.2.1 i.2.2.1 i.2.2.2.1
                i.2.2.2.2.1 i.2.2.2.2.2) *
          fiveSlotKernelBilin (I := I) g₀ x i.2.2.1 i.2.2.2.1 (e (J 0)) (e (J 1)) := by
  classical
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 3 2
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x) n e K J =
      Tensor0SSpace.toModel
        ((arm1FiveSlotFib (I := I) g₀ g₁ x) (coframeS (I := I) (M := M) g₀ x 3 e K))
        (fun j => e (J j)) := rfl
  rw [hcomp, arm1FiveSlotFib, ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Tensor0SSpace.toModelL_apply]
  exact fiveSlotAtom_component (I := I) g₀ g₁ x i.1 i.2.1 i.2.2.1 i.2.2.2.1
    i.2.2.2.2.1 i.2.2.2.2.2 e K J

set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem rfns_arm1FiveSlotFib_le_of_lt_one
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (P : SmoothCcTensor g₀ 0 2)
      (h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
      {δ : ℝ} (hδ : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
      (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
      (x : M),
      letI : Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
          (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x) ≤
        C * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
  classical
  have h1δ : (0 : ℝ) < 1 - δ₀ := by linarith
  have hinv_pos : (0 : ℝ) < 1 / (1 - δ₀) := div_pos one_pos h1δ
  obtain ⟨C₀, hC₀0, hpw⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀
  set Mc : ℝ := ((Module.finrank ℝ E : ℝ) ^ 4 * 20) * ((1 / 2) * (1 / (1 - δ₀)) * C₀) with hMc
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 5 * Mc ^ 2,
    mul_nonneg (by positivity) (sq_nonneg _), ?_⟩
  intro g₁ P h δ hδ hδ0 hbound x
  letI instTens : Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum_rfns⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ hδ₀
  have h1δ' : (0 : ℝ) < 1 - δ := by linarith
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  have hframe1 : ∀ z : Fin (Module.finrank ℝ E),
      g₀.inner x (smoothOrthoFrame (I := I) g₀ x z x)
        (smoothOrthoFrame (I := I) g₀ x z x) = 1 := by
    intro z; rw [smoothOrthoFrame_orthonormal_at_center]; simp
  have he1 : ∀ i : Fin n, g₀.inner x (e i) (e i) = 1 := by
    intro i; rw [horth i i]; simp
  have hsign : ∀ call : Fin 4, |fiveSlotSign call| = 1 := by
    intro call; unfold fiveSlotSign; split_ifs <;> norm_num
  have hcometric : ∀ a b : Fin (Module.finrank ℝ E),
      |fiveSlotCometricCoeff (I := I) g₀ g₁ x a b| ≤ 1 / (1 - δ₀) := by
    intro a b
    rw [fiveSlotCometricCoeff]
    have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x
      (inverseMetricSharpFib (I := I) g₁ x
        (g0FlatCLM (I := I) g₀ x (smoothOrthoFrame (I := I) g₀ x a x)))
      (smoothOrthoFrame (I := I) g₀ x b x)
    rw [hframe1 b, Real.sqrt_one, mul_one] at hcs
    have hsharp := sqrt_inner_inverseMetricSharpFib_g0FlatCLM_le (I := I) (M := M) g₀ g₁
      (fun y => ccTensorBilinSymm (I := I) g₀ P y) h hδ_lt hδ0 hbound x
      (smoothOrthoFrame (I := I) g₀ x a x)
    rw [hframe1 a, Real.sqrt_one, mul_one] at hsharp
    refine le_trans hcs (le_trans hsharp ?_)
    exact one_div_le_one_div_of_le h1δ (by linarith)
  have hsqrt_cd : ∀ z w : Fin (Module.finrank ℝ E),
      Real.sqrt (g₀.inner x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (smoothOrthoFrame (I := I) g₀ x z x)
          (smoothOrthoFrame (I := I) g₀ x w x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (smoothOrthoFrame (I := I) g₀ x z x)
          (smoothOrthoFrame (I := I) g₀ x w x))) ≤ C₀ * G := by
    intro z w
    have ht := hpw g₁ P h hδ hδ0 hbound x (smoothOrthoFrame (I := I) g₀ x z x)
      (smoothOrthoFrame (I := I) g₀ x w x)
    rw [hframe1 z, hframe1 w, Real.sqrt_one, mul_one, mul_one, ← hG_def] at ht
    exact ht
  have key3 : ∀ (K : Fin 3 → Fin n) (u : Fin 3 → E),
      |Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 3 e K) u| ≤
        Real.sqrt (g₀.inner x (u 0) (u 0)) * Real.sqrt (g₀.inner x (u 1) (u 1)) *
          Real.sqrt (g₀.inner x (u 2) (u 2)) := by
    intro K u
    rw [show Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 3 e K) u =
        coframeS (I := I) (M := M) g₀ x 3 e K u from rfl, coframeS_apply,
      Fin.prod_univ_three, abs_mul, abs_mul]
    have b0 := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e (K 0)) (u 0)
    have b1 := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e (K 1)) (u 1)
    have b2 := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e (K 2)) (u 2)
    rw [he1 (K 0), Real.sqrt_one, one_mul] at b0
    rw [he1 (K 1), Real.sqrt_one, one_mul] at b1
    rw [he1 (K 2), Real.sqrt_one, one_mul] at b2
    exact mul_le_mul (mul_le_mul b0 b1 (abs_nonneg _) (Real.sqrt_nonneg _)) b2 (abs_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have htriple : ∀ (K : Fin 3 → Fin n) (a b c d : Fin (Module.finrank ℝ E))
      (call : Fin 4) (contrib : Fin 5),
      |Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 3 e K)
          (fiveSlotTriple (I := I) g₀ g₁ x a b c d call contrib)| ≤ C₀ * G := by
    intro K a b c d call contrib
    refine le_trans (key3 K (fiveSlotTriple (I := I) g₀ g₁ x a b c d call contrib)) ?_
    fin_cases call <;> fin_cases contrib <;>
      simp only [fiveSlotTriple, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta,
        Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, hframe1, Real.sqrt_one,
        one_mul, mul_one] <;>
      exact hsqrt_cd _ _
  have heach_abs : ∀ (K : Fin 3 → Fin n) (J : Fin 2 → Fin n),
      |fiberNormSqComponent (I := I) (M := M) g₀ x 3 2
          (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x)
          n e K J| ≤ Mc * G := by
    intro K J
    rw [fiberNormSqComponent_arm1FiveSlotFib (I := I) g₀ g₁ x e K J]
    have hkernel : ∀ c d : Fin (Module.finrank ℝ E),
        |fiveSlotKernelBilin (I := I) g₀ x c d (e (J 0)) (e (J 1))| ≤ 1 := by
      intro c d
      rw [fiveSlotKernelBilin_apply, abs_mul]
      have h0 := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e (J 0))
        (smoothOrthoFrame (I := I) g₀ x c x)
      have h1 := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e (J 1))
        (smoothOrthoFrame (I := I) g₀ x d x)
      rw [he1 (J 0), hframe1 c, Real.sqrt_one, mul_one] at h0
      rw [he1 (J 1), hframe1 d, Real.sqrt_one, mul_one] at h1
      calc |g₀.inner x (e (J 0)) (smoothOrthoFrame (I := I) g₀ x c x)| *
              |g₀.inner x (e (J 1)) (smoothOrthoFrame (I := I) g₀ x d x)|
          ≤ 1 * 1 := mul_le_mul h0 h1 (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hsummand_bd : ∀ i : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × Fin 4 × Fin 5,
        |((-(1 : ℝ) / 2) * fiveSlotCometricCoeff (I := I) g₀ g₁ x i.1 i.2.1 *
              fiveSlotSign i.2.2.2.2.1) *
            Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 3 e K)
              (fiveSlotTriple (I := I) g₀ g₁ x i.1 i.2.1 i.2.2.1 i.2.2.2.1
                i.2.2.2.2.1 i.2.2.2.2.2) *
            fiveSlotKernelBilin (I := I) g₀ x i.2.2.1 i.2.2.2.1 (e (J 0)) (e (J 1))| ≤
          (1 / 2) * (1 / (1 - δ₀)) * C₀ * G := by
      intro i
      obtain ⟨a, b, c, d, call, contrib⟩ := i
      rw [abs_mul, abs_mul]
      have hX : |(-(1 : ℝ) / 2) * fiveSlotCometricCoeff (I := I) g₀ g₁ x a b *
          fiveSlotSign call| ≤ (1 / 2) * (1 / (1 - δ₀)) := by
        rw [abs_mul, abs_mul, hsign call, mul_one,
          show |(-(1 : ℝ) / 2)| = 1 / 2 from by norm_num]
        exact mul_le_mul_of_nonneg_left (hcometric a b) (by norm_num)
      have hX_nn : (0 : ℝ) ≤ (1 / 2) * (1 / (1 - δ₀)) :=
        mul_nonneg (by norm_num) (le_of_lt hinv_pos)
      calc |(-(1 : ℝ) / 2) * fiveSlotCometricCoeff (I := I) g₀ g₁ x a b *
                fiveSlotSign call| *
              |Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 3 e K)
                (fiveSlotTriple (I := I) g₀ g₁ x a b c d call contrib)| *
              |fiveSlotKernelBilin (I := I) g₀ x c d (e (J 0)) (e (J 1))|
          ≤ (1 / 2) * (1 / (1 - δ₀)) * (C₀ * G) * 1 :=
            mul_le_mul
              (mul_le_mul hX (htriple K a b c d call contrib) (abs_nonneg _) hX_nn)
              (hkernel c d) (abs_nonneg _)
              (mul_nonneg hX_nn (mul_nonneg hC₀0 hG_nn))
        _ = (1 / 2) * (1 / (1 - δ₀)) * C₀ * G := by ring
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun i _ => hsummand_bd i)) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hMc]
    have hcardT : (Fintype.card (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × Fin 4 × Fin 5) : ℝ) =
        (Module.finrank ℝ E : ℝ) ^ 4 * 20 := by
      simp only [Fintype.card_prod, Fintype.card_fin]; push_cast; ring
    rw [hcardT]; exact le_of_eq (by ring)
  have heach : ∀ (K : Fin 3 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 3 2
          (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x)
          n e K J) ^ 2 ≤ (Mc * G) ^ 2 := by
    intro K J
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (heach_abs K J) 2
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 3 2 x
    (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x)
    e bse hnE hbse horth]
  calc ∑ K : Fin 3 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 3 2
          (show Tensor0SBundle.TensorRSSpace 3 2 I x from arm1FiveSlotFib (I := I) g₀ g₁ x)
          n e K J) ^ 2
      ≤ ∑ K : Fin 3 → Fin n, ∑ J : Fin 2 → Fin n, (Mc * G) ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = (Fintype.card (Fin 3 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ) *
          (Mc * G) ^ 2 := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]; ring
    _ = (Module.finrank ℝ E : ℝ) ^ 5 * Mc ^ 2 * G ^ 2 := by
        have hcard : (Fintype.card (Fin 3 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ) =
            (n : ℝ) ^ 5 := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          push_cast; ring
        rw [hcard, ← hnE]; ring

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_arm1FiveSlotField_realizedFam_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((arm1FiveSlotField (I := I) g₀ T T' hδ hδ' s).toSection x) ≤ Λ := by
  classical
  obtain ⟨C, hC0, hbnd⟩ :=
    rfns_arm1FiveSlotFib_le_of_lt_one (I := I) (M := M) g₀
      (le_max_right δ₀ 0) (max_lt hδ₀ (by norm_num))
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_Csob_convexPerturbation_pointwise_C2_le (I := I) (M := M) g₀ a ha_super
  refine ⟨C * (Csob * R) ^ 2, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  letI instTens : Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  set m : ℝ := max δ₀ 0 with hm_def
  have hm0 : 0 ≤ m := le_max_right _ _
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs_mem y v w
  have hδs_raw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  obtain ⟨hs0, hs1⟩ := hs
  have habs_eq : |1 - s| * δ' + |s| * δ = (1 - s) * δ' + s * δ := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
  have hsmall_le : (1 - s) * δ' + s * δ ≤ m := by
    have h1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le (by linarith)
    have h2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have hδ₀_le : δ₀ ≤ m := le_max_left _ _
    nlinarith [h1, h2, hδ₀_le]
  have hδs : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)) m := by
    intro y v w
    refine le_trans (hδs_raw y v w) ?_
    have hprod : 0 ≤ Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hle' : |1 - s| * δ' + |s| * δ ≤ m := by rw [habs_eq]; exact hsmall_le
    nlinarith [hle', hprod]
  have hmain := hbnd (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) htie (le_of_eq hm_def.symm) hm0 hδs x
  rw [show (arm1FiveSlotField (I := I) g₀ T T' hδ hδ' s).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from
        arm1FiveSlotFib (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) x) from rfl]
  refine le_trans hmain ?_
  have hG_le : ‖((iteratedCovGrad (I := I) g₀ 0 2 1
        (convexPerturbation (I := I) g₀ T T' s)).toSection x :
        Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ≤ Csob * R := by
    have hCsob_sum := hCsob T T' hR hTball hT'ball s ⟨hs0, hs1⟩ x
    have hterms : ∀ k ∈ Finset.range 3, 0 ≤
        (letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
        ‖(iteratedCovGrad (I := I) g₀ 0 2 k
            (convexPerturbation (I := I) g₀ T T' s)).toSection x‖) := by
      intro k _
      letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
      exact norm_nonneg _
    exact le_trans (Finset.single_le_sum hterms
      (show (1 : ℕ) ∈ Finset.range 3 from Finset.mem_range.mpr (by norm_num))) hCsob_sum
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hG_le 2) hC0

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
