import DifferentialGeometry.Geometry.Flow.VectorField
import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceFieldJets
import DifferentialGeometry.Geometry.Curvature.Order2Defect.MetricTraceFrame
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.ConnectionDifferenceKoszul
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SharpOrderRealizedJetEmbedding
import DifferentialGeometry.Geometry.Connection.TensorNabla.LiftedSectionCovariantRealizeBridge
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.RiemannianFiberNormSqRiemannOpDualFrameParseval
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.RiemannianFiberNormSqRiemannOpHigherRankParseval
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.CovGradBundleEquivFiberNormFrameSum
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.PosDefPerturbation

/-! # The intrinsic family-uniform value bound of the DeTurck vector field

For a closed (compact, boundaryless) smooth Riemannian manifold modelled on a real inner-product
space `E`, this file proves the **chart-free, family-uniform `g₀`-fibre value bound** of the
DeTurck vector field `W₁ = deTurckVF g₁ g_bg`, where `g₁ = g₀ + ccTensorBilinSymm g₀ T₁` ranges
over the fibre-small (`gFibreOpBound g₀ … δ`, `δ < 1/2`) supercritically `H^{a+2}`-bounded realized
perturbation family:
`√(g₀ x (W₁ x) (W₁ x)) ≤ Λ_W` for a single constant `Λ_W ≥ 0` over the manifold and the family.

## The chartJ obstruction, and the intrinsic route around it

The on-disk evaluation formula `deTurckVF_apply_eq` reads `W₁ x` through the chart-frame inverse
Gram `chartInvGramMatrix g₁ x x` and the chart frame `chartBasisVecFiber x · x`.  Those chart
quantities are genuinely unbounded over a multi-chart manifold (the standard `S²` obstruction:
`chartGramMatrix_entry_isBounded_on_compact` is *per-chart only*), so a term-by-term bound of the
chart-trace is not family-uniform.

The sound route is **intrinsic**: the chart-Gram-weighted trace
`∑_{jk} (g₁⁻¹)^{jk} A(e_j, e_k)` is the basis-independent `g₁`-cometric trace of the connection
difference `A = connDiff g₁ g_bg x`, so in any `g₁`-orthonormal frame `{B_i}` it collapses to the
plain frame sum `W₁ x = ∑_i A(B_i, B_i)` (`deTurckVF_eq_sum_orthonormalBasis`, by the frame-trace
identity `orthonormal_basis_bilin_trace_chartα`).  In a `g₁`-orthonormal frame the inverse Gram is
the identity, so no unbounded chart weight survives.

## The bound

Splitting `connDiff g₁ g_bg = connDiff g₁ g₀ + connDiff g₀ g_bg`:

* the **variable** part `connDiff g₁ g₀` is first order in the metric perturbation
  `h = ccTensorBilinSymm g₀ T₁`; its `g₀`-operator value is family-uniformly controlled by the
  Koszul triangle with Neumann self-absorption (`connDiff_g0_fibre_abs_bound`) through the
  supercritical `H^{a+2} ↪ C¹` embedding of the metric jet
  (`exists_covDerivRealizeEval_gcs_value_bound`), reproduced here as the `g₀`-operator value bound
  `connDiff_g1g0_gOp_value_le`;
* the **fixed** part `connDiff g₀ g_bg` is a single smooth `(1,2)`-tensor, so its `g₀`-fibre value
  is bounded on the compact manifold by `exists_bound_riemannianFiberNormSq_smoothCcTensor` applied
  to the `g₀`-lowered section `loweredConnDiffSection g_bg g₀` (using the metric antisymmetry
  `connDiff g₀ g_bg = − connDiff g_bg g₀`).

The `g₁`-orthonormal frame vectors `B_i` have `g₀`-quadratic at most `1/(1−δ)` (the lower Neumann
comparison `perturbedInner_self_lower_bound`), so `√(g₀ (W₁ x) (W₁ x)) ≤ ∑_i √(g₀ (A(B_i,B_i)))` is
bounded by `finrank · (Λ_C + Λ_bg) / (1 − δ)`, family-uniformly.

## Non-vacuity

Genuine: `Λ_W = 0` forces `W₁ ≡ 0`, false whenever `deTurckVF g₁ g_bg ≠ 0`; at `g₁ = g_bg`
realized the field is the zero section (`deTurckVF_self`) and `Λ_W = 0` works there. -/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace Pullback

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.DeTurck

/-! ### The connection-difference evaluation algebra (boundaryless-free block)

The two `MDiffAt`-gated connection-difference identities below are pure tangent-bundle facts; they
are proved in the variable context without `CompactSpace` / `I.Boundaryless`, whose tangent-bundle
`ChartedSpace` instances obstruct the `MDiffAt (T% ·)` elaboration, then consumed at the fibre level
by the main bound. -/

section CovDerivAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

set_option linter.unusedSectionVars false in
/-- **Metric antisymmetry of the connection difference.**  `connDiff g g' = − connDiff g' g`,
because `connDiff g g'` evaluated on a smooth extension is `∇^{LC}(g) − ∇^{LC}(g')`. -/
private theorem connDiff_metric_antisymm
    (g g' : SmoothRiemannianMetric I M) (x : M) (u v : TangentSpace I x) :
    connDiff (I := I) g g' x u v = - connDiff (I := I) g' g x u v := by
  set σ := Integral.Connection.smoothExtensionTangent (I := I) x u with hσ
  have hσx : σ x = u := Integral.Connection.smoothExtensionTangent_eq (I := I) x u
  have hσsmooth : MDiffAt (T% σ) x :=
    Integral.Connection.smoothExtensionTangent_mdiff (I := I) x u x
  have h1 : connDiff (I := I) g g' x u v =
      (LeviCivita g σ x) v - (LeviCivita g' σ x) v := by
    have := connDiff_apply (I := I) g g' (σ := σ) (x := x) hσsmooth v
    rw [hσx] at this; exact this
  have h2 : connDiff (I := I) g' g x u v =
      (LeviCivita g' σ x) v - (LeviCivita g σ x) v := by
    have := connDiff_apply (I := I) g' g (σ := σ) (x := x) hσsmooth v
    rw [hσx] at this; exact this
  rw [h1, h2]; abel

set_option linter.unusedSectionVars false in
/-- **Metric additivity of the connection difference (diagonal evaluation).**
`connDiff g₁ g_bg x u u = connDiff g₁ g₀ x u u + connDiff g₀ g_bg x u u`, because each connection
difference telescopes through the Levi-Civita connections (`connDiff_apply`). -/
private theorem connDiff_eval_add
    (g₁ g₀ g_bg : SmoothRiemannianMetric I M) (x : M) (u : TangentSpace I x) :
    connDiff (I := I) g₁ g_bg x u u =
      connDiff (I := I) g₁ g₀ x u u + connDiff (I := I) g₀ g_bg x u u := by
  set σ := Integral.Connection.smoothExtensionTangent (I := I) x u with hσ
  have hσx : σ x = u := Integral.Connection.smoothExtensionTangent_eq (I := I) x u
  have hσsmooth : MDiffAt (T% σ) x :=
    Integral.Connection.smoothExtensionTangent_mdiff (I := I) x u x
  have e1 : connDiff (I := I) g₁ g_bg x u u =
      (LeviCivita g₁ σ x) u - (LeviCivita g_bg σ x) u := by
    have := connDiff_apply (I := I) g₁ g_bg (σ := σ) (x := x) hσsmooth u
    rw [hσx] at this; exact this
  have e2 : connDiff (I := I) g₁ g₀ x u u =
      (LeviCivita g₁ σ x) u - (LeviCivita g₀ σ x) u := by
    have := connDiff_apply (I := I) g₁ g₀ (σ := σ) (x := x) hσsmooth u
    rw [hσx] at this; exact this
  have e3 : connDiff (I := I) g₀ g_bg x u u =
      (LeviCivita g₀ σ x) u - (LeviCivita g_bg σ x) u := by
    have := connDiff_apply (I := I) g₀ g_bg (σ := σ) (x := x) hσsmooth u
    rw [hσx] at this; exact this
  rw [e1, e2, e3]; abel

end CovDerivAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### The `g₀`-self-norm Riesz lift -/

set_option linter.unusedSectionVars false in
/-- **The `g₀`-self-norm Riesz lift.**  If a vector `z` has its `g₀`-pairing against every direction
`c` bounded by `K · √(g₀ c c)`, then its `g₀`-self-norm is bounded by `K`.  Tested at `c = z`:
`g₀(z, z) ≤ K · √(g₀ z z)` and `g₀(z, z) = √(g₀ z z)²` give `√(g₀ z z) ≤ K`. -/
private theorem sqrt_gInner_self_le_of_forall_inner_le
    (g₀ : SmoothRiemannianMetric I M) (x : M) (z : TangentSpace I x) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ c : TangentSpace I x, |g₀.inner x z c| ≤ K * Real.sqrt (g₀.inner x c c)) :
    Real.sqrt (g₀.inner x z z) ≤ K := by
  have hzz_nn : 0 ≤ g₀.inner x z z :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x z
  have hsq : Real.sqrt (g₀.inner x z z) * Real.sqrt (g₀.inner x z z) = g₀.inner x z z := by
    rw [← Real.sqrt_mul hzz_nn, Real.sqrt_mul_self hzz_nn]
  have hzz : g₀.inner x z z ≤ K * Real.sqrt (g₀.inner x z z) := by
    have h := hK z
    have hle : g₀.inner x z z ≤ |g₀.inner x z z| := le_abs_self _
    exact le_trans hle h
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (g₀.inner x z z)) with hzero | hpos
  · rw [← hzero]; exact hK0
  · have hsqz : Real.sqrt (g₀.inner x z z) * Real.sqrt (g₀.inner x z z) ≤
        K * Real.sqrt (g₀.inner x z z) := by rw [hsq]; exact hzz
    exact le_of_mul_le_mul_right (by linarith [hsqz]) hpos

/-! ### The `g₀`-norm triangle inequalities -/

set_option linter.unusedSectionVars false in
/-- **Binary triangle inequality for the `g₀`-norm.**  `√(g₀ (z+w) (z+w)) ≤ √(g₀ z z) + √(g₀ w w)`,
from the expansion `g₀(z+w, z+w) = g₀(z,z) + 2 g₀(z,w) + g₀(w,w)` and Cauchy–Schwarz. -/
private theorem sqrt_gInner_add_le
    (g₀ : SmoothRiemannianMetric I M) (x : M) (z w : TangentSpace I x) :
    Real.sqrt (g₀.inner x (z + w) (z + w)) ≤
      Real.sqrt (g₀.inner x z z) + Real.sqrt (g₀.inner x w w) := by
  have hnnZ := DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
    (I := I) (M := M) g₀ x z
  have hnnW := DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
    (I := I) (M := M) g₀ x w
  have hexpand : g₀.inner x (z + w) (z + w) =
      g₀.inner x z z + 2 * g₀.inner x z w + g₀.inner x w w := by
    have hsymm : g₀.inner x w z = g₀.inner x z w := g₀.symm x w z
    simp only [map_add, ContinuousLinearMap.add_apply]
    rw [hsymm]; ring
  have hCS : g₀.inner x z w ≤ Real.sqrt (g₀.inner x z z) * Real.sqrt (g₀.inner x w w) := by
    have habs : |g₀.inner x z w| ≤ Real.sqrt (g₀.inner x z z) * Real.sqrt (g₀.inner x w w) :=
      DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
        (I := I) (M := M) g₀ x z w
    exact le_trans (le_abs_self _) habs
  have hsqZ : Real.sqrt (g₀.inner x z z) ^ 2 = g₀.inner x z z := Real.sq_sqrt hnnZ
  have hsqW : Real.sqrt (g₀.inner x w w) ^ 2 = g₀.inner x w w := Real.sq_sqrt hnnW
  have hub : g₀.inner x (z + w) (z + w) ≤
      (Real.sqrt (g₀.inner x z z) + Real.sqrt (g₀.inner x w w)) ^ 2 := by
    rw [hexpand]
    have hsq : (Real.sqrt (g₀.inner x z z) + Real.sqrt (g₀.inner x w w)) ^ 2 =
        g₀.inner x z z + 2 * (Real.sqrt (g₀.inner x z z) * Real.sqrt (g₀.inner x w w)) +
          g₀.inner x w w := by rw [add_sq, hsqZ, hsqW]; ring
    rw [hsq]; nlinarith [hCS]
  calc Real.sqrt (g₀.inner x (z + w) (z + w))
      ≤ Real.sqrt ((Real.sqrt (g₀.inner x z z) + Real.sqrt (g₀.inner x w w)) ^ 2) :=
        Real.sqrt_le_sqrt hub
    _ = Real.sqrt (g₀.inner x z z) + Real.sqrt (g₀.inner x w w) := by
        rw [Real.sqrt_sq (by positivity)]

set_option linter.unusedSectionVars false in
/-- **Finite-sum triangle inequality for the `g₀`-norm.**
`√(g₀ (∑ᵢ zᵢ) (∑ᵢ zᵢ)) ≤ ∑ᵢ √(g₀ zᵢ zᵢ)`, by induction on the index `Finset` using
`sqrt_gInner_add_le`. -/
private theorem sqrt_gInner_self_sum_le_sum_sqrt
    (g₀ : SmoothRiemannianMetric I M) (x : M) {ι : Type*} (s : Finset ι)
    (z : ι → TangentSpace I x) :
    Real.sqrt (g₀.inner x (∑ i ∈ s, z i) (∑ i ∈ s, z i)) ≤
      ∑ i ∈ s, Real.sqrt (g₀.inner x (z i) (z i)) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine le_trans (sqrt_gInner_add_le (I := I) (M := M) g₀ x (z a) (∑ i ∈ s, z i)) ?_
      have := ih
      linarith

/-! ### The rank-`(0,3)` `g₀`-fibre Cauchy–Schwarz -/

set_option linter.unusedSectionVars false in
/-- **The rank-`(0,3)` `g₀`-fibre Cauchy–Schwarz for a model `(0,3)`-form.**  For a `(0,3)`-fibre
value `Sec : SmoothCcTensor g₀ 0 3`, the absolute model evaluation `|toModel … ![a, b, c]|` is
bounded by the square root of the `(0,3)` Riemannian fibre-norm-squared times the `g₀`-quadratic
factors of the three directions.  Proved by expanding `a, b, c` in a `g₀`-orthonormal frame, the
triple Cauchy–Schwarz, and Parseval. -/
private theorem abs_toModel_three_le_sqrt_rfns
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Sec : Integral.L2.SmoothCcTensor g₀ 0 3) (a b c : TangentSpace I x) :
    |Tensor0SBundle.Tensor0SSpace.toModel (Sec.toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c]| ≤
      Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          (Sec.toSection x)) *
        Real.sqrt (g₀.inner x a a) *
        Real.sqrt (g₀.inner x b b) * Real.sqrt (g₀.inner x c c) := by
  classical
  obtain ⟨n, e, hn, horth, hpars, hexpand, _hrepr2⟩ :=
    Integral.Connection.tangent_frame_expansion (I := I) (M := M) g₀ x
  have hrepr : ∀ (S : Tensor0SBundle.TensorRSSpace 0 3 I x),
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x S =
        ∑ K, ∑ J, Integral.Connection.fiberNormSqSummand (I := I) (M := M) g₀ x 0 3 S n e K J := by
    intro S
    exact Integral.Connection.rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M)
      g₀ 3 x S e hn horth
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  have hcomp_eq : ∀ J : Fin 3 → Fin n,
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 3
          (Sec.toSection x) n e K₀ J =
        Tensor0SBundle.Tensor0SSpace.toModel (Sec.toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          ![e (J 0), e (J 1), e (J 2)] := by
    intro J
    have hcoframe :
        (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun k => g₀.inner x (e (K₀ k))) =
          ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := by
      apply ContinuousMultilinearMap.ext
      intro v
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiAlgebra_apply, Finset.prod_of_isEmpty]
      rfl
    unfold Integral.Connection.fiberNormSqComponent
    rw [hcoframe]
    rw [Tensor0SBundle.Tensor0SSpace.toModel,
      Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply]
    congr 1
    funext k
    fin_cases k <;> rfl
  set σ := Sec.toSection x
    (ContinuousMultilinearMap.constOfIsEmpty ℝ
      (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) with hσ
  set Bval : ℝ := Tensor0SBundle.Tensor0SSpace.toModel σ ![a, b, c] with hB_def
  set abc : Fin 3 → TangentSpace I x := ![a, b, c] with habc
  set Tval : (Fin 3 → Fin n) → ℝ := fun J =>
    Tensor0SBundle.Tensor0SSpace.toModel σ (fun t => e (J t)) with hT_def
  set cf : (Fin 3 → Fin n) → ℝ := fun J =>
    ∏ t : Fin 3, g₀.inner x (e (J t)) (abc t) with hcf_def
  have hexp : Bval = ∑ J : Fin 3 → Fin n, cf J * Tval J := by
    have hcong : abc = (fun t : Fin 3 => ∑ i : Fin n, g₀.inner x (e i) (abc t) • e i) := by
      funext t; exact hexpand (abc t)
    have hmap := (Tensor0SBundle.Tensor0SSpace.toModel σ).map_sum_finset
      (fun (t : Fin 3) (i : Fin n) => g₀.inner x (e i) (abc t) • e i)
    rw [hB_def]
    calc Tensor0SBundle.Tensor0SSpace.toModel σ abc
        = Tensor0SBundle.Tensor0SSpace.toModel σ
            (fun t : Fin 3 => ∑ i : Fin n, g₀.inner x (e i) (abc t) • e i) := by
              congr 1
      _ = ∑ J ∈ Fintype.piFinset (fun _ : Fin 3 => (Finset.univ : Finset (Fin n))),
            Tensor0SBundle.Tensor0SSpace.toModel σ
              (fun t => g₀.inner x (e (J t)) (abc t) • e (J t)) :=
            hmap (fun _ : Fin 3 => (Finset.univ : Finset (Fin n)))
      _ = ∑ J : Fin 3 → Fin n, cf J * Tval J := by
            rw [Fintype.piFinset_univ]
            refine Finset.sum_congr rfl (fun J _ => ?_)
            rw [hcf_def, hT_def]
            have hsmul := (Tensor0SBundle.Tensor0SSpace.toModel σ).toMultilinearMap.map_smul_univ
              (fun t : Fin 3 => g₀.inner x (e (J t)) (abc t)) (fun t : Fin 3 => e (J t))
            rw [ContinuousMultilinearMap.coe_coe] at hsmul
            rw [smul_eq_mul] at hsmul
            exact hsmul
  have hCS : (∑ J : Fin 3 → Fin n, cf J * Tval J) ^ 2 ≤
      (∑ J : Fin 3 → Fin n, cf J ^ 2) * ∑ J : Fin 3 → Fin n, Tval J ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ cf Tval
  have hcfsq : (∑ J : Fin 3 → Fin n, cf J ^ 2) =
      g₀.inner x a a * g₀.inner x b b * g₀.inner x c c := by
    have hstep : (∑ J : Fin 3 → Fin n, cf J ^ 2) =
        ∏ t : Fin 3, ∑ i : Fin n, g₀.inner x (e i) (abc t) ^ 2 := by
      rw [Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset (Fin n)))
        (fun (t : Fin 3) (i : Fin n) => g₀.inner x (e i) (abc t) ^ 2)]
      rw [Fintype.piFinset_univ]
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [hcf_def, ← Finset.prod_pow]
    rw [hstep, Fin.prod_univ_three]
    have h0 : abc 0 = a := rfl
    have h1 : abc 1 = b := rfl
    have h2 : abc 2 = c := rfl
    rw [h0, h1, h2, hpars a, hpars b, hpars c]
  have hTsq : (∑ J : Fin 3 → Fin n, Tval J ^ 2) =
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (Sec.toSection x) := by
    rw [Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g₀ x 3 e
      hrepr (Sec.toSection x) K₀]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    have hfun : (fun t : Fin 3 => e (J t)) = ![e (J 0), e (J 1), e (J 2)] := by
      funext t; fin_cases t <;> rfl
    change (Tensor0SBundle.Tensor0SSpace.toModel σ (fun t : Fin 3 => e (J t))) ^ 2 =
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 3
        (Sec.toSection x) n e K₀ J ^ 2
    rw [hfun]
    exact congrArg (· ^ 2) (hcomp_eq J).symm
  have hBsq : Bval ^ 2 ≤ g₀.inner x a a * g₀.inner x b b * g₀.inner x c c *
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (Sec.toSection x) := by
    rw [hexp]
    refine hCS.trans ?_
    rw [hcfsq, hTsq]
  have hB_abs : |Bval| ≤ Real.sqrt (g₀.inner x a a * g₀.inner x b b * g₀.inner x c c *
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (Sec.toSection x)) := by
    rw [show |Bval| = Real.sqrt (Bval ^ 2) from (Real.sqrt_sq_eq_abs Bval).symm]
    exact Real.sqrt_le_sqrt hBsq
  refine hB_abs.trans ?_
  have ha := DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x a
  have hb := DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x b
  have hc := DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x c
  have hr := Integral.Connection.riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 3 x
    (Sec.toSection x)
  rw [show g₀.inner x a a * g₀.inner x b b * g₀.inner x c c *
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (Sec.toSection x) =
      (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (Sec.toSection x)) *
        (g₀.inner x a a) * (g₀.inner x b b) * (g₀.inner x c c) from by ring]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]

/-! ### The realized covariant-derivative `C⁰` value bound -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **The family-uniform `C⁰` value bound of the realized covariant-derivative `(0,3)`-evaluation.**
For the supercritically `H^{a+2}`-bounded (`2a > finrank + 4`) perturbation family there is a single
constant `Φ ≥ 0` such that, whenever `‖T₁.toHs(a+2)‖ ≤ B`, the realized `(0,3)`-covariant-derivative
evaluation obeys `|covDerivRealizeEval g₀ T₁ x p q r| ≤ Φ · √(g₀ p p) · √(g₀ q q) · √(g₀ r r)`. -/
private theorem exists_covDerivRealizeEval_gcs_value_bound
    (g₀ : SmoothRiemannianMetric I M) (B : ℝ) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Φ : ℝ, 0 ≤ Φ ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2),
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ∀ (x : M) (p q r : TangentSpace I x),
          |covDerivRealizeEval (I := I) g₀ T₁ x p q r| ≤
            Φ * Real.sqrt (g₀.inner x p p) * Real.sqrt (g₀.inner x q q) *
              Real.sqrt (g₀.inner x r r) := by
  classical
  have hsuper : 2 * (a + 2) > Module.finrank ℝ E + 4 := by omega
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    exists_iteratedCovGradJetSum_le_toHs_sharpOrder (I := I) (M := M) g₀ (a + 2) hsuper
  refine ⟨C₀ * max B 0, by positivity, fun T₁ hB x p q r => ?_⟩
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + 0) I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 0)
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + 1) I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + 2) I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 2)
  set Sec : Integral.L2.SmoothCcTensor g₀ 0 3 :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2 (realizeSymmCcTensor (I := I) g₀ T₁) with hSec
  have hSeceq : Sec = PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 1
      (realizeSymmCcTensor (I := I) g₀ T₁) := by
    rw [hSec, PDE.RicciFlow.iteratedCovGrad_succ (I := I) g₀ 0 2 0
      (realizeSymmCcTensor (I := I) g₀ T₁),
      PDE.RicciFlow.iteratedCovGrad_zero (I := I) g₀ 0 2
        (realizeSymmCcTensor (I := I) g₀ T₁)]
  have hsqrt_le : Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        (Sec.toSection x)) ≤ C₀ * max B 0 := by
    have hsummand : Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          (Sec.toSection x)) ≤
        iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x := by
      rw [iteratedCovGradJetSum, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
      rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.norm_toSection_eq_sqrt_riemannianFiberNormSq_installed
          (I := I) (M := M) g₀ 0 (2 + 0)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 0
            (realizeSymmCcTensor (I := I) g₀ T₁)) x,
        DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.norm_toSection_eq_sqrt_riemannianFiberNormSq_installed
          (I := I) (M := M) g₀ 0 (2 + 1)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 1
            (realizeSymmCcTensor (I := I) g₀ T₁)) x,
        DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.norm_toSection_eq_sqrt_riemannianFiberNormSq_installed
          (I := I) (M := M) g₀ 0 (2 + 2)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 2
            (realizeSymmCcTensor (I := I) g₀ T₁)) x]
      have hSec_rfns : Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            (Sec.toSection x) =
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 1
              (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x) := by rw [hSeceq]
      rw [hSec_rfns]
      have h0 := Real.sqrt_nonneg (Integral.Connection.riemannianFiberNormSq (I := I) (M := M)
        g₀ 0 (2 + 0) x ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 0
          (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x))
      have h2 := Real.sqrt_nonneg (Integral.Connection.riemannianFiberNormSq (I := I) (M := M)
        g₀ 0 (2 + 2) x ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 2
          (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x))
      linarith
    have hreal := realizeSymm_iteratedCovGradJetSum_le (I := I) g₀ T₁ x
    have hemb := hC₀ T₁ x
    have hBmax : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤
        max B 0 := le_trans hB (le_max_left _ _)
    have hchain : iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x ≤
        C₀ * max B 0 := by
      refine le_trans hreal (le_trans hemb ?_)
      exact mul_le_mul_of_nonneg_left hBmax hC₀pos.le
    exact le_trans hsummand hchain
  have hmodel := covGrad_realizeSymm_unitModel_eq_covDerivRealizeEval (I := I) g₀ T₁ x p q r
  have hCS := abs_toModel_three_le_sqrt_rfns (I := I) (M := M) g₀ x Sec p q r
  rw [hSec] at hCS
  rw [hmodel] at hCS
  refine le_trans hCS ?_
  have hppnn : 0 ≤ Real.sqrt (g₀.inner x p p) := Real.sqrt_nonneg _
  have hqqnn : 0 ≤ Real.sqrt (g₀.inner x q q) := Real.sqrt_nonneg _
  have hrrnn : 0 ≤ Real.sqrt (g₀.inner x r r) := Real.sqrt_nonneg _
  have hsqrt_le' : Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
        (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x)) ≤ C₀ * max B 0 := by
    rw [← hSec]; exact hsqrt_le
  apply mul_le_mul_of_nonneg_right _ hrrnn
  apply mul_le_mul_of_nonneg_right _ hqqnn
  exact mul_le_mul_of_nonneg_right hsqrt_le' hppnn

/-! ### The `g₀`-operator value bound of the variable connection difference -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **The family-uniform `g₀`-operator value bound of the connection difference `connDiff g₁ g₀`.**
For the fibre-small supercritically `H^{a+2}`-bounded realized perturbation family,
`√(g₀ x (connDiff g₁ g₀ x u v) (connDiff g₁ g₀ x u v)) ≤ Λ_C · √(g₀ x u u) · √(g₀ x v v)` for a single
constant `Λ_C ≥ 0`.  Reproduced via the Koszul triangle with Neumann self-absorption
(`connDiff_g0_fibre_abs_bound`) and the supercritical embedding `exists_covDerivRealizeEval_gcs_value_bound`. -/
private theorem connDiff_g1g0_gOp_value_le
    (g₀ : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Λ_C : ℝ, 0 ≤ Λ_C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ∀ (x : M) (u v : TangentSpace I x),
          Real.sqrt (g₀.inner x (connDiff (I := I) g₁ g₀ x u v) (connDiff (I := I) g₁ g₀ x u v)) ≤
            Λ_C * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by
  classical
  obtain ⟨Φ, hΦ0, hΦ⟩ := exists_covDerivRealizeEval_gcs_value_bound (I := I) (M := M) g₀ B a ha
  have hδlt1 : δ < 1 := by linarith
  have h1δpos : 0 < 1 - δ := by linarith
  refine ⟨3 * Φ / (2 * (1 - δ)), by positivity, fun T₁ g₁ hg₁ hδbnd hB x u v => ?_⟩
  set z : TangentSpace I x := connDiff (I := I) g₁ g₀ x u v with hz
  set su := Real.sqrt (g₀.inner x u u) with hsu
  set sv := Real.sqrt (g₀.inner x v v) with hsv
  have hsu_nn : 0 ≤ su := Real.sqrt_nonneg _
  have hsv_nn : 0 ≤ sv := Real.sqrt_nonneg _
  have hext : connDiff (I := I) g₁ g₀ x
        (Integral.Connection.smoothExtensionTangent (I := I) x u x)
        (Integral.Connection.smoothExtensionTangent (I := I) x v x) = z := by
    rw [Integral.Connection.smoothExtensionTangent_eq (I := I) x u,
      Integral.Connection.smoothExtensionTangent_eq (I := I) x v]
  have hpair : ∀ c : TangentSpace I x,
      |g₀.inner x z c| ≤ ((3 * Φ / 2) * su * sv + δ * Real.sqrt (g₀.inner x z z)) *
        Real.sqrt (g₀.inner x c c) := by
    intro c
    have hkos := connDiff_g0_fibre_abs_bound (I := I) g₁ g₀ T₁ hg₁ x v u c
    rw [hext] at hkos
    have hcdre1 := hΦ T₁ hB x v u c
    have hcdre2 := hΦ T₁ hB x u v c
    have hcdre3 := hΦ T₁ hB x c v u
    set sc := Real.sqrt (g₀.inner x c c) with hsc
    have hsc_nn : 0 ≤ sc := Real.sqrt_nonneg _
    have hself : |ccTensorBilinSymm (I := I) g₀ T₁ x z c| ≤
        δ * Real.sqrt (g₀.inner x z z) * sc := hδbnd x z c
    have hszz_nn : 0 ≤ Real.sqrt (g₀.inner x z z) := Real.sqrt_nonneg _
    have hsum : |2 * g₀.inner x z c| ≤
        3 * Φ * su * sv * sc + 2 * (δ * Real.sqrt (g₀.inner x z z) * sc) := by
      refine le_trans hkos ?_
      have e1 : |covDerivRealizeEval (I := I) g₀ T₁ x v u c| ≤ Φ * sv * su * sc := hcdre1
      have e2 : |covDerivRealizeEval (I := I) g₀ T₁ x u v c| ≤ Φ * su * sv * sc := hcdre2
      have e3 : |covDerivRealizeEval (I := I) g₀ T₁ x c v u| ≤ Φ * sc * sv * su := hcdre3
      have hself2 : 2 * |ccTensorBilinSymm (I := I) g₀ T₁ x z c| ≤
          2 * (δ * Real.sqrt (g₀.inner x z z) * sc) := by linarith
      nlinarith [e1, e2, e3, hself2, hsu_nn, hsv_nn, hsc_nn, hΦ0, mul_nonneg hsu_nn hsv_nn]
    have h2zc : |2 * g₀.inner x z c| = 2 * |g₀.inner x z c| := by rw [abs_mul]; norm_num
    rw [h2zc] at hsum
    have hfinal : |g₀.inner x z c| ≤
        (3 * Φ / 2) * su * sv * sc + δ * Real.sqrt (g₀.inner x z z) * sc := by linarith
    calc |g₀.inner x z c|
        ≤ (3 * Φ / 2) * su * sv * sc + δ * Real.sqrt (g₀.inner x z z) * sc := hfinal
      _ = ((3 * Φ / 2) * su * sv + δ * Real.sqrt (g₀.inner x z z)) * sc := by ring
  set R := Real.sqrt (g₀.inner x z z) with hR
  have hR_nn : 0 ≤ R := Real.sqrt_nonneg _
  have hKnn : 0 ≤ (3 * Φ / 2) * su * sv + δ * R := by positivity
  have hRle : R ≤ (3 * Φ / 2) * su * sv + δ * R :=
    sqrt_gInner_self_le_of_forall_inner_le (I := I) (M := M) g₀ x z hKnn hpair
  have hRabsorb : (1 - δ) * R ≤ (3 * Φ / 2) * su * sv := by nlinarith [hRle]
  have hgoal : R ≤ 3 * Φ / (2 * (1 - δ)) * su * sv := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < 2 * (1 - δ))]
    nlinarith [hRabsorb, h1δpos, hsu_nn, hsv_nn, mul_nonneg hsu_nn hsv_nn, hR_nn]
  exact hgoal

/-! ### The `g₀`-operator value bound of the fixed connection difference -/

set_option linter.unusedSectionVars false in
/-- **The `g₀`-operator value bound of the fixed connection difference `connDiff g₀ g_bg`.**  As a
single smooth `(1,2)`-tensor on the compact manifold, its `g₀`-fibre value satisfies
`√(g₀ x (connDiff g₀ g_bg x u v)²) ≤ Λ_bg · √(g₀ x u u) · √(g₀ x v v)` for a single `Λ_bg ≥ 0`,
through the compact `g₀`-fibre-norm bound of the `g₀`-lowered section `loweredConnDiffSection g_bg g₀`
and the metric antisymmetry `connDiff g₀ g_bg = − connDiff g_bg g₀`. -/
private theorem connDiff_g0gbg_gOp_value_le
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ Λ_bg : ℝ, 0 ≤ Λ_bg ∧
      ∀ (x : M) (u v : TangentSpace I x),
        Real.sqrt (g₀.inner x (connDiff (I := I) g₀ g_bg x u v) (connDiff (I := I) g₀ g_bg x u v)) ≤
          Λ_bg * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by
  classical
  obtain ⟨K, hK0, hK⟩ := Integral.Connection.exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 0 3 (loweredConnDiffSection (I := I) g_bg g₀)
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun x u v => ?_⟩
  set z : TangentSpace I x := connDiff (I := I) g₀ g_bg x u v with hz
  -- Riesz-lift through the pairing `g₀(z, c)`, identified with the lowered model evaluation.
  have hpair : ∀ c : TangentSpace I x,
      |g₀.inner x z c| ≤ Real.sqrt K * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) *
        Real.sqrt (g₀.inner x c c) := by
    intro c
    -- `g₀(z, c) = g₀(connDiff g₀ g_bg x u v, c) = − g₀(connDiff g_bg g₀ x u v, c)`
    --          = − toModel(loweredConnDiffSection g_bg g₀ x) ![v, u, c]
    -- since `loweredConnDiffSection_toModel_apply` reads `![v,u,c] ↦ g₀(connDiff g_bg g₀ x u v, c)`.
    have hanti : z = - connDiff (I := I) g_bg g₀ x u v := by
      rw [hz]; exact connDiff_metric_antisymm (I := I) g₀ g_bg x u v
    have hmodel := loweredConnDiffSection_toModel_apply (I := I) g_bg g₀ x v u c
    have hgzc : g₀.inner x z c =
        - Tensor0SBundle.Tensor0SSpace.toModel
            (((loweredConnDiffSection (I := I) g_bg g₀).toSection x)
              (ContinuousMultilinearMap.constOfIsEmpty ℝ
                (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, u, c] := by
      rw [hanti, map_neg, ContinuousLinearMap.neg_apply, hmodel]
    rw [hgzc, abs_neg]
    have hCS := abs_toModel_three_le_sqrt_rfns (I := I) (M := M) g₀ x
      (loweredConnDiffSection (I := I) g_bg g₀) v u c
    refine le_trans hCS ?_
    have hKb := hK x
    have hsK : Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((loweredConnDiffSection (I := I) g_bg g₀).toSection x)) ≤ Real.sqrt K :=
      Real.sqrt_le_sqrt hKb
    have hcnn : 0 ≤ Real.sqrt (g₀.inner x c c) := Real.sqrt_nonneg _
    have hvnn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
    have hunn : 0 ≤ Real.sqrt (g₀.inner x u u) := Real.sqrt_nonneg _
    calc Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((loweredConnDiffSection (I := I) g_bg g₀).toSection x)) *
          Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x c c)
        ≤ Real.sqrt K *
            Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x c c) := by
          apply mul_le_mul_of_nonneg_right _ hcnn
          apply mul_le_mul_of_nonneg_right _ hunn
          exact mul_le_mul_of_nonneg_right hsK hvnn
      _ = Real.sqrt K * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) *
            Real.sqrt (g₀.inner x c c) := by ring
  have hKnn : 0 ≤ Real.sqrt K * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by
    positivity
  exact sqrt_gInner_self_le_of_forall_inner_le (I := I) (M := M) g₀ x z hKnn hpair

/-! ### The intrinsic orthonormal-frame trace identity -/

set_option linter.unusedSectionVars false in
/-- **Intrinsic orthonormal-frame trace identity for the DeTurck vector field.**  For any
`g₁`-orthonormal frame `{B i}` at `x`, the DeTurck vector field collapses to the plain frame sum of
the connection difference:
`deTurckVF g₁ g_bg x = ∑ i, (connDiff g₁ g_bg x) (B i) (B i)`.

This is the chart-free reading of the chart-Gram-weighted trace `deTurckVF_apply_eq`: the trace is
the basis-independent `g₁`-cometric trace of `connDiff g₁ g_bg`, computed in the `g₁`-orthonormal
frame where the inverse Gram is the identity — supplied by the frame-trace identity
`orthonormal_basis_bilin_trace_chartα` together with `chartBasisVecFiber_self`. -/
private theorem deTurckVF_eq_sum_orthonormalBasis
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (Bvec : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ (i j : Fin (Module.finrank ℝ E)),
      g₁.inner x (Bvec i) (Bvec j) = if i = j then 1 else 0) :
    (deTurckVF (I := I) g₁ g_bg : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      ∑ i, connDiff (I := I) g₁ g_bg x (Bvec i) (Bvec i) := by
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have htrace := Integral.Connection.orthonormal_basis_bilin_trace_chartα (I := I) (M := M)
    (A := TangentSpace I x) g₁ x (b := x) hx (connDiff (I := I) g₁ g_bg x) Bvec hB
  rw [htrace, deTurckVF_apply_eq (I := I) g₁ g_bg x]

/-! ### The intrinsic family-uniform value bound -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **The family-uniform `g₀`-fibre value sup of the DeTurck vector field.**  For the fibre-small
(`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`) supercritically `H^{a+2}`-bounded
(`2a > finrank + 4`) realized perturbation family, the `g₀`-fibre norm of the DeTurck vector field
`W₁ = deTurckVF g₁ g_bg` of every realized member is bounded by a single constant `Λ_W ≥ 0` over the
manifold and the family: `√(g₀ x (W₁ x) (W₁ x)) ≤ Λ_W`.

Proof: with a `g₁`-orthonormal frame `{B i}` at `x` (`tangent_orthonormalBasis_witness g₁ x`),
`W₁ x = ∑_i (connDiff g₁ g_bg x)(B_i, B_i)` (`deTurckVF_eq_sum_orthonormalBasis`).  Each summand is
bounded in `g₀`-norm by `(Λ_C + Λ_bg) · g₀(B_i, B_i)` (the variable part
`connDiff_g1g0_gOp_value_le` plus the fixed part `connDiff_g0gbg_gOp_value_le`, after the metric
additivity `connDiff g₁ g_bg = connDiff g₁ g₀ + connDiff g₀ g_bg`).  The `g₁`-orthonormal vectors
have `g₀(B_i, B_i) ≤ 1/(1−δ)` (the lower Neumann comparison `perturbedInner_self_lower_bound` against
`g₁ = g₀ + h`), so the `finrank`-term triangle inequality gives the family-uniform bound
`Λ_W = finrank · (Λ_C + Λ_bg) / (1 − δ)`.

Non-vacuity: `Λ_W = 0` forces `W₁ ≡ 0`, false whenever `deTurckVF g₁ g_bg ≠ 0`; at `g₁ = g_bg`
realized the field is the zero section (`deTurckVF_self`). -/
theorem exists_deTurckVF_gNorm_sup_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Λ_W : ℝ, 0 ≤ Λ_W ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ∀ x : M,
          Real.sqrt (g₀.inner x (deTurckVF (I := I) g₁ g_bg x) (deTurckVF (I := I) g₁ g_bg x)) ≤
            Λ_W := by
  classical
  obtain ⟨Λ_C, hC0, hC⟩ := connDiff_g1g0_gOp_value_le (I := I) (M := M) g₀ δ hδ0 hδ1 B a ha
  obtain ⟨Λ_bg, hbg0, hbg⟩ := connDiff_g0gbg_gOp_value_le (I := I) (M := M) g₀ g_bg
  have hδlt1 : δ < 1 := by linarith
  have h1δpos : 0 < 1 - δ := by linarith
  set n : ℕ := Module.finrank ℝ E with hn_def
  refine ⟨(n : ℝ) * (Λ_C + Λ_bg) / (1 - δ), by positivity,
    fun T₁ g₁ hg₁ hδbnd hB x => ?_⟩
  -- A `g₁`-orthonormal frame at `x`.
  obtain ⟨m, e, _bse, hm, _hbse, horth, _hpars, _hexpand, _hrepr⟩ :=
    Integral.Connection.tangent_orthonormalBasis_witness (I := I) (M := M) g₁ x
  -- Re-index the frame onto `Fin (finrank E)` (`finrank (TangentSpace I x) = finrank E` by `rfl`).
  have hmn : m = Module.finrank ℝ E := hm
  subst hmn
  set Bvec : Fin (Module.finrank ℝ E) → TangentSpace I x := e with hBvec
  have hBorth : ∀ (i j : Fin (Module.finrank ℝ E)),
      g₁.inner x (Bvec i) (Bvec j) = if i = j then 1 else 0 := horth
  -- The DeTurck field as the plain `g₁`-orthonormal frame sum.
  have hW : (deTurckVF (I := I) g₁ g_bg : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      ∑ i, connDiff (I := I) g₁ g_bg x (Bvec i) (Bvec i) :=
    deTurckVF_eq_sum_orthonormalBasis (I := I) g₁ g_bg x Bvec hBorth
  -- The metric additivity `connDiff g₁ g_bg = connDiff g₁ g₀ + connDiff g₀ g_bg`.
  have hadd : ∀ i, connDiff (I := I) g₁ g_bg x (Bvec i) (Bvec i) =
      connDiff (I := I) g₁ g₀ x (Bvec i) (Bvec i) +
        connDiff (I := I) g₀ g_bg x (Bvec i) (Bvec i) :=
    fun i => connDiff_eval_add (I := I) g₁ g₀ g_bg x (Bvec i)
  -- The `g₀`-quadratic of each `g₁`-orthonormal frame vector is ≤ `1/(1-δ)`.
  have hg0bound : ∀ i, g₀.inner x (Bvec i) (Bvec i) ≤ 1 / (1 - δ) := by
    intro i
    have hlb := perturbedInner_self_lower_bound (I := I) (M := M) g₀
      (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) hδbnd x (Bvec i)
    have hpe : perturbedInner (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) x
        (Bvec i) (Bvec i) = g₁.inner x (Bvec i) (Bvec i) := by
      rw [perturbedInner_apply]; rw [hg₁ x (Bvec i) (Bvec i)]
    have hone : g₁.inner x (Bvec i) (Bvec i) = 1 := by rw [hBorth i i]; simp
    rw [hpe, hone] at hlb
    rw [le_div_iff₀ h1δpos]; linarith
  have hg0nn : ∀ i, 0 ≤ g₀.inner x (Bvec i) (Bvec i) := fun i =>
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x (Bvec i)
  -- Per-summand `g₀`-norm bound: `√(g₀ (A B_i B_i)²) ≤ (Λ_C + Λ_bg) / (1 - δ)`.
  have hsummand : ∀ i, Real.sqrt (g₀.inner x
        (connDiff (I := I) g₁ g_bg x (Bvec i) (Bvec i))
        (connDiff (I := I) g₁ g_bg x (Bvec i) (Bvec i))) ≤ (Λ_C + Λ_bg) / (1 - δ) := by
    intro i
    set zC : TangentSpace I x := connDiff (I := I) g₁ g₀ x (Bvec i) (Bvec i) with hzC
    set zB : TangentSpace I x := connDiff (I := I) g₀ g_bg x (Bvec i) (Bvec i) with hzB
    have hsum_eq : connDiff (I := I) g₁ g_bg x (Bvec i) (Bvec i) = zC + zB := hadd i
    -- Triangle inequality for the `g₀`-norm.
    have htri : Real.sqrt (g₀.inner x (zC + zB) (zC + zB)) ≤
        Real.sqrt (g₀.inner x zC zC) + Real.sqrt (g₀.inner x zB zB) :=
      sqrt_gInner_add_le (I := I) (M := M) g₀ x zC zB
    rw [hsum_eq]
    refine le_trans htri ?_
    -- Bound each piece by `Λ · g₀(B_i, B_i) ≤ Λ · 1/(1-δ)`.
    have hCx := hC T₁ g₁ hg₁ hδbnd hB x (Bvec i) (Bvec i)
    have hBx := hbg x (Bvec i) (Bvec i)
    set s := Real.sqrt (g₀.inner x (Bvec i) (Bvec i)) with hs
    have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
    have hssq : s * s = g₀.inner x (Bvec i) (Bvec i) := Real.mul_self_sqrt (hg0nn i)
    -- `√(g₀ zC zC) ≤ Λ_C · s²`, `√(g₀ zB zB) ≤ Λ_bg · s²`, and `s² ≤ 1/(1-δ)`.
    have hzCle : Real.sqrt (g₀.inner x zC zC) ≤ Λ_C * (g₀.inner x (Bvec i) (Bvec i)) := by
      have hCx' : Real.sqrt (g₀.inner x zC zC) ≤ Λ_C * (s * s) := by
        rw [hzC]; rw [mul_assoc] at hCx; exact hCx
      rwa [hssq] at hCx'
    have hzBle : Real.sqrt (g₀.inner x zB zB) ≤ Λ_bg * (g₀.inner x (Bvec i) (Bvec i)) := by
      have hBx' : Real.sqrt (g₀.inner x zB zB) ≤ Λ_bg * (s * s) := by
        rw [hzB]; rw [mul_assoc] at hBx; exact hBx
      rwa [hssq] at hBx'
    have hsumle : Real.sqrt (g₀.inner x zC zC) + Real.sqrt (g₀.inner x zB zB) ≤
        (Λ_C + Λ_bg) * (g₀.inner x (Bvec i) (Bvec i)) := by nlinarith [hzCle, hzBle]
    refine le_trans hsumle ?_
    rw [div_eq_mul_inv]
    have hΛnn : 0 ≤ Λ_C + Λ_bg := by linarith
    have : (Λ_C + Λ_bg) * (g₀.inner x (Bvec i) (Bvec i)) ≤ (Λ_C + Λ_bg) * (1 / (1 - δ)) :=
      mul_le_mul_of_nonneg_left (hg0bound i) hΛnn
    rw [one_div] at this; linarith
  -- Assemble the `finrank`-term triangle inequality on the frame sum.
  have hWnorm : Real.sqrt (g₀.inner x
        (deTurckVF (I := I) g₁ g_bg x) (deTurckVF (I := I) g₁ g_bg x)) ≤
      ∑ i, Real.sqrt (g₀.inner x
        (connDiff (I := I) g₁ g_bg x (Bvec i) (Bvec i))
        (connDiff (I := I) g₁ g_bg x (Bvec i) (Bvec i))) := by
    rw [hW]
    exact sqrt_gInner_self_sum_le_sum_sqrt (I := I) (M := M) g₀ x Finset.univ
      (fun i => connDiff (I := I) g₁ g_bg x (Bvec i) (Bvec i))
  refine le_trans hWnorm ?_
  calc ∑ i, Real.sqrt (g₀.inner x
          (connDiff (I := I) g₁ g_bg x (Bvec i) (Bvec i))
          (connDiff (I := I) g₁ g_bg x (Bvec i) (Bvec i)))
      ≤ ∑ _i : Fin (Module.finrank ℝ E), (Λ_C + Λ_bg) / (1 - δ) :=
        Finset.sum_le_sum (fun i _ => hsummand i)
    _ = (Module.finrank ℝ E : ℝ) * ((Λ_C + Λ_bg) / (1 - δ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (n : ℝ) * (Λ_C + Λ_bg) / (1 - δ) := by rw [hn_def]; ring

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry
