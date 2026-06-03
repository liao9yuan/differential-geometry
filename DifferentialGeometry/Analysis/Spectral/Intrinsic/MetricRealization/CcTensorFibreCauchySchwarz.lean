import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.RiemannianFiberNormSqRiemannOpHigherRankParseval

/-! # Intrinsic `g`-fibre Cauchy–Schwarz for the extracted bilinear form

For a smooth `(0, 2)`-tensor section `T` on a closed Riemannian manifold `(M, g)`,
the extracted bilinear form `ccTensorBilin g T x` (the fibre identification of the
`(0, 2)`-tensor value `T(x)` as a bilinear map `TₓM × TₓM → ℝ`) satisfies the
intrinsic fibre Cauchy–Schwarz inequality

`(ccTensorBilin g T x v w)² ≤ g(v, v) · g(w, w) · ‖T(x)‖²_g`,

where `‖T(x)‖²_g = riemannianFiberNormSq g 0 2 x (T.toSection x)` is the Riemannian
fibre norm squared. This is the `0`-jet fibre estimate underlying the pointwise
Sobolev control of realized metric perturbations: it bounds the pointwise bilinear
evaluation of a smooth tensor by its Riemannian fibre norm (and hence, through the
fibre Sobolev embedding, by a supercritical spectral norm).

The proof expands `v, w` in a `g`-orthonormal tangent frame, applies the bilinearity
of `ccTensorBilin` and Cauchy–Schwarz over the frame-pair index, and Parseval
`∑_i (g x (e i) v)² = g x v v`, identifying the frame-pair square-sum with the
Riemannian fibre norm squared through `fiberNormSqSummand_eq_component_sq`. -/

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The frame component `fiberNormSqComponent g x 0 2 (T.toSection x) n e K₀ J`
(`K₀ : Fin 0 → Fin n` the unique empty multi-index) equals the extracted bilinear
form `ccTensorBilin g T` evaluated on the frame vectors `(e (J 0), e (J 1))`: both
apply the same model `(0,2)`-fibre value of `T` to the same `2`-tuple. -/
theorem ccTensorBilin_eq_fiberNormSqComponent
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (K₀ : Fin 0 → Fin n) (J : Fin 2 → Fin n) :
    Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x 0 2
        (T.toSection x) n e K₀ J =
      ccTensorBilin (I := I) g T x (e (J 0)) (e (J 1)) := by
  classical
  have hcoframe :
      Integral.Connection.coframeS (I := I) (M := M) g x 0 e K₀ =
        ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := by
    apply Tensor0SBundle.tensor0SSpace_ext
    intro v
    rw [Integral.Connection.coframeS_apply]
    rw [Finset.prod_of_isEmpty _]
    rfl
  rw [ccTensorBilin_apply, ccTensorModel, ccTensorMultilinear_apply]
  unfold Integral.Connection.fiberNormSqComponent
  rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K₀ k))) : Tensor0SBundle.Tensor0SSpace 0 I x) =
      Integral.Connection.coframeS (I := I) (M := M) g x 0 e K₀ from rfl, hcoframe]
  change ((T.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) (fun k : Fin 2 => e (J k)) : ℝ) =
    Tensor0SBundle.Tensor0SSpace.toModel
      (T.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
      ![e (J 0), e (J 1)]
  rw [Tensor0SBundle.Tensor0SSpace.toModel,
    Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply]
  congr 1
  funext k
  fin_cases k <;> rfl

/-- **Intrinsic `g`-fibre Cauchy–Schwarz for the extracted bilinear form.** For a
smooth `(0,2)`-tensor section `T`, the squared value of the extracted bilinear form
`ccTensorBilin g T x v w` is bounded by the product of the intrinsic quadratic factors
`g x v v`, `g x w w` and the intrinsic Riemannian fibre norm squared
`riemannianFiberNormSq g 0 2 x (T.toSection x)`.  Proved by expanding `v, w` in a
`g`-orthonormal tangent frame, applying the bilinearity of `ccTensorBilin` and
Cauchy–Schwarz over the frame-pair index, and Parseval `∑_i (g x (e i) v)² = g x v v`. -/
theorem ccTensorBilin_sq_le_gInner_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) (x : M)
    (v w : TangentSpace I x) :
    (ccTensorBilin (I := I) g T x v w) ^ 2 ≤
      g.inner x v v * g.inner x w w *
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (T.toSection x) := by
  classical
  obtain ⟨n, e, hn, horth, hpars, hexpand, hrepr⟩ :=
    Integral.Connection.tangent_frame_expansion (I := I) (M := M) g x
  set B : ℝ := ccTensorBilin (I := I) g T x v w with hB_def
  set a : Fin n × Fin n → ℝ := fun p =>
    ccTensorBilin (I := I) g T x (e p.1) (e p.2) with ha_def
  set c : Fin n × Fin n → ℝ := fun p =>
    g.inner x (e p.1) v * g.inner x (e p.2) w with hc_def
  have hexp_double : B =
      ∑ i : Fin n, ∑ j : Fin n,
        (g.inner x (e i) v * g.inner x (e j) w) *
          ccTensorBilin (I := I) g T x (e i) (e j) := by
    have hv : v = ∑ i : Fin n, g.inner x (e i) v • e i := hexpand v
    have hw : w = ∑ j : Fin n, g.inner x (e j) w • e j := hexpand w
    rw [hB_def]
    conv_lhs => rw [hv]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply]
    conv_lhs => rw [hw]
    rw [map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  have hexp : B = ∑ p : Fin n × Fin n, c p * a p := by
    rw [hexp_double, Fintype.sum_prod_type
      (f := fun p : Fin n × Fin n => c p * a p)]
  have hCS : (∑ p : Fin n × Fin n, c p * a p) ^ 2 ≤
      (∑ p : Fin n × Fin n, c p ^ 2) * ∑ p : Fin n × Fin n, a p ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c a
  have hcsq : (∑ p : Fin n × Fin n, c p ^ 2) = g.inner x v v * g.inner x w w := by
    have hsplit : (∑ p : Fin n × Fin n, c p ^ 2) =
        (∑ i : Fin n, g.inner x (e i) v ^ 2) *
          ∑ j : Fin n, g.inner x (e j) w ^ 2 := by
      rw [Finset.sum_mul_sum]
      rw [Fintype.sum_prod_type (f := fun p : Fin n × Fin n => c p ^ 2)]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hc_def]; ring
    rw [hsplit, hpars v, hpars w]
  have hasq : (∑ p : Fin n × Fin n, a p ^ 2) =
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        (T.toSection x) := by
    rw [hrepr (T.toSection x)]
    rw [Fintype.sum_subsingleton
      (fun K : Fin 0 → Fin n => ∑ J : Fin 2 → Fin n,
        Integral.Connection.fiberNormSqSummand (I := I) (M := M) g x 0 2
          (T.toSection x) n e K J)
      (fun k : Fin 0 => k.elim0)]
    refine (Fintype.sum_equiv (finTwoArrowEquiv (Fin n)) _ _ ?_).symm
    intro J
    rw [Integral.Connection.fiberNormSqSummand_eq_component_sq,
      ccTensorBilin_eq_fiberNormSqComponent (I := I) g T x e
        (fun k : Fin 0 => k.elim0) J]
    rw [ha_def]
    rfl
  rw [hexp]
  refine hCS.trans ?_
  rw [hcsq, hasq]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
