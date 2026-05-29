import DifferentialGeometry.Integral.Connection.RiemannianFiberNormSqRiemannOpVWFactorBound
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Tensor-frame Parseval bound for the tensor curvature operator's fibre norm

This file completes the `T`-independent (and hence uniform) absorbing constant for the
bundled tensor curvature operator `riemannOp (tensorCov g 0 2) x`, building on the
`(v, w)`-factorisation already established in
`RiemannianFiberNormSqRiemannOpVWFactorBound.lean`.

Stage 1 (the `(v, w)`-factorisation) gives, for a `g`-orthonormal tangent frame `e` at
`x`,
```
riemannianFiberNormSq g 0 2 x (R_x(v, w) T)
  ≤ (g.inner x v v) · (g.inner x w w) · ∑_{i, j} riemannianFiberNormSq g 0 2 x (R_x(e_i, e_j) T).
```
The residual sum `∑_{i, j} riemannianFiberNormSq g 0 2 x (R_x(e_i, e_j) T)` is still
linear-squared in the tensor `T`. This file removes that dependence by a Parseval
argument in a `g`-orthonormal *tensor* frame.

## The dual tensor frame

For the `g`-orthonormal tangent frame `e` and a pair of indices `(a, b)`, the dual
tensor frame element `dualTensorFrame g x e a b : TensorRSSpace 0 2 I x` is the
continuous linear map sending the `(0, 0)`-tensor argument `τ` to `τ(⋆) • (ω^a ⊗ ω^b)`,
where `ω^c := v ↦ g.inner x (e c) v` is the `g`-orthonormal coframe and `τ(⋆)` is the
scalar value of the `(0, 0)`-tensor. Its defining property is the Kronecker identity
```
fiberNormSqComponent g x 0 2 (dualTensorFrame g x e a b) n e K (![c, d]) = δ_{ac} δ_{bd},
```
which holds because the empty-index covector `ω^K` evaluates to `1` and the
`g`-orthonormality of `e` collapses the coframe pairing to a Kronecker delta.

## Parseval expansion and the `C_x`-form bound

Through `Module.Basis.ext_multilinear` (lifted across the
`Tensor0SSpace 0 →L Tensor0SSpace 2` coercion) the dual tensor frame spans the fibre:
```
T = ∑_{a, b} (fiberNormSqComponent g x 0 2 T n e (![]) (![a, b])) • dualTensorFrame g x e a b.
```
Parseval reads
```
riemannianFiberNormSq g 0 2 x T = ∑_{a, b} (fiberNormSqComponent g x 0 2 T n e (![]) (![a, b]))².
```
A Cauchy–Schwarz over the `(a, b)`-index then yields the `T`-independent per-point bound
```
∑_{i, j} riemannianFiberNormSq g 0 2 x (R_x(e_i, e_j) T)
  ≤ C_x · riemannianFiberNormSq g 0 2 x T,
  C_x = ∑_{i, j, a, b} riemannianFiberNormSq g 0 2 x (R_x(e_i, e_j) (dualTensorFrame g x e a b)).
```
Composed with the Stage 1 factorisation this is the `(v, w, T)`-uniform per-point bound
```
riemannianFiberNormSq g 0 2 x (R_x(v, w) T)
  ≤ C_x · (g.inner x v v) · (g.inner x w w) · riemannianFiberNormSq g 0 2 x T.
```

## Main results

* `dualTensorFrame` — the `g`-orthonormal dual tensor frame element.
* `fiberNormSqComponent_dualTensorFrame` — the Kronecker identity for its frame
  components.
* `tensor_dualFrame_expansion` — the multilinear expansion of an arbitrary `(0, 2)`-tensor
  in the dual tensor frame.
* `riemannianFiberNormSq_eq_sum_component_sq` — Parseval in the dual tensor frame.
* `sum_riemannianFiberNormSq_riemannOp_le_Cx` — the `T`-independent per-point bound.
* `riemannianFiberNormSq_riemannOp_tensorCov_vwT_factor_le` — the combined
  `(v, w, T)`-uniform per-point bound.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-! ## The scalar-extraction continuous linear functional on `(0, 0)`-tensors

The fibre `Tensor0SSpace 0 I x` is the space of continuous multilinear maps from the
empty family of tangent vectors to `ℝ`; each element is determined by its value on the
unique empty tuple. The continuous linear functional `tensor00Scalar x` extracts this
value, composing `Tensor0SSpace.toModelL 0 x` (bridging the bundle/norm topologies) with
`continuousMultilinearCurryFin0`. -/

/-- The scalar-extraction functional on the `(0, 0)`-tensor fibre: `τ ↦ τ(⋆)`. -/
noncomputable def tensor00Scalar (x : M) :
    Tensor0SSpace 0 I x →L[ℝ] ℝ :=
  (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.comp
    (Tensor0SSpace.toModelL (I := I) 0 x)

lemma tensor00Scalar_apply (x : M) (τ : Tensor0SSpace 0 I x)
    (m : Fin 0 → TangentSpace I x) :
    tensor00Scalar (I := I) (M := M) x τ = τ m := by
  unfold tensor00Scalar
  rw [ContinuousLinearMap.comp_apply]
  -- `toModelL 0 x τ = τ` on the carrier, then `continuousMultilinearCurryFin0` evaluates.
  have h1 : (Tensor0SSpace.toModelL (I := I) 0 x) τ = Tensor0SSpace.toModel τ := rfl
  rw [h1]
  change (continuousMultilinearCurryFin0 ℝ E ℝ) (Tensor0SSpace.toModel τ) = _
  rw [continuousMultilinearCurryFin0_apply]
  -- `toModel τ 0 = τ 0 = τ m`, the last step by `Subsingleton` of the empty tuple type.
  change τ (0 : Fin 0 → TangentSpace I x) = τ m
  congr 1
  exact Subsingleton.elim _ _

/-! ## The `g`-orthonormal coframe covector and the dual tensor frame

For a `g`-orthonormal tangent frame `e` and a pair of indices `(a, b)`, the rank-`2`
coframe covector `coframe2 g x e a b` is the `(0, 2)`-tensor
`(u, v) ↦ g.inner x (e a) u · g.inner x (e b) v`, built (exactly as the `ω^J` covectors
in `fiberNormSqComponent`) from `mkPiAlgebra` over `Fin 2` composed with the two coframe
linear functionals. -/

/-- The rank-`2` `g`-orthonormal coframe covector `ω^a ⊗ ω^b` as a `(0, 2)`-tensor. -/
noncomputable def coframe2
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (a b : Fin n) :
    Tensor0SSpace 2 I x :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
    (fun k : Fin 2 => g.inner x (e ((![a, b] : Fin 2 → Fin n) k)))

lemma coframe2_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (a b : Fin n)
    (u : Fin 2 → TangentSpace I x) :
    coframe2 (I := I) (M := M) g x e a b u =
      g.inner x (e a) (u 0) * g.inner x (e b) (u 1) := by
  unfold coframe2
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  rw [Fin.prod_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The dual tensor frame element `F_{a, b}`: the continuous linear map sending the
`(0, 0)`-tensor `τ` to `τ(⋆) • (ω^a ⊗ ω^b)`. -/
noncomputable def dualTensorFrame
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (a b : Fin n) :
    TensorRSSpace 0 2 I x :=
  (tensor00Scalar (I := I) (M := M) x).smulRight
    (coframe2 (I := I) (M := M) g x e a b)

lemma dualTensorFrame_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (a b : Fin n)
    (τ : Tensor0SSpace 0 I x) :
    (dualTensorFrame (I := I) (M := M) g x e a b :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) τ =
      tensor00Scalar (I := I) (M := M) x τ • coframe2 (I := I) (M := M) g x e a b := by
  unfold dualTensorFrame
  rw [ContinuousLinearMap.smulRight_apply]

/-! ## The Kronecker identity for the dual tensor frame components

The empty-index covector `ω^K` used in `fiberNormSqComponent` (at `r = 0`) is the
`mkPiAlgebra`-product over the empty family, hence evaluates to `1` on every input. So the
dual tensor frame `F_{a, b}` applied to `ω^K` is `coframe2 g x e a b`, whose evaluation on
the frame pair `(e (J 0), e (J 1))` collapses, by `g`-orthonormality of `e`, to the
Kronecker product `δ_{a, J 0} δ_{b, J 1}`. -/

/-- **Kronecker identity for the dual tensor frame.** For a `g`-orthonormal tangent frame
`e`, the `(K, J)`-frame component of `dualTensorFrame g x e a b` equals
`δ_{a, J 0} · δ_{b, J 1}` (independent of `K`, which ranges over the singleton
`Fin 0 → Fin n`). -/
lemma fiberNormSqComponent_dualTensorFrame
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (a b : Fin n) (K : Fin 0 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 0 2
        (dualTensorFrame (I := I) (M := M) g x e a b) n e K J =
      (if a = J 0 then (1 : ℝ) else 0) * (if b = J 1 then (1 : ℝ) else 0) := by
  classical
  -- Unfold the frame component: it is `F_{a,b}(ω^K)(e_J)`.
  unfold fiberNormSqComponent
  -- `F_{a,b}(ω^K) = tensor00Scalar x (ω^K) • coframe2 g x e a b`.
  rw [show ((dualTensorFrame (I := I) (M := M) g x e a b :
          Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x)
          ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun k => g.inner x (e (K k))))) =
        tensor00Scalar (I := I) (M := M) x
            ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
              (fun k => g.inner x (e (K k)))) •
          coframe2 (I := I) (M := M) g x e a b from
      dualTensorFrame_apply (I := I) (M := M) g x e a b _]
  -- `tensor00Scalar x (ω^K) = ω^K(e_J) = ∏_{k:Fin 0} … = 1`.
  have hscalar : tensor00Scalar (I := I) (M := M) x
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K k)))) = 1 := by
    rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply]
    simp
  rw [hscalar, one_smul]
  -- Evaluate `coframe2` on the frame pair and apply `g`-orthonormality.
  rw [coframe2_apply (I := I) (M := M) g x e a b (fun k : Fin 2 => e (J k))]
  rw [horth a (J 0), horth b (J 1)]
/-! ## Expansion of a `(0, 2)` covariant tensor in the `g`-orthonormal coframe

A `(0, 2)` covariant tensor `A` (an element of `Tensor0SSpace 2 I x`) expands in the
`g`-orthonormal coframe basis as `A = ∑_{a, b} A(e_a, e_b) • (ω^a ⊗ ω^b)`. The proof uses
`Module.Basis.ext_multilinear`: both sides agree on every pair of basis vectors
`(e_c, e_d)` because `coframe2 g x e a b (e_c, e_d) = δ_{ac} δ_{bd}`. -/

/-- **Coframe expansion of a `(0, 2)` covariant tensor.** For a `g`-orthonormal frame `e`
arising from a `Module.Basis bse` (`bse i = e i`), every `(0, 2)` covariant tensor `A`
expands as `A = ∑_{a, b} A(e_a, e_b) • coframe2 g x e a b`. -/
lemma tensor02_coframe_expansion
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (A : Tensor0SSpace 2 I x) :
    A = ∑ a : Fin n, ∑ b : Fin n,
      (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) •
        coframe2 (I := I) (M := M) g x e a b := by
  classical
  -- Both sides are `(0, 2)` tensors; prove equality of the underlying multilinear maps
  -- via `Module.Basis.ext_multilinear`, then transport back through `tensor0SSpace_ext`.
  apply tensor0SSpace_ext (𝕜 := ℝ) 2 x
  intro u
  -- The underlying continuous multilinear maps (these coercions are `rfl`-level).
  let Acmm : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ := A
  let Rcmm : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ :=
    ∑ a : Fin n, ∑ b : Fin n,
      (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) •
        coframe2 (I := I) (M := M) g x e a b
  -- It suffices to prove `Acmm = Rcmm` as multilinear maps; evaluate at `u`.
  suffices h : Acmm.toMultilinearMap = Rcmm.toMultilinearMap by
    exact congrArg
      (fun (T : MultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ) => T u) h
  refine Module.Basis.ext_multilinear (e := fun _ : Fin 2 => bse) ?_
  intro v
  -- `v : Fin 2 → Fin n`; the basis tuple is `(e (v 0), e (v 1))`.
  have hbtuple : (fun i : Fin 2 => bse (v i)) = (fun i : Fin 2 => e (v i)) := by
    funext i; rw [hbse (v i)]
  -- Reduce the multilinear-map evaluations to the continuous-multilinear-map ones.
  change Acmm (fun i : Fin 2 => bse (v i)) = Rcmm (fun i : Fin 2 => bse (v i))
  rw [hbtuple]
  -- Evaluate the RHS finite sum at the basis tuple summand-wise.
  have hRHS_eval : Rcmm (fun i : Fin 2 => e (v i)) =
      ∑ a : Fin n, ∑ b : Fin n,
        (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) *
          coframe2 (I := I) (M := M) g x e a b (fun i : Fin 2 => e (v i)) := by
    change (∑ a : Fin n, ∑ b : Fin n,
          (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) •
            coframe2 (I := I) (M := M) g x e a b)
        (fun i : Fin 2 => e (v i)) = _
    rw [ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  change Acmm (fun i : Fin 2 => e (v i)) = _
  rw [hRHS_eval]
  -- `coframe2 g x e a b (e (v 0), e (v 1)) = δ_{a, v 0} δ_{b, v 1}`.
  have hcoframe : ∀ a b : Fin n,
      coframe2 (I := I) (M := M) g x e a b (fun i : Fin 2 => e (v i)) =
        (if a = v 0 then (1 : ℝ) else 0) * (if b = v 1 then (1 : ℝ) else 0) := by
    intro a b
    rw [coframe2_apply (I := I) (M := M) g x e a b (fun i : Fin 2 => e (v i))]
    rw [horth a (v 0), horth b (v 1)]
  -- Rewrite each summand's `coframe2` factor via the Kronecker identity.
  rw [show (∑ a : Fin n, ∑ b : Fin n,
        (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) *
          coframe2 (I := I) (M := M) g x e a b (fun i : Fin 2 => e (v i))) =
      ∑ a : Fin n, ∑ b : Fin n,
        (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) *
          ((if a = v 0 then (1 : ℝ) else 0) * (if b = v 1 then (1 : ℝ) else 0)) from by
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hcoframe a b]]
  -- Collapse the double sum to the single surviving term `(a, b) = (v 0, v 1)`.
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single (v 1)]
  · rw [Finset.sum_eq_single (v 0)]
    · simp only [if_pos, mul_one]
      congr 1
      funext k
      fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    · intro a _ ha
      rw [if_neg ha, zero_mul, mul_zero]
    · intro h; exact absurd (Finset.mem_univ (v 0)) h
  · intro b _ hb
    refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [if_neg hb, mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ (v 1)) h

/-! ## The `g`-orthonormal frame witness with an explicit `Module.Basis`

A strengthened version of `tangent_frame_expansion` that additionally exposes the
underlying `Module.Basis` of the `g`-orthonormal frame. This is the witness used to feed
`tensor02_coframe_expansion`. -/

/-- **`g`-orthonormal frame witness with `Module.Basis`.** There is a frame
`e : Fin n → TangentSpace I x` arising from a `Module.Basis bse` (`bse i = e i`), with
`n = Module.finrank ℝ (TangentSpace I x)`, that is `g`-orthonormal, satisfies Parseval and
the frame expansion of tangent vectors, and represents `riemannianFiberNormSq` (at
`(0, 2)`) as the frame double sum. -/
lemma tangent_orthonormalBasis_witness
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x)
      (bse : Module.Basis (Fin n) ℝ (TangentSpace I x)),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i : Fin n, bse i = e i) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      (∀ v : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) v ^ 2 = g.inner x v v) ∧
      (∀ v : TangentSpace I x, v = ∑ i : Fin n, g.inner x (e i) v • e i) ∧
      ∀ S : TensorRSSpace 0 2 I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x S =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
            fiberNormSqSummand (I := I) (M := M) g x 0 2 S n e K J := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set eob : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _
    with heob_def
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  refine ⟨n, fun i => eob i, eob.toBasis, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · -- `bse i = e i`.
    intro i
    rw [OrthonormalBasis.coe_toBasis]
  · -- `g`-orthonormality.
    intro i j
    have horth : Orthonormal ℝ (fun i : Fin n => eob i) := eob.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I x)).mp horth i j
    rw [← hinner_eq (eob i) (eob j)]
    exact hite
  · -- Parseval.
    intro v
    have hpars : ∑ i : Fin n, (inner ℝ (eob i) v : ℝ) ^ 2 = ‖v‖ ^ 2 :=
      OrthonormalBasis.sum_sq_inner_right eob v
    have hnorm_sq : (‖v‖ : ℝ) ^ 2 = g.inner x v v := by
      have hri : (inner ℝ v v : ℝ) = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      rw [hinner_eq v v] at hri
      exact hri.symm
    calc
      ∑ i : Fin n, g.inner x (eob i) v ^ 2
          = ∑ i : Fin n, (inner ℝ (eob i) v : ℝ) ^ 2 := by
            refine Finset.sum_congr rfl (fun i _ => ?_); rw [hinner_eq (eob i) v]
      _ = ‖v‖ ^ 2 := hpars
      _ = g.inner x v v := hnorm_sq
  · -- Frame expansion.
    intro v
    have hrepr : ∑ i : Fin n, (inner ℝ (eob i) v : ℝ) • eob i = v :=
      OrthonormalBasis.sum_repr' eob v
    have hcongr : (∑ i : Fin n, g.inner x (eob i) v • eob i) =
        ∑ i : Fin n, (inner ℝ (eob i) v : ℝ) • eob i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hinner_eq (eob i) v]
    rw [hcongr, hrepr]
  · -- The double-sum representation of `riemannianFiberNormSq`.
    intro S
    rfl

/-! ## Parseval in the dual tensor frame and the `T`-independent per-point bound

Combining the coframe expansion `tensor02_coframe_expansion`, the dual-tensor-frame
expansion, Parseval, and a Cauchy–Schwarz over the `(a, b)`-index gives the
`T`-independent per-point bound
```
∑_{i, j} riemannianFiberNormSq g 0 2 x (R_x(e_i, e_j) T) ≤ C_x · riemannianFiberNormSq g 0 2 x T.
```
-/

/-- **Dual-tensor-frame expansion of a `(0, 2)`-tensor.** For the `g`-orthonormal frame
`e` (with basis `bse`), every `(0, 2)`-tensor `T` expands as
`T = ∑_{a, b} (T-component_{a, b}) • dualTensorFrame g x e a b`, where the components are
the `fiberNormSqComponent`s at the empty covector index. -/
lemma tensor_dualFrame_expansion
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (T : TensorRSSpace 0 2 I x) (K₀ : Fin 0 → Fin n) :
    T = ∑ a : Fin n, ∑ b : Fin n,
      (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) •
        dualTensorFrame (I := I) (M := M) g x e a b := by
  classical
  -- `T` is a continuous linear map `Tensor0SSpace 0 → Tensor0SSpace 2`; prove the
  -- equality by extensionality on the `(0, 0)`-tensor argument `τ`.
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 2 x
  intro τ
  -- Abbreviate the scalar value of `τ`.
  set c : ℝ := tensor00Scalar (I := I) (M := M) x τ with hc_def
  -- LHS: `T τ`. Since `τ = c • ω^{K₀}` as `(0, 0)`-tensors, `T τ = c • T ω^{K₀}`.
  -- Here `ω^{K₀}` is the empty covector used in `fiberNormSqComponent`.
  set ωK : Tensor0SSpace 0 I x :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
      (fun k => g.inner x (e (K₀ k))) with hωK_def
  -- `τ = c • ωK` as `(0, 0)`-tensors (both are scalars times the unit).
  have hτ : τ = c • ωK := by
    apply tensor0SSpace_ext (𝕜 := ℝ) 0 x
    intro m
    rw [hc_def, tensor00Scalar_apply (I := I) (M := M) x τ m]
    -- `(c • ωK) m = c * (ωK m)`, and `ωK m = 1`.
    rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hωK1 : ωK m = 1 := by
      rw [hωK_def, ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiAlgebra_apply]
      simp
    rw [hωK1, mul_one]
  -- LHS reduces to `c • (T ωK)`.
  have hLHS : (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) τ =
      c • (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) ωK := by
    rw [hτ, ContinuousLinearMap.map_smul]
  -- The `(0, 2)`-tensor `T ωK` expands in the coframe.
  set A : Tensor0SSpace 2 I x :=
    (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) ωK with hA_def
  have hA_expand : A = ∑ a : Fin n, ∑ b : Fin n,
      (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) •
        coframe2 (I := I) (M := M) g x e a b :=
    tensor02_coframe_expansion (I := I) (M := M) g x e bse hbse horth A
  -- The `A`-evaluation equals the `fiberNormSqComponent` of `T`.
  have hAeval : ∀ a b : Fin n,
      A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k)) =
        fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b]) := by
    intro a b
    rw [hA_def]
    rfl
  -- Goal: `T τ = (∑_a ∑_b comp_{a,b} • dualTensorFrame_{a,b}) τ`.
  -- Compute both sides into the common double-sum `∑_a ∑_b comp_{a,b} • (c • coframe2_{a,b})`.
  -- LHS:
  have hLHS' : (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) τ =
      ∑ a : Fin n, ∑ b : Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) •
          (c • coframe2 (I := I) (M := M) g x e a b) := by
    rw [hLHS, hA_expand, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hAeval a b, smul_comm]
  -- RHS:
  have hRHS' : (∑ a : Fin n, ∑ b : Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) •
          dualTensorFrame (I := I) (M := M) g x e a b :
            Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) τ =
      ∑ a : Fin n, ∑ b : Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) •
          (c • coframe2 (I := I) (M := M) g x e a b) := by
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [ContinuousLinearMap.smul_apply,
      dualTensorFrame_apply (I := I) (M := M) g x e a b τ, ← hc_def]
  rw [hLHS', hRHS']

/-- **Parseval in the dual tensor frame.** For the `g`-orthonormal frame `e`, the intrinsic
fibre norm squared is the sum of squared dual-tensor-frame components:
`riemannianFiberNormSq g 0 2 x T = ∑_{a, b} (fiberNormSqComponent g x 0 2 T n e K₀ ![a, b])²`. -/
lemma riemannianFiberNormSq_eq_sum_component_sq
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hrepr : ∀ S : TensorRSSpace 0 2 I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2 S n e K J)
    (T : TensorRSSpace 0 2 I x) (K₀ : Fin 0 → Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x T =
      ∑ a : Fin n, ∑ b : Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) ^ 2 := by
  classical
  rw [hrepr T]
  -- The covector index `K : Fin 0 → Fin n` is the unique empty function `K₀`.
  rw [Finset.sum_eq_single K₀]
  · -- Reindex the `J : Fin 2 → Fin n` sum to a double sum over `(a, b)`.
    -- `fiberNormSqSummand = (fiberNormSqComponent)²`, and `J ↦ (J 0, J 1)` is a bijection
    -- with inverse `(a, b) ↦ ![a, b]`.
    rw [show (∑ J : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2 T n e K₀ J) =
        ∑ J : Fin 2 → Fin n,
          (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ J) ^ 2 from by
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [fiberNormSqSummand_eq_component_sq]]
    -- Sum over `Fin 2 → Fin n` via the product reindexing.
    rw [← Fintype.sum_prod_type'
      (f := fun a b => (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) ^ 2)]
    -- `∑_{J : Fin 2 → Fin n} comp(J)² = ∑_{p : Fin n × Fin n} comp(![p.1, p.2])²` via the
    -- equiv `(Fin 2 → Fin n) ≃ Fin n × Fin n`.
    rw [← Equiv.sum_comp (finTwoArrowEquiv (Fin n)).symm
      (fun J : Fin 2 → Fin n =>
        (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ J) ^ 2)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    -- `(finTwoArrowEquiv (Fin n)).symm p = ![p.1, p.2]`.
    rw [finTwoArrowEquiv_symm_apply]
  · intro K _ hK
    exact absurd (Subsingleton.elim K K₀) hK
  · intro h; exact absurd (Finset.mem_univ K₀) h

/-! ## The `T`-independent per-point bound

A Cauchy–Schwarz over the `(a, b)`-index, applied to the dual-tensor-frame expansion of
`T` carried through the curvature operator `R_x(e_i, e_j)`, gives the per-point bound. -/

/-- **`T`-independent per-point bound.** For the `g`-orthonormal frame `e` (with basis
`bse`), the frame-pair residual sum of the curvature acting on `T` is bounded by the
`T`-independent constant
`C_x := ∑_{i, j, a, b} riemannianFiberNormSq g 0 2 x (R_x(e_i, e_j) (dualTensorFrame …))`
times the intrinsic fibre norm squared of `T`:
```
∑_{i, j} riemannianFiberNormSq g 0 2 x (R_x(e_i, e_j) T)
  ≤ (∑_{i, j, a, b} riemannianFiberNormSq g 0 2 x (R_x(e_i, e_j) (dualTensorFrame g x e a b)))
    · riemannianFiberNormSq g 0 2 x T.
```
-/
lemma sum_riemannianFiberNormSq_riemannOp_le_Cx
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hrepr : ∀ S : TensorRSSpace 0 2 I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2 S n e K J)
    (T : TensorRSSpace 0 2 I x) :
    (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (riemannOp (tensorCov (I := I) g 0 2) x (e i) (e j) T)) ≤
      (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (riemannOp (tensorCov (I := I) g 0 2) x (e i) (e j)
              (dualTensorFrame (I := I) (M := M) g x e a b))) *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
  classical
  -- The empty covector index.
  let K₀ : Fin 0 → Fin n := fun k => k.elim0
  set R := riemannOp (tensorCov (I := I) g 0 2) x with hR_def
  -- Parseval gives `riemannianFiberNormSq T = ∑_{a,b} comp(T)²`.
  have hParseval := riemannianFiberNormSq_eq_sum_component_sq
    (I := I) (M := M) g x e hrepr T K₀
  -- The dual-frame expansion of `T`.
  have hTexp := tensor_dualFrame_expansion (I := I) (M := M) g x e bse hbse horth T K₀
  -- Abbreviate the `T`-components.
  set cT : Fin n × Fin n → ℝ :=
    fun p => fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![p.1, p.2]) with hcT
  -- Per-frame-pair: `riemannianFiberNormSq (R e_i e_j T) ≤ (∑_{a,b} comp²)·(∑_{a,b} rfns(R e_i e_j F_{a,b}))`.
  have hpair : ∀ i j : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T) ≤
        (∑ a : Fin n, ∑ b : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))) *
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
    intro i j
    -- Express `R e_i e_j T` through the dual-frame expansion of `T`.
    have hRT : R (e i) (e j) T =
        ∑ a : Fin n, ∑ b : Fin n,
          cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b) := by
      conv_lhs => rw [hTexp]
      -- `R e_i e_j` is a CLM applied to the tensor argument; distribute over the sum.
      rw [map_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [ContinuousLinearMap.map_smul]
    rw [hRT]
    -- Parseval of the LHS via the frame-component linear functional `L_{K,J}`.
    rw [hrepr (∑ a : Fin n, ∑ b : Fin n,
      cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))]
    -- Bound each `(K, J)` summand by Cauchy–Schwarz over `(a, b)`.
    have hterm : ∀ (Kx : Fin 0 → Fin n) (Jx : Fin 2 → Fin n),
        fiberNormSqSummand (I := I) (M := M) g x 0 2
            (∑ a : Fin n, ∑ b : Fin n,
              cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))
            n e Kx Jx ≤
          (∑ p : Fin n × Fin n, cT p ^ 2) *
            ∑ p : Fin n × Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 2
                (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2)) n e Kx Jx := by
      intro Kx Jx
      rw [fiberNormSqSummand_eq_component_sq]
      -- Component of the double sum: linear in the tensor argument.
      have hcomp :
          fiberNormSqComponent (I := I) (M := M) g x 0 2
              (∑ a : Fin n, ∑ b : Fin n,
                cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))
              n e Kx Jx =
            ∑ p : Fin n × Fin n,
              cT p *
                fiberNormSqComponent (I := I) (M := M) g x 0 2
                  (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2)) n e Kx Jx := by
        rw [show (∑ a : Fin n, ∑ b : Fin n,
              cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b)) =
            ∑ p : Fin n × Fin n,
              cT p • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2) from
          (Fintype.sum_prod_type'
            (f := fun a b =>
              cT (a, b) • R (e i) (e j)
                (dualTensorFrame (I := I) (M := M) g x e a b))).symm]
        rw [fiberNormSqComponent_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [fiberNormSqComponent_smul]
      rw [hcomp]
      -- Cauchy–Schwarz over the product index.
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ cT
        (fun p => fiberNormSqComponent (I := I) (M := M) g x 0 2
          (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2)) n e Kx Jx)
    -- Sum the per-summand bound over `(K, J)`.
    calc
      (∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2
            (∑ a : Fin n, ∑ b : Fin n,
              cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))
            n e Kx Jx)
          ≤ ∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin 2 → Fin n,
              (∑ p : Fin n × Fin n, cT p ^ 2) *
                ∑ p : Fin n × Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))
                    n e Kx Jx := by
            refine Finset.sum_le_sum (fun Kx _ => Finset.sum_le_sum (fun Jx _ => hterm Kx Jx))
      _ = (∑ p : Fin n × Fin n, cT p ^ 2) *
            ∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin 2 → Fin n,
              ∑ p : Fin n × Fin n,
                fiberNormSqSummand (I := I) (M := M) g x 0 2
                  (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))
                  n e Kx Jx := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Kx _ => ?_)
            rw [Finset.mul_sum]
      _ = (∑ p : Fin n × Fin n, cT p ^ 2) *
            ∑ p : Fin n × Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2)) := by
            congr 1
            -- Fold `∑_K ∑_J summand(F_p)` into `riemannianFiberNormSq (R F_p)`, then swap
            -- the `(K, J)` sums to the inside of the `p` sum.
            rw [show (∑ p : Fin n × Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))) =
                ∑ p : Fin n × Fin n, ∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin 2 → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))
                    n e Kx Jx from by
              refine Finset.sum_congr rfl (fun p _ => ?_)
              rw [hrepr (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))]]
            -- Now both sides are triple sums; reorder `∑_K ∑_J ∑_p = ∑_p ∑_K ∑_J`.
            -- First, under each `K`, swap the inner `∑_J ∑_p → ∑_p ∑_J`.
            rw [show (∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin 2 → Fin n, ∑ p : Fin n × Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))
                    n e Kx Jx) =
                ∑ Kx : Fin 0 → Fin n, ∑ p : Fin n × Fin n, ∑ Jx : Fin 2 → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))
                    n e Kx Jx from by
              refine Finset.sum_congr rfl (fun Kx _ => ?_)
              rw [Finset.sum_comm]]
            -- Then swap the outer `∑_K ∑_p → ∑_p ∑_K`.
            rw [Finset.sum_comm]
      _ ≤ (∑ a : Fin n, ∑ b : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))) *
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
            apply le_of_eq
            -- Identify `∑_p cT² = riemannianFiberNormSq T` (Parseval) and rewrite the
            -- residual product sum into the iterated `(a, b)` double sum.
            rw [show (∑ p : Fin n × Fin n, cT p ^ 2) =
                riemannianFiberNormSq (I := I) (M := M) g 0 2 x T from by
              rw [hParseval, ← Fintype.sum_prod_type' (f := fun a b => cT (a, b) ^ 2)]]
            rw [show (∑ p : Fin n × Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))) =
                ∑ a : Fin n, ∑ b : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b)) from
              Fintype.sum_prod_type'
                (f := fun a b =>
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b)))]
            ring
  -- Sum the per-frame-pair bound over `(i, j)`.
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T))
        ≤ ∑ i : Fin n, ∑ j : Fin n,
            (∑ a : Fin n, ∑ b : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                  (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))) *
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j))
    _ = (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))) *
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_mul]

/-! ## The combined `(v, w, T)`-uniform per-point bound

Combining the Stage 1 `(v, w)`-factorisation with the `T`-independent per-point bound gives
a single per-point constant `C_x` controlling the curvature term for *all* `(v, w, T)`. -/

/-- **`(v, w, T)`-uniform per-point fibre-norm bound for the tensor curvature operator.**
For any point `x`, there is a `T`-independent (and `(v, w)`-independent) nonnegative
constant `C_x` such that for all tangent vectors `v, w` and all `(0, 2)`-tensors `T`,
```
riemannianFiberNormSq g 0 2 x (R_x(v, w) T)
  ≤ C_x · (g.inner x v v) · (g.inner x w w) · riemannianFiberNormSq g 0 2 x T.
```
The constant is
`C_x = ∑_{i, j, a, b} riemannianFiberNormSq g 0 2 x (R_x(e_i, e_j) (dualTensorFrame g x e a b))`
for the `g`-orthonormal tangent frame `e` at `x`. -/
theorem exists_Cx_riemannianFiberNormSq_riemannOp_tensorCov_le
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      ∀ (v w : TangentSpace I x) (T : TensorRSSpace 0 2 I x),
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (riemannOp (tensorCov (I := I) g 0 2) x v w T) ≤
          Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
  classical
  -- Obtain the `g`-orthonormal frame with its `Module.Basis`, Parseval, expansion, repr.
  obtain ⟨n, e, bse, _hn, hbse, horth, hpars, hexpand, hrepr⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g x
  set R := riemannOp (tensorCov (I := I) g 0 2) x with hR_def
  -- The per-point constant `C_x`.
  set Cx : ℝ :=
    ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b)) with hCx_def
  have hCx_nonneg : 0 ≤ Cx := by
    rw [hCx_def]
    refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => ?_))))
    exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x _
  refine ⟨Cx, hCx_nonneg, ?_⟩
  intro v w T
  -- Nonnegativity of the intrinsic factors via Parseval.
  have hvv_nonneg : 0 ≤ g.inner x v v := by
    rw [← hpars v]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hww_nonneg : 0 ≤ g.inner x w w := by
    rw [← hpars w]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  -- Stage 1 `(v, w)`-factorisation for this exact frame: bound the LHS by
  -- `‖v‖²·‖w‖² · ∑_{i,j} riemannianFiberNormSq (R e_i e_j T)`.
  have hvw : riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R v w T) ≤
      g.inner x v v * g.inner x w w *
        ∑ i : Fin n, ∑ j : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T) := by
    -- Expand the LHS via `hrepr`, bound each summand by the Stage 1 per-component lemma.
    rw [hrepr (R v w T)]
    have hterm : ∀ K : Fin 0 → Fin n, ∀ J : Fin 2 → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 2 (R v w T) n e K J ≤
          g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J :=
      fun K J => fiberNormSqSummand_riemannOp_tensorCov_vw_le
        (I := I) (M := M) g x e hpars hexpand v w T K J
    calc
      (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2 (R v w T) n e K J)
          ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
              g.inner x v v * g.inner x w w *
                ∑ i : Fin n, ∑ j : Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J := by
            exact Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => hterm K J))
      _ = g.inner x v v * g.inner x w w *
            ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
              ∑ i : Fin n, ∑ j : Fin n,
                fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun K _ => ?_)
            rw [Finset.mul_sum]
      _ = g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T) := by
            congr 1
            -- Fold and reorder: `∑_K ∑_J ∑_i ∑_j = ∑_i ∑_j (∑_K ∑_J) = ∑_i ∑_j rfns`.
            rw [show (∑ i : Fin n, ∑ j : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T)) =
                ∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J from by
              refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
              rw [hrepr (R (e i) (e j) T)]]
            -- Reorder `∑_K ∑_J ∑_i ∑_j = ∑_i ∑_j ∑_K ∑_J` by collapsing each pair of sums
            -- to a single product-index sum and applying one `Finset.sum_comm`.
            set F : (Fin 0 → Fin n) → (Fin 2 → Fin n) → Fin n → Fin n → ℝ :=
              fun K J i j =>
                fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J
              with hF_def
            have hLHS : (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                  ∑ i : Fin n, ∑ j : Fin n, F K J i j) =
                ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n),
                  ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 := by
              calc
                (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                    ∑ i : Fin n, ∑ j : Fin n, F K J i j)
                    = ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                        ∑ p : Fin n × Fin n, F K J p.1 p.2 := by
                      refine Finset.sum_congr rfl (fun K _ =>
                        Finset.sum_congr rfl (fun J _ => ?_))
                      exact (Fintype.sum_prod_type' (f := fun i j => F K J i j)).symm
                _ = ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n),
                        ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 :=
                      (Fintype.sum_prod_type' (f := fun K J =>
                        ∑ p : Fin n × Fin n, F K J p.1 p.2)).symm
            have hRHS : (∑ i : Fin n, ∑ j : Fin n,
                  ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, F K J i j) =
                ∑ p : Fin n × Fin n,
                  ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 p.1 p.2 := by
              calc
                (∑ i : Fin n, ∑ j : Fin n,
                    ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, F K J i j)
                    = ∑ i : Fin n, ∑ j : Fin n,
                        ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 i j := by
                      refine Finset.sum_congr rfl (fun i _ =>
                        Finset.sum_congr rfl (fun j _ => ?_))
                      exact (Fintype.sum_prod_type' (f := fun K J => F K J i j)).symm
                _ = ∑ p : Fin n × Fin n,
                        ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 p.1 p.2 :=
                      (Fintype.sum_prod_type' (f := fun i j =>
                        ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 i j)).symm
            rw [hLHS, hRHS]
            exact Finset.sum_comm
  -- The `T`-independent per-point bound for the residual.
  have hCxT : (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T)) ≤
      Cx * riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
    rw [hCx_def]
    exact sum_riemannianFiberNormSq_riemannOp_le_Cx
      (I := I) (M := M) g x e bse hbse horth hrepr T
  -- Chain the two bounds.
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R v w T)
        ≤ g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T) := hvw
    _ ≤ g.inner x v v * g.inner x w w *
            (Cx * riemannianFiberNormSq (I := I) (M := M) g 0 2 x T) := by
          refine mul_le_mul_of_nonneg_left hCxT ?_
          exact mul_nonneg hvv_nonneg hww_nonneg
    _ = Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by ring

end Connection
end Integral
end DifferentialGeometry

end
