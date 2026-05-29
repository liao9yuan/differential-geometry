import DifferentialGeometry.Integral.Connection.TensorRicciCommutatorRiemannianFiberNormBound
import DifferentialGeometry.Integral.Connection.RiemannianFiberNormSqLeChartAlphaSummandSum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Intrinsic frame-factorisation of the tensor curvature operator's fibre norm

For a smooth Riemannian metric `g` on a manifold `M`, the bundled curvature operator
`riemannOp (tensorCov g 0 2) x` of the `(0, 2)`-tensor covariant derivative is a
continuous trilinear form `T_x M × T_x M × (T^0_2)_x → (T^0_2)_x`. The order-`2`
Gårding estimate must absorb its action `R_x(v, w) T` with an absorbing constant that
is **independent of the tensor `T` and the vectors `v, w`** (the Gårding constants
`C₁, C₂` are fixed, uniform over all smooth fields). The per-section bound
`exists_bound_riemannianFiberNormSq_smoothCcTensor` and the per-section curvature
bound `exists_bound_riemannianFiberNormSq_riemannOp_tensorCov` only give a
constant that depends on the chosen fields; this file isolates the genuinely
`(v, w, T)`-uniform structure.

## Why the model-norm route is unavailable

The per-point witness `riemannianFiberNormSq_riemannOp_tensorCov_le_witness` controls
`riemannianFiberNormSq g 0 2 x (R_x(v, w) T)` by `‖R_x(v, w) T‖² · A(x)²`, where both
factors involve the model (`E`-induced) fibre norm and the ambient frame scalar
`A(x)` — the latter being the `E`-norm sum of the `g`-orthonormal frame, equivalently
the operator norm of the chart trivialisation. On a multi-chart manifold this scalar
is *genuinely unbounded* on compact sets, so any bound routed through it cannot yield a
uniform `C_g`. The correct, chart-locality-free route works entirely inside the
intrinsic `riemannianFiberNormSq` and the `g`-inner products `g.inner x v v`,
`g.inner x w w`.

## Strategy (`(v, w)`-factorisation)

Fix a `g`-orthonormal frame `e` of `(T_x M, g.inner x)`, as chosen inside the
definition of `riemannianFiberNormSq`. For `(0, 2)`-tensors the intrinsic fibre norm
squared is the sum over the frame of squared frame components,
`riemannianFiberNormSq g 0 2 x S = ∑_{K, J} fiberNormSqSummand … S … K J`, and each
frame component `S ↦ fiberNormSqSummand … S … K J` is the square of an `ℝ`-linear
functional `L_{K, J}(S)` of `S`.

The curvature operator `riemannOp (tensorCov g 0 2) x` is continuous and linear in each
of its three slots, so expanding `v = ∑_i ⟨e_i, v⟩_g e_i`, `w = ∑_j ⟨e_j, w⟩_g e_j`
(orthonormal-frame representation) and applying `L_{K, J}` gives

```
L_{K, J}(R_x(v, w) T) = ∑_{i, j} ⟨e_i, v⟩_g ⟨e_j, w⟩_g · L_{K, J}(R_x(e_i, e_j) T).
```

The Cauchy–Schwarz inequality over the `(i, j)`-index together with Parseval's identity
`∑_i ⟨e_i, v⟩_g² = g.inner x v v` (and likewise for `w`) yields

```
L_{K, J}(R_x(v, w) T)² ≤ (g.inner x v v) · (g.inner x w w)
    · ∑_{i, j} L_{K, J}(R_x(e_i, e_j) T)².
```

Summing over `(K, J)` gives the **intrinsic `(v, w)`-factorised bound**

```
riemannianFiberNormSq g 0 2 x (R_x(v, w) T)
  ≤ (g.inner x v v) · (g.inner x w w) · ∑_{i, j} riemannianFiberNormSq g 0 2 x (R_x(e_i, e_j) T),
```

where the right-hand sum is the intrinsic fibre-norm energy of the curvature acting on
`T` through the *frame pairs* `(e_i, e_j)`, with `e` the `g`-orthonormal frame at `x`.
This is `(v, w)`-uniform: the only place `(v, w)` enters is through the intrinsic
quadratic factors `g.inner x v v = ‖v‖_g²` and `g.inner x w w = ‖w‖_g²`.

## Main results

* `riemannianFiberNormSq_eq_sum_fiberNormSqSummand_orthonormal_witness` — the
  intrinsic fibre-norm squared written as a frame double sum over a `g`-orthonormal
  frame.
* `fiberNormSqSummand_linearFunctional` — the per-frame-component functional and the
  fact that the summand is its square.
* `riemannianFiberNormSq_riemannOp_tensorCov_vw_factor_le` — the intrinsic
  `(v, w)`-factorised bound above.
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

/-! ## The per-frame-component linear functional

For a fixed frame `e : Fin n → TangentSpace I b` and multi-indices `K : Fin r → Fin n`,
`J : Fin s → Fin n`, the map sending a tensor `S : TensorRSSpace r s I b` to its scalar
frame component

```
L_{K, J}(S) = S (ω^K) (e_J),  where ω^K = ∏_k g.inner b (e (K k)),
```

is `ℝ`-linear, and `fiberNormSqSummand g b r s S n e K J = L_{K, J}(S)²`. The linearity
follows from the fact that the underlying continuous-linear-map evaluation
`S ↦ S ω^K` and the multilinear evaluation `(·) e_J` are both `ℝ`-linear in `S`. -/

/-- The per-frame-component scalar functional of a tensor `S` at the frame `e` and
multi-indices `(K, J)`: `L_{K, J}(S) = S(ω^K)(e_J)`. -/
noncomputable def fiberNormSqComponent
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (S : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) : ℝ :=
  (S : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
        (fun k => g.inner b (e (K k))))
      (fun k => e (J k))

/-- The frame summand is the square of the frame component. -/
lemma fiberNormSqSummand_eq_component_sq
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (S : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqSummand (I := I) (M := M) g b r s S n e K J =
      fiberNormSqComponent (I := I) (M := M) g b r s S n e K J ^ 2 := rfl

/-- The frame component is additive in the tensor argument. -/
lemma fiberNormSqComponent_add
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (S S' : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g b r s (S + S') n e K J =
      fiberNormSqComponent (I := I) (M := M) g b r s S n e K J +
        fiberNormSqComponent (I := I) (M := M) g b r s S' n e K J := by
  unfold fiberNormSqComponent
  -- `(S + S') ω = S ω + S' ω` (CLM addition), then evaluate at `e_J`.
  rw [show ((S + S' : TensorRSSpace r s I b) :
        Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
          (fun k => g.inner b (e (K k)))) =
      (S : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
          (fun k => g.inner b (e (K k)))) +
      (S' : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
          (fun k => g.inner b (e (K k)))) from rfl]
  rfl

/-- The frame component is homogeneous in the tensor argument. -/
lemma fiberNormSqComponent_smul
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (c : ℝ) (S : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g b r s (c • S) n e K J =
      c * fiberNormSqComponent (I := I) (M := M) g b r s S n e K J := by
  unfold fiberNormSqComponent
  rw [show ((c • S : TensorRSSpace r s I b) :
        Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
          (fun k => g.inner b (e (K k)))) =
      c • (S : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
          (fun k => g.inner b (e (K k)))) from rfl]
  rfl

/-- The frame component of the zero tensor is zero. -/
lemma fiberNormSqComponent_zero
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g b r s
      (0 : TensorRSSpace r s I b) n e K J = 0 := rfl

/-- The frame component commutes with finite sums in the tensor argument. -/
lemma fiberNormSqComponent_sum
    {ι : Type*} (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (t : Finset ι) (F : ι → TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g b r s (∑ i ∈ t, F i) n e K J =
      ∑ i ∈ t, fiberNormSqComponent (I := I) (M := M) g b r s (F i) n e K J := by
  classical
  refine Finset.cons_induction ?_ ?_ t
  · simp [fiberNormSqComponent_zero]
  · intro a s' ha ih
    rw [Finset.sum_cons, Finset.sum_cons, fiberNormSqComponent_add, ih]

/-! ## The `g`-orthonormal-frame witness for `riemannianFiberNormSq`

A public copy of the strengthened witness exposing both the `g`-orthonormality of the
frame and the double-sum representation, packaged with the frame components used
throughout this file. -/

/-- **Strengthened witness: `g`-orthonormal frame representation of
`riemannianFiberNormSq`.** There is a frame `e : Fin n → TangentSpace I b` with
`n = Module.finrank ℝ (TangentSpace I b)` that is `g`-orthonormal
(`g.inner b (e i) (e j) = if i = j then 1 else 0`) and represents the intrinsic fibre
norm squared as the double frame sum, simultaneously for *all* tensors `S` (the frame
does not depend on `S`). -/
lemma exists_orthonormal_frame_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I b),
      n = Module.finrank ℝ (TangentSpace I b) ∧
      (∀ i j : Fin n, g.inner b (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      (∀ v : TangentSpace I b, ∑ i : Fin n, g.inner b (e i) v ^ 2 = g.inner b v v) ∧
      ∀ S : TensorRSSpace r s I b,
        riemannianFiberNormSq (I := I) (M := M) g r s b S =
          ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
            fiberNormSqSummand (I := I) (M := M) g b r s S n e K J := by
  classical
  -- Build the `letI`-scoped local inner-product instances, as in `riemannianFiberNormSq`.
  let cd : InnerProductSpace.Core ℝ (TangentSpace I b) := g.toRiemannianMetric.toCore b
  have hc : ContinuousAt (fun v : TangentSpace I b => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt b
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I b |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded b
  letI nag : NormedAddCommGroup (TangentSpace I b) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I b) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I b) with hn_def
  set e : OrthonormalBasis (Fin n) ℝ (TangentSpace I b) := stdOrthonormalBasis ℝ _ with he_def
  -- The local `inner ℝ` is definitionally `g.inner b`.
  have hinner_eq : ∀ u v : TangentSpace I b, (inner ℝ u v : ℝ) = g.inner b u v :=
    fun u v => rfl
  refine ⟨n, fun i => e i, rfl, ?_, ?_, ?_⟩
  · -- `g`-orthonormality from the orthonormal basis.
    intro i j
    have horth : Orthonormal ℝ (fun i : Fin n => e i) := e.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I b)).mp horth i j
    rw [← hinner_eq (e i) (e j)]
    exact hite
  · -- Parseval: `∑_i ⟨e i, v⟩_g² = g.inner b v v = ‖v‖²` in the local norm.
    intro v
    have hpars : ∑ i : Fin n, (inner ℝ (e i) v : ℝ) ^ 2 = ‖v‖ ^ 2 :=
      OrthonormalBasis.sum_sq_inner_right e v
    have hnorm_sq : (‖v‖ : ℝ) ^ 2 = g.inner b v v := by
      have hri : (inner ℝ v v : ℝ) = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      rw [hinner_eq v v] at hri
      exact hri.symm
    calc
      ∑ i : Fin n, g.inner b (e i) v ^ 2
          = ∑ i : Fin n, (inner ℝ (e i) v : ℝ) ^ 2 := by
            refine Finset.sum_congr rfl (fun i _ => ?_); rw [hinner_eq (e i) v]
      _ = ‖v‖ ^ 2 := hpars
      _ = g.inner b v v := hnorm_sq
  · -- The double-sum representation: this is the unfolding of `riemannianFiberNormSq`.
    intro S
    rfl

/-! ## Frame-expansion of a tangent vector

In the `g`-orthonormal frame `e`, every tangent vector expands as
`v = ∑_i ⟨e_i, v⟩_g · e_i`. This is the local-inner-product version of
`OrthonormalBasis.sum_repr'`, with the inner product written through `g.inner`. -/

/-- A tangent vector expands in the `g`-orthonormal frame chosen by
`exists_orthonormal_frame_riemannianFiberNormSq`. The expansion is stated for the same
local-inner-product frame; we extract it from `OrthonormalBasis.sum_repr'`. -/
lemma tangent_frame_expansion
    (g : SmoothRiemannianMetric I M) (b : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I b),
      n = Module.finrank ℝ (TangentSpace I b) ∧
      (∀ i j : Fin n, g.inner b (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      (∀ v : TangentSpace I b, ∑ i : Fin n, g.inner b (e i) v ^ 2 = g.inner b v v) ∧
      (∀ v : TangentSpace I b, v = ∑ i : Fin n, g.inner b (e i) v • e i) ∧
      ∀ S : TensorRSSpace 0 2 I b,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 b S =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
            fiberNormSqSummand (I := I) (M := M) g b 0 2 S n e K J := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I b) := g.toRiemannianMetric.toCore b
  have hc : ContinuousAt (fun v : TangentSpace I b => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt b
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I b |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded b
  letI nag : NormedAddCommGroup (TangentSpace I b) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I b) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I b) with hn_def
  set e : OrthonormalBasis (Fin n) ℝ (TangentSpace I b) := stdOrthonormalBasis ℝ _ with he_def
  have hinner_eq : ∀ u v : TangentSpace I b, (inner ℝ u v : ℝ) = g.inner b u v :=
    fun u v => rfl
  refine ⟨n, fun i => e i, rfl, ?_, ?_, ?_, ?_⟩
  · intro i j
    have horth : Orthonormal ℝ (fun i : Fin n => e i) := e.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I b)).mp horth i j
    rw [← hinner_eq (e i) (e j)]
    exact hite
  · intro v
    have hpars : ∑ i : Fin n, (inner ℝ (e i) v : ℝ) ^ 2 = ‖v‖ ^ 2 :=
      OrthonormalBasis.sum_sq_inner_right e v
    have hnorm_sq : (‖v‖ : ℝ) ^ 2 = g.inner b v v := by
      have hri : (inner ℝ v v : ℝ) = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      rw [hinner_eq v v] at hri
      exact hri.symm
    calc
      ∑ i : Fin n, g.inner b (e i) v ^ 2
          = ∑ i : Fin n, (inner ℝ (e i) v : ℝ) ^ 2 := by
            refine Finset.sum_congr rfl (fun i _ => ?_); rw [hinner_eq (e i) v]
      _ = ‖v‖ ^ 2 := hpars
      _ = g.inner b v v := hnorm_sq
  · -- Frame expansion from `OrthonormalBasis.sum_repr'`.
    intro v
    have hrepr : ∑ i : Fin n, (inner ℝ (e i) v : ℝ) • e i = v :=
      OrthonormalBasis.sum_repr' e v
    have hcongr : (∑ i : Fin n, g.inner b (e i) v • e i) =
        ∑ i : Fin n, (inner ℝ (e i) v : ℝ) • e i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hinner_eq (e i) v]
    rw [hcongr, hrepr]
  · intro S
    rfl

/-! ## Frame expansion of the curvature operator action

The bundled curvature operator `riemannOp (tensorCov g 0 2) x` is continuous and linear
in its first two slots. Expanding the input vectors `v, w` in the `g`-orthonormal frame
`e` gives a double-sum expansion of the curvature value in terms of the
frame-pair curvature values `R_x(e_i, e_j) T`. -/

/-- **Frame expansion of the curvature operator action.** For the `g`-orthonormal frame
`e` and a tensor `T`, with `v = ∑_i ⟨e_i, v⟩_g e_i`, `w = ∑_j ⟨e_j, w⟩_g e_j`, the
curvature value expands as
`R_x(v, w) T = ∑_{i, j} (⟨e_i, v⟩_g · ⟨e_j, w⟩_g) • R_x(e_i, e_j) T`. -/
lemma riemannOp_tensorCov_frame_expand
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hv_expand : ∀ u : TangentSpace I x, u = ∑ i : Fin n, g.inner x (e i) u • e i)
    (v w : TangentSpace I x) (T : TensorRSSpace 0 2 I x) :
    riemannOp (tensorCov (I := I) g 0 2) x v w T =
      ∑ i : Fin n, ∑ j : Fin n,
        (g.inner x (e i) v * g.inner x (e j) w) •
          riemannOp (tensorCov (I := I) g 0 2) x (e i) (e j) T := by
  classical
  set R := riemannOp (tensorCov (I := I) g 0 2) x with hR_def
  -- Expand the first slot.
  have hv : v = ∑ i : Fin n, g.inner x (e i) v • e i := hv_expand v
  have hw : w = ∑ j : Fin n, g.inner x (e j) w • e j := hv_expand w
  -- `R v = ∑_i ⟨e_i,v⟩ • R (e_i)` (R is a CLM in the first slot).
  have hRv : R v = ∑ i : Fin n, g.inner x (e i) v • R (e i) := by
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
  -- Apply at `w`: `(R v) w = ∑_i ⟨e_i,v⟩ • (R (e_i)) w`.
  have hRvw : R v w = ∑ i : Fin n, g.inner x (e i) v • R (e i) w := by
    rw [hRv, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ContinuousLinearMap.smul_apply]
  -- Now expand the second slot of each `R (e_i)`.
  have hRei_w : ∀ i : Fin n, R (e i) w =
      ∑ j : Fin n, g.inner x (e j) w • R (e i) (e j) := by
    intro i
    conv_lhs => rw [hw]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul]
  -- Apply at `T`.
  have hRvwT : R v w T = ∑ i : Fin n, g.inner x (e i) v • (R (e i) w) T := by
    rw [hRvw, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ContinuousLinearMap.smul_apply]
  rw [hRvwT]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hRei_w i]
  -- `R (e_i) w T = (∑_j ⟨e_j,w⟩ • R (e_i)(e_j)) T = ∑_j ⟨e_j,w⟩ • R(e_i)(e_j) T`.
  rw [ContinuousLinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ContinuousLinearMap.smul_apply, smul_smul]

/-! ## Per-frame-component Cauchy–Schwarz bound -/

/-- **Per-frame-component Cauchy–Schwarz bound.** For the `g`-orthonormal frame `e`
(with Parseval) and a fixed frame index pair `(K, J)`, the squared frame component of
the curvature value `R_x(v, w) T` is bounded by the intrinsic quadratic factors
`g.inner x v v`, `g.inner x w w` times the sum over frame pairs of the squared frame
components of `R_x(e_i, e_j) T`:

```
fiberNormSqSummand g x 0 2 (R_x(v, w) T) n e K J
  ≤ (g.inner x v v) · (g.inner x w w)
      · ∑_{i, j} fiberNormSqSummand g x 0 2 (R_x(e_i, e_j) T) n e K J.
```
-/
lemma fiberNormSqSummand_riemannOp_tensorCov_vw_le
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hpars : ∀ u : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) u ^ 2 = g.inner x u u)
    (hexpand : ∀ u : TangentSpace I x, u = ∑ i : Fin n, g.inner x (e i) u • e i)
    (v w : TangentSpace I x) (T : TensorRSSpace 0 2 I x)
    (K : Fin 0 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqSummand (I := I) (M := M) g x 0 2
        (riemannOp (tensorCov (I := I) g 0 2) x v w T) n e K J ≤
      g.inner x v v * g.inner x w w *
        ∑ i : Fin n, ∑ j : Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2
            (riemannOp (tensorCov (I := I) g 0 2) x (e i) (e j) T) n e K J := by
  classical
  set R := riemannOp (tensorCov (I := I) g 0 2) x with hR_def
  -- Frame expansion of the curvature value.
  have hexp : R v w T =
      ∑ i : Fin n, ∑ j : Fin n,
        (g.inner x (e i) v * g.inner x (e j) w) • R (e i) (e j) T :=
    riemannOp_tensorCov_frame_expand (I := I) (M := M) g x e hexpand v w T
  -- The frame component is linear, so it commutes with the double sum and the smul.
  -- Write everything over the product index `Fin n × Fin n`.
  set c : Fin n × Fin n → ℝ := fun p => g.inner x (e p.1) v * g.inner x (e p.2) w with hc_def
  set a : Fin n × Fin n → ℝ := fun p =>
    fiberNormSqComponent (I := I) (M := M) g x 0 2 (R (e p.1) (e p.2) T) n e K J with ha_def
  -- Component of the expansion.
  have hcomp_eq :
      fiberNormSqComponent (I := I) (M := M) g x 0 2 (R v w T) n e K J =
        ∑ p : Fin n × Fin n, c p * a p := by
    rw [hexp]
    -- Component of a double sum of smuls.
    rw [show (∑ i : Fin n, ∑ j : Fin n,
          (g.inner x (e i) v * g.inner x (e j) w) • R (e i) (e j) T) =
        ∑ p : Fin n × Fin n,
          (g.inner x (e p.1) v * g.inner x (e p.2) w) • R (e p.1) (e p.2) T from
      (Fintype.sum_prod_type'
        (f := fun i j => (g.inner x (e i) v * g.inner x (e j) w) • R (e i) (e j) T)).symm]
    rw [fiberNormSqComponent_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [fiberNormSqComponent_smul]
  -- The summand is the square of the component.
  rw [fiberNormSqSummand_eq_component_sq, hcomp_eq]
  -- Cauchy–Schwarz over the product index.
  have hCS : (∑ p : Fin n × Fin n, c p * a p) ^ 2 ≤
      (∑ p : Fin n × Fin n, c p ^ 2) * ∑ p : Fin n × Fin n, a p ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c a
  refine hCS.trans ?_
  -- Identify `∑_p c_p² = ‖v‖²·‖w‖²` (Parseval) and `∑_p a_p² = the residual double sum`.
  have hcsq : (∑ p : Fin n × Fin n, c p ^ 2) =
      g.inner x v v * g.inner x w w := by
    have hsplit : (∑ p : Fin n × Fin n, c p ^ 2) =
        (∑ i : Fin n, g.inner x (e i) v ^ 2) *
          ∑ j : Fin n, g.inner x (e j) w ^ 2 := by
      rw [Finset.sum_mul_sum]
      rw [Fintype.sum_prod_type (f := fun p : Fin n × Fin n => c p ^ 2)]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hc_def]
      ring
    rw [hsplit, hpars v, hpars w]
  have hasq : (∑ p : Fin n × Fin n, a p ^ 2) =
      ∑ i : Fin n, ∑ j : Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J := by
    rw [Fintype.sum_prod_type (f := fun p : Fin n × Fin n => a p ^ 2)]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [ha_def, fiberNormSqSummand_eq_component_sq]
  rw [hcsq, hasq]

/-! ## The intrinsic `(v, w)`-factorised fibre-norm bound -/

/-- **Intrinsic `(v, w)`-factorised fibre-norm bound for the tensor curvature operator.**
For a smooth Riemannian metric `g` on a manifold `M`, any point `x`, any tangent vectors
`v, w` and any `(0, 2)`-tensor `T`, the intrinsic Riemannian fibre norm squared of the
curvature value `R_x(v, w) T = riemannOp (tensorCov g 0 2) x v w T` is bounded by the
intrinsic quadratic factors `g.inner x v v = ‖v‖_g²` and `g.inner x w w = ‖w‖_g²` times
a `(v, w)`-uniform residual: the sum over the `g`-orthonormal frame pairs `(e_i, e_j)` of
the intrinsic fibre-norm energies of the curvature acting on `T`:

```
riemannianFiberNormSq g 0 2 x (R_x(v, w) T)
  ≤ (g.inner x v v) · (g.inner x w w)
      · ∑_{i, j} riemannianFiberNormSq g 0 2 x (R_x(e_i, e_j) T).
```

This is the chart-locality-free, model-norm-free, `(v, w)`-uniform form: the dependence
on `(v, w)` is entirely through the intrinsic `g`-norms `‖v‖_g²`, `‖w‖_g²`. -/
theorem riemannianFiberNormSq_riemannOp_tensorCov_vw_factor_le
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (T : TensorRSSpace 0 2 I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (riemannOp (tensorCov (I := I) g 0 2) x v w T) ≤
        g.inner x v v * g.inner x w w *
          ∑ i : Fin n, ∑ j : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              (riemannOp (tensorCov (I := I) g 0 2) x (e i) (e j) T) := by
  classical
  -- Obtain the `g`-orthonormal frame, its Parseval identity and the frame expansion.
  obtain ⟨n, e, _hn, _horth, hpars, hexpand, hrepr⟩ :=
    tangent_frame_expansion (I := I) (M := M) g x
  refine ⟨n, e, ?_⟩
  set R := riemannOp (tensorCov (I := I) g 0 2) x with hR_def
  -- Set `B := g.inner x v v * g.inner x w w` (the intrinsic factor), nonnegative.
  set B : ℝ := g.inner x v v * g.inner x w w with hB_def
  -- Nonnegativity of the intrinsic factors via Parseval (sum of squares).
  have hvv_nonneg : 0 ≤ g.inner x v v := by
    rw [← hpars v]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hww_nonneg : 0 ≤ g.inner x w w := by
    rw [← hpars w]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB_nonneg : 0 ≤ B := mul_nonneg hvv_nonneg hww_nonneg
  -- Write the LHS intrinsic fibre norm as a frame double sum of squared components.
  rw [hrepr (R v w T)]
  -- Per-frame-component bound, summed over `(K, J)`.
  have hterm : ∀ K : Fin 0 → Fin n, ∀ J : Fin 2 → Fin n,
      fiberNormSqSummand (I := I) (M := M) g x 0 2 (R v w T) n e K J ≤
        B * ∑ i : Fin n, ∑ j : Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J := by
    intro K J
    rw [hB_def]
    exact fiberNormSqSummand_riemannOp_tensorCov_vw_le
      (I := I) (M := M) g x e hpars hexpand v w T K J
  -- Sum the termwise bound.
  calc
    (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 2 (R v w T) n e K J)
        ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
            B * ∑ i : Fin n, ∑ j : Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J := by
          refine Finset.sum_le_sum (fun K _ => ?_)
          exact Finset.sum_le_sum (fun J _ => hterm K J)
    _ = B * ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
            ∑ i : Fin n, ∑ j : Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun K _ => ?_)
          rw [Finset.mul_sum]
    _ = B * ∑ i : Fin n, ∑ j : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T) := by
          congr 1
          -- Abbreviate the four-index summand.
          set F : (Fin 0 → Fin n) → (Fin 2 → Fin n) → Fin n → Fin n → ℝ :=
            fun K J i j =>
              fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J
            with hF_def
          -- RHS: expand `riemannianFiberNormSq` via `hrepr`.
          have hrhs : (∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T)) =
              ∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                F K J i j := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            rw [hrepr (R (e i) (e j) T)]
          rw [hrhs]
          -- Collapse each double sum into a single sum over a product index, on both
          -- sides, reducing to a single `Finset.sum_comm`.
          have hLHS : (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                ∑ i : Fin n, ∑ j : Fin n, F K J i j) =
              ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n),
                ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 := by
            -- Collapse inner `(i, j)` to `p`, then outer `(K, J)` to `q`.
            have hinner : ∀ K J,
                (∑ i : Fin n, ∑ j : Fin n, F K J i j) =
                  ∑ p : Fin n × Fin n, F K J p.1 p.2 :=
              fun K J => (Fintype.sum_prod_type' (f := fun i j => F K J i j)).symm
            calc
              (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                  ∑ i : Fin n, ∑ j : Fin n, F K J i j)
                  = ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                      ∑ p : Fin n × Fin n, F K J p.1 p.2 := by
                    refine Finset.sum_congr rfl (fun K _ =>
                      Finset.sum_congr rfl (fun J _ => ?_))
                    rw [hinner K J]
              _ = ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n),
                      ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 :=
                    (Fintype.sum_prod_type' (f := fun K J =>
                      ∑ p : Fin n × Fin n, F K J p.1 p.2)).symm
          have hRHS : (∑ i : Fin n, ∑ j : Fin n,
                ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, F K J i j) =
              ∑ p : Fin n × Fin n,
                ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 p.1 p.2 := by
            have hinner : ∀ i j,
                (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, F K J i j) =
                  ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 i j :=
              fun i j => (Fintype.sum_prod_type' (f := fun K J => F K J i j)).symm
            calc
              (∑ i : Fin n, ∑ j : Fin n,
                  ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, F K J i j)
                  = ∑ i : Fin n, ∑ j : Fin n,
                      ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 i j := by
                    refine Finset.sum_congr rfl (fun i _ =>
                      Finset.sum_congr rfl (fun j _ => ?_))
                    rw [hinner i j]
              _ = ∑ p : Fin n × Fin n,
                      ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 p.1 p.2 :=
                    (Fintype.sum_prod_type' (f := fun i j =>
                      ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 i j)).symm
          rw [hLHS, hRHS]
          exact Finset.sum_comm

end Connection
end Integral
end DifferentialGeometry

end
