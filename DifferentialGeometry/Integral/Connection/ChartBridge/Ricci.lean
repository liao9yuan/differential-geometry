import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.Integral.Connection.ChartBridge.Riemann
import DifferentialGeometry.Geometry.Curvature.Ricci

/-!
# Bridge between the chart Ricci carrier and the abstract Ricci tensor

The chart Ricci carrier `ricciFun g : pointwiseBilin I` (defined in
`Integral.Geometry.Curvature.Riemann`) is the bilinear form on the tangent bundle
whose matrix in the canonical model basis is the chart-coordinate Ricci tensor
$$
  \operatorname{Rc}_{ik}(x, \varphi_x x) = \sum_j R^j{}_{ijk}(g, x)(\varphi_x x).
$$

The abstract Ricci tensor `ricciTensor g x : T_x M →L T_x M →L ℝ` (defined in
`Integral.Connection.Ricci`) is the trace of the curvature endomorphism
$$
  \operatorname{Ric}^{\nabla}(v, w)
    := \operatorname{tr}_{\mathbb{R}}\bigl(Z \mapsto R^{\nabla}(Z, v) w\bigr).
$$

Both objects describe the Ricci curvature of the Levi-Civita connection. This bridge file
identifies the two on the canonical model basis. The identification reduces, by the
basis-coordinate trace formula `ricciTensor_apply_basisSum` and trilinearity of
`riemannOp` and `chartRiemannCLM`, to the *deep* basis identification
`riemannOp (LeviCivita g) x e_j e_k e_i = chartRiemannCLM g x e_j e_k e_i` of the abstract
and chart Riemann CLMs (the iterated chart-Christoffel expansion of `riemannOp`, which is
the standard deep identification deferred to a downstream development; see
`ChartBridge.Riemann` for the structural reduction).

This file therefore exposes the bridge in **hypothesis-bearing** form: a downstream client
that supplies the deep basis identity at the point obtains the pointwise equality
`ricciFun g x = ricciTensor g x` as bilinear forms. The hypothesis is recorded as a
predicate `chartRiemannBasisIdentity g x` on the four indices, mirroring the
`chartHessianMatrixIdentity` pattern in `ChartBridge.Hessian`.

## Main definitions

* `chartRiemannBasisIdentity g x` — the basis-coordinate identification at `x`:
  for every quadruple `(i, j, k, l)`, the `l`-th coordinate of
  `riemannOp (LeviCivita g) x e_j e_k e_i` equals
  `chartRiemannTensor g x i j k l (extChartAt I x x)`. Equivalently, the basis-evaluated
  abstract Riemann CLM agrees with the chart-Riemann CLM at `x`.

## Main theorems

* `chartRiemannBasisIdentity_iff` — the predicate `chartRiemannBasisIdentity g x` is
  equivalent to the basis identity
  `riemannOp (LeviCivita g) x e_j e_k e_i = chartRiemannCLM g x e_j e_k e_i`
  for every `(i, j, k)`.
* `riemannOp_eq_chartRiemannCLM_apply_of_basis_identity` — under
  `chartRiemannBasisIdentity g x`, the trilinear value
  `riemannOp (LeviCivita g) x v w u` equals `chartRiemannCLM g x v w u` for all
  tangent vectors `(v, w, u)`. The proof expands each input in the canonical model basis
  and uses trilinearity of both sides.
* `ricciTensor_eq_chartRicciSwap_of_basis_identity` — the **swap form** of the bridge:
  under `chartRiemannBasisIdentity g x`, the abstract Ricci tensor admits the
  basis-coordinate sum
  `ricciTensor g x v w = ∑ i k, v^k * w^i * Rc_{i, k}(x, ϕ_x x)`,
  with `(v, w)` paired against the chart Ricci entries in the *swapped* index order. This
  is the convention difference between the trace `tr_Z R(Z, v) w` (which has v at the
  second differentiation slot of R, w at the vector slot) and the chart `Rc_{ik}` (which
  takes the vector index first, the second differentiation index second). No symmetry
  assumption is required for this form.
* `ricciFun_eq_ricciTensor_swap_of_basis_identity` — the swap-form bridge to the chart
  Ricci carrier: `ricciFun g x v w = ricciTensor g x w v` under
  `chartRiemannBasisIdentity g x`.
* `ricciFun_eq_ricciTensor_of_basis_identity` — the **direct identification** under
  `[I.Boundaryless]`: under `chartRiemannBasisIdentity g x` and the closed-manifold
  hypothesis (which discharges the chart-level Ricci symmetry via
  `chartRicciTensor_symm_of_boundaryless`), we have
  `ricciFun g x v w = ricciTensor g x v w` as bilinear forms on `T_x M`.

## Sign convention

The chart Riemann tensor `chartRiemannTensor g α i j k l` follows the convention
`R^l{}_{ijk}` with `i` the "vector" index, `(j, k)` the differentiation indices, and `l`
the upper index. The chart Ricci tensor is `Rc_{ik} = ∑_j R^j{}_{ijk}` (contracting the
upper `l` against the first differentiation index `j`). The abstract Ricci tensor is the
trace `tr_Z R(Z, v) w` of the endomorphism `Z ↦ riemannOp x Z v w` on `T_x M`, where
`riemannOp x Z v w` corresponds to `R(Z, v) w` with slot-1 = `Z` (first diff), slot-2 =
`v` (second diff), slot-3 = `w` (vector). The two conventions differ in the assignment of
`(v, w)` to the slots `(diff2, vector)` (abstract) versus `(vector, diff2)` (chart),
producing the swap form recorded in this file. Ricci symmetry then matches the two as
bilinear forms.
-/

noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## The basis-coordinate identification predicate

We package the deep chart-Christoffel identification of the abstract Riemann CLM with the
chart Riemann CLM as a hypothesis-bearing predicate at each point. The predicate asserts
that the basis-coordinate values of `riemannOp (LeviCivita g) x` on the canonical model
basis match the chart-coordinate Riemann entries `R^l{}_{ijk}(g, x)(ϕ_x x)`. -/

/-- The basis-coordinate identification of the abstract Riemann operator and the chart
Riemann tensor at `x`: for every four-tuple `(i, j, k, l)`, the `l`-th coordinate of
`riemannOp (LeviCivita g) x e_j e_k e_i` equals the chart-coordinate Riemann entry
`R^l{}_{ijk}(g, x)(ϕ_x x)`. This is the deep identification produced by iterating the
chart-Christoffel formula for `LeviCivita g` twice; we expose it here as a predicate so
that downstream clients can supply it without forcing this file to depend on the
deferred deep computation. -/
def chartRiemannBasisIdentity (g : SmoothRiemannianMetric I M) (x : M) : Prop :=
  ∀ i j k l : Fin (Module.finrank ℝ E),
    ((Module.finBasis ℝ E).repr
        (riemannOp (cov := LeviCivita (I := I) g) x
          ((Module.finBasis ℝ E) j) ((Module.finBasis ℝ E) k)
          ((Module.finBasis ℝ E) i))) l =
      chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)

/-- The basis-coordinate identification is equivalent to pointwise equality of
`riemannOp (LeviCivita g) x` and `chartRiemannCLM g x` on every basis triple. -/
theorem chartRiemannBasisIdentity_iff (g : SmoothRiemannianMetric I M) (x : M) :
    chartRiemannBasisIdentity (I := I) g x ↔
      ∀ i j k : Fin (Module.finrank ℝ E),
        riemannOp (cov := LeviCivita (I := I) g) x
            ((Module.finBasis ℝ E) j) ((Module.finBasis ℝ E) k)
            ((Module.finBasis ℝ E) i) =
          chartRiemannCLM (I := I) g x
            ((Module.finBasis ℝ E) j) ((Module.finBasis ℝ E) k)
            ((Module.finBasis ℝ E) i) := by
  classical
  constructor
  · intro h i j k
    -- Two vectors are equal iff their basis representations are equal.
    apply (Module.finBasis ℝ E).repr.injective
    ext l
    rw [h i j k]
    -- RHS: compute b.repr (chartRiemannCLM x e_j e_k e_i) l via chartRiemannCLM_repr_basis.
    rw [chartRiemannCLM_repr_basis (I := I) g x i j k l]
  · intro h i j k l
    rw [h i j k]
    rw [chartRiemannCLM_repr_basis (I := I) g x i j k l]

/-! ## Trilinear extension of the basis identification

Under the basis-coordinate identification, the abstract Riemann CLM agrees with the chart
Riemann CLM as trilinear maps. The proof decomposes each input vector in the canonical
model basis and uses trilinearity of both sides. -/

/-- **Trilinear bridge.** Under the basis-coordinate identification, the abstract Riemann
operator `riemannOp (LeviCivita g) x` and the chart Riemann CLM `chartRiemannCLM g x`
agree as trilinear maps: `riemannOp x v w u = chartRiemannCLM x v w u` for all
`v, w, u : TangentSpace I x`. -/
theorem riemannOp_eq_chartRiemannCLM_apply_of_basis_identity
    (g : SmoothRiemannianMetric I M) (x : M)
    (h : chartRiemannBasisIdentity (I := I) g x)
    (v w u : TangentSpace I x) :
    riemannOp (cov := LeviCivita (I := I) g) x v w u =
      chartRiemannCLM (I := I) g x v w u := by
  classical
  -- Both sides are trilinear in (v, w, u). Decompose each input in the model basis and
  -- match term by term on the basis triple via the iff form of the hypothesis.
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hb_def
  have hbasis := (chartRiemannBasisIdentity_iff (I := I) g x).mp h
  -- Decompose v, w, u in the basis.
  have hv : v = ∑ j : Fin (Module.finrank ℝ E), b.repr v j • b j :=
    (Module.Basis.sum_repr b v).symm
  have hw : w = ∑ k : Fin (Module.finrank ℝ E), b.repr w k • b k :=
    (Module.Basis.sum_repr b w).symm
  have hu : u = ∑ i : Fin (Module.finrank ℝ E), b.repr u i • b i :=
    (Module.Basis.sum_repr b u).symm
  -- Expand `riemannOp x v w u` via trilinearity.
  have hLHS : riemannOp (cov := LeviCivita (I := I) g) x v w u =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ∑ i : Fin (Module.finrank ℝ E),
          (b.repr v j * b.repr w k * b.repr u i) •
            riemannOp (cov := LeviCivita (I := I) g) x (b j) (b k) (b i) := by
    -- Step 1: linearise in the first slot via `Module.Basis.sum_repr`.
    have h1 : riemannOp (cov := LeviCivita (I := I) g) x v =
        ∑ j : Fin (Module.finrank ℝ E),
          b.repr v j • riemannOp (cov := LeviCivita (I := I) g) x (b j) := by
      conv_lhs => rw [hv]
      set f : TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
          riemannOp (cov := LeviCivita (I := I) g) x with hf_def
      change f (∑ j : Fin (Module.finrank ℝ E), b.repr v j • b j) =
          ∑ j : Fin (Module.finrank ℝ E), b.repr v j • f (b j)
      rw [map_sum f]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact f.map_smul (b.repr v j) (b j)
    -- Step 2: apply to w; linearise in the second slot.
    have h2 : riemannOp (cov := LeviCivita (I := I) g) x v w =
        ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          (b.repr v j * b.repr w k) •
            riemannOp (cov := LeviCivita (I := I) g) x (b j) (b k) := by
      rw [h1, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h_smul : (b.repr v j • riemannOp (cov := LeviCivita (I := I) g) x (b j)) w =
          b.repr v j • riemannOp (cov := LeviCivita (I := I) g) x (b j) w := rfl
      rw [h_smul]
      have h_inner : riemannOp (cov := LeviCivita (I := I) g) x (b j) w =
          ∑ k : Fin (Module.finrank ℝ E),
            b.repr w k • riemannOp (cov := LeviCivita (I := I) g) x (b j) (b k) := by
        conv_lhs => rw [hw]
        set f : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
          riemannOp (cov := LeviCivita (I := I) g) x (b j) with hf_def
        change f (∑ k : Fin (Module.finrank ℝ E), b.repr w k • b k) =
            ∑ k : Fin (Module.finrank ℝ E), b.repr w k • f (b k)
        rw [map_sum f]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact f.map_smul (b.repr w k) (b k)
      rw [h_inner, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul]
    -- Step 3: apply to u; linearise in the third slot.
    rw [h2]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h_smul :
        ((b.repr v j * b.repr w k) •
            riemannOp (cov := LeviCivita (I := I) g) x (b j) (b k)) u =
        (b.repr v j * b.repr w k) •
            riemannOp (cov := LeviCivita (I := I) g) x (b j) (b k) u := rfl
    rw [h_smul]
    have h_inner : riemannOp (cov := LeviCivita (I := I) g) x (b j) (b k) u =
        ∑ i : Fin (Module.finrank ℝ E),
          b.repr u i • riemannOp (cov := LeviCivita (I := I) g) x (b j) (b k) (b i) := by
      conv_lhs => rw [hu]
      set f : TangentSpace I x →L[ℝ] TangentSpace I x :=
        riemannOp (cov := LeviCivita (I := I) g) x (b j) (b k) with hf_def
      change f (∑ i : Fin (Module.finrank ℝ E), b.repr u i • b i) =
          ∑ i : Fin (Module.finrank ℝ E), b.repr u i • f (b i)
      rw [map_sum f]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact f.map_smul (b.repr u i) (b i)
    rw [h_inner, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
  -- Now expand the RHS `chartRiemannCLM x v w u` symmetrically.
  have hRHS : chartRiemannCLM (I := I) g x v w u =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ∑ i : Fin (Module.finrank ℝ E),
          (b.repr v j * b.repr w k * b.repr u i) •
            chartRiemannCLM (I := I) g x (b j) (b k) (b i) := by
    have h1 : chartRiemannCLM (I := I) g x v =
        ∑ j : Fin (Module.finrank ℝ E),
          b.repr v j • chartRiemannCLM (I := I) g x (b j) := by
      conv_lhs => rw [hv]
      set f : TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
          chartRiemannCLM (I := I) g x with hf_def
      change f (∑ j : Fin (Module.finrank ℝ E), b.repr v j • b j) =
          ∑ j : Fin (Module.finrank ℝ E), b.repr v j • f (b j)
      rw [map_sum f]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact f.map_smul (b.repr v j) (b j)
    have h2 : chartRiemannCLM (I := I) g x v w =
        ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          (b.repr v j * b.repr w k) • chartRiemannCLM (I := I) g x (b j) (b k) := by
      rw [h1, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h_smul : (b.repr v j • chartRiemannCLM (I := I) g x (b j)) w =
          b.repr v j • chartRiemannCLM (I := I) g x (b j) w := rfl
      rw [h_smul]
      have h_inner : chartRiemannCLM (I := I) g x (b j) w =
          ∑ k : Fin (Module.finrank ℝ E),
            b.repr w k • chartRiemannCLM (I := I) g x (b j) (b k) := by
        conv_lhs => rw [hw]
        set f : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
          chartRiemannCLM (I := I) g x (b j) with hf_def
        change f (∑ k : Fin (Module.finrank ℝ E), b.repr w k • b k) =
            ∑ k : Fin (Module.finrank ℝ E), b.repr w k • f (b k)
        rw [map_sum f]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact f.map_smul (b.repr w k) (b k)
      rw [h_inner, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul]
    rw [h2, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h_smul : ((b.repr v j * b.repr w k) • chartRiemannCLM (I := I) g x (b j) (b k)) u =
        (b.repr v j * b.repr w k) • chartRiemannCLM (I := I) g x (b j) (b k) u := rfl
    rw [h_smul]
    have h_inner : chartRiemannCLM (I := I) g x (b j) (b k) u =
        ∑ i : Fin (Module.finrank ℝ E),
          b.repr u i • chartRiemannCLM (I := I) g x (b j) (b k) (b i) := by
      conv_lhs => rw [hu]
      -- The two-slot-applied chartRiemannCLM is a CLM `T_x M →L T_x M`. Apply `map_sum`
      -- through the explicit hom-class instance.
      set f : TangentSpace I x →L[ℝ] TangentSpace I x :=
        chartRiemannCLM (I := I) g x (b j) (b k) with hf_def
      change f (∑ i : Fin (Module.finrank ℝ E), b.repr u i • b i) =
          ∑ i : Fin (Module.finrank ℝ E), b.repr u i • f (b i)
      rw [map_sum f]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact f.map_smul (b.repr u i) (b i)
    rw [h_inner, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
  rw [hLHS, hRHS]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hbasis i j k]

/-! ## Basis-coordinate Ricci identification (swap form)

Combining `ricciTensor_apply_basisSum` with the trilinear bridge gives the basis-sum
expansion of the abstract Ricci tensor in terms of the chart-Riemann entries. The
resulting sum pairs `(v, w)` with the chart Ricci entries `Rc_{i,k}` in *swapped* index
order, reflecting the convention difference between the abstract trace and the chart
contraction. -/

/-- **Basis expansion of the abstract Ricci tensor via the chart Ricci entries (swap
form).** Under the basis-coordinate identification, the abstract Ricci tensor admits the
explicit chart-coordinate sum
`ricciTensor g x v w = ∑ i k, v^k * w^i * Rc_{i, k}(x, ϕ_x x)`,
where `(v^k, w^i) := ((b.repr v) k, (b.repr w) i)`. The pairing is `v` with the second
chart-Ricci index and `w` with the first chart-Ricci index — opposite to `ricciFun`'s
pairing. -/
theorem ricciTensor_eq_chartRicciSwap_of_basis_identity
    (g : SmoothRiemannianMetric I M) (x : M)
    (h : chartRiemannBasisIdentity (I := I) g x)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) g x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr v) k *
            ((Module.finBasis ℝ E).repr w) i *
            chartRicciTensor (I := I) g x i k (extChartAt I x x) := by
  classical
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hb_def
  -- Step 1: rewrite ricciTensor via the basis-sum trace formula.
  rw [ricciTensor_apply_basisSum]
  -- Step 2: each summand `b.repr (riemannOp x e_t v w) t` equals
  -- `b.repr (chartRiemannCLM x e_t v w) t` by the trilinear bridge.
  have hrewrite_term : ∀ t : Fin (Module.finrank ℝ E),
      (b.repr (riemannOp (cov := LeviCivita (I := I) g) x (b t) v w)) t =
        (b.repr (chartRiemannCLM (I := I) g x (b t) v w)) t := by
    intro t
    rw [riemannOp_eq_chartRiemannCLM_apply_of_basis_identity (I := I) g x h (b t) v w]
  -- Step 3: compute `b.repr (chartRiemannCLM x e_t v w) t` via the quadruple sum.
  -- chartRiemannCLM x e_t v w = ∑ i j k l (b.repr w i * b.repr (e_t) j * b.repr v k * R^l_{ijk}) • e_l
  -- Then b.repr ... t = ∑ i k δ_{tj=t}-collapsed: ∑ i k w^i * v^k * R^t_{i, t, k}.
  have h_chart_term : ∀ t : Fin (Module.finrank ℝ E),
      (b.repr (chartRiemannCLM (I := I) g x (b t) v w)) t =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (b.repr w) i * (b.repr v) k *
              chartRiemannTensor (I := I) g x i t k t (extChartAt I x x) := by
    intro t
    -- Expand `chartRiemannCLM x e_t v w` via `chartRiemannCLM_apply`.
    rw [chartRiemannCLM_apply]
    -- The sum: ∑ i j k l (b.repr w i * b.repr (e_t) j * b.repr v k * R^l_{ijk}) • e_l.
    -- b.repr (∑ ... • e_l) t = ∑ ... * δ_{lt} — collapse l = t.
    rw [map_sum]; rw [Finsupp.coe_finset_sum]; rw [Finset.sum_apply]
    -- Move the collapsing l = t inside.
    -- We collapse the inner-most l-sum first.
    -- Goal: ∑_i (b.repr (∑_j ∑_k ∑_l c_ijkl • e_l) t) = ∑_i ∑_k w^i v^k R^t_{itk}.
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]; rw [Finsupp.coe_finset_sum]; rw [Finset.sum_apply]
    -- Goal: ∑_j (b.repr (∑_k ∑_l c_ijkl • e_l) t) = (the i-summand on RHS).
    -- We collapse the j-sum to j = t (since b.repr (e_t) j = δ_{tj}).
    -- First expand:
    -- A small helper: compute `b.repr (c • b l) t = c * (if l = t then 1 else 0)`.
    have h_smul_repr : ∀ (c : ℝ) (l : Fin (Module.finrank ℝ E)),
        ((b.repr (c • (b l : E))) t : ℝ) = c * (if l = t then (1 : ℝ) else 0) := by
      intro c l
      rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
      rw [Module.Basis.repr_self_apply]
    rw [Finset.sum_eq_single t]
    · -- At j = t: the inner k, l sums remain; collapse l = t.
      rw [map_sum]; rw [Finsupp.coe_finset_sum]; rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_sum]; rw [Finsupp.coe_finset_sum]; rw [Finset.sum_apply]
      rw [Finset.sum_eq_single t]
      · -- At l = t: collapse `b.repr (c • e_t) t` to `c * 1 = c`.
        rw [h_smul_repr]
        rw [if_pos rfl, mul_one]
        -- Now compute `b.repr (e_t) t = 1` inside the coefficient `c`.
        rw [show ((b.repr (b t)) t : ℝ) = 1 by
          rw [Module.Basis.repr_self_apply]; rw [if_pos rfl]]
        ring
      · intro l _ hl_ne
        rw [h_smul_repr]
        rw [if_neg hl_ne, mul_zero]
      · intro hl
        exact absurd (Finset.mem_univ t) hl
    · intro j _ hj_ne
      -- At j ≠ t: `b.repr (e_t) j = 0`, so the product is 0.
      rw [map_sum]; rw [Finsupp.coe_finset_sum]; rw [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro k _
      rw [map_sum]; rw [Finsupp.coe_finset_sum]; rw [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro l _
      rw [h_smul_repr]
      -- The coefficient contains `b.repr (e_t) j = if t = j then 1 else 0`. Since
      -- `j ≠ t`, we have `t ≠ j`, hence the value is 0.
      have htj : ¬ (t = j) := fun h => hj_ne h.symm
      rw [show ((b.repr (b t)) j : ℝ) = 0 by
        rw [Module.Basis.repr_self_apply]; rw [if_neg htj]]
      ring
    · intro hj
      exact absurd (Finset.mem_univ t) hj
  -- Combine.
  have h_combined : ∀ t : Fin (Module.finrank ℝ E),
      (b.repr (riemannOp (cov := LeviCivita (I := I) g) x (b t) v w)) t =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (b.repr w) i * (b.repr v) k *
              chartRiemannTensor (I := I) g x i t k t (extChartAt I x x) := by
    intro t
    rw [hrewrite_term t, h_chart_term t]
  -- Now sum over t.
  rw [Finset.sum_congr rfl (fun t _ => h_combined t)]
  -- Goal: ∑ t ∑ i ∑ k (w^i * v^k * R^t_{itk}) = ∑ i ∑ k v^k * w^i * Rc_{i, k}.
  -- Reorder: bring the t-sum innermost, then identify ∑ t R^t_{itk} = Rc_{i, k}.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  -- ∑ t (w^i * v^k * R^t_{itk}) = (v^k * w^i) * Rc_{i,k}.
  rw [chartRicciTensor_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- **Swap-form Ricci bridge.** Under the basis-coordinate identification, the chart
Ricci carrier `ricciFun g x v w` equals the abstract Ricci tensor `ricciTensor g x w v`
with arguments swapped. This identity holds without any symmetry hypothesis: the
swap absorbs the abstract / chart convention difference. -/
theorem ricciFun_eq_ricciTensor_swap_of_basis_identity
    (g : SmoothRiemannianMetric I M) (x : M)
    (h : chartRiemannBasisIdentity (I := I) g x)
    (v w : TangentSpace I x) :
    ricciFun (I := I) g x v w = ricciTensor (I := I) g x w v := by
  classical
  rw [ricciFun_apply, ricciTensor_eq_chartRicciSwap_of_basis_identity (I := I) g x h]
  -- LHS: ∑ i ∑ k v^i * w^k * Rc_{i, k}.
  -- RHS (with v ↔ w swapped): ∑ i' ∑ k' w^{k'} * v^{i'} * Rc_{i', k'}.
  -- The two are equal term by term up to (i ↔ i', k ↔ k') and a commutativity of *.
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Direct Ricci bridge under closed-manifold hypothesis.** Under the basis-coordinate
identification together with `[I.Boundaryless]`, the chart Ricci carrier `ricciFun g x`
equals the abstract Ricci tensor `ricciTensor g x` as bilinear forms on `T_x M`. The
boundaryless hypothesis discharges the chart-level Ricci symmetry
`Rc_{i, k} = Rc_{k, i}` (via `chartRicciTensor_symm_of_boundaryless`), which absorbs the
swap arising from the abstract / chart convention difference. -/
theorem ricciFun_eq_ricciTensor_of_basis_identity [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (h : chartRiemannBasisIdentity (I := I) g x)
    (v w : TangentSpace I x) :
    ricciFun (I := I) g x v w = ricciTensor (I := I) g x v w := by
  classical
  -- Combine the swap form with Ricci symmetry via the abstract `ricciTensor_symm`.
  rw [ricciFun_eq_ricciTensor_swap_of_basis_identity (I := I) g x h v w]
  exact ricciTensor_symm (I := I) g x w v

end Connection
end Integral
end DifferentialGeometry
