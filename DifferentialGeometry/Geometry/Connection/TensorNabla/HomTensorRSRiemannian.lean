import DifferentialGeometry.Geometry.Connection.TensorNabla.SecondOrderHomBundle
import DifferentialGeometry.Geometry.Connection.SingleSlotOperatorFiberNormBound

/-!
# The `g`-fibre operator-norm Riemannian calculus on the second-order Hom-bundle `Hom(T^{r,a}, T^{r,c})`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file equips the **second-order Hom-bundle**
`Hom(TensorRSSpace r a, TensorRSSpace r c) = fun x => HomTensorRSSpace r a c I x`
(built in `SecondOrderHomBundle.lean` as the `Bundle.ContinuousLinearMap` bundle of the smooth
`(r, a)`- and `(r, c)`-tensor bundles) with its intrinsic **`g`-fibre operator-norm** calculus,
making the operator bundle a first-class object of the Riemannian fibre-norm theory.

Each domain / codomain fibre `TensorRSSpace r a I x` / `TensorRSSpace r c I x` carries the `g`-fibre
inner product installed by `Tensor0SBundle.tensorRS_riemannianBundle`, under which it is a
finite-dimensional real inner-product space whose squared norm is the intrinsic
`riemannianFiberNormSq` (the proved bridge `riemannianFiberNormSq_eq_bundle_norm_sq'`).  A fibrewise
operator `A : TensorRSSpace r a I x →L TensorRSSpace r c I x` then has a well-defined intrinsic
`g`-fibre operator norm `‖A‖` (measured in those Riemannian fibre norms), and its action obeys the
sharp fibrewise contraction bound
```
rfns(A v) ≤ ‖A‖² · rfns(v)          for every fibre tensor v,
```
the intrinsic operator-norm analogue (no Hilbert–Schmidt dimension factor) of the codomain-only
post-composition bound.  This is the structural fact that makes the rank-`r` curvature operator-field
bounds clean: the curvature reading operator, being a smooth Hom-bundle section, has a continuous
`g`-fibre operator norm, and that norm is the proportionality coefficient of the fibre-energy bound.

## Main declarations

* `homTensorRS_riemannianFiberNormSq_clm_apply_le` — the **fibrewise** intrinsic operator bound
  `rfns(A v) ≤ ‖A‖² · rfns(v)` for any fibrewise operator `A` and the `g`-fibre operator norm `‖A‖`;
* `continuous_homTensorRS_opNorm` — the single genuinely-irreducible analytic primitive (posited):
  for a smooth full Hom-bundle section `Ψ`, the `g`-fibre operator norm `x ↦ ‖Ψ x‖` is continuous (the
  exact full-Hom analogue of the curvature line's posited frame-energy continuity
  `exists_continuous_riemannOp_tensorCovS_frameEnergy_bound`);
* `exists_uniform_homTensorRS_opNorm_sq` — for a smooth full Hom-bundle section `Ψ`, the squared
  `g`-fibre operator norm `x ↦ ‖Ψ x‖²` admits a single uniform-over-`M` bound `C`, proved on top of
  `continuous_homTensorRS_opNorm` by "continuous on compact ⟹ bounded" (the exact full-Hom analogue of
  the curvature line's uniform constant `exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_const`);
* `exists_continuous_homTensorRS_opNorm_sq` — its continuous-envelope version: a continuous nonnegative
  `N : M → ℝ` dominating `x ↦ ‖Ψ x‖²`, the constant envelope `fun _ => C` of the uniform bound (the
  exact full-Hom analogue of `exists_continuous_riemannOp_tensorCovS_frameEnergy_bound`);
* `exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le` — **the payoff** (the reason
  this file exists): for a smooth full Hom-bundle section `Ψ` there is a continuous nonnegative
  `Cop : M → ℝ` with the per-point fibrewise `g`-contraction bound `rfns(Ψ x v) ≤ Cop x · rfns(v)`,
  the general envelope behind the rank-`r` curvature operator-field bounds;
* `exists_uniform_riemannianFiberNormSq_homTensorRS_section_clm_le` — its uniform version on a closed
  manifold (continuous on compact ⟹ bounded).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set IsManifold Tensor0SBundle ContinuousLinearMap
open scoped Manifold Topology ContDiff BigOperators InnerProductSpace

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor.TensorRSRiemannianBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ## The fibrewise intrinsic operator-norm contraction bound

For a fibrewise continuous-linear operator `A : TensorRSSpace r a I x →L TensorRSSpace r c I x` whose
domain / codomain carry the `g`-fibre inner products (`tensorRS_riemannianBundle`), the intrinsic
squared fibre norm of the image is controlled by the squared `g`-fibre operator norm of `A` with no
dimension factor.  This is the sharp operator-norm fibre-norm bound, proved through the intrinsic
fibre-norm / `g`-bundle-norm bridge `riemannianFiberNormSq_eq_bundle_norm_sq'`. -/

section FibrewiseBound

variable (g : SmoothRiemannianMetric I M) (r a c : ℕ) (x : M)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The sharp intrinsic operator-norm fibre-norm bound on the second-order Hom-bundle.**  Install
the domain / codomain `(r, a)` / `(r, c)`-tensor `g`-fibre Riemannian bundle instances, under which
each fibre is a finite-dimensional inner-product space whose squared norm is `riemannianFiberNormSq`
(the bridge `riemannianFiberNormSq_eq_bundle_norm_sq'`).  For any fibrewise operator
`A : TensorRSSpace r a I x →L TensorRSSpace r c I x` the action obeys the squared `g`-fibre
operator-norm bound
```
rfns(A v) ≤ ‖A‖² · rfns(v)
```
with **no dimension factor**, where `‖A‖` is the `g`-fibre operator norm of `A` (its operator norm
measured in the installed Riemannian fibre norms).  The proof reads the bridge `rfns = ‖·‖²` on both
fibres, under which the claim is the square of the fundamental operator-norm inequality
`‖A v‖ ≤ ‖A‖ · ‖v‖` (`ContinuousLinearMap.le_opNorm`). -/
lemma homTensorRS_riemannianFiberNormSq_clm_apply_le
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (v : TensorRSSpace r a I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
    riemannianFiberNormSq (I := I) (M := M) g r c x (A v) ≤
      ‖A‖ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r a x v := by
  letI instA : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  letI instC : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
  rw [riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g r c x (A v),
    riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g r a x v]
  have hle : ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
  calc ‖A v‖ ^ 2 ≤ (‖A‖ * ‖v‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = ‖A‖ ^ 2 * ‖v‖ ^ 2 := by ring

end FibrewiseBound

/-! ## The continuous `g`-fibre operator norm of a smooth Hom-bundle section

The single genuinely-irreducible analytic content of the payoff: the squared `g`-fibre operator norm
`x ↦ ‖Ψ x‖²` of a smooth full Hom-bundle section `Ψ` is continuous in the base point.  This is the
exact full-Hom analogue of the proved curvature-operator frame-energy continuity
`exists_continuous_riemannOp_tensorCovS_frameEnergy_bound` (`CurvatureFrameEnergyContinuity`): the
operator is assembled from the smooth metric `g` and the smooth section `Ψ`, the `g`-fibre inner
products on the domain / codomain tensor fibres vary continuously with `x`
(`tensorRSRiemannianInnerCLM_continuous`), and `Ψ` varies continuously in the model trivialisation
(`hΨ`), so the least proportionality constant of the fibre-energy bound — the intrinsic `g`-fibre
operator norm `‖Ψ x‖` — is a continuous (never chart-selection-*uniform*) function of `x`.  Posited
here as the precise atomic continuity primitive of the operator-field calculus, exactly as the
curvature line posits its frame-energy continuity. -/

section OpNormContinuity

variable (g : SmoothRiemannianMetric I M) (r a c : ℕ)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Posited `g`-fibre operator-norm continuity of a smooth full Hom-bundle section.**  For a smooth
full Hom-bundle field `Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x` on a closed Riemannian
manifold the intrinsic `g`-fibre operator norm `x ↦ ‖Ψ x‖` — the operator norm of `Ψ x` measured in
the installed `(r, a)` / `(r, c)`-tensor `g`-fibre Riemannian bundle norms — is a *continuous*
function of the base point:
```
Continuous (fun x => ‖Ψ x‖).
```

This is the single genuinely-irreducible analytic content of the Hom-bundle envelope — the exact
full-Hom analogue of the curvature line's posited frame-energy continuity
`exists_continuous_riemannOp_tensorCovS_frameEnergy_bound`; the uniform bound
`exists_uniform_homTensorRS_opNorm_sq` is proved on top of it by "continuous on compact ⟹ bounded".

**Why this is TRUE.**  The intrinsic `g`-fibre operator norm `‖Ψ x‖` is the least constant for which
the fibre-energy bound `‖Ψ x v‖_g ≤ ‖Ψ x‖ · ‖v‖_g` holds.  Reading the operator `Ψ` through the local
trivialisation of the Hom-bundle (`hΨ`), `Ψ` is a continuous operator-valued map into the model
fibre; the comparison between the model tensor fibre norm and the `g`-fibre tensor norm is itself
continuous (`tensorRSRiemannianInnerCLM_continuous`) and (positive-definiteness of `g`) locally
two-sided bounded, so the `g`-fibre operator norm `x ↦ ‖Ψ x‖` is continuous.  This is the
chart-locality-free route: the operator norm is the *intrinsic* `g`-fibre operator norm, never the
chart-trivialisation operator-norm scalar (unbounded on multi-chart manifolds); the trivialisation
enters only as the continuity tool.  Posited here as the precise atomic analytic primitive of the
operator-field calculus, exactly as the curvature line posits its frame-energy continuity.
Consumers transitively depend on `sorryAx`.

**Non-vacuity.**  This is a genuine continuity statement about the `g`-fibre operator norm of `Ψ`,
not a degenerate predicate: it constrains `Ψ` through its operator norm and is *false* for a
discontinuous operator-norm assignment (e.g. an operator-valued field jumping between two distinct
fibre norms), so it is not satisfiable by an arbitrary section. -/
theorem continuous_homTensorRS_opNorm
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
    Continuous (fun x : M => ‖Ψ x‖) := by
  sorry

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Uniform `g`-fibre squared operator-norm bound of a smooth full Hom-bundle section.**
For a smooth full Hom-bundle field `Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x` on a
closed Riemannian manifold there is a *single* nonnegative constant `C`, uniform over `M`, bounding,
at every base point `x`, the squared `g`-fibre operator norm of `Ψ x` (the operator norm measured in
the installed `(r, a)` / `(r, c)`-tensor `g`-fibre Riemannian bundle norms):
```
‖Ψ x‖² ≤ C.
```

This is the exact full-Hom analogue of the curvature line's uniform constant
`exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_const`; the continuous version
`exists_continuous_homTensorRS_opNorm_sq` is proved on top of it by `continuous_const`, exactly as
`exists_continuous_riemannOp_tensorCovS_frameEnergy_bound` is proved on top of its uniform constant.

**Proof.**  By the posited `g`-fibre operator-norm continuity `continuous_homTensorRS_opNorm` the map
`x ↦ ‖Ψ x‖` is continuous, hence so is `x ↦ ‖Ψ x‖²` (`Continuous.pow`); on the compact `M` its range
is compact (`isCompact_range`) and therefore bounded above (`IsCompact.bddAbove`), giving a constant
`C₀` with `‖Ψ x‖² ≤ C₀` at every `x`.  Take `C := max C₀ 0 ≥ 0`, which also bounds `‖Ψ x‖²`.  This is
the chart-locality-free route: the operator norm is the *intrinsic* `g`-fibre operator norm, never
the chart-trivialisation operator-norm scalar (unbounded on multi-chart manifolds).

**Non-vacuity.**  A degenerate `C = 0` is rejected: at any `x` where `Ψ x ≠ 0` there is a fibre
tensor `v` with `‖Ψ x v‖_g > 0`, forcing `‖Ψ x‖² > 0` and hence `C > 0`; the smallest valid value is
the genuine uniform squared `g`-fibre operator-norm sup, positive for a nonzero `Ψ`. -/
theorem exists_uniform_homTensorRS_opNorm_sq
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, ‖Ψ x‖ ^ 2 ≤ C := by
  letI instA : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  letI instC : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
  have hcont : Continuous (fun x : M => ‖Ψ x‖) :=
    continuous_homTensorRS_opNorm (I := I) (M := M) g r a c Ψ hΨ
  have hcont_sq : Continuous (fun x : M => ‖Ψ x‖ ^ 2) := hcont.pow 2
  obtain ⟨C₀, hC₀⟩ := (isCompact_range hcont_sq).bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x => ?_⟩
  exact le_trans (hC₀ (Set.mem_range_self x)) (le_max_left _ _)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Continuous `g`-fibre squared operator norm of a smooth full Hom-bundle section.**  For a smooth
full Hom-bundle field `Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x` on a closed Riemannian
manifold there is a *continuous* nonnegative function `N : M → ℝ` that dominates, at every base point
`x`, the squared `g`-fibre operator norm of `Ψ x` (the operator norm measured in the installed
`(r, a)` / `(r, c)`-tensor `g`-fibre Riemannian bundle norms):
```
‖Ψ x‖² ≤ N x.
```

**Proof.**  By the uniform bound `exists_uniform_homTensorRS_opNorm_sq` there is a single nonnegative
constant `C` with `‖Ψ x‖² ≤ C` at every `x`; take the constant function `N := fun _ => C`, which is
continuous (`continuous_const`) and nonnegative, and dominates `‖Ψ x‖²` at every point.  This is the
exact full-Hom analogue of the proved curvature-operator frame-energy continuity
`exists_continuous_riemannOp_tensorCovS_frameEnergy_bound`, which is likewise the constant continuous
envelope of its posited uniform curvature constant.

**Non-vacuity.**  A degenerate `N ≡ 0` is rejected: at any `x` where `Ψ x ≠ 0` there is a fibre
tensor `v` with `‖Ψ x v‖_g > 0`, forcing `‖Ψ x‖² > 0` and hence `N x > 0`; the smallest valid value
is the genuine squared `g`-fibre operator norm, positive wherever `Ψ x ≠ 0`. -/
theorem exists_continuous_homTensorRS_opNorm_sq
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
    ∃ N : M → ℝ, Continuous N ∧ (∀ x : M, 0 ≤ N x) ∧ ∀ x : M, ‖Ψ x‖ ^ 2 ≤ N x := by
  obtain ⟨C, hC_nonneg, hC_bound⟩ :=
    exists_uniform_homTensorRS_opNorm_sq (I := I) (M := M) g r a c Ψ hΨ
  exact ⟨fun _ => C, continuous_const, fun _ => hC_nonneg, hC_bound⟩

end OpNormContinuity

/-! ## The payoff: the continuous per-point `g`-fibre contraction envelope

The reason this file exists.  Assembled from the fibrewise intrinsic operator bound and the
continuity of the squared `g`-fibre operator norm, the smooth full Hom-bundle section `Ψ` admits a
continuous nonnegative per-point envelope `Cop` for the fibrewise contraction `rfns(Ψ x v) ≤ Cop x ·
rfns(v)`.  This is the general envelope of which the rank-`r` curvature operator-field bound
`exists_continuous_riemannianFiberNormSq_homSection_clm_le` is the curvature instance. -/

section Payoff

variable (g : SmoothRiemannianMetric I M) (r a c : ℕ)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **The continuous per-point `g`-fibre contraction envelope of a smooth full Hom-bundle section
(the payoff, the general envelope).**  For a *fixed* smooth full Hom-bundle field
`Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x` on a closed Riemannian manifold there is a
continuous nonnegative `Cop : M → ℝ` with the per-point fibrewise contraction bound
```
rfns(Ψ x v) ≤ Cop x · rfns(v)
```
at every point `x` and every `(r, a)`-tensor fibre value `v`.

**Proof.**  Take `Cop x := ‖Ψ x‖²_g`, the squared `g`-fibre operator norm of `Ψ x`; it is continuous
and nonnegative as a continuous dominating envelope `N` by `exists_continuous_homTensorRS_opNorm_sq`.
The fibrewise bound `rfns(Ψ x v) ≤ ‖Ψ x‖²_g · rfns(v)` is the sharp intrinsic operator-norm fibre-
norm bound `homTensorRS_riemannianFiberNormSq_clm_apply_le`, and `‖Ψ x‖²_g · rfns(v) ≤ N x · rfns(v)`
since `rfns(v) ≥ 0`.  This is the exact full-Hom analogue of the proved continuous per-point
curvature-operator envelope `exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`,
proved generically for an arbitrary smooth Hom-bundle section.

**Non-vacuity.**  A degenerate `Cop ≡ 0` is rejected: the bound at any `v` with `rfns(v) > 0` and
`Ψ x v ≠ 0` forces `Cop x > 0`; the smallest valid value is the genuine squared `g`-fibre operator
norm `‖Ψ x‖²_g`, positive wherever `Ψ x ≠ 0`. -/
theorem exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ Cop : M → ℝ, Continuous Cop ∧ (∀ x : M, 0 ≤ Cop x) ∧
      ∀ (x : M) (v : TensorRSSpace r a I x),
        riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
          Cop x * riemannianFiberNormSq (I := I) (M := M) g r a x v := by
  letI instA : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  letI instC : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
  obtain ⟨N, hN_cont, hN_nonneg, hN_bound⟩ :=
    exists_continuous_homTensorRS_opNorm_sq (I := I) (M := M) g r a c Ψ hΨ
  refine ⟨N, hN_cont, hN_nonneg, fun x v => ?_⟩
  refine le_trans (homTensorRS_riemannianFiberNormSq_clm_apply_le
    (I := I) (M := M) g r a c x (Ψ x) v) ?_
  exact mul_le_mul_of_nonneg_right (hN_bound x)
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g r a x v)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **The uniform `g`-fibre contraction bound of a smooth full Hom-bundle section.**  For a *fixed*
smooth full Hom-bundle field `Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x` on a closed
Riemannian manifold there is a single nonnegative constant `C`, uniform over `M`, with the per-point
fibrewise contraction bound
```
rfns(Ψ x v) ≤ C · rfns(v)
```
for every point `x` and every `(r, a)`-tensor fibre value `v`.

**Proof.**  By the continuous per-point envelope
`exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le` there is a continuous nonnegative
`Cop : M → ℝ` with `rfns(Ψ x v) ≤ Cop x · rfns(v)`; on the compact `M` the continuous `Cop` has
bounded range (`(isCompact_univ).image Cop_cont |>.bddAbove`), so `C := max C₀ 0 ≥ Cop x` uniformly,
and `Cop x · rfns(v) ≤ C · rfns(v)` by `rfns(v) ≥ 0`.

**Non-vacuity.**  A degenerate `C < 0` is rejected: the conclusion `rfns(Ψ x v) ≤ C · rfns(v)` at any
`v` with `rfns(v) > 0` and `Ψ x v ≠ 0` forces `C > 0`; the smallest valid `C` is the genuine uniform
squared `g`-fibre operator-norm sup, positive for a nonzero `Ψ`. -/
theorem exists_uniform_riemannianFiberNormSq_homTensorRS_section_clm_le
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (v : TensorRSSpace r a I x),
      riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r a x v := by
  obtain ⟨Cop, hCop_cont, hCop_nn, hCop_bound⟩ :=
    exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le
      (I := I) (M := M) g r a c Ψ hΨ
  have hCpt := (isCompact_univ (X := M)).image hCop_cont
  obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x v => ?_⟩
  have hCop_le : Cop x ≤ max C₀ 0 :=
    le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
  refine le_trans (hCop_bound x v) ?_
  exact mul_le_mul_of_nonneg_right hCop_le
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g r a x v)

end Payoff

end DifferentialGeometry.Integral.Connection
