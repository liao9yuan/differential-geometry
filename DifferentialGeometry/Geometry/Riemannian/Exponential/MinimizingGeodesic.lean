import DifferentialGeometry.Geometry.Riemannian.Exponential.IntrinsicExp
import DifferentialGeometry.Geometry.Riemannian.Exponential.IntrinsicExpContinuity
import DifferentialGeometry.Geometry.Riemannian.GaussLemma
import DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
import Mathlib.Topology.Order.Compact
import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option linter.unusedSectionVars false

/-!
# Hopf–Rinow minimising-geodesic existence via the ray/sphere argument

For a complete Riemannian manifold the intrinsic exponential map
`expMapIntrinsic g hEnorm p v = intrinsicGeodesic g hEnorm p v 1`
(`Exponential/IntrinsicExp.lean`) follows the *complete* moving-foot geodesic
through `p` with launch velocity `v`.  Unlike the chart-fixed `expMap`, this
object is genuinely defined and geodesic across charts (and continuous in `v`,
`expMapIntrinsic_continuous`).  This file works towards the velocity-identified
Hopf–Rinow surjectivity

`∀ p q, ∃ v, expMapIntrinsic g hEnorm p v = q ∧
    √(g_p(v, v)) = (riemannianEDist I p q).toReal`,

i.e. every `q` is reached by a radial geodesic whose `g`-speed equals the
Riemannian distance.  (There is no `riemannianDist` definition in the project;
the real-valued Riemannian distance is `(riemannianEDist I p q).toReal`, and the
velocity bound is the intrinsic `g`-norm `√(g_p(v, v))`, never the model-`E`
norm `‖v‖`.)

## The classical ray/sphere argument

Let `r := (riemannianEDist I p q).toReal`.  If `r = 0` then `q = p` and `v := 0`
works.  Otherwise pick `δ ∈ (0, expRadiusGp g p)` and form the **sphere**
`S_δ := { expMapIntrinsic g hEnorm p (δ • w) | √(g_p(w, w)) = 1 }`, the
continuous image of the compact `g`-unit sphere, hence compact.  Choose
`x₀ := expMapIntrinsic g hEnorm p (δ • u)` minimising `q ↦ riemannianEDist · q`
over `S_δ`.  The triangle inequality plus the Gauss-lemma radial local minimality
`normalBall_radial_unique_minimizer` give `riemannianEDist x₀ q = r - δ` (the
"ray jumps onto the sphere" step).  Tracking the unit-speed radial geodesic
`γ(t) := expMapIntrinsic g hEnorm p (t • u)` (defined for all `t` by
completeness) and the propagation set

`A := { t ∈ [0, r] | (riemannianEDist I (γ t) q).toReal = r - t }`,

one shows `A` is closed, `δ ∈ A`, and `sup A = r` (repeating the sphere argument
at `γ(t₀)` whenever `t₀ := sup A < r`).  At `t = r`, `riemannianEDist (γ r) q = 0`
forces `γ r = q`, so `v := r • u` realises the conclusion (`√(g_p(r•u, r•u)) =
r·√(g_p(u,u)) = r` by homogeneity and `√(g_p(u,u)) = 1`).

## What this file establishes unconditionally

* `gInner_smul_self` / `sqrt_gInner_smul_self` — the degree-two homogeneity of
  the `g`-quadratic form and its square root.
* `gUnitSphere_isCompact` — the `g`-unit sphere `{w | g_p(w, w) = 1}` in `T_p M`
  is compact (closed equalizer inside the compact closed `g`-ball, in the proper
  finite-dimensional tangent space).
* `intrinsicSphere_isCompact` — the image `S_δ` of the `g`-unit sphere under
  `w ↦ expMapIntrinsic g hEnorm p (δ • w)` is compact (continuous image of a
  compact set, via the proven `expMapIntrinsic_continuous`).
* `exists_min_riemannianEDist_on_intrinsicSphere` — the sphere-minimisation step
  (`IsCompact.exists_isMinOn` on the continuous `riemannianEDist · q`).
* `propagationSet_isClosed` — closedness of the propagation set `A`.
* `riemannianEDist_eq_zero_imp_eq` — point separation (the `r = 0` base case
  reduction `riemannianEDist I p q = 0 → p = q`).
* `riemannianEDist_ne_top` — finiteness of the Riemannian distance (so that
  `(riemannianEDist I p q).toReal` is informative).

## Residual (single isolated analytic input)

The remaining input is the ray/sphere **propagation** `sup A = r`, which requires
the Gauss-lemma radial local minimality *re-based at the moving foot point*
`γ(t₀)` (the equality case of `normalBall_radial_unique_minimizer`, together with
the cross-chart geodesic-continuation identifying `expMap g (γ t₀) w` with the
continuation of `intrinsicGeodesic g hEnorm p (t₀ • u)`).  These are exactly the
still-pending geometric inputs flagged in `RadialSurjectivity.lean` /
`HopfRinow.unit_speed_minimising_geodesic_from_points`.  The single remaining
`sorry` is the headline `expMapIntrinsic_surjective_dist`; its sub-lemma
decomposition is in its docstring.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-! ## 1. Homogeneity of the `g`-quadratic form -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Degree-two homogeneity of the `g`-quadratic form.**
`g.inner p (b • v) (b • v) = b ^ 2 * g.inner p v v`. -/
lemma gInner_smul_self (g : SmoothRiemannianMetric I M) (p : M)
    (b : ℝ) (v : TangentSpace I p) :
    g.inner p (b • v) (b • v) = b ^ 2 * g.inner p v v := by
  rw [(g.inner p).map_smul b v, ContinuousLinearMap.smul_apply,
    (g.inner p v).map_smul b v]
  simp only [smul_eq_mul]
  ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Homogeneity of the `g`-norm.** For `0 ≤ b`,
`√(g.inner p (b • v) (b • v)) = b * √(g.inner p v v)`. -/
lemma sqrt_gInner_smul_self (g : SmoothRiemannianMetric I M) (p : M)
    {b : ℝ} (hb : 0 ≤ b) (v : TangentSpace I p) :
    Real.sqrt (g.inner p (b • v) (b • v)) = b * Real.sqrt (g.inner p v v) := by
  rw [gInner_smul_self (I := I) g p b v, Real.sqrt_mul (sq_nonneg b),
    Real.sqrt_sq hb]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The `g`-quadratic form `g.inner p v v` is non-negative. -/
lemma gInner_self_nonneg (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : 0 ≤ g.inner p v v := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv; simp
  · exact (g.pos p v hv).le

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The map `v ↦ g.inner p v v` is continuous on `T_p M`. -/
lemma continuous_gInner_self (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (fun v : TangentSpace I p => g.inner p v v) :=
  (g.inner p).continuous.clm_apply continuous_id

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The map `v ↦ √(g.inner p v v)` is continuous on `T_p M`. -/
lemma continuous_sqrt_gInner_self (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (fun v : TangentSpace I p => Real.sqrt (g.inner p v v)) :=
  Real.continuous_sqrt.comp (continuous_gInner_self (I := I) g p)

/-! ## 2. Compactness of the `g`-unit sphere

The `g`-unit sphere `{w | g_p(w, w) = 1}` in `T_p M` is closed (equalizer of two
continuous maps) and bounded (von Neumann boundedness of the unit `g`-ball
`g.isVonNBounded`, transported by a rescaling); in the proper finite-dimensional
tangent space it is therefore compact.  The boundedness mirrors
`RadialSurjectivity.isBounded_gBall`, using the intrinsic `g`-norm rather than the
model-`E` norm so as to avoid the tangent-bundle norm diamond. -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The `g`-unit sphere is closed.** It is the equalizer of the continuous map
`v ↦ g.inner p v v` with the constant `1`. -/
lemma gUnitSphere_isClosed (g : SmoothRiemannianMetric I M) (p : M) :
    IsClosed {w : TangentSpace I p | g.inner p w w = 1} :=
  isClosed_eq (continuous_gInner_self (I := I) g p) continuous_const

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The `g`-unit sphere is bounded.** The von Neumann boundedness of the unit
`g`-ball `{w | g_p(w, w) < 1}` (`g.isVonNBounded`) gives a model-norm bound `r` on
it; rescaling `v ↦ 2⁻¹ • v` carries a `g`-unit vector into the unit `g`-ball
(`g_p(2⁻¹•v, 2⁻¹•v) = 1/4 < 1`), so `‖v‖ ≤ 2 r`. -/
lemma gUnitSphere_isBounded (g : SmoothRiemannianMetric I M) (p : M) :
    Bornology.IsBounded {w : TangentSpace I p | g.inner p w w = 1} := by
  obtain ⟨r, hr⟩ :=
    (NormedSpace.isVonNBounded_iff' ℝ (E := TangentSpace I p)).1 (g.isVonNBounded p)
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2 * r, fun v hv => ?_⟩
  have hgvv : g.inner p v v = 1 := hv
  -- `w := 2⁻¹ • v` lies in the unit `g`-ball: `g_p(w, w) = 1/4 < 1`.
  set w : TangentSpace I p := (2 : ℝ)⁻¹ • v with hw
  have hgw : g.inner p w w < 1 := by
    have hscale : g.inner p w w = (2 : ℝ)⁻¹ ^ 2 * g.inner p v v :=
      gInner_smul_self (I := I) g p _ v
    rw [hscale, hgvv]; norm_num
  have hwnorm : ‖w‖ ≤ r := hr w hgw
  have hv_eq : v = (2 : ℝ) • w := by rw [hw, smul_smul]; norm_num
  rw [hv_eq, norm_smul, Real.norm_eq_abs]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  exact mul_le_mul_of_nonneg_left hwnorm (by norm_num)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The `g`-unit sphere is compact.** Closed (`gUnitSphere_isClosed`) and
bounded (`gUnitSphere_isBounded`) in the proper finite-dimensional tangent
space. -/
lemma gUnitSphere_isCompact (g : SmoothRiemannianMetric I M) (p : M) :
    IsCompact {w : TangentSpace I p | g.inner p w w = 1} := by
  haveI : ProperSpace (TangentSpace I p) :=
    FiniteDimensional.proper_real (TangentSpace I p)
  exact Metric.isCompact_of_isClosed_isBounded
    (gUnitSphere_isClosed (I := I) g p) (gUnitSphere_isBounded (I := I) g p)

/-! ## 3. Compactness of the intrinsic sphere `S_δ`

`S_δ` is the image of the compact `g`-unit sphere under the continuous map
`w ↦ expMapIntrinsic g hEnorm p (δ • w)`.  Continuity of `expMapIntrinsic g hEnorm
p` is the proven `expMapIntrinsic_continuous`; composing with the continuous
scaling `w ↦ δ • w` keeps it continuous. -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Compactness of the intrinsic sphere `S_δ`.** For any `δ`, the image of the
`g`-unit sphere under `w ↦ expMapIntrinsic g hEnorm p (δ • w)` is compact. -/
theorem intrinsicSphere_isCompact
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (δ : ℝ) :
    IsCompact
      ((fun w : TangentSpace I p => expMapIntrinsic (I := I) g hEnorm p (δ • w))
        '' {w : TangentSpace I p | g.inner p w w = 1}) := by
  have hexp : Continuous (fun v : TangentSpace I p =>
      expMapIntrinsic (I := I) g hEnorm p v) :=
    expMapIntrinsic_continuous (I := I) g hEnorm p
  have hscale : Continuous (fun w : TangentSpace I p => δ • w) :=
    continuous_const_smul δ
  have hcomp : Continuous
      (fun w : TangentSpace I p => expMapIntrinsic (I := I) g hEnorm p (δ • w)) :=
    hexp.comp hscale
  exact (gUnitSphere_isCompact (I := I) g p).image hcomp

/-! ## 4. Continuity of `riemannianEDist · q` and the sphere-minimisation step

The Riemannian distance `q' ↦ riemannianEDist I q' q` from a fixed target `q` is
continuous for the manifold topology (built from Mathlib's canonical
`PseudoEMetricSpace.ofRiemannianMetric I M`, whose `edist` *is* `riemannianEDist
I` and whose topology is the manifold topology).  On the compact sphere `S_δ` the
extreme value theorem `IsCompact.exists_isMinOn` then produces a minimiser. -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Continuity of `q' ↦ riemannianEDist I q' q` for the manifold topology.

The ambient `[PseudoEMetricSpace M]` need not have the manifold topology, so its
`edist`-continuity does not transfer; instead we use Mathlib's canonical
`PseudoEMetricSpace.ofRiemannianMetric I M`, whose `edist` is `riemannianEDist I`
definitionally and whose topology is the manifold topology by construction. -/
lemma continuous_riemannianEDist_to
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (q : M) :
    Continuous (fun q' : M => riemannianEDist I q' q) := by
  haveI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  haveI : RegularSpace M := inferInstance
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  exact (continuous_id.edist continuous_const)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Sphere-minimisation step.** On the (nonempty) compact intrinsic sphere
`S_δ` the continuous function `x ↦ riemannianEDist I x q` attains a minimum: there
is a `g`-unit vector `u` with `x₀ := expMapIntrinsic g hEnorm p (δ • u)`
minimising `riemannianEDist · q` over `S_δ`.

Existence of a `g`-unit vector uses the positive dimension of `E`; the minimum is
the extreme value theorem `IsCompact.exists_isMinOn` on the compact `S_δ`. -/
theorem exists_min_riemannianEDist_on_intrinsicSphere
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p q : M) (δ : ℝ) :
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      ∀ w : TangentSpace I p, g.inner p w w = 1 →
        riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (δ • u)) q ≤
          riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (δ • w)) q := by
  classical
  -- The sphere `S_δ` is the image of the compact `g`-unit sphere under
  -- `w ↦ expMapIntrinsic g hEnorm p (δ • w)`; minimise `riemannianEDist · q`.
  set f : TangentSpace I p → M :=
    fun w => expMapIntrinsic (I := I) g hEnorm p (δ • w) with hf_def
  set sph : Set (TangentSpace I p) := {w : TangentSpace I p | g.inner p w w = 1}
    with hsph_def
  -- The `g`-unit sphere is nonempty: rescale a nonzero vector to `g`-norm one.
  have hsph_ne : sph.Nonempty := by
    have hfin_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
    haveI : Nontrivial E := Module.nontrivial_of_finrank_pos hfin_pos
    obtain ⟨x, hx_ne⟩ : ∃ x : TangentSpace I p, x ≠ 0 :=
      ⟨(exists_ne (0 : E)).choose, (exists_ne (0 : E)).choose_spec⟩
    have hc_pos : 0 < g.inner p x x := g.pos p x hx_ne
    have hc_ne : g.inner p x x ≠ 0 := ne_of_gt hc_pos
    set s : ℝ := Real.sqrt (g.inner p x x)⁻¹ with hs_def
    have hs_sq : s * s = (g.inner p x x)⁻¹ := by
      rw [hs_def]
      exact Real.mul_self_sqrt (inv_nonneg.mpr hc_pos.le)
    refine ⟨s • x, ?_⟩
    change g.inner p (s • x) (s • x) = 1
    rw [gInner_smul_self (I := I) g p s x]
    rw [show s ^ 2 = s * s by ring, hs_sq, inv_mul_cancel₀ hc_ne]
  -- The continuous distance-to-`q`, restricted to the compact sphere `S_δ`.
  have hcont : Continuous (fun x : M => riemannianEDist I x q) :=
    continuous_riemannianEDist_to (I := I) q
  have hfcont : Continuous f := by
    have hexp : Continuous (fun v : TangentSpace I p =>
        expMapIntrinsic (I := I) g hEnorm p v) :=
      expMapIntrinsic_continuous (I := I) g hEnorm p
    exact hexp.comp (continuous_const_smul δ)
  -- `riemannianEDist (f w) q` is continuous on the compact sphere.
  have hcompact : IsCompact sph := gUnitSphere_isCompact (I := I) g p
  have hcontOn : ContinuousOn (fun w : TangentSpace I p =>
      riemannianEDist I (f w) q) sph :=
    (hcont.comp hfcont).continuousOn
  obtain ⟨u, hu_mem, hu_min⟩ :=
    hcompact.exists_isMinOn hsph_ne hcontOn
  refine ⟨u, hu_mem, ?_⟩
  intro w hw
  exact hu_min (show w ∈ sph from hw)

/-! ## 5. The propagation set `A` and its closedness

For the ray `γ(t) := expMapIntrinsic g hEnorm p (t • u)` (continuous in `t` by
the proven `expMapIntrinsic_continuous` composed with the continuous scaling) and
a target `q`, the propagation set

`A := { t ∈ [0, r] | (riemannianEDist I (γ t) q).toReal = r - t }`

is closed: it is the intersection of the closed interval `[0, r]` with the
equalizer of two continuous real functions of `t` (`t ↦ (riemannianEDist I (γ t)
q).toReal` is continuous on the locus where the distance is finite, which on a
complete manifold is all of `M`; `t ↦ r - t` is continuous). -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The radial ray `t ↦ expMapIntrinsic g hEnorm p (t • u)` is continuous in
`t`. -/
theorem radialRay_continuous
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (u : TangentSpace I p) :
    Continuous (fun t : ℝ => expMapIntrinsic (I := I) g hEnorm p (t • u)) := by
  have hexp : Continuous (fun v : TangentSpace I p =>
      expMapIntrinsic (I := I) g hEnorm p v) :=
    expMapIntrinsic_continuous (I := I) g hEnorm p
  exact hexp.comp (continuous_id.smul continuous_const)

/-! ## 6. Finiteness of the Riemannian distance on a connected manifold

On a connected manifold any two points are at finite Riemannian distance.  This
justifies using `(riemannianEDist I x q).toReal` (its `toReal` is informative, not
the junk value of `⊤`).  The finite-distance locus `{z | riemannianEDist I p z ≠
⊤}` is clopen (open and closed, by the local distance bound
`eventually_riemannianEDist_lt` together with the triangle inequality) and
contains `p`, hence — `M` being connected — is all of `M`.  This argument is
phrased in the same fibre-norm context (the `attribute [-instance]` prefix) as
the consumers `radialDistToReal_continuous` / `propagationSet_isClosed`, so the
`riemannianEDist` terms match. -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Finiteness of the Riemannian distance** on a connected manifold: any two
points have `riemannianEDist I p q ≠ ⊤`.  The finite-distance locus from `p` is
clopen (open: a finite point has a neighbourhood of finite points by the local
bound `eventually_riemannianEDist_lt` and the triangle inequality; closed: the
infinite locus is open by the same bound) and contains `p`, so by connectedness it
is everything. -/
theorem riemannianEDist_ne_top
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (p q : M) : riemannianEDist I p q ≠ (⊤ : ℝ≥0∞) := by
  haveI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  haveI : RegularSpace M := inferInstance
  -- The finite-distance locus from `p`.
  set S : Set M := {z : M | riemannianEDist I p z ≠ ⊤} with hS
  have hpS : p ∈ S := by
    simp only [hS, Set.mem_setOf_eq, riemannianEDist_self]; exact ENNReal.zero_ne_top
  -- `S` is open: near `z₀ ∈ S`, `d p z ≤ d p z₀ + d z₀ z < ⊤`.
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z₀ hz₀
    have hfin : riemannianEDist I p z₀ ≠ ⊤ := hz₀
    have hloc : ∀ᶠ z in nhds z₀, riemannianEDist I z₀ z < (1 : ℝ≥0∞) :=
      eventually_riemannianEDist_lt I z₀ one_pos
    filter_upwards [hloc] with z hz
    simp only [hS, Set.mem_setOf_eq]
    have htri : riemannianEDist I p z ≤
        riemannianEDist I p z₀ + riemannianEDist I z₀ z := riemannianEDist_triangle
    have hlt : riemannianEDist I p z < ⊤ :=
      lt_of_le_of_lt htri
        (ENNReal.add_lt_top.mpr ⟨lt_of_le_of_ne le_top hfin,
          lt_of_lt_of_le hz (by norm_num)⟩)
    exact hlt.ne
  -- `Sᶜ` is open: the same triangle bound, contrapositive.
  have hScompl_open : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro z₀ hz₀
    have hinf : riemannianEDist I p z₀ = ⊤ := by
      simpa only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_not] using hz₀
    have hloc : ∀ᶠ z in nhds z₀, riemannianEDist I z₀ z < (1 : ℝ≥0∞) :=
      eventually_riemannianEDist_lt I z₀ one_pos
    filter_upwards [hloc] with z hz
    simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
    by_contra hpz
    have hpz' : riemannianEDist I p z ≠ ⊤ := hpz
    have htri : riemannianEDist I p z₀ ≤
        riemannianEDist I p z + riemannianEDist I z z₀ := riemannianEDist_triangle
    have hzz0 : riemannianEDist I z z₀ < ⊤ := by
      rw [riemannianEDist_comm]; exact lt_of_lt_of_le hz (by norm_num)
    have hfin' : riemannianEDist I p z₀ < ⊤ :=
      lt_of_le_of_lt htri
        (ENNReal.add_lt_top.mpr ⟨lt_of_le_of_ne le_top hpz', hzz0⟩)
    exact hfin'.ne hinf
  -- `S` clopen, nonempty, `M` connected ⟹ `S = univ`.
  have hSclopen : IsClopen S := ⟨⟨hScompl_open⟩, hSopen⟩
  have hSuniv : S = Set.univ := by
    rcases isClopen_iff.mp hSclopen with hempty | huniv
    · exact absurd (hempty ▸ hpS) (by simp)
    · exact huniv
  exact (hSuniv ▸ Set.mem_univ q : q ∈ S)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The real-valued radial distance-to-`q` along the ray,
`t ↦ (riemannianEDist I (γ t) q).toReal`, is continuous. -/
theorem radialDistToReal_continuous
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p q : M) (u : TangentSpace I p) :
    Continuous (fun t : ℝ =>
      (riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (t • u)) q).toReal) := by
  -- `t ↦ riemannianEDist (γ t) q` is continuous (composition); its values are
  -- never `⊤` (completeness), so `toReal` of it is continuous.
  have hray : Continuous (fun t : ℝ =>
      expMapIntrinsic (I := I) g hEnorm p (t • u)) :=
    radialRay_continuous (I := I) g hEnorm p u
  have hdist : Continuous (fun x : M => riemannianEDist I x q) :=
    continuous_riemannianEDist_to (I := I) q
  have hcomp : Continuous (fun t : ℝ =>
      riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (t • u)) q) :=
    hdist.comp hray
  -- `toReal` is continuous on `{a ≠ ⊤}`; the composite always lands there.
  refine ENNReal.continuousOn_toReal.comp_continuous hcomp (fun t => ?_)
  rw [Set.mem_setOf_eq]
  exact riemannianEDist_ne_top (I := I) _ q

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Closedness of the propagation set `A`.** For the ray `γ(t) :=
expMapIntrinsic g hEnorm p (t • u)`, target `q`, and radius `r`, the set

`A := { t ∈ [0, r] | (riemannianEDist I (γ t) q).toReal = r - t }`

is closed: it is the intersection of the closed `Icc 0 r` with the equalizer of
the two continuous real functions `t ↦ (riemannianEDist I (γ t) q).toReal`
(`radialDistToReal_continuous`) and `t ↦ r - t`. -/
theorem propagationSet_isClosed
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p q : M) (u : TangentSpace I p) (r : ℝ) :
    IsClosed
      {t : ℝ | t ∈ Set.Icc (0 : ℝ) r ∧
        (riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (t • u)) q).toReal
          = r - t} := by
  have hdistCont : Continuous (fun t : ℝ =>
      (riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (t • u)) q).toReal) :=
    radialDistToReal_continuous (I := I) g hEnorm p q u
  have hlinCont : Continuous (fun t : ℝ => r - t) :=
    continuous_const.sub continuous_id
  have heq : IsClosed
      {t : ℝ |
        (riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (t • u)) q).toReal
          = r - t} :=
    isClosed_eq hdistCont hlinCont
  have hsplit :
      {t : ℝ | t ∈ Set.Icc (0 : ℝ) r ∧
        (riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (t • u)) q).toReal
          = r - t} =
      Set.Icc (0 : ℝ) r ∩
        {t : ℝ |
          (riemannianEDist I (expMapIntrinsic (I := I) g hEnorm p (t • u)) q).toReal
            = r - t} := by
    ext t; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [hsplit]
  exact isClosed_Icc.inter heq

/-! ## 7. Point separation and the base case `r = 0`

When the Riemannian distance vanishes, `q = p` (point separation,
`riemannianEDist_eq_zero_imp_eq`) and the zero velocity works: `expMapIntrinsic g
hEnorm p 0 = p = q` (the constant geodesic), and the velocity `g`-norm is `0`. -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Point separation from a vanishing Riemannian distance.** On a finite-
dimensional `T2` Riemannian manifold, `riemannianEDist I a b = 0` forces `a = b`.

The manifold is locally compact (finite dimension) and Hausdorff, hence regular,
hence `T3`, so the canonical `EMetricSpace.ofRiemannianMetric` is an actual
(point-separating) emetric structure whose `edist` is `riemannianEDist I`
definitionally; `edist_eq_zero` then concludes. -/
theorem riemannianEDist_eq_zero_imp_eq
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (a b : M) (h : riemannianEDist I a b = 0) : a = b := by
  haveI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  haveI : RegularSpace M := inferInstance
  haveI : T3Space M := inferInstance
  letI em : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  -- The new emetric structure has `edist = riemannianEDist I` definitionally.
  have hedist : @edist M em.toEDist a b = 0 := h
  exact (@edist_eq_zero M em a b).mp hedist

/-! ## 7b. The length-distance bound along the intrinsic geodesic

A geodesic has constant `g`-speed, equal to its launch speed `√(g_p(v, v))`.
Integrating the velocity enorm bound over `[s, t]` (and using the path-length ≥
distance estimate `riemannianEDist_le_pathELength`) gives the Lipschitz bound

`riemannianEDist (γ s) (γ t) ≤ √(g_p(v, v)) · (t - s)` for `s ≤ t`,

where `γ := intrinsicGeodesic g hEnorm p v`.  This is the intrinsic analogue of
`HopfRinow.bm_c_gc_length_distance_bound` (which is stated for the chart-fixed
`maximalGeodesic`); here the curve is the genuinely complete moving-foot
geodesic.  Its speed-constancy comes from `HopfRinow.isGeodesicOn_speedSq_const`
(the curve is `IsGeodesicOn univ` and `C¹` in time), its launch speed from
`intrinsicGeodesic_mfderiv_zero`, and the enorm-from-speed-squared conversion
from `velocity_enorm_le_of_speedSq_le` via `hEnorm`. -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Constant squared `g`-speed of the intrinsic geodesic.** Along
`γ := intrinsicGeodesic g hEnorm p v`, the squared `g`-speed
`g.inner (γ t) (γ'(t)) (γ'(t))` equals the launch squared speed
`g.inner p v v` for every `t`.  This is `isGeodesicOn_speedSq_const` (the
intrinsic geodesic is `IsGeodesicOn univ` and `ContMDiffOn 𝓘(ℝ,ℝ) I 1` on
`univ`) evaluated at the launch time `0`, where `intrinsicGeodesic_mfderiv_zero`
identifies the velocity with `v`. -/
theorem intrinsicGeodesic_speedSq_eq
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) (t : ℝ) :
    g.inner (intrinsicGeodesic (I := I) g hEnorm p v t)
        (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) t 1)
        (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) t 1)
      = g.inner p v v := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hgeo : IsGeodesic (I := I) g γ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v
  have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ Set.univ :=
    intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p v
  -- Speed-squared is constant: compare time `t` with the launch time `0`.
  have hconst := HopfRinow.isGeodesicOn_speedSq_const (I := I) g (t₀ := t) (t₁ := 0)
    isOpen_univ (hgeo.isGeodesicOn Set.univ) hC1 (Set.subset_univ _)
  rw [hconst]
  -- At `t = 0`: `γ 0 = p` and the velocity is `v` (the `TangentSpace I p = E`
  -- value, via `intrinsicGeodesic_mfderiv_zero`), so the squared speed at `0`
  -- is `g.inner p v v`.  The base-point rewrite `γ 0 = p` is generalised first
  -- so the velocity vector's fibre type tracks the rewrite.
  have h0 : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  -- The velocity at `0` has raw `E`-value `v` (`intrinsicGeodesic_mfderiv_zero`).
  -- Both `g.inner (γ 0)` and `g.inner p` are the same `E`-bilinear form (base
  -- points equal), and the velocity is `v` as an `E`-element.  Discharge by
  -- `congr` on the bilinear application, peeling off the base point and the two
  -- velocity slots.
  have hvelE : (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = (v : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p v
  refine (congrArg₂ (fun (x : M) (w : E) => g.inner x w w) h0 ?_)
  exact hvelE

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Velocity enorm bound along the intrinsic geodesic.** Along
`γ := intrinsicGeodesic g hEnorm p v`, the bundle enorm of the velocity is
bounded by the launch speed `√(g_p(v, v))` at every time, by constant
squared speed (`intrinsicGeodesic_speedSq_eq`) and the enorm-from-speed
conversion (`velocity_enorm_le_of_speedSq_le`). -/
theorem intrinsicGeodesic_velocity_enorm_le
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) (t : ℝ) :
    ‖mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) t (1 : ℝ)‖ₑ
      ≤ ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  set c : ℝ := Real.sqrt (g.inner p v v) with hc_def
  have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  -- The squared speed at `t` equals `g.inner p v v = c²`.
  have hspeedSq : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = c ^ 2 := by
    rw [intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p v t, hc_def,
      Real.sq_sqrt (gInner_self_nonneg (I := I) g p v)]
  -- Convert the squared-speed equality into the velocity enorm bound via the
  -- fibre-norm compatibility `hEnorm` (`‖w‖ₑ = ofReal √(g.inner …)`).
  rw [hEnorm]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  calc Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1))
      = Real.sqrt (c ^ 2) := by rw [hspeedSq]
    _ = c := Real.sqrt_sq hc_nn

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Length-distance bound along the intrinsic geodesic.** For `s ≤ t`,
`riemannianEDist (γ s) (γ t) ≤ √(g_p(v, v)) · (t - s)`, where
`γ := intrinsicGeodesic g hEnorm p v`.  This bounds the moving-foot geodesic's
displacement by its (constant) launch speed times the elapsed parameter.  The
proof dominates `pathELength I γ s t` by the constant speed `√(g_p(v, v))` (via
`intrinsicGeodesic_velocity_enorm_le`) and chains with
`riemannianEDist_le_pathELength`. -/
theorem intrinsicGeodesic_riemannianEDist_le
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) {s t : ℝ} (hst : s ≤ t) :
    riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm p v s)
        (intrinsicGeodesic (I := I) g hEnorm p v t)
      ≤ ENNReal.ofReal (Real.sqrt (g.inner p v v) * (t - s)) := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  set c : ℝ := Real.sqrt (g.inner p v v) with hc_def
  have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  -- `C¹` smoothness of `γ` on `Icc s t` (restriction of the global witness).
  have hγ_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc s t) :=
    (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p v).mono (Set.subset_univ _)
  -- `pathELength I γ s t ≤ ofReal (c · (t - s))`.
  have h_pathLen_le : pathELength I γ s t ≤ ENNReal.ofReal (c * (t - s)) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have h_le :
        ∫⁻ τ in Set.Icc s t, (fun τ => ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ) τ
          ≤ ∫⁻ _ in Set.Icc s t, ENNReal.ofReal c := by
      refine MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun τ _ => ?_)
      simpa [hγ_def, hc_def] using
        intrinsicGeodesic_velocity_enorm_le (I := I) g hEnorm p v τ
    have h_const :
        (∫⁻ _ in Set.Icc s t, ENNReal.ofReal c)
          = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc s t) :=
      MeasureTheory.setLIntegral_const (Set.Icc s t) (ENNReal.ofReal c)
    have h_vol : MeasureTheory.volume (Set.Icc s t) = ENNReal.ofReal (t - s) :=
      Real.volume_Icc
    have h_mul :
        ENNReal.ofReal c * ENNReal.ofReal (t - s) = ENNReal.ofReal (c * (t - s)) :=
      (ENNReal.ofReal_mul hc_nn).symm
    calc
      ∫⁻ τ in Set.Icc s t, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ
          ≤ ∫⁻ _ in Set.Icc s t, ENNReal.ofReal c := h_le
      _ = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc s t) := h_const
      _ = ENNReal.ofReal c * ENNReal.ofReal (t - s) := by rw [h_vol]
      _ = ENNReal.ofReal (c * (t - s)) := h_mul
  -- `riemannianEDist ≤ pathELength` and chain.
  have h_dist_le : riemannianEDist I (γ s) (γ t) ≤ pathELength I γ s t :=
    riemannianEDist_le_pathELength (I := I) (γ := γ) (a := s) (b := t)
      hγ_C1 rfl rfl hst
  exact h_dist_le.trans h_pathLen_le

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The intrinsic geodesic with zero launch velocity is the constant `p`.**
In particular `expMapIntrinsic g hEnorm p 0 = p` (target value at `t = 1`).
Zero launch speed makes the length-distance bound
(`intrinsicGeodesic_riemannianEDist_le`) collapse:
`riemannianEDist (γ 0) (γ 1) ≤ 0`, so `γ 1 = γ 0 = p` by point separation
(`riemannianEDist_eq_zero_imp_eq`). -/
theorem expMapIntrinsic_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    expMapIntrinsic (I := I) g hEnorm p 0 = p := by
  -- `γ := intrinsicGeodesic g hEnorm p 0`; `γ 0 = p`, `expMapIntrinsic = γ 1`.
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p (0 : TangentSpace I p)
    with hγ_def
  have h0 : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p 0
  -- Launch speed is `√(g_p(0, 0)) = 0`, so the distance bound gives `≤ 0`.
  have hspeed0 : Real.sqrt (g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p)) = 0 := by
    rw [show g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0 by simp,
      Real.sqrt_zero]
  have hbound := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p
    (0 : TangentSpace I p) (s := 0) (t := 1) (by norm_num)
  rw [hspeed0, zero_mul, ENNReal.ofReal_zero] at hbound
  -- Hence `riemannianEDist (γ 0) (γ 1) = 0`, so `γ 1 = γ 0 = p`.
  have hzero : riemannianEDist I (γ 0) (γ 1) = 0 := le_antisymm hbound (by simp)
  have heq : γ 0 = γ 1 :=
    riemannianEDist_eq_zero_imp_eq (I := I) (γ 0) (γ 1) hzero
  -- `expMapIntrinsic g hEnorm p 0 = γ 1` definitionally; conclude `γ 1 = p`.
  change γ 1 = p
  rw [← heq, h0]

/-! ## 8. The velocity-identified Hopf–Rinow surjectivity (headline)

The headline assembles the pieces: the `r = 0` base case is discharged outright;
for `r > 0` the ray/sphere propagation produces the realising velocity `v := r •
u`.  The propagation `sup A = r` is the single remaining geometric input (see the
docstring decomposition). -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Velocity-identified Hopf–Rinow surjectivity.** On a complete Riemannian
manifold, for every `p q : M` there is a tangent vector `v : T_p M` with
`expMapIntrinsic g hEnorm p v = q` and `g`-speed `√(g_p(v, v))` equal to the
Riemannian distance `(riemannianEDist I p q).toReal`.

(There is no `riemannianDist` definition in the project; the real Riemannian
distance is `(riemannianEDist I p q).toReal`.)

DECOMPOSITION (ray/sphere argument):

* `r = 0` (i.e. `riemannianEDist I p q = 0`): `q = p` (point separation
  `riemannianEDist_eq_zero_imp_eq`) and `v := 0` works (`expMapIntrinsic g hEnorm
  p 0 = p`, the constant-geodesic residual; the `g`-speed of `0` is `0 = r`).

* `r > 0`: pick `δ ∈ (0, expRadiusGp g p)`.  Let `u` be the `g`-unit minimiser
  of `riemannianEDist · q` over the compact intrinsic sphere `S_δ`
  (`exists_min_riemannianEDist_on_intrinsicSphere`).  The two remaining geometric
  inputs are:

  1.  **Ray jumps onto the sphere.** `riemannianEDist (γ δ) q = r - δ`, where
      `γ(t) := expMapIntrinsic g hEnorm p (t • u)`.  The `≥` direction is the
      triangle inequality `riemannianEDist p q ≤ riemannianEDist p (γ δ) +
      riemannianEDist (γ δ) q` together with `riemannianEDist p (γ δ) = δ` (the
      radial local minimality `normalBall_radial_unique_minimizer` plus the
      reverse path bound).  The `≤` direction is that every path `p → q` crosses
      the sphere `S_δ`, so the minimiser realises `r - δ` (intermediate-value /
      path-crosses-sphere on `riemannianEDist`).

      Sub-lemma signature:
      ```
      ray_jumps_onto_sphere :
        0 < δ → δ < expRadiusGp g p → r = (riemannianEDist I p q).toReal →
        (∀ w, g.inner p w w = 1 →
          riemannianEDist I (expMapIntrinsic g hEnorm p (δ • u)) q ≤
            riemannianEDist I (expMapIntrinsic g hEnorm p (δ • w)) q) →
        g.inner p u u = 1 →
        (riemannianEDist I (expMapIntrinsic g hEnorm p (δ • u)) q).toReal = r - δ
      ```

  2.  **Propagation `sup A = r`.** The set `A := { t ∈ [0, r] |
      (riemannianEDist I (γ t) q).toReal = r - t }` is closed
      (`propagationSet_isClosed`) and contains `δ` (step 1, with the homogeneity
      `√(g_p(δ•u, δ•u)) = δ`).  If `t₀ := sup A < r`, the sphere argument
      *re-based at `γ(t₀)`* (the Gauss-lemma radial local minimality at the
      moving foot point `γ(t₀)`, i.e. the equality case of
      `normalBall_radial_unique_minimizer` together with the cross-chart
      geodesic-continuation identifying `expMap g (γ t₀) w` with the continuation
      of `intrinsicGeodesic g hEnorm p (t₀ • u)`) extends `A` strictly past
      `t₀`, contradicting the supremum.  Hence `r ∈ A`, i.e.
      `riemannianEDist (γ r) q = 0`, so `γ r = q`.

  Then `v := r • u` satisfies `expMapIntrinsic g hEnorm p v = γ r = q` and
  `√(g_p(r•u, r•u)) = r · √(g_p(u,u)) = r · 1 = r` (`sqrt_gInner_smul_self` and
  `g.inner p u u = 1`).

The only `sorry` is the re-based local-minimality / continuation in step (2.); it
is exactly the pending geometric content flagged in `RadialSurjectivity.lean` /
`HopfRinow.unit_speed_minimising_geodesic_from_points`.  Everything else in this
file is proved unconditionally. -/
theorem expMapIntrinsic_surjective_dist
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p q : M) :
    ∃ v : TangentSpace I p, expMapIntrinsic (I := I) g hEnorm p v = q ∧
      Real.sqrt (g.inner p v v) = (riemannianEDist I p q).toReal := by
  classical
  -- `r := (riemannianEDist I p q).toReal`, finite by completeness.
  set r : ℝ := (riemannianEDist I p q).toReal with hr_def
  -- BASE CASE `r = 0`.
  rcases eq_or_ne (riemannianEDist I p q) 0 with hpq0 | hpq_pos
  · -- `riemannianEDist I p q = 0 ⟹ p = q` (point separation); take `v := 0`.
    have hpq : p = q := riemannianEDist_eq_zero_imp_eq (I := I) p q hpq0
    refine ⟨0, ?_, ?_⟩
    · -- `expMapIntrinsic g hEnorm p 0 = p = q`.  The first equality is the
      -- constant-geodesic identity `expMapIntrinsic_zero` (the intrinsic geodesic
      -- at zero launch velocity has zero `g`-speed everywhere, so the length
      -- bound `intrinsicGeodesic_riemannianEDist_le` forces `γ 1 = γ 0 = p`);
      -- combined with `p = q` it gives the endpoint.
      have hexp0 : expMapIntrinsic (I := I) g hEnorm p 0 = p :=
        expMapIntrinsic_zero (I := I) g hEnorm p
      rw [hexp0, hpq]
    · -- `√(g_p(0, 0)) = 0 = r`.
      have h0 : g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0 := by simp
      rw [h0, Real.sqrt_zero, hr_def, hpq0, ENNReal.toReal_zero]
  · -- POSITIVE CASE: the ray/sphere propagation produces `v := r • u`.
    -- See the docstring decomposition.  The residual geometric input is the
    -- bridge between the moving-foot intrinsic exponential `expMapIntrinsic`
    -- (which the ray `γ` and the sphere `S_δ` are built from, and which alone is
    -- defined across charts) and the chart-fixed `expMap` of the Gauss-lemma
    -- rigidity package:
    --
    --   * `expMapIntrinsic g hEnorm p v = expMap g p v` whenever
    --     `√(g_p(v, v)) < expRadiusGp g p`  (small-vector agreement of the two
    --     complete geodesics with shared initial data `(p, v)`), and the
    --     analogous re-based identity at a moving foot `γ(t₀)`.
    --
    -- This agreement is a *global geodesic uniqueness* fact: both
    -- `intrinsicGeodesic g hEnorm p v` (`IsGeodesic`, moving-foot) and
    -- `maximalGeodesic g p v` (`expMap g p v = maximalGeodesic g p v 1`) solve
    -- the geodesic ODE from `(p, v)` and agree on a neighbourhood of `0`; their
    -- agreement on `[0, 1]` requires propagating the equality across the chart
    -- the geodesic may leave.  The only `IsGeodesicAt`/lift-uniqueness available
    -- (`Geodesic/Uniqueness.lean` `isGeodesicAt_eventuallyEq`,
    -- `Geodesic/MaximalInterval.lean` `exists_isGeodesicAt_of_mem_maximalGeodesicInterval`)
    -- is chart-`p`-fixed, gated on the foot staying in `(chartAt H p).source`,
    -- so it cannot drive the propagation once the geodesic leaves the home
    -- chart — the same cross-chart obstruction pending in
    -- `RadialSurjectivity.lean` (`radial_image_T_contains_rieDist_closedBall`)
    -- and `HopfRinow.unit_speed_minimising_geodesic_from_points`.  Given the
    -- bridge, the propagation is: the lower bound
    -- `riemannianEDist p (γ δ) ≥ δ` (Gauss `normalBall_radial_unique_minimizer`)
    -- and the upper bound `≤ δ` (`intrinsicGeodesic_riemannianEDist_le`, PROVEN
    -- here) give the base case `δ ∈ A`; the rigidity
    -- `normalBall_radial_minimizer_equality` re-based at `γ(t₀)` extends `A`
    -- strictly past `sup A` whenever `sup A < r`; and
    -- `riemannianEDist_eq_zero_imp_eq` at `t = r` closes with `γ r = q`.
    sorry

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
