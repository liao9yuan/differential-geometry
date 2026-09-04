import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.ChangingDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.MovingEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.RicciOperator
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

set_option autoImplicit false

/-!
# Moving-endpoint changing-distance estimates

This file combines the fixed-endpoint Perelman supports with the local motion
of two smooth endpoints.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped ENNReal Manifold ContDiff Topology Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M] in
private theorem smooth_rate_event
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    {T tau : Real} (ht : T - tau ∈ D.regular)
    {x : Real → M}
    (hx : ContMDiffAt 𝓘(Real, Real) I 1 x tau) :
    ∀ epsilon > 0, ∀ᶠ s in 𝓝[>] tau,
      (riemannianEDistOf (I := I) (S.base.metric (T - s))
        (x tau) (x s)).toReal / (s - tau) <
      Real.sqrt ((S.base.metric (T - tau)).inner (x tau)
        (mfderiv 𝓘(Real, Real) I x tau (1 : Real))
        (mfderiv 𝓘(Real, Real) I x tau (1 : Real))) + epsilon := by
  intro epsilon hepsilon
  rcases edist_smooth_rate (I := I) S hG ht hx
      (epsilon / 2) (by linarith) with ⟨delta, hdelta, hbound⟩
  filter_upwards [Ioo_mem_nhdsGT
    (show tau < tau + delta by linarith)] with s hs
  have hden : 0 < s - tau := sub_pos.mpr hs.1
  calc
    (riemannianEDistOf (I := I) (S.base.metric (T - s))
          (x tau) (x s)).toReal / (s - tau) ≤
        ((Real.sqrt ((S.base.metric (T - tau)).inner (x tau)
            (mfderiv 𝓘(Real, Real) I x tau (1 : Real))
            (mfderiv 𝓘(Real, Real) I x tau (1 : Real))) + epsilon / 2) *
          (s - tau)) / (s - tau) :=
      (div_le_div_iff_of_pos_right hden).2 (hbound s hs.1 hs.2)
    _ = Real.sqrt ((S.base.metric (T - tau)).inner (x tau)
          (mfderiv 𝓘(Real, Real) I x tau (1 : Real))
          (mfderiv 𝓘(Real, Real) I x tau (1 : Real))) + epsilon / 2 :=
      mul_div_cancel_right₀ _ hden.ne'
    _ < Real.sqrt ((S.base.metric (T - tau)).inner (x tau)
          (mfderiv 𝓘(Real, Real) I x tau (1 : Real))
          (mfderiv 𝓘(Real, Real) I x tau (1 : Real))) + epsilon := by
      linarith

omit [IsManifold I 2 M] in
/-- Short-distance moving-endpoint form of Perelman's changing-distance
estimate for the backward Ricci-flow clock. -/
theorem dist_short_slope
    [T2Space (TangentBundle I M)] [ConnectedSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T tau K r : Real}
    (ht : T - tau ∈ D.regular)
    (hcomplete : RiemannianMetricComplete
      (I := I) (S.base.metric (T - tau)))
    (hK : 0 ≤ K) (hr : 0 < r)
    (x y : Real → M)
    (hx : ContMDiffAt 𝓘(Real, Real) I 1 x tau)
    (hy : ContMDiffAt 𝓘(Real, Real) I 1 y tau)
    (hshort :
      (riemannianEDistOf (I := I) (S.base.metric (T - tau))
        (x tau) (y tau)).toReal < 2 * r)
    (hRic : ∀ z : M, ∀ w : TangentSpace I z,
      (riemannianEDistOf (I := I) (S.base.metric (T - tau))
          (x tau) z < ENNReal.ofReal r ∨
        riemannianEDistOf (I := I) (S.base.metric (T - tau))
          (y tau) z < ENNReal.ofReal r) →
      ricciTensor (I := I) (S.base.metric (T - tau)) z w w ≤
        ((Module.finrank Real E : Real) - 1) * K *
          (S.base.metric (T - tau)).inner z w w) :
    ∀ epsilon > 0, ∀ᶠ s in 𝓝[>] tau,
      slope (fun u ↦
        (riemannianEDistOf (I := I) (S.base.metric (T - u))
          (x u) (y u)).toReal) tau s <
      2 * ((Module.finrank Real E : Real) - 1) * K * r +
        Real.sqrt ((S.base.metric (T - tau)).inner (x tau)
          (mfderiv 𝓘(Real, Real) I x tau (1 : Real))
          (mfderiv 𝓘(Real, Real) I x tau (1 : Real))) +
        Real.sqrt ((S.base.metric (T - tau)).inner (y tau)
          (mfderiv 𝓘(Real, Real) I y tau (1 : Real))
          (mfderiv 𝓘(Real, Real) I y tau (1 : Real))) + epsilon := by
  rcases dist_short_support (I := I) S hS ht hcomplete hK hr
      (x tau) (y tau) hshort hRic with
    ⟨phi, d, hcontact, hupper, hphi, hd⟩
  refine dist_moving_slope (I := I)
    (fun s ↦ S.base.metric (T - s)) x y phi
    hcontact hupper hphi hd ?_ ?_
  · intro epsilon hepsilon
    filter_upwards [smooth_rate_event (I := I) S hS.smoothMetric ht hx
      epsilon hepsilon] with s hs
    rw [edistOf_comm (I := I) (S.base.metric (T - s)) (x s) (x tau)]
    exact hs
  · exact smooth_rate_event (I := I) S hS.smoothMetric ht hy

omit [IsManifold I 2 M] in
/-- Long-distance moving-endpoint form of Perelman's changing-distance
estimate for the backward Ricci-flow clock. -/
theorem dist_long_slope
    [T2Space (TangentBundle I M)] [ConnectedSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T tau K r : Real}
    (ht : T - tau ∈ D.regular)
    (hcomplete : RiemannianMetricComplete
      (I := I) (S.base.metric (T - tau)))
    (hr : 0 < r)
    (x y : Real → M)
    (hx : ContMDiffAt 𝓘(Real, Real) I 1 x tau)
    (hy : ContMDiffAt 𝓘(Real, Real) I 1 y tau)
    (hlong : 2 * r ≤
      (riemannianEDistOf (I := I) (S.base.metric (T - tau))
        (x tau) (y tau)).toReal)
    (hRic : ∀ z : M, ∀ w : TangentSpace I z,
      (riemannianEDistOf (I := I) (S.base.metric (T - tau))
          (x tau) z < ENNReal.ofReal r ∨
        riemannianEDistOf (I := I) (S.base.metric (T - tau))
          (y tau) z < ENNReal.ofReal r) →
      ricciTensor (I := I) (S.base.metric (T - tau)) z w w ≤
        ((Module.finrank Real E : Real) - 1) * K *
          (S.base.metric (T - tau)).inner z w w) :
    ∀ epsilon > 0, ∀ᶠ s in 𝓝[>] tau,
      slope (fun u ↦
        (riemannianEDistOf (I := I) (S.base.metric (T - u))
          (x u) (y u)).toReal) tau s <
      2 * ((Module.finrank Real E : Real) - 1) *
          ((2 / 3 : Real) * K * r + 1 / r) +
        Real.sqrt ((S.base.metric (T - tau)).inner (x tau)
          (mfderiv 𝓘(Real, Real) I x tau (1 : Real))
          (mfderiv 𝓘(Real, Real) I x tau (1 : Real))) +
        Real.sqrt ((S.base.metric (T - tau)).inner (y tau)
          (mfderiv 𝓘(Real, Real) I y tau (1 : Real))
          (mfderiv 𝓘(Real, Real) I y tau (1 : Real))) + epsilon := by
  rcases dist_long_support (I := I) S hS ht hcomplete hr
      (x tau) (y tau) hlong hRic with
    ⟨phi, d, hcontact, hupper, hphi, hd⟩
  refine dist_moving_slope (I := I)
    (fun s ↦ S.base.metric (T - s)) x y phi
    hcontact hupper hphi hd ?_ ?_
  · intro epsilon hepsilon
    filter_upwards [smooth_rate_event (I := I) S hS.smoothMetric ht hx
      epsilon hepsilon] with s hs
    rw [edistOf_comm (I := I) (S.base.metric (T - s)) (x s) (x tau)]
    exact hs
  · exact smooth_rate_event (I := I) S hS.smoothMetric ht hy

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I 1 M] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] in
private theorem edist_ne_top_of
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (x y : M) :
    riemannianEDistOf (I := I) g x y ≠ (⊤ : ENNReal) := by
  letI : RiemannianBundle (fun p : M ↦ TangentSpace I p) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun p : M ↦ TangentSpace I p) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro p v w; rfl⟩⟩
  change riemannianEDist I x y ≠ (⊤ : ENNReal)
  exact DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
    (I := I) x y

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [IsManifold I 1 M] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] in
private theorem edist_real_tri
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (x y z : M) :
    (riemannianEDistOf (I := I) g x z).toReal ≤
      (riemannianEDistOf (I := I) g x y).toReal +
        (riemannianEDistOf (I := I) g y z).toReal := by
  have hxy := edist_ne_top_of (I := I) g x y
  have hyz := edist_ne_top_of (I := I) g y z
  have htri := edistOf_triangle (I := I) g x y z
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hxy, hyz⟩) htri
  rwa [ENNReal.toReal_add hxy hyz] at hreal

private theorem exp_mul_sub_one
    {K R d : Real} (hK : 0 ≤ K) (hd : d ∈ Icc (0 : Real) R) :
    Real.exp (K * d) - 1 ≤ K * Real.exp (K * R) * d := by
  have hderiv : ∀ u ∈ Icc (0 : Real) R,
      HasDerivWithinAt (fun q : Real ↦ Real.exp (K * q))
        (K * Real.exp (K * u)) (Icc (0 : Real) R) u := by
    intro u hu
    have hlin : HasDerivAt (fun q : Real ↦ K * q) K u := by
      simpa using (hasDerivAt_const u K).mul (hasDerivAt_id u)
    have hexp : HasDerivAt (fun q : Real ↦ Real.exp (K * q))
        (Real.exp (K * u) * K) u := by
      simpa using (Real.hasDerivAt_exp (K * u)).comp u hlin
    simpa only [mul_comm] using hexp.hasDerivWithinAt
  have hbound : ∀ u ∈ Icc (0 : Real) R,
      ‖K * Real.exp (K * u)‖ ≤ K * Real.exp (K * R) := by
    intro u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hK)) hK
  have hmean := (convex_Icc (0 : Real) R).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_Icc.mpr (hd.1.trans hd.2)) hd
  have hexp : 1 ≤ Real.exp (K * d) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hK hd.1)
  simpa only [mul_zero, Real.exp_zero, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hexp), abs_of_nonneg hd.1] using hmean

omit [NeZero (Module.finrank Real E)] [IsManifold I 2 M]
  [SigmaCompactSpace M] in
/-- On a compact regular backward-time interval, a global absolute Ricci bound
and `C1` endpoint curves make the moving intrinsic distance Lipschitz. -/
theorem dist_lip_Icc
    [ConnectedSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T a b K : Real}
    (hab : a ≤ b)
    (hreg : Icc (T - b) (T - a) ⊆ D.regular)
    (hric : ∀ q ∈ Icc (T - b) (T - a), ∀ z : M,
      ∀ v : TangentSpace I z,
        |ricciTensor (I := I) (S.base.metric q) z v v| ≤
          K * (S.base.metric q).inner z v v)
    (x y : Real → M)
    (hx : ContMDiffOn 𝓘(Real, Real) I 1 x (Icc a b))
    (hy : ContMDiffOn 𝓘(Real, Real) I 1 y (Icc a b)) :
    ∃ L : NNReal, LipschitzOnWith L
      (fun u ↦ (riemannianEDistOf (I := I)
        (S.base.metric (T - u)) (x u) (y u)).toReal) (Icc a b) := by
  rcases hab.eq_or_lt with rfl | hab
  · refine ⟨0, LipschitzOnWith.of_dist_le_mul ?_⟩
    intro s hs t ht
    have hs' : s = a := le_antisymm hs.2 hs.1
    have ht' : t = a := le_antisymm ht.2 ht.1
    subst s
    subst t
    simp only [dist_self, NNReal.coe_zero, zero_mul]
    exact le_rfl
  · let K0 : Real := max K 0
    let R : Real := b - a
    have hK0 : 0 ≤ K0 := by exact le_max_right K 0
    have hR : 0 ≤ R := by exact sub_nonneg.mpr hab.le
    have htime : ∀ u ∈ Icc a b, T - u ∈ Icc (T - b) (T - a) := by
      intro u hu
      constructor
      · linarith [hu.2]
      · linarith [hu.1]
    have hslab : Icc (T - b) (T - a) ⊆ D.carrier :=
      fun q hq ↦ D.regular_subset (hreg hq)
    have hpde := metricPDE_Icc (I := I) S hS (by linarith) hslab
      (fun q hq ↦ hreg ⟨hq.1.le, hq.2⟩)
    have hric0 : ∀ q ∈ Icc (T - b) (T - a), ∀ z : M,
        ∀ v : TangentSpace I z,
          |ricciTensor (I := I) (S.base.metric q) z v v| ≤
            K0 * (S.base.metric q).inner z v v := by
      intro q hq z v
      have hvv : 0 ≤ (S.base.metric q).inner z v v := by
        rcases eq_or_ne v 0 with rfl | hv
        · simp only [map_zero, le_refl]
        · exact ((S.base.metric q).pos z v hv).le
      exact (hric q hq z v).trans
        (mul_le_mul_of_nonneg_right (le_max_left K 0) hvv)
    have hcmp : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, ∀ p q : M,
        (riemannianEDistOf (I := I) (S.base.metric (T - u)) p q).toReal ≤
          Real.exp (K0 * |u - v|) *
            (riemannianEDistOf (I := I)
              (S.base.metric (T - v)) p q).toReal := by
      intro u hu v hv p q
      have hed := (edistEquiv_Icc (I := I)
        (fun r ↦ S.base.metric r) hpde hric0
        (htime u hu) (htime v hv) p q).2
      have hfin : ENNReal.ofReal
            (Real.exp (K0 * |(T - u) - (T - v)|)) *
            riemannianEDistOf (I := I) (S.base.metric (T - v)) p q ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (edist_ne_top_of (I := I) (S.base.metric (T - v)) p q)
      have hreal := ENNReal.toReal_mono hfin hed
      rw [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (Real.exp_pos _).le] at hreal
      have habs : |(T - u) - (T - v)| = |u - v| := by
        rw [show (T - u) - (T - v) = v - u by ring, abs_sub_comm]
      simpa only [habs] using hreal
    let g0 : SmoothRiemannianMetric I M := S.base.metric (T - a)
    obtain ⟨Cx, hx0⟩ := edist_curve_lip (I := I) g0 hab.le hx
    obtain ⟨Cy, hy0⟩ := edist_curve_lip (I := I) g0 hab.le hy
    let A : Real := Real.exp (K0 * R)
    let C : Real := A * ((Cx : Real) + (Cy : Real))
    have hA : 0 ≤ A := (Real.exp_pos _).le
    have hC : 0 ≤ C := by
      exact mul_nonneg hA (add_nonneg Cx.2 Cy.2)
    have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
    have hmove : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b,
        ∀ (z : Real → M) (Cz : Real),
        (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
          (riemannianEDistOf (I := I) g0 (z s) (z t)).toReal ≤
            Cz * |t - s|) →
        (riemannianEDistOf (I := I) (S.base.metric (T - v))
          (z u) (z v)).toReal ≤
          A * Cz * |v - u| := by
      intro u hu v hv z Cz hz
      have hdist := hcmp v hv a ha (z u) (z v)
      have hva : |v - a| ≤ R := by
        rw [abs_of_nonneg (sub_nonneg.mpr hv.1)]
        dsimp only [R]
        linarith [hv.2]
      have hexp : Real.exp (K0 * |v - a|) ≤ A := by
        dsimp only [A]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hva hK0)
      calc
        (riemannianEDistOf (I := I) (S.base.metric (T - v))
            (z u) (z v)).toReal ≤
            Real.exp (K0 * |v - a|) *
              (riemannianEDistOf (I := I) g0 (z u) (z v)).toReal := by
          simpa only [g0] using hdist
        _ ≤ A * (riemannianEDistOf (I := I) g0 (z u) (z v)).toReal :=
          mul_le_mul_of_nonneg_right hexp ENNReal.toReal_nonneg
        _ ≤ A * (Cz * |v - u|) :=
          mul_le_mul_of_nonneg_left (hz u hu v hv) hA
        _ = A * Cz * |v - u| := by ring
    have hxmove : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b,
        (riemannianEDistOf (I := I) (S.base.metric (T - v))
          (x u) (x v)).toReal ≤ A * (Cx : Real) * |v - u| := by
      intro u hu v hv
      exact hmove u hu v hv x (Cx : Real) hx0
    have hymove : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b,
        (riemannianEDistOf (I := I) (S.base.metric (T - v))
          (y u) (y v)).toReal ≤ A * (Cy : Real) * |v - u| := by
      intro u hu v hv
      exact hmove u hu v hv y (Cy : Real) hy0
    let F : Real → Real := fun u ↦ (riemannianEDistOf (I := I)
      (S.base.metric (T - u)) (x u) (y u)).toReal
    have hstep : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b,
        F v ≤ Real.exp (K0 * |v - u|) * F u + C * |v - u| := by
      intro u hu v hv
      have htri1 := edist_real_tri (I := I) (S.base.metric (T - v))
        (x v) (x u) (y v)
      have htri2 := edist_real_tri (I := I) (S.base.metric (T - v))
        (x u) (y u) (y v)
      have hxu := hxmove u hu v hv
      rw [edistOf_comm (I := I) (S.base.metric (T - v)) (x v) (x u)] at htri1
      have hyu := hymove u hu v hv
      have hxy := hcmp v hv u hu (x u) (y u)
      calc
        F v ≤ (riemannianEDistOf (I := I) (S.base.metric (T - v))
              (x u) (x v)).toReal +
            (riemannianEDistOf (I := I) (S.base.metric (T - v))
              (x u) (y v)).toReal := by
          simpa only [F] using htri1
        _ ≤ (riemannianEDistOf (I := I) (S.base.metric (T - v))
              (x u) (x v)).toReal +
            ((riemannianEDistOf (I := I) (S.base.metric (T - v))
              (x u) (y u)).toReal +
            (riemannianEDistOf (I := I) (S.base.metric (T - v))
              (y u) (y v)).toReal) := add_le_add_right htri2 _
        _ ≤ A * (Cx : Real) * |v - u| +
            (Real.exp (K0 * |v - u|) * F u +
              A * (Cy : Real) * |v - u|) :=
          add_le_add hxu (add_le_add hxy hyu)
        _ = Real.exp (K0 * |v - u|) * F u + C * |v - u| := by
          dsimp only [C]
          ring
    let B : Real := A * F a + C * R
    have hB : 0 ≤ B := by
      exact add_nonneg (mul_nonneg hA ENNReal.toReal_nonneg) (mul_nonneg hC hR)
    have hFbound : ∀ u ∈ Icc a b, F u ≤ B := by
      intro u hu
      have h := hstep a ha u hu
      have hua : |u - a| ≤ R := by
        rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]
        dsimp only [R]
        linarith [hu.2]
      have hexp : Real.exp (K0 * |u - a|) ≤ A := by
        dsimp only [A]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hua hK0)
      calc
        F u ≤ Real.exp (K0 * |u - a|) * F a + C * |u - a| := h
        _ ≤ A * F a + C * R := add_le_add
          (mul_le_mul_of_nonneg_right hexp ENNReal.toReal_nonneg)
          (mul_le_mul_of_nonneg_left hua hC)
        _ = B := rfl
    let L : NNReal := ⟨K0 * A * B + C,
      add_nonneg (mul_nonneg (mul_nonneg hK0 hA) hB) hC⟩
    refine ⟨L, LipschitzOnWith.of_dist_le_mul ?_⟩
    intro u hu v hv
    let d : Real := |v - u|
    have hd : d ∈ Icc (0 : Real) R := by
      constructor
      · exact abs_nonneg _
      · dsimp only [d, R]
        rw [abs_sub_le_iff]
        constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
    have he1 : 1 ≤ Real.exp (K0 * d) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hK0 hd.1)
    have hediff : Real.exp (K0 * d) - 1 ≤ K0 * A * d := by
      simpa only [A] using exp_mul_sub_one hK0 hd
    have huv := hstep u hu v hv
    have hvu := hstep v hv u hu
    have huv' : F v - F u ≤ (K0 * A * B + C) * d := by
      calc
        F v - F u ≤ Real.exp (K0 * d) * F u + C * d - F u := by
          simpa only [d] using sub_le_sub_right huv (F u)
        _ = (Real.exp (K0 * d) - 1) * F u + C * d := by ring
        _ ≤ (Real.exp (K0 * d) - 1) * B + C * d :=
          add_le_add
            (mul_le_mul_of_nonneg_left (hFbound u hu)
              (sub_nonneg.mpr he1)) le_rfl
        _ ≤ (K0 * A * d) * B + C * d :=
          add_le_add (mul_le_mul_of_nonneg_right hediff hB) le_rfl
        _ = (K0 * A * B + C) * d := by ring
    have hvu' : F u - F v ≤ (K0 * A * B + C) * d := by
      have hd' : |u - v| = d := by
        dsimp only [d]
        exact abs_sub_comm u v
      rw [hd'] at hvu
      calc
        F u - F v ≤ Real.exp (K0 * d) * F v + C * d - F v :=
          sub_le_sub_right hvu (F v)
        _ = (Real.exp (K0 * d) - 1) * F v + C * d := by ring
        _ ≤ (Real.exp (K0 * d) - 1) * B + C * d :=
          add_le_add
            (mul_le_mul_of_nonneg_left (hFbound v hv)
              (sub_nonneg.mpr he1)) le_rfl
        _ ≤ (K0 * A * d) * B + C * d :=
          add_le_add (mul_le_mul_of_nonneg_right hediff hB) le_rfl
        _ = (K0 * A * B + C) * d := by ring
    rw [Real.dist_eq, Real.dist_eq]
    change |F u - F v| ≤ (L : Real) * |u - v|
    rw [show (L : Real) = K0 * A * B + C by rfl]
    dsimp only [d] at huv' hvu'
    have hvu'' : F u - F v ≤ (K0 * A * B + C) * |u - v| := by
      simpa only [abs_sub_comm] using hvu'
    have huv'' : F v - F u ≤ (K0 * A * B + C) * |u - v| := by
      simpa only [abs_sub_comm] using huv'
    exact abs_sub_le_iff.mpr ⟨hvu'', huv''⟩

omit [NeZero (Module.finrank Real E)] [IsManifold I 2 M]
  [SigmaCompactSpace M] in
/-- A global absolute Ricci bound makes the distance between two `C1` endpoint
curves absolutely continuous on a compact regular backward-time interval. -/
theorem dist_ac_Icc
    [ConnectedSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T a b K : Real}
    (hab : a ≤ b)
    (hreg : Icc (T - b) (T - a) ⊆ D.regular)
    (hric : ∀ q ∈ Icc (T - b) (T - a), ∀ z : M,
      ∀ v : TangentSpace I z,
        |ricciTensor (I := I) (S.base.metric q) z v v| ≤
          K * (S.base.metric q).inner z v v)
    (x y : Real → M)
    (hx : ContMDiffOn 𝓘(Real, Real) I 1 x (Icc a b))
    (hy : ContMDiffOn 𝓘(Real, Real) I 1 y (Icc a b)) :
    AbsolutelyContinuousOnInterval
      (fun u ↦ (riemannianEDistOf (I := I)
        (S.base.metric (T - u)) (x u) (y u)).toReal) a b := by
  obtain ⟨L, hL⟩ := dist_lip_Icc (I := I) S hS hab hreg hric x y hx hy
  have hLu : LipschitzOnWith L
      (fun u ↦ (riemannianEDistOf (I := I)
        (S.base.metric (T - u)) (x u) (y u)).toReal) (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hL
  exact hLu.absolutelyContinuousOnInterval

omit [NeZero (Module.finrank Real E)] [IsManifold I 2 M] in
/-- A global curvature bound makes the distance between two `C1` endpoint
curves absolutely continuous on a compact regular backward-time interval. -/
theorem dist_ac_rm
    [ConnectedSpace M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T a b K : Real}
    (hab : a ≤ b)
    (hreg : Icc (T - b) (T - a) ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - b) (T - a), ∀ z : M,
      Tensor0SBundle.normSq0S (I := I) (S.base.metric q) z 4
        (S.base.rm04 q z) ≤ K)
    (x y : Real → M)
    (hx : ContMDiffOn 𝓘(Real, Real) I 1 x (Icc a b))
    (hy : ContMDiffOn 𝓘(Real, Real) I 1 y (Icc a b)) :
    AbsolutelyContinuousOnInterval
      (fun u ↦ (riemannianEDistOf (I := I)
        (S.base.metric (T - u)) (x u) (y u)).toReal) a b := by
  have hquad := twoTensorQuadBound_of_solutions (I := I)
    (fun _ : Nat ↦ S) Set.univ (T - b) (T - a) K
    (hreg.trans D.regular_subset) (fun _ q hq z _ ↦ hRm q hq z)
  have hric : ∀ q ∈ Icc (T - b) (T - a), ∀ z : M,
      ∀ v : TangentSpace I z,
        |ricciTensor (I := I) (S.base.metric q) z v v| ≤
          ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K) *
            (S.base.metric q).inner z v v := by
    intro q hq z v
    rw [← metricRicciAt_apply_eq_ricciTensor]
    exact hquad.2 0 q hq z (Set.mem_univ z) v
  exact dist_ac_Icc (I := I) S hS hab hreg hric x y hx hy

end DifferentialGeometry.PDE.RicciFlow

end
