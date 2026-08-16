import DifferentialGeometry.Analysis.Calculus.RatioMonotonicity
import DifferentialGeometry.Geometry.Comparison.RiemannianDistContinuity
import DifferentialGeometry.Geometry.Comparison.Variation.EndpointNonnegative
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentDomain
import DifferentialGeometry.Geometry.Exponential.IntrinsicFramedJacobi
import Mathlib.Analysis.Calculus.LHopital

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open CovariantDerivativeAlong Exponential NormalCoordinates
open VolumeComparison
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem jacobi_ratio_anti
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {p : M} {u w : TangentSpace I p}
    (hseg : u ∈ SegDom (I := I) g hEnorm p)
    (hu : 0 < g.inner p u u)
    (hperp : g.inner p u w = 0)
    (hsec : NonnegSecMetric (I := I) (M := M) g) :
    let γ := intrinsicGeodesic (I := I) g hEnorm p u
    let J := intrinsicJacobi (I := I) g hEnorm p u w
    AntitoneOn
      (fun t => g.inner (γ t) (J t) (J t) / t ^ 2)
      (Ioo (0 : ℝ) 1) := by
  dsimp only
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  let J := intrinsicJacobi (I := I) g hEnorm p u w
  let F : ℝ → ℝ := fun t => g.inner (γ t) (J t) (J t)
  let P : ℝ → ℝ := fun t =>
    g.inner (γ t) (covDerivAlong (I := I) g γ J t) (J t)
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := by
    simpa only [γ] using intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
  have hF : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt F (2 * P t) t := by
    intro t _ht
    have hinner := inner_deriv_at (I := I) (n := (∞ : WithTop ℕ∞))
      (by simp) g γ J J t hγ.contMDiffAt
      (intrJacobi_diff (I := I) g hEnorm p u w t).1
      (intrJacobi_diff (I := I) g hEnorm p u w t).1
    rw [g.symm (γ t) (J t) (covDerivAlong (I := I) g γ J t)] at hinner
    simpa only [F, P, two_mul] using hinner
  have hP : ∀ t ∈ Ioo (0 : ℝ) 1, t * P t ≤ F t := by
    intro t ht
    have htseg : t • u ∈ SegDom (I := I) g hEnorm p :=
      segDom_smul (I := I) g hEnorm hseg ht.1.le ht.2.le
    have htu : 0 < g.inner p (t • u) (t • u) := by
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      exact mul_pos ht.1 (mul_pos ht.1 hu)
    have htw : g.inner p (t • u) (t • w) = 0 := by
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
        hperp, mul_zero]
    let δ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p (t • u)
    let K := intrinsicJacobi (I := I) g hEnorm p (t • u) (t • w)
    have hδ : δ = fun s => γ (t * s) := by
      funext s
      simpa only [δ, γ] using intrGeo_smul_apply (I := I) g hEnorm p u t s
    have hK : K = fun s => J (t * s) := by
      funext s
      simpa only [K, J] using
        intrJacobi_smul (I := I) g hEnorm p (u : E) (w : E) t s
    have hpair := intrJacobi_pair_le (I := I) g hEnorm
      (show Real.sqrt (g.inner p (t • u) (t • u)) =
        (riemannianEDist I p
          (expMapIntrinsic (I := I) g hEnorm p (t • u))).toReal from htseg)
      htu htw hsec
    change g.inner (δ 1) (covDerivAlong (I := I) g δ K 1) (K 1) ≤
      g.inner (δ 1) (K 1) (K 1) at hpair
    rw [hδ, hK] at hpair
    dsimp only at hpair
    rw [mul_one t] at hpair
    have hD := covDeriv_comp_mul (I := I) g γ J t 1
    rw [hD] at hpair
    rw [mul_one t] at hpair
    have hlin :
        g.inner (γ t) (t • covDerivAlong (I := I) g γ J t) (J t) =
          t * g.inner (γ t) (covDerivAlong (I := I) g γ J t) (J t) := by
      have hmap := (g.inner (γ t)).map_smul t
        (covDerivAlong (I := I) g γ J t)
      exact congrArg (fun L => L (J t)) hmap
    calc
      t * P t =
          g.inner (γ t) (t • covDerivAlong (I := I) g γ J t) (J t) := by
        simpa only [P] using hlin.symm
      _ ≤ g.inner (γ t) (J t) (J t) := hpair
      _ = F t := rfl
  refine ratio_anti_of_cross (f' := fun t => 2 * P t)
    (g' := fun t => 2 * t) hF ?_ ?_ ?_
  · intro t _ht
    convert hasDerivAt_pow 2 t using 1
    all_goals ring
  · intro t ht
    exact sq_pos_of_pos ht.1
  · intro t ht
    have hpair := hP t ht
    calc
      (2 * P t) * t ^ 2 = (2 * t) * (t * P t) := by ring
      _ ≤ (2 * t) * F t :=
        mul_le_mul_of_nonneg_left hpair (mul_nonneg (by norm_num) ht.1.le)
      _ = F t * (2 * t) := by ring

omit [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem jacobi_ratio_tendsto
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u w : TangentSpace I p) :
    let γ := intrinsicGeodesic (I := I) g hEnorm p u
    let J := intrinsicJacobi (I := I) g hEnorm p u w
    Tendsto
      (fun t => g.inner (γ t) (J t) (J t) / t ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (g.inner p w w)) := by
  dsimp only
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  let J := intrinsicJacobi (I := I) g hEnorm p u w
  let DJ : ℝ → E := fun t => covDerivAlong (I := I) g γ J t
  let F : ℝ → ℝ := fun t => g.inner (γ t) (J t) (J t)
  let P : ℝ → ℝ := fun t => g.inner (γ t) (DJ t) (J t)
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := by
    simpa only [γ] using intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
  have hF : ∀ t : ℝ, HasDerivAt F (2 * P t) t := by
    intro t
    have hinner := inner_deriv_at (I := I) (n := (∞ : WithTop ℕ∞))
      (by simp) g γ J J t hγ.contMDiffAt
      (intrJacobi_diff (I := I) g hEnorm p u w t).1
      (intrJacobi_diff (I := I) g hEnorm p u w t).1
    rw [g.symm (γ t) (J t) (covDerivAlong (I := I) g γ J t)] at hinner
    simpa only [F, P, DJ, two_mul] using hinner
  have hP : ∀ t : ℝ, HasDerivAt P
      (g.inner (γ t) (covDerivAlong (I := I) g γ DJ t) (J t) +
        g.inner (γ t) (DJ t) (DJ t)) t := by
    intro t
    simpa only [P] using
      inner_deriv_at (I := I) (n := (∞ : WithTop ℕ∞))
        (by simp) g γ DJ J t hγ.contMDiffAt
        (intrJacobi_diff (I := I) g hEnorm p u w t).2
        (intrJacobi_diff (I := I) g hEnorm p u w t).1
  have hγ0 : γ 0 = p := by
    simpa only [γ] using intrinsicGeodesic_zero (I := I) g hEnorm p u
  have hJ0 : J 0 = 0 := by
    simpa only [J] using intrinsicJacobi_zero (I := I) g hEnorm p u w
  have hDJ0 : DJ 0 = w := by
    simpa only [DJ, γ, J, intrinsicJacobi] using
      intrinsic_jacobi_d0 (I := I) g hEnorm p (u : E) (w : E)
  have hF0 : F 0 = 0 := by
    simp only [F, hJ0, map_zero]
  have hP0 : P 0 = 0 := by
    simp only [P, hJ0]
    exact (g.inner (γ 0) (DJ 0)).map_zero
  have hPderiv : HasDerivAt P (g.inner p w w) 0 := by
    have h := hP 0
    rw [hγ0, hJ0, hDJ0] at h
    have hz : g.inner p (covDerivAlong (I := I) g γ DJ 0) 0 = 0 :=
      (g.inner p (covDerivAlong (I := I) g γ DJ 0)).map_zero
    refine h.congr_deriv ?_
    exact add_eq_right.mpr hz
  have hPslope : Tendsto (fun t => P t / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (g.inner p w w)) := by
    simpa only [zero_add, hP0, sub_zero, smul_eq_mul, div_eq_mul_inv,
      mul_comm] using hPderiv.tendsto_slope_zero_right
  have hdiv : Tendsto (fun t => (2 * P t) / (2 * t))
      (𝓝[>] (0 : ℝ)) (𝓝 (g.inner p w w)) := by
    refine hPslope.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    field_simp [ne_of_gt (show 0 < t from ht)]
  have hFt : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [hF0] using
      (hF 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hsq : Tendsto (fun t : ℝ => t ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using
      ((continuous_id.pow 2).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hsqDeriv : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    intro t
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      hasDerivAt_pow 2 t
  exact HasDerivAt.lhopital_zero_right_on_Ioo (a := (0 : ℝ)) (b := 1)
    zero_lt_one (fun t _ht => hF t)
    (fun t _ht => hsqDeriv t)
    (fun t ht => mul_ne_zero (by norm_num) (ne_of_gt ht.1)) hFt hsq hdiv

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem intrJacobi_sq_le
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {p : M} {u w : TangentSpace I p}
    (hseg : u ∈ SegDom (I := I) g hEnorm p)
    (hu : 0 < g.inner p u u)
    (hperp : g.inner p u w = 0)
    (hsec : NonnegSecMetric (I := I) (M := M) g) :
    let γ := intrinsicGeodesic (I := I) g hEnorm p u
    let J := intrinsicJacobi (I := I) g hEnorm p u w
    g.inner (γ 1) (J 1) (J 1) ≤ g.inner p w w := by
  dsimp only
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  let J := intrinsicJacobi (I := I) g hEnorm p u w
  let F : ℝ → ℝ := fun t => g.inner (γ t) (J t) (J t)
  let Q : ℝ → ℝ := fun t => F t / t ^ 2
  have hanti : AntitoneOn Q (Ioo (0 : ℝ) 1) := by
    simpa only [Q, F, γ, J] using
      jacobi_ratio_anti (I := I) g hEnorm hseg hu hperp hsec
  have hlim : Tendsto Q (𝓝[>] (0 : ℝ)) (𝓝 (g.inner p w w)) := by
    simpa only [Q, F, γ, J] using
      jacobi_ratio_tendsto (I := I) g hEnorm p u w
  have hint : ∀ t ∈ Ioo (0 : ℝ) 1, F t ≤ t ^ 2 * g.inner p w w := by
    intro t ht
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q t ≤ Q s := by
      filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
      exact hanti ⟨hs.1, hs.2.trans ht.2⟩ ht hs.2.le
    have hratio : Q t ≤ g.inner p w w := ge_of_tendsto hlim hev
    have hsq : 0 < t ^ 2 := sq_pos_of_pos ht.1
    simpa only [mul_comm] using (div_le_iff₀ hsq).mp hratio
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := by
    simpa only [γ] using intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
  have hFderiv : HasDerivAt F
      (g.inner (γ 1) (covDerivAlong (I := I) g γ J 1) (J 1) +
        g.inner (γ 1) (J 1) (covDerivAlong (I := I) g γ J 1)) 1 := by
    simpa only [F] using
      inner_deriv_at (I := I) (n := (∞ : WithTop ℕ∞))
        (by simp) g γ J J 1 hγ.contMDiffAt
        (intrJacobi_diff (I := I) g hEnorm p u w 1).1
        (intrJacobi_diff (I := I) g hEnorm p u w 1).1
  have hleft : Tendsto F (𝓝[<] (1 : ℝ)) (𝓝 (F 1)) :=
    hFderiv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun t : ℝ => t ^ 2 * g.inner p w w)
      (𝓝[<] (1 : ℝ)) (𝓝 (g.inner p w w)) := by
    simpa using ((continuous_id.pow 2).mul continuous_const).tendsto (1 : ℝ)
      |>.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
  exact hint t ht

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem intrJacobi_le
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {p : M} {u w : TangentSpace I p}
    (hseg : u ∈ SegDom (I := I) g hEnorm p)
    (hu : 0 < g.inner p u u)
    (hsec : NonnegSecMetric (I := I) (M := M) g) :
    let γ := intrinsicGeodesic (I := I) g hEnorm p u
    let J := intrinsicJacobi (I := I) g hEnorm p u w
    g.inner (γ 1) (J 1) (J 1) ≤ g.inner p w w := by
  dsimp only
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  let q : M := γ 1
  let Z : TangentSpace I q := curveVelocity (I := I) γ 1
  let D : ℝ := g.inner p u u
  let a : ℝ := g.inner p u w / D
  let v : TangentSpace I p := w - a • u
  let Jv : TangentSpace I q := intrinsicJacobi (I := I) g hEnorm p u v 1
  let Jw : TangentSpace I q := intrinsicJacobi (I := I) g hEnorm p u w 1
  let dexp : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) I
      (fun z : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from z)) (u : E)
  have hDpos : 0 < D := hu
  have hvperp : g.inner p u v = 0 := by
    calc
      g.inner p u v = g.inner p u w - g.inner p u (a • u) :=
        (g.inner p u).map_sub w (a • u)
      _ = g.inner p u w - a * g.inner p u u := by
        exact congrArg (fun r : ℝ => g.inner p u w - r)
          (by simpa only [smul_eq_mul] using (g.inner p u).map_smul a u)
      _ = 0 := by
        change g.inner p u w - (g.inner p u w / D) * D = 0
        rw [div_mul_cancel₀ _ hDpos.ne', sub_self]
  have hwdec : w = v + a • u := by
    dsimp only [v]
    abel
  have hjac (z : TangentSpace I p) :
      (intrinsicJacobi (I := I) g hEnorm p u z 1 : E) = dexp z := by
    simpa only [intrinsicJacobi, dexp] using
      intrinsic_jacobi_one (I := I) g hEnorm p (u : E) (z : E)
  have hzu : dexp u = Z := by
    rw [← hjac u]
    simpa only [Z, q, γ] using intrJacobi_self (I := I) g hEnorm p u
  have hJdec : Jw = Jv + a • Z := by
    change (Jw : E) = (Jv : E) + a • (Z : E)
    rw [show (Jw : E) = dexp w by simpa only [Jw] using hjac w]
    rw [show (Jv : E) = dexp v by simpa only [Jv] using hjac v]
    rw [← hzu]
    calc
      dexp w = dexp (v + a • u) := congrArg dexp hwdec
      _ = dexp v + dexp (a • u) := dexp.map_add v (a • u)
      _ = dexp v + a • dexp u :=
        congrArg (fun z : E => dexp v + z) (dexp.map_smul a u)
  have hDend : g.inner q Z Z = D := by
    simpa only [q, Z, γ, D] using
      intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u 1
  have hJvZ : g.inner q Z Jv = 0 := by
    simpa only [q, Z, γ, Jv, hvperp] using
      intrinsicJacobi_perp (I := I) g hEnorm p u v
  have hZJv : g.inner q Jv Z = 0 :=
    (g.symm q Jv Z).trans hJvZ
  have hJvle : g.inner q Jv Jv ≤ g.inner p v v := by
    simpa only [q, γ, Jv] using
      intrJacobi_sq_le (I := I) g hEnorm hseg hu hvperp hsec
  have hout : g.inner q Jw Jw = g.inner q Jv Jv + a ^ 2 * D := by
    rw [hJdec]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hJvZ, hZJv, hDend]
    ring
  have hin : g.inner p w w = g.inner p v v + a ^ 2 * D := by
    rw [hwdec]
    have hvu : g.inner p v u = 0 := (g.symm p v u).trans hvperp
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hvperp, hvu, D]
    ring
  rw [hout, hin]
  simpa only [add_comm] using add_le_add_right hJvle (a ^ 2 * D)

section Framed

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NeZero (Module.finrank ℝ V)] [CompleteSpace V]
variable {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ V K}
  [J.Boundaryless]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace K N]
  [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem intrFrame_deriv_le
    [RiemannianBundle (fun x : N ↦ TangentSpace J x)]
    [PseudoEMetricSpace N] [IsRiemannianManifold J N] [CompleteSpace N]
    [ConnectedSpace N]
    [IsContinuousRiemannianBundle V (fun x : N ↦ TangentSpace J x)]
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (x : N) (v : TangentSpace J x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : N) {z : V}
    (hseg : normalFrame (E := V) (I := J) g p z ∈
      SegDom (I := J) g hEnorm p)
    (hsec : NonnegSecMetric (I := J) (M := N) g) (v : V) :
    g.inner (intrinsicFramedExp (E := V) (I := J) g hEnorm p z)
      (mfderiv 𝓘(ℝ, V) J
        (intrinsicFramedExp (E := V) (I := J) g hEnorm p) z v)
      (mfderiv 𝓘(ℝ, V) J
        (intrinsicFramedExp (E := V) (I := J) g hEnorm p) z v) ≤
      ‖v‖ ^ 2 := by
  by_cases hz : z = 0
  · subst z
    rw [intrFrame_zero (E := V) (I := J) g hEnorm p,
      intrFrame_deriv_zero (E := V) (I := J) g hEnorm p]
    have hclm : intrFrameCLM (E := V) (I := J) g p v =
        normalFrame (E := V) (I := J) g p v :=
      intrFrameCLM_apply (E := V) (I := J) g p v
    calc
      g.inner p (intrFrameCLM (E := V) (I := J) g p v)
          (intrFrameCLM (E := V) (I := J) g p v) =
          g.inner p (normalFrame (E := V) (I := J) g p v)
            (normalFrame (E := V) (I := J) g p v) :=
        congrArg₂ (fun x y : TangentSpace J p => g.inner p x y) hclm hclm
      _ = Inner.inner ℝ v v := normalFrame_inner (E := V) (I := J) g p v v
      _ = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      _ ≤ ‖v‖ ^ 2 := le_rfl
  have hu : 0 < g.inner p
      (normalFrame (E := V) (I := J) g p z)
      (normalFrame (E := V) (I := J) g p z) := by
    rw [normalFrame_inner (E := V), real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hz)
  have h := intrJacobi_le (I := J) g hEnorm hseg hu hsec
    (w := normalFrame (E := V) (I := J) g p v)
  simpa only [intrFrame_apply, expMapIntrinsic_def, intrFrame_deriv,
    normalFrame_inner (E := V),
    real_inner_self_eq_norm_sq] using h

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem intrFrame_edist_le
    [RiemannianBundle (fun x : N ↦ TangentSpace J x)]
    [PseudoEMetricSpace N] [IsRiemannianManifold J N] [CompleteSpace N]
    [ConnectedSpace N]
    [IsContinuousRiemannianBundle V (fun x : N ↦ TangentSpace J x)]
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (x : N) (v : TangentSpace J x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : N) {U : Set V}
    (hU : U ⊆ (intrFrameDiffeo (E := V) (I := J) g hEnorm p).source)
    (hseg : ∀ z ∈ U, normalFrame (E := V) (I := J) g p z ∈
      SegDom (I := J) g hEnorm p)
    (hsec : NonnegSecMetric (I := J) (M := N) g)
    {u v : V} (huv : segment ℝ u v ⊆ U) :
    riemannianEDist J
        (intrinsicFramedExp (E := V) (I := J) g hEnorm p u)
        (intrinsicFramedExp (E := V) (I := J) g hEnorm p v) ≤
      ENNReal.ofReal (dist u v) := by
  let Ψ := intrFrameDiffeo (E := V) (I := J) g hEnorm p
  have hspd : ∀ z ∈ U, ∀ ξ : V,
      ‖mfderiv 𝓘(ℝ, V) J Ψ z ξ‖ₑ ≤ ENNReal.ofReal (1 * ‖ξ‖) := by
    intro z hz ξ
    rw [hEnorm]
    apply ENNReal.ofReal_le_ofReal
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    simpa only [Ψ, intrFrameDiffeo_apply, one_mul] using
      intrFrame_deriv_le (J := J) g hEnorm p (hseg z hz) hsec ξ
  have h := param_edist_le (I := J) Ψ hU hspd huv
  simpa only [Ψ, intrFrameDiffeo_apply, one_mul] using h

end Framed

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
