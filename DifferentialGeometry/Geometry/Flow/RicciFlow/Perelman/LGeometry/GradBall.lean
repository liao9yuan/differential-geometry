import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShiRm1Ball
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.RicciTowerTrace
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.HCGCompactness

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open Bundle Set
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal Topology BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [FiniteDimensional Real E] [CompleteSpace E] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem basis_eq_gON
    [NeZero (Module.finrank Real E)]
    (g : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0) :
    ∃ basis : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x),
      ∀ i, basis i = e i := by
  classical
  let cd : InnerProductSpace.Core Real (TangentSpace I x) :=
    g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x ↦ cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded Real
      {v : TangentSpace I x | RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI : InnerProductSpace Real (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  haveI : Nonempty (Fin (Module.finrank Real E)) :=
    ⟨⟨0, NeZero.pos _⟩⟩
  have hon : Orthonormal Real e := by
    rw [orthonormal_iff_ite]
    intro i j
    change g.inner x (e i) (e j) = _
    exact hON i j
  have hcard : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  let basis : Module.Basis (Fin (Module.finrank Real E)) Real
      (TangentSpace I x) := basisOfOrthonormalOfCardEqFinrank hon hcard
  refine ⟨basis, fun i ↦ ?_⟩
  exact congrFun (coe_basisOfOrthonormalOfCardEqFinrank hon hcard) i

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem sum_diag_trace
    [NeZero (Module.finrank Real E)]
    (g : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0)
    (B : Tensor0SSpace 2 I x) :
    ∑ i, B (vec2 (e i) (e i)) = metricTracePair0SAt (I := I) g B := by
  classical
  obtain ⟨basis, hbasis⟩ := basis_eq_gON (I := I) g x e hON
  have hONbasis : ∀ i j,
      g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
    intro i j
    rw [hbasis i, hbasis j]
    exact hON i j
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis hONbasis
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
    (identityInvMetric (Idx := Fin (Module.finrank Real E))) hinv B]
  simp only [identityInvMetric, diagonalInvMetric,
    ite_mul, one_mul, zero_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, hbasis i]
  · intro j _ hji
    simp only [if_neg (Ne.symm hji)]
  · intro hni
    exact absurd (Finset.mem_univ i) hni

omit [SigmaCompactSpace M] in
private theorem dRic_apply
    (g : SmoothRiemannianMetric I M)
    (X V W : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (x : M) :
    totalNabla0SFun (𝕜 := Real) (I := I) 2 (LeviCivita (I := I) g)
        (metricRicci (I := I) (M := M) g) x (vec3 (X x) (V x) (W x)) =
      nablaRicci (I := I) g X V W x := by
  have htotal := totalNabla0SFun_apply_section (𝕜 := Real) (I := I) 2
    (LeviCivita (I := I) g) X (metricRicci (I := I) (M := M) g) x
    (vec2 (V x) (W x))
  have hslots : Fin.cons (X x) (vec2 (V x) (W x)) =
      vec3 (X x) (V x) (W x) := by
    funext i
    fin_cases i <;> rfl
  rw [← hslots, htotal]
  rw [nabla0S_two_apply (I := I) (LeviCivita (I := I) g) X V W
    (metricRicci (I := I) (M := M) g) x]
  unfold nablaRicci
  have hfun :
      (fun p : M ↦ metricRicci (I := I) (M := M) g p
        (vec2 (V p) (W p))) =
      (fun p : M ↦ ricciTensor (I := I) g p (V p) (W p)) := by
    funext p
    rw [metricRicci_apply, metricRicciAt_apply_eq_ricciTensor]
  rw [hfun]
  simp only [metricRicci_apply, metricRicciAt_apply_eq_ricciTensor]

omit [SigmaCompactSpace M] in
private theorem sum_dRic_div
    [NeZero (Module.finrank Real E)]
    (g : SmoothRiemannianMetric I M) (x : M) (A : TangentSpace I x)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0) :
    ∑ i, totalNabla0SFun (𝕜 := Real) (I := I) 2 (LeviCivita (I := I) g)
        (metricRicci (I := I) (M := M) g) x (vec3 (e i) (e i) A) =
      (1 / 2 : Real) * nablaScalar (I := I) g
        (ContMDiffSection.exists_eq_at_gen
          (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A).choose x := by
  classical
  let X := (ContMDiffSection.exists_eq_at_gen
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A).choose
  have hX : X x = A := (ContMDiffSection.exists_eq_at_gen
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A).choose_spec
  let dRic := totalNabla0SFun (𝕜 := Real) (I := I) 2 (LeviCivita (I := I) g)
    (metricRicci (I := I) (M := M) g) x
  let dRic' : Tensor0SSpace 3 I x := dRic.domDomCongr (Equiv.swap 0 2)
  let Q : Tensor0SSpace 2 I x := tensor0S_curry (I := I) 2 x dRic' A
  let B : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i ↦ smoothOrthoFrame (I := I) g x i x
  have hBON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0 :=
    fun i j ↦ smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have htrace := (sum_diag_trace (I := I) g x e hON Q).trans
    (sum_diag_trace (I := I) g x B hBON Q).symm
  have hQ (v : TangentSpace I x) : Q (vec2 v v) = dRic (vec3 v v A) := by
    change (tensor0S_curry (I := I) 2 x dRic' A) (vec2 v v) = _
    rw [tensor0S_curry_apply_cons]
    change dRic.domDomCongr (Equiv.swap 0 2) _ = _
    rw [Tensor0SSpace.domDomCongr_apply]
    congr 1
    funext q
    fin_cases q <;> rfl
  rw [Finset.sum_congr rfl (fun i _ ↦ hQ (e i)),
    Finset.sum_congr rfl (fun i _ ↦ hQ (B i))] at htrace
  rw [htrace]
  rw [← contracted_second_bianchi (I := I) g X.contMDiff]
  apply Finset.sum_congr rfl
  intro i _
  let Bi : ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    ⟨smoothOrthoFrame (I := I) g x i,
      smoothOrthoFrame_smooth (I := I) g x i⟩
  simpa only [hX, Bi, B, ContMDiffSection.coeFn_mk] using
    (dRic_apply (I := I) g Bi Bi X x)

omit [SigmaCompactSpace M] in
private theorem ricTrace_grad
    [NeZero (Module.finrank Real E)] [BoundarylessManifold I M]
    (S : SolutionOn (I := I) (M := M) D) (q : Real) (x : M)
    (v : TangentSpace I x) :
    metricTraceFirstTwo0STensor (I := I) (S.base.metric q)
        (ricCovTower (I := I) (S.base.metric q) (S.base.metric q) 1 x)
        (fun _ ↦ v) =
      (1 / 2 : Real) * (S.base.metric q).inner x
        (gradientFun (I := I) (S.base.metric q) (S.scalar q) x) v := by
  classical
  let g := S.base.metric q
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h' i j
  have htrace :
      metricTraceFirstTwo0STensor (I := I) g
          (ricCovTower (I := I) g g 1 x) (fun _ ↦ v) =
        ∑ i : Fin (Module.finrank Real E),
          ricCovTower (I := I) g g 1 x (vec3 (basis i) (basis i) v) := by
    rw [metricTraceFirstTwo0STensor_apply,
      metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
        (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x))))
        hinv]
    simp only [metricTrace0S2InBasis, identityInvMetric, diagonalInvMetric,
      ite_mul, one_mul, zero_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
      congr 1
      funext a
      refine Fin.cases ?_ (fun a1 ↦ ?_) a
      · rfl
      · refine Fin.cases ?_ (fun _ ↦ ?_) a1 <;> rfl
    · intro j _ hji
      simp only [if_neg (Ne.symm hji)]
    · intro hni
      exact absurd (Finset.mem_univ i) hni
  rw [show S.base.metric q = g from rfl, htrace]
  have hsum := sum_dRic_div (I := I) g x v basis hON
  have hric :
      ricCovTower (I := I) g g 1 x =
        totalNabla0SFun (𝕜 := Real) (I := I) 2 (LeviCivita (I := I) g)
          (metricRicci (I := I) (M := M) g) x := by
    rfl
  rw [hric, hsum]
  let X := (ContMDiffSection.exists_eq_at_gen
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v).choose
  have hX : X x = v := (ContMDiffSection.exists_eq_at_gen
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v).choose_spec
  have hscalar : scalarCurv (I := I) g = S.scalar q := by
    funext y
    change scalarCurv (I := I) g y = metricScalarAt (I := I) g y
    exact (metricScalar_eq_scal (I := I) g y).symm
  congr 1
  rw [nablaScalar_def, hX, hscalar,
    DifferentialGeometry.extDerivFun_real_eq_mfderiv]
  exact (inner_gradientFun (I := I) g (S.scalar q) x v).symm

/-- The scalar-curvature gradient is controlled on the later, smaller
cylinder supplied by the ball-local first derivative Shi estimate. -/
theorem lGrad_ball
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M] [BoundarylessManifold I M] :
    ∃ theta C : Real, 0 < theta ∧ theta < 1 ∧ 0 < C ∧
      ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
        IsSolutionOn (I := I) S →
        ∀ {time : RealTimeInterval.FlowTime D}
          (B : FlowMetricBall S time), B.IsRmControlled →
          Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
          (∀ q ∈ Set.Icc
            ((time : Real) - theta * B.radius ^ 2) (time : Real),
              RiemannianMetricComplete (I := I) (S.base.metric q)) →
          ∀ q ∈ Set.Icc
            ((time : Real) - theta * B.radius ^ 2 / 2) (time : Real),
            ∀ x (v : TangentSpace I x),
              riemannianEDistOf (I := I) (S.base.metric q) B.center x <
                ENNReal.ofReal (B.radius / 16) →
              |(S.base.metric q).inner x
                  (gradientFun (I := I) (S.base.metric q) (S.scalar q) x) v| ≤
                (C / B.radius ^ 3) *
                  Real.sqrt ((S.base.metric q).inner x v v) := by
  letI : IsManifold I 1 M := IsManifold.of_le
    (I := I) (M := M) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))
  letI : IsManifold I 2 M := IsManifold.of_le
    (I := I) (M := M) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  obtain ⟨theta, K, htheta, htheta_one, hK, hShi⟩ :=
    shiRm1_ball (E := E) (I := I) (M := M)
  let dR : Real := Module.finrank Real E
  let C : Real := 2 * dR ^ 4 * K
  have hd : 0 < dR := by
    dsimp only [dR]
    exact Nat.cast_pos.mpr
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos (mul_pos (by norm_num) (pow_pos hd 4)) hK
  refine ⟨theta, C, htheta, htheta_one, hC, ?_⟩
  intro D S hS time B hB hreg hcomplete q hq x v hx
  let g := S.base.metric q
  let W : Real := nablaKRm04NormSqIntrinsic (I := I) S 1 q x
  let Ric1 : Tensor0SSpace 3 I x :=
    ricCovTower (I := I) g g 1 x
  let tr : Tensor0SSpace 1 I x :=
    metricTraceFirstTwo0STensor (I := I) g Ric1
  have hRic :
      normSq0S (I := I) g x 3 Ric1 ≤ dR ^ 5 * W := by
    simpa only [dR, W, Ric1, g, nablaKRm04NormSqIntrinsic,
      Nat.reduceAdd] using
      (ricTower_normSq_le (I := I) S q 1 x)
  have hTrace :
      normSq0S (I := I) g x 1 tr ≤
        dR ^ 3 * normSq0S (I := I) g x 3 Ric1 := by
    simpa only [dR, tr, Ric1, Nat.reduceAdd] using
      (Tensor0SBundle.trace_normSq_rank_le
        (I := I) g (s := 1) Ric1)
  have hTraceW :
      normSq0S (I := I) g x 1 tr ≤ dR ^ 8 * W := by
    calc
      _ ≤ dR ^ 3 * normSq0S (I := I) g x 3 Ric1 := hTrace
      _ ≤ dR ^ 3 * (dR ^ 5 * W) :=
        mul_le_mul_of_nonneg_left hRic (pow_nonneg hd.le 3)
      _ = dR ^ 8 * W := by ring
  have hsqrtD : Real.sqrt (dR ^ 8) = dR ^ 4 := by
    rw [show dR ^ 8 = (dR ^ 4) ^ 2 by ring,
      Real.sqrt_sq (pow_nonneg hd.le 4)]
  have hroot :
      Real.sqrt (normSq0S (I := I) g x 1 tr) ≤
        dR ^ 4 * Real.sqrt W := by
    calc
      _ ≤ Real.sqrt (dR ^ 8 * W) := Real.sqrt_le_sqrt hTraceW
      _ = Real.sqrt (dR ^ 8) * Real.sqrt W :=
        Real.sqrt_mul (pow_nonneg hd.le 8) W
      _ = dR ^ 4 * Real.sqrt W := by rw [hsqrtD]
  have happ0 :=
    Tensor0SBundle.abs_apply_le_norm0S
      (I := I) g x 1 tr (fun _ : Fin 1 ↦ v)
  have happ :
      |tr (fun _ : Fin 1 ↦ v)| ≤
        Real.sqrt (normSq0S (I := I) g x 1 tr) *
          Real.sqrt (g.inner x v v) := by
    simpa only [Fintype.prod_unique] using happ0
  have hBianchi :
      tr (fun _ : Fin 1 ↦ v) =
        (1 / 2 : Real) * g.inner x
          (gradientFun (I := I) g (S.scalar q) x) v := by
    simpa only [tr, Ric1, g] using
      (ricTrace_grad (I := I) S q x v)
  have hradii : B.radius / 16 ≤ B.radius / 8 := by
    nlinarith [B.radius_pos]
  have hx8 :
      riemannianEDistOf (I := I) (S.base.metric q) B.center x <
        ENNReal.ofReal (B.radius / 8) :=
    hx.trans_le (ENNReal.ofReal_le_ofReal hradii)
  have hShiW : Real.sqrt W ≤ K / B.radius ^ 3 := by
    simpa only [W] using
      (hShi hS B hB hreg hcomplete q hq x hx8)
  have hrootShi :
      Real.sqrt (normSq0S (I := I) g x 1 tr) ≤
        dR ^ 4 * (K / B.radius ^ 3) :=
    hroot.trans
      (mul_le_mul_of_nonneg_left hShiW (pow_nonneg hd.le 4))
  let pair : Real :=
    g.inner x (gradientFun (I := I) g (S.scalar q) x) v
  have hpair : pair = 2 * tr (fun _ : Fin 1 ↦ v) := by
    dsimp only [pair]
    linarith [hBianchi]
  change |pair| ≤ (C / B.radius ^ 3) * Real.sqrt (g.inner x v v)
  calc
    |pair| = 2 * |tr (fun _ : Fin 1 ↦ v)| := by
      rw [hpair, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
    _ ≤ 2 * (Real.sqrt (normSq0S (I := I) g x 1 tr) *
        Real.sqrt (g.inner x v v)) :=
      mul_le_mul_of_nonneg_left happ (by norm_num)
    _ ≤ 2 * ((dR ^ 4 * (K / B.radius ^ 3)) *
        Real.sqrt (g.inner x v v)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hrootShi (Real.sqrt_nonneg _))
        (by norm_num)
    _ = (C / B.radius ^ 3) * Real.sqrt (g.inner x v v) := by
      dsimp only [C]
      ring

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
