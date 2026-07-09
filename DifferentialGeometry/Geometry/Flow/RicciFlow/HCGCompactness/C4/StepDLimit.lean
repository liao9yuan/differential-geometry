import DifferentialGeometry.Geometry.Topology.DirectLimitManifold
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedRiemannian
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCompactness
import DifferentialGeometry.Geometry.Comparison.HopfRinowProper

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 Step D, D3e: the limit `PointedRiemannianManifold`

Assembles the `HCGCompactness.PointedRiemannianManifold` bundle for the direct-limit manifold
`S.Lim` of a `SmoothSeqSystem` (`Geometry/Topology/DirectLimitManifold.lean`).  Every field is
now available from D3a–D3d:

* `charted` — `SeqSystem.instChartedSpaceLim` (D3a),
* `smooth` — `SmoothSeqSystem.instIsManifoldLim` (D3b),
* `sigmaCompact`, `t2` — `SeqSystem.instSigmaCompactSpaceLim` / `instT2SpaceLim` (D3c),
* `t2TangentBundle` — `SmoothSeqSystem.instT2SpaceTangentBundleLim` (D3c, via the general
  `FiberBundle.t2Space_totalSpace`),
* `metric` — `SmoothSeqSystem.limitMetric` (D3d): per-factor metrics with the isometry cocycle
  (`MetricCocycle`, D2c's conclusion shape) glue to `g∞` with `(incl k)^* g∞ = g k`
  (`limitMetric_pullback`).

`limitPointedCoc` is the full D3 endpoint (metrics + cocycle in, pointed bundle out);
`limitPointed` stays as the metric-generic form. -/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

/-- **D3e — the limit pointed Riemannian manifold** (MSM135 `lbl408`).  Carrier `S.Lim`, basepoint
`incl 0 O₀`, and the smooth Riemannian metric `ginf` (the D3d producer, supplied as input).  All the
topological/manifold structure fields (`charted`/`smooth`/`sigmaCompact`/`t2`/`t2TangentBundle`) are
synthesized from the D3a–D3c instances in `DirectLimitManifold.lean`. -/
def limitPointed
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
    [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
    [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]
    (S : SmoothSeqSystem I A) (O₀ : A 0)
    (ginf : SmoothRiemannianMetric I S.toSeqSystem.Lim) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) where
  M := S.toSeqSystem.Lim
  basepoint := S.toSeqSystem.incl 0 O₀
  metric := ginf

/-- **The full D3 endpoint (MSM135 `lbl408`): the limit pointed Riemannian manifold from
per-factor metrics.**  Given per-factor metrics `g k` with the isometry cocycle (D2c's conclusion
shape), the direct limit carries the pointed bundle with metric `g∞ = limitMetric` (D3d), so that
`(incl k)^* g∞ = g k` (`SmoothSeqSystem.limitMetric_pullback`). -/
def limitPointedCoc
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
    [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
    [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]
    (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) :=
  limitPointed S O₀ (S.limitMetric g hg)

section StepD4a

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
  [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]

/-- **The stage members as pointed Riemannian manifolds**: carrier `A k`, basepoint the
transported `F_{0≤k} O₀`, metric `g k`.  The `X.obj k` of the D4a comparison-map package. -/
def factorPointed (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (k : ℕ) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) where
  M := A k
  basepoint := S.toSeqSystem.F (Nat.zero_le k) O₀
  metric := g k

/-- The stage sequence of `factorPointed` members. -/
def factorSeq (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) where
  obj := factorPointed S O₀ g

/-- **The stage ranges exhaust the limit by open sets** (MSM135 `lbl379` packaged for the
comparison maps): open (stage inclusions are open embeddings), monotone (`range_incl_mono`),
and every compact factors through a stage (`isCompact_exists`). -/
theorem rangeExhausts (S : SmoothSeqSystem I A) :
    ExhaustsByOpen (fun k => Set.range (S.toSeqSystem.incl k)) where
  isOpen k := (S.toSeqSystem.incl_isOpenEmb k).isOpen_range
  mono_step k := S.toSeqSystem.range_incl_mono (Nat.le_succ k)
  subset K hK := by
    obtain ⟨k₀, Kk, _, hKeq⟩ := S.toSeqSystem.isCompact_exists hK
    refine ⟨k₀, fun k hk => ?_⟩
    rw [hKeq]
    exact (Set.image_subset_range _ _).trans (S.toSeqSystem.range_incl_mono hk)

/-- **D4a — the Cheeger–Gromov comparison maps of the limit** (MSM135 Step D, L2048–2085 shape):
the inverses `Φ_k := (incl k)⁻¹` of the stage inclusions, packaged as
`PointedRiemannianCGMaps` from the stage sequence to the limit pointed manifold.  Sources are the
stage ranges (an open exhaustion by `rangeExhausts`), the basepoint lies in every source, and it
maps to the transported stage basepoints (`invIncl_incl_le`). -/
noncomputable def limitCGMaps (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g) :
    PointedRiemannianCGMaps.{u, uE, uH} (I := I)
      (X := factorSeq S O₀ g)
      (L := (limitPointedCoc S O₀ g hg : PointedRiemannianManifold.{u, uE, uH} (I := I)))
      (subseq := id) where
  partialDiffeomorph k := S.inclPartialDiffeo k
  source_exhausts := rangeExhausts S
  base_mem k := ⟨S.toSeqSystem.F (Nat.zero_le k) O₀, S.toSeqSystem.incl_comp (Nat.zero_le k) O₀⟩
  basepoint_map k := S.invIncl_incl_le (Nat.zero_le k) O₀

end StepD4a

section StepD5

open Bundle


variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
  [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Pointwise isometry of the stage inclusions (D5 cornerstone).**  Under the
`RiemannianBundle` structures of the limit metric and the stage metric, the stage-inclusion
derivative preserves the extended norm — `limitMetric_pullback` read through the fiber
inner-product bridge (the `TangentNormDiamond` idiom). -/
theorem enorm_mfd_incl (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (k : ℕ) (a : A k) (v : TangentSpace I a) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
      ⟨(g k).toRiemannianMetric⟩
    ‖mfderiv I I (S.toSeqSystem.incl k) a v‖ₑ = ‖v‖ₑ := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
    ⟨(g k).toRiemannianMetric⟩
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
    norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  have h1 : (inner ℝ (mfderiv I I (S.toSeqSystem.incl k) a v)
        (mfderiv I I (S.toSeqSystem.incl k) a v) : ℝ)
      = (S.limitMetric g hg).inner (S.toSeqSystem.incl k a)
          (mfderiv I I (S.toSeqSystem.incl k) a v)
          (mfderiv I I (S.toSeqSystem.incl k) a v) := rfl
  have h2 : (inner ℝ v v : ℝ) = (g k).inner a v v := rfl
  rw [h1, h2, S.limitMetric_pullback g hg k a v v]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Stage inclusions preserve path length (D5).**  For a `C¹` path in a stage, the pushed
path in the limit has the same `pathELength` — pointwise the chain rule plus the isometry
`enorm_mfd_incl`. -/
theorem pathELength_incl (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (k : ℕ) {γ : ℝ → A k} {t₀ t₁ : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc t₀ t₁)) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
      ⟨(g k).toRiemannianMetric⟩
    Manifold.pathELength I (S.toSeqSystem.incl k ∘ γ) t₀ t₁
      = Manifold.pathELength I γ t₀ t₁ := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
    ⟨(g k).toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  have hγt : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    ((hγ.mdifferentiableOn one_ne_zero) t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  have hincl : MDifferentiableAt I I (S.toSeqSystem.incl k) (γ t) :=
    (S.contMDiff_incl k).mdifferentiableAt (by decide)
  have hcomp : mfderiv 𝓘(ℝ, ℝ) I (S.toSeqSystem.incl k ∘ γ) t
      = (mfderiv I I (S.toSeqSystem.incl k) (γ t)).comp (mfderiv 𝓘(ℝ, ℝ) I γ t) :=
    mfderiv_comp t hincl hγt
  rw [hcomp]
  exact enorm_mfd_incl S g hg k (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The stage inclusions are 1-Lipschitz for the Riemannian edistances (D5).**  Every stage
`C¹` path pushes to a limit path of the same length (`pathELength_incl`), so the infimum over
limit paths is at most the infimum over stage paths.  (The reverse inequality is not abstract —
a limit path may leave the stage range; the book recovers it on balls via the `2^k` exhaustion.) -/
theorem edist_incl_le (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (k : ℕ) (a b : A k) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
      ⟨(g k).toRiemannianMetric⟩
    Manifold.riemannianEDist I (S.toSeqSystem.incl k a) (S.toSeqSystem.incl k b)
      ≤ Manifold.riemannianEDist I a b := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
    ⟨(g k).toRiemannianMetric⟩
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  obtain ⟨γ, hγ0, hγ1, hγC, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr
  have hle : Manifold.riemannianEDist I (S.toSeqSystem.incl k a) (S.toSeqSystem.incl k b)
      ≤ Manifold.pathELength I (S.toSeqSystem.incl k ∘ γ) 0 1 :=
    Manifold.riemannianEDist_le_pathELength
      (((S.contMDiff_incl k).of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)).comp_contMDiffOn hγC)
      (by rw [Function.comp_apply, hγ0]) (by rw [Function.comp_apply, hγ1]) zero_le_one
  refine hle.trans ?_
  rw [pathELength_incl S g hg k hγC]
  exact hlen.le

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Limit paths inside a stage range pull back at equal length (D5).**  If a `C¹` limit path
stays in `range (incl k)` on `[t₀, t₁]`, its `(incl k)⁻¹`-pullback is a stage path of the same
`pathELength` — `pathELength_incl` applied to the pullback plus `incl ∘ (incl)⁻¹ = id` on the
range.  This is the reverse comparison the book uses on balls (`lbl408` completeness): limit
almost-geodesics between points of a deep ball stay in a stage range, so stage distances are
controlled by limit distances there. -/
theorem pathELength_invIncl (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (k : ℕ) {δ : ℝ → S.toSeqSystem.Lim} {t₀ t₁ : ℝ}
    (hδ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 δ (Set.Icc t₀ t₁))
    (hδr : ∀ t ∈ Set.Icc t₀ t₁, δ t ∈ Set.range (S.toSeqSystem.incl k)) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
      ⟨(g k).toRiemannianMetric⟩
    Manifold.pathELength I (Function.invFun (S.toSeqSystem.incl k) ∘ δ) t₀ t₁
      = Manifold.pathELength I δ t₀ t₁ := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
    ⟨(g k).toRiemannianMetric⟩
  have hpull : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (Function.invFun (S.toSeqSystem.incl k) ∘ δ)
      (Set.Icc t₀ t₁) := by
    intro t ht
    exact ContMDiffAt.comp_contMDiffWithinAt t
      ((S.contMDiffAt_invIncl k (hδr t ht)).of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞))
      (hδ t ht)
  have h1 := pathELength_incl S g hg k hpull
  have h2 : Manifold.pathELength I
      (S.toSeqSystem.incl k ∘ (Function.invFun (S.toSeqSystem.incl k) ∘ δ)) t₀ t₁
      = Manifold.pathELength I δ t₀ t₁ :=
    Manifold.pathELength_congr fun t ht => Function.invFun_eq (hδr t ht)
  rw [← h2, h1]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Reverse distance comparison on deep balls (D5, the `lbl408` completeness mechanism).**
If the closed `riemannianEDist`-ball of radius `r` around `x` lies in a stage range, then stage
points under `x, y` with `edist x y < r` satisfy the reverse bound: every limit path from `x` of
length `< r` stays in the ball (its partial lengths dominate the distances), hence in the range,
so it pulls back at equal length (`pathELength_invIncl`) and bounds the stage distance. -/
theorem edist_invIncl_le (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (k : ℕ) {x y : S.toSeqSystem.Lim} {r : ENNReal}
    (hxy :
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric g hg).toRiemannianMetric⟩
      Manifold.riemannianEDist I x y < r)
    (hsub : ∀ z : S.toSeqSystem.Lim,
      (letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric g hg).toRiemannianMetric⟩
      Manifold.riemannianEDist I x z ≤ r) → z ∈ Set.range (S.toSeqSystem.incl k)) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    letI : RiemannianBundle (fun a : A k => TangentSpace I a) :=
      ⟨(g k).toRiemannianMetric⟩
    Manifold.riemannianEDist I
        (Function.invFun (S.toSeqSystem.incl k) x) (Function.invFun (S.toSeqSystem.incl k) y)
      ≤ r := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  letI : RiemannianBundle (fun a : A k => TangentSpace I a) :=
    ⟨(g k).toRiemannianMetric⟩
  obtain ⟨γ, hγ0, hγ1, hγC, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hxy
  -- the path stays in the `r`-ball, hence in the stage range
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Set.range (S.toSeqSystem.incl k) := by
    intro t ht
    refine hsub (γ t) ?_
    have hseg : Manifold.riemannianEDist I x (γ t)
        ≤ Manifold.pathELength I γ 0 t :=
      Manifold.riemannianEDist_le_pathELength
        (hγC.mono (Set.Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1
    refine hseg.trans (le_trans ?_ hlen.le)
    exact Manifold.pathELength_mono le_rfl ht.2
  -- pull the path back and compare
  have hpull1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      (Function.invFun (S.toSeqSystem.incl k) ∘ γ) (Set.Icc 0 1) := by
    intro t ht
    exact ContMDiffAt.comp_contMDiffWithinAt t
      ((S.contMDiffAt_invIncl k (hmem t ht)).of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞))
      (hγC t ht)
  have hle : Manifold.riemannianEDist I
      (Function.invFun (S.toSeqSystem.incl k) x) (Function.invFun (S.toSeqSystem.incl k) y)
      ≤ Manifold.pathELength I (Function.invFun (S.toSeqSystem.incl k) ∘ γ) 0 1 :=
    Manifold.riemannianEDist_le_pathELength hpull1
      (by rw [Function.comp_apply, hγ0]) (by rw [Function.comp_apply, hγ1]) zero_le_one
  refine hle.trans ?_
  rw [pathELength_invIncl S g hg k hγC hmem]
  exact hlen.le

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Closed `riemannianEDist`-balls of the limit are compact (D5a core).**  Given the metric
exhaustion (`hexh`, the honest input discharged at D6 from the `2^k`-ball structure) and
compactness of the stage `riemannianEDist`-balls (`hcpt`, from the members' properness), a
closed limit ball of finite radius is a closed subset of the `incl k`-image of a compact stage
ball — `edist_invIncl_le` transports the radius. -/
theorem isCompact_cball_lim (S : SmoothSeqSystem I A)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    (hexh : ∀ (z : S.toSeqSystem.Lim) (r : ENNReal),
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric g hg).toRiemannianMetric⟩
      ∃ k, ∀ w : S.toSeqSystem.Lim,
        Manifold.riemannianEDist I z w ≤ r → w ∈ Set.range (S.toSeqSystem.incl k))
    (hcpt : ∀ (k : ℕ) (a : A k) (r : ENNReal),
      letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
        ⟨(g k).toRiemannianMetric⟩
      IsCompact {b : A k | Manifold.riemannianEDist I a b ≤ r})
    (z : S.toSeqSystem.Lim) (r : ENNReal) (hr : r ≠ ⊤) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric g hg).toRiemannianMetric⟩
    IsCompact {w : S.toSeqSystem.Lim | Manifold.riemannianEDist I z w ≤ r} := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  obtain ⟨k, hk⟩ := hexh z (r + 1)
  letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
    ⟨(g k).toRiemannianMetric⟩
  have hz : z ∈ Set.range (S.toSeqSystem.incl k) :=
    hk z (by rw [Manifold.riemannianEDist_self]; exact zero_le _)
  -- the compact stage ball, pushed to the limit
  have himg : IsCompact (S.toSeqSystem.incl k ''
      {b : A k | Manifold.riemannianEDist I (Function.invFun (S.toSeqSystem.incl k) z) b
        ≤ r + 1}) :=
    (hcpt k _ (r + 1)).image (S.toSeqSystem.continuous_incl k)
  refine IsCompact.of_isClosed_subset himg ?_ ?_
  · -- the limit ball is closed: `riemannianEDist z ·` is `edist` for the induced emetric
    letI : IsManifold I 1 S.toSeqSystem.Lim :=
      IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : TopologicalSpace.MetrizableSpace S.toSeqSystem.Lim :=
      Manifold.metrizableSpace I S.toSeqSystem.Lim
    letI : T3Space S.toSeqSystem.Lim := inferInstance
    letI : IsContinuousRiemannianBundle E (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨⟨(S.limitMetric g hg).inner, (S.limitMetric g hg).contMDiff.continuous,
        by intro x v w; rfl⟩⟩
    letI : EMetricSpace S.toSeqSystem.Lim :=
      EMetricSpace.ofRiemannianMetric I S.toSeqSystem.Lim
    have hcont : Continuous fun w : S.toSeqSystem.Lim => edist z w :=
      continuous_const.edist continuous_id
    have hset : {w : S.toSeqSystem.Lim | Manifold.riemannianEDist I z w ≤ r}
        = (fun w : S.toSeqSystem.Lim => edist z w) ⁻¹' (Set.Iic r) := rfl
    rw [hset]
    exact IsClosed.preimage hcont isClosed_Iic
  · -- the limit ball sits inside the pushed stage ball
    intro w hw
    have hw' : Manifold.riemannianEDist I z w ≤ r := hw
    have hwr : w ∈ Set.range (S.toSeqSystem.incl k) :=
      hk w (hw'.trans le_self_add)
    have hlt : Manifold.riemannianEDist I z w < r + 1 :=
      hw'.trans_lt (ENNReal.lt_add_right hr one_ne_zero)
    have hstage := edist_invIncl_le S g hg k hlt hk
    refine ⟨Function.invFun (S.toSeqSystem.incl k) w, hstage, Function.invFun_eq hwr⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **D5a — the limit is metrically complete** (MSM135 `lbl408` completeness, L2087–2100).
Under the metric exhaustion (`hexh`) and stage-ball compactness (`hcpt`), the closed balls of the
limit's Riemannian distance are compact (`isCompact_cball_lim`), so the realized metric space is
proper, hence complete.  Connectedness of the limit (from preconnected stages) supplies the
finiteness of the Riemannian distance. -/
theorem limitComplete [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    [∀ k, PreconnectedSpace (A k)]
    (hexh : ∀ (z : S.toSeqSystem.Lim) (r : ENNReal),
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric g hg).toRiemannianMetric⟩
      ∃ k, ∀ w : S.toSeqSystem.Lim,
        Manifold.riemannianEDist I z w ≤ r → w ∈ Set.range (S.toSeqSystem.incl k))
    (hcpt : ∀ (k : ℕ) (a : A k) (r : ENNReal),
      letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
        ⟨(g k).toRiemannianMetric⟩
      IsCompact {b : A k | Manifold.riemannianEDist I a b ≤ r}) :
    MetricComplete (I := I) (limitPointedCoc S O₀ g hg) := by
  unfold MetricComplete
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  letI : IsManifold I 1 S.toSeqSystem.Lim :=
    IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : TopologicalSpace.MetrizableSpace S.toSeqSystem.Lim :=
    Manifold.metrizableSpace I S.toSeqSystem.Lim
  letI : T3Space S.toSeqSystem.Lim := inferInstance
  letI : IsContinuousRiemannianBundle E (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨⟨(S.limitMetric g hg).inner, (S.limitMetric g hg).contMDiff.continuous,
      by intro x v w; rfl⟩⟩
  letI : EMetricSpace S.toSeqSystem.Lim :=
    EMetricSpace.ofRiemannianMetric I S.toSeqSystem.Lim
  letI : MetricSpace S.toSeqSystem.Lim :=
    EMetricSpace.toMetricSpace
      (fun x y => Geometry.Riemannian.Exponential.riemannianEDist_ne_top (I := I) x y)
  haveI : ProperSpace S.toSeqSystem.Lim := by
    refine ProperSpace.of_isCompact_closedBall_of_le 0 (fun z r hr => ?_)
    have h := isCompact_cball_lim S g hg hexh hcpt z (ENNReal.ofReal r) ENNReal.ofReal_ne_top
    have hset : Metric.closedBall z r
        = {w : S.toSeqSystem.Lim |
            Manifold.riemannianEDist I z w ≤ ENNReal.ofReal r} := by
      rw [← Metric.closedEBall_ofReal hr]
      ext w
      exact Metric.mem_closedEBall'
    rw [hset]
    exact h
  exact (complete_of_proper : CompleteSpace S.toSeqSystem.Lim)

end StepD5

end HCGCompactness
end DifferentialGeometry
