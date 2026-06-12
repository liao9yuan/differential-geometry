import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ArzelaAscoli
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false

/-!
# `C^p` / `C^∞` convergence of maps (MSM135 Chapter 4, "Compactness of maps")

This file formalizes the two MSM135 definitions in the subsection *Compactness of
maps* (the convergence-of-maps notions, `lbl373`), for maps between open sets of a
real normed space.  These are the Euclidean analogues of the metric-convergence
definitions in `PointedConvergence.lean` (`MetricCPConvOn`,
`MetricCInfConvOnCompacts`): there the derivative is the Levi-Civita covariant
derivative of a reference metric and the norm is metric-induced; here `∇` is the
Euclidean gradient — the iterated Fréchet derivative `iteratedFDeriv ℝ r` — and the
norm is the operator norm on `ContinuousMultilinearMap`s.

The displayed book condition is `sup_{0 ≤ r ≤ p} sup_{x ∈ K} |∇ʳ(Φₖ - Φ_∞)(x)| ≤ ε`.
We state it in the equivalent direct `∀ r ≤ p, ∀ x ∈ K, ‖…‖ ≤ ε` form (avoiding an
`sSup` and its boundedness side conditions), which is the Mathlib-idiomatic shape
that the Arzelà–Ascoli engine and Step D consume.
-/

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology

section MapConvergence

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Euclidean pointwise quantity `|∇ʳ(Φₖ - Φ_∞)(x)|` from the MSM135
"`C^p`-convergence of maps" definition: the operator norm of the `r`-th Fréchet
derivative of the difference `Φₖ - Φ_∞`, with `∇` the Euclidean gradient. -/
noncomputable def mapDerivNorm (r : ℕ) (Φk Φinf : E → F) (x : E) : ℝ :=
  ‖iteratedFDeriv ℝ r (fun y => Φk y - Φinf y) x‖

theorem mapDerivNorm_nonneg (r : ℕ) (Φk Φinf : E → F) (x : E) :
    0 ≤ mapDerivNorm r Φk Φinf x :=
  norm_nonneg _

/-- MSM135 Definition "`C^p`-convergence of maps": `Φₖ → Φ_∞` in `C^p` on the
compact set `K`.  For every `ε > 0` there is a threshold `k₀` past which all
derivatives up to order `p` of `Φₖ - Φ_∞` are uniformly `≤ ε` on `K`. -/
def MapCPConvOn (K : Set E) (p : ℕ) (Φ : ℕ → E → F) (Φinf : E → F) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
    ∀ r : ℕ, r ≤ p → ∀ x ∈ K, mapDerivNorm r (Φ k) Φinf x ≤ ε

/-- MSM135 Definition "`C^∞`-convergence of maps uniformly on compact sets"
(`lbl373`): on every compact `K ⊆ U`, the sequence converges in `C^p` for every
finite order `p`.  (The book's per-`(K,p)` threshold `k₁` is absorbed into the
`∃ k₀` already inside `MapCPConvOn`, since a tail of a `C^p`-convergent sequence is
`C^p`-convergent to the same limit.) -/
def MapCInfConvOnCompacts (U : Set E) (Φ : ℕ → E → F) (Φinf : E → F) : Prop :=
  ∀ K : Set E, IsCompact K → K ⊆ U → ∀ p : ℕ, MapCPConvOn K p Φ Φinf

/-- `C^p` convergence is monotone in the order: convergence to order `p` forces
convergence to every lower order `p' ≤ p` (fewer derivatives to control). -/
theorem MapCPConvOn.mono_order {K : Set E} {p p' : ℕ} (hp : p' ≤ p)
    {Φ : ℕ → E → F} {Φinf : E → F} (h : MapCPConvOn K p Φ Φinf) :
    MapCPConvOn K p' Φ Φinf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  exact ⟨k0, fun k hk r hr x hx => hk0 k hk r (hr.trans hp) x hx⟩

/-- `C^p` convergence on a set restricts to any subset. -/
theorem MapCPConvOn.mono_set {K K' : Set E} (hK : K' ⊆ K) {p : ℕ}
    {Φ : ℕ → E → F} {Φinf : E → F} (h : MapCPConvOn K p Φ Φinf) :
    MapCPConvOn K' p Φ Φinf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  exact ⟨k0, fun k hk r hr x hx => hk0 k hk r hr x (hK hx)⟩

/-- The `C^∞`-on-compacts limit converges in `C^p` on every compact subset of the
domain — the elementary projection that consumers use to extract a single
`MapCPConvOn` instance. -/
theorem MapCInfConvOnCompacts.cPConvOn {U : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCInfConvOnCompacts U Φ Φinf) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U) (p : ℕ) : MapCPConvOn K p Φ Φinf :=
  h K hK hKU p

/-- `C^p` convergence passes to any subsequence (the condition is asymptotic in `k`). -/
theorem MapCPConvOn.comp_subseq {K : Set E} {p : ℕ} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCPConvOn K p Φ Φinf) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    MapCPConvOn K p (fun k => Φ (φ k)) Φinf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  exact ⟨k0, fun k hk r hr x hx => hk0 (φ k) (le_trans hk (hφ.id_le k)) r hr x hx⟩

/-- `C^∞`-on-compacts convergence passes to any subsequence. -/
theorem MapCInfConvOnCompacts.comp_subseq {U : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCInfConvOnCompacts U Φ Φinf) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    MapCInfConvOnCompacts U (fun k => Φ (φ k)) Φinf :=
  fun K hK hKU p => (h K hK hKU p).comp_subseq hφ

/-- The order-`0` content of `C^p` convergence on `K` is plain uniform convergence on `K`
(`∇⁰` is the value itself, `norm_iteratedFDeriv_zero`). -/
theorem tendstoUniformlyOn_of_cPConv {K : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCPConvOn K 0 Φ Φinf) : TendstoUniformlyOn Φ Φinf atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨k0, hk0⟩ := h (ε / 2) (by positivity)
  rw [eventually_atTop]
  refine ⟨k0, fun k hk x hx => ?_⟩
  have hb := hk0 k hk 0 le_rfl x hx
  rw [mapDerivNorm, norm_iteratedFDeriv_zero] at hb
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt hb (by linarith)

/-- Pointwise convergence at a domain point, extracted from `C^∞`-on-compacts convergence
(apply the order-`0` content at the singleton `{x}`). -/
theorem tendsto_of_cInf {U : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCInfConvOnCompacts U Φ Φinf) {x : E} (hx : x ∈ U) :
    Tendsto (fun k => Φ k x) atTop (𝓝 (Φinf x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k0, hk0⟩ :=
    h {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx) 0 (ε / 2) (by positivity)
  refine ⟨k0, fun k hk => ?_⟩
  have hb := hk0 k hk 0 le_rfl x rfl
  rw [mapDerivNorm, norm_iteratedFDeriv_zero] at hb
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hb (by linarith)

/-- **Bridge to the uniform-convergence engine.**  If every Euclidean derivative
`∇ʳΦₖ` of order `r ≤ p` converges uniformly on `K` to `∇ʳΦ_∞` (the natural output of
an Arzelà–Ascoli extraction), then `Φₖ → Φ_∞` in `C^p` on `K`.  The `C^p` smoothness
hypotheses let `∇ʳ` commute with the difference (`iteratedFDeriv_sub_apply`), turning
`∇ʳΦₖ → ∇ʳΦ_∞` into `∇ʳ(Φₖ - Φ_∞) → 0`. -/
theorem mapCPConvOn_of_tendstoUniformly {K : Set E} {p : ℕ}
    {Φ : ℕ → E → F} {Φinf : E → F}
    (hΦ : ∀ k, ContDiff ℝ (p : ℕ∞) (Φ k)) (hΦinf : ContDiff ℝ (p : ℕ∞) Φinf)
    (htu : ∀ r : ℕ, r ≤ p →
      TendstoUniformlyOn (fun k x => iteratedFDeriv ℝ r (Φ k) x)
        (fun x => iteratedFDeriv ℝ r Φinf x) atTop K) :
    MapCPConvOn K p Φ Φinf := by
  intro ε hε
  have key : ∀ r : ℕ, r ≤ p →
      ∀ᶠ k in atTop, ∀ x ∈ K, mapDerivNorm r (Φ k) Φinf x ≤ ε := by
    intro r hr
    have h := (Metric.tendstoUniformlyOn_iff.mp (htu r hr)) ε hε
    filter_upwards [h] with k hk x hx
    have hsub : iteratedFDeriv ℝ r (fun y => Φ k y - Φinf y) x
        = iteratedFDeriv ℝ r (Φ k) x - iteratedFDeriv ℝ r Φinf x :=
      iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := r) (x := x)
        ((hΦ k).contDiffAt.of_le (by exact_mod_cast hr))
        (hΦinf.contDiffAt.of_le (by exact_mod_cast hr))
    have hdist := hk x hx
    rw [dist_eq_norm, ← norm_sub_rev] at hdist
    rw [mapDerivNorm, hsub]
    exact hdist.le
  have hfin : ∀ᶠ k in atTop, ∀ r ∈ Set.Iic p, ∀ x ∈ K,
      mapDerivNorm r (Φ k) Φinf x ≤ ε :=
    (Set.finite_Iic p).eventually_all.2 (fun r hr => key r (Set.mem_Iic.mp hr))
  obtain ⟨k0, hk0⟩ := eventually_atTop.mp hfin
  exact ⟨k0, fun k hk r hr x hx => hk0 k hk r (Set.mem_Iic.mpr hr) x hx⟩

end MapConvergence

section MapArzelaAscoli

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Spaces of continuous multilinear maps with finite-dimensional (real) source and
target are finite-dimensional: curry induction on the arity through
`continuousMultilinearCurryLeftEquiv`, with the linear-arity instance
`ContinuousLinearMap.instModuleFinite` at each step (Mathlib has no multilinear
instance). -/
theorem cmm_finiteDimensional (r : ℕ) :
    FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F) := by
  induction r with
  | zero =>
      exact (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearEquiv.finiteDimensional
  | succ r ih =>
      haveI := ih
      exact ((continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (r + 1) => E) F).symm.toLinearEquiv).finiteDimensional

omit [FiniteDimensional ℝ F] in
/-- Equicontinuity input for the Arzelà–Ascoli extraction: the order-`(r+1)` uniform
bound on the closed unit ball around each point makes the order-`r` derivative family
uniformly Lipschitz there (mean value inequality, `fderiv ∇ʳΦ = (∇^{r+1}Φ).curryLeft`
from the Taylor-series field), hence equicontinuous. -/
private theorem equicont_iteratedFDeriv
    (Φ : ℕ → E → F) (hΦ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ k))
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K →
        ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M) (r : ℕ) :
    Equicontinuous (fun k => iteratedFDeriv ℝ r (Φ k)) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff]
  obtain ⟨M, hM⟩ := hbdd (r + 1) (Metric.closedBall x₀ 1) (isCompact_closedBall x₀ 1)
  intro ε hε
  have hM₀ : (0 : ℝ) ≤ max M 0 := le_max_right M 0
  refine ⟨min 1 (ε / (max M 0 + 1)), lt_min one_pos (by positivity), fun x hx k => ?_⟩
  have hx1 : x ∈ Metric.closedBall x₀ 1 :=
    Metric.mem_closedBall.mpr (hx.trans_le (min_le_left _ _)).le
  have hx₀1 : x₀ ∈ Metric.closedBall x₀ 1 := Metric.mem_closedBall_self zero_le_one
  -- mean value inequality with the uniform order-`(r+1)` bound
  have hlip : ‖iteratedFDeriv ℝ r (Φ k) x - iteratedFDeriv ℝ r (Φ k) x₀‖
      ≤ max M 0 * ‖x - x₀‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f' := fun y => (iteratedFDeriv ℝ (r + 1) (Φ k) y).curryLeft)
      (fun y _ => ((contDiff_infty.mp (hΦ k) (r + 1)).ftaylorSeries.fderiv r
        (by exact_mod_cast lt_add_one r) y).hasFDerivWithinAt)
      (fun y hy => ?_) (convex_closedBall x₀ 1) hx₀1 hx1
    rw [ContinuousMultilinearMap.curryLeft_norm]
    exact (hM k y hy).trans (le_max_left M 0)
  rw [dist_comm, dist_eq_norm]
  calc ‖iteratedFDeriv ℝ r (Φ k) x - iteratedFDeriv ℝ r (Φ k) x₀‖
      ≤ max M 0 * ‖x - x₀‖ := hlip
    _ ≤ max M 0 * (ε / (max M 0 + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hM₀
        rw [← dist_eq_norm]
        exact (hx.trans_le (min_le_right _ _)).le
    _ < (max M 0 + 1) * (ε / (max M 0 + 1)) :=
        mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
    _ = ε := by field_simp

/-- **Arzelà–Ascoli for maps** (the map-valued compactness the MSM135 subsection
*Compactness of maps* "shall need", used to prove the isometry corollary `lbl374`).

If a sequence of smooth maps `Φₖ : E → F` (between finite-dimensional real normed
spaces) has all Euclidean iterated derivatives uniformly bounded on every compact set
— `∀ r, ∀ K compact, ∃ M, ∀ k, ∀ x ∈ K, ‖∇ʳΦₖ(x)‖ ≤ M` — then a subsequence converges
in `C^∞` uniformly on compact sets to a smooth limit `Φ_∞`.

Proof route:
(1) the order-`(r+1)` bound makes `{∇ʳΦₖ}ₖ` equicontinuous (`equicont_iteratedFDeriv`)
   and the order-`r` bound makes it pointwise bounded, so the bundled family has
   compact closure in `C(E, E[×r]→L[ℝ] F)` (`arzelaAscoli_isCompact_closure`, with
   `cmm_finiteDimensional` providing properness of the target);
(2) one subsequence works for every order `r` at once: the sequence of all-order
   derivative tuples lives in the countable product of those compact closures, which
   is compact and first countable (no explicit diagonal, as in `DiagonalSubseq`);
(3) `hasFDerivAt_of_tendstoUniformlyOn` on unit balls identifies the uniform limit of
   the order-`(r+1)` derivatives as the derivative of the order-`r` limit, so the
   limits `G r` assemble into `HasFTaylorSeriesUpTo ⊤` of `Φ_∞ := (G 0).curry0`;
(4) hence `Φ_∞` is `C^∞` with `∇ʳΦ_∞ = G r` (`HasFTaylorSeriesUpTo.eq_iteratedFDeriv`)
   and the convergence is `C^∞`-on-compacts via `mapCPConvOn_of_tendstoUniformly`. -/
theorem exists_cInf_subseq
    (Φ : ℕ → E → F) (hΦ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ k))
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K →
        ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F),
      StrictMono φ ∧ ContDiff ℝ (⊤ : ℕ∞) Φinf ∧
        MapCInfConvOnCompacts Set.univ (fun k => Φ (φ k)) Φinf := by
  classical
  -- bundle the order-`r` derivative families as continuous maps
  let Fb : (r : ℕ) → ℕ → C(E, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F) :=
    fun r k => ⟨iteratedFDeriv ℝ r (Φ k),
      (contDiff_infty.mp (hΦ k) r).continuous_iteratedFDeriv'⟩
  -- each family has compact closure in `C(E, ⋯)` (vector Arzelà–Ascoli)
  have hcpt : ∀ r : ℕ, IsCompact (closure (Set.range (Fb r))) := by
    intro r
    haveI := cmm_finiteDimensional (E := E) (F := F) r
    refine arzelaAscoli_isCompact_closure (Fb r)
      (equicont_iteratedFDeriv Φ hΦ hbdd r) (fun x => ?_)
    obtain ⟨M, hM⟩ := hbdd r {x} isCompact_singleton
    exact ⟨M, fun k => hM k x rfl⟩
  -- one subsequence for all orders at once, via the compact countable product
  haveI : ∀ r : ℕ, CompactSpace (closure (Set.range (Fb r))) :=
    fun r => isCompact_iff_compactSpace.mp (hcpt r)
  set xseq : ℕ → Π r : ℕ, closure (Set.range (Fb r)) :=
    fun k r => ⟨Fb r k, subset_closure ⟨k, rfl⟩⟩ with hxseq
  obtain ⟨a, -, φ, hφ, ha⟩ :=
    (isCompact_univ :
        IsCompact (Set.univ : Set (Π r : ℕ, closure (Set.range (Fb r))))).tendsto_subseq
      (x := xseq) (fun k => Set.mem_univ _)
  set G : (r : ℕ) → C(E, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F) :=
    fun r => (a r : C(E, _)) with hG
  have hGconv : ∀ r : ℕ, Tendsto (fun k => Fb r (φ k)) atTop (𝓝 (G r)) := by
    intro r
    have h1 : Tendsto (fun k => xseq (φ k) r) atTop (𝓝 (a r)) :=
      (tendsto_pi_nhds.mp ha) r
    have h2 := (continuous_subtype_val.tendsto (a r)).comp h1
    simpa [hxseq, hG, Function.comp] using h2
  have hGunif : ∀ r : ℕ, ∀ K : Set E, IsCompact K →
      TendstoUniformlyOn (fun k => ⇑(Fb r (φ k))) (⇑(G r)) atTop K :=
    fun r => ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp (hGconv r)
  -- the uniform limits are linked by differentiation
  have hGderiv : ∀ (r : ℕ) (x₀ : E),
      HasFDerivAt (⇑(G r)) (((G (r + 1)) x₀).curryLeft) x₀ := by
    intro r x₀
    have hball : IsCompact (Metric.closedBall x₀ 1) := isCompact_closedBall x₀ 1
    have hf' : TendstoUniformlyOn (fun k y => ((Fb (r + 1) (φ k)) y).curryLeft)
        (fun y => ((G (r + 1)) y).curryLeft) atTop (Metric.ball x₀ 1) := by
      have h2 := ((continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (r + 1) => E) F).isometry.uniformContinuous).comp_tendstoUniformlyOn
        ((hGunif (r + 1) _ hball).mono Metric.ball_subset_closedBall)
      simpa [Function.comp_def] using h2
    have hfd : ∀ k : ℕ, ∀ y ∈ Metric.ball x₀ 1,
        HasFDerivAt (⇑(Fb r (φ k))) (((Fb (r + 1) (φ k)) y).curryLeft) y := fun k y _ =>
      (contDiff_infty.mp (hΦ (φ k)) (r + 1)).ftaylorSeries.fderiv r
        (by exact_mod_cast lt_add_one r) y
    have hfg : ∀ y ∈ Metric.ball x₀ 1,
        Tendsto (fun k => (Fb r (φ k)) y) atTop (𝓝 ((G r) y)) := fun y hy =>
      (hGunif r _ hball).tendsto_at (Metric.ball_subset_closedBall hy)
    exact hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hf' hfd hfg
      (Metric.mem_ball_self one_pos)
  -- the limits assemble into a full Taylor series of the order-`0` limit
  have htaylor : HasFTaylorSeriesUpTo ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => ((G 0) y).curry0) (fun y r => (G r) y) :=
    ⟨fun _ => rfl, fun m _ y => hGderiv m y, fun m _ => (G m).continuous⟩
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => ((G 0) y).curry0) := htaylor.contDiff
  have hid : ∀ (r : ℕ) (y : E),
      iteratedFDeriv ℝ r (fun z => ((G 0) z).curry0) y = (G r) y := fun r y =>
    (htaylor.eq_iteratedFDeriv (by exact_mod_cast le_top) y).symm
  refine ⟨φ, fun y => ((G 0) y).curry0, hφ, hsmooth, ?_⟩
  intro K hK _ p
  refine mapCPConvOn_of_tendstoUniformly
    (fun k => (hΦ (φ k)).of_le (by exact_mod_cast le_top))
    (hsmooth.of_le (by exact_mod_cast le_top)) ?_
  intro r _hr
  have h := hGunif r K hK
  rw [show (⇑(G r)) = fun y => iteratedFDeriv ℝ r (fun z => ((G 0) z).curry0) y from
    funext fun y => (hid r y).symm] at h
  exact h

end MapArzelaAscoli

end HCGCompactness
end DifferentialGeometry
