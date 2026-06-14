import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ComponentConvAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvWindow

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Window limit metrics from fixed-time spatial precompactness

This file is the P3 C-II-final `gInf` producer layer.  It first exposes the
pointwise `metricDerivNorm` convergence that is built inside `metricPreconvInf`,
then diagonalizes that stronger fixed-time output over a countable time net.

The final all-time family `Real -> SmoothRiemannianMetric` is not constructed
here yet; `windowOfNet` records the exact consumer once such a family agrees
with the net-time limits and satisfies the limit time-Lipschitz estimate.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection
open Tensor0SBundle TensorLieDeriv
open Filter Topology
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]

set_option maxHeartbeats 800000 in
/-- Fixed-time spatial precompactness in the pointwise norm shape consumed by
`windowPreconv`.  This is the `hnorm` part of `metricPreconvInf`, exposed before
the final `metricDerivNormSupOn` packaging. -/
theorem metricPreconvNorm (hne : Nonempty M)
    (K : Set M) (hK : IsCompact K) (p : Nat)
    (gRef : SmoothRiemannianMetric I M) (gSeq : Nat -> SmoothRiemannianMetric I M)
    (hbdd : forall q : Nat, forall K' : Set M, IsCompact K' -> exists C : Real,
      forall k : Nat, forall z, z ∈ K' ->
        metricCovDerivNorm (I := I) q (gSeq k) gRef z <= C)
    (hlow : exists c : Real, 0 < c /\ forall (k : Nat) (x : M) (v : TangentSpace I x),
      c * gRef.inner x v v <= (gSeq k).inner x v v) :
    exists phi : Nat -> Nat, StrictMono phi /\ exists gInf : SmoothRiemannianMetric I M,
      forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
        forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (phi k)) gInf gRef x < eps := by
  classical
  obtain ⟨phi0, hphi0, gInf, hconv⟩ := metricPreconv_gInf (I := I) hne gRef gSeq hbdd hlow
  choose W C hWopen hxW hCcpt hWC hpatch using
    exists_uniform_patch (I := I) gRef gSeq hbdd phi0 gInf hconv
  obtain ⟨s, hscount, hscov⟩ :=
    (isLindelof_univ (X := M)).elim_countable_subcover W hWopen
      (fun y _ => Set.mem_iUnion.2 ⟨y, hxW y⟩)
  have hsne : s.Nonempty := by
    obtain ⟨y⟩ := hne
    obtain ⟨z, hz, -⟩ := Set.mem_iUnion₂.1 (hscov (Set.mem_univ y))
    exact ⟨z, hz⟩
  obtain ⟨e, hse⟩ := hscount.exists_eq_range hsne
  have hcovN : (Set.univ : Set M) ⊆ ⋃ n : Nat, W (e n) := fun z hz => by
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.1 (hscov hz)
    rw [hse] at hw
    obtain ⟨n, rfl⟩ := hw
    exact Set.mem_iUnion.2 ⟨n, hzw⟩
  obtain ⟨phid, hphid, hPphid⟩ := exists_diag_subseq
    (fun n phi => forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall a : Nat, a <= p ->
        forall z, z ∈ C (e n) ->
          metricDerivNorm (I := I) a (gSeq (phi0 (phi k))) gInf gRef z < eps)
    (fun n phi hphi => by
      obtain ⟨psi, hpsi, hu⟩ := hpatch (e n) phi hphi
      refine ⟨psi, hpsi, fun eps heps => ?_⟩
      obtain ⟨k0, hk0⟩ := hu p eps heps
      refine ⟨k0, fun k hk a ha z hz => ?_⟩
      simpa only [Function.comp_apply] using hk0 k hk a ha z hz)
    (fun n phi psi hpsi hP eps heps => by
      obtain ⟨k0, hk0⟩ := hP eps heps
      exact ⟨k0, fun k hk a ha z hz =>
        hk0 (psi k) (le_trans hk (hpsi.id_le k)) a ha z hz⟩)
    (fun n phi m hP eps heps => by
      obtain ⟨k0, hk0⟩ := hP eps heps
      refine ⟨k0 + m, fun k hk a ha z hz => ?_⟩
      have hval := hk0 (k - m) (by omega) a ha z hz
      simp only [Nat.sub_add_cancel (show m <= k by omega)] at hval
      exact hval)
  refine ⟨phi0 ∘ phid, hphi0.comp hphid, gInf, fun eps heps => ?_⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun n => W (e n)) (fun n => hWopen (e n))
    (fun z hz => hcovN (Set.mem_univ z))
  have perN : forall n, n ∈ F -> exists k0 : Nat, forall k : Nat, k0 <= k ->
      forall a : Nat, a <= p -> forall z, z ∈ C (e n) ->
        metricDerivNorm (I := I) a (gSeq (phi0 (phid k))) gInf gRef z < eps :=
    fun n _ => hPphid n eps heps
  choose k0fn hk0fn using perN
  refine ⟨F.attach.sup (fun n => k0fn n.1 n.2), fun k hk a ha z hz => ?_⟩
  obtain ⟨n, hn, hzw⟩ := Set.mem_iUnion₂.1 (hF hz)
  simpa only [Function.comp_apply] using
    hk0fn n hn k (le_trans (Finset.le_sup (f := fun n => k0fn n.1 n.2)
      (Finset.mem_attach F ⟨n, hn⟩)) hk) a ha z (hWC (e n) hzw)

/-- Diagonalize the fixed-time norm producers over a countable time net.  The
result is one master subsequence and one smooth limit metric for each net time,
in the exact pointwise convergence shape needed by the window upgrade. -/
theorem netNormDiag (hne : Nonempty M)
    (K : Set M) (hK : IsCompact K) (p : Nat)
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M) (e : Nat -> Real)
    (hbdd : forall n : Nat, forall rho : Nat -> Nat, StrictMono rho ->
      forall q : Nat, forall K' : Set M, IsCompact K' -> exists C : Real,
        forall k : Nat, forall z, z ∈ K' ->
          metricCovDerivNorm (I := I) q (gSeq (rho k) (e n)) gRef z <= C)
    (hlow : forall n : Nat, forall rho : Nat -> Nat, StrictMono rho ->
      exists c : Real, 0 < c /\ forall (k : Nat) (x : M) (v : TangentSpace I x),
        c * gRef.inner x v v <= (gSeq (rho k) (e n)).inner x v v) :
    exists phi : Nat -> Nat, StrictMono phi /\
      exists gNet : Nat -> SmoothRiemannianMetric I M,
        forall n : Nat, forall eps : Real, 0 < eps -> exists k0 : Nat,
          forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
            metricDerivNorm (I := I) a (gSeq (phi k) (e n)) (gNet n) gRef x < eps := by
  classical
  obtain ⟨phi, hphi, hPphi⟩ := exists_diag_subseq
    (fun n rho => exists gLim : SmoothRiemannianMetric I M,
      forall eps : Real, 0 < eps -> exists k0 : Nat,
        forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq (rho k) (e n)) gLim gRef x < eps)
    (fun n rho hrho => by
      obtain ⟨psi, hpsi, gLim, hlim⟩ :=
        metricPreconvNorm (I := I) hne K hK p gRef (fun k => gSeq (rho k) (e n))
          (hbdd n rho hrho) (hlow n rho hrho)
      refine ⟨psi, hpsi, gLim, ?_⟩
      intro eps heps
      obtain ⟨k0, hk0⟩ := hlim eps heps
      exact ⟨k0, fun k hk a ha x hx => by
        simpa only [Function.comp_apply] using hk0 k hk a ha x hx⟩)
    (fun n rho psi hpsi hP => by
      obtain ⟨gLim, hlim⟩ := hP
      refine ⟨gLim, fun eps heps => ?_⟩
      obtain ⟨k0, hk0⟩ := hlim eps heps
      exact ⟨k0, fun k hk a ha x hx => by
        simpa only [Function.comp_apply] using
          hk0 (psi k) (le_trans hk (hpsi.id_le k)) a ha x hx⟩)
    (fun n rho m hP => by
      obtain ⟨gLim, hlim⟩ := hP
      refine ⟨gLim, fun eps heps => ?_⟩
      obtain ⟨k0, hk0⟩ := hlim eps heps
      refine ⟨k0 + m, fun k hk a ha x hx => ?_⟩
      have hval := hk0 (k - m) (by omega) a ha x hx
      simp only [Nat.sub_add_cancel (show m <= k by omega)] at hval
      exact hval)
  choose gNet hgNet using hPphi
  exact ⟨phi, hphi, gNet, hgNet⟩

/-- Once an all-time limit family is available and agrees with the net-time
limits in the pointwise norm-convergence shape, the existing `windowPreconv`
lemma gives the final window-uniform convergence along the master subsequence. -/
theorem windowOfNet
    (K : Set M) (beta psiT : Real) (p : Nat)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gInf : Real -> SmoothRiemannianMetric I M) (gRef : SmoothRiemannianMetric I M)
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (L : Real) (hL : 0 <= L)
    (hgLip : forall k : Nat, forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
      forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x <= L * |s - t|)
    (hInfLip : forall s, s ∈ Set.Icc beta psiT -> forall t, t ∈ Set.Icc beta psiT ->
      forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gInf s) (gInf t) gRef x <= L * |s - t|)
    (e : Nat -> Real) (he : forall n : Nat, e n ∈ Set.Icc beta psiT)
    (hdense : forall t, t ∈ Set.Icc beta psiT -> forall delta : Real, 0 < delta ->
      exists n : Nat, |t - e n| < delta)
    (hnet : forall n : Nat, forall eps : Real, 0 < eps -> exists k0 : Nat,
      forall k : Nat, k0 <= k -> forall a : Nat, a <= p -> forall x, x ∈ K ->
        metricDerivNorm (I := I) a (gSeq (phi k) (e n)) (gInf (e n)) gRef x < eps) :
    exists phi' : Nat -> Nat, StrictMono phi' /\
      forall eps : Real, 0 < eps -> exists k0 : Nat, forall k : Nat, k0 <= k ->
        forall t, t ∈ Set.Icc beta psiT ->
          metricDerivNormSupOn (I := I) K p (gSeq (phi' k) t) (gInf t) gRef < eps := by
  refine ⟨phi, hphi, ?_⟩
  refine windowPreconv (I := I) K beta psiT p (fun k => gSeq (phi k)) gInf gRef L hL
    (fun k => hgLip (phi k)) hInfLip (Set.range e) ?_ ?_
  · intro t ht delta hdelta
    obtain ⟨n, hn⟩ := hdense t ht delta hdelta
    exact ⟨e n, ⟨n, rfl⟩, he n, hn⟩
  · rintro tau ⟨n, rfl⟩ _ eps heps
    exact hnet n eps heps

end HCGCompactness
end DifferentialGeometry
