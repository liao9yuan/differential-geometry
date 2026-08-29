import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Equation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.MetricLowerBound
import DifferentialGeometry.Geometry.Metric.Convergence.RicciFromJetsCompact

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Phi : PointedCGHMaps (I := I) X P subseq)

/-- Scalar curvature of the pulled-back sequence converges uniformly on a
compact spatial set and the whole compact time window. -/
theorem ConvOut.scalar_convOn
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Phi) (hsrc : SrcSigma Phi) (htgt : TgtSigma Phi)
    (beta psi : Real) (cLow : Real) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ (k : Nat) (t : Real), t ∈ Set.Icc beta psi →
        ∀ (y : SourceDomain (I := I) Phi k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
            letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            TangentSpace I y),
          cLow * R.inner (y : P.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
            letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
              sourceDomSmooth (I := I) Phi k
            (srcMetric (I := I) Phi hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc beta psi →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Phi R bf hsrc htgt k t) R z ≤ C)
    (co : ConvOut (I := I) Phi R bf hsrc htgt beta psi)
    (K : Set P.M)
    (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∀ epsilon : Real, 0 < epsilon → ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
      ∀ t : Real, t ∈ Set.Icc beta psi → ∀ x : P.M, x ∈ K →
        |(letI : TopologicalSpace (X.term ((subseq ∘ co.φ) k)).M :=
              (X.term ((subseq ∘ co.φ) k)).topology;
           letI : ChartedSpace H (X.term ((subseq ∘ co.φ) k)).M :=
              (X.term ((subseq ∘ co.φ) k)).charted;
           letI : IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M :=
              (X.term ((subseq ∘ co.φ) k)).smooth;
           letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
              (X.term ((subseq ∘ co.φ) k)).M := (by
                change IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M
                infer_instance);
           letI : SigmaCompactSpace (X.term ((subseq ∘ co.φ) k)).M :=
              (X.term ((subseq ∘ co.φ) k)).sigmaCompact;
           letI : T2Space (X.term ((subseq ∘ co.φ) k)).M :=
              (X.term ((subseq ∘ co.φ) k)).t2;
           (X.term ((subseq ∘ co.φ) k)).S.scalar t (Phi.map (co.φ k) x)) -
          metricScalarAt (I := I) (co.gInf t) x| < epsilon := by
  classical
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : CompleteSpace E := FiniteDimensional.complete Real E
  let lam : Real := min cLow 1
  have hlam : 0 < lam := by
    simpa only [lam] using lt_min hcLow one_pos
  have hlowSeq : ∀ (k : Nat) (t : Real), t ∈ Set.Icc beta psi →
      ∀ (x : P.M) (v : TangentSpace I x),
        lam * R.inner x v v ≤
          (gSeqExt (I := I) Phi R bf hsrc htgt (co.φ k) t).inner x v v := by
    intro k t ht x v
    simpa only [lam] using
      gSeqExt_lower (I := I) Phi R bf hsrc htgt cLow beta psi hcLow hbound
        (co.φ k) t ht x v
  have hlowInf : ∀ (t : Real), t ∈ Set.Icc beta psi →
      ∀ (x : P.M) (v : TangentSpace I x),
        lam * R.inner x v v ≤ (co.gInf t).inner x v v :=
    ConvOut.lower_of (I := I) (Φ := Phi) co hlowSeq
  choose C hC using hcovTail
  let Cmax : Real := max (C 0) (max (C 1) (C 2))
  let B0 : Real := max 0 (Cmax + 1)
  have hCmax : ∀ a : Nat, a ≤ 2 → C a ≤ Cmax := by
    intro a ha
    interval_cases a <;> simp only [Cmax, le_max_iff] <;> aesop
  obtain ⟨kgrow, hkgrow⟩ := bf.grow_cover K hK
  have hbddSeqC : ∀ (k : Nat), kgrow ≤ k → ∀ (t : Real),
      t ∈ Set.Icc beta psi → ∀ (x : P.M), x ∈ K →
        ∀ a : Nat, a ≤ 2 →
          metricCovDerivNorm (I := I) a
            (gSeqExt (I := I) Phi R bf hsrc htgt (co.φ k) t) R x ≤ C a := by
    intro k hk t ht x hx a _ha
    exact hC a (co.φ k) t ht x
      (hkgrow (co.φ k) (hk.trans (co.hφ.id_le k)) hx)
  have hbddSeq : ∀ (k : Nat), kgrow ≤ k → ∀ (t : Real),
      t ∈ Set.Icc beta psi → ∀ (x : P.M), x ∈ K →
        ∀ a : Nat, a ≤ 2 →
          metricCovDerivNorm (I := I) a
            (gSeqExt (I := I) Phi R bf hsrc htgt (co.φ k) t) R x ≤ B0 := by
    intro k hk t ht x hx a ha
    exact (hbddSeqC k hk t ht x hx a ha).trans
      ((hCmax a ha).trans
        ((le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)))
  obtain ⟨kconv, hkconv⟩ := co.conv K hK 2 1 one_pos
  let kbase : Nat := max kgrow kconv
  have hkbaseGrow : kgrow ≤ kbase := le_max_left _ _
  have hkbaseConv : kconv ≤ kbase := le_max_right _ _
  have hbddInf : ∀ (t : Real), t ∈ Set.Icc beta psi →
      ∀ (x : P.M), x ∈ K → ∀ a : Nat, a ≤ 2 →
        metricCovDerivNorm (I := I) a (co.gInf t) R x ≤ B0 := by
    intro t ht x hx a ha
    have hdiff : metricDerivNorm (I := I) a (co.gInf t)
        (gSeqExt (I := I) Phi R bf hsrc htgt (co.φ kbase) t) R x < 1 := by
      rw [metricDerivNorm_symm (I := I) a (co.gInf t)
        (gSeqExt (I := I) Phi R bf hsrc htgt (co.φ kbase) t) R x]
      exact (derivNorm_le_sup (I := I) hK ha
        (gSeqExt (I := I) Phi R bf hsrc htgt (co.φ kbase) t) (co.gInf t) R hx).trans_lt
          (hkconv kbase hkbaseConv t ht)
    have htri := covNorm_le_add (I := I) a (co.gInf t)
      (gSeqExt (I := I) Phi R bf hsrc htgt (co.φ kbase) t) R x
    calc
      metricCovDerivNorm (I := I) a (co.gInf t) R x
          ≤ metricCovDerivNorm (I := I) a
              (gSeqExt (I := I) Phi R bf hsrc htgt (co.φ kbase) t) R x +
            metricDerivNorm (I := I) a (co.gInf t)
              (gSeqExt (I := I) Phi R bf hsrc htgt (co.φ kbase) t) R x := htri
      _ ≤ Cmax + 1 := add_le_add
        ((hbddSeqC kbase hkbaseGrow t ht x hx a ha).trans (hCmax a ha)) hdiff.le
      _ ≤ B0 := le_max_right _ _
  obtain ⟨Csc, hCsc, hscalar⟩ :=
    scalarSub_le_dNormOn (I := I) R hK lam B0 hlam
  intro epsilon hepsilon
  let den : Real := 3 * Csc + 1
  have hden : 0 < den := by
    dsimp only [den]
    nlinarith
  let delta : Real := epsilon / den
  have hdelta : 0 < delta := div_pos hepsilon hden
  obtain ⟨kdelta, hkdelta⟩ := co.conv K hK 2 delta hdelta
  refine ⟨max kgrow kdelta, fun k hk t ht x hx ↦ ?_⟩
  have hkGrow : kgrow ≤ k := (le_max_left _ _).trans hk
  have hkDelta : kdelta ≤ k := (le_max_right _ _).trans hk
  let u := gSeqExt (I := I) Phi R bf hsrc htgt (co.φ k) t
  let rho := metricDerivNormSupOn (I := I) K 2 u (co.gInf t) R
  have hrho : rho < delta := by
    simpa only [rho, u] using hkdelta k hkDelta t ht
  have hsum :
      (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u (co.gInf t) R x) ≤
        3 * rho := by
    calc
      (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u (co.gInf t) R x)
          ≤ ∑ _q ∈ Finset.range 3, rho := by
            exact Finset.sum_le_sum fun q hq ↦
              derivNorm_le_sup (I := I) hK
                (Nat.le_of_lt_succ (Finset.mem_range.1 hq)) u (co.gInf t) R hx
      _ = 3 * rho := by norm_num
  have hlocal := hscalar u (co.gInf t)
    (fun y _hy xi ↦ hlowSeq k t ht y xi)
    (fun y _hy xi ↦ hlowInf t ht y xi)
    (fun y hy a ha ↦ hbddSeq k hkGrow t ht y hy a ha)
    (fun y hy a ha ↦ hbddInf t ht y hy a ha) x hx
  have hdeltaEq : delta * den = epsilon := by
    dsimp only [delta]
    exact div_mul_cancel₀ epsilon (ne_of_gt hden)
  have hprod : Csc * (3 * rho) < epsilon := by
    have hmul : 3 * Csc * rho < 3 * Csc * delta :=
      mul_lt_mul_of_pos_left hrho (mul_pos (by norm_num) hCsc)
    dsimp only [den] at hdeltaEq
    nlinarith
  have hmetric :
      |metricScalarAt (I := I) u x - metricScalarAt (I := I) (co.gInf t) x| < epsilon :=
    (hlocal.trans (mul_le_mul_of_nonneg_left hsum hCsc.le)).trans_lt hprod
  have hxgrow : x ∈ bf.grow (co.φ k) :=
    hkgrow (co.φ k) (hkGrow.trans (co.hφ.id_le k)) hx
  dsimp only [u] at hmetric
  rw [gSeqExt_scalar (I := I) Phi R bf hsrc htgt (co.φ k) t x hxgrow] at hmetric
  simpa only [Function.comp_apply] using hmetric

end HCGCompactness
end DifferentialGeometry
