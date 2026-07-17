import DifferentialGeometry.Analysis.Integration.Measure.FamilyLocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjPotential
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.FlowVariation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Perelman's W variation along reversed Ricci flow

This file assembles the actual reverse-flow metric, scalar-curvature,
gradient-square, and reconstructed-potential paths into a local first
variation of `W`.  The pointwise geometric derivatives live in
`FlowVariation`; this module is only their moving-volume assembly.
-/

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Bundle Filter MeasureTheory Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

universe u uE uH

variable {M : Type u}

private theorem w_base_eq [MeasurableSpace M]
    (mu : Measure M) (n : Nat) (tau : Real)
    (scalar gradSq potential : M -> Real)
    (htau : 0 ≤ tau)
    (hmeas : AEMeasurable
      (fun x : M => ENNReal.ofReal (perelmanDensity n tau potential x)) mu) :
    wFunctional mu n tau scalar gradSq potential =
      ∫ x, perelmanDensity n tau potential x *
        wEntropyBracket n tau scalar gradSq potential x ∂mu := by
  unfold wFunctional perelmanWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (μ := mu)
    (f := fun x : M => ENNReal.ofReal (perelmanDensity n tau potential x))
    hmeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    (wEntropyBracket n tau scalar gradSq potential)]
  apply integral_congr_ae
  filter_upwards with x
  have hnonneg : 0 ≤ perelmanDensity n tau potential x := by
    unfold perelmanDensity perelmanDensityPrefactor
    exact mul_nonneg
      (Real.rpow_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) htau) _)
      (Real.exp_pos _).le
  simp only [ENNReal.toReal_ofReal hnonneg, smul_eq_mul]

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The actual reversed Ricci-flow metric, scalar curvature, squared gradient,
and positive conjugate-heat potential have a local first variation of
Perelman's `W` functional. -/
theorem w_rev_hasDerivAt
    [I.Boundaryless] [CompactSpace M]
    {D Dr : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (n : Nat)
    (u : Real -> M -> Real)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn Dr
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) T)
      (fun r x =>
        (conjCoeff (I := I) (M := M) S (T - r) : M -> Real) x) u)
    (hpos : ∀ r : Real, r ∈ Dr.regular ∩ Set.Ioi (0 : Real) ->
      ∀ x : M, 0 < u r x)
    {s : Real} (hs : s ∈ Dr.regular) (hspos : 0 < s)
    (hTs : T - s ∈ D.regular) :
    let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
    let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
    let R : Real -> M -> Real := fun r x => S.scalar (T - r) x
    let q : Real -> M -> Real := fun r x =>
      (G.metric r).inner x
        (gradientFun (I := I) (G.metric r) (f r) x)
        (gradientFun (I := I) (G.metric r) (f r) x)
    let ft : M -> Real := fun x =>
      laplacianAt (I := I) G s (f s) x - q s x + R s x -
        (n : Real) / (2 * s)
    let Rt : M -> Real := fun x =>
      -(laplacianAt (I := I) G s (R s) x +
        2 * normSq0S (I := I) (G.metric s) x 2 (S.ricci (T - s) x))
    let qt : M -> Real := fun x =>
      (-2 : Real) * S.ricciAt (T - s) x
          (vec2
            (gradientFun (I := I) (G.metric s) (f s) x)
            (gradientFun (I := I) (G.metric s) (f s) x)) +
        2 * (G.metric s).inner x
          (gradientFun (I := I) (G.metric s) ft x)
          (gradientFun (I := I) (G.metric s) (f s) x)
    WEntropyHasFirstVariationAt
      (volumeMeasureFamily (I := I) (M := M) G) n (fun r : Real => r)
      R q f s
      (∫ x,
        wEntropyWeightedIntegralVariationIntegrand n s 1
          (f s) ft (fun y => 2 * R s y)
          (wEntropyBracket n s (R s) (q s) (f s))
          (wEntropyBracketVariation s 1 (R s) Rt (q s) qt ft) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s)) := by
  dsimp only
  let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
  have huScalar : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn Dr G
      (fun r x => -S.scalar (T - r) x) u := by
    simpa only [G, conjCoeff_apply] using hu
  let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
  let R : Real -> M -> Real := fun r x => S.scalar (T - r) x
  let q : Real -> M -> Real := fun r x =>
    (G.metric r).inner x
      (gradientFun (I := I) (G.metric r) (f r) x)
      (gradientFun (I := I) (G.metric r) (f r) x)
  let ft : M -> Real := fun x =>
    laplacianAt (I := I) G s (f s) x - q s x + R s x -
      (n : Real) / (2 * s)
  let Rt : M -> Real := fun x =>
    -(laplacianAt (I := I) G s (R s) x +
      2 * normSq0S (I := I) (G.metric s) x 2 (S.ricci (T - s) x))
  let qt : M -> Real := fun x =>
    (-2 : Real) * S.ricciAt (T - s) x
        (vec2
          (gradientFun (I := I) (G.metric s) (f s) x)
          (gradientFun (I := I) (G.metric s) (f s) x)) +
      2 * (G.metric s).inner x
        (gradientFun (I := I) (G.metric s) ft x)
        (gradientFun (I := I) (G.metric s) (f s) x)
  let U : Set Real :=
    (Dr.regular ∩ Set.Ioi (0 : Real)) ∩ {r : Real | T - r ∈ D.regular}
  have hUo : IsOpen U := by
    dsimp only [U]
    exact (Dr.regular_isOpen.inter isOpen_Ioi).inter
      (D.regular_isOpen.preimage (continuous_const.sub continuous_id))
  have hsU : s ∈ U := ⟨⟨hs, hspos⟩, hTs⟩
  have hUmap : Set.MapsTo (fun r : Real => T - r) U D.regular := by
    intro r hr
    exact hr.2
  have hgram (x₀ : M) (i j : Fin (Module.finrank Real E)) :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          chartGramMatrix (I := I) (G.metric p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    simpa only [G] using
      revGram_smooth (I := I) (M := M) (S := S) hS T hUmap x₀ i j
  have hf :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => f p.1 p.2) (U ×ˢ Set.univ) := by
    have h := potential_joint (I := I) Dr G
      (fun r x => -S.scalar (T - r) x) u n huScalar hpos
    simpa only [f] using h.mono
      (Set.prod_mono (fun _ hr => hr.1) Set.Subset.rfl)
  have hrev :
      ContMDiff (𝓘(Real, Real).prod I) (𝓘(Real, Real).prod I) ∞
        (fun p : Real × M => (T - p.1, p.2)) :=
    (contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd
  have hR :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => R p.1 p.2) (U ×ˢ Set.univ) := by
    have h := (scalar_joint (I := I) S hS).comp hrev.contMDiffOn
      (fun p (hp : p ∈ U ×ˢ Set.univ) =>
        ⟨hUmap hp.1, Set.mem_univ p.2⟩)
    simpa only [R, Function.comp_apply] using h
  have hq :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => q p.1 p.2) (U ×ˢ Set.univ) := by
    simpa only [q] using
      gradSq_joint (I := I) G hUo hgram f hf
  have huU :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => u p.1 p.2) (U ×ˢ Set.univ) :=
    huScalar.jointSmooth.mono
      (Set.prod_mono (fun _ hr => hr.1.1) Set.Subset.rfl)
  have hdens :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => perelmanDensity n p.1 (f p.1) p.2)
        (U ×ˢ Set.univ) := by
    refine huU.congr ?_
    intro p hp
    have heq := density_potential n (u p.1) hp.1.1.2 (hpos p.1 hp.1.1)
    simpa only [f] using congrFun heq p.2
  have htau :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => p.1) (U ×ˢ Set.univ) :=
    contMDiffOn_fst
  have hn :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun _ : Real × M => (n : Real)) (U ×ˢ Set.univ) :=
    contMDiffOn_const
  have hbracket :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          wEntropyBracket n p.1 (R p.1) (q p.1) (f p.1) p.2)
        (U ×ˢ Set.univ) := by
    simpa only [wEntropyBracket] using
      ((htau.mul (hR.add hq)).add hf).sub hn
  have hintegrand :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          perelmanDensity n p.1 (f p.1) p.2 *
            wEntropyBracket n p.1 (R p.1) (q p.1) (f p.1) p.2)
        (U ×ˢ Set.univ) :=
    hdens.mul hbracket
  have hft (x : M) :
      HasDerivAt (fun r : Real => f r x) (ft x) s := by
    simpa only [f, ft, q, R, G, sub_neg_eq_add] using
      potential_pde (I := I) Dr G
        (fun r y => -S.scalar (T - r) y) u n huScalar hs hspos
        (hpos s ⟨hs, hspos⟩) x
  have hRt (x : M) :
      HasDerivAt (fun r : Real => R r x) (Rt x) s := by
    simpa only [R, Rt, G] using
      revScalar_time (I := I) S hS T s hTs x
  have hqt (x : M) :
      HasDerivAt (fun r : Real => q r x) (qt x) s := by
    simpa only [q, qt, f, ft, R, G, sub_neg_eq_add] using
      revGradSq_time (I := I) S hS T
        (fun r y => -S.scalar (T - r) y) u n huScalar hpos hs hspos hTs x
  have htrace (x : M) :
      traceTimeDerivMetricAt (I := I) G s x = 2 * R s x := by
    simpa only [G, R] using
      revTrace_eq (I := I) (M := M) (S := S) hS T s hTs x
  have hbaseEq :
      (fun r : Real =>
        wFunctional (volumeMeasureFamily (I := I) (M := M) G r) n r
          (R r) (q r) (f r)) =ᶠ[nhds s]
        (fun r : Real =>
          ∫ x, perelmanDensity n r (f r) x *
            wEntropyBracket n r (R r) (q r) (f r) x
          ∂(volumeMeasureFamily (I := I) (M := M) G r)) := by
    filter_upwards [hUo.mem_nhds hsU] with r hr
    have hdensity : perelmanDensity n r (f r) = u r := by
      simpa only [f] using
        density_potential n (u r) hr.1.2 (hpos r hr.1)
    have hcont : Continuous (perelmanDensity n r (f r)) := by
      rw [hdensity]
      exact (huScalar.sliceSmooth r (Dr.regular_subset hr.1.1)).continuous
    have hmeas : AEMeasurable
        (fun x : M => ENNReal.ofReal (perelmanDensity n r (f r) x))
        (volumeMeasureFamily (I := I) (M := M) G r) :=
      (ENNReal.continuous_ofReal.comp hcont).aemeasurable
    exact w_base_eq
      (volumeMeasureFamily (I := I) (M := M) G r) n r
      (R r) (q r) (f r) hr.1.2.le hmeas
  have hvar := first_var_joint (I := I) (M := M)
    (g_fam := G.metric)
    (f := fun r x => perelmanDensity n r (f r) x *
      wEntropyBracket n r (R r) (q r) (f r) x)
    hUo hsU hgram hintegrand
  have hbase :
      HasDerivAt
        (fun r : Real =>
          ∫ x, perelmanDensity n r (f r) x *
            wEntropyBracket n r (R r) (q r) (f r) x
          ∂(volumeMeasureFamily (I := I) (M := M) G r))
        (∫ x,
          wEntropyWeightedIntegralVariationIntegrand n s 1
            (f s) ft (fun y => 2 * R s y)
            (wEntropyBracket n s (R s) (q s) (f s))
            (wEntropyBracketVariation s 1 (R s) Rt (q s) qt ft) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s)) s := by
    refine hvar.congr_deriv ?_
    apply integral_congr_ae
    filter_upwards with x
    have hdensDeriv := perelmanDensity_hasDerivAt
      (M := M) (n := n) (tauPath := fun r : Real => r)
      (potentialPath := f) (s0 := s) (tau := s) (tauVariation := 1)
      rfl hspos (hasDerivAt_id (x := s)) hft x
    have hbracketDeriv := wEntropyBracket_hasDerivAt
      (M := M) (n := n) (tauPath := fun r : Real => r)
      (scalarCurvaturePath := R) (gradPotentialNormSqPath := q)
      (potentialPath := f) (s0 := s) (tau := s) (tauVariation := 1)
      rfl (hasDerivAt_id (x := s)) hRt hqt hft x
    have hderiv := (hdensDeriv.mul hbracketDeriv).deriv
    change
      deriv
          ((fun r : Real => perelmanDensity n r (f r) x) *
            fun r : Real => wEntropyBracket n r (R r) (q r) (f r) x) s +
          (1 / 2) * traceTimeDerivMetricAt (I := I) G s x *
            (perelmanDensity n s (f s) x *
              wEntropyBracket n s (R s) (q s) (f s) x) =
        wEntropyWeightedIntegralVariationIntegrand n s 1
          (f s) ft (fun y => 2 * R s y)
          (wEntropyBracket n s (R s) (q s) (f s))
          (wEntropyBracketVariation s 1 (R s) Rt (q s) qt ft) x
    rw [hderiv, htrace x]
    unfold wEntropyWeightedIntegralVariationIntegrand
      wEntropyWeightedMeasureVariationFactor
    ring
  have hout := WEntropyHasFirstVariationAt_of_baseIntegral_hasDerivAt
    (M := M)
    (muPath := volumeMeasureFamily (I := I) (M := M) G)
    (n := n) (tauPath := fun r : Real => r)
    (scalarCurvaturePath := R) (gradPotentialNormSqPath := q)
    (potentialPath := f) (s0 := s)
    hbaseEq hbase
  simpa only [G, f, R, q, ft, Rt, qt] using hout

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
