import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Exponential.SmoothnessClose
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartPushVFEq
import DifferentialGeometry.Coordinates.NablaComponents
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.IntegralCurve.Transform

set_option linter.unusedSectionVars false

/-!
# Affine reparametrisation of geodesics

Skeleton stubs for the tangent-bundle chain rule plus affine
reparametrisation of geodesics. The four declarations below state:

* `chartChristoffelContraction_smul_left_right` — bilinear scaling of the
  chart-Christoffel contraction in both vector slots simultaneously.
* `geodesicVectorFieldChartFiber_scaling_along_lift` — degree-two fibre
  homogeneity of `geodesicVectorFieldChart g α`.
* `scaledTangentLift_transport` — rescaling an integral curve of
  `geodesicVectorFieldChart g α` by an affine reparametrisation and a
  fibre rescaling yields another integral curve of the same field.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Bilinear scaling of the chart-Christoffel contraction in both vector
slots: `Γ(a v, a w)(y) = a² · Γ(v, w)(y)`. -/
theorem chartChristoffelContraction_smul_left_right
    (g : SmoothRiemannianMetric I M) (α : M) (a : ℝ) (v w : E) (y : E) :
    chartChristoffelContraction (I := I) g α (a • v) (a • w) y
      = (a * a) • chartChristoffelContraction (I := I) g α v w y := by
  classical
  unfold chartChristoffelContraction
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [smul_smul]
  congr 1
  calc ∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i (a • v) * chartCoord (E := E) j (a • w)
      = ∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
          (a * chartCoord (E := E) i v) * (a * chartCoord (E := E) j w) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [chartCoord_smul, chartCoord_smul]
    _ = (a * a) * ∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i v * chartCoord (E := E) j w := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        ring

/-- **Fibre-coordinate scaling under fibre rescaling.** Scaling the fibre
vector of a tangent-bundle point by `c` scales its chart-`α` fibre
coordinate by `c`: `chartFiberCoord α ⟨q.proj, c • q.snd⟩ = c • chartFiberCoord α q`.
This holds whenever `q.proj` lies in the chart-`α` source (so that the
trivialisation at `α` acts linearly on the fibre over `q.proj`). -/
theorem chartFiberCoord_fiberScale
    (α : M) (c : ℝ) {q : TangentBundle I M}
    (hq : q.proj ∈ (chartAt H α).source) :
    chartFiberCoord (I := I) α
        (⟨q.proj, c • q.snd⟩ : TangentBundle I M) =
      c • chartFiberCoord (I := I) α q := by
  classical
  have hbase : q.proj ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hq
  -- `chartFiberCoord α p = (continuousLinearMapAt ℝ p.proj) p.snd` for `p` over
  -- the base set; this map is `ℝ`-linear in the fibre vector.
  have hcoe : ∀ w : E,
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ q.proj) w =
        (trivializationAt E (TangentSpace I) α
          (⟨q.proj, w⟩ : TangentBundle I M)).2 := by
    intro w
    have hcoe' :=
      (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem (R := ℝ) hbase
    change ((trivializationAt E (TangentSpace I) α).linearMapAt ℝ q.proj) w = _
    exact congrFun hcoe' w
  -- LHS fibre coord.
  have hL : chartFiberCoord (I := I) α
      (⟨q.proj, c • q.snd⟩ : TangentBundle I M) =
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ q.proj)
        (c • q.snd) := by
    rw [chartFiberCoord_def]; exact (hcoe (c • q.snd)).symm
  -- RHS fibre coord (note `q = ⟨q.proj, q.snd⟩` by `TotalSpace` eta).
  have hR : chartFiberCoord (I := I) α q =
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ q.proj)
        q.snd := by
    rw [chartFiberCoord_def]; exact (hcoe q.snd).symm
  rw [hL, hR, map_smul]

section ChartCoordBridges

variable [I.Boundaryless]

/-- **Within-set, fixed-base forward chart bridge.** For a curve
`f : ℝ → TangentBundle I M` that is an integral curve of
`geodesicVectorFieldChart g α` on `S`, and a time `t ∈ S` whose
projection lies in the chart-`α` source, the chart-pushed curve at the
fixed zero-section base `⟨α, 0⟩` has the chart-phase ODE
`HasDerivWithinAt` form on `S` at `t`.

This is the `IsMIntegralCurveOn` / `HasDerivWithinAt` analogue of the
neighbourhood-form `eventually_hasDerivAt_chartPhaseVF_at_zero_section`;
it works at endpoints of `S` because it never passes to a full
neighbourhood. -/
theorem hasDerivWithinAt_chartPhaseVF_at_zero_section_within
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {S : Set ℝ} {t : ℝ}
    (ht : t ∈ S) (hsrc : (f t).proj ∈ (chartAt H α).source)
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g α) S) :
    HasDerivWithinAt
      (fun s' : ℝ => extChartAt I.tangent
        (⟨α, (0 : E)⟩ : TangentBundle I M) (f s'))
      (chartPhaseVF (I := I) g α
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f t)))
      S t := by
  classical
  set q₀ : TangentBundle I M := (⟨α, (0 : E)⟩ : TangentBundle I M) with hq₀_def
  -- `f t ∈` chart-of-`TM`-at-`⟨α,0⟩` source.
  have hf_chsrc : f t ∈ (chartAt (ModelProd H E) q₀).source :=
    (mem_chartAt_modelProd_zero_source_iff (I := I) α (f t)).mpr hsrc
  -- Mirror the within-version of `IsMIntegralCurveOn.hasDerivWithinAt`,
  -- with the running chart base replaced by the fixed `q₀`.
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t
    (hasMFDerivWithinAt_extChartAt (I := I.tangent) hf_chsrc) (hf t ht)
    (Set.subset_preimage_image _ _)).congr_mfderiv
  -- The composed CLM equals the target `(1).smulRight (chartPhaseVF …)`.
  -- Identify the two CLMs through the `comp`/`smulRight`/`toSpanSingleton`
  -- algebra, reducing to the fibre-vector equality supplied by
  -- `tangentCoordChange_tangent_geodesicVF`.
  rw [mfderiv_chartAt_eq_tangentCoordChange hf_chsrc, hq₀_def]
  -- It remains to identify the two CLMs `ℝ →L (E × E)`.  Both are determined by
  -- their value at `1`; the LHS gives `tcc (V (f t))`, the RHS `chartPhaseVF …`.
  have hval :
      (tangentCoordChange I.tangent (f t) (⟨α, (0 : E)⟩ : TangentBundle I M) (f t))
          (geodesicVectorFieldChart (I := I) g α (f t)) =
        chartPhaseVF (I := I) g α
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f t)) := by
    trans (geodesicVectorFieldChartFiber (I := I) g α (f t))
    · exact tangentCoordChange_tangent_geodesicVF (I := I) g α (f t) hsrc
    · symm
      rw [extChartAt_tangent_zero_apply_chartFiber (I := I) α hsrc]
      rfl
  apply ContinuousLinearMap.ext_ring
  change (tangentCoordChange I.tangent (f t) (⟨α, (0 : E)⟩ : TangentBundle I M) (f t))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (geodesicVectorFieldChart (I := I) g α (f t))) 1) =
    (ContinuousLinearMap.toSpanSingleton ℝ
      (chartPhaseVF (I := I) g α
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f t)))) 1
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  exact hval

end ChartCoordBridges

/-- An `IsMIntegralCurveOn` of `geodesicVectorFieldChart g α`, rescaled in
the time variable by an affine reparametrisation and in the fibre by the
matching constant, yields another `IsMIntegralCurveOn` of the same
field. This is the degree-two homogeneity of the geodesic spray on `T(TM)`:
combining time-rescaling-by-`c` (which would scale the vector field by `c`
via `IsMIntegralCurveOn.comp_mul`) with the matching fibre rescaling on the
lift exactly cancels the extra `c`, returning the same vector field.

The chart-coordinate skeleton is provided by the proved lemmas in this
file.  The **forward** bridge
`hasDerivWithinAt_chartPhaseVF_at_zero_section_within` (fully proved, on the
locus where the lift's projection lies in the chart-`α` source) turns an
integral-curve hypothesis into the chart-phase ODE for the chart-`⟨α,0⟩`
push; the fibre-rescaling identity `chartFiberCoord_fiberScale` (fully
proved) identifies the chart-`⟨α,0⟩` push of the candidate lift
`s ↦ ⟨(f(c·s+d)).proj, c • (f(c·s+d)).snd⟩` with `rescaleChartOrbit c` of
the chart-`⟨α,0⟩` push of `f ∘ (s ↦ c·s+d)`; and `hasDerivAt_rescaled_orbit`
/ `chartPhaseVF_rescale` (with the degree-two `chartChristoffel` core
`chartChristoffelContraction_smul_left_right`) supply the chart-phase ODE
for that rescaled push.

The remaining residual is the **reverse** reconstruction — turning the
chart-`⟨α,0⟩` push's chart-phase ODE back into the manifold
`HasMFDerivWithinAt` — which is the within-set, fixed-base inverse of
`tangentCoordChange_tangent_geodesicVF`, mirroring Mathlib's
`exists_isMIntegralCurveAt_of_contMDiffAt` reconstruction
(`HasFDerivWithinAt.comp` of `hasFDerivWithinAt_tangentCoordChange` with the
chart-`⟨α,0⟩` push derivative), plus the within-set form of
`hasDerivAt_rescaled_orbit` for the affine-and-rescale chain rule. -/
theorem scaledTangentLift_transport
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {S : Set ℝ}
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g α) S)
    (c d : ℝ) :
    IsMIntegralCurveOn
      (fun s : ℝ =>
        (⟨(f (c * s + d)).proj, c • (f (c * s + d)).snd⟩ : TangentBundle I M))
      (geodesicVectorFieldChart (I := I) g α)
      {s : ℝ | c * s + d ∈ S} := by
  -- Forward direction (proved): on the locus where `(f ·).proj` stays in the
  -- chart-`α` source, `hasDerivWithinAt_chartPhaseVF_at_zero_section_within`
  -- gives the chart-`⟨α,0⟩` push of `f` a chart-phase derivative; composing
  -- with the affine map `s ↦ c·s+d` (slope `c`) and the linear fibre rescale
  -- (matched by `chartPhaseVF_rescale` /
  -- `chartChristoffelContraction_smul_left_right`) gives the chart-phase
  -- derivative of the chart-`⟨α,0⟩` push of the candidate lift, which by
  -- `chartFiberCoord_fiberScale` equals `rescaleChartOrbit c` of the push of
  -- `f ∘ (·c+d)`.  Reverse direction (residual): reconstruct the manifold
  -- `HasMFDerivWithinAt` from this chart-phase derivative — the within-set,
  -- fixed-base inverse of `tangentCoordChange_tangent_geodesicVF`, mirroring
  -- `exists_isMIntegralCurveAt_of_contMDiffAt`.
  let _hf' := hf
  sorry

/-! ## Affine reparametrisation invariance of `pathELength`

For an affine reparametrisation `s ↦ c * s + d` with `c > 0`, the
`pathELength` of the composed curve over `Icc ((a - d) / c) ((b - d) / c)`
equals the `pathELength` of the original curve over `Icc a b`. This is a
direct corollary of Mathlib's `pathELength_comp_of_monotoneOn` applied to
the strictly increasing affine map `s ↦ c * s + d`.

The lemma is stated in the `Manifold` namespace's `pathELength`. The
typeclass requirement `[∀ x, ENormSMulClass ℝ (TangentSpace I x)]` for
the underlying Mathlib reparametrisation lemma is supplied by the
`RiemannianBundle` instance through the chain
`RiemannianBundle ⟶ NormedAddCommGroup ⟶ NormSMulClass ⟶ ENormSMulClass`.
-/

section AffinePathELengthReparam

open Manifold

variable [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- Affine reparametrisation invariance of `pathELength` with positive
slope. If `c > 0` and `a ≤ b`, then the path length of `s ↦ γ (c * s + d)`
on `Icc ((a - d) / c) ((b - d) / c)` equals the path length of `γ` on
`Icc a b`, provided `γ` is `MDifferentiableOn` `Icc a b`. -/
theorem pathELength_comp_affineHomeo
    (γ : ℝ → M) {a b : ℝ} (c d : ℝ) (hab : a ≤ b) (hc : 0 < c)
    (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ (Set.Icc a b)) :
    pathELength I (fun s : ℝ => γ (c * s + d)) ((a - d) / c) ((b - d) / c)
      = pathELength I γ a b := by
  -- The reparametrisation `f s = c * s + d`.
  set f : ℝ → ℝ := fun s : ℝ => c * s + d with hf_def
  -- Image of the endpoints: `f ((a - d) / c) = a`, `f ((b - d) / c) = b`.
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hfa : f ((a - d) / c) = a := by
    simp only [hf_def]
    rw [mul_div_cancel₀ _ hc_ne]
    ring
  have hfb : f ((b - d) / c) = b := by
    simp only [hf_def]
    rw [mul_div_cancel₀ _ hc_ne]
    ring
  -- The new lower endpoint is `≤` the new upper endpoint.
  have hab' : (a - d) / c ≤ (b - d) / c := by
    rw [div_le_div_iff_of_pos_right hc]
    linarith
  -- `f` is monotone on `Icc ((a - d) / c) ((b - d) / c)` (it is monotone
  -- on `ℝ`, hence on any subset).
  have hf_mono : MonotoneOn f (Set.Icc ((a - d) / c) ((b - d) / c)) := by
    intro x _ y _ hxy
    simp only [hf_def]
    have : c * x ≤ c * y := mul_le_mul_of_nonneg_left hxy hc.le
    linarith
  -- `f` is differentiable everywhere, hence on `Icc ((a - d) / c) ((b - d) / c)`.
  have hf_diff : DifferentiableOn ℝ f (Set.Icc ((a - d) / c) ((b - d) / c)) := by
    intro x _
    -- `f x = c * x + d` is differentiable; convert from `Differentiable`.
    have hdiff : Differentiable ℝ f := by
      simp only [hf_def]
      exact ((differentiable_const c).mul differentiable_id).add (differentiable_const d)
    exact (hdiff x).differentiableWithinAt
  -- The hypothesis `MDiff[Icc (f a') (f b')] γ` becomes `MDifferentiableOn`
  -- on `Icc a b` after rewriting via `hfa`/`hfb`.
  have hγ' : MDifferentiableOn 𝓘(ℝ, ℝ) I γ
      (Set.Icc (f ((a - d) / c)) (f ((b - d) / c))) := by
    rw [hfa, hfb]; exact hγ
  -- Apply Mathlib's `pathELength_comp_of_monotoneOn`.
  have hmain :
      pathELength I (γ ∘ f) ((a - d) / c) ((b - d) / c)
        = pathELength I γ (f ((a - d) / c)) (f ((b - d) / c)) :=
    pathELength_comp_of_monotoneOn (I := I) (γ := γ) hab' hf_mono hf_diff hγ'
  -- Rewrite the endpoints.
  rw [hfa, hfb] at hmain
  -- The composition `γ ∘ f` is `fun s => γ (c * s + d)` by definition of `f`.
  exact hmain

end AffinePathELengthReparam

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
