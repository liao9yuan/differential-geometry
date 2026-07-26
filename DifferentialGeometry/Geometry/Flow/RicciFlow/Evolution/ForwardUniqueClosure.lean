import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRateLe
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Forward-uniqueness closure: `E ≡ 0` and `g₁ = g₂` (Route-K brick K5)

`Evolution/ForwardUniqueEnergy.lean` (K3) differentiates the Kotschwar energy exactly and
`Evolution/ForwardUniqueRateLe.lean` (K4) bounds that derivative by `K·E − D`.  This file is
the **scalar closure** of `ShortTime/FORWARD_UNIQUE_PRO_RULING.md` §6: the two facts plus
the closed-edge hypothesis `g₁ a = g₂ a` force the energy to vanish on the whole compact
slab, and a vanishing energy forces the two metrics to agree.

No new analysis happens here.  The three steps are

1. **Grönwall** — `E(a) = 0`, `E' ≤ K·E` on the *open* interval, `E` continuous up to the
   closed edge, so `E ≡ 0` on `Icc a c`.  Derivatives are never taken at the edge.
2. **Integral-zero-to-equality** — the energy density is a sum of three squared fibre norms,
   hence nonnegative; a nonnegative *continuous* integrand with zero integral against the
   Riemannian volume measure (which is positive on nonempty opens) vanishes identically, and
   fibre positive-definiteness then kills the metric-difference carrier.
3. **Continuation** — every `t ∈ Ico a b` lies in a compact subslab `Icc a c` with `c < b`,
   so the per-subslab conclusion sups up to the half-open window.

## Main results

* `gronwall_zero_on` — the closed-edge Grönwall closure on `Icc a c`.
* `energy_zero_on` — `∀ t ∈ Icc a c, forwardUniqueEnergy g₁ g₂ t = 0`, under the combined
  K3 + K4 slab package.
* `metric_eq_of_energy_zero` — `forwardUniqueEnergy g₁ g₂ t = 0 → g₁ t = g₂ t`.
* `metrics_eq_on` — the compact-slab capstone `∀ t ∈ Icc a c, g₁ t = g₂ t`.
* `metrics_eq_ico` — the half-open continuation `∀ t ∈ Ico a b, g₁ t = g₂ t`.

## Hypothesis discipline

`energy_zero_on` quotes the K3 and K4 hypothesis packages **verbatim**, quantified over the
open subslab `Ioo a c`; the two theorems are called, never re-proved.  The carrier fields
`Sfield`, `U`, `rem` therefore become time-indexed families and the K4 constants are
slab-uniform, which is exactly the ruling's "constants slab-local, no global `Ico a b`
constant" discipline.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.Measure

section ScalarGronwall

/-! ## The closed-edge Grönwall closure

`Analysis/Spectral/Intrinsic/DeTurck/EdgeStrongData.lean` proves the same statement for the
left edge `0` of `Icc 0 T`.  The forward-uniqueness slab starts at an arbitrary time `a`, so
the statement is given here for `Icc a c`; the proof is the same two-step argument (ordinary
Grönwall on `[a + ε, t]`, then `ε → 0⁺`).  Canonical home for the merged statement is
`Analysis/ODE/`, next to `IntegralGronwall.lean`; it is kept local here because the file that
holds the `Icc 0 T` version sits in the (currently unbuilt) intrinsic-spectral tree. -/

/-- **Closed-edge Grönwall closure.**  A nonnegative function that vanishes at the left edge
`a`, is continuous on the closed slab `Icc a c`, and satisfies `f' ≤ K · f` on the *open*
slab `Ioo a c`, vanishes identically on `Icc a c`.

No derivative at the edge is required: the differential inequality is used only on `Ioo a c`
and the edge is reached by continuity. -/
theorem gronwall_zero_on {a c K : ℝ} (hac : a < c)
    (energy energy' : ℝ → ℝ)
    (hcont : ContinuousOn energy (Icc a c))
    (hzero : energy a = 0)
    (hnonneg : ∀ t ∈ Icc a c, 0 ≤ energy t)
    (hderiv : ∀ t ∈ Ioo a c, HasDerivAt energy (energy' t) t)
    (hbound : ∀ t ∈ Ioo a c, energy' t ≤ K * energy t) :
    ∀ t ∈ Icc a c, energy t = 0 := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | htpos
  · exact hzero
  have hlimc : Filter.Tendsto energy (nhdsWithin a (Ioo a c)) (nhds 0) := by
    have hlim := (hcont a ⟨le_rfl, hac.le⟩).tendsto.mono_left
      (nhdsWithin_mono a Ioo_subset_Icc_self)
    simpa only [hzero] using hlim
  have hsub : Ioo a t ⊆ Ioo a c := fun s hs => ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩
  have hlim : Filter.Tendsto energy (nhdsWithin a (Ioo a t)) (nhds 0) :=
    hlimc.mono_left (nhdsWithin_mono a hsub)
  haveI : (nhdsWithin a (Ioo a t)).NeBot := by
    rw [nhdsWithin_Ioo_eq_nhdsGT htpos]
    infer_instance
  have heps : Filter.Tendsto (fun ε : ℝ => ε) (nhdsWithin a (Ioo a t)) (nhds a) :=
    (continuous_id.tendsto a).mono_left nhdsWithin_le_nhds
  have harg : Filter.Tendsto (fun ε : ℝ => K * (t - ε))
      (nhdsWithin a (Ioo a t)) (nhds (K * (t - a))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub heps)
  have hexp : Filter.Tendsto (fun ε : ℝ => Real.exp (K * (t - ε)))
      (nhdsWithin a (Ioo a t)) (nhds (Real.exp (K * (t - a)))) :=
    Real.continuous_exp.continuousAt.tendsto.comp harg
  have hrhs : Filter.Tendsto (fun ε : ℝ => energy ε * Real.exp (K * (t - ε)))
      (nhdsWithin a (Ioo a t)) (nhds 0) := by
    simpa only [zero_mul] using hlim.mul hexp
  have hev : ∀ᶠ ε in nhdsWithin a (Ioo a t),
      energy t ≤ energy ε * Real.exp (K * (t - ε)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hcontε : ContinuousOn energy (Icc ε t) :=
      hcont.mono (Icc_subset_Icc hε.1.le ht.2)
    have hslope : ∀ x ∈ Ico ε t, ∀ r, energy' x < r →
        ∃ᶠ z in nhdsWithin x (Ioi x), (z - x)⁻¹ * (energy z - energy x) < r := by
      intro x hx r hr
      have hxc : x ∈ Ioo a c :=
        ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_lt_of_le hx.2 ht.2⟩
      exact (hderiv x hxc).hasDerivWithinAt.liminf_right_slope_le hr
    have hgr := le_gronwallBound_of_liminf_deriv_right_le (ε := 0) hcontε hslope le_rfl
      (fun x hx => by
        have hxc : x ∈ Ioo a c :=
          ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_lt_of_le hx.2 ht.2⟩
        have := hbound x hxc
        linarith) t ⟨hε.2.le, le_rfl⟩
    simpa only [gronwallBound_ε0] using hgr
  exact le_antisymm (ge_of_tendsto hrhs hev) (hnonneg t ht)

end ScalarGronwall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]

section EdgeValue

/-! ## The energy at the closed edge

`h0 : g₁ a = g₂ a` makes all three difference carriers vanish, hence the density, hence the
energy.  Together with `energy_nonneg` this supplies two of `gronwall_zero_on`'s inputs. -/

/-- The squared fibre norm of the zero covariant tensor vanishes. -/
private theorem normSq0S_zero (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ) :
    normSq0S (I := I) g x s 0 = 0 :=
  ((tensor0SMetricData (I := I) g x s).inner_self_eq_zero_iff 0).2 rfl

/-- A vanishing squared fibre norm forces the tensor to vanish. -/
private theorem eq_zero_of_normSq0S (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {A : Tensor0SSpace s I x} (h : normSq0S (I := I) g x s A = 0) : A = 0 :=
  ((tensor0SMetricData (I := I) g x s).inner_self_eq_zero_iff A).1 h

/-- The Kotschwar energy is nonnegative: its density is a sum of three squared fibre norms. -/
theorem energy_nonneg (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ) :
    0 ≤ forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t :=
  integral_nonneg fun x => density_nonneg (I := I) g₁ g₂ t x

/-- Equal metrics at time `t` give a vanishing energy density. -/
theorem density_eq_zero_of_eq (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {t : ℝ}
    (h : g₁ t = g₂ t) (x : M) :
    forwardUniqueDensity (I := I) g₁ g₂ t x = 0 := by
  rw [forwardUniqueDensity, metricDiffSq_def, connDiffSq_def, rmDiffSq_def, h]
  rw [metricDiffAt_self, connDiffLowAt_self, rmDiffLowAt_self,
    normSq0S_zero, normSq0S_zero, normSq0S_zero]
  ring

/-- **The closed-edge energy vanishes.**  This is the `E(a) = 0` input of `gronwall_zero_on`,
supplied by the forward-uniqueness hypothesis `h0 : g₁ a = g₂ a`. -/
theorem energy_eq_zero_of_eq (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {t : ℝ}
    (h : g₁ t = g₂ t) :
    forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t = 0 := by
  simp only [forwardUniqueEnergy, density_eq_zero_of_eq (I := I) g₁ g₂ h, integral_zero]

end EdgeValue

section EnergyZero

/-! ## Step 1: the energy vanishes on the compact slab

The hypothesis list is the **union of the K3 and K4 packages**, quoted verbatim and
quantified over the open subslab `Ioo a c` (the K3 window is `U := Ioo a c`), together with
the two edge inputs `hinit` and `hcont`.  Neither theorem is re-proved: `energy_zero_on`
calls `forwardUniqueEnergy_hasDerivAt` for the derivative and `forwardUniqueRate_le` (with
`dissipation_nonneg`) for the differential inequality, and feeds both to
`gronwall_zero_on`. -/

/-- **The forward-uniqueness energy vanishes on the compact slab `Icc a c`.**

`E' ≤ K·E − D ≤ K·E` on `Ioo a c` by K4, `E(a) = 0` by the closed-edge hypothesis
`hinit : g₁ a = g₂ a`, `E ≥ 0` always, and `E` is continuous up to the closed edge; the
Grönwall closure then forces `E ≡ 0`.  The Grönwall constant is K4's explicit
`K = C_R + 4C_Ric + 2 + δC_A + δ⁻¹ + C_V + ε⁻¹C_U + C_rem`.

The carrier fields `Sfield`, `Uflux`, `rem` are time-indexed families and the constants are
slab-uniform: this is the ruling's "constants slab-local, no global `Ico a b` constant". -/
theorem energy_zero_on
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (Adot : ℝ → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : ℝ → (x : M) → Tensor0SSpace 4 I x)
    (Sfield : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Uflux : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (rem : ℝ → (x : M) → Tensor0SSpace 4 I x)
    {a c ε δ C_A C_R C_Ric C_V C_U C_rem : ℝ}
    (hac : a < c)
    -- K3 package, on the open window `U := Ioo a c`
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ioo a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdens : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (Ioo a c ×ˢ (Set.univ : Set M)))
    (hPDE₁ : ∀ t ∈ Ioo a c, ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : ℝ => (g₁ r).inner x X Y)
        ((-2 : ℝ) * metricRicciAt (I := I) (g₁ t) x
          (fun i : Fin 2 => if i = 0 then X else Y)) t)
    (hPDE₂ : ∀ t ∈ Ioo a c, ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : ℝ => (g₂ r).inner x X Y)
        ((-2 : ℝ) * metricRicciAt (I := I) (g₂ t) x
          (fun i : Fin 2 => if i = 0 then X else Y)) t)
    (hA : ∀ t ∈ Ioo a c, ∀ (x : M) (v : Fin 3 → TangentSpace I x),
      HasDerivAt (fun r : ℝ => connDiffLowAt (I := I) (g₁ r) (g₂ r) x v) (Adot t x v) t)
    (hS : ∀ t ∈ Ioo a c, ∀ (x : M) (v : Fin 4 → TangentSpace I x),
      HasDerivAt (fun r : ℝ => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x v) (Sdot t x v) t)
    -- K4 package, slab-uniform constants and time-indexed carrier fields
    (hε : 0 < ε) (hδ : 0 < δ) (habs : δ * C_A + ε ≤ 1)
    (hcar : ∀ t ∈ Ioo a c, ∀ x, Sfield t x = rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)
    (hSdec : ∀ t ∈ Ioo a c, ∀ x, Sdot t x =
      roughLap0SField (I := I) (g₁ t) (Sfield t) x +
        covDiv0SField (I := I) (g₁ t) (Uflux t) x + rem t x)
    (hUb : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 5 (Uflux t x) ≤
      C_U * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hrem : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 4 (rem t x) ≤
      C_rem * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hreact : ∀ t ∈ Ioo a c, ∀ x,
      movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
          (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
          (connDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
      C_R * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hRic : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 2
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) ≤
      C_Ric * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hAdot : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 3 (Adot t x) ≤
      C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
        normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) (Sfield t) x)))
    (hvol : ∀ t ∈ Ioo a c, ∀ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V)
    (hirest : ∀ t ∈ Ioo a c, Integrable (fun x => rateRest (I := I) g₁ g₂ Adot t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hipair : ∀ t ∈ Ioo a c, Integrable
      (fun x => 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hilap : ∀ t ∈ Ioo a c, Integrable (fun x => inner0S (I := I) (g₁ t) x 4
        (roughLap0SField (I := I) (g₁ t) (Sfield t) x) (Sfield t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidiv : ∀ t ∈ Ioo a c, Integrable (fun x => inner0S (I := I) (g₁ t) x 4
        (covDiv0SField (I := I) (g₁ t) (Uflux t) x) (Sfield t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hirem : ∀ t ∈ Ioo a c, Integrable
      (fun x => inner0S (I := I) (g₁ t) x 4 (rem t x) (Sfield t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hinab : ∀ t ∈ Ioo a c, Integrable (fun x => inner0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (Sfield t) x) (Uflux t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidis : ∀ t ∈ Ioo a c, Integrable (fun x => normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (Sfield t) x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidens : ∀ t ∈ Ioo a c, Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    -- closed-edge inputs
    (hinit : g₁ a = g₂ a)
    (hcont : ContinuousOn (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (Icc a c)) :
    ∀ t ∈ Icc a c, forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t = 0 := by
  refine gronwall_zero_on
    (K := C_R + 4 * C_Ric + 2 + δ * C_A + δ⁻¹ + C_V + ε⁻¹ * C_U + C_rem) hac
    (forwardUniqueEnergy (I := I) (M := M) g₁ g₂)
    (forwardUniqueRate (I := I) (M := M) g₁ g₂ Adot Sdot)
    hcont (energy_eq_zero_of_eq (I := I) g₁ g₂ hinit)
    (fun t _ => energy_nonneg (I := I) g₁ g₂ t)
    (fun t ht => forwardUniqueEnergy_hasDerivAt (I := I) g₁ g₂ Adot Sdot isOpen_Ioo ht
      hgram hdens (hPDE₁ t ht) (hPDE₂ t ht) (hA t ht) (hS t ht))
    (fun t ht => ?_)
  have hle := forwardUniqueRate_le (I := I) g₁ g₂ Adot Sdot (Sfield t) (Uflux t) (rem t)
    hε hδ habs (hcar t ht) (hSdec t ht) (hUb t ht) (hrem t ht) (hreact t ht) (hRic t ht)
    (hAdot t ht) (hvol t ht) (hirest t ht) (hipair t ht) (hilap t ht) (hidiv t ht)
    (hirem t ht) (hinab t ht) (hidis t ht) (hidens t ht)
  have hD := dissipation_nonneg (I := I) (M := M) g₁ (Sfield t) t
  linarith

end EnergyZero

section IntegralZero

/-! ## Step 2: a vanishing energy forces the two metrics to agree

The density is a sum of three squared fibre norms, so it is nonnegative; a nonnegative
integrable function with zero integral vanishes almost everywhere; the Riemannian volume
measure is positive on nonempty open sets, so a *continuous* a.e.-zero function is zero
everywhere; and fibre positive-definiteness turns `|h₀₂|² = 0` into `h₀₂ = 0`, i.e. into
equality of the two inner products. -/

/-- **Extensionality for smooth Riemannian metrics.**  Only the `inner` field is data;
`symm`, `pos`, `isVonNBounded` and `contMDiff` are `Prop`-valued, hence proof-irrelevant.

Canonical home is `Geometry/Metric/Basic.lean`; this is the third local copy (see
`Geometry/Metric/Sphere/QuotientDescent.lean` and
`ShortTime/DeTurckRealizedSolutionFamily.lean`), kept private here because neither of those
files is an admissible import for the `Evolution` layer. -/
private theorem metricExtInner {g g' : SmoothRiemannianMetric I M}
    (h : ∀ (x : M) (v w : TangentSpace I x), g.inner x v w = g'.inner x v w) : g = g' := by
  obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g
  obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g'
  have hi : i₁ = i₂ :=
    funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
  subst hi
  rfl

/-- **Integral-zero-to-metric-equality.**  A vanishing forward-uniqueness energy at time `t`
forces `g₁ t = g₂ t`.

`hdcont` is the continuity of the energy density in the space variable at the fixed time `t`
— the regularity that turns "a.e. zero" into "everywhere zero" against the full-support
Riemannian volume measure; `hidens` is K4's own integrability side condition. -/
theorem metric_eq_of_energy_zero (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {t : ℝ}
    (hdcont : Continuous (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x))
    (hidens : Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hE : forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t = 0) :
    g₁ t = g₂ t := by
  rw [forwardUniqueEnergy] at hE
  have hae : (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      =ᵐ[riemannianMeasureFamily (I := I) (M := M) g₁ t] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg
      (fun x => density_nonneg (I := I) g₁ g₂ t x) hidens).mp hE
  haveI : (riemannianMeasureFamily (I := I) (M := M) g₁ t).IsOpenPosMeasure := by
    rw [riemannianMeasureFamily_def]
    exact riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) (g₁ t)
  have heq : (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x) = 0 :=
    (Continuous.ae_eq_iff_eq (riemannianMeasureFamily (I := I) (M := M) g₁ t)
      hdcont continuous_const).mp hae
  refine metricExtInner (I := I) fun x X Y => ?_
  have hx : forwardUniqueDensity (I := I) g₁ g₂ t x = 0 := congrFun heq x
  have hmnn : (0 : ℝ) ≤ metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [metricDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 2 _
  have hmle := metricDiffSq_le_dens (I := I) g₁ g₂ t x
  have hm : normSq0S (I := I) (g₁ t) x 2 (metricDiffAt (I := I) (g₁ t) (g₂ t) x) = 0 := by
    rw [← metricDiffSq_def]; linarith
  have h0 : metricDiffAt (I := I) (g₁ t) (g₂ t) x = 0 :=
    eq_zero_of_normSq0S (I := I) (g₁ t) x 2 hm
  have hval := congrArg (fun A : Tensor0SSpace 2 I x =>
    A (fun i : Fin 2 => if i = 0 then X else Y)) h0
  simp only [metricDiffAt_apply, Tensor0SSpace.zero_apply] at hval
  norm_num at hval
  linarith [hval]

end IntegralZero

section Capstone

/-! ## Step 3: the two metrics agree, first on `Icc a c`, then on `Ico a b`

`metrics_eq_on` is the compact-slab capstone: it runs `energy_zero_on` and then
`metric_eq_of_energy_zero` at every time of the slab.  `metrics_eq_ico` is the elementary
continuation step: every `t ∈ Ico a b` lies in some compact subslab `Icc a c` with `c < b`,
and the ruling's hypothesis package is per-subslab, so the conclusion sups up. -/

/-- **Forward uniqueness on a compact slab.**  Under the combined K3 + K4 slab package, the
closed-edge hypothesis `hinit : g₁ a = g₂ a`, continuity of the energy up to the closed edge,
and the space-continuity/integrability of the density on the closed slab, the two flows agree
on `Icc a c`. -/
theorem metrics_eq_on
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (Adot : ℝ → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : ℝ → (x : M) → Tensor0SSpace 4 I x)
    (Sfield : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Uflux : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (rem : ℝ → (x : M) → Tensor0SSpace 4 I x)
    {a c ε δ C_A C_R C_Ric C_V C_U C_rem : ℝ}
    (hac : a < c)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ioo a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdens : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (Ioo a c ×ˢ (Set.univ : Set M)))
    (hPDE₁ : ∀ t ∈ Ioo a c, ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : ℝ => (g₁ r).inner x X Y)
        ((-2 : ℝ) * metricRicciAt (I := I) (g₁ t) x
          (fun i : Fin 2 => if i = 0 then X else Y)) t)
    (hPDE₂ : ∀ t ∈ Ioo a c, ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : ℝ => (g₂ r).inner x X Y)
        ((-2 : ℝ) * metricRicciAt (I := I) (g₂ t) x
          (fun i : Fin 2 => if i = 0 then X else Y)) t)
    (hA : ∀ t ∈ Ioo a c, ∀ (x : M) (v : Fin 3 → TangentSpace I x),
      HasDerivAt (fun r : ℝ => connDiffLowAt (I := I) (g₁ r) (g₂ r) x v) (Adot t x v) t)
    (hS : ∀ t ∈ Ioo a c, ∀ (x : M) (v : Fin 4 → TangentSpace I x),
      HasDerivAt (fun r : ℝ => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x v) (Sdot t x v) t)
    (hε : 0 < ε) (hδ : 0 < δ) (habs : δ * C_A + ε ≤ 1)
    (hcar : ∀ t ∈ Ioo a c, ∀ x, Sfield t x = rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)
    (hSdec : ∀ t ∈ Ioo a c, ∀ x, Sdot t x =
      roughLap0SField (I := I) (g₁ t) (Sfield t) x +
        covDiv0SField (I := I) (g₁ t) (Uflux t) x + rem t x)
    (hUb : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 5 (Uflux t x) ≤
      C_U * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hrem : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 4 (rem t x) ≤
      C_rem * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hreact : ∀ t ∈ Ioo a c, ∀ x,
      movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
          (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
          (connDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
      C_R * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hRic : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 2
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) ≤
      C_Ric * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hAdot : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 3 (Adot t x) ≤
      C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
        normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) (Sfield t) x)))
    (hvol : ∀ t ∈ Ioo a c, ∀ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V)
    (hirest : ∀ t ∈ Ioo a c, Integrable (fun x => rateRest (I := I) g₁ g₂ Adot t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hipair : ∀ t ∈ Ioo a c, Integrable
      (fun x => 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hilap : ∀ t ∈ Ioo a c, Integrable (fun x => inner0S (I := I) (g₁ t) x 4
        (roughLap0SField (I := I) (g₁ t) (Sfield t) x) (Sfield t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidiv : ∀ t ∈ Ioo a c, Integrable (fun x => inner0S (I := I) (g₁ t) x 4
        (covDiv0SField (I := I) (g₁ t) (Uflux t) x) (Sfield t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hirem : ∀ t ∈ Ioo a c, Integrable
      (fun x => inner0S (I := I) (g₁ t) x 4 (rem t x) (Sfield t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hinab : ∀ t ∈ Ioo a c, Integrable (fun x => inner0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (Sfield t) x) (Uflux t x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidis : ∀ t ∈ Ioo a c, Integrable (fun x => normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) (Sfield t) x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidens : ∀ t ∈ Icc a c, Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hdcont : ∀ t ∈ Icc a c, Continuous (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x))
    (hinit : g₁ a = g₂ a)
    (hcont : ContinuousOn (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (Icc a c)) :
    ∀ t ∈ Icc a c, g₁ t = g₂ t := by
  have hzero := energy_zero_on (I := I) g₁ g₂ Adot Sdot Sfield Uflux rem hac hgram hdens
    hPDE₁ hPDE₂ hA hS hε hδ habs hcar hSdec hUb hrem hreact hRic hAdot hvol hirest hipair
    hilap hidiv hirem hinab hidis (fun t ht => hidens t (Ioo_subset_Icc_self ht)) hinit hcont
  exact fun t ht => metric_eq_of_energy_zero (I := I) g₁ g₂ (hdcont t ht) (hidens t ht)
    (hzero t ht)

/-- **Forward uniqueness on the half-open window.**  The ruling's hypothesis package is
per-subslab, so the compact-slab conclusion of `metrics_eq_on` is quantified over the
subslab endpoints `c ∈ Ioo a b`; every `t ∈ Ico a b` lies in `Icc a c` for
`c = (t + b)/2 ∈ Ioo a b`, which is the ruling's "sup over `c < b`". -/
theorem metrics_eq_ico (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {a b : ℝ}
    (h : ∀ c ∈ Ioo a b, ∀ t ∈ Icc a c, g₁ t = g₂ t) :
    ∀ t ∈ Ico a b, g₁ t = g₂ t := by
  intro t ht
  have htb : t < b := ht.2
  have hat : a ≤ t := ht.1
  refine h ((t + b) / 2) ⟨by linarith, by linarith⟩ t ⟨hat, by linarith⟩

end Capstone

end DifferentialGeometry.PDE.RicciFlow

end
