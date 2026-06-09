import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.StepAInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedEmetric

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 §2 Step A: good coverings by balls — the radius `λ[r]`

This file begins the Step A construction for `metricCompactness` (MSM135 Theorem
3.9).  `InjRadiusDecayInput.mu` is the Cheeger--Gromov--Taylor injectivity-radius
lower bound `μ[r] = a·min(ι₀,1)ⁿ·e^{−Cr}` of MSM135 Proposition `lbl384` (the
radius appearing in `InjRadiusDecayInput.decay`).  `InjRadiusDecayInput.lambda D r`
is the MSM135 eq (`lbl386`) covering radius `λ[r] = μ[r]/D`.

The geometric payoff of this layer (`lambda_hasInjRadiusAt`) is that for `D ≥ 1`
the radius `λ[d(x,O)]` never exceeds the injectivity radius at `x`, so the balls
`B(x, λ[d(x,O)])` are embedded.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

namespace InjRadiusDecayInput

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

/-- The Cheeger--Gromov--Taylor injectivity-radius lower bound
`μ[r] = a·min(ι₀,1)ⁿ·e^{−Cr}` of MSM135 Proposition `lbl384`.  This is exactly
the radius appearing in `InjRadiusDecayInput.decay`. -/
noncomputable def mu (hd : InjRadiusDecayInput (I := I) X) (r : Real) : Real :=
  hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) * Real.exp (-hd.C * r)

/-- MSM135 eq (`lbl386`): the covering radius `λ[r] = μ[r]/D`. -/
noncomputable def lambda (hd : InjRadiusDecayInput (I := I) X) (D r : Real) : Real :=
  hd.mu r / D

theorem mu_pos (hd : InjRadiusDecayInput (I := I) X) (r : Real) : 0 < hd.mu r :=
  mul_pos (mul_pos hd.a_pos (pow_pos (lt_min hd.baseInj.pos one_pos) _)) (Real.exp_pos _)

theorem mu_nonneg (hd : InjRadiusDecayInput (I := I) X) (r : Real) : 0 ≤ hd.mu r :=
  (hd.mu_pos r).le

theorem mu_antitone (hd : InjRadiusDecayInput (I := I) X) : Antitone hd.mu := by
  intro r₁ r₂ h
  have hK : 0 ≤ hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) :=
    (mul_pos hd.a_pos (pow_pos (lt_min hd.baseInj.pos one_pos) _)).le
  have hexp : Real.exp (-hd.C * r₂) ≤ Real.exp (-hd.C * r₁) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left h hd.C_nonneg])
  exact mul_le_mul_of_nonneg_left hexp hK

theorem lambda_pos (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (r : Real) : 0 < hd.lambda D r :=
  div_pos (hd.mu_pos r) hD

theorem lambda_antitone (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D) :
    Antitone (hd.lambda D) := by
  intro r₁ r₂ h
  exact mul_le_mul_of_nonneg_right (hd.mu_antitone h) (inv_nonneg.mpr hD.le)

theorem lambda_le_mu (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 1 ≤ D)
    (r : Real) : hd.lambda D r ≤ hd.mu r :=
  div_le_self (hd.mu_nonneg r) hD

/-- MSM135 chooses `D` large so that `λ[0] ≤ 1`.  This holds once
`D ≥ a·min(ι₀,1)ⁿ`. -/
theorem lambda_le_one_at_zero (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) ≤ D) :
    hd.lambda D 0 ≤ 1 := by
  have hpos : 0 < hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) :=
    mul_pos hd.a_pos (pow_pos (lt_min hd.baseInj.pos one_pos) _)
  have hDpos : 0 < D := lt_of_lt_of_le hpos hD
  unfold lambda mu
  rw [mul_zero, Real.exp_zero, mul_one]
  exact (div_le_one hDpos).mpr hD

/-- Geometric payoff of `λ`: for `D ≥ 1` the radius `λ[d(x,O)]` is at most the
injectivity radius at `x`, so `B(x, λ[d(x,O)])` is embedded.  This is the
combination of MSM135 `lbl386` with the decay estimate `lbl384`. -/
theorem lambda_hasInjRadiusAt (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 1 ≤ D) (k : Nat) (x : (X.obj k).M) :
    HasInjRadiusAt (I := I) (X.obj k) x
      (hd.lambda D (hd.dist k x (X.obj k).basepoint)) := by
  have hdecay := hd.decay k x
  rw [hasInjRadiusAt_iff] at hdecay ⊢
  refine ⟨hd.lambda_pos (lt_of_lt_of_le one_pos hD) _, ?_⟩
  exact le_trans (ENNReal.ofReal_le_ofReal (hd.lambda_le_mu hD _)) hdecay.2

end InjRadiusDecayInput

/-! ## A2: maximal `λ`-separated packing (Zorn engine)

The MSM135 net of ball centers (`lbl383`) is realized as a maximal pairwise-disjoint
family of `λ`-balls.  These two generic lemmas are the engine: a maximal
pairwise-disjoint family exists, and maximality forces every outside point's set to
meet a chosen one (the covering property `lbl387`).  They are stated generically and
can be lifted to a generic order/set layer later. -/
section Packing

variable {α : Type*} {β : Type*}

/-- A maximal pairwise-disjoint family `S` (under `⊆`) exists for any `f : α → Set β`,
by Zorn: pairwise-disjointness is preserved under unions of chains. -/
theorem exists_maximal_pairwiseDisjoint (f : α → Set β) :
    ∃ S : Set α, S.PairwiseDisjoint f ∧
      ∀ T : Set α, S ⊆ T → T.PairwiseDisjoint f → T ⊆ S := by
  have hchainub : ∀ c ⊆ {T : Set α | T.PairwiseDisjoint f}, IsChain (· ⊆ ·) c →
      ∃ ub ∈ {T : Set α | T.PairwiseDisjoint f}, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    intro x hx y hy hxy
    rw [Set.mem_sUnion] at hx hy
    obtain ⟨s₁, hs₁, hx⟩ := hx
    obtain ⟨s₂, hs₂, hy⟩ := hy
    rcases hchain.total hs₁ hs₂ with hsub | hsub
    · exact hc hs₂ (hsub hx) hy hxy
    · exact hc hs₁ hx (hsub hy) hxy
  obtain ⟨S, hSpd, hSmax⟩ :=
    zorn_subset {T : Set α | T.PairwiseDisjoint f} hchainub
  exact ⟨S, hSpd, fun T hST hT => hSmax hT hST⟩

/-- Maximality of a pairwise-disjoint family is a covering property: any point `z`
outside the family has `f z` meeting some `f x` with `x` in the family.  Instantiated
with `λ`-balls this is the doubled-ball cover of MSM135 `lbl387`. -/
theorem exists_not_disjoint_of_maximal_pairwiseDisjoint (f : α → Set β) {S : Set α}
    (hS : S.PairwiseDisjoint f)
    (hmax : ∀ T : Set α, S ⊆ T → T.PairwiseDisjoint f → T ⊆ S)
    {z : α} (hz : z ∉ S) :
    ∃ x ∈ S, ¬ Disjoint (f z) (f x) := by
  by_contra hcon
  push Not at hcon
  exact hz (hmax (insert z S) (Set.subset_insert z S)
    (hS.insert fun y hy _ => hcon y hy) (Set.mem_insert z S))

end Packing

namespace InjRadiusDecayInput

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

/-- The MSM135 `lbl383` `λ`-ball `B(x, λ[d(x,O)])` of the `k`-th manifold, in the
Riemannian emetric of its stored metric (`PointedRiemannianManifold.emetricSpace`). -/
def lambdaBall (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat)
    (x : (X.obj k).M) : Set ((X.obj k).M) :=
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  Metric.eball x (ENNReal.ofReal (hd.lambda D (hd.dist k x (X.obj k).basepoint)))

/-- MSM135 `lbl383` net of ball centers: a maximal `λ`-separated family `S` exists in
the `k`-th manifold, so the `λ`-balls `{B(x, λ[d(x,O)]) : x ∈ S}` are pairwise disjoint
and `S` is maximal (the covering input to `lbl387`).  Immediate from
`exists_maximal_pairwiseDisjoint` applied to `lambdaBall`. -/
theorem exists_lambdaNet (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat) :
    ∃ S : Set ((X.obj k).M),
      S.PairwiseDisjoint (hd.lambdaBall D k) ∧
      ∀ T : Set ((X.obj k).M),
        S ⊆ T → T.PairwiseDisjoint (hd.lambdaBall D k) → T ⊆ S :=
  exists_maximal_pairwiseDisjoint (hd.lambdaBall D k)

/-- MSM135 `lbl387` geometric cover (Zorn form): every point `z` of the `k`-th
manifold lies within `λ[d(z,O)] + λ[d(x,O)]` of some center `x` of a maximal
`λ`-separated net `S`.  (With the book's distance-ordered net one would get the
cleaner `2λ[r^α]`; the maximal-packing route gives the point-dependent sum, which
still covers.)  Proof: `z ∈ S` is immediate; otherwise maximality gives a center
`x` whose `λ`-ball meets `z`'s, and the emetric triangle inequality bounds
`edist z x`. -/
theorem lambdaNet_cover (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat)
    (hD : 0 < D) {S : Set ((X.obj k).M)}
    (hS : S.PairwiseDisjoint (hd.lambdaBall D k))
    (hmax : ∀ T : Set ((X.obj k).M),
      S ⊆ T → T.PairwiseDisjoint (hd.lambdaBall D k) → T ⊆ S)
    (z : (X.obj k).M) :
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
    ∃ x ∈ S, edist z x <
      ENNReal.ofReal (hd.lambda D (hd.dist k z (X.obj k).basepoint)) +
      ENNReal.ofReal (hd.lambda D (hd.dist k x (X.obj k).basepoint)) := by
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  by_cases hz : z ∈ S
  · refine ⟨z, hz, ?_⟩
    rw [edist_self]
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (hd.lambda_pos hD _)) le_self_add
  · obtain ⟨x, hxS, hndis⟩ :=
      exists_not_disjoint_of_maximal_pairwiseDisjoint (hd.lambdaBall D k) hS hmax hz
    obtain ⟨w, hwz, hwx⟩ := Set.not_disjoint_iff.mp hndis
    refine ⟨x, hxS, ?_⟩
    have e1 : edist w z <
        ENNReal.ofReal (hd.lambda D (hd.dist k z (X.obj k).basepoint)) := hwz
    have e2 : edist w x <
        ENNReal.ofReal (hd.lambda D (hd.dist k x (X.obj k).basepoint)) := hwx
    calc edist z x ≤ edist z w + edist w x := edist_triangle z w x
      _ < _ := by rw [edist_comm z w]; exact ENNReal.add_lt_add e1 e2

/-- MSM135 net separation (dual to `lambdaNet_cover`): distinct centers of a
pairwise-disjoint `λ`-net are `λ`-separated in the emetric,
`λ[d(x,O)] ≤ edist x y`.  This is the volume-packing input that, combined with the
A0' multiplicity bound, controls the number of net balls.  Proof: if `edist x y`
were below `λ[d(x,O)]` then `y` would lie in both `B(x,λ_x)` and `B(y,λ_y)`,
contradicting disjointness. -/
theorem lambdaNet_separated (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat)
    (hD : 0 < D) {S : Set ((X.obj k).M)}
    (hS : S.PairwiseDisjoint (hd.lambdaBall D k))
    {x y : (X.obj k).M} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
    ENNReal.ofReal (hd.lambda D (hd.dist k x (X.obj k).basepoint)) ≤ edist x y := by
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  have hdisj := Set.disjoint_left.mp (hS hx hy hxy)
  by_contra hlt
  push Not at hlt
  have hyx : y ∈ hd.lambdaBall D k x :=
    lt_of_eq_of_lt (edist_comm y x) hlt
  have hyy : y ∈ hd.lambdaBall D k y :=
    lt_of_eq_of_lt (edist_self y) (ENNReal.ofReal_pos.mpr (hd.lambda_pos hD _))
  exact hdisj hyx hyy

/-- The supplied distance realizes the Riemannian emetric of each manifold:
`edist x y = ofReal (dist k x y)`, with `dist ≥ 0`.  This makes precise the
documented intent that `PointedSeqDistance` is the Riemannian distance, now that
the emetric (`PointedRiemannianManifold.emetricSpace`) is available.  It bridges
the `edist`-separated net to the `dist`-stated volume input A0'. -/
structure RealizesEdist (hd : InjRadiusDecayInput (I := I) X) : Prop where
  dist_nonneg : ∀ (k : Nat) (x y : (X.obj k).M), 0 ≤ hd.dist k x y
  edist_eq : ∀ (k : Nat) (x y : (X.obj k).M),
    (letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
     edist x y) = ENNReal.ofReal (hd.dist k x y)

/-- Under `RealizesEdist` the supplied distance is symmetric (from `edist_comm`). -/
theorem RealizesEdist.dist_comm {hd : InjRadiusDecayInput (I := I) X}
    (hre : hd.RealizesEdist) (k : Nat) (x y : (X.obj k).M) :
    hd.dist k x y = hd.dist k y x := by
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  have : ENNReal.ofReal (hd.dist k x y) = ENNReal.ofReal (hd.dist k y x) := by
    rw [← hre.edist_eq k x y, ← hre.edist_eq k y x, edist_comm]
  exact (ENNReal.ofReal_eq_ofReal_iff (hre.dist_nonneg k x y)
    (hre.dist_nonneg k y x)).mp this

/-- Under `RealizesEdist` the supplied distance satisfies the triangle inequality
(from `edist_triangle`; the bridge forces `edist` finite, so `toReal` is additive). -/
theorem RealizesEdist.dist_triangle {hd : InjRadiusDecayInput (I := I) X}
    (hre : hd.RealizesEdist) (k : Nat) (x y z : (X.obj k).M) :
    hd.dist k x z ≤ hd.dist k x y + hd.dist k y z := by
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  have h1 : ENNReal.ofReal (hd.dist k x z) ≤
      ENNReal.ofReal (hd.dist k x y) + ENNReal.ofReal (hd.dist k y z) := by
    rw [← hre.edist_eq k x z, ← hre.edist_eq k x y, ← hre.edist_eq k y z]
    exact edist_triangle x y z
  rw [← ENNReal.ofReal_add (hre.dist_nonneg k x y) (hre.dist_nonneg k y z)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (hre.dist_nonneg k x y) (hre.dist_nonneg k y z))).mp h1

/-- Reverse triangle for the distance to the basepoint. -/
theorem RealizesEdist.distO_sub_le {hd : InjRadiusDecayInput (I := I) X}
    (hre : hd.RealizesEdist) (k : Nat) (x y : (X.obj k).M) :
    hd.dist k y (X.obj k).basepoint - hd.dist k x (X.obj k).basepoint ≤ hd.dist k x y := by
  have h := hre.dist_triangle k y x (X.obj k).basepoint
  have hc := hre.dist_comm k y x
  linarith

/-- The covering radius in closed form: `λ[r] = (a·min(ι₀,1)ⁿ/D)·e^{−Cr}`. -/
theorem lambda_eq (hd : InjRadiusDecayInput (I := I) X) (D r : Real) :
    hd.lambda D r =
      (hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) / D) * Real.exp (-hd.C * r) := by
  unfold InjRadiusDecayInput.lambda InjRadiusDecayInput.mu
  ring

/-- λ-ratio bound (the mechanism behind `lbl391`'s `e^{cC}` factors): for nearby
points `λ[d(x,O)] ≤ e^{C·dist(x,y)}·λ[d(y,O)]`, since `λ` decays like `e^{−Cr}` and
`d(y,O) − d(x,O) ≤ dist(x,y)`. -/
theorem lambda_ratio_le (hd : InjRadiusDecayInput (I := I) X) (hre : hd.RealizesEdist)
    (D : Real) (k : Nat) (hD : 0 < D) (x y : (X.obj k).M) :
    hd.lambda D (hd.dist k x (X.obj k).basepoint) ≤
      Real.exp (hd.C * hd.dist k x y) *
        hd.lambda D (hd.dist k y (X.obj k).basepoint) := by
  rw [hd.lambda_eq D, hd.lambda_eq D]
  have hP : 0 ≤ hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) / D :=
    le_of_lt (div_pos (mul_pos hd.a_pos (pow_pos (lt_min hd.baseInj.pos one_pos) _)) hD)
  rw [show Real.exp (hd.C * hd.dist k x y) *
        (hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) / D *
          Real.exp (-hd.C * hd.dist k y (X.obj k).basepoint))
      = hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) / D *
          Real.exp (hd.C * hd.dist k x y + -hd.C * hd.dist k y (X.obj k).basepoint) from by
        rw [Real.exp_add]; ring]
  apply mul_le_mul_of_nonneg_left _ hP
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left (hre.distO_sub_le k x y) hd.C_nonneg]

/-- Net separation in the supplied distance: under `RealizesEdist`, distinct centers
of a pairwise-disjoint net satisfy `λ[d(x,O)] ≤ dist x y`.  This is the
`dist`-separation consumed by A0' (`VolumeComparisonInput.ballMult`). -/
theorem lambdaNet_dist_separated (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (k : Nat) (hD : 0 < D) (hre : hd.RealizesEdist) {S : Set ((X.obj k).M)}
    (hS : S.PairwiseDisjoint (hd.lambdaBall D k))
    {x y : (X.obj k).M} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    hd.lambda D (hd.dist k x (X.obj k).basepoint) ≤ hd.dist k x y := by
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  have hsep := hd.lambdaNet_separated D k hD hS hx hy hxy
  exact (ENNReal.ofReal_le_ofReal_iff (hre.dist_nonneg k x y)).mp
    (le_of_le_of_eq hsep (hre.edist_eq k x y))

/-- MSM135 `lbl383` item 5 / A10 multiplicity bound: among the centers of a
pairwise-disjoint net lying in `B(O,R)`, at most `Imult` can be within `4·λ[R]` of
any fixed point `z`.  The net is uniformly `λ[R]`-separated there (`λ` is antitone),
so this is the A0' Bishop--Gromov bound `VolumeComparisonInput.ballMult`. -/
theorem net_multiplicity (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat)
    (hD : 0 < D) (hre : hd.RealizesEdist)
    (vc : VolumeComparisonInput (I := I) X) (hvc : vc.dist = hd.dist) (R : Real)
    {S : Set ((X.obj k).M)} (hS : S.PairwiseDisjoint (hd.lambdaBall D k))
    (hSR : ∀ x ∈ S, hd.dist k x (X.obj k).basepoint ≤ R)
    (z : (X.obj k).M) (J : Finset ((X.obj k).M)) (hJS : ↑J ⊆ S)
    (hJz : ∀ x ∈ J, hd.dist k x z ≤ 4 * hd.lambda D R) :
    J.card ≤ vc.Imult := by
  classical
  have hr : 0 < hd.lambda D R := hd.lambda_pos hD R
  have hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → hd.lambda D R ≤ hd.dist k i j := by
    intro i hi j hj hij
    have hiS : i ∈ S := hJS (Finset.mem_coe.mpr hi)
    have hjS : j ∈ S := hJS (Finset.mem_coe.mpr hj)
    calc hd.lambda D R
        ≤ hd.lambda D (hd.dist k i (X.obj k).basepoint) :=
          hd.lambda_antitone hD (hSR i hiS)
      _ ≤ hd.dist k i j :=
          hd.lambdaNet_dist_separated D k hD hre hS hiS hjS hij
  have hmul := vc.ballMult k
    (centers := fun i : {x // x ∈ J} => (i : (X.obj k).M)) (r := hd.lambda D R) hr
    (fun i j hij => by
      rw [hvc]; exact hsep i i.2 j j.2 (fun h => hij (Subtype.ext h)))
    z Finset.univ
    (fun j _ => by rw [hvc]; exact hJz j j.2)
  rwa [Finset.card_univ, Fintype.card_coe] at hmul

/-- The achievable metric core of MSM135 `lbl383` (good covering) on the Zorn λ-net:
a maximal λ-separated net whose λ-balls are pairwise disjoint (item 2), whose doubled
balls cover (item 4, `lbl387`), and which is λ-separated (the packing property).  The
bounded multiplicity (item 5) is `net_multiplicity`.  The geodesic convexity (item 3)
and the 5 nested radii (`lbl391`) of the full statement are Step B refinements that
remain honest geometric inputs (they need §5 / `exp`). -/
structure GoodCovering (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat)
    (hD : 0 < D) where
  centers : Set ((X.obj k).M)
  disjoint : centers.PairwiseDisjoint (hd.lambdaBall D k)
  maximal : ∀ T : Set ((X.obj k).M),
    centers ⊆ T → T.PairwiseDisjoint (hd.lambdaBall D k) → T ⊆ centers
  cover : ∀ z : (X.obj k).M, ∃ x ∈ centers,
    (letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
     edist z x < ENNReal.ofReal (hd.lambda D (hd.dist k z (X.obj k).basepoint)) +
       ENNReal.ofReal (hd.lambda D (hd.dist k x (X.obj k).basepoint)))
  separated : ∀ {x y : (X.obj k).M}, x ∈ centers → y ∈ centers → x ≠ y →
    (letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
     ENNReal.ofReal (hd.lambda D (hd.dist k x (X.obj k).basepoint)) ≤ edist x y)

/-- MSM135 `lbl383` (achievable metric core): a good λ-covering exists for every term
of the sequence.  Assembled from `exists_lambdaNet`, `lambdaNet_cover`, and
`lambdaNet_separated`. -/
theorem exists_goodCovering (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat)
    (hD : 0 < D) : Nonempty (hd.GoodCovering D k hD) := by
  obtain ⟨S, hSdisj, hSmax⟩ := hd.exists_lambdaNet D k
  exact ⟨{ centers := S
           disjoint := hSdisj
           maximal := hSmax
           cover := fun z => hd.lambdaNet_cover D k hD hSdisj hSmax z
           separated := fun hx hy hxy => hd.lambdaNet_separated D k hD hSdisj hx hy hxy }⟩

/-- A scaled `λ`-ball `B(x, c·λ[d(x,O)])`, the family underlying the MSM135 `lbl391`
nested radii (`B̃ = c·=1/2`, `B̂ = c=4`, `B = c=5`, `B̄ = c=45e^{10cC}`,
`B⃗ = c=205e^{20cC}`). -/
def lambdaBallC (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat) (c : Real)
    (x : (X.obj k).M) : Set ((X.obj k).M) :=
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  Metric.eball x (ENNReal.ofReal (c * hd.lambda D (hd.dist k x (X.obj k).basepoint)))

/-- A `c·λ`-ball with `c ≤ 1` is contained in the `λ`-ball (monotonicity in radius). -/
theorem lambdaBallC_subset (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat)
    (hD : 0 < D) {c : Real} (hc : c ≤ 1) (x : (X.obj k).M) :
    hd.lambdaBallC D k c x ⊆ hd.lambdaBall D k x := by
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  intro w hw
  exact lt_of_lt_of_le hw (ENNReal.ofReal_le_ofReal (by
    nlinarith [hd.lambda_pos hD (hd.dist k x (X.obj k).basepoint)]))

/-- MSM135 `lbl391` "disjointness of smaller balls": the smaller balls `B(x, c·λ)`
with `c ≤ 1` (in particular `B̃ = B(x, λ/2)`) of a maximal net are pairwise disjoint,
since the net is already a packing of `λ`-balls and smaller balls are contained in them. -/
theorem lambdaBallC_pairwiseDisjoint (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (k : Nat) (hD : 0 < D) {c : Real} (hc : c ≤ 1) {S : Set ((X.obj k).M)}
    (hS : S.PairwiseDisjoint (hd.lambdaBall D k)) :
    S.PairwiseDisjoint (hd.lambdaBallC D k c) :=
  hS.mono (fun x => hd.lambdaBallC_subset D k hD hc x)

end InjRadiusDecayInput

end HCGCompactness
end DifferentialGeometry
