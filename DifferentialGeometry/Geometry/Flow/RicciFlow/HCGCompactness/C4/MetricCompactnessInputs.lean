import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCovering
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringSeq
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.VolumeComparisonBridge

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Theorem 3.9 — the conditional endpoint (`MetricCompactnessInputs`)

**Endpoint ruling (2026-07-05, user).**  The unconditional `metricCompactness`
(`HCGCompactness/MetricCompactness.lean`) cannot be discharged by the Chapter 4
construction alone: the construction consumes book-external theorems (the honest
inputs below) that are *not* among its three hypotheses, and the project has no
volume-form/comparison infrastructure to prove them natively.  The Chapter 4
working target is therefore this **conditional** endpoint: the same conclusion,
with the externally cited theorems bundled as an explicit input structure.  The
unconditional `metricCompactness` keeps its single `sorry`, now documented as
`= MetricCompactnessInputs.metricCompactness + the cited external theorems`.

## The bundle, field by field (mathematical audit 2026-07-05)

Sequence-level external inputs, each TRUE under the Theorem 3.9 hypotheses
(complete + `|∇^ℓ Rm| ≤ C_ℓ` + `inj(O_k) ≥ ρ`) by the book's citations:

* `decay` — Cheeger–Gromov–Taylor injectivity-radius decay (`lbl384`):
  `inj(x) ≥ a·min{ρ,1}^n·e^{−C·d(x,O)}`, constants `a(n,C₀), C(n,C₀)`.  The Lean
  field matches the book form exactly.
* `pack` — Bishop–Gromov total packing count `A(r)` (`lbl387`): per-radius, no
  uniformity trap.
* `volume` — Bishop-Gromov intersection multiplicity, capped at containing
  scale `m * r ≤ r0` (the joint cap is mathematically necessary; see the
  structure docstring), with `stepA_cap_le` recording the producer's choice
  that `r0` dominates the largest Step A ratio times `λ[0]`.
* `realizes` — the supplied distance realizes the Riemannian emetric
  (plumbing; discharged at instantiation from the Hopf–Rinow realization).
* `normalBounds` — normal-coordinate metric `C^p` bounds (`lbl395`, [H6]
  Cor 4.12): per-center radius, `k`- and center-uniform constants (uniformity is
  genuine: the Jacobi-field ODE analysis depends only on the curvature bounds).
* `expInvDeriv` — `exp⁻¹`-transition derivative bounds below the comparison
  scale `r₁` (`lbl418`), domain-capped to the book's `r₁ ≤ min{inj/4, c/√C₀}`
  regime.

## Deliberately NOT in the bundle (derived at assembly, or bundle-v2)

* **Construction-stage scale inputs** (`Item3RadiusInput`, `Item3GpScaleInput`,
  `SigmaScaleField`, and the per-configuration `CmHessianInput` /
  `StrictDistInput`): these are parameterized by Step A's constructed nets and
  Step C's configurations, so they cannot appear at sequence level.  Each is a
  "`D` large enough" consequence of `normalBounds` + `decay` (uniform positive
  `C²`-radius at bounded distance ⇒ choose `D` so `4λ[0]` sits below it); the
  D5 assembly must discharge them from the bundle, with one uniformity lemma
  per input as the assembly bricks.
* **`IsometryDerivBounds`** (`lbl375`, [H6] §5): the isometry-derivative
  polynomial recursion is per-map-sequence; its bundle-v2 field shape is pinned
  by the B-loc bridge brick (see `CHAPTER4_PLAN.md`), not yet stated here.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter
open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

/-- The bundled Chapter 4 book-external inputs for MSM135 Theorem 3.9.

Every field is a theorem the book cites externally (Cheeger–Gromov–Taylor,
Bishop–Gromov, [H6] Cor 4.12 / `lbl418`) or the compatibility of the producer's
scale choices; none is provable in-tree today (no Riemannian volume layer).
See the module docstring for the per-field mathematical audit. -/
structure MetricCompactnessInputs
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  /-- A0 (`lbl384`): Cheeger–Gromov–Taylor injectivity-radius decay. -/
  decay : InjRadiusDecayInput (I := I) X
  /-- The good-covering scale divisor (`λ = μ/D`); the assembly chooses it
  large against `normalBounds`' uniform radius. -/
  D : Real
  hD : 0 < D
  /-- `lbl387`: Bishop–Gromov total packing count `A(r)`. -/
  pack : decay.PackingBound D
  /-- A0': Bishop-Gromov intersection multiplicity, capped at `m * r ≤ r0`. -/
  volume : VolumeComparisonInput (I := I) X
  /-- The two Bishop–Gromov inputs quantify over the same supplied distance. -/
  dist_eq : volume.dist = decay.dist
  /-- Producer compatibility: the multiplicity cap dominates the largest Step A
  ratio times the largest packing scale `λ[0]`. -/
  stepA_cap_le :
    max 4 (50 * Real.exp (decay.C * (20 * decay.lambda D 0))) *
      decay.lambda D 0 <= volume.r0
  /-- The supplied distance realizes the Riemannian emetric. -/
  realizes : decay.RealizesEdist
  /-- `lbl395` ([H6] Cor 4.12): normal-coordinate metric `C^p` bounds. -/
  normalBounds : NormalCoordMetricBoundInput (I := I) X
  /-- S6 (`lbl418`): `exp⁻¹`-transition derivative bounds below scale `r₁`. -/
  expInvDeriv : ExpInverseDerivBoundInput (I := I) X

namespace MetricCompactnessInputs

/-- Build the conditional compactness input bundle from an explicit uniform
local-volume packing producer.

This keeps the public `MetricCompactnessInputs.volume` field as the Step A
consumer shape `VolumeComparisonInput`, while allowing callers to supply the
more precise uniform local-volume data checked by `UniformBallPack.toVCInput`. -/
def ofUniformVolume
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (decay : InjRadiusDecayInput (I := I) X)
    (D : Real) (hD : 0 < D)
    (pack : decay.PackingBound D)
    (vol : UniformBallPack (I := I) X)
    (dist_eq : vol.dist = decay.dist)
    (stepA_cap_le :
      max 4 (50 * Real.exp (decay.C * (20 * decay.lambda D 0))) *
        decay.lambda D 0 ≤ vol.r0)
    (realizes : decay.RealizesEdist)
    (normalBounds : NormalCoordMetricBoundInput (I := I) X)
    (expInvDeriv : ExpInverseDerivBoundInput (I := I) X) :
    MetricCompactnessInputs (I := I) X where
  decay := decay
  D := D
  hD := hD
  pack := pack
  volume := vol.toVCInput
  dist_eq := by
    change vol.dist = decay.dist
    exact dist_eq
  stepA_cap_le := by
    change max 4 (50 * Real.exp (decay.C * (20 * decay.lambda D 0))) *
      decay.lambda D 0 ≤ vol.r0
    exact stepA_cap_le
  realizes := realizes
  normalBounds := normalBounds
  expInvDeriv := expInvDeriv

/-- Reindex the conditional compactness input bundle along a subsequence. -/
def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) (f : Nat -> Nat) :
    MetricCompactnessInputs (I := I) (X.subseq f) where
  decay := inp.decay.subseq f
  D := inp.D
  hD := inp.hD
  pack := inp.pack.subseq f
  volume := inp.volume.subseq f
  dist_eq := by
    funext k x y
    change inp.volume.dist (f k) x y = inp.decay.dist (f k) x y
    rw [inp.dist_eq]
  stepA_cap_le := by
    simpa [InjRadiusDecayInput.subseq, InjRadiusDecayInput.lambda, InjRadiusDecayInput.mu]
      using inp.stepA_cap_le
  realizes := inp.realizes.subseq f
  normalBounds := inp.normalBounds.subseq f
  expInvDeriv := inp.expInvDeriv.subseq f

/-- The Step A `m = 4` multiplicity cap extracted from the bundled maximum cap.

This is the exact cap needed by `net_multiplicity` at scale `lambda[0]`. -/
theorem cap_four
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) :
    (4 : Real) * inp.decay.lambda inp.D 0 <= inp.volume.r0 := by
  have hlam : 0 <= inp.decay.lambda inp.D 0 :=
    (inp.decay.lambda_pos inp.hD 0).le
  have hle :
      (4 : Real) <=
        max 4 (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) :=
    le_max_left _ _
  exact (mul_le_mul_of_nonneg_right hle hlam).trans inp.stepA_cap_le

/-- The Step A `m = 4` multiplicity cap at any nonnegative radius argument.

This combines `cap_four` with monotonicity of `lambda`; it is the form used
when a net radius is known to be bounded by the base scale `lambda[0]`. -/
theorem cap_four_of_nonneg
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) {R : Real} (hR : 0 <= R) :
    (4 : Real) * inp.decay.lambda inp.D R <= inp.volume.r0 := by
  have hlam : inp.decay.lambda inp.D R <= inp.decay.lambda inp.D 0 :=
    inp.decay.lambda_antitone inp.hD hR
  have hmul :
      (4 : Real) * inp.decay.lambda inp.D R <=
        (4 : Real) * inp.decay.lambda inp.D 0 :=
    mul_le_mul_of_nonneg_left hlam (by norm_num)
  exact hmul.trans inp.cap_four

/-- The Step A item-5 ratio cap extracted from the bundled maximum cap.

This is the exact cap hypothesis required by `NetLimitData.inter_count`. -/
theorem cap_inter
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) :
    (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) *
        inp.decay.lambda inp.D 0 <= inp.volume.r0 := by
  have hlam : 0 <= inp.decay.lambda inp.D 0 :=
    (inp.decay.lambda_pos inp.hD 0).le
  have hle :
      50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)) <=
        max 4 (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) :=
    le_max_right _ _
  exact (mul_le_mul_of_nonneg_right hle hlam).trans inp.stepA_cap_le

/-- Bundle-level wrapper for Step A's net multiplicity estimate. -/
theorem net_mult
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) (k : Nat) {R : Real}
    (hR : 0 <= R) {S : Set ((X.obj k).M)}
    (hS : S.PairwiseDisjoint (inp.decay.lambdaBall inp.D k))
    (hSR : ∀ x ∈ S, inp.decay.dist k x (X.obj k).basepoint <= R)
    (z : (X.obj k).M) (J : Finset ((X.obj k).M)) (hJS : ↑J ⊆ S)
    (hJz : ∀ x ∈ J, inp.decay.dist k x z <= 4 * inp.decay.lambda inp.D R) :
    J.card <= inp.volume.Imult 4 := by
  exact InjRadiusDecayInput.net_multiplicity
    inp.decay inp.D k inp.hD inp.realizes inp.volume inp.dist_eq R
    (inp.cap_four_of_nonneg hR) hS hSR z J hJS hJz

/-- Bundle-level wrapper for the Step A item-5 intersection count. -/
theorem inter_count
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (α : Nat) :
    ∀ᶠ k in atTop,
      ∀ xα : (X.obj (L.φ k)).M,
        seqCenter inp.decay inp.D P (L.φ k) α = some xα →
      ∀ J : Finset Nat,
        (∀ β ∈ J, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) →
        J.card <=
          inp.volume.Imult
            (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) := by
  exact NetLimitData.inter_count inp.decay inp.hD P L inp.realizes inp.pack
    inp.volume inp.dist_eq inp.cap_inter α

/-- Bundle-level wrapper for the Step A diagonal net datum. -/
theorem exists_net_data
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    Nonempty (NetLimitData inp.decay inp.D P) :=
  exists_netLimitData inp.decay inp.hD P

/-- Bundle-level wrapper for the stabilized Step A net datum. -/
theorem exists_stable_net
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    ∃ L : NetLimitData inp.decay inp.D P,
      ∀ α β : Nat,
        (∀ᶠ k in atTop, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop, ¬ BInter inp.decay inp.D P L.lamInf α β (L.φ k)) :=
  exists_stableNetData inp.decay inp.hD P

/-- Bundle-level Step A net package: a stable diagonal net datum together with
the item-5 intersection bound supplied by the bundled volume input. -/
theorem exists_stepA_net
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    ∃ L : NetLimitData inp.decay inp.D P,
      (∀ α β : Nat,
        (∀ᶠ k in atTop, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop, ¬ BInter inp.decay inp.D P L.lamInf α β (L.φ k))) ∧
      (∀ α : Nat,
        ∀ᶠ k in atTop,
          ∀ xα : (X.obj (L.φ k)).M,
            seqCenter inp.decay inp.D P (L.φ k) α = some xα →
          ∀ J : Finset Nat,
            (∀ β ∈ J, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) →
            J.card <=
              inp.volume.Imult
                (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)))) := by
  obtain ⟨L, hstable⟩ := inp.exists_stable_net P
  exact ⟨L, hstable, fun α => inp.inter_count P L α⟩

/-- The per-member proper metric realization supplied by the endpoint's
completeness and connectedness hypotheses. -/
noncomputable def properMetrics
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (_inp : MetricCompactnessInputs (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∀ k : Nat, ProperMetricOn (I := I) (X.obj k) :=
  fun k => properMetricOn (I := I) (X.obj k) (hcomplete.complete k) (hconn k)

/-- Endpoint-hypothesis wrapper for the Step A net package. -/
theorem stepA_net
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∃ L : NetLimitData inp.decay inp.D (inp.properMetrics hcomplete hconn),
      (∀ α β : Nat,
        (∀ᶠ k in atTop,
          BInter inp.decay inp.D (inp.properMetrics hcomplete hconn)
            L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop,
          ¬ BInter inp.decay inp.D (inp.properMetrics hcomplete hconn)
            L.lamInf α β (L.φ k))) ∧
      (∀ α : Nat,
        ∀ᶠ k in atTop,
          ∀ xα : (X.obj (L.φ k)).M,
            seqCenter inp.decay inp.D (inp.properMetrics hcomplete hconn)
              (L.φ k) α = some xα →
          ∀ J : Finset Nat,
            (∀ β ∈ J,
              BInter inp.decay inp.D (inp.properMetrics hcomplete hconn)
                L.lamInf α β (L.φ k)) →
            J.card <=
              inp.volume.Imult
                (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)))) :=
  inp.exists_stepA_net (inp.properMetrics hcomplete hconn)

/-- Endpoint-hypothesis wrapper for the Step A net package after reindexing by
a subsequence. -/
theorem stepA_net_subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (f : Nat -> Nat) :
    ∃ L : NetLimitData (inp.subseq f).decay (inp.subseq f).D
        ((inp.subseq f).properMetrics (hcomplete.subseq f)
          (fun k => by
            simpa [PointedRiemannianSeq.subseq] using hconn (f k))),
      (∀ α β : Nat,
        (∀ᶠ k in atTop,
          BInter (inp.subseq f).decay (inp.subseq f).D
            ((inp.subseq f).properMetrics (hcomplete.subseq f)
              (fun k => by
                simpa [PointedRiemannianSeq.subseq] using hconn (f k)))
            L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop,
          ¬ BInter (inp.subseq f).decay (inp.subseq f).D
            ((inp.subseq f).properMetrics (hcomplete.subseq f)
              (fun k => by
                simpa [PointedRiemannianSeq.subseq] using hconn (f k)))
            L.lamInf α β (L.φ k))) ∧
      (∀ α : Nat,
        ∀ᶠ k in atTop,
          ∀ xα : ((X.subseq f).obj (L.φ k)).M,
            seqCenter (inp.subseq f).decay (inp.subseq f).D
              ((inp.subseq f).properMetrics (hcomplete.subseq f)
                (fun k => by
                  simpa [PointedRiemannianSeq.subseq] using hconn (f k)))
              (L.φ k) α = some xα →
          ∀ J : Finset Nat,
            (∀ β ∈ J,
              BInter (inp.subseq f).decay (inp.subseq f).D
                ((inp.subseq f).properMetrics (hcomplete.subseq f)
                  (fun k => by
                    simpa [PointedRiemannianSeq.subseq] using hconn (f k)))
                L.lamInf α β (L.φ k)) →
            J.card <=
              (inp.subseq f).volume.Imult
                (50 * Real.exp
                  ((inp.subseq f).decay.C *
                    (20 * (inp.subseq f).decay.lambda (inp.subseq f).D 0)))) := by
  exact (inp.subseq f).stepA_net (hcomplete.subseq f)
    (fun k => by
      simpa [PointedRiemannianSeq.subseq] using hconn (f k))

/-- **MSM135 Theorem 3.9, conditional form — the Chapter 4 working target.**
Compactness for complete pointed Riemannian manifolds with uniformly bounded
geometry and a basepoint injectivity-radius lower bound, given the bundled
book-external inputs.  The `sorry` is the Steps A→D assembly (good coverings →
local metrics/transition maps → center-of-mass averaging → direct limit); no
external mathematics hides in it beyond the bundle.

Connectedness is required by the Hopf–Rinow proper-realization step
(`properMetricOn`): on a disconnected member the Riemannian emetric is `⊤`
across components and no realizing proper distance exists.  (The book's
manifolds are connected by convention.) -/
def metricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (_inp : MetricCompactnessInputs (I := I) X)
    (_hcomplete : SeqMetricComplete (I := I) X)
    (_hgeom : SeqBoundedGeometry (I := I) X)
    (_hinj : BaseInjBound (I := I) X)
    (_hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    MetricCompactnessConclusion (I := I) X := by
  sorry

end MetricCompactnessInputs

end HCGCompactness
end DifferentialGeometry
