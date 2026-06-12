import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.NablaReactionAllK
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeatFrameInvariant
import DifferentialGeometry.Tensor.RSTensor.ProductNablaLeibniz

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# `StarSum2` — the inductive class of `∇ᵃRm ∗ ∇ᵇRm` star sums

This file defines the BBS "star-sum" class `StarSum2 S t k T`, the predicate that a
rank-`(4+k)` field `T` is a finite sum of metric contractions of `∇ᵃRm ⊗ ∇ᵇRm`.
This is the formalization of Hamilton's schematic `T = Σ ∇ᵃRm ∗ ∇ᵇRm` notation
(Hamilton / Morgan–Tian "Lemma 6.1"-style curvature algebra), specialized to the
**two-factor** star products that appear in the iterated curvature evolution
`E_k = (∂ₜ − Δ)∇ᵏRm`.

## The `base` term

Every `∇ᵃRm ∗ ∇ᵇRm` landing in rank `4 + k` is, up to a slot permutation `σ`, a
**double metric trace** of the tensor product `∇ᵃRm ⊗ ∇ᵇRm`:

`starBaseField S t k a b σ
  = metricTrace₁₂ (metricTrace₁₂ (domDomCongr σ (∇ᵃRm ⊗ ∇ᵇRm)))`,

mirroring the concrete `knRicT` / `knField` constructions in
`Evolution/UhlenbeckBaseProducer.lean`.  The level `k` is **decoupled** from `a + b`
in the signature: the output rank is pinned by `σ`'s codomain `(((4+k)+2)+2)`, and
the cardinality of `σ` forces `a + b = k` semantically.  This decoupling is what
lets `.nabla` send `base k a b` to `base (k+1) (a+1) b + base (k+1) a (b+1)` without
any `(a+1)+b = (a+b)+1` dependent-rank casts.

## Closure properties (the BBS bricks)

* **`.add` / `.zero` / `.smul`** — the constructors.
* **`.nabla`** (this file) — `T ∈ StarSum2 k ⟹ ∇T ∈ StarSum2 (k+1)`: `∇` commutes
  through both traces (`nablaRealizes_metricTraceFirstTwo`, the keystone realizer in
  `MetricTrace/NablaTraceGen.lean`) and through `domDomCongr`
  (`totalNabla0SRealizes_domDomCongr`); the product Leibniz rule
  (`nabla0S_product_realizes`) then splits `∇(∇ᵃRm ⊗ ∇ᵇRm)` into the two daughter
  `base` terms.
* **`.bound`** (next) — `T ∈ StarSum2 k ⟹ ∃C, ‖T‖ ≤ C·Σⱼ√wⱼ√w_{k−j}` by
  Cauchy–Schwarz on the traces.

## The Lean instance wall (resolved)

Generic-rank `0` / `+` / `•` on `Tensor0SField (4+k)` trigger a `whnf`-timeout in
instance synthesis in this heavy import context; the fix is the codebase-standard
`set_option backward.isDefEq.respectTransparency false in` on each declaration.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}

/-- Metric compatibility of the solution's Levi-Civita connection at time `t`
(local copy of the `UhlenbeckBaseProducer.metricCompatSol` handle, which lives in a
sibling import branch). -/
private theorem stMetricCompat
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I)
      (S.family.connection t) (S.family.metric t) := by
  simpa [SolutionFamily.connection, SolutionOn.family_metric] using
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) (S.base.metric t)

set_option backward.isDefEq.respectTransparency false in
/-- **The star generator** `∇ᵃRm ⊗ ∇ᵇRm ⊗ g^{⊗r}`: the two iterated-curvature factors
with `r` metric factors appended one at a time on the right.  This appending order keeps
every rank step definitional (`(R + 2r) + 2 ≡ R + 2(r+1)`), avoiding the cast in
`metricPow`'s successor.  The metric factors are required: the dim-3 reaction
(`B# = KN(C, −|R|², δ)`, `C = 2R² − (3S/2)R + (S²/2−|R|²)δ`) contains terms with free
`g`-slots, which no pure `∇ᵃRm ⊗ ∇ᵇRm` contraction can produce. -/
def starProd (S : SolutionOn (I := I) (M := M) D) (t : Real) (a b : ℕ) :
    (r : ℕ) → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (((4 + a) + (4 + b)) + 2 * r)
  | 0 => MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 4 + a) (q := 4 + b)
      (nablaKRm04Field (I := I) S t a) (nablaKRm04Field (I := I) S t b)
  | (r + 1) => MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (n := (∞ : WithTop ℕ∞))
      (s := ((4 + a) + (4 + b)) + 2 * r) (q := 2)
      (starProd S t a b r) (metricTensorField (I := I) (S.family.metric t))

set_option backward.isDefEq.respectTransparency false in
/-- The `τ`-fold first-two metric trace `Field (s + 2τ) → Field s`. -/
def mtIter (g : SmoothRiemannianMetric I M) {s : ℕ} :
    (τ : ℕ) → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2 * τ) →
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) s
  | 0, A => A
  | (τ + 1), A => mtIter g τ
      (metricTraceFirstTwoField (I := I) (M := M) (s := s + 2 * τ) g A)

set_option backward.isDefEq.respectTransparency false in
/-- The iterated trace is additive. -/
theorem mtIter_add (g : SmoothRiemannianMetric I M) {s : ℕ} (τ : ℕ) :
    ∀ A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2 * τ),
      mtIter (I := I) g τ (A + B) = mtIter (I := I) g τ A + mtIter (I := I) g τ B := by
  induction τ with
  | zero => intro A B; rfl
  | succ τ ih =>
      intro A B
      change mtIter (I := I) g τ
          (metricTraceFirstTwoField (I := I) (M := M) (s := s + 2 * τ) g (A + B)) = _
      rw [metricTraceFirstTwoField_add, ih]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The generating star term** `∇ᵃRm ∗ ∇ᵇRm ∗ g^{⊗r}` at level `k`: the `(2+r)`-fold
metric trace of the slot-permuted generator `domDomCongr σ (starProd a b r)`.  The output
rank `4 + k` is pinned by `σ`'s codomain; `σ`'s existence forces `a + b = k`. -/
def starBaseField
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k a b r : ℕ)
    (σ : Fin (((4 + a) + (4 + b)) + 2 * r) ≃ Fin ((4 + k) + 2 * (2 + r))) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k) :=
  mtIter (I := I) (S.family.metric t) (2 + r)
    (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (∞ : WithTop ℕ∞) σ (starProd (I := I) S t a b r))

set_option backward.isDefEq.respectTransparency false in
/-- **The BBS star-sum class.**  `StarSum2 S t k T` holds when the rank-`(4+k)` field
`T` is a finite linear combination of `base` star terms `∇ᵃRm ∗ ∇ᵇRm`.

* `zero` / `add` / `smul`: the field operations generating finite linear combinations.
* `base k a b σ`: the generating two-factor star product `starBaseField S t k a b σ`
  (with `a + b = k` forced by `σ`'s cardinality).

This is the smallest class containing the two-factor star products and closed under
sums and scalar multiples — exactly enough to host the reaction `E_0 = Rm ∗ Rm`
(`base 0 0 0 σ` terms) and to be closed under `∇` (`StarSum2.nabla` below). -/
inductive StarSum2 (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    (k : ℕ) → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k) → Prop
  | zero (k : ℕ) :
      StarSum2 S t k
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (4 + k))
  | add {k : ℕ}
      {A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (4 + k)} :
      StarSum2 S t k A → StarSum2 S t k B → StarSum2 S t k (A + B)
  | smul {k : ℕ} (c : Real)
      {A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (4 + k)} :
      StarSum2 S t k A → StarSum2 S t k (c • A)
  | base (k a b r : ℕ)
      (σ : Fin (((4 + a) + (4 + b)) + 2 * r) ≃ Fin ((4 + k) + 2 * (2 + r))) :
      StarSum2 S t k (starBaseField (I := I) S t k a b r σ)

/-! ## The canonical `∇` operator and its linearity

`stNabla` is the canonical total covariant derivative `totalNabla0S` of the solution's
Levi-Civita connection, with the regularity certificate auto-supplied by
`totalNabla0S_reg` + `connSmoothInf`.  Its linearity follows from realizer uniqueness
(`totalNabla0SRealizes_unique`) against the `TotalNabla0SRealizes.add` / `.smul`
closures. -/

set_option backward.isDefEq.respectTransparency false in
/-- The canonical total covariant derivative of a rank-`(4+k)` field, for the
solution's connection at time `t`. -/
def stNabla (S : SolutionOn (I := I) (M := M) D) (t : Real) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + (k + 1)) :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (4 + k) (S.family.connection t) T
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      (4 + k) (S.family.connection t) (connSmoothInf (I := I) S t) T)

set_option backward.isDefEq.respectTransparency false in
/-- `stNabla` realizes the total covariant derivative. -/
theorem stNabla_realizes (S : SolutionOn (I := I) (M := M) D) (t : Real) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) (S.family.connection t) T (stNabla (I := I) S t T) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (4 + k) (S.family.connection t) T
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      (4 + k) (S.family.connection t) (connSmoothInf (I := I) S t) T)

set_option backward.isDefEq.respectTransparency false in
/-- `∇0 = 0` for the canonical operator. -/
theorem stNabla_zero (S : SolutionOn (I := I) (M := M) D) (t : Real) {k : ℕ} :
    stNabla (I := I) S t
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (4 + k))
      = 0 := by
  have hc := stNabla_realizes (I := I) S t
    (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k))
  have h2 := hc.smul (0 : Real)
  rw [smul_zero] at h2
  have h3 := totalNabla0SRealizes_unique (I := I) hc h2
  rw [h3, zero_smul]

set_option backward.isDefEq.respectTransparency false in
/-- `∇(A + B) = ∇A + ∇B` for the canonical operator. -/
theorem stNabla_add (S : SolutionOn (I := I) (M := M) D) (t : Real) {k : ℕ}
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)) :
    stNabla (I := I) S t (A + B) = stNabla (I := I) S t A + stNabla (I := I) S t B :=
  totalNabla0SRealizes_unique (I := I) (stNabla_realizes (I := I) S t (A + B))
    ((stNabla_realizes (I := I) S t A).add (stNabla_realizes (I := I) S t B))

set_option backward.isDefEq.respectTransparency false in
/-- `∇(c • A) = c • ∇A` for the canonical operator. -/
theorem stNabla_smul (S : SolutionOn (I := I) (M := M) D) (t : Real) {k : ℕ} (c : Real)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)) :
    stNabla (I := I) S t (c • A) = c • stNabla (I := I) S t A :=
  totalNabla0SRealizes_unique (I := I) (stNabla_realizes (I := I) S t (c • A))
    ((stNabla_realizes (I := I) S t A).smul c)

/-! ## `∇` of a base term

The keystone chain: the product Leibniz realizer (`nabla0S_product_realizes`), pushed
through `domDomCongr σ` (`totalNabla0SRealizes_domDomCongr`) and through both metric
traces (`nablaRealizes_metricTraceFirstTwo`, twice), realizes `∇(starBaseField)`.  By
realizer uniqueness the canonical `stNabla` equals that chain, and distributing the
sums/reindexings lands exactly on two daughter base terms. -/

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The generator Leibniz rule**: `∇(∇ᵃRm ⊗ ∇ᵇRm ⊗ g^{⊗r})` is realized by the two
daughter generators (the metric factors are parallel, so their Leibniz branches vanish). -/
theorem starProdNabla
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (a b : ℕ) :
    ∀ r : ℕ,
      ∃ (e₁ : Fin (((4 + (a + 1)) + (4 + b)) + 2 * r)
            ≃ Fin ((((4 + a) + (4 + b)) + 2 * r) + 1))
        (e₂ : Fin (((4 + a) + (4 + (b + 1))) + 2 * r)
            ≃ Fin ((((4 + a) + (4 + b)) + 2 * r) + 1)),
        TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (((4 + a) + (4 + b)) + 2 * r) (S.family.connection t)
          (starProd (I := I) S t a b r)
          (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞) e₁
              (starProd (I := I) S t (a + 1) b r)
            + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞) e₂
              (starProd (I := I) S t a (b + 1) r)) := by
  intro r
  induction r with
  | zero =>
      exact ⟨leibnizLeftEquiv (4 + a) (4 + b), leibnizRightEquiv (4 + a) (4 + b),
        nabla0S_product_realizes (I := I) (M := M) (S.family.connection t)
          (nablaKRm04Field (I := I) S t a) (nablaKRm04Field (I := I) S t b)
          (nablaKRm04Field (I := I) S t (a + 1)) (nablaKRm04Field (I := I) S t (b + 1))
          (nablaKRm04Field_realizes (I := I) S t a)
          (nablaKRm04Field_realizes (I := I) S t b)⟩
  | succ r ih =>
      obtain ⟨e₁, e₂, hr⟩ := ih
      have h0 := zero_realizes_metric (I := I) (S.family.connection t)
        (S.family.metric t) (stMetricCompat (I := I) S t)
      have hp := nabla0S_product_realizes (I := I) (M := M) (S.family.connection t)
        (starProd (I := I) S t a b r)
        (metricTensorField (I := I) (S.family.metric t)) _ 0 hr h0
      rw [MultilinearSection.product_zero, MultilinearSection.domDomCongr_zero, add_zero,
        MultilinearSection.product_add_left, MultilinearSection.product_domDomCongr_left,
        MultilinearSection.product_domDomCongr_left, MultilinearSection.domDomCongr_add,
        MultilinearSection.domDomCongr_trans, MultilinearSection.domDomCongr_trans] at hp
      exact ⟨_, _, hp⟩

set_option backward.isDefEq.respectTransparency false in
/-- **The iterated-trace keystone**: a realizer of `∇A` pushes through `τ` metric traces,
up to a slot reindexing `ρ` of the realizer. -/
theorem stNablaMtIter
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    {s : ℕ} (τ : ℕ) :
    ∀ (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 2 * τ))
      (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) ((s + 2 * τ) + 1)),
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2 * τ) cov A nablaA →
      ∃ ρ : Fin ((s + 2 * τ) + 1) ≃ Fin ((s + 1) + 2 * τ),
        TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov (mtIter (I := I) g τ A)
          (mtIter (I := I) g τ
            (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞) ρ nablaA)) := by
  induction τ with
  | zero =>
      intro A nablaA h
      refine ⟨Equiv.refl _, ?_⟩
      rw [MultilinearSection.domDomCongr_refl]
      exact h
  | succ τ ih =>
      intro A nablaA h
      have h1 := nablaRealizes_metricTraceFirstTwo (I := I) (M := M) (s := s + 2 * τ)
        cov hcov1 g hmc A nablaA h
      obtain ⟨ρ', h2⟩ := ih
        (metricTraceFirstTwoField (I := I) (M := M) (s := s + 2 * τ) g A)
        (metricTraceFirstTwoField (I := I) (M := M) (s := (s + 2 * τ) + 1) g
          (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞)
            (traceNablaShuffle (s + 2 * τ)) nablaA)) h1
      rw [← metricTraceFirstTwoField_domDomCongr (I := I) (M := M) g ρ'
            (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞)
              (traceNablaShuffle (s + 2 * τ)) nablaA),
          MultilinearSection.domDomCongr_trans] at h2
      exact ⟨_, h2⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **`∇(∇ᵃRm ∗ ∇ᵇRm ∗ g^{⊗r}) = ∇^{a+1}Rm ∗ ∇ᵇRm ∗ g^{⊗r} + ∇ᵃRm ∗ ∇^{b+1}Rm ∗ g^{⊗r}`**:
the canonical derivative of a base star term is the sum of the two daughter base star
terms at level `k+1`. -/
theorem stNabla_starBase
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection t) 1)
    (k a b r : ℕ)
    (σ : Fin (((4 + a) + (4 + b)) + 2 * r) ≃ Fin ((4 + k) + 2 * (2 + r))) :
    ∃ (σL : Fin (((4 + (a + 1)) + (4 + b)) + 2 * r) ≃ Fin ((4 + (k + 1)) + 2 * (2 + r)))
      (σR : Fin (((4 + a) + (4 + (b + 1))) + 2 * r) ≃ Fin ((4 + (k + 1)) + 2 * (2 + r))),
      stNabla (I := I) S t (starBaseField (I := I) S t k a b r σ)
        = starBaseField (I := I) S t (k + 1) (a + 1) b r σL
          + starBaseField (I := I) S t (k + 1) a (b + 1) r σR := by
  classical
  obtain ⟨e₁, e₂, hP⟩ := starProdNabla (I := I) S t a b r
  have h2 := totalNabla0SRealizes_domDomCongr (I := I) (S.family.connection t) σ _ _ hP
  obtain ⟨ρ, h3⟩ := stNablaMtIter (I := I) (S.family.metric t) (S.family.connection t)
    hcov1 (stMetricCompat (I := I) S t) (s := 4 + k) (2 + r) _ _ h2
  have heq := totalNabla0SRealizes_unique (I := I)
    (stNabla_realizes (I := I) S t (starBaseField (I := I) S t k a b r σ)) h3
  refine ⟨e₁.trans ((frontExtendEquiv σ).trans ρ),
    e₂.trans ((frontExtendEquiv σ).trans ρ), ?_⟩
  rw [heq]
  simp only [MultilinearSection.domDomCongr_add, MultilinearSection.domDomCongr_trans,
    Equiv.trans_assoc, mtIter_add, starBaseField]

set_option backward.isDefEq.respectTransparency false in
/-- **Brick 3: the star-sum class is closed under `∇`.**  The level steps `k ↦ k+1`. -/
theorem StarSum2.nabla
    {S : SolutionOn (I := I) (M := M) D} {t : Real}
    (hcov1 : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection t) 1)
    {k : ℕ}
    {T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)}
    (hT : StarSum2 (I := I) S t k T) :
    StarSum2 (I := I) S t (k + 1) (stNabla (I := I) S t T) := by
  induction hT with
  | zero =>
      rw [stNabla_zero]
      exact StarSum2.zero _
  | add hA hB ihA ihB =>
      rw [stNabla_add]
      exact StarSum2.add ihA ihB
  | smul c hA ih =>
      rw [stNabla_smul]
      exact StarSum2.smul c ih
  | base a b r σ =>
      obtain ⟨σL, σR, h⟩ := stNabla_starBase (I := I) S t hcov1 _ a b r σ
      rw [h]
      exact StarSum2.add (StarSum2.base _ (a + 1) b r σL)
        (StarSum2.base _ a (b + 1) r σR)

/-! ## Brick 2: the Cauchy–Schwarz star bound

Every `T ∈ StarSum2 S t k` is bounded, at any `g_t`-orthonormal basis, by
`C·Σⱼ √(wⱼ)·√(w_{k−j})` with `wⱼ = |∇ʲRm|²` (the orthonormal-component squared norm).
Induction on the derivation: `zero/add/smul` are constant bookkeeping; the `base` case
is the double-trace δ-collapse (each metric trace costs one `card` factor) followed by
the single-component Cauchy–Schwarz `abs_le_sqrt_compNormSqMulti` on the two product
factors, landing on the `j := a` term of the sum (`a + b = k` is forced by `σ`'s
cardinality). -/

set_option backward.isDefEq.respectTransparency false in
/-- The squared orthonormal-component norm `wⱼ = |∇ʲRm|²` of the `j`-th iterated
curvature derivative at `x`, in a tangent basis. -/
def stNormSq (S : SolutionOn (I := I) (M := M) D) (t : Real) (j : ℕ) (x : M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Real :=
  compNormSqMulti (fun m : Fin (4 + j) → Idx =>
    nablaKRm04Field (I := I) S t j x (fun p => basis (m p)))

/-- Kronecker-delta double-sum collapse: `Σᵢⱼ δᵢⱼ·Xᵢⱼ = Σᵢ Xᵢᵢ`. -/
private theorem sumIdentityDiag {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (X : Idx → Idx → Real) :
    (∑ i : Idx, ∑ j : Idx, identityInvMetric (Idx := Idx) i j * X i j)
      = ∑ i : Idx, X i i := by
  classical
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [identityInvMetric_apply_self, one_mul]
  · intro j _ hj
    rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne (fun h => hj h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- A trace input built from basis vectors is the basis composed with an index-level
tuple. -/
private theorem mtInputBasis {x : M} {Idx : Type*} {s' : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (r r' : Idx) (mm : Fin s' → Idx) :
    ∃ mIdx : Fin (s' + 2) → Idx,
      metricTraceInput (I := I) (basis r) (basis r') (fun p => basis (mm p))
        = fun q => basis (mIdx q) := by
  refine ⟨fun q => if h0 : (q : ℕ) = 0 then r else if h1 : (q : ℕ) = 1 then r'
    else mm ⟨(q : ℕ) - 2, by have := q.isLt; omega⟩, ?_⟩
  funext q
  simp only [metricTraceInput_apply]
  split_ifs <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Orthonormal trace bound**: if every basis-component of `X` is bounded by `c`,
every basis-component of its first-two metric trace is bounded by `card·c` (the
δ-collapsed trace is a single `card`-fold sum of components of `X`). -/
private theorem mtfOrthoBd {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M} {s' : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (X : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s' + 2))
    (c : Real)
    (hX : ∀ mm : Fin (s' + 2) → Idx, |X x (fun q => basis (mm q))| ≤ c)
    (mm : Fin s' → Idx) :
    |metricTraceFirstTwoField (I := I) (M := M) g X x (fun q => basis (mm q))| ≤
      (Fintype.card Idx : Real) * c := by
  classical
  have hinv := metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
      (identityInvMetric (Idx := Idx)) hinv (X x) (fun q => basis (mm q))]
  unfold metricTrace0S2InBasis
  rw [sumIdentityDiag (fun i j => (X x)
    (metricTraceInput (I := I) (basis i) (basis j) (fun q => basis (mm q))))]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [show (Fintype.card Idx : Real) * c = ∑ _i : Idx, c from by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨mIdx, hmt⟩ := mtInputBasis (I := I) basis i i mm
  rw [hmt]
  exact hX _

set_option backward.isDefEq.respectTransparency false in
/-- **Iterated orthonormal trace bound**: a componentwise bound `c` survives `τ` metric
traces at the cost of one `card` factor per trace. -/
private theorem mtIterOrthoBd {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    {s' : ℕ} (τ : ℕ) :
    ∀ (X : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s' + 2 * τ)) (c : Real),
      (∀ mm : Fin (s' + 2 * τ) → Idx, |X x (fun q => basis (mm q))| ≤ c) →
      ∀ mm : Fin s' → Idx,
        |mtIter (I := I) g τ X x (fun q => basis (mm q))| ≤
          (Fintype.card Idx : Real) ^ τ * c := by
  induction τ with
  | zero =>
      intro X c hX mm
      simpa using hX mm
  | succ τ ih =>
      intro X c hX mm
      have h1 : ∀ mm' : Fin ((s' + 2 * τ) + 2) → Idx,
          |X x (fun q => basis (mm' q))| ≤ c := fun mm' => hX mm'
      have h2 := ih (metricTraceFirstTwoField (I := I) (M := M) (s := s' + 2 * τ) g X)
        ((Fintype.card Idx : Real) * c)
        (fun mm' => mtfOrthoBd (I := I) g basis horth (s' := s' + 2 * τ) X c h1 mm') mm
      refine le_trans h2 (le_of_eq ?_)
      ring

set_option backward.isDefEq.respectTransparency false in
/-- **Componentwise Cauchy–Schwarz for the star generator**: every basis-component of
`∇ᵃRm ⊗ ∇ᵇRm ⊗ g^{⊗r}` is bounded by `√(wₐ)·√(w_b)` (metric components are `δ ≤ 1` at an
orthonormal basis). -/
private theorem starProdBd {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (a b : ℕ) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      (S.family.metric t).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0) :
    ∀ (r : ℕ) (mm : Fin ((((4 + a) + (4 + b)) + 2 * r)) → Idx),
      |starProd (I := I) S t a b r x (fun q => basis (mm q))| ≤
        Real.sqrt (stNormSq (I := I) S t a x basis) *
          Real.sqrt (stNormSq (I := I) S t b x basis) := by
  intro r
  induction r with
  | zero =>
      intro mm
      have hpf := Bundle.continuousMultilinearMap.product_fun_apply
        (nablaKRm04Field (I := I) S t a x) (nablaKRm04Field (I := I) S t b x)
        (fun q => basis (mm q))
      refine le_trans (le_of_eq (congrArg abs hpf)) ?_
      rw [abs_mul]
      refine mul_le_mul ?_ ?_ (abs_nonneg _) (Real.sqrt_nonneg _)
      · exact Real.abs_le_sqrt (sq_le_compNormSqMulti
          (fun m' : Fin (4 + a) → Idx =>
            nablaKRm04Field (I := I) S t a x (fun p => basis (m' p))) _)
      · exact Real.abs_le_sqrt (sq_le_compNormSqMulti
          (fun m' : Fin (4 + b) → Idx =>
            nablaKRm04Field (I := I) S t b x (fun p => basis (m' p))) _)
  | succ r ih =>
      intro mm
      have hpf := Bundle.continuousMultilinearMap.product_fun_apply
        (starProd (I := I) S t a b r x)
        (metricTensorField (I := I) (S.family.metric t) x)
        (fun q => basis (mm q))
      refine le_trans (le_of_eq (congrArg abs hpf)) ?_
      rw [abs_mul, metricTensorField_apply]
      refine le_trans (mul_le_mul (ih _) ?_ (abs_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) (le_of_eq (mul_one _))
      show |(S.family.metric t).inner x
          (basis (mm (Fin.natAdd (((4 + a) + (4 + b)) + 2 * r) (0 : Fin 2))))
          (basis (mm (Fin.natAdd (((4 + a) + (4 + b)) + 2 * r) (1 : Fin 2))))| ≤ 1
      rw [horth]
      split_ifs <;> simp

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **Brick 2: the star-sum Cauchy–Schwarz bound.**  Every `T ∈ StarSum2 S t k` admits a
constant `C ≥ 0` (uniform in the point and the orthonormal basis) with

`|T(basis-components)| ≤ C · Σ_{j ≤ k} √(wⱼ)·√(w_{k−j})`,    `wⱼ = |∇ʲRm|²`.

`zero → 0`, `add → C₁+C₂`, `smul c → |c|·C`, `base → card²` (one `card` per metric
trace, then componentwise Cauchy–Schwarz on the two factors of `∇ᵃRm ⊗ ∇ᵇRm`). -/
theorem StarSum2.bound
    {S : SolutionOn (I := I) (M := M) D} {t : Real}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {k : ℕ}
    {T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (4 + k)}
    (hT : StarSum2 (I := I) S t k T) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (x : M) (basis : Module.Basis Idx Real (TangentSpace I x)),
        (∀ i j : Idx, (S.family.metric t).inner x (basis i) (basis j)
            = if i = j then (1 : Real) else 0) →
        ∀ m : Fin (4 + k) → Idx,
          |T x (fun p => basis (m p))| ≤
            C * ∑ j ∈ Finset.range (k + 1),
              Real.sqrt (stNormSq (I := I) S t j x basis) *
                Real.sqrt (stNormSq (I := I) S t (k - j) x basis) := by
  classical
  induction hT with
  | zero =>
      refine ⟨0, le_refl 0, fun x basis _ m => ?_⟩
      simp [ContMDiffSection.coe_zero]
  | @add A B hA hB ihA ihB =>
      obtain ⟨Ca, hCa0, hCa⟩ := ihA
      obtain ⟨Cb, hCb0, hCb⟩ := ihB
      refine ⟨Ca + Cb, add_nonneg hCa0 hCb0, fun x basis horth m => ?_⟩
      have h1 := hCa x basis horth m
      have h2 := hCb x basis horth m
      have hval : (A + B) x (fun p => basis (m p))
          = A x (fun p => basis (m p)) + B x (fun p => basis (m p)) := rfl
      rw [hval]
      refine le_trans (abs_add_le _ _) (le_trans (add_le_add h1 h2) (le_of_eq (by ring)))
  | @smul c A hA ih =>
      obtain ⟨Ca, hCa0, hCa⟩ := ih
      refine ⟨|c| * Ca, mul_nonneg (abs_nonneg c) hCa0, fun x basis horth m => ?_⟩
      have h1 := hCa x basis horth m
      have hval : (c • A) x (fun p => basis (m p))
          = c * (A x (fun p => basis (m p))) := rfl
      rw [hval, abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left h1 (abs_nonneg c)) (le_of_eq (by ring))
  | base a b r σ =>
      have hcard := Fintype.card_congr σ
      simp only [Fintype.card_fin] at hcard
      have hab : a + b = k := by omega
      refine ⟨(Fintype.card Idx : Real) ^ (2 + r), by positivity,
        fun x basis horth m => ?_⟩
      -- componentwise Cauchy–Schwarz on the reindexed generator
      have hinner : ∀ mm : Fin ((4 + k) + 2 * (2 + r)) → Idx,
          |(MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (∞ : WithTop ℕ∞) σ
              (starProd (I := I) S t a b r)) x (fun q => basis (mm q))| ≤
            Real.sqrt (stNormSq (I := I) S t a x basis) *
              Real.sqrt (stNormSq (I := I) S t b x basis) := by
        intro mm
        rw [MultilinearSection.domDomCongr_apply,
          ContinuousMultilinearMap.domDomCongr_apply]
        exact starProdBd (I := I) S t a b basis horth r (fun p => mm (σ p))
      -- the `(2+r)`-fold trace: one `card` factor per trace
      have htop := mtIterOrthoBd (I := I) (S.family.metric t) basis horth
        (s' := 4 + k) (2 + r) _ _ hinner m
      have hmem : a ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
      have hb : k - a = b := by omega
      have hsingle : Real.sqrt (stNormSq (I := I) S t a x basis) *
            Real.sqrt (stNormSq (I := I) S t b x basis) ≤
          ∑ j ∈ Finset.range (k + 1),
            Real.sqrt (stNormSq (I := I) S t j x basis) *
              Real.sqrt (stNormSq (I := I) S t (k - j) x basis) := by
        have hs := Finset.single_le_sum
          (f := fun j => Real.sqrt (stNormSq (I := I) S t j x basis) *
            Real.sqrt (stNormSq (I := I) S t (k - j) x basis))
          (fun j _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hmem
        simp only [hb] at hs
        exact hs
      exact le_trans htop (mul_le_mul_of_nonneg_left hsingle (by positivity))

end DifferentialGeometry.PDE.RicciFlow
