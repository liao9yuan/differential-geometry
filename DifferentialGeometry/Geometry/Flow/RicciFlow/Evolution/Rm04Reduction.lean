import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Rm04Variation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Uhlenbeck

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Static reduction of the lowered-Riemann variation to Uhlenbeck reaction–diffusion form

`Evolution/Rm04Variation.lean` proves that along a Ricci flow the canonical coordinate
component of the lowered Riemann tensor has time derivative `rm04VarRHS`, the explicit
`∇²Ric` expansion of the Christoffel variation.  This module performs the **static**
half of the reduction: at one fixed time and one fixed frame centre it rewrites
`rm04VarRHS` into the Uhlenbeck reaction–diffusion right-hand side

`Δ Rm_{ijkl} − 2 (B_{ijkl} − B_{ijlk} + B_{ikjl} − B_{iljk}) − drift_{ijkl}`

which is the shape consumed by `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`.
Nothing here involves a time derivative: every statement is an identity of real
numbers built from the components of a single Riemannian metric.

The route is MSM110 (Chow–Knopf) Chapter 6, Lemma 6.14 / Corollary / Lemma 6.15:

* `rmVar_eq_hess` — the algebraic half of the `∂ₜ` side: contracting the metric out of
  the two `∇Γ̇` terms leaves a plain `∇∇Ric` commutator plus the four-Hessian block
  `rmHess` and `−2` times the last drift term.
* `comm_eq_drift` — the `(0,2)` Ricci identity turns that commutator into the difference
  of the third and fourth drift terms.
* `rmHess_eq_lap` — MSM110 Lemma 6.14, the second-Bianchi + curvature-commutator core,
  proved from the `Rm04LapIn` input package (differentiated second Bianchi, `(0,4)` Ricci
  identity, trace realizations, symmetries).
* `rmQuad_eq_b` — MSM110 Lemma 6.15, purely algebraic: the quadratic curvature block
  produced by Lemma 6.14 equals `−2(B − B + B − B)` for the project's minus-free `B`.

## Sign conventions

`convention.md` fixes `Rm04(X,Y,Z,W) = g(W, R(X,Y)Z)` with
`R(X,Y)Z = ∇_X∇_Y Z − ∇_Y∇_X Z − ∇_{[X,Y]}Z`, which is exactly MSM110's
`R_{ijkℓ} = g_{ℓm}R^m_{ijk}`.  The project's `uhlenbeckBTensorInFrame` has **no** leading
minus, while MSM110's `B` carries one, so `bComp = −B_MSM`; this is why the project's
target predicate reads `− 2 (B − B + B − B)` where the book reads `+ 2 (B − B + B − B)`.
See `Evolution/UhlenbeckBaseProducer.md` for the verified reconciliation.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

/-! ## Component algebra of an algebraic curvature tensor

Everything in this section is finite-sum algebra over a bare index type: no manifold,
no metric object, no smoothness.  The solution-level statements at the end of the file
are thin instantiations. -/

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The algebraic symmetries of a lowered curvature tensor in components:
antisymmetry in each pair, pair symmetry, and the first Bianchi identity (cyclic in
the first three slots). -/
structure Rm04Symm (Rm : ι → ι → ι → ι → Real) : Prop where
  /-- Antisymmetry in the first slot pair. -/
  swap12 : ∀ a b c d : ι, Rm a b c d = -Rm b a c d
  /-- Antisymmetry in the second slot pair. -/
  swap34 : ∀ a b c d : ι, Rm a b c d = -Rm a b d c
  /-- Symmetry under exchanging the two slot pairs. -/
  pair : ∀ a b c d : ι, Rm a b c d = Rm c d a b
  /-- First Bianchi identity, cyclic in the first three slots. -/
  bianchi : ∀ a b c d : ι, Rm a b c d + Rm b c a d + Rm c a b d = 0

/-- Exchange the outer index pair with the inner index pair of a quadruple sum. -/
private theorem sum4Swap (F : ι → ι → ι → ι → Real) :
    (∑ a : ι, ∑ b : ι, ∑ c : ι, ∑ d : ι, F a b c d)
      = ∑ c : ι, ∑ d : ι, ∑ a : ι, ∑ b : ι, F a b c d := by
  calc (∑ a : ι, ∑ b : ι, ∑ c : ι, ∑ d : ι, F a b c d)
      = ∑ a : ι, ∑ c : ι, ∑ b : ι, ∑ d : ι, F a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c : ι, ∑ a : ι, ∑ b : ι, ∑ d : ι, F a b c d := Finset.sum_comm
    _ = ∑ c : ι, ∑ a : ι, ∑ d : ι, ∑ b : ι, F a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c : ι, ∑ d : ι, ∑ a : ι, ∑ b : ι, F a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Normal form for a double metric contraction of a quadratically indexed quantity:
`Σ g^{pq} g^{rs} X_{pqrs}`.  Every quadratic curvature block of MSM110 Lemma 6.14 is
one of these; putting them all in this shape reduces the book's index gymnastics to
pointwise rewriting under a fixed sum. -/
def quadSum (gInv : ι → ι → Real) (X : ι → ι → ι → ι → Real) : Real :=
  ∑ p : ι, ∑ q : ι, ∑ r : ι, ∑ s : ι, gInv p q * gInv r s * X p q r s

theorem quadSum_congr (gInv : ι → ι → Real) {X Y : ι → ι → ι → ι → Real}
    (h : ∀ p q r s : ι, X p q r s = Y p q r s) :
    quadSum gInv X = quadSum gInv Y :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [h]

/-- Four-term linearity of `quadSum`, in the exact combination produced by the first
Bianchi expansion of the `Q₁` block. -/
private theorem quadSum4 (gInv : ι → ι → Real) (X₁ X₂ X₃ X₄ : ι → ι → ι → ι → Real) :
    quadSum gInv (fun p q r s => X₁ p q r s - X₂ p q r s - X₃ p q r s + X₄ p q r s)
      = quadSum gInv X₁ - quadSum gInv X₂ - quadSum gInv X₃ + quadSum gInv X₄ := by
  unfold quadSum
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]

private theorem quadSumAdd (gInv : ι → ι → Real) (X Y : ι → ι → ι → ι → Real) :
    quadSum gInv (fun p q r s => X p q r s + Y p q r s)
      = quadSum gInv X + quadSum gInv Y := by
  unfold quadSum
  simp only [mul_add, Finset.sum_add_distrib]

private theorem quadSumA4 (gInv : ι → ι → Real) (X₁ X₂ X₃ X₄ : ι → ι → ι → ι → Real) :
    quadSum gInv (fun p q r s => X₁ p q r s + X₂ p q r s + X₃ p q r s + X₄ p q r s)
      = quadSum gInv X₁ + quadSum gInv X₂ + quadSum gInv X₃ + quadSum gInv X₄ := by
  unfold quadSum
  simp only [mul_add, Finset.sum_add_distrib]

private theorem quadSumNeg (gInv : ι → ι → Real) (X : ι → ι → ι → ι → Real) :
    quadSum gInv (fun p q r s => -X p q r s) = -quadSum gInv X := by
  unfold quadSum
  simp only [mul_neg, Finset.sum_neg_distrib]

/-- Exchanging the roles of the two contracted index pairs. -/
private theorem quadSwapPR (gInv : ι → ι → Real) (X : ι → ι → ι → ι → Real) :
    quadSum gInv X = quadSum gInv (fun p q r s => X r s p q) := by
  unfold quadSum
  calc (∑ p : ι, ∑ q : ι, ∑ r : ι, ∑ s : ι, gInv p q * gInv r s * X p q r s)
      = ∑ r : ι, ∑ s : ι, ∑ p : ι, ∑ q : ι, gInv p q * gInv r s * X p q r s :=
        sum4Swap _
    _ = ∑ p : ι, ∑ q : ι, ∑ r : ι, ∑ s : ι, gInv p q * gInv r s * X r s p q :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Transposing the second contracted index pair, using symmetry of the inverse metric. -/
private theorem quadSwapRS (gInv : ι → ι → Real)
    (hgi : ∀ a b : ι, gInv a b = gInv b a) (X : ι → ι → ι → ι → Real) :
    quadSum gInv X = quadSum gInv (fun p q r s => X p q s r) := by
  unfold quadSum
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  calc (∑ r : ι, ∑ s : ι, gInv p q * gInv r s * X p q r s)
      = ∑ s : ι, ∑ r : ι, gInv p q * gInv r s * X p q r s := Finset.sum_comm
    _ = ∑ r : ι, ∑ s : ι, gInv p q * gInv r s * X p q s r :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hgi b a]

/-- Transposing the first contracted index pair, using symmetry of the inverse metric. -/
private theorem quadSwapPQ (gInv : ι → ι → Real)
    (hgi : ∀ a b : ι, gInv a b = gInv b a) (X : ι → ι → ι → ι → Real) :
    quadSum gInv X = quadSum gInv (fun p q r s => X q p r s) := by
  unfold quadSum
  calc (∑ p : ι, ∑ q : ι, ∑ r : ι, ∑ s : ι, gInv p q * gInv r s * X p q r s)
      = ∑ q : ι, ∑ p : ι, ∑ r : ι, ∑ s : ι, gInv p q * gInv r s * X p q r s :=
        Finset.sum_comm
    _ = ∑ p : ι, ∑ q : ι, ∑ r : ι, ∑ s : ι, gInv p q * gInv r s * X q p r s :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [hgi b a]

/-! ### The quadratic blocks -/

/-- Uhlenbeck's quadratic `B_{abcd} = Σ g^{eg} g^{fr} Rm_{aebf} Rm_{cgdr}` in bare
components: the frame-free core of `uhlenbeckBTensorInFrame`.  Note the absence of a
leading minus sign; this is `−B` in MSM110's normalization. -/
def bComp (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real) (a b c d : ι) : Real :=
  ∑ e : ι, ∑ g : ι, ∑ f : ι, ∑ r : ι,
    gInv e g * gInv f r * Rm a e b f * Rm c g d r

private theorem bComp_quad (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real)
    (a b c d : ι) :
    bComp gInv Rm a b c d = quadSum gInv (fun p q r s => Rm a p b r * Rm c q d s) :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem quadB (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real) (a b c d : ι) :
    quadSum gInv (fun p q r s => Rm a r b p * Rm c s d q) = bComp gInv Rm a b c d := by
  rw [bComp_quad]
  exact quadSwapPR gInv (fun p q r s => Rm a r b p * Rm c s d q)

/-- `B_{abcd} = B_{badc}`, one of the algebraic identities of MSM110 (6.42). -/
theorem bComp_swap (gInv : ι → ι → Real) {Rm : ι → ι → ι → ι → Real}
    (hsym : Rm04Symm Rm) (a b c d : ι) :
    bComp gInv Rm a b c d = bComp gInv Rm b a d c := by
  calc bComp gInv Rm a b c d
      = quadSum gInv (fun p q r s => Rm a r b p * Rm c s d q) := (quadB gInv Rm a b c d).symm
    _ = quadSum gInv (fun p q r s => Rm b p a r * Rm d q c s) :=
        quadSum_congr gInv fun p q r s => by rw [hsym.pair a r b p, hsym.pair c s d q]
    _ = bComp gInv Rm b a d c := (bComp_quad gInv Rm b a d c).symm

/-- First quadratic block of MSM110 Lemma 6.14: `Σ g^{pq} g^{rs} Rm_{ijps} Rm_{rqkl}`,
the all-lowered form of `g^{pq} R^r_{ijp} R_{rqkl}`. -/
def rmQ1 (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real) (i j k l : ι) : Real :=
  quadSum gInv (fun p q r s => Rm i j p s * Rm r q k l)

/-- Second quadratic block: the all-lowered form of `g^{pq} R^r_{pik} R_{jqrl}`. -/
def rmQ2 (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real) (i j k l : ι) : Real :=
  quadSum gInv (fun p q r s => Rm p i k s * Rm j q r l)

/-- Third quadratic block: the all-lowered form of `g^{pq} R_{pirl} R^r_{jqk}`. -/
def rmQ4 (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real) (i j k l : ι) : Real :=
  quadSum gInv (fun p q r s => Rm p i r l * Rm j q k s)

/-- The quadratic curvature block of the MSM110 `(4,0)` reaction–diffusion equation,
`g^{pq}(R^r_{ijp}R_{rqkl} − 2R^r_{pik}R_{jqrl} + 2R_{pirl}R^r_{jqk})`. -/
def rmQuad (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real) (i j k l : ι) : Real :=
  rmQ1 gInv Rm i j k l - 2 * rmQ2 gInv Rm i j k l + 2 * rmQ4 gInv Rm i j k l

theorem rmQ2_eq_b (gInv : ι → ι → Real) {Rm : ι → ι → ι → ι → Real}
    (hsym : Rm04Symm Rm) (hgi : ∀ a b : ι, gInv a b = gInv b a) (i j k l : ι) :
    rmQ2 gInv Rm i j k l = bComp gInv Rm i k j l := by
  calc rmQ2 gInv Rm i j k l
      = quadSum gInv (fun p q r s => Rm i p k s * Rm j q l r) :=
        quadSum_congr gInv fun p q r s => by
          rw [hsym.swap12 p i k s, hsym.swap34 j q r l]; ring
    _ = quadSum gInv (fun p q r s => Rm i p k r * Rm j q l s) :=
        quadSwapRS gInv hgi (fun p q r s => Rm i p k s * Rm j q l r)
    _ = bComp gInv Rm i k j l := (bComp_quad gInv Rm i k j l).symm

theorem rmQ4_eq_b (gInv : ι → ι → Real) {Rm : ι → ι → ι → ι → Real}
    (hsym : Rm04Symm Rm) (i j k l : ι) :
    rmQ4 gInv Rm i j k l = bComp gInv Rm i l j k := by
  calc rmQ4 gInv Rm i j k l
      = quadSum gInv (fun p q r s => Rm i p l r * Rm j q k s) :=
        quadSum_congr gInv fun p q r s => by
          rw [hsym.swap12 p i r l, hsym.swap34 i p r l]; ring
    _ = bComp gInv Rm i l j k := (bComp_quad gInv Rm i l j k).symm

theorem rmQ1_eq_b (gInv : ι → ι → Real) {Rm : ι → ι → ι → ι → Real}
    (hsym : Rm04Symm Rm) (hgi : ∀ a b : ι, gInv a b = gInv b a) (i j k l : ι) :
    rmQ1 gInv Rm i j k l = -2 * (bComp gInv Rm i j k l - bComp gInv Rm i j l k) := by
  have hA : ∀ p s : ι, Rm i j p s = Rm s p j i := by
    intro p s
    rw [hsym.pair i j p s, hsym.swap12 p s i j, hsym.swap34 s p i j]
    ring
  have hB1 : ∀ r p : ι, Rm r p j i = -Rm i r j p + Rm j r i p := by
    intro r p
    have h : Rm j i r p + Rm i r j p + Rm r j i p = 0 := hsym.bianchi j i r p
    have h2 : Rm r j i p = -Rm j r i p := hsym.swap12 r j i p
    rw [hsym.pair r p j i]
    linarith
  have hB2 : ∀ s q : ι, Rm s q k l = -Rm l s k q + Rm k s l q := by
    intro s q
    have h : Rm k l s q + Rm l s k q + Rm s k l q = 0 := hsym.bianchi k l s q
    have h2 : Rm s k l q = -Rm k s l q := hsym.swap12 s k l q
    rw [hsym.pair s q k l]
    linarith
  calc rmQ1 gInv Rm i j k l
      = quadSum gInv (fun p q r s => Rm s p j i * Rm r q k l) :=
        quadSum_congr gInv fun p q r s => by rw [hA p s]
    _ = quadSum gInv (fun p q r s => Rm r p j i * Rm s q k l) :=
        quadSwapRS gInv hgi (fun p q r s => Rm s p j i * Rm r q k l)
    _ = quadSum gInv (fun p q r s =>
          Rm i r j p * Rm l s k q - Rm i r j p * Rm k s l q
            - Rm j r i p * Rm l s k q + Rm j r i p * Rm k s l q) :=
        quadSum_congr gInv fun p q r s => by rw [hB1 r p, hB2 s q]; ring
    _ = quadSum gInv (fun p q r s => Rm i r j p * Rm l s k q)
          - quadSum gInv (fun p q r s => Rm i r j p * Rm k s l q)
          - quadSum gInv (fun p q r s => Rm j r i p * Rm l s k q)
          + quadSum gInv (fun p q r s => Rm j r i p * Rm k s l q) :=
        quadSum4 gInv _ _ _ _
    _ = bComp gInv Rm i j l k - bComp gInv Rm i j k l
          - bComp gInv Rm j i l k + bComp gInv Rm j i k l := by
        rw [quadB gInv Rm i j l k, quadB gInv Rm i j k l, quadB gInv Rm j i l k,
          quadB gInv Rm j i k l]
    _ = -2 * (bComp gInv Rm i j k l - bComp gInv Rm i j l k) := by
        rw [bComp_swap gInv hsym j i l k, bComp_swap gInv hsym j i k l]
        ring

/-- **MSM110 Lemma 6.15, algebraic half.**  The quadratic curvature block of the
`(4,0)` reaction–diffusion equation is `−2(B − B + B − B)` in the project's minus-free
`B`, which is `+2(B − B + B − B)` in MSM110's normalization. -/
theorem rmQuad_eq_b (gInv : ι → ι → Real) {Rm : ι → ι → ι → ι → Real}
    (hsym : Rm04Symm Rm) (hgi : ∀ a b : ι, gInv a b = gInv b a) (i j k l : ι) :
    rmQuad gInv Rm i j k l
      = -2 * (bComp gInv Rm i j k l - bComp gInv Rm i j l k
          + bComp gInv Rm i k j l - bComp gInv Rm i l j k) := by
  rw [rmQuad, rmQ1_eq_b gInv hsym hgi i j k l, rmQ2_eq_b gInv hsym hgi i j k l,
    rmQ4_eq_b gInv hsym i j k l]
  ring

/-! ### The evolution blocks -/

/-- Rough Laplacian of the lowered curvature tensor, `Σ g^{pq}(∇_p∇_q Rm)_{ijkl}`. -/
def rmLap (gInv : ι → ι → Real) (n2Rm : ι → ι → ι → ι → ι → ι → Real)
    (i j k l : ι) : Real :=
  ∑ p : ι, ∑ q : ι, gInv p q * n2Rm p q i j k l

/-- The four Ricci-drift contractions, matching `riemann04RicciDriftInFrame`. -/
def rmDrift (Rup : ι → ι → Real) (Rm : ι → ι → ι → ι → Real) (i j k l : ι) : Real :=
  (∑ p : ι, Rup i p * Rm p j k l) + (∑ p : ι, Rup j p * Rm i p k l) +
    (∑ p : ι, Rup k p * Rm i j p l) + (∑ p : ι, Rup l p * Rm i j k p)

/-- The four-Hessian block of MSM110 (6.41a), all indices lowered:
`−∇_i∇_k Ric_{jl} + ∇_i∇_l Ric_{jk} + ∇_j∇_k Ric_{il} − ∇_j∇_l Ric_{ik}`. -/
def rmHess (n2Ric : ι → ι → ι → ι → Real) (i j k l : ι) : Real :=
  -n2Ric i k j l + n2Ric i l j k + n2Ric j k i l - n2Ric j l i k

/-- Covariant derivative of the Ricci-flow Christoffel variation in components,
the frame-free core of `nablaGammaDtFromNabla2RicInFrame`. -/
def nabGamma (gInv : ι → ι → Real) (n2Ric : ι → ι → ι → ι → Real)
    (d c a b : ι) : Real :=
  ∑ q : ι, gInv c q * (-n2Ric d a b q - n2Ric d b a q + n2Ric d q a b)

/-- The `∇²Ric`-expanded lowered-Riemann variation in components, the frame-free core
of `rm04VarRHS`. -/
def rmVar (g gInv : ι → ι → Real) (Ric : ι → ι → Real)
    (Rm13 : ι → ι → ι → ι → Real) (n2Ric : ι → ι → ι → ι → Real)
    (i j k l : ι) : Real :=
  ∑ p : ι,
    ((nabGamma gInv n2Ric i p j k - nabGamma gInv n2Ric j p i k) * g l p +
      Rm13 i j k p * ((-2 : Real) * Ric l p))

/-- Contracting the metric against `∇Γ̇` cancels the inverse metric of the Christoffel
variation and leaves a plain second covariant derivative of `Ric`. -/
private theorem lowerGamma (g gInv : ι → ι → Real) (n2Ric : ι → ι → ι → ι → Real)
    (hcon : ∀ a b : ι, (∑ p : ι, g a p * gInv p b) = if a = b then 1 else 0)
    (d a b l : ι) :
    (∑ p : ι, nabGamma gInv n2Ric d p a b * g l p)
      = -n2Ric d a b l - n2Ric d b a l + n2Ric d l a b := by
  calc (∑ p : ι, nabGamma gInv n2Ric d p a b * g l p)
      = ∑ p : ι, ∑ q : ι,
          g l p * gInv p q * (-n2Ric d a b q - n2Ric d b a q + n2Ric d q a b) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [nabGamma, Finset.sum_mul]
        exact Finset.sum_congr rfl fun q _ => by ring
    _ = ∑ q : ι, ∑ p : ι,
          g l p * gInv p q * (-n2Ric d a b q - n2Ric d b a q + n2Ric d q a b) :=
        Finset.sum_comm
    _ = ∑ q : ι, (∑ p : ι, g l p * gInv p q) *
          (-n2Ric d a b q - n2Ric d b a q + n2Ric d q a b) :=
        Finset.sum_congr rfl fun q _ => (Finset.sum_mul _ _ _).symm
    _ = -n2Ric d a b l - n2Ric d b a l + n2Ric d l a b := by
        simp only [hcon, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]

/-- **Step 3 (MSM110 §6, `RiemCurv3-1 tensor RicciFlow1`).**  Purely algebraic half of
the reduction: contracting the metric out of the two `∇Γ̇` summands of `rmVar` leaves the
`∇∇Ric` commutator `∇_j∇_i Ric_{kl} − ∇_i∇_j Ric_{kl}`, the four-Hessian block `rmHess`,
and `−2` times the last Ricci-drift contraction. -/
theorem rmVar_eq_hess (g gInv : ι → ι → Real) (Ric : ι → ι → Real)
    (Rm13 : ι → ι → ι → ι → Real) (n2Ric : ι → ι → ι → ι → Real)
    (hcon : ∀ a b : ι, (∑ p : ι, g a p * gInv p b) = if a = b then 1 else 0)
    (i j k l : ι) :
    rmVar g gInv Ric Rm13 n2Ric i j k l
      = (n2Ric j i k l - n2Ric i j k l) + rmHess n2Ric i j k l
        - 2 * ∑ p : ι, Rm13 i j k p * Ric l p := by
  have h1 : (∑ p : ι,
        (nabGamma gInv n2Ric i p j k - nabGamma gInv n2Ric j p i k) * g l p)
      = (∑ p : ι, nabGamma gInv n2Ric i p j k * g l p)
        - (∑ p : ι, nabGamma gInv n2Ric j p i k * g l p) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have h2 : (∑ p : ι, Rm13 i j k p * ((-2 : Real) * Ric l p))
      = -2 * ∑ p : ι, Rm13 i j k p * Ric l p := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [rmVar, Finset.sum_add_distrib, h1, h2,
    lowerGamma g gInv n2Ric hcon i j k l, lowerGamma g gInv n2Ric hcon j i k l, rmHess]
  ring

/-- The `(0,2)` Ricci identity for the Ricci tensor in fixed-frame components:
`∇_j∇_i Ric_{kl} − ∇_i∇_j Ric_{kl} = R^p_{ijk} Ric_{pl} + R^p_{ijl} Ric_{kp}`. -/
def RicCommAt (Rm13 : ι → ι → ι → ι → Real) (Ric : ι → ι → Real)
    (n2Ric : ι → ι → ι → ι → Real) : Prop :=
  ∀ i j k l : ι,
    n2Ric j i k l - n2Ric i j k l
      = (∑ p : ι, Rm13 i j k p * Ric p l) + (∑ p : ι, Rm13 i j l p * Ric k p)

/-- Raising the last index of `Rm13` against `Ric` turns a `Rm13 · Ric` contraction into
a `Rup · Rm` drift contraction. -/
private theorem contractRm13 (gInv : ι → ι → Real) (Ric Rup : ι → ι → Real)
    (Rm13 Rm : ι → ι → ι → ι → Real)
    (hraise : ∀ a b c d : ι, Rm13 a b c d = ∑ q : ι, gInv d q * Rm a b c q)
    (hRup : ∀ a b : ι, Rup a b = ∑ q : ι, gInv b q * Ric a q)
    (hgi : ∀ a b : ι, gInv a b = gInv b a)
    (a b c e : ι) :
    (∑ p : ι, Rm13 a b c p * Ric e p) = ∑ p : ι, Rup e p * Rm a b c p := by
  calc (∑ p : ι, Rm13 a b c p * Ric e p)
      = ∑ p : ι, ∑ q : ι, gInv p q * Rm a b c q * Ric e p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hraise a b c p, Finset.sum_mul]
    _ = ∑ q : ι, ∑ p : ι, gInv p q * Rm a b c q * Ric e p := Finset.sum_comm
    _ = ∑ q : ι, Rup e q * Rm a b c q := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hRup e q, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => by rw [hgi q p]; ring

/-- **Step 3b.**  The `∇∇Ric` commutator left by `rmVar_eq_hess` is the difference of the
third and fourth Ricci-drift contractions. -/
theorem comm_eq_drift (gInv : ι → ι → Real) (Ric Rup : ι → ι → Real)
    (Rm13 Rm : ι → ι → ι → ι → Real) (n2Ric : ι → ι → ι → ι → Real)
    (hsym : Rm04Symm Rm)
    (hcomm : RicCommAt Rm13 Ric n2Ric)
    (hricsym : ∀ a b : ι, Ric a b = Ric b a)
    (hraise : ∀ a b c d : ι, Rm13 a b c d = ∑ q : ι, gInv d q * Rm a b c q)
    (hRup : ∀ a b : ι, Rup a b = ∑ q : ι, gInv b q * Ric a q)
    (hgi : ∀ a b : ι, gInv a b = gInv b a)
    (i j k l : ι) :
    n2Ric j i k l - n2Ric i j k l
      = (∑ p : ι, Rup l p * Rm i j k p) - (∑ p : ι, Rup k p * Rm i j p l) := by
  have hfirst : (∑ p : ι, Rm13 i j k p * Ric p l) = ∑ p : ι, Rup l p * Rm i j k p := by
    rw [show (∑ p : ι, Rm13 i j k p * Ric p l) = ∑ p : ι, Rm13 i j k p * Ric l p from
      Finset.sum_congr rfl fun p _ => by rw [hricsym p l]]
    exact contractRm13 gInv Ric Rup Rm13 Rm hraise hRup hgi i j k l
  have hsecond : (∑ p : ι, Rm13 i j l p * Ric k p) = -∑ p : ι, Rup k p * Rm i j p l := by
    rw [contractRm13 gInv Ric Rup Rm13 Rm hraise hRup hgi i j l k, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ => by rw [hsym.swap34 i j l p]; ring
  rw [hcomm i j k l, hfirst, hsecond]
  ring

/-! ### The Laplacian core (MSM110 Lemma 6.14) -/

/-- Differential inputs of the book's `Δ Rm` computation (MSM110 Lemma 6.14), all in
fixed-frame components at one point.  `n2Rm p q a b c d = (∇_p∇_q Rm)_{abcd}` and
`n2Ric p q a b = (∇_p∇_q Ric)_{ab}`. -/
structure Rm04LapIn (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real)
    (Ric : ι → ι → Real) (n2Ric : ι → ι → ι → ι → Real)
    (n2Rm : ι → ι → ι → ι → ι → ι → Real) : Prop where
  /-- The second Bianchi identity, differentiated once. -/
  bianchi2 : ∀ p a b c d e : ι,
    n2Rm p a b c d e + n2Rm p b c a d e + n2Rm p c a b d e = 0
  /-- The Ricci identity for the `(0,4)` curvature tensor, with the curvature action
  written through the all-lowered `Rm`. -/
  ricciId : ∀ a b c d e f : ι,
    n2Rm a b c d e f - n2Rm b a c d e f
      = -∑ q : ι, ∑ r : ι, gInv q r *
          (Rm a b c r * Rm q d e f + Rm a b d r * Rm c q e f +
            Rm a b e r * Rm c d q f + Rm a b f r * Rm c d e q)
  /-- `Ric` is the first metric trace of `Rm`. -/
  ricTrace : ∀ a b : ι, Ric a b = ∑ p : ι, ∑ q : ι, gInv p q * Rm p a b q
  /-- `∇²Ric` is the first metric trace of `∇²Rm`; the trace passes the covariant
  derivatives because the connection is metric. -/
  n2RicTrace : ∀ a b c d : ι,
    n2Ric a b c d = ∑ p : ι, ∑ q : ι, gInv p q * n2Rm a b p c d q
  /-- `∇²Rm` inherits the antisymmetry of `Rm` in its first tensor slot pair. -/
  n2RmSwap12 : ∀ a b c d e f : ι, n2Rm a b c d e f = -n2Rm a b d c e f
  /-- `∇²Rm` inherits the pair symmetry of `Rm`. -/
  n2RmPair : ∀ a b c d e f : ι, n2Rm a b c d e f = n2Rm a b e f c d
  /-- `∇²Ric` inherits the symmetry of `Ric`. -/
  n2RicSym : ∀ a b c d : ι, n2Ric a b c d = n2Ric a b d c

/-- The middle metric trace of `Rm` is minus `Ric`: `Σ g^{pq} Rm_{p a q b} = −Ric_{ab}`. -/
private theorem traceMid (gInv : ι → ι → Real) {Ric : ι → ι → Real}
    {Rm : ι → ι → ι → ι → Real} (hsym : Rm04Symm Rm)
    (hric : ∀ a b : ι, Ric a b = ∑ p : ι, ∑ q : ι, gInv p q * Rm p a b q) (a b : ι) :
    (∑ p : ι, ∑ q : ι, gInv p q * Rm p a q b) = -Ric a b := by
  rw [hric a b, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun q _ => by rw [hsym.swap34 p a q b]; ring

/-- Contracting the middle trace out of a `quadSum` whose first factor is traced. -/
private theorem quadTr (gInv : ι → ι → Real) {Ric : ι → ι → Real}
    {Rm : ι → ι → ι → ι → Real} (hsym : Rm04Symm Rm)
    (hric : ∀ a b : ι, Ric a b = ∑ p : ι, ∑ q : ι, gInv p q * Rm p a b q)
    (F : ι → Real) (a : ι) :
    quadSum gInv (fun p q u v => Rm p a q v * F u)
      = ∑ u : ι, ∑ v : ι, gInv u v * (-Ric a v) * F u := by
  unfold quadSum
  calc (∑ p : ι, ∑ q : ι, ∑ u : ι, ∑ v : ι, gInv p q * gInv u v * (Rm p a q v * F u))
      = ∑ u : ι, ∑ v : ι, ∑ p : ι, ∑ q : ι,
          gInv p q * gInv u v * (Rm p a q v * F u) := sum4Swap _
    _ = ∑ u : ι, ∑ v : ι, gInv u v * (∑ p : ι, ∑ q : ι, gInv p q * Rm p a q v) * F u := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        simp only [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ u : ι, ∑ v : ι, gInv u v * (-Ric a v) * F u :=
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
          rw [traceMid gInv hsym hric a v]

/-- A traced `quadSum` of the above shape is one Ricci-drift contraction. -/
private theorem quadTrDrift (gInv : ι → ι → Real) {Ric Rup : ι → ι → Real}
    {Rm : ι → ι → ι → ι → Real} (hsym : Rm04Symm Rm)
    (hric : ∀ a b : ι, Ric a b = ∑ p : ι, ∑ q : ι, gInv p q * Rm p a b q)
    (hRup : ∀ a b : ι, Rup a b = ∑ q : ι, gInv b q * Ric a q)
    (F G : ι → Real) (hFG : ∀ u : ι, F u = -G u) (a : ι) :
    quadSum gInv (fun p q u v => Rm p a q v * F u) = ∑ u : ι, Rup a u * G u := by
  rw [quadTr gInv hsym hric F a]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hRup a u, Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => by rw [hFG u]; ring

/-- **Differentiated traced second Bianchi identity.**  `Σ g^{pq} ∇_d∇_p Rm_{aqkl}`
collapses to a difference of two second covariant derivatives of `Ric`; this is the
`(0,4)` form of MSM110's `g^{pq}∇_p R^ℓ_{jqk} = ∇_k R_j^ℓ − ∇^ℓ R_{jk}` after applying
`∇_d`. -/
private theorem tracedBi (gInv : ι → ι → Real) {Ric : ι → ι → Real}
    {Rm : ι → ι → ι → ι → Real} {n2Ric : ι → ι → ι → ι → Real}
    {n2Rm : ι → ι → ι → ι → ι → ι → Real}
    (hin : Rm04LapIn gInv Rm Ric n2Ric n2Rm) (d a k l : ι) :
    (∑ p : ι, ∑ q : ι, gInv p q * n2Rm d p a q k l)
      = n2Ric d k a l - n2Ric d l a k := by
  have hpt : ∀ p q : ι,
      n2Rm d p a q k l = n2Rm d k p l a q - n2Rm d l p k a q := by
    intro p q
    have hb := hin.bianchi2 d p k l a q
    have h1 : n2Rm d p a q k l = n2Rm d p k l a q := hin.n2RmPair d p a q k l
    have h2 : n2Rm d k l p a q = -n2Rm d k p l a q := hin.n2RmSwap12 d k l p a q
    rw [h1]
    linarith
  calc (∑ p : ι, ∑ q : ι, gInv p q * n2Rm d p a q k l)
      = ∑ p : ι, ∑ q : ι,
          (gInv p q * n2Rm d k p l a q - gInv p q * n2Rm d l p k a q) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
          rw [hpt p q]; ring
    _ = (∑ p : ι, ∑ q : ι, gInv p q * n2Rm d k p l a q)
          - (∑ p : ι, ∑ q : ι, gInv p q * n2Rm d l p k a q) := by
        simp only [Finset.sum_sub_distrib]
    _ = n2Ric d k a l - n2Ric d l a k := by
        rw [← hin.n2RicTrace d k l a, ← hin.n2RicTrace d l k a,
          hin.n2RicSym d k l a, hin.n2RicSym d l k a]

/-- The eight quadratic curvature terms produced by commuting `∇_p` past `∇_i` and
`∇_j` in the book's computation of `Δ Rm`. -/
private def rmW (gInv : ι → ι → Real) (Rm : ι → ι → ι → ι → Real) (i j k l : ι) : Real :=
  quadSum gInv (fun p q u v =>
      Rm p i j v * Rm u q k l + Rm p i q v * Rm j u k l +
        Rm p i k v * Rm j q u l + Rm p i l v * Rm j q k u) +
    quadSum gInv (fun p q u v =>
      Rm p j q v * Rm u i k l + Rm p j i v * Rm q u k l +
        Rm p j k v * Rm q i u l + Rm p j l v * Rm q i k u)

/-- **Steps 1–3 of MSM110 Lemma 6.14.**  Second Bianchi on the inner derivative,
`∇`-commutation, and the differentiated traced Bianchi identity turn the rough
Laplacian of `Rm` into the four-Hessian block plus the eight quadratic terms. -/
private theorem lapHessW (gInv : ι → ι → Real) {Ric : ι → ι → Real}
    {Rm : ι → ι → ι → ι → Real} {n2Ric : ι → ι → ι → ι → Real}
    {n2Rm : ι → ι → ι → ι → ι → ι → Real}
    (hin : Rm04LapIn gInv Rm Ric n2Ric n2Rm) (i j k l : ι) :
    rmLap gInv n2Rm i j k l = rmHess n2Ric i j k l + rmW gInv Rm i j k l := by
  have hpt : ∀ p q : ι,
      n2Rm p q i j k l
        = -n2Rm i p j q k l - n2Rm j p q i k l
          + (∑ u : ι, ∑ v : ι, gInv u v *
              (Rm p i j v * Rm u q k l + Rm p i q v * Rm j u k l +
                Rm p i k v * Rm j q u l + Rm p i l v * Rm j q k u))
          + (∑ u : ι, ∑ v : ι, gInv u v *
              (Rm p j q v * Rm u i k l + Rm p j i v * Rm q u k l +
                Rm p j k v * Rm q i u l + Rm p j l v * Rm q i k u)) := by
    intro p q
    have hb := hin.bianchi2 p q i j k l
    have h1 := hin.ricciId p i j q k l
    have h2 := hin.ricciId p j q i k l
    linarith
  have hsplit : rmLap gInv n2Rm i j k l
      = -(∑ p : ι, ∑ q : ι, gInv p q * n2Rm i p j q k l)
        - (∑ p : ι, ∑ q : ι, gInv p q * n2Rm j p q i k l)
        + rmW gInv Rm i j k l := by
    unfold rmLap rmW quadSum
    calc (∑ p : ι, ∑ q : ι, gInv p q * n2Rm p q i j k l)
        = ∑ p : ι, ∑ q : ι,
            (-(gInv p q * n2Rm i p j q k l) - gInv p q * n2Rm j p q i k l
              + (∑ u : ι, ∑ v : ι, gInv p q * gInv u v *
                  (Rm p i j v * Rm u q k l + Rm p i q v * Rm j u k l +
                    Rm p i k v * Rm j q u l + Rm p i l v * Rm j q k u))
              + (∑ u : ι, ∑ v : ι, gInv p q * gInv u v *
                  (Rm p j q v * Rm u i k l + Rm p j i v * Rm q u k l +
                    Rm p j k v * Rm q i u l + Rm p j l v * Rm q i k u))) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          rw [hpt p q]
          simp only [mul_add, mul_sub, mul_neg, Finset.mul_sum, mul_assoc]
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_neg_distrib]
          ring
  have hswap : (∑ p : ι, ∑ q : ι, gInv p q * n2Rm j p q i k l)
      = -(∑ p : ι, ∑ q : ι, gInv p q * n2Rm j p i q k l) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun q _ => by rw [hin.n2RmSwap12 j p q i k l]; ring
  rw [hsplit, hswap, tracedBi gInv hin i j k l, tracedBi gInv hin j i k l, rmHess]
  ring

/-- **Step 4 of MSM110 Lemma 6.14, plus Lemma 6.15's regrouping.**  The eight quadratic
terms are the first two Ricci-drift contractions minus the quadratic curvature block. -/
private theorem wEq (gInv : ι → ι → Real) {Ric Rup : ι → ι → Real}
    {Rm : ι → ι → ι → ι → Real} (hsym : Rm04Symm Rm)
    (hgi : ∀ a b : ι, gInv a b = gInv b a)
    (hric : ∀ a b : ι, Ric a b = ∑ p : ι, ∑ q : ι, gInv p q * Rm p a b q)
    (hRup : ∀ a b : ι, Rup a b = ∑ q : ι, gInv b q * Ric a q) (i j k l : ι) :
    rmW gInv Rm i j k l
      = (∑ p : ι, Rup i p * Rm p j k l) + (∑ p : ι, Rup j p * Rm i p k l)
        - rmQuad gInv Rm i j k l := by
  -- The first and sixth terms merge by the first Bianchi identity into `−Q₁`.
  have h16 : quadSum gInv (fun p q u v => Rm p i j v * Rm u q k l)
        + quadSum gInv (fun p q u v => Rm p j i v * Rm q u k l)
      = -rmQ1 gInv Rm i j k l := by
    rw [← quadSumAdd gInv (fun p q u v => Rm p i j v * Rm u q k l)
      (fun p q u v => Rm p j i v * Rm q u k l), rmQ1, ← quadSumNeg]
    refine quadSum_congr gInv fun p q u v => ?_
    have hb := hsym.bianchi p i j v
    have hs : Rm j p i v = -Rm p j i v := hsym.swap12 j p i v
    have hq : Rm q u k l = -Rm u q k l := hsym.swap12 q u k l
    have hx : Rm p i j v = -Rm i j p v + Rm p j i v := by linarith
    rw [hq, hx]
    ring
  -- Second term: a middle trace, giving the first Ricci drift.
  have h2 : quadSum gInv (fun p q u v => Rm p i q v * Rm j u k l)
      = ∑ u : ι, Rup i u * Rm u j k l :=
    quadTrDrift gInv hsym hric hRup (fun u => Rm j u k l) (fun u => Rm u j k l)
      (fun u => hsym.swap12 j u k l) i
  -- Fifth term: the same trace with `i` and `j` exchanged.
  have h5 : quadSum gInv (fun p q u v => Rm p j q v * Rm u i k l)
      = ∑ u : ι, Rup j u * Rm i u k l :=
    quadTrDrift gInv hsym hric hRup (fun u => Rm u i k l) (fun u => Rm i u k l)
      (fun u => hsym.swap12 u i k l) j
  -- Third term: literally `Q₂`.
  have h3 : quadSum gInv (fun p q u v => Rm p i k v * Rm j q u l)
      = rmQ2 gInv Rm i j k l := rfl
  -- Fourth term: `−Q₄` after transposing the second contracted pair.
  have h4 : quadSum gInv (fun p q u v => Rm p i l v * Rm j q k u)
      = -rmQ4 gInv Rm i j k l := by
    rw [quadSwapRS gInv hgi (fun p q u v => Rm p i l v * Rm j q k u), rmQ4, ← quadSumNeg]
    exact quadSum_congr gInv fun p q r s => by rw [hsym.swap34 p i l r]; ring
  -- Seventh term: `−Q₄` after transposing the first contracted pair.
  have h7 : quadSum gInv (fun p q u v => Rm p j k v * Rm q i u l)
      = -rmQ4 gInv Rm i j k l := by
    rw [quadSwapPQ gInv hgi (fun p q u v => Rm p j k v * Rm q i u l), rmQ4, ← quadSumNeg]
    exact quadSum_congr gInv fun p q r s => by rw [hsym.swap12 q j k s]; ring
  -- Eighth term: `Q₂` after transposing both contracted pairs.
  have h8 : quadSum gInv (fun p q u v => Rm p j l v * Rm q i k u)
      = rmQ2 gInv Rm i j k l := by
    rw [quadSwapPQ gInv hgi (fun p q u v => Rm p j l v * Rm q i k u)]
    rw [quadSwapRS gInv hgi (fun p q r s => Rm q j l s * Rm p i k r), rmQ2]
    refine quadSum_congr gInv fun p q r s => ?_
    rw [hsym.swap12 q j l r, hsym.swap34 j q l r]
    ring
  rw [rmW, quadSumA4 gInv (fun p q u v => Rm p i j v * Rm u q k l)
      (fun p q u v => Rm p i q v * Rm j u k l) (fun p q u v => Rm p i k v * Rm j q u l)
      (fun p q u v => Rm p i l v * Rm j q k u),
    quadSumA4 gInv (fun p q u v => Rm p j q v * Rm u i k l)
      (fun p q u v => Rm p j i v * Rm q u k l) (fun p q u v => Rm p j k v * Rm q i u l)
      (fun p q u v => Rm p j l v * Rm q i k u),
    h2, h3, h4, h5, h7, h8, rmQuad]
  linarith [h16]

/-- **MSM110 Lemma 6.14 — the `Δ Rm` core.**

The four-Hessian block equals the rough Laplacian of `Rm` plus the quadratic curvature
block minus the first two Ricci-drift contractions.  The proof follows the book: start
from `Δ Rm = g^{pq}∇_p∇_q Rm`, apply the second Bianchi identity to the inner
derivative, commute `∇_p` past `∇_i`/`∇_j` (producing the eight quadratic curvature
terms `rmW`), and substitute the differentiated traced Bianchi identity `tracedBi`; the
first Bianchi identity then merges two of the quadratic terms. -/
theorem rmHess_eq_lap (gInv : ι → ι → Real) {Ric Rup : ι → ι → Real}
    {Rm : ι → ι → ι → ι → Real} {n2Ric : ι → ι → ι → ι → Real}
    {n2Rm : ι → ι → ι → ι → ι → ι → Real}
    (hsym : Rm04Symm Rm) (hgi : ∀ a b : ι, gInv a b = gInv b a)
    (hin : Rm04LapIn gInv Rm Ric n2Ric n2Rm)
    (hRup : ∀ a b : ι, Rup a b = ∑ q : ι, gInv b q * Ric a q)
    (i j k l : ι) :
    rmHess n2Ric i j k l
      = rmLap gInv n2Rm i j k l + rmQuad gInv Rm i j k l
        - (∑ p : ι, Rup i p * Rm p j k l) - (∑ p : ι, Rup j p * Rm i p k l) := by
  rw [lapHessW gInv hin i j k l, wEq gInv hsym hgi hin.ricTrace hRup i j k l]
  ring

/-! ### Assembly -/

/-- **The static reduction, component form.**  The `∇²Ric`-expanded lowered-Riemann
variation equals the Uhlenbeck reaction–diffusion right-hand side
`Δ Rm − 2(B − B + B − B) − drift`. -/
theorem rmVar_eq_uhl (g gInv : ι → ι → Real) (Ric Rup : ι → ι → Real)
    (Rm13 Rm : ι → ι → ι → ι → Real) (n2Ric : ι → ι → ι → ι → Real)
    (n2Rm : ι → ι → ι → ι → ι → ι → Real)
    (hsym : Rm04Symm Rm) (hgi : ∀ a b : ι, gInv a b = gInv b a)
    (hricsym : ∀ a b : ι, Ric a b = Ric b a)
    (hcon : ∀ a b : ι, (∑ p : ι, g a p * gInv p b) = if a = b then 1 else 0)
    (hraise : ∀ a b c d : ι, Rm13 a b c d = ∑ q : ι, gInv d q * Rm a b c q)
    (hRup : ∀ a b : ι, Rup a b = ∑ q : ι, gInv b q * Ric a q)
    (hcomm : RicCommAt Rm13 Ric n2Ric)
    (hin : Rm04LapIn gInv Rm Ric n2Ric n2Rm)
    (i j k l : ι) :
    rmVar g gInv Ric Rm13 n2Ric i j k l
      = rmLap gInv n2Rm i j k l
        - 2 * (bComp gInv Rm i j k l - bComp gInv Rm i j l k
            + bComp gInv Rm i k j l - bComp gInv Rm i l j k)
        - rmDrift Rup Rm i j k l := by
  have hdrift4 : (∑ p : ι, Rm13 i j k p * Ric l p) = ∑ p : ι, Rup l p * Rm i j k p :=
    contractRm13 gInv Ric Rup Rm13 Rm hraise hRup hgi i j k l
  rw [rmVar_eq_hess g gInv Ric Rm13 n2Ric hcon i j k l,
    comm_eq_drift gInv Ric Rup Rm13 Rm n2Ric hsym hcomm hricsym hraise hRup hgi i j k l,
    rmHess_eq_lap gInv hsym hgi hin hRup i j k l,
    rmQuad_eq_b gInv hsym hgi i j k l, hdrift4, rmDrift]
  ring

end Algebra

/-! ## Solution-level statement

The manifold-level wrapper.  Every array is a `FourComp`/`MatrixComp` component array,
exactly as in `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`, and every hypothesis is
a component realization statement at the frame centre `x₀` and the fixed time `t`. -/

section Solution

open Bundle Tensor0SBundle Set
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- **The static reduction at a Ricci-flow solution.**  At the centre `x₀` of the
coordinate frame and at a fixed time `t`, the `∇²Ric`-expanded lowered-Riemann variation
`rm04VarRHS` of `Evolution/Rm04Variation.lean` equals the Uhlenbeck reaction–diffusion
right-hand side built from the supplied component arrays.  Combined with `rm04Var_of_sol`
this is the pointwise statement behind
`Riemann04BTensorWithRicciDriftEvolutionInFrameOn`. -/
theorem rm04Var_eq_uhl
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    (Rm04 : FourComp M (CoordinateIdx (𝕜 := Real) E))
    (ricciOneUp : MatrixComp M (CoordinateIdx (𝕜 := Real) E))
    (nabla2Ric :
      Real → M → CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E →
        CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (nabla2Rm :
      Real → M → CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E →
        CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E →
        CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (hsym : Rm04Symm (Rm04 t x₀))
    (hgi : ∀ a b : CoordinateIdx (𝕜 := Real) E,
      coordInv (I := I) S x₀ t x₀ a b = coordInv (I := I) S x₀ t x₀ b a)
    (hricsym : ∀ a b : CoordinateIdx (𝕜 := Real) E,
      ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀ a b =
        ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀ b a)
    (hcon : ∀ a b : CoordinateIdx (𝕜 := Real) E,
      (∑ p : CoordinateIdx (𝕜 := Real) E,
        metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀ a p *
          coordInv (I := I) S x₀ t x₀ p b) = if a = b then 1 else 0)
    (hraise : ∀ a b c d : CoordinateIdx (𝕜 := Real) E,
      DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
          (I := I) (S.family.connection t) x₀ a b c d =
        ∑ q : CoordinateIdx (𝕜 := Real) E,
          coordInv (I := I) S x₀ t x₀ d q * Rm04 t x₀ a b c q)
    (hRup : ∀ a b : CoordinateIdx (𝕜 := Real) E,
      ricciOneUp t x₀ a b =
        ∑ q : CoordinateIdx (𝕜 := Real) E,
          coordInv (I := I) S x₀ t x₀ b q *
            ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀ a q)
    (hcomm : RicCommAt
      (DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
        (I := I) (S.family.connection t) x₀)
      (ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀)
      (nabla2Ric t x₀))
    (hin : Rm04LapIn (coordInv (I := I) S x₀ t x₀) (Rm04 t x₀)
      (ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀)
      (nabla2Ric t x₀) (nabla2Rm t x₀))
    (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    rm04VarRHS (I := I) S x₀ nabla2Ric t m
      = rmLap (coordInv (I := I) S x₀ t x₀) (nabla2Rm t x₀) (m 0) (m 1) (m 2) (m 3)
        - 2 * (uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) Rm04 t x₀
                (m 0) (m 1) (m 2) (m 3)
            - uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) Rm04 t x₀
                (m 0) (m 1) (m 3) (m 2)
            + uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) Rm04 t x₀
                (m 0) (m 2) (m 1) (m 3)
            - uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) Rm04 t x₀
                (m 0) (m 3) (m 1) (m 2))
        - riemann04RicciDriftInFrame ricciOneUp Rm04 t x₀ (m 0) (m 1) (m 2) (m 3) := by
  have hb : ∀ a b c d : CoordinateIdx (𝕜 := Real) E,
      uhlenbeckBTensorInFrame (coordInv (I := I) S x₀) Rm04 t x₀ a b c d
        = bComp (coordInv (I := I) S x₀ t x₀) (Rm04 t x₀) a b c d := fun _ _ _ _ => rfl
  have hd : riemann04RicciDriftInFrame ricciOneUp Rm04 t x₀ (m 0) (m 1) (m 2) (m 3)
      = rmDrift (ricciOneUp t x₀) (Rm04 t x₀) (m 0) (m 1) (m 2) (m 3) := rfl
  have hv : rm04VarRHS (I := I) S x₀ nabla2Ric t m
      = rmVar
          (metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀)
          (coordInv (I := I) S x₀ t x₀)
          (ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀)
          (DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
            (I := I) (S.family.connection t) x₀)
          (nabla2Ric t x₀) (m 0) (m 1) (m 2) (m 3) := rfl
  rw [hv, hd, hb, hb, hb, hb]
  exact rmVar_eq_uhl
    (metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀)
    (coordInv (I := I) S x₀ t x₀)
    (ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x₀)
    (ricciOneUp t x₀)
    (DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt
      (I := I) (S.family.connection t) x₀)
    (Rm04 t x₀) (nabla2Ric t x₀) (nabla2Rm t x₀)
    hsym hgi hricsym hcon hraise hRup hcomm hin (m 0) (m 1) (m 2) (m 3)

end Solution

end DifferentialGeometry.PDE.RicciFlow
