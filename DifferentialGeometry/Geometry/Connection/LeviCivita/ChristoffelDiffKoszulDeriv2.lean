import DifferentialGeometry.Geometry.Connection.LeviCivita.ChristoffelDiffKoszulDeriv

/-!
# The a=2 differentiated Christoffel-difference Koszul identity (`connDiff_koszul_deriv2`)

This leaf differentiates the a=1 lowered-eval Koszul identity `connDiff_koszul_deriv`
(`ChristoffelDiffKoszulDeriv.lean`) once more, along a new base direction `V`, under
`∇₂ = LeviCivita g₂`.  It discharges the FRONTIER ingredient of
`HCGCompactness/ConnDiffDeriv2Bound.lean` (`covStepDiff2_exists_const`): the a=2 base-Leibniz jet of a
single connection-difference step needs the second base covariant derivative of the connection
difference `A = Γ₁ − Γ₂`, controlled in `metricCovDeriv` currency at order 3.

The differentiation reuses the SAME generic engine `nabla0SFun_eval_smooth_slots` one order up: the
three `∇₂²g₁` combos of the a=1 RHS become `∇₂³g₁` combos (via the next-order combo engine
`nablaMetric_combo_extDeriv2` here), and the quadratic `(∇₂_W g₁)(A,·)` term differentiates by the
EXISTING a=1 `nablaMetric_combo_extDeriv` into the split quadratic `∇₂²g₁·A + ∇₂g₁·∇₂A`.  See
`ChristoffelDiffKoszulDeriv2.md` for the full route and reusability finding.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- **Order-3 regularity of the metric jet field** `field₂ = ∇₂²g₁`.  The second total covariant
derivative (Levi-Civita of `g₂`) of `mtf g₁` — i.e. the `∇₂`-total derivative of the a=1 jet field
`field₁ = totalNabla0S 2 (LC g₂)(mtf g₁)` — is a smooth `(0,4)` field.  Directly from `totalNabla0S_reg`
one order above `metricField_totalReg`. -/
theorem metricField_totalReg2
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M) :
    Tensor0SBundle.TotalNabla0SRegular (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
      (LeviCivita (I := I) g₂)
      (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
        (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
        (metricField_totalReg (I := I) g₁ g₂)) :=
  Tensor0SBundle.totalNabla0S_reg (I := I) 3 (LeviCivita (I := I) g₂)
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g₂)
    (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
      (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
      (metricField_totalReg (I := I) g₁ g₂))

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- **One combo term of the twice-differentiated Koszul RHS.**  The directional derivative along `W` of
a `∇₂²g₁` combo term `nabla0SFun 3 (LC g₂) (V 0) field₁ · (slots)` (direction `V 0`, slots `V 1..3`)
equals the third covariant derivative `∇₂³g₁` (`nabla0SFun 4 (LC g₂) W field₂`) plus the Leibniz slot
corrections, by `nabla0SFun_eval_smooth_slots` on the bundled `∇₂²g₁` field `field₂`.  This is the
next-order mirror of `nablaMetric_combo_extDeriv`; the three `∇₂²g₁` combos of `connDiff_koszul_deriv`
are its instances at `V = ![W,X,Y,Z]`, `![W,Y,X,Z]`, `![W,Z,X,Y]`. -/
theorem nablaMetric_combo_extDeriv2
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (V : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (W : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
          (LeviCivita (I := I) g₂) (V 0)
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
            (metricField_totalReg (I := I) g₁ g₂)) p
          (fun q : Fin 3 => V q.succ p)) x (W x) =
      Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
          (LeviCivita (I := I) g₂) W
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
            (LeviCivita (I := I) g₂)
            (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
              (metricField_totalReg (I := I) g₁ g₂))
            (metricField_totalReg2 (I := I) g₁ g₂)) x
          (fun a : Fin 4 => V a x) +
        ∑ a : Fin 4,
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
            (LeviCivita (I := I) g₂)
            (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
              (metricField_totalReg (I := I) g₁ g₂))
            (metricField_totalReg2 (I := I) g₁ g₂)) x
            (Function.update (fun b : Fin 4 => V b x) a
              (((LeviCivita (I := I) g₂) (fun p : M => V a p) x) (W x))) := by
  classical
  set α := Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
    (LeviCivita (I := I) g₂)
    (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
      (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
      (metricField_totalReg (I := I) g₁ g₂))
    (metricField_totalReg2 (I := I) g₁ g₂) with hαdef
  have hbridge : (fun p : M => α p (fun a : Fin 4 => V a p)) =
      (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
        (LeviCivita (I := I) g₂) (V 0)
        (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
          (metricField_totalReg (I := I) g₁ g₂)) p
        (fun q : Fin 3 => V q.succ p)) := by
    funext p
    rw [hαdef, Tensor0SBundle.totalNabla0S_apply,
      show (fun a : Fin 4 => V a p) =
          Fin.cons ((V 0) p) (fun q : Fin 3 => (V q.succ) p) from
        (Fin.cons_self_tail (fun a : Fin 4 => V a p)).symm,
      Tensor0SBundle.totalNabla0SFun_apply_section]
  rw [Tensor0SBundle.nabla0SFun_eval_smooth_slots (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (LeviCivita (I := I) g₂) W V α x, hbridge]
  abel

/-- **The a=2 differentiated Christoffel-difference Koszul identity (master form).**  Differentiate the
a=1 lowered-eval identity `connDiff_koszul_deriv` once more along a new base direction `V` under
`∇₂ = LeviCivita g₂`.  The left-hand side is `∂_V` of the a=1 pairing `2 g₁(∇₂A(W,X,Y), Z)` (the second
base covariant derivative of the connection difference `A = Γ₁ − Γ₂`, paired with `Z`); the right-hand
side is the a=1 right-hand side differentiated once more, staying in `nabla0SFun`/`metricCovDeriv`
currency:

* the three `∇₂²g₁` combos of the a=1 RHS become **`∇₂³g₁` combos** `nabla0SFun 4 (LC g₂) V field₂`
  (`field₂ = ∇₂²g₁`) plus their Leibniz slot corrections (via `nablaMetric_combo_extDeriv2`);
* the quadratic `(∇₂_W g₁)(A, Z)` term differentiates into the **split quadratic** — the leading
  `∇₂²g₁·A` term `nabla0SFun 3 (LC g₂) V field₁ x ![W, A(Y,X), Z]` (`field₁ = ∇₂g₁`), the middle
  Leibniz correction `∇₂g₁·∇₂A` `field₁ x ![W, ∇₂_V A(Y,X), Z]`, and the two outer slot corrections
  (via the EXISTING a=1 `nablaMetric_combo_extDeriv`).

This is the "second base-connection differentiation" of `ConnDiffDeriv2Bound.md §2`.  The clean form
`2 g₁(covDerivConnDiff2, Z) = …` (isolating the fully covariant `∇₂²A` by absorbing the slot
corrections through `koszul_field`, mirroring how the a=1 clean form absorbs its corrections) is the
downstream refinement consumed by the a=2 dual core; it collapses this master identity by the same
bookkeeping the a=1 proof used one order up. -/
theorem connDiff_koszul_deriv2
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (V W X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun p : M => 2 * g₁.inner p (covDerivConnDiff (I := I) g₂ g₁ W X Y p) (Z p)) x (V x) =
      (Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
          (LeviCivita (I := I) g₂) V
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
            (LeviCivita (I := I) g₂)
            (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
              (metricField_totalReg (I := I) g₁ g₂))
            (metricField_totalReg2 (I := I) g₁ g₂)) x ![W x, X x, Y x, Z x] +
        ∑ a : Fin 4,
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
            (LeviCivita (I := I) g₂)
            (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
              (metricField_totalReg (I := I) g₁ g₂))
            (metricField_totalReg2 (I := I) g₁ g₂)) x
            (Function.update
              (fun b : Fin 4 =>
                ((![W, X, Y, Z] : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
                    (TangentSpace I : M → Type _)) b) x) a
              (((LeviCivita (I := I) g₂)
                  (fun p : M =>
                    ((![W, X, Y, Z] : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
                      (TangentSpace I : M → Type _)) a) p) x) (V x)))) +
      (Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
          (LeviCivita (I := I) g₂) V
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
            (LeviCivita (I := I) g₂)
            (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
              (metricField_totalReg (I := I) g₁ g₂))
            (metricField_totalReg2 (I := I) g₁ g₂)) x ![W x, Y x, X x, Z x] +
        ∑ a : Fin 4,
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
            (LeviCivita (I := I) g₂)
            (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
              (metricField_totalReg (I := I) g₁ g₂))
            (metricField_totalReg2 (I := I) g₁ g₂)) x
            (Function.update
              (fun b : Fin 4 =>
                ((![W, Y, X, Z] : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
                    (TangentSpace I : M → Type _)) b) x) a
              (((LeviCivita (I := I) g₂)
                  (fun p : M =>
                    ((![W, Y, X, Z] : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
                      (TangentSpace I : M → Type _)) a) p) x) (V x)))) -
      (Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
          (LeviCivita (I := I) g₂) V
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
            (LeviCivita (I := I) g₂)
            (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
              (metricField_totalReg (I := I) g₁ g₂))
            (metricField_totalReg2 (I := I) g₁ g₂)) x ![W x, Z x, X x, Y x] +
        ∑ a : Fin 4,
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
            (LeviCivita (I := I) g₂)
            (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
              (metricField_totalReg (I := I) g₁ g₂))
            (metricField_totalReg2 (I := I) g₁ g₂)) x
            (Function.update
              (fun b : Fin 4 =>
                ((![W, Z, X, Y] : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
                    (TangentSpace I : M → Type _)) b) x) a
              (((LeviCivita (I := I) g₂)
                  (fun p : M =>
                    ((![W, Z, X, Y] : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
                      (TangentSpace I : M → Type _)) a) p) x) (V x)))) -
      2 * (Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
            (LeviCivita (I := I) g₂) V
            (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
              (metricField_totalReg (I := I) g₁ g₂)) x
            ![W x,
              (CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x)
                (Y x) (X x), Z x] +
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
            (metricField_totalReg (I := I) g₁ g₂)) x
            ![((LeviCivita (I := I) g₂) (fun p : M => W p) x) (V x),
              (CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x)
                (Y x) (X x), Z x] +
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
            (metricField_totalReg (I := I) g₁ g₂)) x
            ![W x,
              ((LeviCivita (I := I) g₂)
                (fun p : M =>
                  (CovariantDerivative.difference (LeviCivita (I := I) g₁)
                    (LeviCivita (I := I) g₂) p) (Y p) (X p)) x) (V x), Z x] +
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
            (metricField_totalReg (I := I) g₁ g₂)) x
            ![W x,
              (CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x)
                (Y x) (X x), ((LeviCivita (I := I) g₂) (fun p : M => Z p) x) (V x)]) := by
  classical
  -- The connection-difference section `A(X,Y) = ∇₂-difference of X against Y`, smooth.
  have hAsm : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (diffSec (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
        (fun b => X b) (fun b => Y b))) :=
    diffSec_contMDiff (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁) X.contMDiff
      (by rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
          exact Y.contMDiff)
  set Adiff : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (diffSec (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
      (fun b => X b) (fun b => Y b)) hAsm with hAdiff
  have hDA : ∀ p : M, (CovariantDerivative.difference (LeviCivita (I := I) g₁)
      (LeviCivita (I := I) g₂) p) (Y p) (X p) = Adiff p := fun _ => rfl
  -- Slot normalisers (field-free).
  have e4x : ∀ (a b c d : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      (fun i : Fin 4 => ((![a, b, c, d] : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)) i) x) = ![a x, b x, c x, d x] := by
    intro a b c d; funext i; fin_cases i <;> rfl
  have e3x : ∀ (a b c : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      (fun i : Fin 3 => ((![a, b, c] : Fin 3 → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)) i) x) = ![a x, b x, c x] := by
    intro a b c; funext i; fin_cases i <;> rfl
  have hup0 : ∀ (v a b c : TangentSpace I x),
      Function.update (![a, b, c] : Fin 3 → TangentSpace I x) 0 v = ![v, b, c] := by
    intro v a b c; funext i; fin_cases i <;> simp
  have hup1 : ∀ (v a b c : TangentSpace I x),
      Function.update (![a, b, c] : Fin 3 → TangentSpace I x) 1 v = ![a, v, c] := by
    intro v a b c; funext i; fin_cases i <;> simp
  have hup2 : ∀ (v a b c : TangentSpace I x),
      Function.update (![a, b, c] : Fin 3 → TangentSpace I x) 2 v = ![a, b, v] := by
    intro v a b c; funext i; fin_cases i <;> simp
  -- Differentiate the a=1 identity along `V`, then move to the `Adiff` form of its quadratic slot.
  have hmaster := congrArg (fun f : M → ℝ => extDerivFun (I := I) f x (V x))
    (funext (fun p => connDiff_koszul_deriv (I := I) g₁ g₂ W X Y Z p))
  simp only [hDA] at hmaster
  -- Differentiability of a `field₂`/`field₁`-eval on smooth slots, bridged to the `nabla0SFun` form.
  have hMDgen4 : ∀ (Vt : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
          (LeviCivita (I := I) g₂) (Vt 0)
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
            (metricField_totalReg (I := I) g₁ g₂)) p (fun q : Fin 3 => Vt q.succ p)) x := by
    intro Vt
    have hbr : (fun p : M =>
          Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
            (LeviCivita (I := I) g₂)
            (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
              (metricField_totalReg (I := I) g₁ g₂)) (metricField_totalReg2 (I := I) g₁ g₂) p
            (fun a : Fin 4 => Vt a p))
        = (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
            (LeviCivita (I := I) g₂) (Vt 0)
            (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
              (metricField_totalReg (I := I) g₁ g₂)) p (fun q : Fin 3 => Vt q.succ p)) := by
      funext p
      rw [Tensor0SBundle.totalNabla0S_apply,
        show (fun a : Fin 4 => Vt a p) = Fin.cons ((Vt 0) p) (fun q : Fin 3 => (Vt q.succ) p) from
          (Fin.cons_self_tail (fun a : Fin 4 => Vt a p)).symm,
        Tensor0SBundle.totalNabla0SFun_apply_section]
    rw [← hbr]
    exact (Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) _ Vt x).mdifferentiableAt (by simp)
  have hMDgen3 : ∀ (Vt : Fin 3 → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) (Vt 0) (Tensor0SBundle.metricTensorField (I := I) g₁) p
          (fun q : Fin 2 => Vt q.succ p)) x := by
    intro Vt
    have hbr : (fun p : M =>
          Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
            (metricField_totalReg (I := I) g₁ g₂) p (fun a : Fin 3 => Vt a p))
        = (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) (Vt 0) (Tensor0SBundle.metricTensorField (I := I) g₁) p
            (fun q : Fin 2 => Vt q.succ p)) := by
      funext p
      rw [Tensor0SBundle.totalNabla0S_apply,
        show (fun a : Fin 3 => Vt a p) = Fin.cons ((Vt 0) p) (fun q : Fin 2 => (Vt q.succ) p) from
          (Fin.cons_self_tail (fun a : Fin 3 => Vt a p)).symm,
        Tensor0SBundle.totalNabla0SFun_apply_section]
    rw [← hbr]
    exact (Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) _ Vt x).mdifferentiableAt (by simp)
  -- Slot-form normalisation of the `nabla0SFun` directional forms.
  have hV4 : ∀ (a b c d : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
          (LeviCivita (I := I) g₂)
          ((![a, b, c, d] : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
            (TangentSpace I : M → Type _)) 0)
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
            (metricField_totalReg (I := I) g₁ g₂)) p
          (fun q : Fin 3 =>
            (![a, b, c, d] : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
              (TangentSpace I : M → Type _)) q.succ p))
        = (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
            (LeviCivita (I := I) g₂) a
            (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
              (metricField_totalReg (I := I) g₁ g₂)) p ![b p, c p, d p]) := by
    intro a b c d; funext p
    have hs : (fun q : Fin 3 =>
        (![a, b, c, d] : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _)) q.succ p) = ![b p, c p, d p] := by
      funext q; fin_cases q <;> rfl
    rw [hs, Matrix.cons_val_zero]
  have hV3 : ∀ (a b c : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂)
          ((![a, b, c] : Fin 3 → ContMDiffSection I E (∞ : WithTop ℕ∞)
            (TangentSpace I : M → Type _)) 0) (Tensor0SBundle.metricTensorField (I := I) g₁) p
          (fun q : Fin 2 =>
            (![a, b, c] : Fin 3 → ContMDiffSection I E (∞ : WithTop ℕ∞)
              (TangentSpace I : M → Type _)) q.succ p))
        = (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) a (Tensor0SBundle.metricTensorField (I := I) g₁) p
            ![b p, c p]) := by
    intro a b c; funext p
    have hs : (fun q : Fin 2 =>
        (![a, b, c] : Fin 3 → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _)) q.succ p) = ![b p, c p] := by
      funext q; fin_cases q <;> rfl
    rw [hs, Matrix.cons_val_zero]
  have hMD1 := hV4 W X Y Z ▸ hMDgen4 ![W, X, Y, Z]
  have hMD2 := hV4 W Y X Z ▸ hMDgen4 ![W, Y, X, Z]
  have hMD3 := hV4 W Z X Y ▸ hMDgen4 ![W, Z, X, Y]
  have hMD4 := hV3 W Adiff Z ▸ hMDgen3 ![W, Adiff, Z]
  -- The four combo-derivative results, normalised to the a=1-RHS slot forms.
  have hR1 := nablaMetric_combo_extDeriv2 (I := I) g₁ g₂ ![W, X, Y, Z] V x
  have hR2 := nablaMetric_combo_extDeriv2 (I := I) g₁ g₂ ![W, Y, X, Z] V x
  have hR3 := nablaMetric_combo_extDeriv2 (I := I) g₁ g₂ ![W, Z, X, Y] V x
  have hR4 := nablaMetric_combo_extDeriv (I := I) g₁ g₂ ![W, Adiff, Z] V x
  rw [hV4 W X Y Z, e4x W X Y Z] at hR1
  rw [hV4 W Y X Z, e4x W Y X Z] at hR2
  rw [hV4 W Z X Y, e4x W Z X Y] at hR3
  rw [hV3 W Adiff Z, e3x W Adiff Z] at hR4
  -- Linearity split of the exterior derivative over the a=1 RHS sum.
  have hsub' : ∀ {f g : M → ℝ}, MDifferentiableAt I 𝓘(ℝ, ℝ) f x →
      MDifferentiableAt I 𝓘(ℝ, ℝ) g x →
      extDerivFun (I := I) (f - g) x = extDerivFun (I := I) f x - extDerivFun (I := I) g x := by
    intro f g hf hg
    have h := extDerivFun_add (I := I) (g := f - g) (g' := g) (hf.sub hg) hg
    rw [sub_add_cancel] at h
    exact eq_sub_of_add_eq h.symm
  have hMD4' : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun p : M => (2 : ℝ) * Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
        (LeviCivita (I := I) g₂) W (Tensor0SBundle.metricTensorField (I := I) g₁) p
        ![Adiff p, Z p]) x :=
    (mdifferentiableAt_const (I := I) (I' := 𝓘(ℝ, ℝ)) (c := (2 : ℝ))).mul hMD4
  rw [show (fun p : M =>
        Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
            (LeviCivita (I := I) g₂) W
            (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
              (metricField_totalReg (I := I) g₁ g₂)) p ![X p, Y p, Z p]
          + Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
            (LeviCivita (I := I) g₂) W
            (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
              (metricField_totalReg (I := I) g₁ g₂)) p ![Y p, X p, Z p]
          - Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
            (LeviCivita (I := I) g₂) W
            (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
              (metricField_totalReg (I := I) g₁ g₂)) p ![Z p, X p, Y p]
          - 2 * Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) W (Tensor0SBundle.metricTensorField (I := I) g₁) p
            ![Adiff p, Z p])
        = (((fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
              (LeviCivita (I := I) g₂) W
              (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
                (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
                (metricField_totalReg (I := I) g₁ g₂)) p ![X p, Y p, Z p])
            + (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
              (LeviCivita (I := I) g₂) W
              (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
                (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
                (metricField_totalReg (I := I) g₁ g₂)) p ![Y p, X p, Z p]))
            - (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
              (LeviCivita (I := I) g₂) W
              (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
                (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
                (metricField_totalReg (I := I) g₁ g₂)) p ![Z p, X p, Y p]))
          - (fun p : M => 2 * Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) W (Tensor0SBundle.metricTensorField (I := I) g₁) p
              ![Adiff p, Z p]) from rfl,
    hsub' ((hMD1.add hMD2).sub hMD3) hMD4',
    hsub' (hMD1.add hMD2) hMD3, extDerivFun_add hMD1 hMD2,
    extDerivFun_const_mul I (2 : ℝ) hMD4] at hmaster
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at hmaster
  rw [hR1, hR2, hR3, hR4] at hmaster
  -- Normalise the quadratic correction sum and match the goal (associativity by `ring`).
  rw [hmaster]
  simp only [e4x, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, hup0, hup1, hup2, hDA]
  ring

end Connection
end Integral
end DifferentialGeometry

end
