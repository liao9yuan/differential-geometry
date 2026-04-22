import DifferentialGeometry.Synthetic.Algebra.VectorFieldAlgebra
import DifferentialGeometry.Synthetic.Realization.Connection
import DifferentialGeometry.VectorBundle.PartialMfderiv
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# SmoothRicciFlow: Time Derivative via Jointly-Smooth Families

Canonical concrete realisation of `TimeDerivativeData` on the algebra
`C^∞⟮I, M; ℝ⟯` with `Time = ℝ`: a family `f : ℝ → C^∞⟮I, M; ℝ⟯` is *smooth*
iff the uncurried map `(t, x) ↦ f t x` is jointly `C^∞` on `ℝ × M`. The lift
embeds such families as elements of `C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; ℝ⟯`, and the
time derivation is partial differentiation along the ℝ-factor.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- Jointly smooth ℝ-valued functions on `ℝ × M`, with the product model. -/
abbrev SmoothTimeAlgebra : Type _ :=
  C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; ℝ⟯

/-- The ring homomorphism `f ↦ f.comp ContMDiffMap.snd` from `C^∞⟮I, M; ℝ⟯` into
`SmoothTimeAlgebra I M`. -/
def compSndRingHom : C^∞⟮I, M; ℝ⟯ →+* SmoothTimeAlgebra I M where
  toFun f := f.comp (ContMDiffMap.snd : C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯)
  map_one' := by
    ext p
    simp [ContMDiffMap.comp_apply, ContMDiffMap.coe_one]
  map_mul' f g := by
    ext p
    simp [ContMDiffMap.comp_apply, ContMDiffMap.coe_mul, Pi.mul_apply]
  map_zero' := by
    ext p
    simp [ContMDiffMap.comp_apply, ContMDiffMap.coe_zero]
  map_add' f g := by
    ext p
    simp [ContMDiffMap.comp_apply, ContMDiffMap.coe_add, Pi.add_apply]

/-- The `C^∞⟮I, M; ℝ⟯`-algebra structure on `SmoothTimeAlgebra I M` obtained by
pulling back along the second projection. -/
noncomputable instance : Algebra C^∞⟮I, M; ℝ⟯ (SmoothTimeAlgebra I M) :=
  (compSndRingHom I M).toAlgebra

/-- A family `f : ℝ → C^∞⟮I, M; ℝ⟯` is a *smooth family* when the uncurried
map `(t, x) ↦ f t x` is jointly `C^∞` on `ℝ × M`. -/
def concreteIsSmoothFam (f : ℝ → C^∞⟮I, M; ℝ⟯) : Prop :=
  ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => f p.1 p.2)

/-- Constant families are smooth. -/
theorem concreteIsSmoothFam_const (c : C^∞⟮I, M; ℝ⟯) :
    concreteIsSmoothFam I M (fun _ => c) := by
  change ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => c p.2)
  exact c.contMDiff.comp contMDiff_snd

/-- Smooth families are closed under pointwise addition. -/
theorem concreteIsSmoothFam_add (f g : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam I M f) (hg : concreteIsSmoothFam I M g) :
    concreteIsSmoothFam I M (f + g) := by
  change ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => (f + g) p.1 p.2)
  have heq : (fun p : ℝ × M => (f + g) p.1 p.2) =
      (fun p : ℝ × M => f p.1 p.2) + (fun p : ℝ × M => g p.1 p.2) := by
    funext p
    change (f p.1 + g p.1) p.2 = f p.1 p.2 + g p.1 p.2
    simp [ContMDiffMap.coe_add]
  rw [heq]
  exact hf.add hg

/-- Smooth families are closed under pointwise multiplication. -/
theorem concreteIsSmoothFam_mul (f g : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam I M f) (hg : concreteIsSmoothFam I M g) :
    concreteIsSmoothFam I M (f * g) := by
  change ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => (f * g) p.1 p.2)
  have heq : (fun p : ℝ × M => (f * g) p.1 p.2) =
      (fun p : ℝ × M => f p.1 p.2) * (fun p : ℝ × M => g p.1 p.2) := by
    funext p
    change (f p.1 * g p.1) p.2 = f p.1 p.2 * g p.1 p.2
    simp [ContMDiffMap.coe_mul]
  rw [heq]
  exact hf.mul hg

/-- Smooth families are closed under pointwise negation. -/
theorem concreteIsSmoothFam_neg (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam I M f) :
    concreteIsSmoothFam I M (-f) := by
  change ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => (-f) p.1 p.2)
  have heq : (fun p : ℝ × M => (-f) p.1 p.2) =
      (fun p : ℝ × M => -(f p.1 p.2)) := by
    funext p
    change (-(f p.1)) p.2 = -(f p.1 p.2)
    simp [ContMDiffMap.coe_neg]
  rw [heq]
  exact hf.neg

/-- Lift a smooth family to a `SmoothTimeAlgebra` element; collapse to 0
on non-smooth families. -/
noncomputable def concreteLift (f : ℝ → C^∞⟮I, M; ℝ⟯) : SmoothTimeAlgebra I M :=
  open Classical in
  if h : concreteIsSmoothFam I M f then
    ⟨fun p : ℝ × M => f p.1 p.2, h⟩
  else 0

/-- When `f` is a smooth family, `concreteLift I M f` has the expected underlying
function `(t, x) ↦ f t x`. -/
theorem concreteEval_concreteLift_apply (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam I M f) :
    (concreteLift I M f : ℝ × M → ℝ) = fun p => f p.1 p.2 := by
  simp only [concreteLift, dif_pos hf, ContMDiffMap.coeFn_mk]

/-- `concreteLift` is additive on smooth families. -/
theorem concreteLift_add (f g : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam I M f) (hg : concreteIsSmoothFam I M g) :
    concreteLift I M (f + g) = concreteLift I M f + concreteLift I M g := by
  have hfg : concreteIsSmoothFam I M (f + g) := concreteIsSmoothFam_add I M f g hf hg
  ext p
  have lhs_eq := congrFun (concreteEval_concreteLift_apply I M (f + g) hfg) p
  have f_eq := congrFun (concreteEval_concreteLift_apply I M f hf) p
  have g_eq := congrFun (concreteEval_concreteLift_apply I M g hg) p
  -- `ContMDiffMap.ext` turned the goal into pointwise equality of coerced functions at `p`.
  simp only [ContMDiffMap.coe_add, Pi.add_apply] at *
  rw [lhs_eq, f_eq, g_eq]

/-- `concreteLift` is multiplicative on smooth families. -/
theorem concreteLift_mul (f g : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam I M f) (hg : concreteIsSmoothFam I M g) :
    concreteLift I M (f * g) = concreteLift I M f * concreteLift I M g := by
  have hfg : concreteIsSmoothFam I M (f * g) := concreteIsSmoothFam_mul I M f g hf hg
  ext p
  have lhs_eq := congrFun (concreteEval_concreteLift_apply I M (f * g) hfg) p
  have f_eq := congrFun (concreteEval_concreteLift_apply I M f hf) p
  have g_eq := congrFun (concreteEval_concreteLift_apply I M g hg) p
  simp only [ContMDiffMap.coe_mul, Pi.mul_apply] at *
  rw [lhs_eq, f_eq, g_eq]

/-- `concreteLift` of a constant family equals the algebra-map image of the
constant. -/
theorem concreteLift_algebraMap (c : C^∞⟮I, M; ℝ⟯) :
    concreteLift I M (fun _ => c) =
      algebraMap C^∞⟮I, M; ℝ⟯ (SmoothTimeAlgebra I M) c := by
  have hc : concreteIsSmoothFam I M (fun _ => c) := concreteIsSmoothFam_const I M c
  ext p
  have lhs_eq := congrFun (concreteEval_concreteLift_apply I M (fun _ => c) hc) p
  rw [lhs_eq]
  -- RHS reduces to `c.comp ContMDiffMap.snd` by the RingHom.toAlgebra instance
  change c p.2 =
      ((c.comp (ContMDiffMap.snd :
        C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯)) : ℝ × M → ℝ) p
  simp [ContMDiffMap.comp_apply, ContMDiffMap.snd]

/-- Partial evaluation at a fixed time `t`, producing a smooth function on `M`. -/
noncomputable def concreteEval (F : SmoothTimeAlgebra I M) (t : ℝ) : C^∞⟮I, M; ℝ⟯ :=
  ⟨fun x => F (t, x),
    F.contMDiff.comp ((contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => t)).prodMk
      (contMDiff_id : ContMDiff I I ∞ (id : M → M)))⟩

/-- `concreteEval` is additive. -/
theorem concreteEval_add (F G : SmoothTimeAlgebra I M) (t : ℝ) :
    concreteEval I M (F + G) t = concreteEval I M F t + concreteEval I M G t := by
  ext x
  change (F + G) (t, x) = F (t, x) + G (t, x)
  simp [ContMDiffMap.coe_add]

/-- `concreteEval` is multiplicative. -/
theorem concreteEval_mul (F G : SmoothTimeAlgebra I M) (t : ℝ) :
    concreteEval I M (F * G) t = concreteEval I M F t * concreteEval I M G t := by
  ext x
  change (F * G) (t, x) = F (t, x) * G (t, x)
  simp [ContMDiffMap.coe_mul]

/-- `concreteEval` agrees with the algebra map on constant-in-time elements. -/
theorem concreteEval_algebraMap (c : C^∞⟮I, M; ℝ⟯) (t : ℝ) :
    concreteEval I M (algebraMap C^∞⟮I, M; ℝ⟯ (SmoothTimeAlgebra I M) c) t = c := by
  ext x
  change ((algebraMap C^∞⟮I, M; ℝ⟯ (SmoothTimeAlgebra I M) c :
    SmoothTimeAlgebra I M) : ℝ × M → ℝ) (t, x) = c x
  change ((compSndRingHom I M c : SmoothTimeAlgebra I M) : ℝ × M → ℝ) (t, x) = c x
  change ((c.comp (ContMDiffMap.snd :
      C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯)) : ℝ × M → ℝ) (t, x) = c x
  simp [ContMDiffMap.comp_apply, ContMDiffMap.snd]

/-- Round-trip: evaluating the lift of a smooth family at time `t` recovers `f t`. -/
theorem concreteEval_concreteLift (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam I M f) (t : ℝ) :
    concreteEval I M (concreteLift I M f) t = f t := by
  ext x
  change (concreteLift I M f : ℝ × M → ℝ) (t, x) = f t x
  rw [concreteEval_concreteLift_apply I M f hf]

-- ============================================================
-- Partial derivative along the ℝ factor as a SmoothTimeAlgebra element
-- ============================================================

/-- Pointwise partial t-derivative packaged back into `SmoothTimeAlgebra`. -/
noncomputable def concreteDtFun (F : SmoothTimeAlgebra I M) : SmoothTimeAlgebra I M :=
  ⟨fun p : ℝ × M => deriv (fun t : ℝ => F (t, p.2)) p.1,
   DifferentialGeometry.contMDiff_partial_deriv_fst I F⟩

/-- For any `x : M`, the real-valued function `t ↦ F (t, x)` is `C^∞`. -/
private theorem concreteDt_slice_contDiff (F : SmoothTimeAlgebra I M) (x : M) :
    ContDiff ℝ ∞ (fun s : ℝ => F (s, x)) := by
  rw [← contMDiff_iff_contDiff]
  exact F.contMDiff.comp
    ((contMDiff_id : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (id : ℝ → ℝ)).prodMk
      (contMDiff_const : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun _ : ℝ => x)))

/-- For any `x : M` and `t : ℝ`, the slice `s ↦ F (s, x)` is differentiable at `t`. -/
private theorem concreteDt_slice_differentiableAt
    (F : SmoothTimeAlgebra I M) (x : M) (t : ℝ) :
    DifferentiableAt ℝ (fun s : ℝ => F (s, x)) t :=
  ((concreteDt_slice_contDiff I M F x).differentiable (by decide)).differentiableAt

/-- `concreteDtFun` is additive. -/
private theorem concreteDtFun_add (F G : SmoothTimeAlgebra I M) :
    concreteDtFun I M (F + G) = concreteDtFun I M F + concreteDtFun I M G := by
  ext p
  -- Expand the LHS and RHS to pointwise expressions.
  change deriv (fun s : ℝ => (F + G) (s, p.2)) p.1 =
      deriv (fun s : ℝ => F (s, p.2)) p.1 +
        deriv (fun s : ℝ => G (s, p.2)) p.1
  have hslice : (fun s : ℝ => (F + G) (s, p.2)) =
      (fun s : ℝ => F (s, p.2)) + (fun s : ℝ => G (s, p.2)) := by
    funext s
    change (F + G) (s, p.2) = F (s, p.2) + G (s, p.2)
    rw [ContMDiffMap.coe_add]; rfl
  rw [hslice,
      deriv_add (concreteDt_slice_differentiableAt I M F p.2 p.1)
        (concreteDt_slice_differentiableAt I M G p.2 p.1)]

/-- `concreteDtFun` commutes with scalar multiplication by `C^∞⟮I, M; ℝ⟯`. -/
private theorem concreteDtFun_smul (c : C^∞⟮I, M; ℝ⟯) (F : SmoothTimeAlgebra I M) :
    concreteDtFun I M (c • F) = c • concreteDtFun I M F := by
  ext p
  -- `c • F = (compSndRingHom I M c) * F` by definition of the `RingHom.toAlgebra` algebra.
  -- Expand both sides at `p`.
  change deriv (fun s : ℝ => (c • F) (s, p.2)) p.1 =
      (c • concreteDtFun I M F) p
  -- Rewrite the RHS: `c • _` unfolds to `(compSndRingHom I M c) * _`, then at `p`
  -- this is `c p.2 * (concreteDtFun I M F) p`.
  have hrhs : (c • concreteDtFun I M F) p = c p.2 * deriv (fun s : ℝ => F (s, p.2)) p.1 := by
    change (compSndRingHom I M c * concreteDtFun I M F) p =
        c p.2 * deriv (fun s : ℝ => F (s, p.2)) p.1
    rw [ContMDiffMap.coe_mul]
    change (compSndRingHom I M c) p * (concreteDtFun I M F) p =
        c p.2 * deriv (fun s : ℝ => F (s, p.2)) p.1
    rfl
  rw [hrhs]
  -- Rewrite the LHS slice to `c p.2 * F (s, p.2)`.
  have hslice : (fun s : ℝ => (c • F) (s, p.2)) =
      (fun s : ℝ => c p.2 * F (s, p.2)) := by
    funext s
    change (compSndRingHom I M c * F) (s, p.2) = c p.2 * F (s, p.2)
    rw [ContMDiffMap.coe_mul]
    rfl
  rw [hslice,
      deriv_const_mul (c p.2) (concreteDt_slice_differentiableAt I M F p.2 p.1)]

/-- `concreteDtFun` satisfies the Leibniz rule. -/
private theorem concreteDtFun_mul (F G : SmoothTimeAlgebra I M) :
    concreteDtFun I M (F * G) =
      F * concreteDtFun I M G + G * concreteDtFun I M F := by
  ext p
  -- Rewrite the RHS at `p`.
  have hrhs : (F * concreteDtFun I M G + G * concreteDtFun I M F) p =
      F p * deriv (fun s : ℝ => G (s, p.2)) p.1 +
      G p * deriv (fun s : ℝ => F (s, p.2)) p.1 := by
    rw [ContMDiffMap.coe_add, ContMDiffMap.coe_mul, ContMDiffMap.coe_mul]
    rfl
  change deriv (fun s : ℝ => (F * G) (s, p.2)) p.1 =
      (F * concreteDtFun I M G + G * concreteDtFun I M F) p
  rw [hrhs]
  -- Rewrite the LHS slice to a product of slices.
  have hslice : (fun s : ℝ => (F * G) (s, p.2)) =
      (fun s : ℝ => F (s, p.2)) * (fun s : ℝ => G (s, p.2)) := by
    funext s
    change (F * G) (s, p.2) = F (s, p.2) * G (s, p.2)
    rw [ContMDiffMap.coe_mul]; rfl
  rw [hslice,
      deriv_mul (concreteDt_slice_differentiableAt I M F p.2 p.1)
        (concreteDt_slice_differentiableAt I M G p.2 p.1)]
  -- Match the two sides: `F p = F (p.1, p.2)` definitionally.
  have hFp : F p = F (p.1, p.2) := by rfl
  have hGp : G p = G (p.1, p.2) := by rfl
  rw [hFp, hGp]
  ring

/-- `concreteDtFun` sends the constant `1` to `0`. -/
private theorem concreteDtFun_one : concreteDtFun I M 1 = 0 := by
  ext p
  change deriv (fun s : ℝ => (1 : SmoothTimeAlgebra I M) (s, p.2)) p.1 =
      (0 : SmoothTimeAlgebra I M) p
  have hslice : (fun s : ℝ => (1 : SmoothTimeAlgebra I M) (s, p.2)) =
      (fun _ : ℝ => (1 : ℝ)) := by
    funext s
    change (1 : SmoothTimeAlgebra I M) (s, p.2) = (1 : ℝ)
    rw [ContMDiffMap.coe_one]; rfl
  rw [hslice, deriv_const]
  change (0 : ℝ) = (0 : SmoothTimeAlgebra I M) p
  rw [ContMDiffMap.coe_zero]; rfl

/-- The time derivation on `SmoothTimeAlgebra` induced by partial t-differentiation. -/
noncomputable def concreteDt :
    Derivation C^∞⟮I, M; ℝ⟯ (SmoothTimeAlgebra I M) (SmoothTimeAlgebra I M) where
  toLinearMap :=
    { toFun := concreteDtFun I M
      map_add' := concreteDtFun_add I M
      map_smul' := fun c F => concreteDtFun_smul I M c F }
  map_one_eq_zero' := concreteDtFun_one I M
  leibniz' F G := by
    change concreteDtFun I M (F * G) = F • concreteDtFun I M G + G • concreteDtFun I M F
    -- `SmoothTimeAlgebra` acts on itself via `Algebra.toModule`; `•` unfolds to `*`.
    have hF_smul :
        (F : SmoothTimeAlgebra I M) • (concreteDtFun I M G) =
          F * concreteDtFun I M G := smul_eq_mul _ _
    have hG_smul :
        (G : SmoothTimeAlgebra I M) • (concreteDtFun I M F) =
          G * concreteDtFun I M F := smul_eq_mul _ _
    rw [hF_smul, hG_smul]
    exact concreteDtFun_mul I M F G

-- ============================================================
-- Package: TimeDerivativeData on the joint-smooth algebra
-- ============================================================

/-- Concrete `TimeDerivativeData` on the joint-smooth algebra `SmoothTimeAlgebra`. -/
noncomputable def concreteTimeDerivativeData :
    TimeDerivativeData C^∞⟮I, M; ℝ⟯ (SmoothTimeAlgebra I M) ℝ where
  dt := concreteDt I M
  lift := concreteLift I M
  eval := concreteEval I M
  lift_algebraMap := concreteLift_algebraMap I M
  eval_add := concreteEval_add I M
  eval_mul := concreteEval_mul I M
  eval_algebraMap := concreteEval_algebraMap I M

/-- The distinguished `TimeRegularFam` instance for the concrete joint-smooth
    realisation: a family is regular iff it is jointly `C^∞` on `ℝ × M`. -/
noncomputable instance concreteTimeRegularFam :
    TimeRegularFam (concreteTimeDerivativeData I M) where
  isSmoothFam := concreteIsSmoothFam I M
  eval_lift := fun f hf t => concreteEval_concreteLift I M f hf t
  lift_add := concreteLift_add I M
  lift_mul := concreteLift_mul I M
  isSmoothFam_const := concreteIsSmoothFam_const I M
  isSmoothFam_add := concreteIsSmoothFam_add I M
  isSmoothFam_mul := concreteIsSmoothFam_mul I M
  isSmoothFam_neg := concreteIsSmoothFam_neg I M

-- ============================================================
-- Smoothness closure under the embedded vector-field action
-- ============================================================

/-!
### Smoothness of the embedded vector-field action on a smooth family

Given a smooth vector field `X` and a smooth family `f : ℝ → C^∞⟮I, M; ℝ⟯`, the
family `s ↦ (concreteDerivationEmbedding I M).embed X (f s)` — whose underlying
function is `(s, x) ↦ extDerivFun (f s) x (X x)` — is again a smooth family on
`ℝ × M`. This is the smoothness-closure lemma consumed by the Schwarz-type
spatial/temporal commutativity argument.
-/

open Bundle in
/-- The section `(s, x) ↦ ⟨(s, x), (0, X x)⟩` of the tangent bundle of `ℝ × M` is
smooth. It lifts the spatial vector field `X` to a "time-horizontal" vector field
on the product manifold. -/
theorem concreteIsSmoothFam_embed_liftedSection_contMDiff
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
      (fun p : ℝ × M =>
        (TotalSpace.mk' (ℝ × E) p
          ((0, X p.2) :
            TangentSpace (𝓘(ℝ, ℝ).prod I) p) :
          TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) := by
  -- Build the total-space map via the product equivalence
  -- `equivTangentBundleProd.symm : TangentBundle 𝓘(ℝ,ℝ) ℝ × TangentBundle I M →
  --   TangentBundle (𝓘(ℝ,ℝ).prod I) (ℝ × M)`.
  -- Smoothness of the two factors:
  -- `ψ (s, x) = ⟨s, 0⟩ : TangentBundle 𝓘(ℝ,ℝ) ℝ` is `zeroSection ∘ Prod.fst`.
  -- `χ (s, x) = ⟨x, X x⟩ : TangentBundle I M` is `X.contMDiff ∘ Prod.snd`.
  have hψ : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × M =>
        (TotalSpace.mk' ℝ p.1 (0 : TangentSpace 𝓘(ℝ, ℝ) p.1) :
          TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    -- `zeroSection` on the tangent bundle of `𝓘(ℝ, ℝ)` composed with `Prod.fst`.
    have hzero :
        ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
          (zeroSection ℝ (TangentSpace 𝓘(ℝ, ℝ) (M := ℝ))) :=
      Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, ℝ) (M := ℝ))
    exact hzero.comp contMDiff_fst
  have hχ : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M =>
        (TotalSpace.mk' E p.2 (X p.2) :
          TangentBundle I M)) :=
    X.contMDiff.comp contMDiff_snd
  -- Package into a pair, then apply the (smooth) inverse product equivalence.
  have hpair : ContMDiff (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (I.prod 𝓘(ℝ, E))) ∞
      (fun p : ℝ × M =>
        ((TotalSpace.mk' ℝ p.1 (0 : TangentSpace 𝓘(ℝ, ℝ) p.1) :
            TangentBundle 𝓘(ℝ, ℝ) ℝ),
          (TotalSpace.mk' E p.2 (X p.2) :
            TangentBundle I M))) :=
    hψ.prodMk hχ
  have hsymm :
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (I.prod 𝓘(ℝ, E)))
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
        ((equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ I M).symm) :=
    contMDiff_equivTangentBundleProd_symm
  -- The composition yields exactly the desired section.
  exact hsymm.comp hpair

open Bundle in
/-- The family `s ↦ embed X (f s)` is a smooth family whenever `f` is a smooth
family and `X` is a smooth vector field. In the joint-smoothness model this is
precisely smoothness of the map
`(s, x) ↦ extDerivFun (f s) x (X x)` on `ℝ × M`. -/
theorem concreteIsSmoothFam_embed
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam I M f) :
    concreteIsSmoothFam I M
      (fun s => (concreteDerivationEmbedding I M).embed X (f s)) := by
  -- Unfold the embedding to the pointwise vector-field action.
  change ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
    (fun p : ℝ × M =>
      extDerivFun (I := I) ((f p.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) p.2 (X p.2))
  -- Package `f` as a jointly-smooth map `F : ℝ × M → ℝ`.
  set F : SmoothTimeAlgebra I M := concreteLift I M f with hF_def
  have hF_apply : (F : ℝ × M → ℝ) = fun p => f p.1 p.2 :=
    concreteEval_concreteLift_apply I M f hf
  have hF_smooth : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ ((F : ℝ × M → ℝ)) :=
    F.contMDiff
  -- Smoothness of the tangent map of `F`.
  have htangent :
      ContMDiff ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (tangentMap (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ((F : ℝ × M → ℝ))) := by
    apply ContMDiff.contMDiff_tangentMap hF_smooth
    simp
  -- Compose with the lifted section `p ↦ ⟨p, (0, X p.2)⟩`.
  have hlift := concreteIsSmoothFam_embed_liftedSection_contMDiff I M X
  have hcomp :
      ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × M =>
          tangentMap (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ((F : ℝ × M → ℝ))
            (⟨p, ((0, X p.2) : TangentSpace (𝓘(ℝ, ℝ).prod I) p)⟩)) :=
    htangent.comp hlift
  -- Pointwise, extract the fiber via `contMDiffAt_totalSpace`.
  intro p₀
  have hcompAt := hcomp p₀
  rw [contMDiffAt_totalSpace] at hcompAt
  obtain ⟨_, hfiber⟩ := hcompAt
  -- `hfiber` provides smoothness of the model-space-trivialised fiber; on 𝓘(ℝ,ℝ)
  -- the trivialisation is the identity, matching the target up to the
  -- `extDerivFun`/`mfderiv` identification.
  convert hfiber using 1
  -- We now need to identify the two scalar-valued functions of `p`.
  ext p
  -- Compute the RHS at `p` (the fiber coordinate of the tangent map).
  simp only [trivializationAt_model_space_apply, tangentMap]
  -- Reduce `(F : ℝ × M → ℝ) p` using `hF_apply`; likewise for the mfderiv.
  have hFp : (F : ℝ × M → ℝ) p = f p.1 p.2 := by
    simpa using congrFun hF_apply p
  -- The LHS is `extDerivFun (f p.1) p.2 (X p.2)`.
  -- Unfold `extDerivFun` and use the chain rule to rewrite the mfderiv of the
  -- slice as a partial derivative of `F`.
  -- Slice map: `fun y => F (p.1, y)`.
  set s₀ := p.1
  set x₀ := p.2
  -- `(f s₀ : M → ℝ) = fun y => F (s₀, y)`.
  have hSliceFun : ((f s₀ : C^∞⟮I, M; ℝ⟯) : M → ℝ) = fun y => (F : ℝ × M → ℝ) (s₀, y) := by
    funext y; simp [hF_apply, s₀]
  -- Slice-map differentiability and chain rule.
  have hF_diff : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ((F : ℝ × M → ℝ)) (s₀, x₀) :=
    hF_smooth.contMDiffAt.mdifferentiableAt (by simp)
  have hinj_diff : MDifferentiableAt I (𝓘(ℝ, ℝ).prod I)
      (fun y : M => ((s₀, y) : ℝ × M)) x₀ :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  -- Chain rule: `mfderiv (fun y => F (s₀, y)) x₀ = mfderiv F (s₀, x₀) ∘L inr`.
  have hchain :
      mfderiv I 𝓘(ℝ, ℝ) (fun y : M => (F : ℝ × M → ℝ) (s₀, y)) x₀ =
        (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ((F : ℝ × M → ℝ)) (s₀, x₀)).comp
          (ContinuousLinearMap.inr ℝ (TangentSpace 𝓘(ℝ, ℝ) s₀) (TangentSpace I x₀)) := by
    have h :=
      mfderiv_comp (I := I) (I' := 𝓘(ℝ, ℝ).prod I) (I'' := 𝓘(ℝ, ℝ))
        (f := fun y : M => ((s₀, y) : ℝ × M))
        (g := (F : ℝ × M → ℝ))
        (x := x₀) hF_diff hinj_diff
    -- `⇑F ∘ (fun y => (s₀, y))` is definitionally `fun y => F (s₀, y)`.
    change mfderiv I 𝓘(ℝ, ℝ) ((F : ℝ × M → ℝ) ∘ fun y : M => ((s₀, y) : ℝ × M)) x₀ = _
    rw [h, mfderiv_prod_right]
  -- Apply to `X x₀` to get the scalar identity.
  have happly :
      mfderiv I 𝓘(ℝ, ℝ) (fun y : M => (F : ℝ × M → ℝ) (s₀, y)) x₀ (X x₀) =
        mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ((F : ℝ × M → ℝ)) (s₀, x₀)
          ((0, X x₀) : TangentSpace (𝓘(ℝ, ℝ).prod I) (s₀, x₀)) := by
    rw [hchain]
    rfl
  -- Assemble the identification.
  -- RHS reduces to `mfderiv F (s₀, x₀) (0, X x₀)`.
  -- LHS = `extDerivFun (f s₀) x₀ (X x₀)` = `fromTangentSpace ... (mfderiv (f s₀) x₀ (X x₀))`
  -- = `mfderiv (f s₀) x₀ (X x₀)` (fromTangentSpace is identity on ℝ).
  change extDerivFun (I := I) ((f p.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) p.2 (X p.2) = _
  -- Rewrite the slice.
  rw [show ((f p.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) = fun y => (F : ℝ × M → ℝ) (s₀, y) from hSliceFun]
  simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  -- Reduce `NormedSpace.fromTangentSpace` applied to a scalar.
  change (NormedSpace.fromTangentSpace _)
      (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => (F : ℝ × M → ℝ) (s₀, y)) x₀ (X x₀)) = _
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
  -- LHS is now the scalar `mfderiv (fun y => F(s₀, y)) x₀ (X x₀)`.
  rw [happly]
  -- RHS is `mfderiv F p (0, X p.2)` applied. Unfold the `set` markers so the RHS matches.
  rfl

-- ============================================================
-- Spatial/temporal commutativity (Schwarz-type) for SmoothTime
-- ============================================================

/-!
### Spatial/temporal commutativity

The classical Schwarz/Clairaut theorem: for a jointly-smooth family
`f : ℝ → C^∞⟮I, M; ℝ⟯`, partial differentiation in time commutes with the
vector-field action.

With `[I.Boundaryless]`, manifold derivatives at `x₀` collapse to ordinary
Fréchet derivatives pulled back through the chart `φ := extChartAt I x₀`
(because `range I = univ` lets `fderivWithin _ (range I)` reduce to `fderiv`).
The proof then reduces to the ordinary Schwarz equality for the chart
pullback `Ft(s, e) := F(s, φ.symm e)`, obtained via
`ContDiffAt.isSymmSndFDerivAt`.
-/

/-- Chart pullback: writing the jointly-smooth family `F` locally through
the inverse extended chart at `x₀`. -/
private noncomputable def chartPullback
    (F : SmoothTimeAlgebra I M) (x₀ : M) : ℝ × E → ℝ :=
  fun q => (F : ℝ × M → ℝ) (q.1, (extChartAt I x₀).symm q.2)

/-- `chartPullback` is `C^∞` at `(s, e)` for every time `s` and every `e` in
the (open) extended-chart target at `x₀`, when the model is boundaryless. -/
private theorem chartPullback_contDiffAt_of_mem_target [I.Boundaryless]
    (F : SmoothTimeAlgebra I M) (x₀ : M) (s : ℝ) {e : E}
    (he : e ∈ (extChartAt I x₀).target) :
    ContDiffAt ℝ ∞ (chartPullback I M F x₀) (s, e) := by
  -- `(extChartAt I x₀).symm` is `C^∞` at `e` (Boundaryless makes the target open).
  have hmem : (extChartAt I x₀).target ∈ nhds e :=
    (isOpen_extChartAt_target x₀).mem_nhds he
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ ((extChartAt I x₀).symm : E → M) e := by
    have hon : ContMDiffOn 𝓘(ℝ, E) I ∞ ((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀).target :=
      contMDiffOn_extChartAt_symm x₀
    exact (hon _ he).contMDiffAt hmem
  -- Pair with identity on the time factor.  We use `𝓘(ℝ, ℝ × E)` (not the product
  -- model) on the source side so that `contMDiffAt_iff_contDiffAt` applies directly.
  have hfst : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × E => q.1) (s, e) := by
    rw [contMDiffAt_iff_contDiffAt]
    exact (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := E)).contDiffAt
  have hsnd : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) ∞ (fun q : ℝ × E => q.2) (s, e) := by
    rw [contMDiffAt_iff_contDiffAt]
    exact (contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := E)).contDiffAt
  have hsymm_comp : ContMDiffAt 𝓘(ℝ, ℝ × E) I ∞
      (fun q : ℝ × E => (extChartAt I x₀).symm q.2) (s, e) :=
    hsymm.comp (s, e) hsnd
  have hpair :
      ContMDiffAt 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × E => (q.1, (extChartAt I x₀).symm q.2)) (s, e) :=
    hfst.prodMk hsymm_comp
  have hcomp :
      ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞ (chartPullback I M F x₀) (s, e) :=
    F.contMDiff.contMDiffAt.comp (s, e) hpair
  exact hcomp.contDiffAt

/-- `chartPullback` is `C^∞` at `(s, φ x₀)` for every time `s`. -/
private theorem chartPullback_contDiffAt [I.Boundaryless]
    (F : SmoothTimeAlgebra I M) (x₀ : M) (s : ℝ) :
    ContDiffAt ℝ ∞ (chartPullback I M F x₀) (s, extChartAt I x₀ x₀) :=
  chartPullback_contDiffAt_of_mem_target I M F x₀ s
    (mem_of_mem_nhds (extChartAt_target_mem_nhds x₀))

/-- `chartPullback` is `C^2` at `(s, φ x₀)` for every `s`. -/
private theorem chartPullback_contDiffAt_two [I.Boundaryless]
    (F : SmoothTimeAlgebra I M) (x₀ : M) (s : ℝ) :
    ContDiffAt ℝ 2 (chartPullback I M F x₀) (s, extChartAt I x₀ x₀) :=
  (chartPullback_contDiffAt I M F x₀ s).of_le (by
    show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.2 le_top)

/-- Schwarz: the chart pullback has symmetric second Fréchet derivative at
`(t, φ x₀)`. -/
private theorem chartPullback_isSymmSndFDerivAt [I.Boundaryless]
    (F : SmoothTimeAlgebra I M) (x₀ : M) (t : ℝ) :
    IsSymmSndFDerivAt ℝ (chartPullback I M F x₀) (t, extChartAt I x₀ x₀) :=
  (chartPullback_contDiffAt_two I M F x₀ t).isSymmSndFDerivAt (by simp)

/-- `chartPullback` differentiable at `(s, φ x₀)` for any `s`. -/
private theorem chartPullback_differentiableAt [I.Boundaryless]
    (F : SmoothTimeAlgebra I M) (x₀ : M) (s : ℝ) :
    DifferentiableAt ℝ (chartPullback I M F x₀) (s, extChartAt I x₀ x₀) := by
  have h1 : ContDiffAt ℝ 1 (chartPullback I M F x₀) (s, extChartAt I x₀ x₀) :=
    (chartPullback_contDiffAt I M F x₀ s).of_le (by
      show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.2 le_top)
  exact h1.differentiableAt (by norm_num)

/-- For any time `s`, the E-slice of `chartPullback` at `s` is the chart
pullback of the spatial slice of `F`. -/
private theorem chartPullback_slice_eq
    (F : SmoothTimeAlgebra I M) (x₀ : M) (s : ℝ) :
    (fun e : E => chartPullback I M F x₀ (s, e)) =
      (fun y : M => (F : ℝ × M → ℝ) (s, y)) ∘ (extChartAt I x₀).symm := rfl

/-- The spatial manifold derivative of the slice `y ↦ F(s, y)` at `x₀` equals
the Fréchet derivative of the chart-pullback slice at `φ x₀` (thanks to
`Boundaryless` collapsing `fderivWithin _ (range I)` to `fderiv _`). -/
private theorem mfderiv_slice_right_eq_fderiv_chartPullback [I.Boundaryless]
    (F : SmoothTimeAlgebra I M) (x₀ : M) (s : ℝ) (v : E) :
    mfderiv I 𝓘(ℝ, ℝ) (fun y : M => (F : ℝ × M → ℝ) (s, y)) x₀ v =
      fderiv ℝ (fun e : E => chartPullback I M F x₀ (s, e))
        (extChartAt I x₀ x₀) v := by
  have hslice : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => (F : ℝ × M → ℝ) (s, y)) x₀ := by
    have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (F : ℝ × M → ℝ) (s, y)) :=
      F.contMDiff.comp
        ((contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => s)).prodMk
          (contMDiff_id : ContMDiff I I ∞ (id : M → M)))
    exact hsmooth.contMDiffAt.mdifferentiableAt (by simp)
  rw [hslice.mfderiv]
  -- `writtenInExtChartAt I 𝓘(ℝ,ℝ) x₀ g = g ∘ (extChartAt I x₀).symm`.
  have hchart : (writtenInExtChartAt I 𝓘(ℝ, ℝ) x₀
      (fun y : M => (F : ℝ × M → ℝ) (s, y)) :) =
      fun e : E => chartPullback I M F x₀ (s, e) := by
    funext e
    simp [writtenInExtChartAt, chartPullback]
  rw [hchart]
  -- Boundaryless → `range I = univ`, then `fderivWithin _ univ _ = fderiv _ _`.
  rw [I.range_eq_univ, fderivWithin_univ]
  rfl

/-- Factor the spatial slice of `fderiv Ft` via `inr`. -/
private theorem fderiv_chartPullback_slice_right [I.Boundaryless]
    (F : SmoothTimeAlgebra I M) (x₀ : M) (s : ℝ) (v : E) :
    fderiv ℝ (fun e : E => chartPullback I M F x₀ (s, e))
        (extChartAt I x₀ x₀) v =
      fderiv ℝ (chartPullback I M F x₀) (s, extChartAt I x₀ x₀)
        ((0, v) : ℝ × E) := by
  -- The slice is `F_tilde ∘ (fun e => (s, e))`. Chain rule.
  have hinr : HasFDerivAt (fun e : E => ((s, e) : ℝ × E))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E))
      (extChartAt I x₀ x₀) :=
    (hasFDerivAt_const (s : ℝ) (extChartAt I x₀ x₀)).prodMk
      (hasFDerivAt_id (extChartAt I x₀ x₀))
  have hFt : DifferentiableAt ℝ (chartPullback I M F x₀)
      (s, extChartAt I x₀ x₀) :=
    chartPullback_differentiableAt I M F x₀ s
  have hcomp :
      HasFDerivAt (fun e : E => chartPullback I M F x₀ (s, e))
        ((fderiv ℝ (chartPullback I M F x₀) (s, extChartAt I x₀ x₀)).comp
          ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)))
        (extChartAt I x₀ x₀) :=
    hFt.hasFDerivAt.comp (extChartAt I x₀ x₀) hinr
  have heq := hcomp.fderiv
  rw [heq]
  -- `((fderiv Ft q).comp ((0).prod id)) v = (fderiv Ft q) (0, v)`.
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply]


/-- `Spatial-temporal commutativity` for the `SmoothTime` realisation: partial
differentiation in time commutes with the vector-field action, assuming the
model `I` is boundaryless. -/
theorem concrete_spatial_temporal_comm [I.Boundaryless] :
    SpatialTemporalComm (concreteDerivationEmbedding I M)
      (concreteTimeDerivativeData I M) := by
  intro X f t hf
  -- The family `s ↦ (embed X) (f s)` is smooth (substep 2d-α result).
  have hembed :
      concreteIsSmoothFam I M
        (fun s => (concreteDerivationEmbedding I M).embed X (f s)) :=
    concreteIsSmoothFam_embed I M X f hf
  ext x₀
  -- Abbreviations.
  set F : SmoothTimeAlgebra I M := concreteLift I M f with hF_def
  have hF_apply : (F : ℝ × M → ℝ) = fun p => f p.1 p.2 :=
    concreteEval_concreteLift_apply I M f hf
  -- Abbreviate `φ := extChartAt I x₀`, `v := X x₀`, `Ft` for `chartPullback I M F x₀`.
  set Ft : ℝ × E → ℝ := chartPullback I M F x₀ with hFt_def
  set v : E := X x₀ with hv_def
  -- Schwarz: the chart pullback has symmetric second Fréchet derivative at `(t, φ x₀)`.
  have hsymm : IsSymmSndFDerivAt ℝ Ft (t, extChartAt I x₀ x₀) :=
    chartPullback_isSymmSndFDerivAt I M F x₀ t
  -- `Ft` is `C^2` at `(t, φ x₀)`.
  have hC2 : ContDiffAt ℝ 2 Ft (t, extChartAt I x₀ x₀) :=
    chartPullback_contDiffAt_two I M F x₀ t
  -- Step (1) — rewrite LHS of `SpatialTemporalComm` at `x₀` as
  -- `deriv (fun s => fderiv Ft (s, φ x₀) (0, v)) t`.
  -- Step (2) — rewrite the RHS as
  -- `fderiv (fun e => deriv (fun u => Ft(u, e)) t) (φ x₀) v`.
  -- Step (3) — both sides equal an application of `fderiv (fderiv Ft) (t, φ x₀)`
  -- with `(1,0)` and `(0,v)` in opposite orders; use `hsymm` to conclude.
  -- -----------
  -- LHS reduction:
  -- `lhs_fn = fun s => (f s) ∘ X` pointwise, lifted and differentiated in time.
  -- First, unfold `td.dt_apply` and `concreteEval`/`concreteLift` for `lhs_fn`.
  -- LHS (as real number) = `deriv (fun s => (Ft_s) (v))` at t, where
  -- `Ft_s := fderiv (fun e => Ft(s, e)) (φ x₀)`, then the whole thing applied to v.
  change
    (concreteTimeDerivativeData I M).dt_apply
      (fun s => (concreteDerivationEmbedding I M).embed X (f s)) t x₀ =
    (concreteDerivationEmbedding I M).embed X
      ((concreteTimeDerivativeData I M).dt_apply f t) x₀
  -- LHS: unfold.
  have hLHS_unfold :
      ((concreteTimeDerivativeData I M).dt_apply
        (fun s => (concreteDerivationEmbedding I M).embed X (f s)) t : M → ℝ) x₀ =
      deriv (fun s => mfderiv I 𝓘(ℝ, ℝ) (f s) x₀ (X x₀)) t := by
    -- Unfold `dt_apply = eval ∘ dt ∘ lift`.
    change ((concreteEval I M (concreteDt I M
      (concreteLift I M
        (fun s => (concreteDerivationEmbedding I M).embed X (f s)))) t) : M → ℝ) x₀ =
      deriv (fun s => mfderiv I 𝓘(ℝ, ℝ) (f s) x₀ (X x₀)) t
    change (concreteDt I M
      (concreteLift I M
        (fun s => (concreteDerivationEmbedding I M).embed X (f s)))) (t, x₀) =
      deriv (fun s => mfderiv I 𝓘(ℝ, ℝ) (f s) x₀ (X x₀)) t
    change
      deriv (fun u : ℝ =>
        (concreteLift I M
          (fun s => (concreteDerivationEmbedding I M).embed X (f s)) :
            ℝ × M → ℝ) (u, x₀)) t =
      deriv (fun s => mfderiv I 𝓘(ℝ, ℝ) (f s) x₀ (X x₀)) t
    -- Replace the underlying function using the lift-eval identity.
    have hlift_apply :
        (concreteLift I M
            (fun s => (concreteDerivationEmbedding I M).embed X (f s)) :
              ℝ × M → ℝ) =
          fun p => ((concreteDerivationEmbedding I M).embed X (f p.1) : M → ℝ) p.2 :=
      concreteEval_concreteLift_apply I M _ hembed
    have hslice_fn :
        (fun u : ℝ =>
          (concreteLift I M
            (fun s => (concreteDerivationEmbedding I M).embed X (f s)) :
              ℝ × M → ℝ) (u, x₀)) =
          fun u => mfderiv I 𝓘(ℝ, ℝ) (f u) x₀ (X x₀) := by
      funext u
      rw [hlift_apply]
      -- `(embed X (f u)) x₀ = extDerivFun (f u) x₀ (X x₀) = mfderiv _ _ _ x₀ (X x₀)`.
      change extDerivFun (I := I) ((f u : C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀ (X x₀) = _
      simp only [extDerivFun, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, NormedSpace.fromTangentSpace,
        ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
      rfl
    rw [hslice_fn]
  -- RHS: unfold.
  have hRHS_unfold :
      ((concreteDerivationEmbedding I M).embed X
          ((concreteTimeDerivativeData I M).dt_apply f t) : M → ℝ) x₀ =
        mfderiv I 𝓘(ℝ, ℝ)
          (fun x : M => deriv (fun u : ℝ => (F : ℝ × M → ℝ) (u, x)) t) x₀
          (X x₀) := by
    change extDerivFun (I := I)
      (((concreteTimeDerivativeData I M).dt_apply f t : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        x₀ (X x₀) = _
    simp only [extDerivFun, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, NormedSpace.fromTangentSpace,
      ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
    -- Need: `mfderiv I 𝓘(ℝ,ℝ) (↑(td.dt_apply f t)) x₀ (X x₀) = mfderiv I 𝓘(ℝ,ℝ) (...) x₀ (X x₀)`.
    -- Rewrite the coerced function of `td.dt_apply f t` explicitly.
    have hfn : (((concreteTimeDerivativeData I M).dt_apply f t :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) =
        fun x : M => deriv (fun u : ℝ => (F : ℝ × M → ℝ) (u, x)) t := by
      funext x
      change (concreteEval I M (concreteDt I M (concreteLift I M f)) t) x = _
      change (concreteDt I M (concreteLift I M f)) (t, x) = _
      change deriv (fun u : ℝ => (concreteLift I M f : ℝ × M → ℝ) (u, x)) t = _
      rfl
    rw [hfn]
    rfl
  -- Goal reduction: show the two unfolded forms equal each other.
  rw [hLHS_unfold, hRHS_unfold]
  -- Main Schwarz reduction now on the two unfolded forms.
  -- LHS = deriv (fun s => mfderiv I 𝓘(ℝ,ℝ) (f s) x₀ v) t
  -- RHS = mfderiv I 𝓘(ℝ,ℝ) (fun x => deriv (fun u => F(u, x)) t) x₀ v
  -- Rewrite `f s` as the slice of `F` so we can use `mfderiv_slice_right_eq_fderiv_chartPullback`.
  have hf_slice : ∀ s : ℝ,
      ((f s : C^∞⟮I, M; ℝ⟯) : M → ℝ) = fun y => (F : ℝ × M → ℝ) (s, y) := by
    intro s
    funext y
    rw [hF_apply]
  -- Rewrite LHS:
  have hLHS_eq :
      deriv (fun s => mfderiv I 𝓘(ℝ, ℝ) (f s) x₀ (X x₀)) t =
        fderiv ℝ (fderiv ℝ Ft) (t, extChartAt I x₀ x₀) ((1, 0) : ℝ × E)
          ((0, v) : ℝ × E) := by
    -- Step LHS.1: slice-chart rewrite.
    have hLHS_inner : ∀ s : ℝ,
        mfderiv I 𝓘(ℝ, ℝ) (f s) x₀ (X x₀) =
          fderiv ℝ Ft (s, extChartAt I x₀ x₀) ((0, v) : ℝ × E) := by
      intro s
      -- `⇑(f s) = fun y => F(s, y)` up to coercion, so the two mfderivs are equal.
      have hfn_eq : ((f s : C^∞⟮I, M; ℝ⟯) : M → ℝ) =
          (fun y : M => (F : ℝ × M → ℝ) (s, y)) := hf_slice s
      -- `mfderiv (f s) x₀` definitionally equals `mfderiv (⇑(f s)) x₀`.
      change mfderiv I 𝓘(ℝ, ℝ) ((f s : C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀ (X x₀) = _
      rw [hfn_eq,
        mfderiv_slice_right_eq_fderiv_chartPullback I M F x₀ s (X x₀),
        fderiv_chartPullback_slice_right I M F x₀ s (X x₀)]
    -- Step LHS.2: substitute pointwise.
    have hfun_eq :
        (fun s => mfderiv I 𝓘(ℝ, ℝ) (f s) x₀ (X x₀)) =
          (fun s => fderiv ℝ Ft (s, extChartAt I x₀ x₀) ((0, v) : ℝ × E)) := by
      funext s
      exact hLHS_inner s
    rw [hfun_eq]
    -- Step LHS.3: compute the scalar derivative in s via the chain rule through `(1,0)`.
    -- `fun s => fderiv Ft (s, φ x₀) w = (fun q => fderiv Ft q w) ∘ (fun s => (s, φ x₀))`.
    -- So `deriv (·) t 1 = fderiv (fun q => fderiv Ft q w) (t, φ x₀) (1, 0)`.
    have hinl : HasFDerivAt (fun s : ℝ => ((s, extChartAt I x₀ x₀) : ℝ × E))
        (ContinuousLinearMap.inl ℝ ℝ E) t := by
      have h1 : HasFDerivAt (fun u : ℝ => u) (ContinuousLinearMap.id ℝ ℝ) t :=
        hasFDerivAt_id t
      have h2 : HasFDerivAt (fun _ : ℝ => extChartAt I x₀ x₀) (0 : ℝ →L[ℝ] E) t :=
        hasFDerivAt_const _ _
      have h := h1.prodMk h2
      exact h
    -- Differentiability of `fun q => fderiv Ft q` at `(t, φ x₀)`.
    have hfderivFt_diff : DifferentiableAt ℝ (fderiv ℝ Ft) (t, extChartAt I x₀ x₀) := by
      -- `Ft` is `C^2` at `(t, φ x₀)` ⇒ `fderiv Ft` is `C^1` (hence differentiable) at `(t, φ x₀)`.
      have hC1 : ContDiffAt ℝ 1 (fderiv ℝ Ft) (t, extChartAt I x₀ x₀) := by
        have := hC2.fderiv_right (m := 1) (by norm_cast)
        exact this
      exact hC1.differentiableAt (by norm_num)
    have hfderivFt_app_diff :
        DifferentiableAt ℝ (fun q : ℝ × E => fderiv ℝ Ft q ((0, v) : ℝ × E))
          (t, extChartAt I x₀ x₀) := by
      -- `fun q => fderiv Ft q w = ContinuousLinearMap.apply ℝ ℝ w ∘ fderiv Ft`; the outer map is a CLM.
      exact
        ((ContinuousLinearMap.apply ℝ ℝ ((0, v) : ℝ × E)).differentiable.differentiableAt).comp
          (t, extChartAt I x₀ x₀) hfderivFt_diff
    -- Chain rule for `fun s => (fun q => fderiv Ft q w) (s, φ x₀)`.
    have hslice_app :
        HasFDerivAt
          (fun s : ℝ => (fderiv ℝ Ft (s, extChartAt I x₀ x₀)) ((0, v) : ℝ × E))
          ((fderiv ℝ (fun q : ℝ × E => fderiv ℝ Ft q ((0, v) : ℝ × E))
              (t, extChartAt I x₀ x₀)).comp (ContinuousLinearMap.inl ℝ ℝ E)) t := by
      have := hfderivFt_app_diff.hasFDerivAt.comp t hinl
      exact this
    -- `deriv (·) t = fderiv (·) t 1`.
    rw [show deriv
          (fun s : ℝ => fderiv ℝ Ft (s, extChartAt I x₀ x₀) ((0, v) : ℝ × E)) t =
          fderiv ℝ
            (fun s : ℝ => fderiv ℝ Ft (s, extChartAt I x₀ x₀) ((0, v) : ℝ × E)) t 1
          from rfl]
    rw [hslice_app.fderiv]
    -- Now: `(fderiv (fun q => fderiv Ft q w) (t, φ x₀)).comp inl 1 = fderiv (fderiv Ft) (t, φ x₀) (1,0) w`.
    -- Use `fderiv_clm_apply` with `c = fderiv Ft`, `u = const w`.
    have hu_diff : DifferentiableAt ℝ (fun _ : ℝ × E => ((0, v) : ℝ × E))
        (t, extChartAt I x₀ x₀) := differentiableAt_const _
    rw [fderiv_clm_apply hfderivFt_diff hu_diff, fderiv_fun_const, Pi.zero_apply,
      ContinuousLinearMap.comp_zero, zero_add]
    change
        (((fderiv ℝ (fderiv ℝ Ft) (t, extChartAt I x₀ x₀)).flip ((0, v) : ℝ × E))
          ((ContinuousLinearMap.inl ℝ ℝ E) (1 : ℝ))) =
            ((fderiv ℝ (fderiv ℝ Ft) (t, extChartAt I x₀ x₀)) ((1, 0) : ℝ × E))
              ((0, v) : ℝ × E)
    simp only [ContinuousLinearMap.inl_apply, ContinuousLinearMap.flip_apply]
  -- Rewrite RHS.
  have hRHS_eq :
      mfderiv I 𝓘(ℝ, ℝ)
        (fun x : M => deriv (fun u : ℝ => (F : ℝ × M → ℝ) (u, x)) t) x₀ (X x₀) =
        fderiv ℝ (fderiv ℝ Ft) (t, extChartAt I x₀ x₀) ((0, v) : ℝ × E)
          ((1, 0) : ℝ × E) := by
    -- Step RHS.1: rewrite the inner `deriv` as a chart-pullback deriv slice at `(u, φ x₀)`.
    -- Key: `(fun u => F(u, x)) = (fun u => chartPullback I M F x₀ (u, φ x))` is wrong — `φ` is for `x₀`, not `x`.
    -- Instead, we rewrite the whole RHS using `mfderiv_slice_right_eq_fderiv_chartPullback`.
    -- The slice map is `h : x ↦ deriv (fun u => F(u, x)) t`.
    -- Note: at the level of the single-point chart: `h ∘ φ.symm (e) = deriv (fun u => F(u, φ.symm e)) t = deriv (fun u => Ft(u, e)) t`.
    -- So `mfderiv I 𝓘(ℝ,ℝ) h x₀ = fderiv ℝ (fun e => deriv (fun u => Ft(u, e)) t) (φ x₀)` by chart (Boundaryless).
    -- Smoothness of the RHS slice map.
    have hinner_smooth :
        ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun x : M => deriv (fun u : ℝ => (F : ℝ × M → ℝ) (u, x)) t) := by
      -- `fun x => deriv (fun u => F(u, x)) t` is `concreteDtFun I M F` evaluated at `(t, x)`.
      have hdt_smooth : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (concreteDtFun I M F) :=
        (concreteDtFun I M F).contMDiff
      exact hdt_smooth.comp
        ((contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => t)).prodMk
          (contMDiff_id : ContMDiff I I ∞ (id : M → M)))
    have hinner_mdiff :
        MDifferentiableAt I 𝓘(ℝ, ℝ)
          (fun x : M => deriv (fun u : ℝ => (F : ℝ × M → ℝ) (u, x)) t) x₀ :=
      hinner_smooth.contMDiffAt.mdifferentiableAt (by simp)
    rw [hinner_mdiff.mfderiv]
    -- Rewrite `writtenInExtChartAt` and `range I`.
    have hchart : (writtenInExtChartAt I 𝓘(ℝ, ℝ) x₀
        (fun x : M => deriv (fun u : ℝ => (F : ℝ × M → ℝ) (u, x)) t) :) =
        fun e : E => deriv (fun u : ℝ => Ft (u, e)) t := by
      funext e
      simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_self_apply,
        modelWithCornersSelf_coe, id_eq]
      rfl
    rw [hchart, I.range_eq_univ, fderivWithin_univ]
    -- Step RHS.2: rewrite `fderiv (fun e => deriv (fun u => Ft(u, e)) t) (φ x₀) = fderiv (fun e => fderiv Ft (t, e) (1,0)) (φ x₀)`.
    -- The two inner functions agree on the open neighbourhood `(extChartAt I x₀).target` of `φ x₀`.
    have hev : (fun e : E => deriv (fun u : ℝ => Ft (u, e)) t) =ᶠ[nhds (extChartAt I x₀ x₀)]
        (fun e : E => fderiv ℝ Ft (t, e) ((1, 0) : ℝ × E)) := by
      refine (Filter.eventually_of_mem (extChartAt_target_mem_nhds x₀) (fun e he => ?_))
      -- Smoothness of `Ft` at `(t, e)` for `e ∈ target`.
      have hcontDiff : ContDiffAt ℝ ∞ Ft (t, e) :=
        chartPullback_contDiffAt_of_mem_target I M F x₀ t he
      have hC1 : ContDiffAt ℝ 1 Ft (t, e) :=
        hcontDiff.of_le (by
          show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
          exact WithTop.coe_le_coe.2 le_top)
      have hdiff : DifferentiableAt ℝ Ft (t, e) :=
        hC1.differentiableAt (by norm_num)
      -- Slice `fun u => Ft(u, e)` = `Ft ∘ (fun u => (u, e))`.
      have hinl' : HasFDerivAt (fun u : ℝ => ((u, e) : ℝ × E))
          (ContinuousLinearMap.inl ℝ ℝ E) t := by
        have h1 : HasFDerivAt (fun u : ℝ => u) (ContinuousLinearMap.id ℝ ℝ) t :=
          hasFDerivAt_id t
        have h2 : HasFDerivAt (fun _ : ℝ => e) (0 : ℝ →L[ℝ] E) t :=
          hasFDerivAt_const _ _
        have h := h1.prodMk h2
        exact h
      have hcomp : HasFDerivAt (fun u : ℝ => Ft (u, e))
          ((fderiv ℝ Ft (t, e)).comp (ContinuousLinearMap.inl ℝ ℝ E)) t := by
        have := hdiff.hasFDerivAt.comp t hinl'
        exact this
      change deriv (fun u : ℝ => Ft (u, e)) t = fderiv ℝ Ft (t, e) ((1, 0) : ℝ × E)
      rw [show deriv (fun u : ℝ => Ft (u, e)) t =
          (fderiv ℝ (fun u : ℝ => Ft (u, e)) t) 1 from rfl]
      rw [hcomp.fderiv]
      rfl
    rw [hev.fderiv_eq]
    -- Now: `fderiv ℝ (fun e => fderiv Ft (t, e) (1, 0)) (φ x₀) v = fderiv (fderiv Ft) (t, φ x₀) (0, v) (1, 0)`.
    -- Apply the chain rule on `fun e => (t, e)`.
    have hinr : HasFDerivAt (fun e : E => ((t, e) : ℝ × E))
        (ContinuousLinearMap.inr ℝ ℝ E) (extChartAt I x₀ x₀) := by
      have h1 : HasFDerivAt (fun _ : E => t) (0 : E →L[ℝ] ℝ) (extChartAt I x₀ x₀) :=
        hasFDerivAt_const _ _
      have h2 : HasFDerivAt (fun e : E => e) (ContinuousLinearMap.id ℝ E)
          (extChartAt I x₀ x₀) :=
        hasFDerivAt_id _
      have h := h1.prodMk h2
      exact h
    have hfderivFt_diff : DifferentiableAt ℝ (fderiv ℝ Ft) (t, extChartAt I x₀ x₀) := by
      have hC1 : ContDiffAt ℝ 1 (fderiv ℝ Ft) (t, extChartAt I x₀ x₀) :=
        hC2.fderiv_right (m := 1) (by norm_cast)
      exact hC1.differentiableAt (by norm_num)
    have hfderivFt_app_diff :
        DifferentiableAt ℝ (fun q : ℝ × E => fderiv ℝ Ft q ((1, 0) : ℝ × E))
          (t, extChartAt I x₀ x₀) :=
      ((ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × E)).differentiable.differentiableAt).comp
        (t, extChartAt I x₀ x₀) hfderivFt_diff
    have hslice_app :
        HasFDerivAt
          (fun e : E => (fderiv ℝ Ft (t, e)) ((1, 0) : ℝ × E))
          ((fderiv ℝ (fun q : ℝ × E => fderiv ℝ Ft q ((1, 0) : ℝ × E))
              (t, extChartAt I x₀ x₀)).comp (ContinuousLinearMap.inr ℝ ℝ E))
          (extChartAt I x₀ x₀) := by
      have := hfderivFt_app_diff.hasFDerivAt.comp (extChartAt I x₀ x₀) hinr
      exact this
    rw [hslice_app.fderiv]
    -- Reduce `fderiv (fun q => fderiv Ft q (1,0)) (t, φ x₀) (0, v) = fderiv (fderiv Ft) (t, φ x₀) (0, v) (1, 0)`.
    have hu_diff : DifferentiableAt ℝ (fun _ : ℝ × E => ((1, 0) : ℝ × E))
        (t, extChartAt I x₀ x₀) := differentiableAt_const _
    rw [fderiv_clm_apply hfderivFt_diff hu_diff, fderiv_fun_const, Pi.zero_apply,
      ContinuousLinearMap.comp_zero, zero_add]
    -- Goal: `(((... ).flip (1, 0)).comp inr) (X x₀) = (... ) (0, v) (1, 0)`.
    change
        (((fderiv ℝ (fderiv ℝ Ft) (t, extChartAt I x₀ x₀)).flip ((1, 0) : ℝ × E))
          ((ContinuousLinearMap.inr ℝ ℝ E) (X x₀))) =
            ((fderiv ℝ (fderiv ℝ Ft) (t, extChartAt I x₀ x₀)) ((0, v) : ℝ × E))
              ((1, 0) : ℝ × E)
    simp only [ContinuousLinearMap.inr_apply, ContinuousLinearMap.flip_apply]
    rfl
  -- Combine LHS, RHS, and Schwarz.
  rw [hLHS_eq, hRHS_eq]
  exact hsymm ((1, 0) : ℝ × E) ((0, v) : ℝ × E)

/-!
### General-manifolds version (no `[I.Boundaryless]` required)

The same identity holds on general manifolds (possibly with boundary/corners),
using `fderivWithin` on the closed set `univ ×ˢ range I` and the "within" form
of Schwarz (`ContDiffWithinAt.isSymmSndFDerivWithinAt`).
-/

/-- `chartPullback` is `C^∞` at `(t, φ x₀)` within `univ ×ˢ range I` — the
general-manifolds analogue of `chartPullback_contDiffAt_of_mem_target`. -/
private theorem chartPullback_contDiffWithinAt
    (F : SmoothTimeAlgebra I M) (x₀ : M) (t : ℝ) :
    ContDiffWithinAt ℝ ∞ (chartPullback I M F x₀)
      (Set.univ ×ˢ Set.range I) (t, extChartAt I x₀ x₀) := by
  -- `(extChartAt I x₀).symm` is `ContMDiffWithinAt` at `φ x₀` within `range I`.
  have hsymm_within :
      ContMDiffWithinAt 𝓘(ℝ, E) I ∞ ((extChartAt I x₀).symm : E → M)
        (Set.range I) (extChartAt I x₀ x₀) :=
    contMDiffWithinAt_extChartAt_symm_range (n := ∞) x₀ (mem_extChartAt_target x₀)
  -- Build `fst` and `snd` as manifold maps within `univ ×ˢ range I` at `(t, φ x₀)`.
  -- Use space model on source to make composition with `F` work.
  have hfst :
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × E => q.1) (Set.univ ×ˢ Set.range I) (t, extChartAt I x₀ x₀) :=
    contMDiffWithinAt_fst
  have hsnd_space :
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × E => q.2) (Set.univ ×ˢ Set.range I) (t, extChartAt I x₀ x₀) :=
    contMDiffWithinAt_snd
  -- Compose `(extChartAt I x₀).symm` with `snd`.
  have hsymm_comp :
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) I ∞
        (fun q : ℝ × E => (extChartAt I x₀).symm q.2)
        (Set.univ ×ˢ Set.range I) (t, extChartAt I x₀ x₀) := by
    have hmaps : Set.MapsTo (fun q : ℝ × E => q.2)
        (Set.univ ×ˢ Set.range I) (Set.range I) := by
      intro q hq; exact hq.2
    exact hsymm_within.comp (t, extChartAt I x₀ x₀) hsnd_space hmaps
  -- Pair `fst` and `symm_comp` into a map `ℝ × E → ℝ × M`.
  have hpair :
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × E => (q.1, (extChartAt I x₀).symm q.2))
        (Set.univ ×ˢ Set.range I) (t, extChartAt I x₀ x₀) :=
    hfst.prodMk hsymm_comp
  -- Compose with `F`.
  have hFcomp :
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (chartPullback I M F x₀) (Set.univ ×ˢ Set.range I)
        (t, extChartAt I x₀ x₀) := by
    have hF : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (F : ℝ × M → ℝ) (t, (extChartAt I x₀).symm (extChartAt I x₀ x₀)) :=
      F.contMDiff.contMDiffAt
    exact hF.comp_contMDiffWithinAt (t, extChartAt I x₀ x₀) hpair
  -- Now transfer through the ℝ × E ≈ 𝓘(ℝ, ℝ).prod 𝓘(ℝ, E) ≈ 𝓘(ℝ, ℝ × E) equivalences.
  -- The models `𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)` and `𝓘(ℝ, ℝ × E)` are the same model on `ℝ × E`;
  -- we can convert via `contMDiffWithinAt_iff_contDiffWithinAt` using the space model.
  -- Alternative: use `ContMDiffWithinAt.contDiffWithinAt` via space form.
  -- The map `chartPullback` is between normed spaces, so we can go via space models.
  have hspace :
      ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
        (chartPullback I M F x₀) (Set.univ ×ˢ Set.range I)
        (t, extChartAt I x₀ x₀) := by
    -- Reconcile `𝓘(ℝ, ℝ × E)` with `𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)` and the charted-space instance.
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hFcomp
  exact hspace.contDiffWithinAt

/-- Schwarz: the chart pullback has symmetric second `fderivWithin` at
`(t, φ x₀)` on the set `univ ×ˢ range I` — the general-manifolds analogue of
`chartPullback_isSymmSndFDerivAt`. -/
private theorem chartPullback_isSymmSndFDerivWithinAt
    (F : SmoothTimeAlgebra I M) (x₀ : M) (t : ℝ) :
    IsSymmSndFDerivWithinAt ℝ (chartPullback I M F x₀)
      (Set.univ ×ˢ Set.range I) (t, extChartAt I x₀ x₀) := by
  -- Base smoothness and the `minSmoothness` bound.
  have hC : ContDiffWithinAt ℝ ∞ (chartPullback I M F x₀)
      (Set.univ ×ˢ Set.range I) (t, extChartAt I x₀ x₀) :=
    chartPullback_contDiffWithinAt I M F x₀ t
  have hn : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (WithTop.coe_le_coe.mpr (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)))
  -- Unique differentiability on `univ ×ˢ range I`.
  have hS : UniqueDiffOn ℝ (Set.univ ×ˢ Set.range I : Set (ℝ × E)) :=
    uniqueDiffOn_univ.prod I.uniqueDiffOn
  -- `(t, φ x₀) ∈ closure (interior (univ ×ˢ range I))`.
  have hclosure : (t, extChartAt I x₀ x₀) ∈
      closure (interior (Set.univ ×ˢ Set.range I : Set (ℝ × E))) := by
    rw [interior_prod_eq, closure_prod_eq]
    refine ⟨?_, ?_⟩
    · simp [interior_univ]
    · exact I.range_subset_closure_interior
        (extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀))
  -- `(t, φ x₀) ∈ univ ×ˢ range I`.
  have hmem : (t, extChartAt I x₀ x₀) ∈ (Set.univ ×ˢ Set.range I : Set (ℝ × E)) :=
    ⟨Set.mem_univ _, extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀)⟩
  exact hC.isSymmSndFDerivWithinAt hn hS hclosure hmem

/-- `chartPullback` is differentiable within `univ ×ˢ range I` at `(s, φ x₀)`. -/
private theorem chartPullback_differentiableWithinAt
    (F : SmoothTimeAlgebra I M) (x₀ : M) (s : ℝ) :
    DifferentiableWithinAt ℝ (chartPullback I M F x₀)
      (Set.univ ×ˢ Set.range I) (s, extChartAt I x₀ x₀) := by
  have h1 : ContDiffWithinAt ℝ 1 (chartPullback I M F x₀)
      (Set.univ ×ˢ Set.range I) (s, extChartAt I x₀ x₀) :=
    (chartPullback_contDiffWithinAt I M F x₀ s).of_le (by
      show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.2 le_top)
  exact h1.differentiableWithinAt (by norm_num)

/-- The spatial manifold derivative of the slice `y ↦ F(s, y)` at `x₀` equals the
Fréchet `fderivWithin` (on `range I`) of the chart-pullback slice at `φ x₀`. This is
the general (non-Boundaryless) analogue. -/
private theorem mfderiv_slice_right_eq_fderivWithin_chartPullback
    (F : SmoothTimeAlgebra I M) (x₀ : M) (s : ℝ) (v : E) :
    mfderiv I 𝓘(ℝ, ℝ) (fun y : M => (F : ℝ × M → ℝ) (s, y)) x₀ v =
      fderivWithin ℝ (fun e : E => chartPullback I M F x₀ (s, e))
        (Set.range I) (extChartAt I x₀ x₀) v := by
  have hslice : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => (F : ℝ × M → ℝ) (s, y)) x₀ := by
    have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (F : ℝ × M → ℝ) (s, y)) :=
      F.contMDiff.comp
        ((contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => s)).prodMk
          (contMDiff_id : ContMDiff I I ∞ (id : M → M)))
    exact hsmooth.contMDiffAt.mdifferentiableAt (by simp)
  rw [hslice.mfderiv]
  -- `writtenInExtChartAt I 𝓘(ℝ,ℝ) x₀ g = g ∘ (extChartAt I x₀).symm`.
  have hchart : (writtenInExtChartAt I 𝓘(ℝ, ℝ) x₀
      (fun y : M => (F : ℝ × M → ℝ) (s, y)) :) =
      fun e : E => chartPullback I M F x₀ (s, e) := by
    funext e
    simp [writtenInExtChartAt, chartPullback]
  rw [hchart]
  rfl

/-- Factor the spatial slice of `fderivWithin Ft` via `inr`, within `range I`. -/
private theorem fderivWithin_chartPullback_slice_right
    (F : SmoothTimeAlgebra I M) (x₀ : M) (s : ℝ) (v : E) :
    fderivWithin ℝ (fun e : E => chartPullback I M F x₀ (s, e))
        (Set.range I) (extChartAt I x₀ x₀) v =
      fderivWithin ℝ (chartPullback I M F x₀)
        (Set.univ ×ˢ Set.range I) (s, extChartAt I x₀ x₀)
        ((0, v) : ℝ × E) := by
  -- The slice is `chartPullback ∘ (fun e => (s, e))`.
  have hinr : HasFDerivWithinAt (fun e : E => ((s, e) : ℝ × E))
      (ContinuousLinearMap.inr ℝ ℝ E) (Set.range I) (extChartAt I x₀ x₀) := by
    have h1 : HasFDerivWithinAt (fun _ : E => s) (0 : E →L[ℝ] ℝ)
        (Set.range I) (extChartAt I x₀ x₀) :=
      (hasFDerivAt_const _ _).hasFDerivWithinAt
    have h2 : HasFDerivWithinAt (fun e : E => e) (ContinuousLinearMap.id ℝ E)
        (Set.range I) (extChartAt I x₀ x₀) :=
      (hasFDerivAt_id _).hasFDerivWithinAt
    exact h1.prodMk h2
  -- The inner map sends `range I` to `univ ×ˢ range I`.
  have hmaps : Set.MapsTo (fun e : E => ((s, e) : ℝ × E))
      (Set.range I) (Set.univ ×ˢ Set.range I) := by
    intro e he; exact ⟨Set.mem_univ _, he⟩
  -- Differentiability of `chartPullback` within `univ ×ˢ range I` at `(s, φ x₀)`.
  have hFt : DifferentiableWithinAt ℝ (chartPullback I M F x₀)
      (Set.univ ×ˢ Set.range I) (s, extChartAt I x₀ x₀) :=
    chartPullback_differentiableWithinAt I M F x₀ s
  -- Chain rule.
  have hcomp : HasFDerivWithinAt (fun e : E => chartPullback I M F x₀ (s, e))
      ((fderivWithin ℝ (chartPullback I M F x₀) (Set.univ ×ˢ Set.range I)
          (s, extChartAt I x₀ x₀)).comp (ContinuousLinearMap.inr ℝ ℝ E))
      (Set.range I) (extChartAt I x₀ x₀) :=
    hFt.hasFDerivWithinAt.comp (extChartAt I x₀ x₀) hinr hmaps
  -- Extract `fderivWithin` using unique differentiability.
  have huniq : UniqueDiffWithinAt ℝ (Set.range I) (extChartAt I x₀ x₀) :=
    I.uniqueDiffOn _ (extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀))
  rw [hcomp.fderivWithin huniq]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- Bridge lemma B-time: the time-direction slice of `fderivWithin Ft` computed via
`deriv` equals the `(1, 0)`-derivative of the "apply `(0, v)`" mapping within
`univ ×ˢ range I`. -/
private theorem fderivWithin_clm_apply_comp_inl_sliceTime
    (F : SmoothTimeAlgebra I M) (x₀ : M) (t : ℝ) (v : E) :
    deriv (fun σ : ℝ => fderivWithin ℝ (chartPullback I M F x₀)
          (Set.univ ×ˢ Set.range I) (σ, extChartAt I x₀ x₀) ((0, v) : ℝ × E)) t =
      fderivWithin ℝ (fderivWithin ℝ (chartPullback I M F x₀)
          (Set.univ ×ˢ Set.range I)) (Set.univ ×ˢ Set.range I)
          (t, extChartAt I x₀ x₀) ((1, 0) : ℝ × E) ((0, v) : ℝ × E) := by
  set Ft : ℝ × E → ℝ := chartPullback I M F x₀
  set S : Set (ℝ × E) := Set.univ ×ˢ Set.range I
  -- The outer slicing in `σ` is a composition with `fun σ => (σ, φ x₀)`.
  have hinl : HasFDerivAt (fun σ : ℝ => ((σ, extChartAt I x₀ x₀) : ℝ × E))
      (ContinuousLinearMap.inl ℝ ℝ E) t := by
    have h1 : HasFDerivAt (fun u : ℝ => u) (ContinuousLinearMap.id ℝ ℝ) t :=
      hasFDerivAt_id t
    have h2 : HasFDerivAt (fun _ : ℝ => extChartAt I x₀ x₀) (0 : ℝ →L[ℝ] E) t :=
      hasFDerivAt_const _ _
    exact h1.prodMk h2
  -- The inner map sends `univ` into `S = univ ×ˢ range I`? NO. We're sliding only in σ,
  -- so `(σ, φ x₀) ∈ S ↔ φ x₀ ∈ range I`, which holds for all σ. So the preimage is `univ`.
  have hmaps_univ : Set.MapsTo (fun σ : ℝ => ((σ, extChartAt I x₀ x₀) : ℝ × E))
      (Set.univ : Set ℝ) S := by
    intro σ _
    exact ⟨Set.mem_univ _, extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀)⟩
  -- Differentiability of `fderivWithin Ft S` within `S` at `(t, φ x₀)` — from `C^2`.
  have hFt_C : ContDiffWithinAt ℝ ∞ Ft S (t, extChartAt I x₀ x₀) :=
    chartPullback_contDiffWithinAt I M F x₀ t
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_univ.prod I.uniqueDiffOn
  have hmem : (t, extChartAt I x₀ x₀) ∈ S :=
    ⟨Set.mem_univ _, extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀)⟩
  have hfderivFt_within_C : ContDiffWithinAt ℝ 1
      (fderivWithin ℝ Ft S) S (t, extChartAt I x₀ x₀) :=
    hFt_C.fderivWithin_right hS (m := 1) (by norm_cast) hmem
  have hfderivFt_within_diff : DifferentiableWithinAt ℝ
      (fderivWithin ℝ Ft S) S (t, extChartAt I x₀ x₀) :=
    hfderivFt_within_C.differentiableWithinAt (by norm_num)
  -- The map `fun q => (fderivWithin Ft S q) (0, v) = ContinuousLinearMap.apply ℝ ℝ (0,v) ∘ fderivWithin Ft S`.
  have hfderivFt_app_within_diff :
      DifferentiableWithinAt ℝ
        (fun q : ℝ × E => fderivWithin ℝ Ft S q ((0, v) : ℝ × E))
        S (t, extChartAt I x₀ x₀) := by
    have happ : DifferentiableWithinAt ℝ
        (fun c : ℝ × E →L[ℝ] ℝ => c ((0, v) : ℝ × E)) Set.univ
        (fderivWithin ℝ Ft S (t, extChartAt I x₀ x₀)) :=
      (ContinuousLinearMap.apply ℝ ℝ ((0, v) : ℝ × E)).differentiableAt.differentiableWithinAt
    exact happ.comp (t, extChartAt I x₀ x₀)
      hfderivFt_within_diff (Set.mapsTo_univ _ _)
  -- Compose the slice: `(fun σ => ...) = (fun q => fderivWithin Ft S q (0, v)) ∘ (σ ↦ (σ, φ x₀))`.
  have hslice_app_within :
      HasFDerivWithinAt
        (fun σ : ℝ => (fderivWithin ℝ Ft S (σ, extChartAt I x₀ x₀)) ((0, v) : ℝ × E))
        ((fderivWithin ℝ (fun q : ℝ × E => fderivWithin ℝ Ft S q ((0, v) : ℝ × E))
            S (t, extChartAt I x₀ x₀)).comp
          (ContinuousLinearMap.inl ℝ ℝ E))
        Set.univ t := by
    have hbase := hfderivFt_app_within_diff.hasFDerivWithinAt.comp t
      hinl.hasFDerivWithinAt hmaps_univ
    exact hbase
  -- Go from HasFDerivWithinAt on `univ` to HasFDerivAt, then use `deriv = fderiv · 1`.
  have hslice_app :
      HasFDerivAt
        (fun σ : ℝ => (fderivWithin ℝ Ft S (σ, extChartAt I x₀ x₀)) ((0, v) : ℝ × E))
        ((fderivWithin ℝ (fun q : ℝ × E => fderivWithin ℝ Ft S q ((0, v) : ℝ × E))
            S (t, extChartAt I x₀ x₀)).comp
          (ContinuousLinearMap.inl ℝ ℝ E)) t :=
    hasFDerivWithinAt_univ.mp hslice_app_within
  -- `deriv (·) t = fderiv (·) t 1`.
  rw [show deriv
        (fun σ : ℝ => fderivWithin ℝ Ft S (σ, extChartAt I x₀ x₀) ((0, v) : ℝ × E)) t =
        fderiv ℝ
          (fun σ : ℝ => fderivWithin ℝ Ft S (σ, extChartAt I x₀ x₀) ((0, v) : ℝ × E)) t 1
        from rfl]
  rw [hslice_app.fderiv]
  -- Now apply `fderivWithin_clm_apply` to factor the outer `fderivWithin`.
  have huniq_S : UniqueDiffWithinAt ℝ S (t, extChartAt I x₀ x₀) := hS _ hmem
  have hu_within : DifferentiableWithinAt ℝ (fun _ : ℝ × E => ((0, v) : ℝ × E))
      S (t, extChartAt I x₀ x₀) := differentiableWithinAt_const _
  rw [fderivWithin_clm_apply huniq_S hfderivFt_within_diff hu_within]
  -- The constant map has zero derivative, so the flip term vanishes.
  rw [fderivWithin_const_apply]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

/-- Bridge lemma B-space: the spatial slice of `fderivWithin Ft`, when evaluated at `(1, 0)`
and then `fderivWithin`-ed in `e`, equals the `(0, v)`-derivative of the "apply `(1, 0)`" mapping
within `univ ×ˢ range I`. -/
private theorem fderivWithin_clm_apply_comp_inr_sliceSpace
    (F : SmoothTimeAlgebra I M) (x₀ : M) (t : ℝ) (v : E) :
    fderivWithin ℝ (fun e : E => fderivWithin ℝ (chartPullback I M F x₀)
          (Set.univ ×ˢ Set.range I) (t, e) ((1, 0) : ℝ × E))
        (Set.range I) (extChartAt I x₀ x₀) v =
      fderivWithin ℝ (fderivWithin ℝ (chartPullback I M F x₀)
          (Set.univ ×ˢ Set.range I)) (Set.univ ×ˢ Set.range I)
          (t, extChartAt I x₀ x₀) ((0, v) : ℝ × E) ((1, 0) : ℝ × E) := by
  set Ft : ℝ × E → ℝ := chartPullback I M F x₀
  set S : Set (ℝ × E) := Set.univ ×ˢ Set.range I
  -- Differentiability preliminaries (reuse from the time-slice lemma).
  have hFt_C : ContDiffWithinAt ℝ ∞ Ft S (t, extChartAt I x₀ x₀) :=
    chartPullback_contDiffWithinAt I M F x₀ t
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_univ.prod I.uniqueDiffOn
  have hmem : (t, extChartAt I x₀ x₀) ∈ S :=
    ⟨Set.mem_univ _, extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀)⟩
  have hfderivFt_within_C : ContDiffWithinAt ℝ 1
      (fderivWithin ℝ Ft S) S (t, extChartAt I x₀ x₀) :=
    hFt_C.fderivWithin_right hS (m := 1) (by norm_cast) hmem
  have hfderivFt_within_diff : DifferentiableWithinAt ℝ
      (fderivWithin ℝ Ft S) S (t, extChartAt I x₀ x₀) :=
    hfderivFt_within_C.differentiableWithinAt (by norm_num)
  -- Inner map `fun e => (t, e)` has `HasFDerivWithinAt (...) inr (range I) (φ x₀)`
  -- because the constant term has zero derivative.
  have hinr : HasFDerivWithinAt (fun e : E => ((t, e) : ℝ × E))
      (ContinuousLinearMap.inr ℝ ℝ E) (Set.range I) (extChartAt I x₀ x₀) := by
    have h1 : HasFDerivWithinAt (fun _ : E => t) (0 : E →L[ℝ] ℝ)
        (Set.range I) (extChartAt I x₀ x₀) :=
      (hasFDerivAt_const _ _).hasFDerivWithinAt
    have h2 : HasFDerivWithinAt (fun e : E => e) (ContinuousLinearMap.id ℝ E)
        (Set.range I) (extChartAt I x₀ x₀) :=
      (hasFDerivAt_id _).hasFDerivWithinAt
    exact h1.prodMk h2
  -- The inner map sends `range I` to `S`.
  have hmaps : Set.MapsTo (fun e : E => ((t, e) : ℝ × E)) (Set.range I) S := by
    intro e he; exact ⟨Set.mem_univ _, he⟩
  -- `fun q => (fderivWithin Ft S q) (1, 0)` is differentiable within `S` at `(t, φ x₀)`.
  have hfderivFt_app_within_diff :
      DifferentiableWithinAt ℝ
        (fun q : ℝ × E => fderivWithin ℝ Ft S q ((1, 0) : ℝ × E))
        S (t, extChartAt I x₀ x₀) := by
    have happ : DifferentiableWithinAt ℝ
        (fun c : ℝ × E →L[ℝ] ℝ => c ((1, 0) : ℝ × E)) Set.univ
        (fderivWithin ℝ Ft S (t, extChartAt I x₀ x₀)) :=
      (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × E)).differentiableAt.differentiableWithinAt
    exact happ.comp (t, extChartAt I x₀ x₀)
      hfderivFt_within_diff (Set.mapsTo_univ _ _)
  -- Compose: `(fun e => fderivWithin Ft S (t, e) (1, 0)) = (fun q => fderivWithin Ft S q (1, 0)) ∘ (e ↦ (t, e))`.
  have hslice_app : HasFDerivWithinAt
      (fun e : E => (fderivWithin ℝ Ft S (t, e)) ((1, 0) : ℝ × E))
      ((fderivWithin ℝ (fun q : ℝ × E => fderivWithin ℝ Ft S q ((1, 0) : ℝ × E))
          S (t, extChartAt I x₀ x₀)).comp (ContinuousLinearMap.inr ℝ ℝ E))
      (Set.range I) (extChartAt I x₀ x₀) := by
    exact hfderivFt_app_within_diff.hasFDerivWithinAt.comp
      (extChartAt I x₀ x₀) hinr hmaps
  -- Extract `fderivWithin` using unique differentiability on `range I`.
  have huniq_range : UniqueDiffWithinAt ℝ (Set.range I) (extChartAt I x₀ x₀) :=
    I.uniqueDiffOn _ (extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀))
  rw [hslice_app.fderivWithin huniq_range]
  -- Apply `fderivWithin_clm_apply` to the inner `fderivWithin`.
  have huniq_S : UniqueDiffWithinAt ℝ S (t, extChartAt I x₀ x₀) := hS _ hmem
  have hu_within : DifferentiableWithinAt ℝ (fun _ : ℝ × E => ((1, 0) : ℝ × E))
      S (t, extChartAt I x₀ x₀) := differentiableWithinAt_const _
  rw [fderivWithin_clm_apply huniq_S hfderivFt_within_diff hu_within]
  rw [fderivWithin_const_apply]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- `Spatial-temporal commutativity` for the `SmoothTime` realisation — the general
(non-Boundaryless) version. Partial differentiation in time commutes with the
vector-field action for any (possibly with-boundary) manifold `M`. -/
theorem concrete_spatial_temporal_comm_general :
    SpatialTemporalComm (concreteDerivationEmbedding I M)
      (concreteTimeDerivativeData I M) := by
  intro X f t hf
  -- The family `s ↦ (embed X) (f s)` is smooth (substep 2d-α result).
  have hembed :
      concreteIsSmoothFam I M
        (fun s => (concreteDerivationEmbedding I M).embed X (f s)) :=
    concreteIsSmoothFam_embed I M X f hf
  ext x₀
  -- Abbreviations.
  set F : SmoothTimeAlgebra I M := concreteLift I M f with hF_def
  have hF_apply : (F : ℝ × M → ℝ) = fun p => f p.1 p.2 :=
    concreteEval_concreteLift_apply I M f hf
  set Ft : ℝ × E → ℝ := chartPullback I M F x₀ with hFt_def
  set S : Set (ℝ × E) := Set.univ ×ˢ Set.range I with hS_def
  set v : E := X x₀ with hv_def
  -- Schwarz within S.
  have hsymm : IsSymmSndFDerivWithinAt ℝ Ft S (t, extChartAt I x₀ x₀) :=
    chartPullback_isSymmSndFDerivWithinAt I M F x₀ t
  -- Unfold the `SpatialTemporalComm` goal at `x₀`.
  change
    (concreteTimeDerivativeData I M).dt_apply
      (fun s => (concreteDerivationEmbedding I M).embed X (f s)) t x₀ =
    (concreteDerivationEmbedding I M).embed X
      ((concreteTimeDerivativeData I M).dt_apply f t) x₀
  -- LHS: same unfolding as in the Boundaryless version.
  have hLHS_unfold :
      ((concreteTimeDerivativeData I M).dt_apply
        (fun s => (concreteDerivationEmbedding I M).embed X (f s)) t : M → ℝ) x₀ =
      deriv (fun s => mfderiv I 𝓘(ℝ, ℝ) (f s) x₀ (X x₀)) t := by
    change ((concreteEval I M (concreteDt I M
      (concreteLift I M
        (fun s => (concreteDerivationEmbedding I M).embed X (f s)))) t) : M → ℝ) x₀ =
      deriv (fun s => mfderiv I 𝓘(ℝ, ℝ) (f s) x₀ (X x₀)) t
    change (concreteDt I M
      (concreteLift I M
        (fun s => (concreteDerivationEmbedding I M).embed X (f s)))) (t, x₀) =
      deriv (fun s => mfderiv I 𝓘(ℝ, ℝ) (f s) x₀ (X x₀)) t
    change
      deriv (fun u : ℝ =>
        (concreteLift I M
          (fun s => (concreteDerivationEmbedding I M).embed X (f s)) :
            ℝ × M → ℝ) (u, x₀)) t =
      deriv (fun s => mfderiv I 𝓘(ℝ, ℝ) (f s) x₀ (X x₀)) t
    have hlift_apply :
        (concreteLift I M
            (fun s => (concreteDerivationEmbedding I M).embed X (f s)) :
              ℝ × M → ℝ) =
          fun p => ((concreteDerivationEmbedding I M).embed X (f p.1) : M → ℝ) p.2 :=
      concreteEval_concreteLift_apply I M _ hembed
    have hslice_fn :
        (fun u : ℝ =>
          (concreteLift I M
            (fun s => (concreteDerivationEmbedding I M).embed X (f s)) :
              ℝ × M → ℝ) (u, x₀)) =
          fun u => mfderiv I 𝓘(ℝ, ℝ) (f u) x₀ (X x₀) := by
      funext u
      rw [hlift_apply]
      change extDerivFun (I := I) ((f u : C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀ (X x₀) = _
      simp only [extDerivFun, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, NormedSpace.fromTangentSpace,
        ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
      rfl
    rw [hslice_fn]
  -- RHS: same unfolding.
  have hRHS_unfold :
      ((concreteDerivationEmbedding I M).embed X
          ((concreteTimeDerivativeData I M).dt_apply f t) : M → ℝ) x₀ =
        mfderiv I 𝓘(ℝ, ℝ)
          (fun x : M => deriv (fun u : ℝ => (F : ℝ × M → ℝ) (u, x)) t) x₀
          (X x₀) := by
    change extDerivFun (I := I)
      (((concreteTimeDerivativeData I M).dt_apply f t : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        x₀ (X x₀) = _
    simp only [extDerivFun, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, NormedSpace.fromTangentSpace,
      ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
    have hfn : (((concreteTimeDerivativeData I M).dt_apply f t :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) =
        fun x : M => deriv (fun u : ℝ => (F : ℝ × M → ℝ) (u, x)) t := by
      funext x
      change (concreteEval I M (concreteDt I M (concreteLift I M f)) t) x = _
      change (concreteDt I M (concreteLift I M f)) (t, x) = _
      change deriv (fun u : ℝ => (concreteLift I M f : ℝ × M → ℝ) (u, x)) t = _
      rfl
    rw [hfn]
    rfl
  rw [hLHS_unfold, hRHS_unfold]
  -- Replace `f s` slice with the `F` slice.
  have hf_slice : ∀ s : ℝ,
      ((f s : C^∞⟮I, M; ℝ⟯) : M → ℝ) = fun y => (F : ℝ × M → ℝ) (s, y) := by
    intro s
    funext y
    rw [hF_apply]
  -- Rewrite LHS in terms of `fderivWithin (fderivWithin Ft S) S (t, φ x₀) (1, 0) (0, v)`.
  have hLHS_eq :
      deriv (fun s => mfderiv I 𝓘(ℝ, ℝ) (f s) x₀ (X x₀)) t =
        fderivWithin ℝ (fderivWithin ℝ Ft S) S (t, extChartAt I x₀ x₀)
          ((1, 0) : ℝ × E) ((0, v) : ℝ × E) := by
    have hLHS_inner : ∀ s : ℝ,
        mfderiv I 𝓘(ℝ, ℝ) (f s) x₀ (X x₀) =
          fderivWithin ℝ Ft S (s, extChartAt I x₀ x₀) ((0, v) : ℝ × E) := by
      intro s
      have hfn_eq : ((f s : C^∞⟮I, M; ℝ⟯) : M → ℝ) =
          (fun y : M => (F : ℝ × M → ℝ) (s, y)) := hf_slice s
      change mfderiv I 𝓘(ℝ, ℝ) ((f s : C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀ (X x₀) = _
      rw [hfn_eq,
        mfderiv_slice_right_eq_fderivWithin_chartPullback I M F x₀ s (X x₀),
        fderivWithin_chartPullback_slice_right I M F x₀ s (X x₀)]
    have hfun_eq :
        (fun s => mfderiv I 𝓘(ℝ, ℝ) (f s) x₀ (X x₀)) =
          (fun s => fderivWithin ℝ Ft S (s, extChartAt I x₀ x₀) ((0, v) : ℝ × E)) := by
      funext s
      exact hLHS_inner s
    rw [hfun_eq]
    exact fderivWithin_clm_apply_comp_inl_sliceTime I M F x₀ t v
  -- Rewrite RHS in terms of `fderivWithin (fderivWithin Ft S) S (t, φ x₀) (0, v) (1, 0)`.
  have hRHS_eq :
      mfderiv I 𝓘(ℝ, ℝ)
        (fun x : M => deriv (fun u : ℝ => (F : ℝ × M → ℝ) (u, x)) t) x₀ (X x₀) =
        fderivWithin ℝ (fderivWithin ℝ Ft S) S (t, extChartAt I x₀ x₀)
          ((0, v) : ℝ × E) ((1, 0) : ℝ × E) := by
    -- Smoothness of RHS slice.
    have hinner_smooth :
        ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun x : M => deriv (fun u : ℝ => (F : ℝ × M → ℝ) (u, x)) t) := by
      have hdt_smooth : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (concreteDtFun I M F) :=
        (concreteDtFun I M F).contMDiff
      exact hdt_smooth.comp
        ((contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => t)).prodMk
          (contMDiff_id : ContMDiff I I ∞ (id : M → M)))
    have hinner_mdiff :
        MDifferentiableAt I 𝓘(ℝ, ℝ)
          (fun x : M => deriv (fun u : ℝ => (F : ℝ × M → ℝ) (u, x)) t) x₀ :=
      hinner_smooth.contMDiffAt.mdifferentiableAt (by simp)
    rw [hinner_mdiff.mfderiv]
    -- Express `writtenInExtChartAt` as a chart-pullback composition.
    have hchart : (writtenInExtChartAt I 𝓘(ℝ, ℝ) x₀
        (fun x : M => deriv (fun u : ℝ => (F : ℝ × M → ℝ) (u, x)) t) :) =
        fun e : E => deriv (fun u : ℝ => Ft (u, e)) t := by
      funext e
      simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_self_apply,
        modelWithCornersSelf_coe, id_eq]
      rfl
    rw [hchart]
    -- Rewrite the inner `deriv (fun u => Ft (u, e)) t` as a `fderivWithin` expression
    -- locally on `range I`.  We use `eventuallyEq` via `nhdsWithin` within `range I`.
    -- Specifically, for `e ∈ range I` near `φ x₀` *and* in target of chart, we have
    -- `deriv (fun u => Ft (u, e)) t = fderivWithin Ft S (t, e) (1, 0)`.
    have hev : (fun e : E => deriv (fun u : ℝ => Ft (u, e)) t) =ᶠ[nhdsWithin (extChartAt I x₀ x₀) (Set.range I)]
        (fun e : E => fderivWithin ℝ Ft S (t, e) ((1, 0) : ℝ × E)) := by
      refine Filter.eventually_of_mem (extChartAt_target_mem_nhdsWithin x₀) ?_
      intro e he
      -- `Ft` is `C^∞` within `S` at `(t, e)`.
      have hctargerange : e ∈ Set.range I := extChartAt_target_subset_range x₀ he
      have hmem_te : (t, e) ∈ S := ⟨Set.mem_univ _, hctargerange⟩
      -- Show `deriv (fun u => Ft (u, e)) t = fderivWithin Ft S (t, e) (1, 0)`.
      -- Strategy: `HasFDerivAt (fun u => Ft(u,e))` via the chain rule through `inl`,
      -- but we only have `HasFDerivWithinAt Ft _ S (t, e)`. So we need `hmaps` ensuring
      -- `(u, e) ∈ S` for all `u`.
      have hmaps_te : Set.MapsTo (fun u : ℝ => ((u, e) : ℝ × E))
          (Set.univ : Set ℝ) S := by
        intro u _; exact ⟨Set.mem_univ _, hctargerange⟩
      have hinl' : HasFDerivAt (fun u : ℝ => ((u, e) : ℝ × E))
          (ContinuousLinearMap.inl ℝ ℝ E) t := by
        have h1 : HasFDerivAt (fun u : ℝ => u) (ContinuousLinearMap.id ℝ ℝ) t :=
          hasFDerivAt_id t
        have h2 : HasFDerivAt (fun _ : ℝ => e) (0 : ℝ →L[ℝ] E) t :=
          hasFDerivAt_const _ _
        exact h1.prodMk h2
      have hFt_C_te : ContDiffWithinAt ℝ 1 Ft S (t, e) := by
        have hbig : ContDiffWithinAt ℝ ∞ Ft S (t, e) := by
          -- Recompute at `(t, e)` using the `_within` helper, but the helper is tied to
          -- `φ x₀`.  Reuse `chartPullback_contDiffWithinAt` is not general enough.
          -- Instead, prove smoothness directly at `(t, e)` using the same recipe.
          have hsymm_within :
              ContMDiffWithinAt 𝓘(ℝ, E) I ∞ ((extChartAt I x₀).symm : E → M)
                (Set.range I) e :=
            contMDiffWithinAt_extChartAt_symm_range (n := ∞) x₀ he
          have hfst :
              ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
                (fun q : ℝ × E => q.1) S (t, e) := contMDiffWithinAt_fst
          have hsnd_space :
              ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
                (fun q : ℝ × E => q.2) S (t, e) := contMDiffWithinAt_snd
          have hmaps_snd : Set.MapsTo (fun q : ℝ × E => q.2) S (Set.range I) := by
            intro q hq; exact hq.2
          have hsymm_comp :
              ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) I ∞
                (fun q : ℝ × E => (extChartAt I x₀).symm q.2) S (t, e) :=
            hsymm_within.comp (t, e) hsnd_space hmaps_snd
          have hpair :
              ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
                (fun q : ℝ × E => (q.1, (extChartAt I x₀).symm q.2)) S (t, e) :=
            hfst.prodMk hsymm_comp
          have hFcomp :
              ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
                (chartPullback I M F x₀) S (t, e) := by
            have hF : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
                (F : ℝ × M → ℝ) (t, (extChartAt I x₀).symm e) :=
              F.contMDiff.contMDiffAt
            exact hF.comp_contMDiffWithinAt (t, e) hpair
          have hspace :
              ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
                (chartPullback I M F x₀) S (t, e) := by
            rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
            exact hFcomp
          exact hspace.contDiffWithinAt
        exact hbig.of_le (by
          show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
          exact WithTop.coe_le_coe.2 le_top)
      have hFt_diff : DifferentiableWithinAt ℝ Ft S (t, e) :=
        hFt_C_te.differentiableWithinAt (by norm_num)
      -- Compose via `HasFDerivWithinAt` on `univ` source; transport to `HasFDerivAt`.
      have hFt_has : HasFDerivWithinAt Ft (fderivWithin ℝ Ft S (t, e)) S (t, e) :=
        hFt_diff.hasFDerivWithinAt
      have hcomp_raw : HasFDerivWithinAt (Ft ∘ (fun u : ℝ => ((u, e) : ℝ × E)))
          ((fderivWithin ℝ Ft S (t, e)).comp (ContinuousLinearMap.inl ℝ ℝ E))
          Set.univ t :=
        hFt_has.comp t hinl'.hasFDerivWithinAt hmaps_te
      have hcomp : HasFDerivWithinAt (fun u : ℝ => Ft (u, e))
          ((fderivWithin ℝ Ft S (t, e)).comp (ContinuousLinearMap.inl ℝ ℝ E))
          Set.univ t := hcomp_raw
      have hcomp' : HasFDerivAt (fun u : ℝ => Ft (u, e))
          ((fderivWithin ℝ Ft S (t, e)).comp (ContinuousLinearMap.inl ℝ ℝ E)) t :=
        hasFDerivWithinAt_univ.mp hcomp
      change deriv (fun u : ℝ => Ft (u, e)) t = fderivWithin ℝ Ft S (t, e) ((1, 0) : ℝ × E)
      rw [show deriv (fun u : ℝ => Ft (u, e)) t =
          (fderiv ℝ (fun u : ℝ => Ft (u, e)) t) 1 from rfl]
      rw [hcomp'.fderiv]
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    -- Use `Filter.EventuallyEq.fderivWithin_eq` to transport `fderivWithin`.
    have huniq_range : UniqueDiffWithinAt ℝ (Set.range I) (extChartAt I x₀ x₀) :=
      I.uniqueDiffOn _ (extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀))
    have hev_eq : fderivWithin ℝ (fun e : E => deriv (fun u : ℝ => Ft (u, e)) t)
          (Set.range I) (extChartAt I x₀ x₀) =
        fderivWithin ℝ (fun e : E => fderivWithin ℝ Ft S (t, e) ((1, 0) : ℝ × E))
          (Set.range I) (extChartAt I x₀ x₀) :=
      Filter.EventuallyEq.fderivWithin_eq hev
        (hev.self_of_nhdsWithin
          (extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀)))
    rw [hev_eq]
    exact fderivWithin_clm_apply_comp_inr_sliceSpace I M F x₀ t (X x₀)
  -- Combine via Schwarz.
  rw [hLHS_eq, hRHS_eq]
  exact hsymm ((1, 0) : ℝ × E) ((0, v) : ℝ × E)

-- ============================================================
-- Subset-time realisation: `SmoothTimeAlgebraOn I M s`
-- ============================================================

/-!
### Subset-time joint-smooth algebra

The `SmoothTimeAlgebra` abbrev above is hard-wired to *global* joint smoothness
on `ℝ × M`. For Ricci flow on arbitrary time windows `s : Set ℝ` (for example
`Set.Ioo a b` or `Set.Icc a b`), we introduce a parallel *subset-time* family
`SmoothTimeAlgebraOn I M s` whose elements carry both
* a formal curried family `fam : ℝ → C^∞⟮I, M; ℝ⟯`, and
* a joint-smoothness witness for the uncurried map on `s ×ˢ Set.univ`.

Storing the formal family as data (rather than defining an element as the raw
uncurried function) lets us define `concreteEvalOn` as `F.fam t` on the nose —
agreeing with `f t` for every `t : ℝ`, including `t ∉ s` — which is what the
abstract `TimeRegularFam.eval_lift` axiom demands.

All algebraic structure (`CommRing`, `Algebra C^∞⟮I, M; ℝ⟯ _`) is induced
pointwise on `fam`; closure under the ring operations follows from the standard
Mathlib `ContMDiffOn.add`/`.mul`/`.neg` API.
-/

/-- Subset-time joint-smooth algebra: a curried family
`fam : ℝ → C^∞⟮I, M; ℝ⟯` together with a witness that the uncurried map
`(t, x) ↦ fam t x` is jointly `C^∞` on `s ×ˢ Set.univ`. -/
structure SmoothTimeAlgebraOn (s : Set ℝ) : Type _ where
  /-- The underlying time-parametrised family of smooth maps. -/
  fam : ℝ → C^∞⟮I, M; ℝ⟯
  /-- The uncurried family is jointly smooth on the product set `s ×ˢ univ`. -/
  smooth_on :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => fam p.1 p.2)
      (s ×ˢ (Set.univ : Set M))

namespace SmoothTimeAlgebraOn

variable {I M} {s : Set ℝ}

/-- Extensionality: two elements of `SmoothTimeAlgebraOn I M s` are equal when
their underlying families agree pointwise. -/
@[ext]
theorem ext {F G : SmoothTimeAlgebraOn I M s} (h : ∀ t, F.fam t = G.fam t) : F = G := by
  cases F with
  | mk f hf =>
    cases G with
    | mk g hg =>
      congr
      funext t
      exact h t

/-- `SmoothTimeAlgebraOn.mk f h` unfolds to `f` on the `fam` projection. -/
@[simp]
theorem fam_mk (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (h : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => f p.1 p.2)
      (s ×ˢ (Set.univ : Set M))) :
    (SmoothTimeAlgebraOn.mk f h).fam = f := rfl

/-- Injectivity of `fam`: two elements are equal iff their families coincide. -/
theorem fam_injective :
    Function.Injective (SmoothTimeAlgebraOn.fam (I := I) (M := M) (s := s)) := by
  intro F G hFG
  cases F with
  | mk f hf =>
    cases G with
    | mk g hg =>
      dsimp only at hFG
      subst hFG
      rfl

end SmoothTimeAlgebraOn

/-!
#### Pointwise algebraic instances

Each instance is defined by pointwise action on `fam` and justified by the
ordinary `ContMDiffOn` closure laws (`add`, `mul`, `neg`, `const`).
-/

namespace SmoothTimeAlgebraOn

variable {I M} {s : Set ℝ}

/-- Helper: the uncurried map of the zero family is the constant zero function. -/
private theorem uncurry_zero_eq :
    (fun p : ℝ × M => ((0 : ℝ → C^∞⟮I, M; ℝ⟯) p.1) p.2) = fun _ => (0 : ℝ) := by
  funext p
  change ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ) p.2 = 0
  simp

/-- Helper: the uncurried map of the unit family is the constant one function. -/
private theorem uncurry_one_eq :
    (fun p : ℝ × M => ((1 : ℝ → C^∞⟮I, M; ℝ⟯) p.1) p.2) = fun _ => (1 : ℝ) := by
  funext p
  change ((1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) p.2 = 1
  simp

/-- Helper: the uncurried pointwise sum. -/
private theorem uncurry_add_eq (f g : ℝ → C^∞⟮I, M; ℝ⟯) :
    (fun p : ℝ × M => ((f + g) p.1) p.2) =
      (fun p : ℝ × M => f p.1 p.2) + (fun p : ℝ × M => g p.1 p.2) := by
  funext p
  change ((f p.1 + g p.1) : C^∞⟮I, M; ℝ⟯) p.2 = f p.1 p.2 + g p.1 p.2
  simp [ContMDiffMap.coe_add]

/-- Helper: the uncurried pointwise product. -/
private theorem uncurry_mul_eq (f g : ℝ → C^∞⟮I, M; ℝ⟯) :
    (fun p : ℝ × M => ((f * g) p.1) p.2) =
      (fun p : ℝ × M => f p.1 p.2) * (fun p : ℝ × M => g p.1 p.2) := by
  funext p
  change ((f p.1 * g p.1) : C^∞⟮I, M; ℝ⟯) p.2 = f p.1 p.2 * g p.1 p.2
  simp [ContMDiffMap.coe_mul]

/-- Helper: the uncurried pointwise negation. -/
private theorem uncurry_neg_eq (f : ℝ → C^∞⟮I, M; ℝ⟯) :
    (fun p : ℝ × M => ((-f) p.1) p.2) = fun p : ℝ × M => -(f p.1 p.2) := by
  funext p
  change ((-f p.1) : C^∞⟮I, M; ℝ⟯) p.2 = -(f p.1 p.2)
  simp [ContMDiffMap.coe_neg]

/-- Helper: the uncurried pointwise subtraction. -/
private theorem uncurry_sub_eq (f g : ℝ → C^∞⟮I, M; ℝ⟯) :
    (fun p : ℝ × M => ((f - g) p.1) p.2) =
      (fun p : ℝ × M => f p.1 p.2) - (fun p : ℝ × M => g p.1 p.2) := by
  funext p
  change ((f p.1 - g p.1) : C^∞⟮I, M; ℝ⟯) p.2 = f p.1 p.2 - g p.1 p.2
  simp [ContMDiffMap.coe_sub]

/-- Helper: repeated-addition `ℕ` action on `C^∞⟮I, M; ℝ⟯` agrees with
real multiplication by `(n : ℝ)` on pointwise values. -/
private theorem coe_nsmul_apply (n : ℕ) (c : C^∞⟮I, M; ℝ⟯) (x : M) :
    ((n • c : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = ((n : ℕ) : ℝ) * c x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, ContMDiffMap.coe_add, Pi.add_apply, ih]
    push_cast
    ring

/-- Helper: repeated-addition `ℤ` action on `C^∞⟮I, M; ℝ⟯` agrees with
real multiplication by `(n : ℝ)` on pointwise values. -/
private theorem coe_zsmul_apply (n : ℤ) (c : C^∞⟮I, M; ℝ⟯) (x : M) :
    ((n • c : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = ((n : ℤ) : ℝ) * c x := by
  match n with
  | Int.ofNat k =>
    -- `((k : ℕ) : ℤ) • c = (k : ℕ) • c`.
    change ((((k : ℕ) : ℤ) • c : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = _
    have hzn : (((k : ℕ) : ℤ) • (c : C^∞⟮I, M; ℝ⟯)) = (k : ℕ) • c :=
      natCast_zsmul c k
    rw [hzn, coe_nsmul_apply]
    change ((k : ℕ) : ℝ) * c x = ((Int.ofNat k : ℤ) : ℝ) * c x
    simp
  | Int.negSucc k =>
    -- `Int.negSucc k • c = -((k + 1 : ℕ) • c)`.
    change ((Int.negSucc k • c : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = _
    have hns : (Int.negSucc k • (c : C^∞⟮I, M; ℝ⟯)) = -((k + 1 : ℕ) • c) :=
      negSucc_zsmul c k
    rw [hns, ContMDiffMap.coe_neg, Pi.neg_apply, coe_nsmul_apply]
    push_cast
    ring

/-- Helper: `n • f` uncurried equals constant `(n : ℝ)` times the uncurried `f`. -/
private theorem uncurry_nsmul_eq (n : ℕ) (f : ℝ → C^∞⟮I, M; ℝ⟯) :
    (fun p : ℝ × M => ((n • f) p.1) p.2) =
      (fun _ : ℝ × M => ((n : ℕ) : ℝ)) * (fun p : ℝ × M => f p.1 p.2) := by
  funext p
  change ((n • f p.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) p.2 = ((n : ℕ) : ℝ) * f p.1 p.2
  rw [coe_nsmul_apply]

/-- Helper: `n • f` uncurried (for `ℤ` action) equals constant `(n : ℝ)` times
the uncurried `f`. -/
private theorem uncurry_zsmul_eq (n : ℤ) (f : ℝ → C^∞⟮I, M; ℝ⟯) :
    (fun p : ℝ × M => ((n • f) p.1) p.2) =
      (fun _ : ℝ × M => ((n : ℤ) : ℝ)) * (fun p : ℝ × M => f p.1 p.2) := by
  funext p
  change ((n • f p.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) p.2 = ((n : ℤ) : ℝ) * f p.1 p.2
  rw [coe_zsmul_apply]

/-- Helper: the uncurried power equals the pointwise power of the uncurried. -/
private theorem uncurry_pow_eq (f : ℝ → C^∞⟮I, M; ℝ⟯) (n : ℕ) :
    (fun p : ℝ × M => ((f ^ n) p.1) p.2) =
      (fun p : ℝ × M => f p.1 p.2) ^ n := by
  funext p
  change ((f p.1 ^ n : C^∞⟮I, M; ℝ⟯) : M → ℝ) p.2 = (f p.1 p.2) ^ n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ContMDiffMap.coe_mul, Pi.mul_apply, ih, pow_succ]

/-- Helper: `((n : ℕ) : C^∞⟮I, M; ℝ⟯) x = (n : ℝ)` for any point `x`. -/
private theorem coe_natCast_apply (n : ℕ) (x : M) :
    (((n : ℕ) : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = ((n : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have : (((k + 1 : ℕ) : ℕ) : C^∞⟮I, M; ℝ⟯) =
        ((k : ℕ) : C^∞⟮I, M; ℝ⟯) + 1 := by push_cast; rfl
    rw [this, ContMDiffMap.coe_add, Pi.add_apply, ih]
    simp

/-- Helper: the uncurried `NatCast` constant family is constant. -/
private theorem uncurry_natCast_eq (n : ℕ) :
    (fun p : ℝ × M => (((n : ℕ) : ℝ → C^∞⟮I, M; ℝ⟯) p.1) p.2) =
      fun _ => ((n : ℕ) : ℝ) := by
  funext p
  change (((n : ℕ) : C^∞⟮I, M; ℝ⟯) : M → ℝ) p.2 = ((n : ℕ) : ℝ)
  rw [coe_natCast_apply]

/-- Helper: `((n : ℤ) : C^∞⟮I, M; ℝ⟯) x = (n : ℝ)` for any point `x`. -/
private theorem coe_intCast_apply (n : ℤ) (x : M) :
    (((n : ℤ) : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = ((n : ℤ) : ℝ) := by
  match n with
  | Int.ofNat k =>
    change (((k : ℕ) : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = ((k : ℕ) : ℝ)
    exact coe_natCast_apply k x
  | Int.negSucc k =>
    -- `((Int.negSucc k : ℤ) : C^∞⟮I, M; ℝ⟯) = -((k + 1 : ℕ) : C^∞⟮I, M; ℝ⟯)`
    -- by `Int.cast_negSucc`.
    rw [Int.cast_negSucc]
    rw [ContMDiffMap.coe_neg, Pi.neg_apply, coe_natCast_apply]
    push_cast
    rfl

/-- Helper: the uncurried `IntCast` constant family is constant. -/
private theorem uncurry_intCast_eq (n : ℤ) :
    (fun p : ℝ × M => (((n : ℤ) : ℝ → C^∞⟮I, M; ℝ⟯) p.1) p.2) =
      fun _ => ((n : ℤ) : ℝ) := by
  funext p
  change (((n : ℤ) : C^∞⟮I, M; ℝ⟯) : M → ℝ) p.2 = ((n : ℤ) : ℝ)
  rw [coe_intCast_apply]

/-- The zero element: constantly zero in every slice. -/
noncomputable instance instZero : Zero (SmoothTimeAlgebraOn I M s) where
  zero :=
    { fam := 0
      smooth_on := by
        rw [uncurry_zero_eq]
        exact contMDiffOn_const }

@[simp]
theorem fam_zero : (0 : SmoothTimeAlgebraOn I M s).fam = 0 := rfl

/-- The unit element: constantly one in every slice. -/
noncomputable instance instOne : One (SmoothTimeAlgebraOn I M s) where
  one :=
    { fam := 1
      smooth_on := by
        rw [uncurry_one_eq]
        exact contMDiffOn_const }

@[simp]
theorem fam_one : (1 : SmoothTimeAlgebraOn I M s).fam = 1 := rfl

/-- Pointwise addition. -/
noncomputable instance instAdd : Add (SmoothTimeAlgebraOn I M s) where
  add F G :=
    { fam := F.fam + G.fam
      smooth_on := by
        rw [uncurry_add_eq]
        exact F.smooth_on.add G.smooth_on }

@[simp]
theorem fam_add (F G : SmoothTimeAlgebraOn I M s) : (F + G).fam = F.fam + G.fam := rfl

/-- Pointwise multiplication. -/
noncomputable instance instMul : Mul (SmoothTimeAlgebraOn I M s) where
  mul F G :=
    { fam := F.fam * G.fam
      smooth_on := by
        rw [uncurry_mul_eq]
        exact F.smooth_on.mul G.smooth_on }

@[simp]
theorem fam_mul (F G : SmoothTimeAlgebraOn I M s) : (F * G).fam = F.fam * G.fam := rfl

/-- Pointwise negation. -/
noncomputable instance instNeg : Neg (SmoothTimeAlgebraOn I M s) where
  neg F :=
    { fam := -F.fam
      smooth_on := by
        rw [uncurry_neg_eq]
        exact F.smooth_on.neg }

@[simp]
theorem fam_neg (F : SmoothTimeAlgebraOn I M s) : (-F).fam = -F.fam := rfl

/-- Pointwise subtraction. -/
noncomputable instance instSub : Sub (SmoothTimeAlgebraOn I M s) where
  sub F G :=
    { fam := F.fam - G.fam
      smooth_on := by
        rw [uncurry_sub_eq]
        -- `ContMDiffOn` is closed under `sub` via `add` and `neg`.
        have := F.smooth_on.add G.smooth_on.neg
        simpa [Pi.sub_def, sub_eq_add_neg, Pi.add_def, Pi.neg_def] using this }

@[simp]
theorem fam_sub (F G : SmoothTimeAlgebraOn I M s) : (F - G).fam = F.fam - G.fam := rfl

/-- Natural-number scalar multiplication: `n • F` has underlying family `n • F.fam`. -/
noncomputable instance instSMulNat : SMul ℕ (SmoothTimeAlgebraOn I M s) where
  smul n F :=
    { fam := n • F.fam
      smooth_on := by
        rw [uncurry_nsmul_eq]
        exact (contMDiffOn_const (c := ((n : ℕ) : ℝ))).mul F.smooth_on }

@[simp]
theorem fam_nsmul (n : ℕ) (F : SmoothTimeAlgebraOn I M s) :
    (n • F).fam = n • F.fam := rfl

/-- Integer scalar multiplication: `n • F` has underlying family `n • F.fam`. -/
noncomputable instance instSMulInt : SMul ℤ (SmoothTimeAlgebraOn I M s) where
  smul n F :=
    { fam := n • F.fam
      smooth_on := by
        rw [uncurry_zsmul_eq]
        exact (contMDiffOn_const (c := ((n : ℤ) : ℝ))).mul F.smooth_on }

@[simp]
theorem fam_zsmul (n : ℤ) (F : SmoothTimeAlgebraOn I M s) :
    (n • F).fam = n • F.fam := rfl

/-- Natural-number power (iterated multiplication). -/
noncomputable instance instPowNat : Pow (SmoothTimeAlgebraOn I M s) ℕ where
  pow F n :=
    { fam := F.fam ^ n
      smooth_on := by
        rw [uncurry_pow_eq]
        induction n with
        | zero =>
          show ContMDiffOn _ _ _ ((fun p : ℝ × M => F.fam p.1 p.2) ^ 0) _
          simpa [pow_zero] using
            (contMDiffOn_const : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
              (fun _ : ℝ × M => (1 : ℝ)) (s ×ˢ (Set.univ : Set M)))
        | succ k ih =>
          show ContMDiffOn _ _ _ ((fun p : ℝ × M => F.fam p.1 p.2) ^ (k + 1)) _
          rw [pow_succ]
          exact ih.mul F.smooth_on }

@[simp]
theorem fam_pow (F : SmoothTimeAlgebraOn I M s) (n : ℕ) :
    (F ^ n).fam = F.fam ^ n := rfl

/-- Natural number coercion into `SmoothTimeAlgebraOn`: constantly `n`. -/
noncomputable instance instNatCast : NatCast (SmoothTimeAlgebraOn I M s) where
  natCast n :=
    { fam := (n : ℝ → C^∞⟮I, M; ℝ⟯)
      smooth_on := by
        rw [uncurry_natCast_eq]
        exact contMDiffOn_const }

@[simp]
theorem fam_natCast (n : ℕ) :
    ((n : SmoothTimeAlgebraOn I M s).fam) = (n : ℝ → C^∞⟮I, M; ℝ⟯) := rfl

/-- Integer coercion into `SmoothTimeAlgebraOn`: constantly `n`. -/
noncomputable instance instIntCast : IntCast (SmoothTimeAlgebraOn I M s) where
  intCast n :=
    { fam := (n : ℝ → C^∞⟮I, M; ℝ⟯)
      smooth_on := by
        rw [uncurry_intCast_eq]
        exact contMDiffOn_const }

@[simp]
theorem fam_intCast (n : ℤ) :
    ((n : SmoothTimeAlgebraOn I M s).fam) = (n : ℝ → C^∞⟮I, M; ℝ⟯) := rfl

/-- `SmoothTimeAlgebraOn I M s` is a commutative ring via pointwise operations
on `fam`. The CommRing instance is pulled back through the injective
projection `fam : SmoothTimeAlgebraOn I M s → ℝ → C^∞⟮I, M; ℝ⟯`. -/
noncomputable instance instCommRing : CommRing (SmoothTimeAlgebraOn I M s) :=
  fam_injective.commRing
    (f := fam)
    (zero := fam_zero)
    (one := fam_one)
    (add := fam_add)
    (mul := fam_mul)
    (neg := fam_neg)
    (sub := fam_sub)
    (nsmul := fun n F => fam_nsmul n F)
    (zsmul := fun n F => fam_zsmul n F)
    (npow := fun F n => fam_pow F n)
    (natCast := fam_natCast)
    (intCast := fam_intCast)

/-- Auxiliary: the constant-in-time lift of a spatial smooth function. -/
private noncomputable def constLift (c : C^∞⟮I, M; ℝ⟯) : SmoothTimeAlgebraOn I M s :=
  { fam := fun _ => c
    smooth_on := (c.contMDiff.comp contMDiff_snd).contMDiffOn }

@[simp]
private theorem fam_constLift (c : C^∞⟮I, M; ℝ⟯) (t : ℝ) :
    (constLift (s := s) (I := I) (M := M) c).fam t = c := rfl

/-- The `C^∞⟮I, M; ℝ⟯`-algebra structure on `SmoothTimeAlgebraOn I M s`: a
spatial smooth function `c` embeds as the constant-in-time family `fun _ => c`. -/
noncomputable def compSndRingHomOn :
    C^∞⟮I, M; ℝ⟯ →+* SmoothTimeAlgebraOn I M s where
  toFun := constLift (I := I) (M := M) (s := s)
  map_one' := by
    apply fam_injective
    funext _
    rw [fam_constLift, fam_one]; rfl
  map_mul' c₁ c₂ := by
    apply fam_injective
    funext _
    rw [fam_constLift, fam_mul]
    change c₁ * c₂ = (constLift (I := I) (M := M) (s := s) c₁).fam _ *
      (constLift (I := I) (M := M) (s := s) c₂).fam _
    rw [fam_constLift, fam_constLift]
  map_zero' := by
    apply fam_injective
    funext _
    rw [fam_constLift, fam_zero]; rfl
  map_add' c₁ c₂ := by
    apply fam_injective
    funext _
    rw [fam_constLift, fam_add]
    change c₁ + c₂ = (constLift (I := I) (M := M) (s := s) c₁).fam _ +
      (constLift (I := I) (M := M) (s := s) c₂).fam _
    rw [fam_constLift, fam_constLift]

@[simp]
theorem fam_compSndRingHomOn (c : C^∞⟮I, M; ℝ⟯) (t : ℝ) :
    (compSndRingHomOn (I := I) (M := M) (s := s) c).fam t = c := rfl

/-- `C^∞⟮I, M; ℝ⟯`-algebra structure on `SmoothTimeAlgebraOn I M s` obtained
from `compSndRingHomOn`. -/
noncomputable instance instAlgebra :
    Algebra C^∞⟮I, M; ℝ⟯ (SmoothTimeAlgebraOn I M s) :=
  (compSndRingHomOn (I := I) (M := M) (s := s)).toAlgebra

end SmoothTimeAlgebraOn

-- ============================================================
-- Smooth-in-time-on-`s` predicate and bridge from global smoothness
-- ============================================================

/-- A family `f : ℝ → C^∞⟮I, M; ℝ⟯` is *jointly smooth on `s`* when the
uncurried map `(t, x) ↦ f t x` is jointly `C^∞` on `s ×ˢ Set.univ`. This is the
subset-time analogue of `concreteIsSmoothFam`. -/
def concreteIsSmoothFamOn (s : Set ℝ) (f : ℝ → C^∞⟮I, M; ℝ⟯) : Prop :=
  ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => f p.1 p.2)
    (s ×ˢ (Set.univ : Set M))

/-- Global joint smoothness implies joint smoothness on any subset. -/
theorem concreteIsSmoothFam.of_global_to_on
    (s : Set ℝ) (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam I M f) :
    concreteIsSmoothFamOn I M s f :=
  hf.contMDiffOn

/-- Constant families are jointly smooth on any subset. -/
theorem concreteIsSmoothFamOn_const (s : Set ℝ) (c : C^∞⟮I, M; ℝ⟯) :
    concreteIsSmoothFamOn I M s (fun _ => c) :=
  (concreteIsSmoothFam_const I M c).contMDiffOn

/-- Subset-smooth families are closed under pointwise addition. -/
theorem concreteIsSmoothFamOn_add (s : Set ℝ) (f g : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFamOn I M s f) (hg : concreteIsSmoothFamOn I M s g) :
    concreteIsSmoothFamOn I M s (f + g) := by
  change ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
    (fun p : ℝ × M => (f + g) p.1 p.2) (s ×ˢ (Set.univ : Set M))
  have heq : (fun p : ℝ × M => (f + g) p.1 p.2) =
      (fun p : ℝ × M => f p.1 p.2) + (fun p : ℝ × M => g p.1 p.2) := by
    funext p
    change (f p.1 + g p.1) p.2 = f p.1 p.2 + g p.1 p.2
    simp [ContMDiffMap.coe_add]
  rw [heq]
  exact hf.add hg

/-- Subset-smooth families are closed under pointwise multiplication. -/
theorem concreteIsSmoothFamOn_mul (s : Set ℝ) (f g : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFamOn I M s f) (hg : concreteIsSmoothFamOn I M s g) :
    concreteIsSmoothFamOn I M s (f * g) := by
  change ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
    (fun p : ℝ × M => (f * g) p.1 p.2) (s ×ˢ (Set.univ : Set M))
  have heq : (fun p : ℝ × M => (f * g) p.1 p.2) =
      (fun p : ℝ × M => f p.1 p.2) * (fun p : ℝ × M => g p.1 p.2) := by
    funext p
    change (f p.1 * g p.1) p.2 = f p.1 p.2 * g p.1 p.2
    simp [ContMDiffMap.coe_mul]
  rw [heq]
  exact hf.mul hg

/-- Subset-smooth families are closed under pointwise negation. -/
theorem concreteIsSmoothFamOn_neg (s : Set ℝ) (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFamOn I M s f) :
    concreteIsSmoothFamOn I M s (-f) := by
  change ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
    (fun p : ℝ × M => (-f) p.1 p.2) (s ×ˢ (Set.univ : Set M))
  have heq : (fun p : ℝ × M => (-f) p.1 p.2) =
      (fun p : ℝ × M => -(f p.1 p.2)) := by
    funext p
    change (-(f p.1)) p.2 = -(f p.1 p.2)
    simp [ContMDiffMap.coe_neg]
  rw [heq]
  exact hf.neg

/-- Subset-smooth families are closed under pointwise subtraction. -/
theorem concreteIsSmoothFamOn_sub (s : Set ℝ) (f g : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFamOn I M s f) (hg : concreteIsSmoothFamOn I M s g) :
    concreteIsSmoothFamOn I M s (f - g) := by
  have heq : f - g = f + (-g) := by funext t; simp [sub_eq_add_neg]
  rw [heq]
  exact concreteIsSmoothFamOn_add I M s f _ hf (concreteIsSmoothFamOn_neg I M s g hg)

-- ============================================================
-- `concreteLiftOn` and `concreteEvalOn`
-- ============================================================

/-- Lift a family `f : ℝ → C^∞⟮I, M; ℝ⟯` to an element of
`SmoothTimeAlgebraOn I M s`; when `f` is not jointly smooth on `s`, fall back
to `0`. The formal family is stored on the `fam` projection so that
`concreteEvalOn` can recover `f t` verbatim for every `t`. -/
noncomputable def concreteLiftOn (s : Set ℝ) (f : ℝ → C^∞⟮I, M; ℝ⟯) :
    SmoothTimeAlgebraOn I M s :=
  open Classical in
  if h : concreteIsSmoothFamOn I M s f then
    { fam := f, smooth_on := h }
  else 0

/-- Partial evaluation at a fixed time `t`: recover `F.fam t`. Because the
formal family is stored as data, this always returns the slice that `lift`
originally packed in, irrespective of whether `t ∈ s`. -/
def concreteEvalOn {s : Set ℝ} (F : SmoothTimeAlgebraOn I M s) (t : ℝ) :
    C^∞⟮I, M; ℝ⟯ :=
  F.fam t

/-- When `f` is subset-smooth, `concreteLiftOn` stores `f` verbatim as its
underlying family. -/
theorem concreteEvalOn_concreteLiftOn_apply
    {s : Set ℝ} (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFamOn I M s f) :
    (concreteLiftOn I M s f).fam = f := by
  simp only [concreteLiftOn, dif_pos hf, SmoothTimeAlgebraOn.fam_mk]

/-- Fundamental identity: evaluating the lift of a subset-smooth family at any
time `t` recovers `f t`. This holds for *all* `t : ℝ`, not just `t ∈ s`,
because `fam` is stored as data. -/
theorem concreteEvalOn_concreteLiftOn
    {s : Set ℝ} (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFamOn I M s f) (t : ℝ) :
    concreteEvalOn I M (concreteLiftOn I M s f) t = f t := by
  change (concreteLiftOn I M s f).fam t = f t
  rw [concreteEvalOn_concreteLiftOn_apply I M f hf]

/-- `concreteLiftOn` is additive on subset-smooth families. -/
theorem concreteLiftOn_add
    {s : Set ℝ} (f g : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFamOn I M s f)
    (hg : concreteIsSmoothFamOn I M s g) :
    concreteLiftOn I M s (f + g) =
      concreteLiftOn I M s f + concreteLiftOn I M s g := by
  have hfg : concreteIsSmoothFamOn I M s (f + g) :=
    concreteIsSmoothFamOn_add I M s f g hf hg
  apply SmoothTimeAlgebraOn.fam_injective
  rw [SmoothTimeAlgebraOn.fam_add]
  rw [concreteEvalOn_concreteLiftOn_apply I M (f + g) hfg,
      concreteEvalOn_concreteLiftOn_apply I M f hf,
      concreteEvalOn_concreteLiftOn_apply I M g hg]

/-- `concreteLiftOn` is multiplicative on subset-smooth families. -/
theorem concreteLiftOn_mul
    {s : Set ℝ} (f g : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFamOn I M s f)
    (hg : concreteIsSmoothFamOn I M s g) :
    concreteLiftOn I M s (f * g) =
      concreteLiftOn I M s f * concreteLiftOn I M s g := by
  have hfg : concreteIsSmoothFamOn I M s (f * g) :=
    concreteIsSmoothFamOn_mul I M s f g hf hg
  apply SmoothTimeAlgebraOn.fam_injective
  rw [SmoothTimeAlgebraOn.fam_mul]
  rw [concreteEvalOn_concreteLiftOn_apply I M (f * g) hfg,
      concreteEvalOn_concreteLiftOn_apply I M f hf,
      concreteEvalOn_concreteLiftOn_apply I M g hg]

/-- `concreteLiftOn` of a constant family equals the algebra-map image of the
constant. -/
theorem concreteLiftOn_algebraMap {s : Set ℝ} (c : C^∞⟮I, M; ℝ⟯) :
    concreteLiftOn I M s (fun _ => c) =
      algebraMap C^∞⟮I, M; ℝ⟯ (SmoothTimeAlgebraOn I M s) c := by
  have hc : concreteIsSmoothFamOn I M s (fun _ => c) :=
    concreteIsSmoothFamOn_const I M s c
  apply SmoothTimeAlgebraOn.fam_injective
  rw [concreteEvalOn_concreteLiftOn_apply I M (fun _ => c) hc]
  funext t
  -- RHS reduces to `compSndRingHomOn c` by the `RingHom.toAlgebra` definition.
  change c = (SmoothTimeAlgebraOn.compSndRingHomOn (I := I) (M := M) (s := s) c).fam t
  simp

/-- `concreteEvalOn` is additive. -/
theorem concreteEvalOn_add
    {s : Set ℝ} (F G : SmoothTimeAlgebraOn I M s) (t : ℝ) :
    concreteEvalOn I M (F + G) t = concreteEvalOn I M F t + concreteEvalOn I M G t := by
  change (F + G).fam t = F.fam t + G.fam t
  rw [SmoothTimeAlgebraOn.fam_add]; rfl

/-- `concreteEvalOn` is multiplicative. -/
theorem concreteEvalOn_mul
    {s : Set ℝ} (F G : SmoothTimeAlgebraOn I M s) (t : ℝ) :
    concreteEvalOn I M (F * G) t = concreteEvalOn I M F t * concreteEvalOn I M G t := by
  change (F * G).fam t = F.fam t * G.fam t
  rw [SmoothTimeAlgebraOn.fam_mul]; rfl

/-- `concreteEvalOn` agrees with the algebra map on constant-in-time elements. -/
theorem concreteEvalOn_algebraMap {s : Set ℝ} (c : C^∞⟮I, M; ℝ⟯) (t : ℝ) :
    concreteEvalOn I M
        (algebraMap C^∞⟮I, M; ℝ⟯ (SmoothTimeAlgebraOn I M s) c) t = c := by
  -- `algebraMap = compSndRingHomOn` by the `RingHom.toAlgebra` instance.
  change (SmoothTimeAlgebraOn.compSndRingHomOn (I := I) (M := M) (s := s) c).fam t = c
  simp

-- ============================================================
-- Subset-time partial `derivWithin` as a `SmoothTimeAlgebraOn`
-- ============================================================

/-!
### Joint smoothness of the partial `derivWithin` in the time direction

The core technical lemma: if `F : ℝ × M → ℝ` is jointly `ContMDiffOn` on
`s ×ˢ univ` (with `UniqueDiffOn ℝ s`), then the uncurried partial derivative
`(t, x) ↦ derivWithin (fun τ => F (τ, x)) s t` is itself jointly `ContMDiffOn`
on `s ×ˢ univ`.

This is the subset-time analogue of `DifferentialGeometry.contMDiff_partial_deriv_fst`.
The proof reduces `derivWithin` to `mfderivWithin` applied to `1`, then invokes
`ContMDiffWithinAt.mfderivWithin_apply` with the product ambient space
`(ℝ × M) × ℝ` serving as the "parameter × differentiation" domain.
-/

/-- The partial `derivWithin` along the ℝ-factor of a function jointly
`ContMDiffOn` on `s ×ˢ univ` is itself jointly `ContMDiffOn` on `s ×ˢ univ`,
provided `UniqueDiffOn ℝ s`. -/
theorem contMDiffOn_partial_derivWithin_fst
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ F (s ×ˢ (Set.univ : Set M))) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => derivWithin (fun τ : ℝ => F (τ, p.2)) s p.1)
      (s ×ˢ (Set.univ : Set M)) := by
  -- Rewrite `derivWithin` as `mfderivWithin ... 1`.
  have hrw : (fun p : ℝ × M => derivWithin (fun τ : ℝ => F (τ, p.2)) s p.1) =
      fun p : ℝ × M =>
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun τ : ℝ => F (τ, p.2)) s p.1) (1 : ℝ) := by
    funext p
    rw [mfderivWithin_eq_fderivWithin]
    exact fderivWithin_derivWithin.symm
  rw [hrw]
  -- Reduce `∞` to every natural level.
  rw [contMDiffOn_infty]
  intro n p₀ hp₀
  -- Joint smoothness of `(q : (ℝ × M) × ℝ) ↦ F (q.2, q.1.2)` on
  -- `(s ×ˢ univ) ×ˢ s`: derived from `hF` by pre-composing with `(p, τ) ↦ (τ, p.2)`.
  have harg : ContMDiffOn ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : (ℝ × M) × ℝ => (q.2, q.1.2))
      ((s ×ˢ (Set.univ : Set M)) ×ˢ s) := by
    have h1 : ContMDiff ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : (ℝ × M) × ℝ => (q.2, q.1.2)) :=
      ContMDiff.prodMk contMDiff_snd contMDiff_fst.snd
    exact h1.contMDiffOn
  have hF' : ContMDiffOn ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : (ℝ × M) × ℝ => F (q.2, q.1.2))
      ((s ×ˢ (Set.univ : Set M)) ×ˢ s) := by
    have hmap : Set.MapsTo (fun q : (ℝ × M) × ℝ => (q.2, q.1.2))
        ((s ×ˢ (Set.univ : Set M)) ×ˢ s) (s ×ˢ (Set.univ : Set M)) := by
      intro q hq
      rcases hq with ⟨hq1, hq2⟩
      refine ⟨hq2, ?_⟩
      exact Set.mem_univ _
    exact hF.comp harg hmap
  -- Apply `ContMDiffWithinAt.mfderivWithin_apply` with `m = n`, `n' = n + 1`.
  have hmn : ((n : WithTop ℕ∞) : WithTop ℕ∞) + 1 ≤ ∞ := by
    exact_mod_cast le_top
  have hf_at :
      ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((n : WithTop ℕ∞) + 1)
        (Function.uncurry (fun (p : ℝ × M) (τ : ℝ) => F (τ, p.2)))
        ((s ×ˢ (Set.univ : Set M)) ×ˢ s) (p₀, p₀.1) := by
    have hmem : (p₀, p₀.1) ∈ (s ×ˢ (Set.univ : Set M)) ×ˢ s := by
      exact ⟨hp₀, hp₀.1⟩
    have hFat : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun q : (ℝ × M) × ℝ => F (q.2, q.1.2))
        ((s ×ˢ (Set.univ : Set M)) ×ˢ s) (p₀, p₀.1) := hF' _ hmem
    have hFat' : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        ((n : WithTop ℕ∞) + 1)
        (fun q : (ℝ × M) × ℝ => F (q.2, q.1.2))
        ((s ×ˢ (Set.univ : Set M)) ×ˢ s) (p₀, p₀.1) := hFat.of_le hmn
    -- `Function.uncurry` of `fun p τ => F (τ, p.2)` unfolds to `fun q => F (q.2, q.1.2)`.
    change ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        ((n : WithTop ℕ∞) + 1)
        (fun q : (ℝ × M) × ℝ => F (q.2, q.1.2))
        ((s ×ˢ (Set.univ : Set M)) ×ˢ s) (p₀, p₀.1)
    exact hFat'
  have h_apply :=
    ContMDiffWithinAt.mfderivWithin_apply
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (f := fun (p : ℝ × M) (τ : ℝ) => F (τ, p.2))
      (g := fun p : ℝ × M => p.1)
      (g₁ := fun p : ℝ × M => p)
      (g₂ := fun _ : ℝ × M => (1 : ℝ))
      (t := s ×ˢ (Set.univ : Set M))
      (u := s)
      (v := s ×ˢ (Set.univ : Set M))
      (x₀ := p₀)
      (m := (n : WithTop ℕ∞))
      (n := (n : WithTop ℕ∞) + 1)
      hf_at
      (contMDiffWithinAt_fst (I := 𝓘(ℝ, ℝ)) (J := I))
      contMDiffWithinAt_id
      contMDiffWithinAt_const
      le_rfl
      (Set.mapsTo_id _)
      hp₀
      (fun q hq => hq.1)
      hs.uniqueMDiffOn
  -- The source and target models are model spaces, so `inTangentCoordinates`
  -- collapses to the raw `mfderivWithin`.
  simpa [inTangentCoordinates_model_space] using h_apply

/-- Specialization: joint `ContMDiffOn` on `s ×ˢ univ` of the partial time
derivative of a `SmoothTimeAlgebraOn` element. -/
theorem SmoothTimeAlgebraOn.derivWithin_contMDiffOn
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (F : SmoothTimeAlgebraOn I M s) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => derivWithin (fun τ : ℝ => F.fam τ p.2) s p.1)
      (s ×ˢ (Set.univ : Set M)) :=
  contMDiffOn_partial_derivWithin_fst I M hs F.smooth_on

/-- Per-slice spatial smoothness at `t ∈ s`: if the joint `ContMDiffOn` holds
on `s ×ˢ univ`, then for every `t ∈ s` the spatial slice
`x ↦ derivWithin (fun τ => F.fam τ x) s t` is smooth on `M`. -/
theorem SmoothTimeAlgebraOn.derivWithin_contMDiff_slice
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (F : SmoothTimeAlgebraOn I M s)
    {t : ℝ} (ht : t ∈ s) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => derivWithin (fun τ : ℝ => F.fam τ x) s t) := by
  have hjoint := SmoothTimeAlgebraOn.derivWithin_contMDiffOn I M hs F
  intro x
  -- Compose with `x ↦ (t, x)`, which maps `univ : Set M` into `s ×ˢ univ`.
  have hemb : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (fun y : M => (t, y)) :=
    (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => t)).prodMk contMDiff_id
  have hmap : Set.MapsTo (fun y : M => (t, y))
      (Set.univ : Set M) (s ×ˢ (Set.univ : Set M)) := by
    intro y _
    exact ⟨ht, Set.mem_univ _⟩
  have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      ((fun p : ℝ × M => derivWithin (fun τ : ℝ => F.fam τ p.2) s p.1) ∘
        fun y : M => (t, y))
      (Set.univ : Set M) :=
    hjoint.comp hemb.contMDiffOn hmap
  -- Simplify the composition.
  have heq : ((fun p : ℝ × M => derivWithin (fun τ : ℝ => F.fam τ p.2) s p.1) ∘
      fun y : M => (t, y)) = fun y : M => derivWithin (fun τ : ℝ => F.fam τ y) s t := by
    funext y; rfl
  rw [heq] at hcomp
  exact (contMDiffOn_univ.mp hcomp) x

/-!
### The subset-time time-derivative family and its joint smoothness

We package the partial `derivWithin` as a curried family
`ℝ → C^∞⟮I, M; ℝ⟯`: at each `t ∈ s` the slice is the actual partial
derivative; at `t ∉ s` we take the slice to be `0` so the family is
well-defined on all of `ℝ`. Joint smoothness on `s ×ˢ univ` only sees the
`t ∈ s` case, where the conditional agrees with the actual derivative.
-/

/-- The per-slice component of the subset-time time-derivative: for `t ∈ s`,
the smooth function `x ↦ derivWithin (fun τ => F.fam τ x) s t`; for `t ∉ s`,
the zero function. -/
noncomputable def concreteDtOnFam {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (F : SmoothTimeAlgebraOn I M s) (t : ℝ) : C^∞⟮I, M; ℝ⟯ :=
  open Classical in
  if ht : t ∈ s then
    ⟨fun x : M => derivWithin (fun τ : ℝ => F.fam τ x) s t,
      SmoothTimeAlgebraOn.derivWithin_contMDiff_slice I M hs F ht⟩
  else 0

/-- On `s`, `concreteDtOnFam` has the expected underlying function. -/
theorem concreteDtOnFam_apply_of_mem {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (F : SmoothTimeAlgebraOn I M s) {t : ℝ} (ht : t ∈ s) (x : M) :
    (concreteDtOnFam I M hs F t : M → ℝ) x = derivWithin (fun τ : ℝ => F.fam τ x) s t := by
  simp only [concreteDtOnFam, dif_pos ht, ContMDiffMap.coeFn_mk]

/-- Off `s`, `concreteDtOnFam` is the zero function. -/
theorem concreteDtOnFam_of_notMem {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (F : SmoothTimeAlgebraOn I M s) {t : ℝ} (ht : t ∉ s) :
    concreteDtOnFam I M hs F t = 0 := by
  simp only [concreteDtOnFam, dif_neg ht]

/-- Joint smoothness of the uncurried `concreteDtOnFam` on `s ×ˢ univ`. -/
theorem concreteDtOnFam_smooth_on {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (F : SmoothTimeAlgebraOn I M s) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => concreteDtOnFam I M hs F p.1 p.2)
      (s ×ˢ (Set.univ : Set M)) := by
  -- On `s ×ˢ univ`, the uncurried `concreteDtOnFam` coincides with the raw
  -- `derivWithin`, which is jointly smooth by `derivWithin_contMDiffOn`.
  have hjoint := SmoothTimeAlgebraOn.derivWithin_contMDiffOn I M hs F
  refine hjoint.congr ?_
  intro p hp
  obtain ⟨ht, _⟩ := hp
  simp [concreteDtOnFam_apply_of_mem I M hs F ht p.2]

-- ============================================================
-- `concreteDtOn` as a `Derivation`
-- ============================================================

/-- Underlying set-function of the subset-time time-derivative: assembles the
per-slice `concreteDtOnFam` into a `SmoothTimeAlgebraOn` element. -/
noncomputable def concreteDtOnFun {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (F : SmoothTimeAlgebraOn I M s) : SmoothTimeAlgebraOn I M s where
  fam := concreteDtOnFam I M hs F
  smooth_on := concreteDtOnFam_smooth_on I M hs F

@[simp]
theorem concreteDtOnFun_fam {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (F : SmoothTimeAlgebraOn I M s) :
    (concreteDtOnFun I M hs F).fam = concreteDtOnFam I M hs F := rfl

/-- On `s`, the `fam` component of `concreteDtOnFun F` has the pointwise
`derivWithin` expression. -/
theorem concreteDtOnFun_fam_apply_of_mem
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (F : SmoothTimeAlgebraOn I M s) {t : ℝ} (ht : t ∈ s) (x : M) :
    ((concreteDtOnFun I M hs F).fam t : M → ℝ) x =
      derivWithin (fun τ : ℝ => F.fam τ x) s t := by
  change (concreteDtOnFam I M hs F t : M → ℝ) x = _
  exact concreteDtOnFam_apply_of_mem I M hs F ht x

/-!
### Per-slice differentiability witnesses

For the algebraic laws of `concreteDt` (additivity, Leibniz, …) we need each
`t ∈ s` slice `τ ↦ F.fam τ x` to be `DifferentiableWithinAt ℝ _ s t` for every
`x : M`. This follows from the joint `ContMDiffOn` hypothesis: the spatial
slice at fixed `x` is `ContMDiffOn ℝ ∞` on `s`, hence
`DifferentiableWithinAt` on `s`.
-/

/-- For any `x : M` and `t ∈ s`, the function `τ ↦ F.fam τ x` is
`DifferentiableWithinAt ℝ _ s t`. -/
theorem SmoothTimeAlgebraOn.fam_slice_differentiableWithinAt
    {s : Set ℝ} (F : SmoothTimeAlgebraOn I M s) (x : M) {t : ℝ} (ht : t ∈ s) :
    DifferentiableWithinAt ℝ (fun τ : ℝ => F.fam τ x) s t := by
  -- Compose `F.smooth_on` with `τ ↦ (τ, x)`.
  have hemb : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞ (fun τ : ℝ => (τ, x)) :=
    contMDiff_id.prodMk (contMDiff_const : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun _ : ℝ => x))
  have hmap : Set.MapsTo (fun τ : ℝ => (τ, x)) s (s ×ˢ (Set.univ : Set M)) := by
    intro τ hτ; exact ⟨hτ, Set.mem_univ _⟩
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      ((fun p : ℝ × M => F.fam p.1 p.2) ∘ fun τ : ℝ => (τ, x)) s :=
    F.smooth_on.comp hemb.contMDiffOn hmap
  have heq : ((fun p : ℝ × M => F.fam p.1 p.2) ∘ fun τ : ℝ => (τ, x)) =
      fun τ : ℝ => F.fam τ x := by
    funext τ; rfl
  rw [heq] at hcomp
  -- Transport `ContMDiffOn` to `ContDiffOn` (via `contMDiffOn_iff_contDiffOn`
  -- for model spaces).
  have hContDiff : ContDiffOn ℝ ∞ (fun τ : ℝ => F.fam τ x) s := by
    rw [contMDiffOn_iff_contDiffOn] at hcomp
    exact hcomp
  have hdiff : DifferentiableOn ℝ (fun τ : ℝ => F.fam τ x) s :=
    hContDiff.differentiableOn (by decide)
  exact hdiff t ht

/-- `concreteDtOnFun` is additive. -/
private theorem concreteDtOnFun_add
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (F G : SmoothTimeAlgebraOn I M s) :
    concreteDtOnFun I M hs (F + G) =
      concreteDtOnFun I M hs F + concreteDtOnFun I M hs G := by
  apply SmoothTimeAlgebraOn.fam_injective
  rw [SmoothTimeAlgebraOn.fam_add, concreteDtOnFun_fam, concreteDtOnFun_fam,
      concreteDtOnFun_fam]
  funext t
  ext x
  by_cases ht : t ∈ s
  · -- On `s`: use `derivWithin_add`.
    have hFdiff := SmoothTimeAlgebraOn.fam_slice_differentiableWithinAt I M F x ht
    have hGdiff := SmoothTimeAlgebraOn.fam_slice_differentiableWithinAt I M G x ht
    -- The slice of `F + G` equals `τ ↦ F.fam τ x + G.fam τ x`.
    have hslice : (fun τ : ℝ => (F + G).fam τ x) =
        (fun τ : ℝ => F.fam τ x) + (fun τ : ℝ => G.fam τ x) := by
      funext τ
      change ((F + G).fam τ : M → ℝ) x = ((F.fam τ : M → ℝ) x + (G.fam τ : M → ℝ) x)
      rw [SmoothTimeAlgebraOn.fam_add]
      change ((F.fam τ + G.fam τ) : C^∞⟮I, M; ℝ⟯) x = (F.fam τ) x + (G.fam τ) x
      simp [ContMDiffMap.coe_add]
    change (concreteDtOnFam I M hs (F + G) t : M → ℝ) x =
      ((concreteDtOnFam I M hs F t + concreteDtOnFam I M hs G t :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) x
    rw [concreteDtOnFam_apply_of_mem I M hs (F + G) ht x, hslice,
        derivWithin_add hFdiff hGdiff, ContMDiffMap.coe_add, Pi.add_apply,
        concreteDtOnFam_apply_of_mem I M hs F ht x,
        concreteDtOnFam_apply_of_mem I M hs G ht x]
  · -- Off `s`: all three slices are 0.
    change (concreteDtOnFam I M hs (F + G) t : M → ℝ) x =
      ((concreteDtOnFam I M hs F t + concreteDtOnFam I M hs G t :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) x
    rw [concreteDtOnFam_of_notMem I M hs (F + G) ht,
        concreteDtOnFam_of_notMem I M hs F ht,
        concreteDtOnFam_of_notMem I M hs G ht]
    simp

/-- `concreteDtOnFun` commutes with scalar multiplication by `C^∞⟮I, M; ℝ⟯`:
spatial smooth functions don't depend on time, so the time derivative
passes through. -/
private theorem concreteDtOnFun_smul
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (c : C^∞⟮I, M; ℝ⟯) (F : SmoothTimeAlgebraOn I M s) :
    concreteDtOnFun I M hs (c • F) = c • concreteDtOnFun I M hs F := by
  apply SmoothTimeAlgebraOn.fam_injective
  funext t
  ext x
  by_cases ht : t ∈ s
  · -- On `s`: `c • F` has slice `τ ↦ c x * F.fam τ x` at point `x`.
    have hFdiff := SmoothTimeAlgebraOn.fam_slice_differentiableWithinAt I M F x ht
    have hslice : (fun τ : ℝ => ((c • F).fam τ : M → ℝ) x) =
        fun τ : ℝ => c x * (F.fam τ : M → ℝ) x := by
      funext τ
      change ((c • F).fam τ : M → ℝ) x = c x * (F.fam τ : M → ℝ) x
      -- `c • F = (compSndRingHomOn c) * F` by `RingHom.toAlgebra`.
      change (((SmoothTimeAlgebraOn.compSndRingHomOn (I := I) (M := M) (s := s) c
        : SmoothTimeAlgebraOn I M s) * F).fam τ : M → ℝ) x = c x * (F.fam τ : M → ℝ) x
      rw [SmoothTimeAlgebraOn.fam_mul]
      change ((SmoothTimeAlgebraOn.compSndRingHomOn (I := I) (M := M) (s := s) c).fam τ *
        F.fam τ : C^∞⟮I, M; ℝ⟯) x = c x * (F.fam τ) x
      rw [ContMDiffMap.coe_mul]
      simp
    -- `c • concreteDtOnFun hs F` at `(t, x)` equals `c x * (concreteDtOnFun hs F).fam t x`.
    change (concreteDtOnFam I M hs (c • F) t : M → ℝ) x =
      ((c • concreteDtOnFun I M hs F).fam t : M → ℝ) x
    rw [concreteDtOnFam_apply_of_mem I M hs (c • F) ht x]
    -- Rewrite the slice.
    have hderivEq : derivWithin (fun τ : ℝ => ((c • F).fam τ : M → ℝ) x) s t =
        c x * derivWithin (fun τ : ℝ => (F.fam τ : M → ℝ) x) s t := by
      rw [hslice, derivWithin_const_mul _ hFdiff]
    change derivWithin (fun τ : ℝ => ((c • F).fam τ : M → ℝ) x) s t = _
    rw [hderivEq]
    -- Simplify the RHS: `c • concreteDtOnFun hs F` has fam `(compSndRingHomOn c) * fam`.
    change c x * derivWithin (fun τ : ℝ => (F.fam τ : M → ℝ) x) s t =
      ((SmoothTimeAlgebraOn.compSndRingHomOn (I := I) (M := M) (s := s) c *
        concreteDtOnFun I M hs F).fam t : M → ℝ) x
    rw [SmoothTimeAlgebraOn.fam_mul]
    change c x * derivWithin (fun τ : ℝ => (F.fam τ : M → ℝ) x) s t =
      (((SmoothTimeAlgebraOn.compSndRingHomOn (I := I) (M := M) (s := s) c).fam t *
        (concreteDtOnFun I M hs F).fam t : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
    rw [ContMDiffMap.coe_mul]
    change c x * derivWithin (fun τ : ℝ => (F.fam τ : M → ℝ) x) s t =
      (SmoothTimeAlgebraOn.compSndRingHomOn (I := I) (M := M) (s := s) c).fam t x *
        ((concreteDtOnFun I M hs F).fam t : M → ℝ) x
    rw [SmoothTimeAlgebraOn.fam_compSndRingHomOn,
        concreteDtOnFun_fam_apply_of_mem I M hs F ht x]
  · -- Off `s`: `concreteDtOnFam (c • F) t = 0` and `c • 0 = 0` on the slice.
    change (concreteDtOnFam I M hs (c • F) t : M → ℝ) x =
      ((c • concreteDtOnFun I M hs F).fam t : M → ℝ) x
    rw [concreteDtOnFam_of_notMem I M hs (c • F) ht]
    -- RHS: the slice of `c • concreteDtOnFun hs F` at `t ∉ s` is `c x * 0 = 0`.
    change ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x =
      ((SmoothTimeAlgebraOn.compSndRingHomOn (I := I) (M := M) (s := s) c *
        concreteDtOnFun I M hs F).fam t : M → ℝ) x
    rw [SmoothTimeAlgebraOn.fam_mul]
    change ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x =
      (((SmoothTimeAlgebraOn.compSndRingHomOn (I := I) (M := M) (s := s) c).fam t *
        (concreteDtOnFun I M hs F).fam t : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
    rw [ContMDiffMap.coe_mul]
    change ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x =
      (SmoothTimeAlgebraOn.compSndRingHomOn (I := I) (M := M) (s := s) c).fam t x *
        ((concreteDtOnFun I M hs F).fam t : M → ℝ) x
    change ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x =
      (SmoothTimeAlgebraOn.compSndRingHomOn (I := I) (M := M) (s := s) c).fam t x *
        ((concreteDtOnFam I M hs F t : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
    rw [concreteDtOnFam_of_notMem I M hs F ht]
    simp

/-- `concreteDtOnFun` satisfies the Leibniz rule. -/
private theorem concreteDtOnFun_mul
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (F G : SmoothTimeAlgebraOn I M s) :
    concreteDtOnFun I M hs (F * G) =
      F * concreteDtOnFun I M hs G + G * concreteDtOnFun I M hs F := by
  apply SmoothTimeAlgebraOn.fam_injective
  funext t
  ext x
  by_cases ht : t ∈ s
  · -- Product rule via `derivWithin_mul`.
    have hFdiff := SmoothTimeAlgebraOn.fam_slice_differentiableWithinAt I M F x ht
    have hGdiff := SmoothTimeAlgebraOn.fam_slice_differentiableWithinAt I M G x ht
    have hslice : (fun τ : ℝ => ((F * G).fam τ : M → ℝ) x) =
        (fun τ : ℝ => (F.fam τ : M → ℝ) x) *
          (fun τ : ℝ => (G.fam τ : M → ℝ) x) := by
      funext τ
      change ((F * G).fam τ : M → ℝ) x =
        (F.fam τ : M → ℝ) x * (G.fam τ : M → ℝ) x
      rw [SmoothTimeAlgebraOn.fam_mul]
      change ((F.fam τ * G.fam τ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = _
      rw [ContMDiffMap.coe_mul]; rfl
    -- LHS: derivWithin of the product slice.
    change (concreteDtOnFam I M hs (F * G) t : M → ℝ) x =
      ((F * concreteDtOnFun I M hs G + G * concreteDtOnFun I M hs F).fam t :
        M → ℝ) x
    rw [concreteDtOnFam_apply_of_mem I M hs (F * G) ht x]
    -- RHS: `fam_add`/`fam_mul` unfolding.
    rw [SmoothTimeAlgebraOn.fam_add, SmoothTimeAlgebraOn.fam_mul,
        SmoothTimeAlgebraOn.fam_mul]
    change derivWithin (fun τ : ℝ => ((F * G).fam τ : M → ℝ) x) s t =
      ((F.fam t * (concreteDtOnFun I M hs G).fam t +
        G.fam t * (concreteDtOnFun I M hs F).fam t : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
    rw [hslice, derivWithin_mul hFdiff hGdiff, ContMDiffMap.coe_add,
        ContMDiffMap.coe_mul, ContMDiffMap.coe_mul]
    change derivWithin (fun τ : ℝ => (F.fam τ : M → ℝ) x) s t *
          (G.fam t : M → ℝ) x +
        (F.fam t : M → ℝ) x *
          derivWithin (fun τ : ℝ => (G.fam τ : M → ℝ) x) s t =
      (F.fam t : M → ℝ) x * ((concreteDtOnFun I M hs G).fam t : M → ℝ) x +
      (G.fam t : M → ℝ) x * ((concreteDtOnFun I M hs F).fam t : M → ℝ) x
    rw [concreteDtOnFun_fam_apply_of_mem I M hs F ht x,
        concreteDtOnFun_fam_apply_of_mem I M hs G ht x]
    ring
  · -- Off `s`: all `concreteDtOn` slices are zero.
    change (concreteDtOnFam I M hs (F * G) t : M → ℝ) x =
      ((F * concreteDtOnFun I M hs G + G * concreteDtOnFun I M hs F).fam t :
        M → ℝ) x
    rw [concreteDtOnFam_of_notMem I M hs (F * G) ht,
        SmoothTimeAlgebraOn.fam_add, SmoothTimeAlgebraOn.fam_mul,
        SmoothTimeAlgebraOn.fam_mul]
    change ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x =
      ((F.fam t * (concreteDtOnFun I M hs G).fam t +
        G.fam t * (concreteDtOnFun I M hs F).fam t : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
    have hDG : (concreteDtOnFun I M hs G).fam t = 0 := by
      change concreteDtOnFam I M hs G t = 0
      exact concreteDtOnFam_of_notMem I M hs G ht
    have hDF : (concreteDtOnFun I M hs F).fam t = 0 := by
      change concreteDtOnFam I M hs F t = 0
      exact concreteDtOnFam_of_notMem I M hs F ht
    rw [hDG, hDF]
    simp

/-- `concreteDtOnFun` sends the constant `1` to `0`. -/
private theorem concreteDtOnFun_one {s : Set ℝ} (hs : UniqueDiffOn ℝ s) :
    concreteDtOnFun I M hs (1 : SmoothTimeAlgebraOn I M s) = 0 := by
  apply SmoothTimeAlgebraOn.fam_injective
  funext t
  ext x
  by_cases ht : t ∈ s
  · -- On `s`: the constant slice `τ ↦ 1` has derivWithin = 0.
    change (concreteDtOnFam I M hs (1 : SmoothTimeAlgebraOn I M s) t : M → ℝ) x =
      ((0 : SmoothTimeAlgebraOn I M s).fam t : M → ℝ) x
    rw [concreteDtOnFam_apply_of_mem I M hs 1 ht x]
    -- The slice `τ ↦ ((1 : _).fam τ : M → ℝ) x` is constantly 1 (so derivWithin = 0).
    have hslice : (fun τ : ℝ => ((1 : SmoothTimeAlgebraOn I M s).fam τ : M → ℝ) x) =
        fun _ : ℝ => (1 : ℝ) := by
      funext τ
      change ((1 : SmoothTimeAlgebraOn I M s).fam τ : M → ℝ) x = 1
      rw [SmoothTimeAlgebraOn.fam_one]
      change ((1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1
      rw [ContMDiffMap.coe_one]; rfl
    rw [hslice]
    change derivWithin (fun _ : ℝ => (1 : ℝ)) s t =
      ((0 : SmoothTimeAlgebraOn I M s).fam t : M → ℝ) x
    rw [show (fun _ : ℝ => (1 : ℝ)) = Function.const ℝ (1 : ℝ) from rfl,
        derivWithin_const]
    -- The RHS is `((0 : SmoothTimeAlgebraOn _).fam t : M → ℝ) x = 0`.
    change (0 : ℝ) = ((0 : SmoothTimeAlgebraOn I M s).fam t : M → ℝ) x
    rw [SmoothTimeAlgebraOn.fam_zero]
    change (0 : ℝ) = ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
    rw [ContMDiffMap.coe_zero]; rfl
  · -- Off `s`: both sides are 0.
    change (concreteDtOnFam I M hs (1 : SmoothTimeAlgebraOn I M s) t : M → ℝ) x =
      ((0 : SmoothTimeAlgebraOn I M s).fam t : M → ℝ) x
    rw [concreteDtOnFam_of_notMem I M hs 1 ht, SmoothTimeAlgebraOn.fam_zero]
    change ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
    rfl

/-- The subset-time time-derivation: the `Derivation` on
`SmoothTimeAlgebraOn I M s` induced by partial `derivWithin` in the
time direction. -/
noncomputable def concreteDtOn {s : Set ℝ} (hs : UniqueDiffOn ℝ s) :
    Derivation C^∞⟮I, M; ℝ⟯ (SmoothTimeAlgebraOn I M s)
      (SmoothTimeAlgebraOn I M s) where
  toLinearMap :=
    { toFun := concreteDtOnFun I M hs
      map_add' := concreteDtOnFun_add I M hs
      map_smul' := fun c F => concreteDtOnFun_smul I M hs c F }
  map_one_eq_zero' := concreteDtOnFun_one I M hs
  leibniz' F G := by
    change concreteDtOnFun I M hs (F * G) =
      F • concreteDtOnFun I M hs G + G • concreteDtOnFun I M hs F
    -- `•` on `SmoothTimeAlgebraOn` (as a module over itself) reduces to `*`.
    have hF_smul :
        (F : SmoothTimeAlgebraOn I M s) • (concreteDtOnFun I M hs G) =
          F * concreteDtOnFun I M hs G := smul_eq_mul _ _
    have hG_smul :
        (G : SmoothTimeAlgebraOn I M s) • (concreteDtOnFun I M hs F) =
          G * concreteDtOnFun I M hs F := smul_eq_mul _ _
    rw [hF_smul, hG_smul]
    exact concreteDtOnFun_mul I M hs F G

-- ============================================================
-- Package: `TimeDerivativeData` and `TimeRegularFam` on subset-time
-- ============================================================

/-- Subset-time `TimeDerivativeData`. -/
noncomputable def concreteTimeDerivativeDataOn
    (s : Set ℝ) (hs : UniqueDiffOn ℝ s) :
    TimeDerivativeData C^∞⟮I, M; ℝ⟯ (SmoothTimeAlgebraOn I M s) ℝ where
  dt := concreteDtOn I M hs
  lift := concreteLiftOn I M s
  eval := concreteEvalOn I M (s := s)
  lift_algebraMap := concreteLiftOn_algebraMap I M (s := s)
  eval_add := fun F G t => concreteEvalOn_add I M F G t
  eval_mul := fun F G t => concreteEvalOn_mul I M F G t
  eval_algebraMap := fun c t => concreteEvalOn_algebraMap I M (s := s) c t

/-- The distinguished `TimeRegularFam` realisation for subset-time: a family
is regular on `s` iff its uncurried map is jointly `ContMDiffOn` on
`s ×ˢ univ`. Registered as an `instance` so that downstream declarations
(structure fields depending on `concreteTimeDerivativeDataOn`) can resolve
the typeclass automatically. -/
@[reducible]
noncomputable instance concreteTimeRegularFamOn
    (s : Set ℝ) (hs : UniqueDiffOn ℝ s) :
    TimeRegularFam (concreteTimeDerivativeDataOn I M s hs) where
  isSmoothFam := concreteIsSmoothFamOn I M s
  eval_lift := fun f hf t => concreteEvalOn_concreteLiftOn I M (s := s) f hf t
  lift_add := fun f g hf hg => concreteLiftOn_add I M (s := s) f g hf hg
  lift_mul := fun f g hf hg => concreteLiftOn_mul I M (s := s) f g hf hg
  isSmoothFam_const := fun c => concreteIsSmoothFamOn_const I M s c
  isSmoothFam_add := fun f g hf hg => concreteIsSmoothFamOn_add I M s f g hf hg
  isSmoothFam_mul := fun f g hf hg => concreteIsSmoothFamOn_mul I M s f g hf hg
  isSmoothFam_neg := fun f hf => concreteIsSmoothFamOn_neg I M s f hf

