import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.RicciNorm
import DifferentialGeometry.Synthetic.Operator.CovariantDerivative
import DifferentialGeometry.Synthetic.Operator.SpatialConstant

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Three-Dimensional Curvature Algebra Interfaces

The Hamilton theorem in `RicciFlow/main.tex` uses curvature identities special
to dimension three. This file records those targets without committing the
project to a concrete finite-dimensional basis API yet.
-/

open SyntheticTensor

section DimensionThree

variable {R V : Type*}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- Synthetic marker for the three-dimensional algebra layer.

At this level, dimension is read through the abstract trace as `tr(id)`. -/
structure IsDimensionThree (atr : AbstractTrace R V) : Prop where
  abstractTraceDimension_eq_three : abstractTraceDimension atr = 3

theorem isDimensionThree_abstractTraceDimension (atr : AbstractTrace R V)
    (h : IsDimensionThree atr) :
    abstractTraceDimension atr = 3 :=
  h.abstractTraceDimension_eq_three

theorem isDimensionThree_nInv_normalization (atr : AbstractTrace R V)
    (h : IsDimensionThree atr) (nInv : R) (h_nInv_three : nInv * 3 = 1) :
    nInv * abstractTraceDimension atr = 1 := by
  rw [isDimensionThree_abstractTraceDimension atr h]
  exact h_nInv_three

end DimensionThree

section CurvatureIdentities

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Predicate saying that `half` is the coefficient `1 / 2`. -/
def IsHalfCoefficient (half : R) : Prop :=
  (2 : R) * half = 1

/-- The three-dimensional algebraic RHS expressing Riemann curvature through Ricci and scalar.

`half` stands for `1 / 2`, avoiding a field assumption on the coefficient ring.
The sign convention is the one used by the synthetic `Rm` pairing in this
project. The `IsHalfCoefficient half` argument keeps callers from using the
raw algebraic expression with an incoherent coefficient. -/
noncomputable def riemannFromRicci3DRHS
    (met : MetricDuality R V) (Rc : TensorData R V 0 2) (scalar half : R)
    (_h_half : IsHalfCoefficient half)
    (X Y Z W : V) : R :=
  Rc ![X, Z] ![] * met.g Y W +
    Rc ![Y, W] ![] * met.g X Z -
    Rc ![X, W] ![] * met.g Y Z -
    Rc ![Y, Z] ![] * met.g X W -
    half * scalar * (met.g X Z * met.g Y W - met.g X W * met.g Y Z)

theorem riemannFromRicci3DRHS_eval
    (met : MetricDuality R V) (Rc : TensorData R V 0 2) (scalar half : R)
    (h_half : IsHalfCoefficient half)
    (X Y Z W : V) :
    riemannFromRicci3DRHS met Rc scalar half h_half X Y Z W =
      Rc ![X, Z] ![] * met.g Y W +
        Rc ![Y, W] ![] * met.g X Z -
        Rc ![X, W] ![] * met.g Y Z -
        Rc ![Y, Z] ![] * met.g X W -
        half * scalar * (met.g X Z * met.g Y W - met.g X W * met.g Y Z) := by
  rfl

/-- Interface for the 3D formula expressing Riemann curvature through Ricci and scalar curvature. -/
def RiemannFromRicciFormula
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (_ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (_hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (_hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (_hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) (rhs : V -> V -> V -> V -> R) : Prop :=
  forall X Y Z W, met.g (Rm emb conn X Y Z) W = rhs X Y Z W

/-- Three-dimensional Riemann-from-Ricci formula with the coefficient constraint included. -/
structure RiemannFromRicci3DFormula
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (half : R) : Prop where
  h_half : IsHalfCoefficient half
  formula : RiemannFromRicciFormula emb conn ha hal hsl hl met
    (riemannFromRicci3DRHS met
      (ricciForm_tensor emb conn ha hal hsl hl atr)
      (ScalarCurvature emb conn ha hal hsl hl atr met) half h_half)

theorem riemannFromRicci3DFormula_half
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (half : R)
    (h : RiemannFromRicci3DFormula emb conn ha hal hsl hl atr met half) :
    IsHalfCoefficient half :=
  h.h_half

theorem riemannFromRicci3DFormula_apply
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (half : R)
    (h : RiemannFromRicci3DFormula emb conn ha hal hsl hl atr met half)
    (X Y Z W : V) :
    met.g (Rm emb conn X Y Z) W =
      riemannFromRicci3DRHS met
        (ricciForm_tensor emb conn ha hal hsl hl atr)
        (ScalarCurvature emb conn ha hal hsl hl atr met) half h.h_half X Y Z W :=
  h.formula X Y Z W

/-- In a field where `2` is nonzero, `2⁻¹` satisfies the abstract half constraint. -/
theorem isHalfCoefficient_inv_two {R : Type*} [Field R] (h_two : (2 : R) ≠ 0) :
    IsHalfCoefficient ((2 : R)⁻¹) := by
  unfold IsHalfCoefficient
  exact mul_inv_cancel₀ h_two

/-- Turn a nonzero coefficient into the cancellation hypothesis used by the
contracted-Bianchi consumer. In field-valued concrete calls this is usually
applied to `half - third`. -/
theorem coeff_cancel_of_ne {R : Type*} [CommRing R] [NoZeroDivisors R]
    {c : R} (hc : c ≠ 0) :
    forall a, c * a = 0 -> a = 0 := by
  intro a h
  exact (mul_eq_zero.mp h).resolve_left hc

/-- Predicate saying that `third` is the coefficient `1 / 3`. -/
def IsThirdCoefficient (third : R) : Prop :=
  (3 : R) * third = 1

/-- Ricci is pure trace with coefficient `third`, i.e. `Rc = (R/3)g`. -/
def EinsteinRicciFormula
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (third : R) : Prop :=
  forall X Y,
    ricciForm_tensor emb conn ha hal hsl hl atr ![X, Y] ![] =
      third * ScalarCurvature emb conn ha hal hsl hl atr met * met.g X Y

/-- Vanishing trace-free Ricci gives the pure-trace Einstein Ricci formula,
once the pure-trace coefficient is identified with the chosen `nInv`. -/
theorem einsteinRicciFormula_of_tracefree_ricci_tensor_eq_zero
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv third : R)
    (h_zero : tracefree_ricci_tensor emb conn ha hal hsl hl atr met nInv = 0)
    (h_third : third = nInv) :
    EinsteinRicciFormula emb conn ha hal hsl hl atr met third := by
  intro X Y
  have h := congr_arg (fun T : TensorData R V 0 2 => T ![X, Y] ![]) h_zero
  change tracefree_ricci_tensor emb conn ha hal hsl hl atr met nInv ![X, Y] ![] =
    (0 : TensorData R V 0 2) ![X, Y] ![] at h
  rw [tracefree_ricci_tensor_eval] at h
  simp only [MultilinearMap.zero_apply] at h
  rw [h_third]
  simpa [mul_assoc] using sub_eq_zero.mp h

/-- Divergence of Ricci, evaluated at `Y`, using the narrow `(0,2)` tensor
divergence API from Section 14.2. -/
noncomputable def ricciDivergenceAt
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (Y : V) : R :=
  covariantDivergence02At emb met atr conn ha hal hsl hl
    (ricciForm_tensor emb conn ha hal hsl hl atr) Y

/-- Contracted second Bianchi identity in the form needed for Lemma 11.6:
`div Ric = (1/2) dR`. This is a concrete equation over the synthetic Ricci and
scalar-curvature objects; proving it from `second_bianchi` is the next tensor
calculus target. -/
def ContractedSecondBianchiIdentity
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (half : R) : Prop :=
  IsHalfCoefficient half /\
    forall Y,
      ricciDivergenceAt emb conn ha hal hsl hl atr met Y =
        half * grad_R emb conn ha hal hsl hl atr met Y

theorem contractedSecondBianchi_apply
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (half : R)
    (h : ContractedSecondBianchiIdentity emb conn ha hal hsl hl atr met half)
    (Y : V) :
    ricciDivergenceAt emb conn ha hal hsl hl atr met Y =
      half * grad_R emb conn ha hal hsl hl atr met Y :=
  h.2 Y

/-- Tensor-calculus product-rule target for an Einstein Ricci tensor:
if `Ric = third * R * g`, then `div Ric = third * dR`.
This is separated from `EinsteinRicciFormula` until the divergence product rule
for scalar multiples of the metric is proved. -/
def EinsteinDivergenceFormula
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (third : R) : Prop :=
  forall Y,
    ricciDivergenceAt emb conn ha hal hsl hl atr met Y =
      third * grad_R emb conn ha hal hsl hl atr met Y

/-- Product-rule proof of the Einstein-divergence formula:
from `Ric = third * R * g`, metric compatibility, and spatial constancy of
`third`, one gets `div Ric = third * dR`. -/
theorem einsteinDivergenceFormula_of_einsteinRicciFormula
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (third : R)
    (h_mc : IsMetricCompatible emb conn met)
    (h_third_const : IsSpatialConstant emb third)
    (h_einstein : EinsteinRicciFormula emb conn ha hal hsl hl atr met third) :
    EinsteinDivergenceFormula emb conn ha hal hsl hl atr met third := by
  intro Y
  have h_tensor :
      ricciForm_tensor emb conn ha hal hsl hl atr =
        (third * ScalarCurvature emb conn ha hal hsl hl atr met) • met.g_tensor := by
    ext vs αs
    have hαs : αs = ![] := by
      ext i
      exact i.elim0
    rw [hαs]
    have hvs : vs = ![vs 0, vs 1] := by
      ext i
      fin_cases i <;> rfl
    rw [hvs]
    rw [MetricDuality.g_tensor_smul_eval]
    simpa [mul_assoc] using h_einstein (vs 0) (vs 1)
  unfold ricciDivergenceAt
  rw [h_tensor]
  rw [covariantDivergence02At_smul_metric emb met atr conn ha hal hsl hl h_mc
    (third * ScalarCurvature emb conn ha hal hsl hl atr met) Y]
  rw [action_smul_right emb Y third (ScalarCurvature emb conn ha hal hsl hl atr met),
    h_third_const Y, zero_mul, zero_add]
  rfl

/-- Differential half of Lemma 11.6 as a tensor-calculus consumer: contracted
Bianchi plus the divergence formula for an Einstein Ricci tensor force scalar
curvature to be spatially constant, provided `half - third` is cancellable. -/
theorem scalar_spatial_constant_of_contracted_bianchi_and_einstein_divergence
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (half third : R)
    (h_bianchi : ContractedSecondBianchiIdentity emb conn ha hal hsl hl atr met half)
    (h_ein_div : EinsteinDivergenceFormula emb conn ha hal hsl hl atr met third)
    (h_coeff_cancel : forall a, (half - third) * a = 0 -> a = 0) :
    IsSpatialConstant emb (ScalarCurvature emb conn ha hal hsl hl atr met) := by
  intro Y
  change grad_R emb conn ha hal hsl hl atr met Y = 0
  apply h_coeff_cancel
  have h_cb := contractedSecondBianchi_apply emb conn ha hal hsl hl atr met half h_bianchi Y
  have h_div := h_ein_div Y
  calc
    (half - third) * grad_R emb conn ha hal hsl hl atr met Y
        = half * grad_R emb conn ha hal hsl hl atr met Y -
            third * grad_R emb conn ha hal hsl hl atr met Y := by ring
    _ = ricciDivergenceAt emb conn ha hal hsl hl atr met Y -
            ricciDivergenceAt emb conn ha hal hsl hl atr met Y := by
          rw [← h_cb, ← h_div]
    _ = 0 := by ring

/-- Differential half of Lemma 11.6 starting from vanishing trace-free Ricci.
This packages the already-proved pure-trace algebra bridge with the product-rule
proof of the Einstein-divergence formula. The only remaining analytic/geometric
input is the contracted second Bianchi identity. -/
theorem scalar_spatial_constant_of_contracted_bianchi_and_tracefree_ricci_zero
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv half : R)
    (h_zero : tracefree_ricci_tensor emb conn ha hal hsl hl atr met nInv = 0)
    (h_mc : IsMetricCompatible emb conn met)
    (h_nInv_const : IsSpatialConstant emb nInv)
    (h_bianchi : ContractedSecondBianchiIdentity emb conn ha hal hsl hl atr met half)
    (h_coeff_cancel : forall a, (half - nInv) * a = 0 -> a = 0) :
    IsSpatialConstant emb (ScalarCurvature emb conn ha hal hsl hl atr met) := by
  have h_einstein :
      EinsteinRicciFormula emb conn ha hal hsl hl atr met nInv :=
    einsteinRicciFormula_of_tracefree_ricci_tensor_eq_zero emb conn ha hal hsl hl
      atr met nInv nInv h_zero rfl
  have h_ein_div :
      EinsteinDivergenceFormula emb conn ha hal hsl hl atr met nInv :=
    einsteinDivergenceFormula_of_einsteinRicciFormula emb conn ha hal hsl hl
      atr met nInv h_mc h_nInv_const h_einstein
  exact scalar_spatial_constant_of_contracted_bianchi_and_einstein_divergence
    emb conn ha hal hsl hl atr met half nInv h_bianchi h_ein_div h_coeff_cancel

/-- Constant-sectional-curvature Riemann tensor formula with coefficient `sectionalCoeff`. -/
def ConstantSectionalCurvatureFormula
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (met : MetricDuality R V) (scalar sectionalCoeff : R) : Prop :=
  forall X Y Z W,
    met.g (Rm emb conn X Y Z) W =
      sectionalCoeff * scalar * (met.g X Z * met.g Y W - met.g X W * met.g Y Z)

/-- Scalar algebra behind the 3D Einstein-to-space-form curvature formula. -/
theorem einsteinRiemannCoefficient_algebra (half third scalar A B C D : R) :
    third * scalar * A * C + third * scalar * C * A -
        third * scalar * B * D - third * scalar * D * B -
        half * scalar * (A * C - B * D) =
      (2 * third - half) * scalar * (A * C - B * D) := by
  ring

/-- Algebraic part of Lemma 11.6: in dimension three, an Einstein metric has
the constant-sectional-curvature Riemann tensor form. The differential step
that the scalar curvature is constant comes from the contracted Bianchi
identity and is represented separately in the global/realization layer. -/
theorem riemannFromRicci3DFormula_constant_curvature_of_einstein
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (half third : R)
    (h_riem : RiemannFromRicci3DFormula emb conn ha hal hsl hl atr met half)
    (h_einstein : EinsteinRicciFormula emb conn ha hal hsl hl atr met third) :
    ConstantSectionalCurvatureFormula emb conn met
      (ScalarCurvature emb conn ha hal hsl hl atr met) (2 * third - half) := by
  intro X Y Z W
  rw [riemannFromRicci3DFormula_apply emb conn ha hal hsl hl atr met half h_riem X Y Z W]
  unfold riemannFromRicci3DRHS
  rw [h_einstein X Z, h_einstein Y W, h_einstein X W, h_einstein Y Z]
  exact einsteinRiemannCoefficient_algebra half third
    (ScalarCurvature emb conn ha hal hsl hl atr met)
    (met.g X Z) (met.g X W) (met.g Y W) (met.g Y Z)

/-- Numerator of sectional curvature; denominator normalization is a later bridge target. -/
noncomputable def sectional_curvature_numerator
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (met : MetricDuality R V) (X Y : V) : R :=
  met.g (Rm emb conn X Y Y) X

/-- Nonnegative Ricci curvature as a pointwise quadratic-form condition. -/
def NonnegativeRicci [Preorder R]
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) : Prop :=
  forall X, 0 <= ricciForm_tensor emb conn ha hal hsl hl atr ![X, X] ![]

/-- Interface for the estimate that, in dimension three, nonnegative Ricci controls Riemann. -/
def CurvatureControlledByRicci [Preorder R]
    (rmNorm ricciNorm constant : R) : Prop :=
  rmNorm <= constant * ricciNorm

theorem curvature_control_from_interface [Preorder R]
    (rmNorm ricciNorm constant : R)
    (h : CurvatureControlledByRicci rmNorm ricciNorm constant) :
    rmNorm <= constant * ricciNorm :=
  h

/-- Chapter 11 corollary interface: in dimension three, nonnegative Ricci
controls the full curvature norm by scalar curvature. -/
def CurvatureControlledByScalar3D [Preorder R]
    (rmNorm scalar constant : R) : Prop :=
  rmNorm <= constant * scalar

theorem curvature_control_by_scalar_from_interface [Preorder R]
    (rmNorm scalar constant : R)
    (h : CurvatureControlledByScalar3D rmNorm scalar constant) :
    rmNorm <= constant * scalar :=
  h

end CurvatureIdentities
