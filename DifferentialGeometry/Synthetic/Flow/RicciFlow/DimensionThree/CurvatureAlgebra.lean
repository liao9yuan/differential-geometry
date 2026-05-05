import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.RicciNorm
import DifferentialGeometry.Synthetic.Geometry.CurvatureContractions
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

/-- Constructor for the coefficient-safe 3D Riemann-from-Ricci interface.

This is the quote point for realization layers that have proved the algebraic
3D curvature formula by finite-dimensional linear algebra. The stronger
synthetic target is to derive `h_formula` from `IsDimensionThree atr` plus the
Riemann symmetries and first Bianchi identity. -/
theorem riemannFromRicci3DFormula_of_formula
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (half : R)
    (h_half : IsHalfCoefficient half)
    (h_formula : RiemannFromRicciFormula emb conn ha hal hsl hl met
      (riemannFromRicci3DRHS met
        (ricciForm_tensor emb conn ha hal hsl hl atr)
        (ScalarCurvature emb conn ha hal hsl hl atr met) half h_half)) :
    RiemannFromRicci3DFormula emb conn ha hal hsl hl atr met half :=
  ⟨h_half, h_formula⟩

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

theorem isThirdCoefficient_of_mul_three_eq_one (third : R)
    (h_third : third * 3 = 1) :
    IsThirdCoefficient third := by
  unfold IsThirdCoefficient
  calc
    (3 : R) * third = third * 3 := by ring
    _ = 1 := h_third

/-- In the Einstein 3D space-form coefficient, `2 * (1/3) - (1/2)` is
normalized as `1/6`, stated without division by requiring multiplication by
`6` to give `1`. -/
theorem einsteinRiemannCoefficient_sixth
    (half third : R)
    (h_half : IsHalfCoefficient half)
    (h_third : IsThirdCoefficient third) :
    (6 : R) * (2 * third - half) = 1 := by
  unfold IsHalfCoefficient at h_half
  unfold IsThirdCoefficient at h_third
  calc
    (6 : R) * (2 * third - half) =
        4 * ((3 : R) * third) - 3 * ((2 : R) * half) := by ring
    _ = 4 * 1 - 3 * 1 := by rw [h_third, h_half]
    _ = 1 := by ring

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

/-- Divergence of Ricci in the opposite Ricci slot, evaluated at `Y`.

The named contracted-Bianchi divergence trace leaves the Ricci slot that
corresponds to `(∇_A Ric)(Y, Z)` before the final metric trace. This accessor
records that slot order explicitly. A later Ricci-symmetry bridge should
identify it with `ricciDivergenceAt` for Levi-Civita curvature. -/
noncomputable def ricciDivergenceAtSecond
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (Y : V) : R :=
  covariantDivergence02At emb met atr conn ha hal hsl hl
    (swap_covariant (0 : Fin 2) 1
      (ricciForm_tensor emb conn ha hal hsl hl atr)) Y

/-- If the Ricci `(0,2)` tensor is symmetric as a tensor, the two slot
conventions for Ricci divergence agree. This is the exact symmetry bridge
needed after the named contracted-Bianchi divergence pattern is identified
with `ricciDivergenceAtSecond`. -/
theorem ricciDivergenceAtSecond_eq_ricciDivergenceAt_of_ricciForm_tensor_symm
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_symm : swap_covariant (0 : Fin 2) 1
        (ricciForm_tensor emb conn ha hal hsl hl atr) =
      ricciForm_tensor emb conn ha hal hsl hl atr)
    (Y : V) :
    ricciDivergenceAtSecond emb conn ha hal hsl hl atr met Y =
      ricciDivergenceAt emb conn ha hal hsl hl atr met Y := by
  unfold ricciDivergenceAtSecond ricciDivergenceAt
  rw [h_symm]

/-- The raw covariant derivative of the Ricci `(0,2)` tensor is the synthetic
`covDerivRc` scalar expression. This is the first definitional bridge needed
to contract the vector-level second Bianchi identity into `div Ric = 1/2 dR`. -/
theorem rawCovDeriv_ricciForm_tensor_eq_covDerivRc
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (X Z Y : V) :
    rawCovDeriv emb conn X (ricciForm_tensor emb conn ha hal hsl hl atr) Z Y =
      covDerivRc emb conn ha hal hsl hl atr X Z Y := by
  unfold rawCovDeriv covDerivRc
  rw [ricciForm_tensor_eval, ricciForm_tensor_eval, ricciForm_tensor_eval]

/-- The covector traced in the `(0,2)` divergence API specializes to
`covDerivRc` when the tensor is Ricci. -/
theorem covDeriv02TraceCovector_ricciForm_tensor_apply
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (X Y Z : V) :
    covDeriv02TraceCovector emb conn ha hl X
        (ricciForm_tensor emb conn ha hal hsl hl atr) Y Z =
      covDerivRc emb conn ha hal hsl hl atr X Z Y := by
  change rawCovDeriv emb conn X (ricciForm_tensor emb conn ha hal hsl hl atr) Z Y =
    covDerivRc emb conn ha hal hsl hl atr X Z Y
  exact rawCovDeriv_ricciForm_tensor_eq_covDerivRc emb conn ha hal hsl hl atr X Z Y

/-- The covector traced in `ricciDivergenceAtSecond` has the Ricci arguments
in the order produced by the current named double-trace pattern. -/
theorem covDeriv02TraceCovector_swap_ricciForm_tensor_apply
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (X Y Z : V) :
    covDeriv02TraceCovector emb conn ha hl X
        (swap_covariant (0 : Fin 2) 1
          (ricciForm_tensor emb conn ha hal hsl hl atr)) Y Z =
      covDerivRc emb conn ha hal hsl hl atr X Y Z := by
  change rawCovDeriv emb conn X
      (swap_covariant (0 : Fin 2) 1
        (ricciForm_tensor emb conn ha hal hsl hl atr)) Z Y =
    covDerivRc emb conn ha hal hsl hl atr X Y Z
  unfold rawCovDeriv covDerivRc
  simp only [swap_covariant_eval]
  have h0 : (![Z, Y] : Fin 2 -> V) ∘ Equiv.swap (0 : Fin 2) 1 = ![Y, Z] := by
    ext i
    fin_cases i <;> rfl
  have h1 : (![conn X Z, Y] : Fin 2 -> V) ∘ Equiv.swap (0 : Fin 2) 1 =
      ![Y, conn X Z] := by
    ext i
    fin_cases i <;> rfl
  have h2 : (![Z, conn X Y] : Fin 2 -> V) ∘ Equiv.swap (0 : Fin 2) 1 =
      ![conn X Y, Z] := by
    ext i
    fin_cases i <;> rfl
  rw [h0, h1, h2, ricciForm_tensor_eval, ricciForm_tensor_eval, ricciForm_tensor_eval]
  ring

/-- Pairing the divergence endomorphism for the swapped Ricci tensor with the
metric recovers the Ricci covariant derivative in the slot order produced by
`ricciDivergenceAtSecond`. -/
theorem covDivergence02Endomorphism_swap_ricciForm_metric_apply
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (X Y Z : V) :
    met.g
        (covDivergence02Endomorphism emb met conn ha hal hsl hl
          (swap_covariant (0 : Fin 2) 1
            (ricciForm_tensor emb conn ha hal hsl hl atr)) Y X) Z =
      covDerivRc emb conn ha hal hsl hl atr X Y Z := by
  unfold covDivergence02Endomorphism
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [met.g_sharp]
  exact covDeriv02TraceCovector_swap_ricciForm_tensor_apply
    emb conn ha hal hsl hl atr X Y Z

/-- Evaluation form of `ricciDivergenceAtSecond`: it is the trace of the
endomorphism whose metric pairing is `(∇_X Ric)(Y,Z)`. -/
theorem ricciDivergenceAtSecond_eq_trace_swap_ricci_divergence_endomorphism
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (Y : V) :
    ricciDivergenceAtSecond emb conn ha hal hsl hl atr met Y =
      atr.tr
        (covDivergence02Endomorphism emb met conn ha hal hsl hl
          (swap_covariant (0 : Fin 2) 1
            (ricciForm_tensor emb conn ha hal hsl hl atr)) Y) := by
  rfl

/-- Reduction lemma for the divergence named pattern.

If a raw contraction calculation identifies the named divergence pattern with
the trace of the swapped-Ricci divergence endomorphism, then it is exactly
`ricciDivergenceAtSecond`. -/
theorem contractedBianchiDivPattern_apply_eq_neg_ricciDivergenceAtSecond_of_neg_trace_swap_ricci_divergence
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (Y : V)
    (h_trace :
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        - atr.tr
          (covDivergence02Endomorphism emb met conn ha hal hsl hl
            (swap_covariant (0 : Fin 2) 1
              (ricciForm_tensor emb conn ha hal hsl hl atr)) Y)) :
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        - ricciDivergenceAtSecond emb conn ha hal hsl hl atr met Y := by
  rw [h_trace]
  rw [ricciDivergenceAtSecond_eq_trace_swap_ricci_divergence_endomorphism
    emb conn ha hal hsl hl atr met Y]

/-- Ricci symmetry from the algebraic curvature symmetries plus trace
invariance under metric adjoints.

The curvature calculation shows that the two Ricci endomorphisms are metric
adjoints. The trace bridge then identifies their traces. -/
theorem Rc_symm_of_metric_adjoint_trace_invariant
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasMetricAdjointTraceInvariant atr met]
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn)
    (h2 : forall a : R, (2 : R) * a = 0 -> a = 0)
    (X Y : V) :
    Rc emb conn ha hal hsl hl atr X Y =
      Rc emb conn ha hal hsl hl atr Y X := by
  unfold Rc
  exact HasMetricAdjointTraceInvariant.trace_eq_of_metric_adjoint
    (atr := atr) (met := met)
    (RcEndo emb conn ha hal hsl hl X Y)
    (RcEndo emb conn ha hal hsl hl Y X)
    (by
      intro E F
      calc
        met.g (RcEndo emb conn ha hal hsl hl X Y E) F =
            met.g (Rm emb conn X E Y) F := rfl
        _ = met.g (Rm emb conn Y F X) E := by
          exact Rm_symm_blocks emb conn ha hal met h_mc h_tf h2 X E Y F
        _ = met.g E (Rm emb conn Y F X) := by
          exact met.g_symm (Rm emb conn Y F X) E
        _ = met.g E (RcEndo emb conn ha hal hsl hl Y X F) := rfl)

/-- Pointwise Ricci symmetry gives the tensor-level symmetry form used by the
P1 contracted-Bianchi divergence wrappers. -/
theorem ricciForm_tensor_symm_of_Rc_symm
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V)
    (h_Rc_symm : forall X Y,
      Rc emb conn ha hal hsl hl atr X Y =
        Rc emb conn ha hal hsl hl atr Y X) :
    swap_covariant (0 : Fin 2) 1
        (ricciForm_tensor emb conn ha hal hsl hl atr) =
      ricciForm_tensor emb conn ha hal hsl hl atr := by
  ext vs αs
  have hvs : vs = ![vs 0, vs 1] := by
    ext i
    fin_cases i <;> rfl
  have hswap :
      (![vs 0, vs 1] : Fin 2 -> V) ∘ Equiv.swap (0 : Fin 2) 1 =
        ![vs 1, vs 0] := by
    ext i
    fin_cases i <;> rfl
  rw [hvs]
  simp only [swap_covariant_eval, hswap]
  exact (h_Rc_symm (vs 0) (vs 1)).symm

/-- Pointwise Ricci symmetry is enough to convert the second-slot Ricci
divergence convention to the public `ricciDivergenceAt` convention. -/
theorem ricciDivergenceAtSecond_eq_ricciDivergenceAt_of_Rc_symm
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_Rc_symm : forall X Y,
      Rc emb conn ha hal hsl hl atr X Y =
        Rc emb conn ha hal hsl hl atr Y X)
    (Y : V) :
    ricciDivergenceAtSecond emb conn ha hal hsl hl atr met Y =
      ricciDivergenceAt emb conn ha hal hsl hl atr met Y :=
  ricciDivergenceAtSecond_eq_ricciDivergenceAt_of_ricciForm_tensor_symm
    emb conn ha hal hsl hl atr met
    (ricciForm_tensor_symm_of_Rc_symm emb conn ha hal hsl hl atr h_Rc_symm) Y

/-- Tensor-level Ricci symmetry from curvature symmetries and trace invariance
under metric adjoints. -/
theorem ricciForm_tensor_symm_of_metric_adjoint_trace_invariant
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasMetricAdjointTraceInvariant atr met]
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn)
    (h2 : forall a : R, (2 : R) * a = 0 -> a = 0) :
    swap_covariant (0 : Fin 2) 1
        (ricciForm_tensor emb conn ha hal hsl hl atr) =
      ricciForm_tensor emb conn ha hal hsl hl atr :=
  ricciForm_tensor_symm_of_Rc_symm emb conn ha hal hsl hl atr
    (Rc_symm_of_metric_adjoint_trace_invariant
      emb conn ha hal hsl hl atr met h_mc h_tf h2)

/-- Divergence-convention conversion from curvature symmetries and trace
invariance under metric adjoints. -/
theorem ricciDivergenceAtSecond_eq_ricciDivergenceAt_of_metric_adjoint_trace_invariant
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasMetricAdjointTraceInvariant atr met]
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn)
    (h2 : forall a : R, (2 : R) * a = 0 -> a = 0)
    (Y : V) :
    ricciDivergenceAtSecond emb conn ha hal hsl hl atr met Y =
      ricciDivergenceAt emb conn ha hal hsl hl atr met Y :=
  ricciDivergenceAtSecond_eq_ricciDivergenceAt_of_ricciForm_tensor_symm
    emb conn ha hal hsl hl atr met
    (ricciForm_tensor_symm_of_metric_adjoint_trace_invariant
      emb conn ha hal hsl hl atr met h_mc h_tf h2) Y

/-- Endomorphism form of `∇_X Rm(·, Z)Y`.

It is defined through the commutator with the connection and the two correction
terms for the differentiated `Z` and `Y` slots. This avoids separately proving
linearity of `covDerivRm` in the traced argument. -/
noncomputable def covDerivRmEndomorphism
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Z Y : V) : V →ₗ[R] V :=
  commutatorEndo (emb.embed X).toFun (conn X) (ha X) (hl X)
      (RcEndo emb conn ha hal hsl hl Z Y) -
    RcEndo emb conn ha hal hsl hl (conn X Z) Y -
      RcEndo emb conn ha hal hsl hl Z (conn X Y)

theorem covDerivRmEndomorphism_apply
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Z Y E : V) :
    covDerivRmEndomorphism emb conn ha hal hsl hl X Z Y E =
      covDerivRm emb conn X Z E Y := by
  unfold covDerivRmEndomorphism covDerivRm RcEndo commutatorEndo
  simp only [LinearMap.sub_apply, LinearMap.coe_mk, AddHom.coe_mk]
  abel

/-- Trace-commutation bridge: the covariant derivative of Ricci is the trace of
the covariant derivative of Riemann in the traced curvature slot. -/
theorem covDerivRc_eq_trace_covDerivRmEndomorphism
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V)
    (h_ntr : NablaTrComm emb atr conn ha hl)
    (X Z Y : V) :
    covDerivRc emb conn ha hal hsl hl atr X Z Y =
      atr.tr (covDerivRmEndomorphism emb conn ha hal hsl hl X Z Y) := by
  unfold covDerivRc Rc covDerivRmEndomorphism
  rw [h_ntr X (RcEndo emb conn ha hal hsl hl Z Y)]
  simp only [map_sub]

/-- Endomorphism form of the covariant derivative of the Ricci endomorphism. -/
noncomputable def covDerivRicciEndomorphism
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (X : V) : V →ₗ[R] V :=
  commutatorEndo (emb.embed X).toFun (conn X) (ha X) (hl X)
    (RicciEndomorphism emb conn ha hal hsl hl atr met)

/-- Trace-commutation bridge for scalar curvature:
`dR(X)` is the trace of `∇_X Ric♯`. -/
theorem grad_R_eq_trace_covDerivRicciEndomorphism
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_ntr : NablaTrComm emb atr conn ha hl)
    (X : V) :
    grad_R emb conn ha hal hsl hl atr met X =
      atr.tr (covDerivRicciEndomorphism emb conn ha hal hsl hl atr met X) := by
  unfold grad_R ScalarCurvature covDerivRicciEndomorphism
  exact h_ntr X (RicciEndomorphism emb conn ha hal hsl hl atr met)

/-- Pairing `∇Ric♯` with the metric recovers the covariant derivative of the
Ricci `(0,2)` tensor. -/
theorem covDerivRicciEndomorphism_metric_apply
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (X Z Y : V) :
    met.g (covDerivRicciEndomorphism emb conn ha hal hsl hl atr met X Z) Y =
      covDerivRc emb conn ha hal hsl hl atr X Z Y := by
  unfold covDerivRicciEndomorphism covDerivRc commutatorEndo
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [MetricDuality.g_sub_left]
  have h_conn :
      met.g (conn X (RicciEndomorphism emb conn ha hal hsl hl atr met Z)) Y =
        (emb.embed X) (Rc emb conn ha hal hsl hl atr Z Y) -
          Rc emb conn ha hal hsl hl atr Z (conn X Y) := by
    have h := h_mc X (RicciEndomorphism emb conn ha hal hsl hl atr met Z) Y
    rw [RicciEndomorphism_spec emb conn ha hal hsl hl atr met Z Y] at h
    rw [RicciEndomorphism_spec emb conn ha hal hsl hl atr met Z (conn X Y)] at h
    exact eq_sub_of_add_eq h.symm
  rw [h_conn]
  rw [RicciEndomorphism_spec emb conn ha hal hsl hl atr met (conn X Z) Y]
  ring

/-- Reduction lemma for the scalar-gradient named pattern.

If a double-trace calculation identifies the named gradient pattern with the
negative trace of `∇ Ric♯`, then `NablaTrComm` converts it to the public
`-grad_R` accessor. -/
theorem contractedBianchiGradPattern_apply_eq_grad_R_of_trace_covDerivRicciEndomorphism
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (h_ntr : NablaTrComm emb atr conn ha hl) (Y : V)
    (h_trace :
      (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        atr.tr (covDerivRicciEndomorphism emb conn ha hal hsl hl atr met Y)) :
      (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        grad_R emb conn ha hal hsl hl atr met Y := by
  rw [h_trace]
  rw [grad_R_eq_trace_covDerivRicciEndomorphism emb conn ha hal hsl hl atr met h_ntr Y]

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

/-- Constructor for the contracted second Bianchi interface once the traced
second-Bianchi calculation has produced the divergence formula.

The remaining P1 target is exactly to prove `h_div` from
`second_bianchi`/`covDerivRm_sum_endo` plus the `AbstractTrace` contraction
commutation rules. -/
theorem contractedSecondBianchiIdentity_from_divergence_formula
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (half : R)
    (h_half : IsHalfCoefficient half)
    (h_div : forall Y,
      ricciDivergenceAt emb conn ha hal hsl hl atr met Y =
        half * grad_R emb conn ha hal hsl hl atr met Y) :
    ContractedSecondBianchiIdentity emb conn ha hal hsl hl atr met half :=
  ⟨h_half, h_div⟩

/-- Algebraic conversion from the traced second Bianchi form
`2 * div Ric = dR` to the half-gradient form `div Ric = half * dR`.

This is the exact scalar algebra needed after the remaining tensor-calculus
contraction of `second_bianchi` has produced the traced identity. -/
theorem contractedSecondBianchiIdentity_from_traced_second_bianchi
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (half : R)
    (h_half : IsHalfCoefficient half)
    (h_trace : forall Y,
      (2 : R) * ricciDivergenceAt emb conn ha hal hsl hl atr met Y =
        grad_R emb conn ha hal hsl hl atr met Y) :
    ContractedSecondBianchiIdentity emb conn ha hal hsl hl atr met half := by
  refine ⟨h_half, ?_⟩
  intro Y
  calc
    ricciDivergenceAt emb conn ha hal hsl hl atr met Y
        = 1 * ricciDivergenceAt emb conn ha hal hsl hl atr met Y := by ring
    _ = ((2 : R) * half) * ricciDivergenceAt emb conn ha hal hsl hl atr met Y := by
          rw [h_half]
    _ = half * ((2 : R) * ricciDivergenceAt emb conn ha hal hsl hl atr met Y) := by ring
    _ = half * grad_R emb conn ha hal hsl hl atr met Y := by rw [h_trace Y]

/-- Concrete double-trace data for deriving the contracted second Bianchi
identity from the lowered `(0,5)` tensor `∇Rm`.

The three patterns represent the three traced terms in the cyclic second
Bianchi identity. The `divFubini_to_divPattern` field is the Fubini/swap step
which identifies the two Ricci-divergence contractions. The remaining fields
identify the selected double traces with the existing synthetic
`ricciDivergenceAt` and `grad_R` accessors.

The sign convention in `traced_cyclic_sum` is
`divPattern + divFubiniPattern + gradPattern = 0`. With the Ricci convention
`Rc(X,Z) = tr(Y ↦ Rm(X,Y)Z)`, the two divergence patterns are the negative
Ricci-divergence contractions, while the gradient pattern is the positive
scalar-gradient contraction. Thus the cyclic sum gives
`-div Ric - div Ric + dR = 0`. -/
structure ContractedSecondBianchiDoubleTraceData
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) where
  lowered : LoweredCovDerivRmTensorData emb conn met
  divPattern : DoubleMetricTrace05Pattern
  divFubiniPattern : DoubleMetricTrace05Pattern
  gradPattern : DoubleMetricTrace05Pattern
  traced_cyclic_sum : forall Y,
    divPattern.apply met atr lowered.tensor Y +
      divFubiniPattern.apply met atr lowered.tensor Y +
        gradPattern.apply met atr lowered.tensor Y = 0
  divPattern_eq_neg_ricciDivergence : forall Y,
    divPattern.apply met atr lowered.tensor Y =
      - ricciDivergenceAt emb conn ha hal hsl hl atr met Y
  divFubini_to_divPattern :
    divFubiniPattern.Fubini divPattern met atr lowered.tensor
  gradPattern_eq_grad_R : forall Y,
    gradPattern.apply met atr lowered.tensor Y =
      grad_R emb conn ha hal hsl hl atr met Y

/-- Slot-audit interface for the cyclic trace of the lowered second Bianchi
identity.

The tensor-level cyclic identity is already proved from `second_bianchi`.
This class records only the remaining index bookkeeping: after tracing the two
cyclic permutations with the divergence pattern, the left cyclic term is the
reversed divergence pattern and the right cyclic term is the named scalar
gradient pattern. Concrete proofs are expected to use metric-trace permutation
lemmas built from `HasTensorContractSwapNaturality`, double-trace Fubini, and
the curvature antisymmetry that later identifies the named gradient pattern
with `-dR`. -/
class HasContractedSecondBianchiCyclicTraceSlotAudit
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) : Prop where
  cycle_left_apply_eq_divFubiniPattern :
    forall (h_mc : IsMetricCompatible emb conn met) Y,
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (covariantCycle012Left05
            (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor) Y =
        (DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y
  cycle_right_apply_eq_gradPattern :
    forall (h_mc : IsMetricCompatible emb conn met) Y,
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (covariantCycle012Right05
            (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor) Y =
        (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y

/-- Synthetic proof package for the two trace-accessor identifications in the
contracted second Bianchi contraction.

The reusable metric-trace Fubini step is deliberately not a field here; it is
handled by `HasDoubleMetricTrace05PatternFubini`. The cyclic trace is derived
from `second_bianchi` plus `HasContractedSecondBianchiCyclicTraceSlotAudit`.
The divergence and gradient identifications additionally take `NablaTrComm`,
since they identify derivatives of traced curvature quantities with traces of
curvature derivatives. -/
class HasContractedSecondBianchiNamedPatternCalculus
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) : Prop
    extends HasContractedSecondBianchiCyclicTraceSlotAudit emb conn ha hal hsl hl atr met where
  divPattern_apply_eq_neg_ricciDivergence :
    forall (h_mc : IsMetricCompatible emb conn met)
      (_h_ntr : NablaTrComm emb atr conn ha hl) Y,
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        - ricciDivergenceAt emb conn ha hal hsl hl atr met Y
  gradPattern_apply_eq_grad_R :
    forall (h_mc : IsMetricCompatible emb conn met)
      (_h_ntr : NablaTrComm emb atr conn ha hl) Y,
      (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        grad_R emb conn ha hal hsl hl atr met Y

/-- Trace of the tensor-level lowered second Bianchi identity with the
divergence trace pattern.

This is the proved core of the named-pattern cyclic calculation. The remaining
slot-audit obligations are to identify the traced cyclic permutations with the
named `divFubini` and `grad` patterns on the unpermuted tensor. -/
theorem contractedBianchiDivPattern_apply_cyclic_tensor_sum
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn) (Y : V) :
    let T := (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor
    (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr T Y +
        (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (covariantCycle012Left05 T) Y +
          (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
            (covariantCycle012Right05 T) Y = 0 := by
  intro T
  have htensor :
      T + covariantCycle012Left05 T + covariantCycle012Right05 T =
        (0 : TensorData R V 0 5) := by
    simpa [T] using
      covDerivRmLoweredTensor_cyclic_sum_tensor emb conn ha hal hsl hl met h_mc h_tf
  have happly := congr_arg
    (fun S : TensorData R V 0 5 =>
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr S Y) htensor
  change
    (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
        (T + covariantCycle012Left05 T + covariantCycle012Right05 T) Y =
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
        (0 : TensorData R V 0 5) Y at happly
  rw [DoubleMetricTrace05Pattern.apply_add,
    DoubleMetricTrace05Pattern.apply_add,
    DoubleMetricTrace05Pattern.apply_zero] at happly
  exact happly

/-- Slot-audit projection for the first cyclic term in the traced second
Bianchi identity. -/
theorem contractedBianchiDivPattern_apply_cycle_left_eq_divFubiniPattern
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasContractedSecondBianchiCyclicTraceSlotAudit emb conn ha hal hsl hl atr met]
    (h_mc : IsMetricCompatible emb conn met) (Y : V) :
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (covariantCycle012Left05
            (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor) Y =
        (DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y :=
  HasContractedSecondBianchiCyclicTraceSlotAudit.cycle_left_apply_eq_divFubiniPattern
    h_mc Y

/-- Slot-audit projection for the second cyclic term in the traced second
Bianchi identity. This is same-sign slot bookkeeping; the curvature sign is in
the later `gradPattern = -dR` identification. -/
theorem contractedBianchiDivPattern_apply_cycle_right_eq_gradPattern
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasContractedSecondBianchiCyclicTraceSlotAudit emb conn ha hal hsl hl atr met]
    (h_mc : IsMetricCompatible emb conn met) (Y : V) :
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (covariantCycle012Right05
            (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor) Y =
        (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y :=
  HasContractedSecondBianchiCyclicTraceSlotAudit.cycle_right_apply_eq_gradPattern
    h_mc Y

/-- The named-pattern cyclic trace equation follows from the tensor-level
second Bianchi identity plus the two cyclic slot-audit identifications. -/
theorem contractedBianchi_named_patterns_traced_cyclic_sum_from_slot_audit
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasContractedSecondBianchiCyclicTraceSlotAudit emb conn ha hal hsl hl atr met]
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn) (Y : V) :
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y +
        (DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y +
            (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
              (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y = 0 := by
  let T := (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor
  have hcore :=
    contractedBianchiDivPattern_apply_cyclic_tensor_sum
      emb conn ha hal hsl hl atr met h_mc h_tf Y
  have hleft :
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (covariantCycle012Left05 T) Y =
        (DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern).apply met atr T Y := by
    simpa [T] using
      contractedBianchiDivPattern_apply_cycle_left_eq_divFubiniPattern
        emb conn ha hal hsl hl atr met h_mc Y
  have hright :
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (covariantCycle012Right05 T) Y =
        (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr T Y := by
    simpa [T] using
      contractedBianchiDivPattern_apply_cycle_right_eq_gradPattern
        emb conn ha hal hsl hl atr met h_mc Y
  simpa [T, hleft, hright] using hcore

/-- Projection for the named-pattern cyclic trace calculation. -/
theorem contractedBianchi_named_patterns_traced_cyclic_sum
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasContractedSecondBianchiNamedPatternCalculus emb conn ha hal hsl hl atr met]
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn) (Y : V) :
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y +
        (DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y +
            (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
              (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y = 0 :=
  contractedBianchi_named_patterns_traced_cyclic_sum_from_slot_audit
    emb conn ha hal hsl hl atr met h_mc h_tf Y

/-- Projection for the divergence named-pattern calculation.

With the convention `Rc(X,Z) = tr(Y ↦ Rm(X,Y)Z)`, this trace pattern is the
negative Ricci divergence. -/
theorem contractedBianchiDivPattern_apply_eq_neg_ricciDivergence
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasContractedSecondBianchiNamedPatternCalculus emb conn ha hal hsl hl atr met]
    (h_mc : IsMetricCompatible emb conn met)
    (h_ntr : NablaTrComm emb atr conn ha hl) (Y : V) :
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        - ricciDivergenceAt emb conn ha hal hsl hl atr met Y :=
  HasContractedSecondBianchiNamedPatternCalculus.divPattern_apply_eq_neg_ricciDivergence
    h_mc h_ntr Y

/-- Reduction lemma for the divergence named pattern.

The current named divergence pattern naturally matches
`ricciDivergenceAtSecond`, because it leaves the Ricci slot corresponding to
`(∇_A Ric)(Y, Z)`. Once that second-slot identification and Ricci symmetry are
available, the public first-slot divergence target follows. -/
theorem contractedBianchiDivPattern_apply_eq_neg_ricciDivergence_of_second_slot
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (Y : V)
    (h_second :
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        - ricciDivergenceAtSecond emb conn ha hal hsl hl atr met Y)
    (h_ricci_symm : swap_covariant (0 : Fin 2) 1
        (ricciForm_tensor emb conn ha hal hsl hl atr) =
      ricciForm_tensor emb conn ha hal hsl hl atr) :
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        - ricciDivergenceAt emb conn ha hal hsl hl atr met Y := by
  rw [h_second]
  rw [ricciDivergenceAtSecond_eq_ricciDivergenceAt_of_ricciForm_tensor_symm
    emb conn ha hal hsl hl atr met h_ricci_symm Y]

/-- Projection for the scalar-gradient named-pattern calculation.

With the current curvature convention, this named pattern is the positive
scalar gradient. -/
theorem contractedBianchiGradPattern_apply_eq_grad_R
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasContractedSecondBianchiNamedPatternCalculus emb conn ha hal hsl hl atr met]
    (h_mc : IsMetricCompatible emb conn met)
    (h_ntr : NablaTrComm emb atr conn ha hl) (Y : V) :
      (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        grad_R emb conn ha hal hsl hl atr met Y :=
  HasContractedSecondBianchiNamedPatternCalculus.gradPattern_apply_eq_grad_R
    h_mc h_ntr Y

/-- For the named contracted-Bianchi patterns, the Fubini field says exactly
that the two divergence double traces agree after evaluation in the remaining
slot. -/
theorem contractedBianchiDivFubiniPattern_apply_eq_divPattern
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (Y : V)
    (h_fubini :
      (DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern).Fubini
        DoubleMetricTrace05Pattern.contractedBianchiDivPattern met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor) :
    (DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern).apply met atr
        (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
        (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y := by
  exact DoubleMetricTrace05Pattern.apply_eq_of_fubini
    DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern
    DoubleMetricTrace05Pattern.contractedBianchiDivPattern met atr
    (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor h_fubini Y

/-- Build the contracted-Bianchi double-trace data using the sign-correct named
patterns.

For a lowered `(0,5)` tensor
`T(A, X, Y, Z, W) = (∇_A Rm)(X, Y, Z, W)`, these patterns are:

* divergence: trace original slots `(0, 3)` and `(1, 4)`, leaving slot `2`;
* Fubini divergence: the same traces in the reverse order;
* scalar gradient: trace original slots `(1, 3)` and `(2, 4)`, leaving slot `0`.

The remaining hypotheses are the concrete trace calculations still owed by the
realization layer: the double-traced cyclic sum, the two identifications with
`div Ric` and `-dR`, and the Fubini/swap equality for the reversed trace order. -/
noncomputable def contractedSecondBianchiDoubleTraceData_of_named_patterns
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (h_cyclic : forall Y,
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y +
        (DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y +
            (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
              (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y = 0)
    (h_div : forall Y,
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        - ricciDivergenceAt emb conn ha hal hsl hl atr met Y)
    (h_fubini :
      (DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern).Fubini
        DoubleMetricTrace05Pattern.contractedBianchiDivPattern met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor)
    (h_grad : forall Y,
      (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        grad_R emb conn ha hal hsl hl atr met Y) :
    ContractedSecondBianchiDoubleTraceData emb conn ha hal hsl hl atr met where
  lowered := loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc
  divPattern := DoubleMetricTrace05Pattern.contractedBianchiDivPattern
  divFubiniPattern := DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern
  gradPattern := DoubleMetricTrace05Pattern.contractedBianchiGradPattern
  traced_cyclic_sum := h_cyclic
  divPattern_eq_neg_ricciDivergence := h_div
  divFubini_to_divPattern := h_fubini
  gradPattern_eq_grad_R := h_grad

/-- Build the named-pattern data when the divergence-pattern Fubini equality is
available from the reusable metric-trace bridge. This removes the ad hoc
`h_fubini` argument from P1 callers. -/
noncomputable def contractedSecondBianchiDoubleTraceData_of_named_patterns_and_metric_fubini
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasDoubleMetricTrace05PatternFubini
      DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern
      DoubleMetricTrace05Pattern.contractedBianchiDivPattern met atr]
    (h_mc : IsMetricCompatible emb conn met)
    (h_cyclic : forall Y,
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y +
        (DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y +
            (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
              (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y = 0)
    (h_div : forall Y,
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        - ricciDivergenceAt emb conn ha hal hsl hl atr met Y)
    (h_grad : forall Y,
      (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        grad_R emb conn ha hal hsl hl atr met Y) :
    ContractedSecondBianchiDoubleTraceData emb conn ha hal hsl hl atr met :=
  contractedSecondBianchiDoubleTraceData_of_named_patterns emb conn ha hal hsl hl
    atr met h_mc h_cyclic h_div
    (contractedBianchiDivMetricTraceFubini met atr
      (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor)
    h_grad

/-- Build the named-pattern double-trace data from the bundled synthetic
named-pattern calculus and the reusable metric-trace Fubini bridge.

This is the stronger P1 constructor: callers provide the usual geometric
connection hypotheses (`h_mc`, `h_tf`) and trace-commutation (`h_ntr`), while
the cyclic trace is derived from the slot-audit superclass and the divergence
and gradient identifications are supplied by
`HasContractedSecondBianchiNamedPatternCalculus`. -/
noncomputable def contractedSecondBianchiDoubleTraceData_from_second_bianchi_named_patterns
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasDoubleMetricTrace05PatternFubini
      DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern
      DoubleMetricTrace05Pattern.contractedBianchiDivPattern met atr]
    [HasContractedSecondBianchiNamedPatternCalculus emb conn ha hal hsl hl atr met]
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn)
    (h_ntr : NablaTrComm emb atr conn ha hl) :
    ContractedSecondBianchiDoubleTraceData emb conn ha hal hsl hl atr met :=
  contractedSecondBianchiDoubleTraceData_of_named_patterns_and_metric_fubini
    emb conn ha hal hsl hl atr met h_mc
    (contractedBianchi_named_patterns_traced_cyclic_sum
      emb conn ha hal hsl hl atr met h_mc h_tf)
    (contractedBianchiDivPattern_apply_eq_neg_ricciDivergence
      emb conn ha hal hsl hl atr met h_mc h_ntr)
    (contractedBianchiGradPattern_apply_eq_grad_R
      emb conn ha hal hsl hl atr met h_mc h_ntr)

/-- The double-traced lowered second Bianchi calculation produces
`2 * div Ric = dR` once the three concrete trace patterns are identified.

This theorem is the current Fubini-based contraction bridge: it does not prove
which index patterns are correct, but after a realization supplies those
pattern equalities the scalar contracted-Bianchi identity is immediate. -/
theorem traced_second_bianchi_from_double_metric_trace_data
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (data : ContractedSecondBianchiDoubleTraceData emb conn ha hal hsl hl atr met) :
    forall Y,
      (2 : R) * ricciDivergenceAt emb conn ha hal hsl hl atr met Y =
        grad_R emb conn ha hal hsl hl atr met Y := by
  intro Y
  have h_fubini :
      data.divFubiniPattern.apply met atr data.lowered.tensor Y =
        data.divPattern.apply met atr data.lowered.tensor Y :=
    DoubleMetricTrace05Pattern.apply_eq_of_fubini
      data.divFubiniPattern data.divPattern met atr data.lowered.tensor
      data.divFubini_to_divPattern Y
  have hsum := data.traced_cyclic_sum Y
  rw [h_fubini, data.divPattern_eq_neg_ricciDivergence Y,
    data.gradPattern_eq_grad_R Y] at hsum
  apply sub_eq_zero.mp
  calc
    (2 : R) * ricciDivergenceAt emb conn ha hal hsl hl atr met Y -
        grad_R emb conn ha hal hsl hl atr met Y
        = ricciDivergenceAt emb conn ha hal hsl hl atr met Y +
            ricciDivergenceAt emb conn ha hal hsl hl atr met Y -
              grad_R emb conn ha hal hsl hl atr met Y := by ring
    _ = 0 := by
        have hneg : -(ricciDivergenceAt emb conn ha hal hsl hl atr met Y) +
              -(ricciDivergenceAt emb conn ha hal hsl hl atr met Y) +
                grad_R emb conn ha hal hsl hl atr met Y = 0 := by
          simpa [add_assoc] using hsum
        linear_combination -hneg

/-- Contracted second Bianchi from the double-trace/Fubini package. -/
theorem contractedSecondBianchiIdentity_from_double_metric_trace_data
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (half : R)
    (h_half : IsHalfCoefficient half)
    (data : ContractedSecondBianchiDoubleTraceData emb conn ha hal hsl hl atr met) :
    ContractedSecondBianchiIdentity emb conn ha hal hsl hl atr met half :=
  contractedSecondBianchiIdentity_from_traced_second_bianchi emb conn ha hal hsl hl
    atr met half h_half
    (traced_second_bianchi_from_double_metric_trace_data emb conn ha hal hsl hl atr met data)

/-- Contracted second Bianchi from the named sign-correct trace patterns. This
is the preferred P1 entry point until the low-level metric-trace evaluation and
Fubini bridges are proved. -/
theorem contractedSecondBianchiIdentity_from_named_double_trace_patterns
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (half : R)
    (h_half : IsHalfCoefficient half)
    (h_mc : IsMetricCompatible emb conn met)
    (h_cyclic : forall Y,
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y +
        (DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y +
            (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
              (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y = 0)
    (h_div : forall Y,
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        - ricciDivergenceAt emb conn ha hal hsl hl atr met Y)
    (h_fubini :
      (DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern).Fubini
        DoubleMetricTrace05Pattern.contractedBianchiDivPattern met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor)
    (h_grad : forall Y,
      (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        grad_R emb conn ha hal hsl hl atr met Y) :
    ContractedSecondBianchiIdentity emb conn ha hal hsl hl atr met half := by
  exact contractedSecondBianchiIdentity_from_double_metric_trace_data emb conn ha hal hsl hl
    atr met half h_half
    (contractedSecondBianchiDoubleTraceData_of_named_patterns emb conn ha hal hsl hl
      atr met h_mc h_cyclic h_div h_fubini h_grad)

/-- Contracted second Bianchi from the named trace patterns and the reusable
metric-trace Fubini bridge. This is the preferred P1 theorem shape for
realization layers: they instantiate the bridge once for the concrete trace,
then only supply the cyclic-sum and trace-identification calculations. -/
theorem contractedSecondBianchiIdentity_from_named_patterns_and_metric_fubini
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (half : R)
    (h_half : IsHalfCoefficient half)
    [HasDoubleMetricTrace05PatternFubini
      DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern
      DoubleMetricTrace05Pattern.contractedBianchiDivPattern met atr]
    (h_mc : IsMetricCompatible emb conn met)
    (h_cyclic : forall Y,
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y +
        (DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y +
            (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
              (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y = 0)
    (h_div : forall Y,
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        - ricciDivergenceAt emb conn ha hal hsl hl atr met Y)
    (h_grad : forall Y,
      (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
        grad_R emb conn ha hal hsl hl atr met Y) :
    ContractedSecondBianchiIdentity emb conn ha hal hsl hl atr met half := by
  exact contractedSecondBianchiIdentity_from_double_metric_trace_data emb conn ha hal hsl hl
    atr met half h_half
    (contractedSecondBianchiDoubleTraceData_of_named_patterns_and_metric_fubini
      emb conn ha hal hsl hl atr met h_mc h_cyclic h_div h_grad)

/-- Contracted second Bianchi from the named trace-pattern calculus.

Compared with `contractedSecondBianchiIdentity_from_named_patterns_and_metric_fubini`,
this theorem no longer asks callers to pass `h_cyclic`, `h_div`, and `h_grad`
explicitly. The cyclic trace is proved from the slot-audit superclass and
second Bianchi; the divergence and gradient equations come from the
named-pattern calculus class. The Fubini/swap step remains the separate
reusable `HasDoubleMetricTrace05PatternFubini` instance. -/
theorem contractedSecondBianchiIdentity_from_second_bianchi_named_patterns
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (half : R)
    (h_half : IsHalfCoefficient half)
    [HasDoubleMetricTrace05PatternFubini
      DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern
      DoubleMetricTrace05Pattern.contractedBianchiDivPattern met atr]
    [HasContractedSecondBianchiNamedPatternCalculus emb conn ha hal hsl hl atr met]
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn)
    (h_ntr : NablaTrComm emb atr conn ha hl) :
    ContractedSecondBianchiIdentity emb conn ha hal hsl hl atr met half := by
  exact contractedSecondBianchiIdentity_from_double_metric_trace_data
    emb conn ha hal hsl hl atr met half h_half
    (contractedSecondBianchiDoubleTraceData_from_second_bianchi_named_patterns
      emb conn ha hal hsl hl atr met h_mc h_tf h_ntr)

section SlotAuditObligations

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Bundled algebraic obligations to discharge
`HasContractedSecondBianchiCyclicTraceSlotAudit`. Two scalar equations, one
per cyclic permutation. -/
structure ContractedBianchiSlotAuditObligations
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) : Prop where
  /-- The left-cycled tensor's `divPattern` trace identifies with
  `divFubiniPattern` on the original tensor. Mathematical content: first
  Bianchi + second-pair antisymmetry + trace commutation + double-trace
  Fubini. -/
  cycle_left_apply_eq_divFubiniPattern :
    forall (h_mc : IsMetricCompatible emb conn met) Y,
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (covariantCycle012Left05
            (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor) Y =
        (DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y
  /-- The right-cycled tensor's `divPattern` trace identifies with the
  same-sign `gradPattern` on the original tensor. The scalar-gradient sign is
  handled by the raw trace identity. -/
  cycle_right_apply_eq_gradPattern :
    forall (h_mc : IsMetricCompatible emb conn met) Y,
      (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
          (covariantCycle012Right05
            (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor) Y =
        (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
          (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y

/-- Stronger trace-form variant of the named-pattern calculus wrapper.

This is the final-facing P1 producer in this file. It keeps the input shape
that the concrete local-frame calculation naturally provides:

* the two cyclic slot-audit identities, bundled as
  `ContractedBianchiSlotAuditObligations`;
* `divPattern` as the negative trace of the swapped Ricci-divergence
  endomorphism;
* `gradPattern` as the trace of the Ricci endomorphism derivative.

Ricci symmetry is derived here from metric-adjoint trace invariance, so callers
no longer need the intermediate second-slot/Ricci-symmetry feeder theorems. -/
theorem hasContractedSecondBianchiNamedPatternCalculus_of_trace_divergence_trace_adjoint_and_grad_trace
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasMetricAdjointTraceInvariant atr met]
    (obligations :
      ContractedBianchiSlotAuditObligations emb conn ha hal hsl hl atr met)
    (h_tf : IsTorsionFree emb conn)
    (h2 : forall a : R, (2 : R) * a = 0 -> a = 0)
    (h_div_trace :
      forall (h_mc : IsMetricCompatible emb conn met)
        (_h_ntr : NablaTrComm emb atr conn ha hl) Y,
        (DoubleMetricTrace05Pattern.contractedBianchiDivPattern).apply met atr
            (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
          - atr.tr
            (covDivergence02Endomorphism emb met conn ha hal hsl hl
              (swap_covariant (0 : Fin 2) 1
                (ricciForm_tensor emb conn ha hal hsl hl atr)) Y))
    (h_grad_trace :
      forall (h_mc : IsMetricCompatible emb conn met)
        (_h_ntr : NablaTrComm emb atr conn ha hl) Y,
        (DoubleMetricTrace05Pattern.contractedBianchiGradPattern).apply met atr
            (loweredCovDerivRmTensorData emb conn ha hal hsl hl met h_mc).tensor Y =
          atr.tr (covDerivRicciEndomorphism emb conn ha hal hsl hl atr met Y)) :
    HasContractedSecondBianchiNamedPatternCalculus emb conn ha hal hsl hl atr met :=
  { cycle_left_apply_eq_divFubiniPattern :=
      obligations.cycle_left_apply_eq_divFubiniPattern
    cycle_right_apply_eq_gradPattern :=
      obligations.cycle_right_apply_eq_gradPattern
    divPattern_apply_eq_neg_ricciDivergence := by
      intro h_mc h_ntr Y
      exact contractedBianchiDivPattern_apply_eq_neg_ricciDivergence_of_second_slot
        emb conn ha hal hsl hl atr met h_mc Y
        (contractedBianchiDivPattern_apply_eq_neg_ricciDivergenceAtSecond_of_neg_trace_swap_ricci_divergence
          emb conn ha hal hsl hl atr met h_mc Y (h_div_trace h_mc h_ntr Y))
        (ricciForm_tensor_symm_of_Rc_symm emb conn ha hal hsl hl atr
          (Rc_symm_of_metric_adjoint_trace_invariant
            emb conn ha hal hsl hl atr met h_mc h_tf h2))
    gradPattern_apply_eq_grad_R := by
      intro h_mc h_ntr Y
      exact contractedBianchiGradPattern_apply_eq_grad_R_of_trace_covDerivRicciEndomorphism
        emb conn ha hal hsl hl atr met h_mc h_ntr Y (h_grad_trace h_mc h_ntr Y) }

end SlotAuditObligations

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

/-- Divergence of the trace-free Ricci tensor:
`div(Ric - nInv * R * g) = div Ric - nInv * dR`, assuming `nInv` is spatially
constant and the connection is metric compatible. -/
theorem tracefreeRicciDivergenceAt_eq_ricciDivergence_sub
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv : R)
    (h_mc : IsMetricCompatible emb conn met)
    (h_nInv_const : IsSpatialConstant emb nInv)
    (Y : V) :
    covariantDivergence02At emb met atr conn ha hal hsl hl
        (tracefree_ricci_tensor emb conn ha hal hsl hl atr met nInv) Y =
      ricciDivergenceAt emb conn ha hal hsl hl atr met Y -
        nInv * grad_R emb conn ha hal hsl hl atr met Y := by
  unfold tracefree_ricci_tensor ricciDivergenceAt
  rw [covariantDivergence02At_sub emb met atr conn ha hal hsl hl]
  rw [covariantDivergence02At_smul_metric emb met atr conn ha hal hsl hl h_mc]
  rw [action_smul_right emb Y nInv
    (ScalarCurvature emb conn ha hal hsl hl atr met), h_nInv_const Y, zero_mul, zero_add]
  rfl

/-- If the trace-free Ricci tensor vanishes as a tensor, then its divergence
vanishes in the narrow `(0,2)` divergence API. -/
theorem tracefreeRicciDivergenceAt_zero_of_tracefree_ricci_tensor_eq_zero
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv : R)
    (h_zero : tracefree_ricci_tensor emb conn ha hal hsl hl atr met nInv = 0)
    (Y : V) :
    covariantDivergence02At emb met atr conn ha hal hsl hl
        (tracefree_ricci_tensor emb conn ha hal hsl hl atr met nInv) Y = 0 := by
  rw [h_zero]
  exact covariantDivergence02At_zero emb met atr conn ha hal hsl hl Y

/-- Differential half of Lemma 11.6 through trace-free Ricci divergence:
contracted Bianchi and `Ric^0 = 0` force scalar curvature to be spatially
constant. This is equivalent to the Einstein-divergence route below, but keeps
the trace-free tensor as the central object. -/
theorem scalar_spatial_constant_of_contracted_bianchi_and_tracefree_ricci_zero_via_divergence
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
  intro Y
  change grad_R emb conn ha hal hsl hl atr met Y = 0
  apply h_coeff_cancel
  have h_cb := contractedSecondBianchi_apply emb conn ha hal hsl hl atr met half h_bianchi Y
  have h_tf_div :=
    tracefreeRicciDivergenceAt_eq_ricciDivergence_sub emb conn ha hal hsl hl
      atr met nInv h_mc h_nInv_const Y
  have h_tf_zero :=
    tracefreeRicciDivergenceAt_zero_of_tracefree_ricci_tensor_eq_zero emb conn
      ha hal hsl hl atr met nInv h_zero Y
  calc
    (half - nInv) * grad_R emb conn ha hal hsl hl atr met Y
        = half * grad_R emb conn ha hal hsl hl atr met Y -
            nInv * grad_R emb conn ha hal hsl hl atr met Y := by ring
    _ = ricciDivergenceAt emb conn ha hal hsl hl atr met Y -
            nInv * grad_R emb conn ha hal hsl hl atr met Y := by
          rw [← h_cb]
    _ = covariantDivergence02At emb met atr conn ha hal hsl hl
          (tracefree_ricci_tensor emb conn ha hal hsl hl atr met nInv) Y := by
          rw [← h_tf_div]
    _ = 0 := h_tf_zero

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
