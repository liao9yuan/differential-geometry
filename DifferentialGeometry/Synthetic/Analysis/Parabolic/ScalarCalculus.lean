import Mathlib.Algebra.Ring.Basic
import DifferentialGeometry.Synthetic.Analysis.Parabolic.ScalarMaximumPrinciple
import DifferentialGeometry.Synthetic.Operator.Divergence
import DifferentialGeometry.Synthetic.Operator.Laplacian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open SyntheticTensor

/-!
# Scalar Parabolic Calculus Interface

This file records reusable calculus rules for scalar heat operators. The Ricci
flow pinching argument should consume these rules rather than threading
product-rule and power-rule hypotheses through each proof.
-/

section ScalarParabolicCalculus

variable {R Time : Type*}
variable [CommRing R] [Preorder R]

/-- A reusable calculus package for a scalar parabolic heat operator.

`pow c u` is an abstract scalar power operation. A concrete realization may use
`rpow`, integer powers, or another locally positive power API. The fields
`Smooth` and `Positive` are intentionally part of the package: unlike a purely
algebraic helper, the product and power rules below are only available for
functions with enough analytic regularity, and negative powers require a
positivity domain.

The gradient data are also abstract. In a Riemannian realization,
`gradInner f g` is `<nabla f, nabla g>` and `gradNormSq f` is `|nabla f|^2`. -/
structure ScalarParabolicCalculus (P : ScalarParabolicProblem R Time) where
  Smooth : (Time -> R) -> Prop
  Positive : (Time -> R) -> Prop
  pow : R -> (Time -> R) -> Time -> R
  gradInner : (Time -> R) -> (Time -> R) -> Time -> R
  gradNormSq : (Time -> R) -> Time -> R
  smooth_mul :
    forall {f g : Time -> R}, Smooth f -> Smooth g -> Smooth (fun t => f t * g t)
  smooth_power :
    forall (c : R) {u : Time -> R}, Smooth u -> Positive u -> Smooth (pow c u)
  heat_product_rule :
    forall {f g : Time -> R}, Smooth f -> Smooth g -> forall t,
      P.heat (fun s => f s * g s) t =
        f t * P.heat g t + g t * P.heat f t - 2 * gradInner f g t
  heat_power_rule :
    forall (c : R) {u : Time -> R}, Smooth u -> Positive u -> forall t,
      P.heat (pow c u) t =
        c * pow (c - 1) u t * P.heat u t -
          c * (c - 1) * pow (c - 2) u t * gradNormSq u t
  grad_inner_power_rule :
    forall {u v : Time -> R} (c d : R),
      Smooth u -> Positive u -> Smooth v -> Positive v -> forall t,
        gradInner (pow c u) (pow d v) t =
          c * d * pow (c - 1) u t * pow (d - 1) v t * gradInner u v t
  grad_inner_power_right_rule :
    forall {f u : Time -> R} (c : R),
      Smooth f -> Smooth u -> Positive u -> forall t,
        gradInner f (pow c u) t =
          c * pow (c - 1) u t * gradInner f u t

end ScalarParabolicCalculus

section DoubleDivergenceHeatOperator

variable {k R V A Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Spatial scalar Laplacian written as `div (grad u)` on each time slice.

This is the "double divergence" form used by scalar parabolic calculus. In the
current synthetic operator API it is definitionally equal to the existing
`laplacian`, which is the metric trace of the Hessian. -/
noncomputable def scalarDoubleDivergenceAt
    (emb : DerivationEmbedding k R V)
    (atr : AbstractTrace R V)
    (met_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (conn_add_right_fam :
      forall t, forall X Y Z : V, conn_fam t X (Y + Z) = conn_fam t X Y + conn_fam t X Z)
    (conn_leibniz_fam :
      forall t, forall X (f : R) (Y : V),
        conn_fam t X (f • Y) = (emb.embed X) f • Y + f • conn_fam t X Y)
    (conn_add_left_fam :
      forall t, forall X Y Z : V, conn_fam t (X + Y) Z = conn_fam t X Z + conn_fam t Y Z)
    (conn_smul_left_fam :
      forall t, forall (f : R) (X Z : V), conn_fam t (f • X) Z = f • conn_fam t X Z)
    (u : Time -> R) (t : Time) : R :=
  divergence emb (met_fam t) atr (conn_fam t)
    (conn_add_right_fam t) (conn_leibniz_fam t)
    (conn_add_left_fam t) (conn_smul_left_fam t)
    (grad emb (met_fam t) (u t))

/-- The double-divergence definition agrees with the existing synthetic
Laplacian on each time slice. -/
theorem scalarDoubleDivergenceAt_eq_laplacian
    (emb : DerivationEmbedding k R V)
    (atr : AbstractTrace R V)
    (met_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (conn_add_right_fam :
      forall t, forall X Y Z : V, conn_fam t X (Y + Z) = conn_fam t X Y + conn_fam t X Z)
    (conn_leibniz_fam :
      forall t, forall X (f : R) (Y : V),
        conn_fam t X (f • Y) = (emb.embed X) f • Y + f • conn_fam t X Y)
    (conn_add_left_fam :
      forall t, forall X Y Z : V, conn_fam t (X + Y) Z = conn_fam t X Z + conn_fam t Y Z)
    (conn_smul_left_fam :
      forall t, forall (f : R) (X Z : V), conn_fam t (f • X) Z = f • conn_fam t X Z)
    (u : Time -> R) (t : Time) :
    scalarDoubleDivergenceAt emb atr met_fam conn_fam
        conn_add_right_fam conn_leibniz_fam conn_add_left_fam conn_smul_left_fam u t =
      laplacian emb (met_fam t) atr (conn_fam t)
        (conn_add_right_fam t) (conn_leibniz_fam t)
        (conn_add_left_fam t) (conn_smul_left_fam t) (u t) := by
  rfl

/-- Scalar heat operator `partial_t - div grad`, with the spatial part written
in double-divergence form. -/
noncomputable def scalarHeatOperatorFromDoubleDivergence
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (atr : AbstractTrace R V)
    (met_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (conn_add_right_fam :
      forall t, forall X Y Z : V, conn_fam t X (Y + Z) = conn_fam t X Y + conn_fam t X Z)
    (conn_leibniz_fam :
      forall t, forall X (f : R) (Y : V),
        conn_fam t X (f • Y) = (emb.embed X) f • Y + f • conn_fam t X Y)
    (conn_add_left_fam :
      forall t, forall X Y Z : V, conn_fam t (X + Y) Z = conn_fam t X Z + conn_fam t Y Z)
    (conn_smul_left_fam :
      forall t, forall (f : R) (X Z : V), conn_fam t (f • X) Z = f • conn_fam t X Z)
    (u : Time -> R) (t : Time) : R :=
  td.dt_apply u t -
    scalarDoubleDivergenceAt emb atr met_fam conn_fam
      conn_add_right_fam conn_leibniz_fam conn_add_left_fam conn_smul_left_fam u t

variable [Preorder R]

/-- Scalar parabolic problem whose heat operator is definitionally
`partial_t - div grad`. -/
noncomputable def scalarParabolicProblemFromDoubleDivergence
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (atr : AbstractTrace R V)
    (met_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (conn_add_right_fam :
      forall t, forall X Y Z : V, conn_fam t X (Y + Z) = conn_fam t X Y + conn_fam t X Z)
    (conn_leibniz_fam :
      forall t, forall X (f : R) (Y : V),
        conn_fam t X (f • Y) = (emb.embed X) f • Y + f • conn_fam t X Y)
    (conn_add_left_fam :
      forall t, forall X Y Z : V, conn_fam t (X + Y) Z = conn_fam t X Z + conn_fam t Y Z)
    (conn_smul_left_fam :
      forall t, forall (f : R) (X Z : V), conn_fam t (f • X) Z = f • conn_fam t X Z)
    (domain initial : Time -> Prop) : ScalarParabolicProblem R Time where
  domain := domain
  initial := initial
  heat :=
    scalarHeatOperatorFromDoubleDivergence emb td atr met_fam conn_fam
      conn_add_right_fam conn_leibniz_fam conn_add_left_fam conn_smul_left_fam

end DoubleDivergenceHeatOperator

section ScalarParabolicDoubleDivergenceCalculus

variable {R Time : Type*}
variable [CommRing R] [Preorder R]

/-- Reusable calculus rules for a heat operator defined as
`partial_t - doubleDivergence`.

The product and power rules are split at the correct level: time-derivative
rules and spatial double-divergence rules are reusable, and the heat rules are
verified from them. A concrete Riemannian realization should instantiate
`doubleDivergence` by `scalarDoubleDivergenceAt`. -/
structure ScalarParabolicDoubleDivergenceCalculus
    (P : ScalarParabolicProblem R Time) where
  Smooth : (Time -> R) -> Prop
  Positive : (Time -> R) -> Prop
  pow : R -> (Time -> R) -> Time -> R
  gradInner : (Time -> R) -> (Time -> R) -> Time -> R
  gradNormSq : (Time -> R) -> Time -> R
  dt : (Time -> R) -> Time -> R
  doubleDivergence : (Time -> R) -> Time -> R
  heat_eq : forall u t, P.heat u t = dt u t - doubleDivergence u t
  smooth_mul :
    forall {f g : Time -> R}, Smooth f -> Smooth g -> Smooth (fun t => f t * g t)
  smooth_power :
    forall (c : R) {u : Time -> R}, Smooth u -> Positive u -> Smooth (pow c u)
  dt_product_rule :
    forall {f g : Time -> R}, Smooth f -> Smooth g -> forall t,
      dt (fun s => f s * g s) t = f t * dt g t + g t * dt f t
  doubleDivergence_product_rule :
    forall {f g : Time -> R}, Smooth f -> Smooth g -> forall t,
      doubleDivergence (fun s => f s * g s) t =
        f t * doubleDivergence g t + g t * doubleDivergence f t +
          2 * gradInner f g t
  dt_power_rule :
    forall (c : R) {u : Time -> R}, Smooth u -> Positive u -> forall t,
      dt (pow c u) t = c * pow (c - 1) u t * dt u t
  doubleDivergence_power_rule :
    forall (c : R) {u : Time -> R}, Smooth u -> Positive u -> forall t,
      doubleDivergence (pow c u) t =
        c * pow (c - 1) u t * doubleDivergence u t +
          c * (c - 1) * pow (c - 2) u t * gradNormSq u t
  grad_inner_power_rule :
    forall {u v : Time -> R} (c d : R),
      Smooth u -> Positive u -> Smooth v -> Positive v -> forall t,
        gradInner (pow c u) (pow d v) t =
          c * d * pow (c - 1) u t * pow (d - 1) v t * gradInner u v t
  grad_inner_power_right_rule :
    forall {f u : Time -> R} (c : R),
      Smooth f -> Smooth u -> Positive u -> forall t,
        gradInner f (pow c u) t =
          c * pow (c - 1) u t * gradInner f u t

/-- The heat product rule follows from `heat = partial_t - doubleDivergence`
and the reusable product rules for each piece. -/
theorem heat_product_rule_of_doubleDivergence
    {P : ScalarParabolicProblem R Time}
    (C : ScalarParabolicDoubleDivergenceCalculus P)
    {f g : Time -> R} (hf : C.Smooth f) (hg : C.Smooth g) (t : Time) :
    P.heat (fun s => f s * g s) t =
      f t * P.heat g t + g t * P.heat f t - 2 * C.gradInner f g t := by
  rw [C.heat_eq (fun s => f s * g s) t, C.dt_product_rule hf hg t,
    C.doubleDivergence_product_rule hf hg t, C.heat_eq g t, C.heat_eq f t]
  ring

/-- The heat power rule follows from `heat = partial_t - doubleDivergence`
and the reusable chain rules for each piece. -/
theorem heat_power_rule_of_doubleDivergence
    {P : ScalarParabolicProblem R Time}
    (C : ScalarParabolicDoubleDivergenceCalculus P)
    (c : R) {u : Time -> R} (hu : C.Smooth u) (hpos : C.Positive u) (t : Time) :
    P.heat (C.pow c u) t =
      c * C.pow (c - 1) u t * P.heat u t -
        c * (c - 1) * C.pow (c - 2) u t * C.gradNormSq u t := by
  rw [C.heat_eq (C.pow c u) t, C.dt_power_rule c hu hpos t,
    C.doubleDivergence_power_rule c hu hpos t, C.heat_eq u t]
  ring

/-- A double-divergence calculus package induces the higher-level scalar
parabolic calculus package used by Hamilton's quotient identity. -/
def ScalarParabolicDoubleDivergenceCalculus.toScalarParabolicCalculus
    {P : ScalarParabolicProblem R Time}
    (C : ScalarParabolicDoubleDivergenceCalculus P) :
    ScalarParabolicCalculus P where
  Smooth := C.Smooth
  Positive := C.Positive
  pow := C.pow
  gradInner := C.gradInner
  gradNormSq := C.gradNormSq
  smooth_mul := C.smooth_mul
  smooth_power := C.smooth_power
  heat_product_rule := heat_product_rule_of_doubleDivergence C
  heat_power_rule := heat_power_rule_of_doubleDivergence C
  grad_inner_power_rule := C.grad_inner_power_rule
  grad_inner_power_right_rule := C.grad_inner_power_right_rule

end ScalarParabolicDoubleDivergenceCalculus
