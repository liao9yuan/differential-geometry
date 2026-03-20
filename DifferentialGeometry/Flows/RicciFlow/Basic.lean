import DifferentialGeometry.Operators.Variation
import DifferentialGeometry.Geometry.RicciTensor
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Algebra.Metric

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Ricci Flow
Defines the Ricci flow equation and Levi-Civita connections.
-/

open DifferentialGeometry.Bridge TensorAlgebra

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V] [TraceOperator R V]
variable [DerivationRules R V] [LieDerivationRules R V] [TraceLinearityRules R V]

-- 1. Levi-Civita Property
class LeviCivita (conn : AbstractAffineConnection R V) (g : AbstractMetricTensor R V) : Prop where
  compat : MetricCompatible conn g
  torsion_free : TorsionFree conn

-- 2. Ricci Flow Equation
class RicciFlow (Time : Type) [TimeDerivative Time R] [TimeDerivativeRules Time R V]
  (g_fam : Time → AbstractMetricTensor R V) (conn_fam : Time → AbstractAffineConnection R V)  where
  is_levi_civita : ∀ t, LeviCivita (conn_fam t) (g_fam t)
  evolution : ∀ t, metric_var_form g_fam t = (- (2:R)) • ricciForm (conn_fam t)
