import DifferentialGeometry.Integral.Connection.ChartLieBracket
import DifferentialGeometry.Integral.Connection.CotangentExtensionCore
import DifferentialGeometry.Synthetic.Analysis.NablaOnTensors
import DifferentialGeometry.Synthetic.Geometry.Connection
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Core Ricci Identities

This file isolates the borrowable algebra of the connection Ricci identities.
The manifold-facing cotangent connection is exposed by
`CotangentExtensionCore`; the theorems below record the common bracket-form
calculation before any RicciFlower tensor-realization bridge is applied.
-/

noncomputable section

namespace DifferentialGeometry
namespace Integral
namespace Connection

open SyntheticTensor

section Algebra

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Vector Ricci identity in bracket-form notation. -/
theorem ricci_identity_vector
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (X Y Z : V) :
    conn X (conn Y Z) - conn Y (conn X Z) - conn (bracket emb X Y) Z =
      Rm emb conn X Y Z :=
  rfl

/-- One-form Ricci identity in bracket form:
`(∇*_X∇*_Y α - ∇*_Y∇*_X α - ∇*_[X,Y] α)(Z) = -α(R(X,Y)Z)`.

This is the algebraic core of the borrowed upstream calculation.  It is
connection-generic: torsion-freeness is needed only when converting this
bracket-form identity to a tensor commutator in the first two covariant slots.
-/
theorem ricci_identity_oneForm
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y Z : V) (alpha : V →ₗ[R] R) :
    (nabla_dual emb conn ha hl X (nabla_dual emb conn ha hl Y alpha)) Z -
        (nabla_dual emb conn ha hl Y (nabla_dual emb conn ha hl X alpha)) Z -
          (nabla_dual emb conn ha hl (bracket emb X Y) alpha) Z =
      -alpha (Rm emb conn X Y Z) := by
  simp only [nabla_dual, Rm, LinearMap.coe_mk, AddHom.coe_mk, map_sub]
  have hab : (emb.embed (bracket emb X Y)) (alpha Z) =
      (emb.embed X) ((emb.embed Y) (alpha Z)) -
        (emb.embed Y) ((emb.embed X) (alpha Z)) := by
    simpa [action] using action_bracket emb X Y (alpha Z)
  rw [hab]
  abel

end Algebra

end Connection
end Integral
end DifferentialGeometry
