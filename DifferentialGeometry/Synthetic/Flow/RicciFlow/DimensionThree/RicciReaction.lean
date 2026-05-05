import DifferentialGeometry.Synthetic.Flow.RicciFlow.DimensionThree.Pinching
import DifferentialGeometry.Synthetic.Flow.RicciFlow.DimensionThree.RiemannFromRicci3D
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.RicciNorm

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open BigOperators

/-!
# Three-Dimensional Riemann-Ricci-Ricci Contraction (P3.3-geom architecture)

This file is the dim-3 architecture layer for the scalar contraction of the
Riemann tensor against two Ricci tensors, parallel to the P1
contracted-second-Bianchi pipeline and the P2 Riemann-from-Ricci pipeline.

The geometric scalar is the pointwise Riemann-Ricci-Ricci contraction

```
sum_{i,j} Rm_lowered(e_i, e_j, e_i, e_j) * lambda_i * lambda_j
```

in an orthonormal Ricci eigenframe. Equivalently, it is the coordinate
contraction usually written schematically as `R_{ikjl} Ric^{kl} Ric^{ij}`
up to the slot convention fixed by `Rm_lowered`. Some existing APIs in this
file still use the short parameter name `reaction`; in documentation, that
parameter means this Riemann-Ricci-Ricci contraction scalar.

The geometric content of P3.3-geom: in dimension three, contracting the
Riemann-from-Ricci formula against two Ricci tensors yields the Hamilton
cubic contraction relation

```
2 R * (Riemann-Ricci-Ricci contraction scalar) = 2 |Ric|^4 - Q
```

where `Q = hamiltonCubicQ` is the synthetic cubic Hamilton quantity. The
contraction scalar itself is parameterized: the realization layer supplies a
concrete value plus a predicate witnessing that the value equals the geometric
Riemann-Ricci-Ricci contraction.

Three layers:

* `RicciReactionContractionDataPackage`: the structured input the realization
  produces. Bundles a chosen Riemann-Ricci-Ricci contraction scalar, the realization-side
  geometricity predicate, and the residual-zero identity.
* `HasRicciReactionContractionCalculus`: typeclass bundling the same residual
  zero identity. The realization picks `IsGeometricReactionScalar`.
* `ricciReactionContractionIdentity_from_dim3_calculus`: stable entry theorem
  producing the contraction equation from the typeclass plus connection
  hypotheses.

The intended proof route is:

1. use P2 to express all sectional curvatures in an orthonormal Ricci
   eigenframe;
2. identify the Riemann-Ricci-Ricci contraction scalar with
   `ricciEigenRiemannReaction3`;
3. use the already-proved eigenvalue algebra
   `ricciEigenRiemannReaction3_cubicQ_relation`;
4. package the result as `HasRicciReactionContractionCalculus`, then feed it
   into the trace-free Ricci norm evolution in `Evolution/RicciNorm.lean`.

The coordinate realization should only prove step 2: frame expansion of the
Riemann-Ricci-Ricci contraction in a Ricci eigenframe. The scalar algebra below
handles step 3 without coordinates.

The typeclass field `IsGeometricReactionScalar : R → Prop` mirrors the
Hamilton-level pattern from `HamiltonP3CubicReactionGeometryTheorem`: the
realization picks the predicate, and instances of the typeclass commit to
producing the residual-zero proof for any value satisfying that predicate.
-/

namespace SyntheticTensor

section RicciReactionContractionArchitecture

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Residual form of the dim-3 Riemann-Ricci-Ricci contraction identity.

The parameter named `reaction` is the existing API name for the scalar
`R_{ikjl} Ric^{kl} Ric^{ij}` in the current slot convention. The residual is
`2 R * reaction - (2 |Ric|^4 - Q)`, and the realization shows it is zero. -/
noncomputable def ricciReactionContractionResidual
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (reaction : R) : R :=
  2 * ScalarCurvature emb conn ha hal hsl hl atr met * reaction -
    (2 * ricci_norm_sq emb conn ha hal hsl hl atr met ^ 2 -
      hamiltonCubicQ emb conn ha hal hsl hl atr met)

/-- Data package for the dim-3 Riemann-Ricci-Ricci contraction identity.

A realization layer that derives the contraction identity should produce one of
these. The scalar field is named `reaction` for compatibility with the existing
P3 API, but it denotes the Riemann-Ricci-Ricci contraction scalar. It is bundled
with a realization-chosen geometricity predicate and the residual-zero proof.
The realization may use the connection hypotheses (metric compatibility,
torsion-freeness) and the dim-3 Riemann-from-Ricci formula in its proof. -/
structure RicciReactionContractionDataPackage
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) where
  /-- The Riemann-Ricci-Ricci contraction scalar produced by the realization.
  Classically this is the contraction `R_{ikjl} Ric^{kl} Ric^{ij}` of the
  Riemann tensor against two copies of the Ricci tensor. -/
  reaction : R
  /-- Realization-side predicate witnessing that `reaction` is the geometric
  Riemann-Ricci-Ricci contraction. Opaque at the synthetic layer; concrete at
  the realization layer. -/
  IsGeometricReactionScalar : Prop
  /-- The dim-3 contraction identity in residual form. -/
  residual_zero :
    IsDimensionThree atr ->
      IsMetricCompatible emb conn met ->
        IsTorsionFree emb conn ->
          IsGeometricReactionScalar ->
            ricciReactionContractionResidual emb conn ha hal hsl hl atr met reaction = 0

/-- Synthetic calculation target for the dim-3 Riemann-Ricci-Ricci contraction.

The realization-supplied predicate `IsGeometricReactionScalar` characterizes
which scalars are valid Riemann-Ricci-Ricci contraction values. The realization
proves the residual vanishes for any such value, given dim-3, metric
compatibility, and torsion-freeness. -/
class HasRicciReactionContractionCalculus
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) where
  /-- Realization-supplied predicate for valid synthetic Riemann-Ricci-Ricci
  contraction scalars. -/
  IsGeometricReactionScalar : R -> Prop
  /-- For any scalar witnessing the realization's Riemann-Ricci-Ricci
  geometricity predicate, the residual vanishes in dim 3 under metric
  compatibility and torsion-freeness. -/
  residual_zero :
    forall (reaction : R),
      IsGeometricReactionScalar reaction ->
        IsDimensionThree atr ->
          IsMetricCompatible emb conn met ->
            IsTorsionFree emb conn ->
              ricciReactionContractionResidual emb conn ha hal hsl hl atr met reaction = 0

/-- Constructor for the calculus class from a raw residual-zero hypothesis. -/
@[reducible]
noncomputable def hasRicciReactionContractionCalculus_of_residual_zero
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (IsGeom : R -> Prop)
    (h_residual :
      forall (reaction : R),
        IsGeom reaction ->
          IsDimensionThree atr ->
            IsMetricCompatible emb conn met ->
              IsTorsionFree emb conn ->
                ricciReactionContractionResidual emb conn ha hal hsl hl atr met reaction = 0) :
    HasRicciReactionContractionCalculus emb conn ha hal hsl hl atr met where
  IsGeometricReactionScalar := IsGeom
  residual_zero := h_residual

/-- Projection for the residual-zero field of the calculus class. -/
theorem ricciReactionContractionResidual_eq_zero
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasRicciReactionContractionCalculus emb conn ha hal hsl hl atr met]
    (reaction : R)
    (h_geom :
      HasRicciReactionContractionCalculus.IsGeometricReactionScalar
        (emb := emb) (conn := conn) (ha := ha) (hal := hal) (hsl := hsl) (hl := hl)
        (atr := atr) (met := met) reaction)
    (h_dim : IsDimensionThree atr)
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn) :
    ricciReactionContractionResidual emb conn ha hal hsl hl atr met reaction = 0 :=
  HasRicciReactionContractionCalculus.residual_zero reaction h_geom h_dim h_mc h_tf

/-- Stable P3.3-geom entry theorem.

The synthetic calculus typeclass plus `IsDimensionThree`, metric compatibility,
torsion-freeness, and a scalar satisfying the realization's
Riemann-Ricci-Ricci geometricity predicate produces Hamilton's cubic contraction
relation `2 R * reaction = 2 |Ric|^4 - Q`. The parameter name `reaction` is
legacy API terminology for this contraction scalar. -/
theorem ricciReactionContractionIdentity_from_dim3_calculus
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasRicciReactionContractionCalculus emb conn ha hal hsl hl atr met]
    (reaction : R)
    (h_geom :
      HasRicciReactionContractionCalculus.IsGeometricReactionScalar
        (emb := emb) (conn := conn) (ha := ha) (hal := hal) (hsl := hsl) (hl := hl)
        (atr := atr) (met := met) reaction)
    (h_dim : IsDimensionThree atr)
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn) :
    2 * ScalarCurvature emb conn ha hal hsl hl atr met * reaction =
      2 * ricci_norm_sq emb conn ha hal hsl hl atr met ^ 2 -
        hamiltonCubicQ emb conn ha hal hsl hl atr met := by
  have h_zero :=
    ricciReactionContractionResidual_eq_zero emb conn ha hal hsl hl atr met
      reaction h_geom h_dim h_mc h_tf
  unfold ricciReactionContractionResidual at h_zero
  linear_combination h_zero

/-! ## Eigenvalue package for the P3 algebraic contraction

This is the narrow algebraic abstraction that the P2 realization should target.
Once a concrete coordinate/eigenframe calculation identifies the geometric
Riemann-Ricci-Ricci contraction scalar with `ricciEigenRiemannReaction3`, the
remaining P3 cubic identity is pure scalar algebra.
-/

/-- Per-slice eigenvalue realization for the P3 Riemann-Ricci-Ricci contraction.

The fields deliberately mention only scalar curvature, `|Ric|^2`, Hamilton's
`Q`, and the Riemann-Ricci-Ricci contraction scalar. The harder coordinate
calculation is hidden in `reaction_eq`: in a Ricci eigenframe, the geometric
contraction `Rm * Ric * Ric` is `ricciEigenRiemannReaction3 l1 l2 l3`. -/
structure RicciReactionEigenvaluePackage
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (reaction : R) where
  l1 : R
  l2 : R
  l3 : R
  scalar_eq :
    ScalarCurvature emb conn ha hal hsl hl atr met =
      ricciEigenScalar3 l1 l2 l3
  ricciNormSq_eq :
    ricci_norm_sq emb conn ha hal hsl hl atr met =
      ricciEigenNormSq3 l1 l2 l3
  cubicQ_eq :
    hamiltonCubicQ emb conn ha hal hsl hl atr met =
      hamiltonCubicQ3 l1 l2 l3
  reaction_eq :
    reaction = ricciEigenRiemannReaction3 l1 l2 l3

/-- The P3 residual vanishes once the geometric Riemann-Ricci-Ricci contraction
has been reduced to its eigenvalue expression. This is the scalar algebra part
of P3. -/
theorem ricciReactionContractionResidual_eq_zero_of_eigenvalue_package
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (reaction : R)
    (pkg :
      RicciReactionEigenvaluePackage emb conn ha hal hsl hl atr met reaction) :
    ricciReactionContractionResidual emb conn ha hal hsl hl atr met reaction = 0 := by
  let l1 : R := pkg.l1
  let l2 : R := pkg.l2
  let l3 : R := pkg.l3
  have h_scalar :
      ScalarCurvature emb conn ha hal hsl hl atr met =
        ricciEigenScalar3 l1 l2 l3 := pkg.scalar_eq
  have h_norm :
      ricci_norm_sq emb conn ha hal hsl hl atr met =
        ricciEigenNormSq3 l1 l2 l3 := pkg.ricciNormSq_eq
  have h_Q :
      hamiltonCubicQ emb conn ha hal hsl hl atr met =
        hamiltonCubicQ3 l1 l2 l3 := pkg.cubicQ_eq
  have h_reaction :
      reaction = ricciEigenRiemannReaction3 l1 l2 l3 := pkg.reaction_eq
  unfold ricciReactionContractionResidual
  rw [h_scalar, h_norm, h_Q, h_reaction]
  exact sub_eq_zero.mpr
    (ricciEigenRiemannReaction3_cubicQ_relation l1 l2 l3)

/-- Eigenvalue realization data for the P3 Riemann-Ricci-Ricci contraction scalar.

This is a smaller, more geometric target than
`RicciReactionEigenvaluePackage`: the realization proves the synthetic scalar
curvature, Ricci norm, cubic trace, and Riemann-Ricci-Ricci contraction scalar
are the corresponding Ricci-eigenvalue expressions. The
`hamiltonCubicQ = hamiltonCubicQ3` field of `RicciReactionEigenvaluePackage` is
then derived internally from the definition of `Q`. -/
structure RicciReactionEigenvalueRealization
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (reaction : R) where
  l1 : R
  l2 : R
  l3 : R
  scalar_eq :
    ScalarCurvature emb conn ha hal hsl hl atr met =
      ricciEigenScalar3 l1 l2 l3
  ricciNormSq_eq :
    ricci_norm_sq emb conn ha hal hsl hl atr met =
      ricciEigenNormSq3 l1 l2 l3
  traceCube_eq :
    ricci_trace_cube emb conn ha hal hsl hl atr met =
      ricciEigenTraceCube3 l1 l2 l3
  reaction_eq :
    reaction = ricciEigenRiemannReaction3 l1 l2 l3

theorem hamiltonCubicQ_eq_hamiltonCubicQ3_of_ricciReactionEigenvalueRealization
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (reaction : R)
    (eig :
      RicciReactionEigenvalueRealization emb conn ha hal hsl hl atr met reaction) :
    hamiltonCubicQ emb conn ha hal hsl hl atr met =
      hamiltonCubicQ3 eig.l1 eig.l2 eig.l3 := by
  unfold hamiltonCubicQ hamiltonCubicQ3
  rw [eig.scalar_eq, eig.ricciNormSq_eq, eig.traceCube_eq]

/-- Convert the geometric eigenvalue realization target into the older package
shape consumed by the residual-zero proof. -/
noncomputable def ricciReactionEigenvaluePackage_of_eigenvalue_realization
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (reaction : R)
    (eig :
      RicciReactionEigenvalueRealization emb conn ha hal hsl hl atr met reaction) :
    RicciReactionEigenvaluePackage emb conn ha hal hsl hl atr met reaction where
  l1 := eig.l1
  l2 := eig.l2
  l3 := eig.l3
  scalar_eq := eig.scalar_eq
  ricciNormSq_eq := eig.ricciNormSq_eq
  cubicQ_eq :=
    hamiltonCubicQ_eq_hamiltonCubicQ3_of_ricciReactionEigenvalueRealization
      emb conn ha hal hsl hl atr met reaction eig
  reaction_eq := eig.reaction_eq

/-- Realization predicate for P3 using the direct eigenvalue realization
fields. This is the preferred target for the actual geometric contraction:
prove the scalar, norm, trace-cube, and Riemann-Ricci-Ricci contraction
identities in a Ricci eigenframe. -/
def IsRicciReactionEigenvalueRealized
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (reaction : R) : Prop :=
  Nonempty (RicciReactionEigenvalueRealization emb conn ha hal hsl hl atr met reaction)

/-- Build the P3 calculus class from direct Ricci-eigenvalue realization data.

This closes the synthetic cubic algebra once the realization layer has
identified the actual Riemann-Ricci-Ricci contraction scalar with its
Ricci-eigenvalue expression. -/
@[reducible]
noncomputable def hasRicciReactionContractionCalculus_of_eigenvalue_realizations
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) :
    HasRicciReactionContractionCalculus emb conn ha hal hsl hl atr met where
  IsGeometricReactionScalar :=
    IsRicciReactionEigenvalueRealized emb conn ha hal hsl hl atr met
  residual_zero := by
    intro reaction h_geom _h_dim _h_mc _h_tf
    rcases h_geom with ⟨eig⟩
    exact ricciReactionContractionResidual_eq_zero_of_eigenvalue_package
      emb conn ha hal hsl hl atr met reaction
      (ricciReactionEigenvaluePackage_of_eigenvalue_realization
        emb conn ha hal hsl hl atr met reaction eig)

theorem MetricDuality.eq_of_forall_g_basis_eq
    (met : MetricDuality R V) (basis : Module.Basis (Fin 3) R V) {X Y : V}
    (h : forall i : Fin 3, met.g X (basis i) = met.g Y (basis i)) :
    X = Y := by
  apply met.eq_of_forall_g_eq
  intro Z
  have hflat : met.flat X = met.flat Y := by
    apply basis.ext
    intro i
    exact h i
  exact congr_fun (congr_arg DFunLike.coe hflat) Z

theorem ricciEndomorphism_apply_basis_of_diagonalization
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met) (i : Fin 3) :
    RicciEndomorphism emb conn ha hal hsl hl atr met (diag.basis i) =
      diag.lambda i • diag.basis i := by
  apply MetricDuality.eq_of_forall_g_basis_eq met diag.basis
  intro j
  rw [RicciEndomorphism_spec emb conn ha hal hsl hl atr met]
  rw [← ricciForm_tensor_eval emb conn ha hal hsl hl atr]
  rw [diag.ricci_diagonal i j, met.g_smul_left, diag.orthonormal i j]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

theorem scalarCurvature_eq_ricciEigenScalar3_of_diagonalization
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met) :
    ScalarCurvature emb conn ha hal hsl hl atr met =
      ricciEigenScalar3 (diag.lambda 0) (diag.lambda 1) (diag.lambda 2) := by
  rw [scalarCurvature_eq_sum_lambda_of_orthonormal_trace3 emb conn ha hal hsl hl
    atr met diag]
  rw [Fin.sum_univ_three]
  unfold ricciEigenScalar3
  ring

theorem ricci_norm_sq_eq_ricciEigenNormSq3_of_diagonalization
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met) :
    ricci_norm_sq emb conn ha hal hsl hl atr met =
      ricciEigenNormSq3 (diag.lambda 0) (diag.lambda 1) (diag.lambda 2) := by
  let T : V →ₗ[R] V := RicciEndomorphism emb conn ha hal hsl hl atr met
  unfold ricci_norm_sq
  change atr.tr (T.comp T) =
    ricciEigenNormSq3 (diag.lambda 0) (diag.lambda 1) (diag.lambda 2)
  rw [HasOrthonormalBasisTraceFormula3.tr_eq_sum_orthonormal3
    diag.basis diag.orthonormal]
  have hterm : forall i : Fin 3,
      met.g (diag.basis i) ((T.comp T) (diag.basis i)) = diag.lambda i ^ 2 := by
    intro i
    have hT :
        T (diag.basis i) = diag.lambda i • diag.basis i := by
      dsimp [T]
      exact ricciEndomorphism_apply_basis_of_diagonalization
        emb conn ha hal hsl hl atr met diag i
    calc
      met.g (diag.basis i) ((T.comp T) (diag.basis i))
          = met.g (diag.basis i) (T (T (diag.basis i))) := by
              rfl
      _ = met.g (diag.basis i) (T (diag.lambda i • diag.basis i)) := by
              rw [hT]
      _ = met.g (diag.basis i) (diag.lambda i • T (diag.basis i)) := by
              rw [map_smul]
      _ = met.g (diag.basis i)
            (diag.lambda i • (diag.lambda i • diag.basis i)) := by
              rw [hT]
      _ = diag.lambda i ^ 2 := by
              rw [met.g_smul_right, met.g_smul_right, diag.orthonormal i i]
              simp
              ring
  calc
    ∑ i : Fin 3, met.g (diag.basis i) ((T.comp T) (diag.basis i))
        = ∑ i : Fin 3, diag.lambda i ^ 2 := by
            exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ricciEigenNormSq3 (diag.lambda 0) (diag.lambda 1) (diag.lambda 2) := by
            rw [Fin.sum_univ_three]
            unfold ricciEigenNormSq3
            ring

theorem ricci_trace_cube_eq_ricciEigenTraceCube3_of_diagonalization
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met) :
    ricci_trace_cube emb conn ha hal hsl hl atr met =
      ricciEigenTraceCube3 (diag.lambda 0) (diag.lambda 1) (diag.lambda 2) := by
  let T : V →ₗ[R] V := RicciEndomorphism emb conn ha hal hsl hl atr met
  unfold ricci_trace_cube
  change atr.tr (T.comp (T.comp T)) =
    ricciEigenTraceCube3 (diag.lambda 0) (diag.lambda 1) (diag.lambda 2)
  rw [HasOrthonormalBasisTraceFormula3.tr_eq_sum_orthonormal3
    diag.basis diag.orthonormal]
  have hterm : forall i : Fin 3,
      met.g (diag.basis i) ((T.comp (T.comp T)) (diag.basis i)) =
        diag.lambda i ^ 3 := by
    intro i
    have hT :
        T (diag.basis i) = diag.lambda i • diag.basis i := by
      dsimp [T]
      exact ricciEndomorphism_apply_basis_of_diagonalization
        emb conn ha hal hsl hl atr met diag i
    calc
      met.g (diag.basis i) ((T.comp (T.comp T)) (diag.basis i))
          = met.g (diag.basis i) (T (T (T (diag.basis i)))) := by
              rfl
      _ = met.g (diag.basis i) (T (T (diag.lambda i • diag.basis i))) := by
              rw [hT]
      _ = met.g (diag.basis i) (T (diag.lambda i • T (diag.basis i))) := by
              rw [map_smul]
      _ = met.g (diag.basis i)
            (T (diag.lambda i • (diag.lambda i • diag.basis i))) := by
              rw [hT]
      _ = met.g (diag.basis i)
            (diag.lambda i • T (diag.lambda i • diag.basis i)) := by
              rw [map_smul]
      _ = met.g (diag.basis i)
            (diag.lambda i • (diag.lambda i • T (diag.basis i))) := by
              rw [map_smul]
      _ = met.g (diag.basis i)
            (diag.lambda i • (diag.lambda i • (diag.lambda i • diag.basis i))) := by
              rw [hT]
      _ = diag.lambda i ^ 3 := by
              rw [met.g_smul_right, met.g_smul_right, met.g_smul_right,
                diag.orthonormal i i]
              simp
              ring
  calc
    ∑ i : Fin 3, met.g (diag.basis i) ((T.comp (T.comp T)) (diag.basis i))
        = ∑ i : Fin 3, diag.lambda i ^ 3 := by
            exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ricciEigenTraceCube3 (diag.lambda 0) (diag.lambda 1) (diag.lambda 2) := by
            rw [Fin.sum_univ_three]
            unfold ricciEigenTraceCube3
            ring

/-- The Riemann-Ricci-Ricci contraction scalar expanded in a Ricci eigenframe.

This is the finite component expression
`sum_i sum_j Rm_lowered(e_i,e_j,e_i,e_j) lambda_i lambda_j`, using the same
slot convention as `sectionalComponent3D`. -/
noncomputable def ricciEigenframeRiemannReaction3D
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met) : R :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    Rm_lowered emb conn met (diag.basis i) (diag.basis j)
        (diag.basis i) (diag.basis j) *
      diag.lambda i * diag.lambda j

/-- In a Ricci eigenframe, the sectional-curvature formulas reduce the
Riemann-Ricci-Ricci contraction scalar to Hamilton's three-eigenvalue expression. -/
theorem ricciEigenframeRiemannReaction3D_eq_ricciEigenRiemannReaction3_of_sectional_trace
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (half : R)
    (sec : RicciSectionalTraceFormula3D emb conn ha hal hsl hl atr met diag half) :
    ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met diag =
      ricciEigenRiemannReaction3 (diag.lambda 0) (diag.lambda 1) (diag.lambda 2) := by
  have h00 :
      Rm_lowered emb conn met (diag.basis 0) (diag.basis 0)
          (diag.basis 0) (diag.basis 0) = 0 := by
    exact Rm_lowered_self_first_pair_eq_zero emb conn hal met h2
      (diag.basis 0) (diag.basis 0) (diag.basis 0)
  have h11 :
      Rm_lowered emb conn met (diag.basis 1) (diag.basis 1)
          (diag.basis 1) (diag.basis 1) = 0 := by
    exact Rm_lowered_self_first_pair_eq_zero emb conn hal met h2
      (diag.basis 1) (diag.basis 1) (diag.basis 1)
  have h22 :
      Rm_lowered emb conn met (diag.basis 2) (diag.basis 2)
          (diag.basis 2) (diag.basis 2) = 0 := by
    exact Rm_lowered_self_first_pair_eq_zero emb conn hal met h2
      (diag.basis 2) (diag.basis 2) (diag.basis 2)
  have h01 :
      Rm_lowered emb conn met (diag.basis 0) (diag.basis 1)
          (diag.basis 0) (diag.basis 1) =
        half * (diag.lambda 0 + diag.lambda 1 - diag.lambda 2) := by
    change sectionalComponent3D emb conn met diag.basis 0 1 =
      half * (diag.lambda 0 + diag.lambda 1 - diag.lambda 2)
    exact sec.sectional_01
  have h02 :
      Rm_lowered emb conn met (diag.basis 0) (diag.basis 2)
          (diag.basis 0) (diag.basis 2) =
        half * (diag.lambda 0 + diag.lambda 2 - diag.lambda 1) := by
    change sectionalComponent3D emb conn met diag.basis 0 2 =
      half * (diag.lambda 0 + diag.lambda 2 - diag.lambda 1)
    exact sec.sectional_02
  have h12 :
      Rm_lowered emb conn met (diag.basis 1) (diag.basis 2)
          (diag.basis 1) (diag.basis 2) =
        half * (diag.lambda 1 + diag.lambda 2 - diag.lambda 0) := by
    change sectionalComponent3D emb conn met diag.basis 1 2 =
      half * (diag.lambda 1 + diag.lambda 2 - diag.lambda 0)
    exact sec.sectional_12
  have h10 :
      Rm_lowered emb conn met (diag.basis 1) (diag.basis 0)
          (diag.basis 1) (diag.basis 0) =
        half * (diag.lambda 0 + diag.lambda 1 - diag.lambda 2) := by
    change sectionalComponent3D emb conn met diag.basis 1 0 =
      half * (diag.lambda 0 + diag.lambda 1 - diag.lambda 2)
    rw [sectionalComponent3D_swap emb conn hal met h_mc diag.basis (0 : Fin 3) 1]
    exact sec.sectional_01
  have h20 :
      Rm_lowered emb conn met (diag.basis 2) (diag.basis 0)
          (diag.basis 2) (diag.basis 0) =
        half * (diag.lambda 0 + diag.lambda 2 - diag.lambda 1) := by
    change sectionalComponent3D emb conn met diag.basis 2 0 =
      half * (diag.lambda 0 + diag.lambda 2 - diag.lambda 1)
    rw [sectionalComponent3D_swap emb conn hal met h_mc diag.basis (0 : Fin 3) 2]
    exact sec.sectional_02
  have h21 :
      Rm_lowered emb conn met (diag.basis 2) (diag.basis 1)
          (diag.basis 2) (diag.basis 1) =
        half * (diag.lambda 1 + diag.lambda 2 - diag.lambda 0) := by
    change sectionalComponent3D emb conn met diag.basis 2 1 =
      half * (diag.lambda 1 + diag.lambda 2 - diag.lambda 0)
    rw [sectionalComponent3D_swap emb conn hal met h_mc diag.basis (1 : Fin 3) 2]
    exact sec.sectional_12
  unfold ricciEigenframeRiemannReaction3D
  repeat rw [Fin.sum_univ_three]
  rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
  unfold ricciEigenRiemannReaction3
  have hhalf : (2 : R) * half = 1 := sec.h_half
  linear_combination
    (diag.lambda 0 * diag.lambda 1 * (diag.lambda 0 + diag.lambda 1 - diag.lambda 2) +
      diag.lambda 0 * diag.lambda 2 * (diag.lambda 0 + diag.lambda 2 - diag.lambda 1) +
      diag.lambda 1 * diag.lambda 2 * (diag.lambda 1 + diag.lambda 2 - diag.lambda 0)) *
        hhalf

/-- Construct the direct P3 eigenvalue realization from a Ricci eigenframe and
the single Riemann-Ricci-Ricci contraction eigenvalue identity.

The scalar, Ricci-norm, and cubic-trace fields are derived from the
orthonormal trace formula and the diagonalization data. The only remaining
geometric input is `h_reaction`, which identifies the actual `Rm * Ric * Ric`
contraction scalar with the standard 3D eigenvalue expression. -/
noncomputable def ricciReactionEigenvalueRealization_of_diagonalization
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (reaction : R)
    (h_reaction :
      reaction =
        ricciEigenRiemannReaction3 (diag.lambda 0) (diag.lambda 1) (diag.lambda 2)) :
    RicciReactionEigenvalueRealization emb conn ha hal hsl hl atr met reaction where
  l1 := diag.lambda 0
  l2 := diag.lambda 1
  l3 := diag.lambda 2
  scalar_eq :=
    scalarCurvature_eq_ricciEigenScalar3_of_diagonalization
      emb conn ha hal hsl hl atr met diag
  ricciNormSq_eq :=
    ricci_norm_sq_eq_ricciEigenNormSq3_of_diagonalization
      emb conn ha hal hsl hl atr met diag
  traceCube_eq :=
    ricci_trace_cube_eq_ricciEigenTraceCube3_of_diagonalization
      emb conn ha hal hsl hl atr met diag
  reaction_eq := h_reaction

/-- Construct the direct P3 eigenvalue realization from a Ricci eigenframe and
the solved sectional curvature formulas.

This discharges the reaction-specific eigenvalue identity for the concrete
finite-frame scalar `ricciEigenframeRiemannReaction3D`. -/
noncomputable def ricciReactionEigenvalueRealization_of_sectional_trace
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (h_mc : IsMetricCompatible emb conn met)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (half : R)
    (sec : RicciSectionalTraceFormula3D emb conn ha hal hsl hl atr met diag half) :
    RicciReactionEigenvalueRealization emb conn ha hal hsl hl atr met
      (ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met diag) :=
  ricciReactionEigenvalueRealization_of_diagonalization
    emb conn ha hal hsl hl atr met diag
    (ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met diag)
    (ricciEigenframeRiemannReaction3D_eq_ricciEigenRiemannReaction3_of_sectional_trace
      emb conn ha hal hsl hl atr met h_mc h2 diag half sec)

/-- Construct the direct P3 eigenvalue realization from an orthonormal Ricci
eigenframe trace formula.

This packages the P2 trace solve internally, then applies the sectional-trace
reaction contraction theorem. -/
noncomputable def ricciReactionEigenvalueRealization_of_orthonormal_trace3
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (h_mc : IsMetricCompatible emb conn met)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (half : R) (h_half : IsHalfCoefficient half) :
    RicciReactionEigenvalueRealization emb conn ha hal hsl hl atr met
      (ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met diag) := by
  let sec :
      RicciSectionalTraceFormula3D emb conn ha hal hsl hl atr met diag half :=
    ricciSectionalTraceFormula3D_of_orthonormal_trace3
      emb conn ha hal hsl hl atr met h_mc h2 diag half h_half
  exact ricciReactionEigenvalueRealization_of_sectional_trace
    emb conn ha hal hsl hl atr met h_mc h2 diag half sec

/-- Construct the direct P3 eigenvalue realization from the P2 trace/eigenframe
package.

The package already contains the orthonormal trace formula, metric
compatibility, two-cancel hypothesis, half coefficient, and Ricci
diagonalization needed by the P3 eigenframe contraction proof. -/
noncomputable def ricciReactionEigenvalueRealization_of_trace_eigenframe_package
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (pkg :
      RiemannFromRicci3DTraceEigenframePackage emb conn ha hal hsl hl atr met) :
    RicciReactionEigenvalueRealization emb conn ha hal hsl hl atr met
      (ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met
        pkg.diagonalization) := by
  haveI : HasOrthonormalBasisTraceFormula3 atr met := pkg.trace_formula
  exact ricciReactionEigenvalueRealization_of_orthonormal_trace3
    emb conn ha hal hsl hl atr met pkg.metric_compatible pkg.two_cancel
    pkg.diagonalization pkg.half pkg.half_coeff

/-- Predicate-level constructor for the preferred direct P3 realization. -/
theorem isRicciReactionEigenvalueRealized_of_diagonalization
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (reaction : R)
    (h_reaction :
      reaction =
        ricciEigenRiemannReaction3 (diag.lambda 0) (diag.lambda 1) (diag.lambda 2)) :
    IsRicciReactionEigenvalueRealized emb conn ha hal hsl hl atr met reaction :=
  Nonempty.intro
    (ricciReactionEigenvalueRealization_of_diagonalization
      emb conn ha hal hsl hl atr met diag reaction h_reaction)

/-- Predicate-level constructor from solved sectional curvature formulas. -/
theorem isRicciReactionEigenvalueRealized_of_sectional_trace
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (h_mc : IsMetricCompatible emb conn met)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (half : R)
    (sec : RicciSectionalTraceFormula3D emb conn ha hal hsl hl atr met diag half) :
    IsRicciReactionEigenvalueRealized emb conn ha hal hsl hl atr met
      (ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met diag) :=
  Nonempty.intro
    (ricciReactionEigenvalueRealization_of_sectional_trace
      emb conn ha hal hsl hl atr met h_mc h2 diag half sec)

/-- Predicate-level constructor from an orthonormal Ricci eigenframe trace
formula. -/
theorem isRicciReactionEigenvalueRealized_of_orthonormal_trace3
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (h_mc : IsMetricCompatible emb conn met)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (half : R) (h_half : IsHalfCoefficient half) :
    IsRicciReactionEigenvalueRealized emb conn ha hal hsl hl atr met
      (ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met diag) :=
  Nonempty.intro
    (ricciReactionEigenvalueRealization_of_orthonormal_trace3
      emb conn ha hal hsl hl atr met h_mc h2 diag half h_half)

/-- Predicate-level constructor from the P2 trace/eigenframe package. -/
theorem isRicciReactionEigenvalueRealized_of_trace_eigenframe_package
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (pkg :
      RiemannFromRicci3DTraceEigenframePackage emb conn ha hal hsl hl atr met) :
    IsRicciReactionEigenvalueRealized emb conn ha hal hsl hl atr met
      (ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met
        pkg.diagonalization) :=
  Nonempty.intro
    (ricciReactionEigenvalueRealization_of_trace_eigenframe_package
      emb conn ha hal hsl hl atr met pkg)

/-- Realization predicate for P3 when the concrete proof proceeds through a
Ricci eigenframe. This should be the common coordinate/eigenframe target:
construct this package, and the scalar cubic reaction identity follows. -/
def IsRicciReactionEigenvalueGeometric
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (reaction : R) : Prop :=
  Nonempty (RicciReactionEigenvaluePackage emb conn ha hal hsl hl atr met reaction)

/-- A direct eigenvalue realization supplies the package predicate consumed by
the Hamilton P3 default instance. -/
theorem isRicciReactionEigenvalueGeometric_of_eigenvalue_realization
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (reaction : R)
    (eig :
      RicciReactionEigenvalueRealization emb conn ha hal hsl hl atr met reaction) :
    IsRicciReactionEigenvalueGeometric emb conn ha hal hsl hl atr met reaction :=
  Nonempty.intro
    (ricciReactionEigenvaluePackage_of_eigenvalue_realization
      emb conn ha hal hsl hl atr met reaction eig)

/-- Solved sectional curvature formulas supply the package predicate consumed
by the Hamilton P3 default instance for the finite eigenframe
Riemann-Ricci-Ricci contraction scalar. -/
theorem isRicciReactionEigenvalueGeometric_of_sectional_trace
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (h_mc : IsMetricCompatible emb conn met)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (half : R)
    (sec : RicciSectionalTraceFormula3D emb conn ha hal hsl hl atr met diag half) :
    IsRicciReactionEigenvalueGeometric emb conn ha hal hsl hl atr met
      (ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met diag) :=
  isRicciReactionEigenvalueGeometric_of_eigenvalue_realization
    emb conn ha hal hsl hl atr met
    (ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met diag)
    (ricciReactionEigenvalueRealization_of_sectional_trace
      emb conn ha hal hsl hl atr met h_mc h2 diag half sec)

/-- Orthonormal Ricci eigenframe trace data supplies the package predicate
consumed by the Hamilton P3 default instance for the finite eigenframe
Riemann-Ricci-Ricci contraction scalar. -/
theorem isRicciReactionEigenvalueGeometric_of_orthonormal_trace3
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (h_mc : IsMetricCompatible emb conn met)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (half : R) (h_half : IsHalfCoefficient half) :
    IsRicciReactionEigenvalueGeometric emb conn ha hal hsl hl atr met
      (ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met diag) :=
  isRicciReactionEigenvalueGeometric_of_eigenvalue_realization
    emb conn ha hal hsl hl atr met
    (ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met diag)
    (ricciReactionEigenvalueRealization_of_orthonormal_trace3
      emb conn ha hal hsl hl atr met h_mc h2 diag half h_half)

/-- The P2 trace/eigenframe package supplies the package predicate consumed by
the Hamilton P3 default instance for the finite eigenframe
Riemann-Ricci-Ricci contraction scalar. -/
theorem isRicciReactionEigenvalueGeometric_of_trace_eigenframe_package
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (pkg :
      RiemannFromRicci3DTraceEigenframePackage emb conn ha hal hsl hl atr met) :
    IsRicciReactionEigenvalueGeometric emb conn ha hal hsl hl atr met
      (ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met
        pkg.diagonalization) :=
  isRicciReactionEigenvalueGeometric_of_eigenvalue_realization
    emb conn ha hal hsl hl atr met
    (ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met
      pkg.diagonalization)
    (ricciReactionEigenvalueRealization_of_trace_eigenframe_package
      emb conn ha hal hsl hl atr met pkg)

/-- Diagonalization-level constructor for the package predicate consumed by
Hamilton P3.

The only caller-supplied identity is the actual Riemann-Ricci-Ricci contraction
scalar computation in the Ricci eigenframe. The scalar, norm, trace-cube, and
`Q` eigenvalue identities are derived internally. -/
theorem isRicciReactionEigenvalueGeometric_of_diagonalization
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (reaction : R)
    (h_reaction :
      reaction =
        ricciEigenRiemannReaction3 (diag.lambda 0) (diag.lambda 1) (diag.lambda 2)) :
    IsRicciReactionEigenvalueGeometric emb conn ha hal hsl hl atr met reaction :=
  isRicciReactionEigenvalueGeometric_of_eigenvalue_realization
    emb conn ha hal hsl hl atr met reaction
    (ricciReactionEigenvalueRealization_of_diagonalization
      emb conn ha hal hsl hl atr met diag reaction h_reaction)

/-- Build the P3 calculus class from the eigenvalue realization target.

The remaining geometric work is exactly to prove
`IsRicciReactionEigenvalueGeometric` for the actual Riemann-Ricci-Ricci
contraction scalar. No coordinate details appear in this constructor. -/
@[reducible]
noncomputable def hasRicciReactionContractionCalculus_of_eigenvalue_packages
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) :
    HasRicciReactionContractionCalculus emb conn ha hal hsl hl atr met where
  IsGeometricReactionScalar :=
    IsRicciReactionEigenvalueGeometric emb conn ha hal hsl hl atr met
  residual_zero := by
    intro reaction h_geom _h_dim _h_mc _h_tf
    rcases h_geom with ⟨pkg⟩
    exact ricciReactionContractionResidual_eq_zero_of_eigenvalue_package
      emb conn ha hal hsl hl atr met reaction pkg

/-- Build the P3 calculus class from a P2 trace/eigenframe package.

The geometricity predicate becomes the concrete statement that the chosen scalar
is the finite Ricci-eigenframe Riemann-Ricci-Ricci contraction
`ricciEigenframeRiemannReaction3D` associated to the package. -/
@[reducible]
noncomputable def hasRicciReactionContractionCalculus_of_trace_eigenframe_package
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (pkg :
      RiemannFromRicci3DTraceEigenframePackage emb conn ha hal hsl hl atr met) :
    HasRicciReactionContractionCalculus emb conn ha hal hsl hl atr met where
  IsGeometricReactionScalar reaction :=
    reaction =
      ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met pkg.diagonalization
  residual_zero := by
    intro reaction h_reaction _h_dim _h_mc _h_tf
    subst reaction
    have eig :
        RicciReactionEigenvalueRealization emb conn ha hal hsl hl atr met
          (ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met
            pkg.diagonalization) :=
      ricciReactionEigenvalueRealization_of_trace_eigenframe_package
        emb conn ha hal hsl hl atr met pkg
    exact ricciReactionContractionResidual_eq_zero_of_eigenvalue_package
      emb conn ha hal hsl hl atr met
      (ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met
        pkg.diagonalization)
      (ricciReactionEigenvaluePackage_of_eigenvalue_realization
        emb conn ha hal hsl hl atr met
        (ricciEigenframeRiemannReaction3D emb conn ha hal hsl hl atr met
          pkg.diagonalization) eig)

/-- Convert a Riemann-Ricci-Ricci contraction data package into the calculus typeclass.

The data package binds a single contraction value with its own geometricity
predicate (a `Prop`); to fit the calculus typeclass which takes a `R -> Prop`
realization predicate, this constructor uses the indicator predicate
`fun r => r = data.reaction ∧ data.IsGeometricReactionScalar`. The realization
that prefers a more general geometricity predicate should provide a custom
`HasRicciReactionContractionCalculus` instance directly. -/
@[reducible]
noncomputable def hasRicciReactionContractionCalculus_of_data_package
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (data : RicciReactionContractionDataPackage emb conn ha hal hsl hl atr met) :
    HasRicciReactionContractionCalculus emb conn ha hal hsl hl atr met where
  IsGeometricReactionScalar r := r = data.reaction /\ data.IsGeometricReactionScalar
  residual_zero := by
    intro reaction h_geom h_dim h_mc h_tf
    obtain ⟨h_eq, h_pkg⟩ := h_geom
    subst h_eq
    exact data.residual_zero h_dim h_mc h_tf h_pkg

/-- Build a data package directly from a reaction value, a geometricity
witness, and the residual-zero proof. Convenience constructor for realizations
that work at the data-package level. -/
noncomputable def ricciReactionContractionDataPackage_of_residual_zero
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (reaction : R) (IsGeom : Prop)
    (h_residual :
      IsDimensionThree atr ->
        IsMetricCompatible emb conn met ->
          IsTorsionFree emb conn ->
            IsGeom ->
              ricciReactionContractionResidual emb conn ha hal hsl hl atr met reaction = 0) :
    RicciReactionContractionDataPackage emb conn ha hal hsl hl atr met where
  reaction := reaction
  IsGeometricReactionScalar := IsGeom
  residual_zero := h_residual

end RicciReactionContractionArchitecture

section TracefreeRicciNormHeatFromContractionCalculus

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [Field R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Full P3 trace-free Ricci norm heat identity from the
Riemann-Ricci-Ricci contraction calculus.

This is the downstream-facing version of
`hamilton3D_tracefree_norm_eq_of_cubic_reaction_components`: the contraction
identity
`2 R * (Riemann-Ricci-Ricci contraction) = 2 |Ric|^4 - Q`
is discharged from `HasRicciReactionContractionCalculus`. The remaining inputs
are the analytic component identities for the Ricci-norm heat equation, scalar
heat equation, scalar-square Laplacian, and the basic smoothness hypotheses
needed by the time-derivative product rule. -/
theorem hamilton3D_tracefree_norm_heat_eq_of_contraction_calculus
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (nInv : R)
    (h_nInv_dim : nInv * abstractTraceDimension atr = 1)
    (h_nInv_const : forall X : V, action emb X nInv = 0)
    (h_nInv : nInv = (1 : R) / 3)
    (h_dim : IsDimensionThree atr)
    (h_mc : forall t, IsMetricCompatible emb (conn_fam t) (g_fam t))
    (h_tf : forall t, IsTorsionFree emb (conn_fam t))
    (h_calc : forall t,
      HasRicciReactionContractionCalculus emb (conn_fam t)
        (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr (g_fam t))
    (ricciNormDt scalarDt ricciNormLap scalarLap gradScalarNormSq
        nablaRicNormSq cubicQ contraction : Time -> R)
    (h_geom : forall t, (h_calc t).IsGeometricReactionScalar (contraction t))
    (h_cubicQ : forall t,
      cubicQ t =
        hamiltonCubicQ emb (conn_fam t) (ha_fam t) (hal_fam t)
          (hsl_fam t) (hl_fam t) atr (g_fam t))
    (h_scalar_ne : forall t,
      scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t ≠ 0)
    (h_ricciNorm_dt :
      RicciNormEvolutionEquation emb td atr g_fam conn_fam ha_fam hal_fam
        hsl_fam hl_fam ricciNormDt)
    (h_scalar_dt : forall t,
      td.dt_apply
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
        t = scalarDt t)
    (h_ricciNorm_smooth :
      td.isSmoothFam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_scalar_smooth :
      td.isSmoothFam
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_ricciNorm_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam) t =
      ricciNormLap t)
    (h_scalar_square_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (fun s =>
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s) t =
      2 *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
          scalarLap t +
        2 * gradScalarNormSq t)
    (h_ricciNorm_heat : forall t,
      ricciNormDt t - ricciNormLap t =
        -2 * nablaRicNormSq t + 4 * contraction t)
    (h_scalar_heat : forall t,
      scalarDt t - scalarLap t =
        2 * ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t) :
    TracefreeRicciNormHamilton3DTimeLaplacianEquation
      (fun u t => td.dt_apply u t)
      (scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      (tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv)
      nablaRicNormSq gradScalarNormSq
      (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      cubicQ
      (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam) := by
  have h_contraction : forall t,
      2 *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
          contraction t =
        2 *
            ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t ^ 2 -
          cubicQ t := by
    intro t
    have h_zero :=
      (h_calc t).residual_zero (contraction t) (h_geom t) h_dim (h_mc t) (h_tf t)
    have h_rel :
        2 * ScalarCurvature emb (conn_fam t) (ha_fam t) (hal_fam t)
              (hsl_fam t) (hl_fam t) atr (g_fam t) * contraction t =
          2 * ricci_norm_sq emb (conn_fam t) (ha_fam t) (hal_fam t)
              (hsl_fam t) (hl_fam t) atr (g_fam t) ^ 2 -
            hamiltonCubicQ emb (conn_fam t) (ha_fam t) (hal_fam t)
              (hsl_fam t) (hl_fam t) atr (g_fam t) := by
      unfold ricciReactionContractionResidual at h_zero
      linear_combination h_zero
    rw [h_cubicQ t]
    simpa [scalarCurvatureAlongFlow, ricciNormSqAlongFlow] using h_rel
  exact hamilton3D_tracefree_norm_eq_of_cubic_reaction_components
    emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv
    h_nInv_dim h_nInv_const h_nInv ricciNormDt scalarDt ricciNormLap
    scalarLap gradScalarNormSq nablaRicNormSq cubicQ contraction h_scalar_ne
    h_ricciNorm_dt h_scalar_dt h_ricciNorm_smooth h_scalar_smooth
    h_ricciNorm_lap h_scalar_square_lap h_ricciNorm_heat h_scalar_heat
    h_contraction

/-- Full P3 trace-free Ricci norm heat identity from P2 trace/eigenframe
packages.

This is the most concrete checked synthetic route currently available. The
Riemann-Ricci-Ricci contraction scalar is not an extra opaque input here: at
time `t` it is the finite eigenframe contraction
`ricciEigenframeRiemannReaction3D ... (h_pkg t).diagonalization` supplied by
the P2 trace/eigenframe package. -/
theorem hamilton3D_tracefree_norm_heat_eq_of_trace_eigenframe_packages
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (nInv : R)
    (h_nInv_dim : nInv * abstractTraceDimension atr = 1)
    (h_nInv_const : forall X : V, action emb X nInv = 0)
    (h_nInv : nInv = (1 : R) / 3)
    (h_dim : IsDimensionThree atr)
    (h_pkg : forall t,
      RiemannFromRicci3DTraceEigenframePackage emb (conn_fam t)
        (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr (g_fam t))
    (ricciNormDt scalarDt ricciNormLap scalarLap gradScalarNormSq
        nablaRicNormSq cubicQ : Time -> R)
    (h_cubicQ : forall t,
      cubicQ t =
        hamiltonCubicQ emb (conn_fam t) (ha_fam t) (hal_fam t)
          (hsl_fam t) (hl_fam t) atr (g_fam t))
    (h_scalar_ne : forall t,
      scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t ≠ 0)
    (h_ricciNorm_dt :
      RicciNormEvolutionEquation emb td atr g_fam conn_fam ha_fam hal_fam
        hsl_fam hl_fam ricciNormDt)
    (h_scalar_dt : forall t,
      td.dt_apply
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
        t = scalarDt t)
    (h_ricciNorm_smooth :
      td.isSmoothFam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_scalar_smooth :
      td.isSmoothFam
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_ricciNorm_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam) t =
      ricciNormLap t)
    (h_scalar_square_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (fun s =>
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s) t =
      2 *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
          scalarLap t +
        2 * gradScalarNormSq t)
    (h_ricciNorm_heat : forall t,
      ricciNormDt t - ricciNormLap t =
        -2 * nablaRicNormSq t +
          4 *
            ricciEigenframeRiemannReaction3D emb (conn_fam t)
              (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr (g_fam t)
              (h_pkg t).diagonalization)
    (h_scalar_heat : forall t,
      scalarDt t - scalarLap t =
        2 * ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t) :
    TracefreeRicciNormHamilton3DTimeLaplacianEquation
      (fun u t => td.dt_apply u t)
      (scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      (tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv)
      nablaRicNormSq gradScalarNormSq
      (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      cubicQ
      (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam) :=
  hamilton3D_tracefree_norm_heat_eq_of_contraction_calculus
    emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv
    h_nInv_dim h_nInv_const h_nInv h_dim
    (fun t => (h_pkg t).metric_compatible)
    (fun t => (h_pkg t).torsion_free)
    (fun t =>
      hasRicciReactionContractionCalculus_of_trace_eigenframe_package
        emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t)
        atr (g_fam t) (h_pkg t))
    ricciNormDt scalarDt ricciNormLap scalarLap gradScalarNormSq nablaRicNormSq
    cubicQ
    (fun t =>
      ricciEigenframeRiemannReaction3D emb (conn_fam t)
        (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr (g_fam t)
        (h_pkg t).diagonalization)
    (by
      intro t
      rfl)
    h_cubicQ h_scalar_ne h_ricciNorm_dt h_scalar_dt h_ricciNorm_smooth
    h_scalar_smooth h_ricciNorm_lap h_scalar_square_lap h_ricciNorm_heat
    h_scalar_heat

/-- Full P3 trace-free Ricci norm heat identity from P2 trace/eigenframe
packages and lower-level evolution components.

Compared with `hamilton3D_tracefree_norm_heat_eq_of_trace_eigenframe_packages`,
this version does not ask for the scalar heat equation or the Ricci-norm heat
equation as already-assembled inputs. It derives them from:

* the scalar-curvature evolution theorem plus the trace identity identifying
  `tr(partial_t Ric)` with the scalar Laplacian term;
* the Ricci-norm time derivative component and Bochner Laplacian component.

The scalar-square Laplacian rule remains explicit because the current
synthetic Laplacian API has no general multiplication theorem. -/
theorem hamilton3D_tracefree_norm_heat_eq_of_trace_eigenframe_evolution_components
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (h_met : forall vs covs, td.isSmoothFam (fun s => (g_fam s).g_tensor vs covs))
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs covs, td.isSmoothFam
      (fun s =>
        ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
          (hsl_fam s) (hl_fam s) atr vs covs))
    (h_rf : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h_sc_prod : ScalarCurvatureProductRule emb td atr g_fam h_met conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rc_smooth)
    (nInv : R)
    (h_nInv_dim : nInv * abstractTraceDimension atr = 1)
    (h_nInv_const : forall X : V, action emb X nInv = 0)
    (h_nInv : nInv = (1 : R) / 3)
    (h_dim : IsDimensionThree atr)
    (h_pkg : forall t,
      RiemannFromRicci3DTraceEigenframePackage emb (conn_fam t)
        (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr (g_fam t))
    (ricciNormDt scalarDt ricciNormLap scalarLap gradScalarNormSq
        nablaRicNormSq cubicQ lapInner : Time -> R)
    (h_cubicQ : forall t,
      cubicQ t =
        hamiltonCubicQ emb (conn_fam t) (ha_fam t) (hal_fam t)
          (hsl_fam t) (hl_fam t) atr (g_fam t))
    (h_scalar_ne : forall t,
      scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t ≠ 0)
    (h_ricciNorm_dt :
      RicciNormEvolutionEquation emb td atr g_fam conn_fam ha_fam hal_fam
        hsl_fam hl_fam ricciNormDt)
    (h_scalar_dt : forall t,
      td.dt_apply
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
        t = scalarDt t)
    (h_ricciNorm_smooth :
      td.isSmoothFam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_scalar_smooth :
      td.isSmoothFam
        (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam))
    (h_ricciNorm_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam) t =
      ricciNormLap t)
    (h_scalar_square_lap : forall t,
      scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        (fun s =>
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam s) t =
      2 *
          scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam t *
          scalarLap t +
        2 * gradScalarNormSq t)
    (h_scalar_trace : RicciTraceIdentity emb td atr g_fam conn_fam ha_fam hal_fam
      hsl_fam hl_fam h_Rc_smooth scalarLap)
    (h_ricciNorm_dt_component : forall t,
      ricciNormDt t =
        2 * lapInner t +
          4 *
            ricciEigenframeRiemannReaction3D emb (conn_fam t)
              (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr (g_fam t)
              (h_pkg t).diagonalization)
    (h_ricciNorm_lap_component : forall t,
      ricciNormLap t = 2 * lapInner t + 2 * nablaRicNormSq t) :
    TracefreeRicciNormHamilton3DTimeLaplacianEquation
      (fun u t => td.dt_apply u t)
      (scalarLaplacianAlongTimeSlice emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      (tracefreeRicciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv)
      nablaRicNormSq gradScalarNormSq
      (ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
      cubicQ
      (scalarCurvatureAlongFlow emb atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam) := by
  exact hamilton3D_tracefree_norm_heat_eq_of_trace_eigenframe_packages
    emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam nInv
    h_nInv_dim h_nInv_const h_nInv h_dim h_pkg ricciNormDt scalarDt
    ricciNormLap scalarLap gradScalarNormSq nablaRicNormSq cubicQ h_cubicQ
    h_scalar_ne h_ricciNorm_dt h_scalar_dt h_ricciNorm_smooth h_scalar_smooth
    h_ricciNorm_lap h_scalar_square_lap
    (ricci_norm_heat_eq_of_dt_laplacian_components
      ricciNormDt ricciNormLap lapInner nablaRicNormSq
      (fun t =>
        ricciEigenframeRiemannReaction3D emb (conn_fam t)
          (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr (g_fam t)
          (h_pkg t).diagonalization)
      h_ricciNorm_dt_component h_ricciNorm_lap_component)
    (by
      intro t
      have h_full :=
        scalar_curvature_evolution_full emb td atr g_fam h_met conn_fam
          ha_fam hal_fam hsl_fam hl_fam h_Rc_smooth h_rf h_sc_prod
          scalarLap h_scalar_trace t
      have h_dt :
          scalarDt t =
            scalarLap t +
              2 *
                ricciNormSqAlongFlow emb atr g_fam conn_fam ha_fam hal_fam
                  hsl_fam hl_fam t := by
        rw [← h_scalar_dt t]
        simpa [scalarCurvatureAlongFlow, ricciNormSqAlongFlow] using h_full
      rw [h_dt]
      ring)

end TracefreeRicciNormHeatFromContractionCalculus

end SyntheticTensor
