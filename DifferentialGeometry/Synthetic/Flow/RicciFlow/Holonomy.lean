import DifferentialGeometry.Synthetic.Geometry.Holonomy
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Basic

/-!
# Time-indexed holonomy family

Given a time-dependent connection `conn_fam : Time → V → V → V` (with per-time
axiom families), we get a family of restricted/full holonomy Lie algebras, one
for each `s : Time`. This file is a purely definitional wrapper around the
spatial definitions in `Synthetic/Geometry/Holonomy.lean`, mirroring the way
`Rm_tensor`/`ricciForm_tensor` in `Flow/RicciFlow/Basic.lean` wrap the spatial
`Rm`/`ricciForm`.

The genuine time-dependent content — invariance of holonomy under Ricci flow,
i.e. Kotschwar's Theorem 5.1 — will live in `Evolution/Holonomy.lean` once the
PDE toolkit (Laplacian / backwards-uniqueness) is in place.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open SyntheticTensor

namespace Synthetic

section HolonomyFam

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Restricted holonomy algebra at each time `s`. -/
noncomputable def restrictedHolonomyAlgebra_fam
    (emb : DerivationEmbedding k R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) =
      (emb.embed X) f • Y + f • conn_fam s X Y) :
    Time → LieSubalgebra R (Module.End R V) :=
  fun s => restrictedHolonomyAlgebra emb (conn_fam s)
    (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s)

/-- Full (Ambrose–Singer) holonomy algebra at each time `s`. -/
noncomputable def holonomyAlgebra_fam
    (emb : DerivationEmbedding k R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) =
      (emb.embed X) f • Y + f • conn_fam s X Y) :
    Time → LieSubalgebra R (Module.End R V) :=
  fun s => holonomyAlgebra emb (conn_fam s)
    (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s)

@[simp] theorem restrictedHolonomyAlgebra_fam_apply
    (emb : DerivationEmbedding k R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) =
      (emb.embed X) f • Y + f • conn_fam s X Y) (s : Time) :
    restrictedHolonomyAlgebra_fam emb conn_fam ha_fam hal_fam hsl_fam hl_fam s =
      restrictedHolonomyAlgebra emb (conn_fam s)
        (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) := rfl

@[simp] theorem holonomyAlgebra_fam_apply
    (emb : DerivationEmbedding k R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) =
      (emb.embed X) f • Y + f • conn_fam s X Y) (s : Time) :
    holonomyAlgebra_fam emb conn_fam ha_fam hal_fam hsl_fam hl_fam s =
      holonomyAlgebra emb (conn_fam s)
        (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) := rfl

/-- The restricted holonomy inclusion is preserved per time. -/
theorem restrictedHolonomyAlgebra_fam_le_holonomyAlgebra_fam
    (emb : DerivationEmbedding k R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) =
      (emb.embed X) f • Y + f • conn_fam s X Y) (s : Time) :
    restrictedHolonomyAlgebra_fam emb conn_fam ha_fam hal_fam hsl_fam hl_fam s ≤
      holonomyAlgebra_fam emb conn_fam ha_fam hal_fam hsl_fam hl_fam s := by
  apply LieSubalgebra.lieSpan_le.mpr
  rintro _ ⟨⟨A, B⟩, rfl⟩
  exact LieSubalgebra.subset_lieSpan
    (IteratedCurvatureEndo.curvature (emb := emb) (conn := conn_fam s)
      (ha := ha_fam s) (hal := hal_fam s) (hsl := hsl_fam s) (hl := hl_fam s) A B)

end HolonomyFam

-- ============================================================
-- Per-time skew-adjoint corollaries from a metric-compatible family
-- ============================================================

section SkewAdjointFam

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Per-time skew-adjoint for the restricted holonomy family. -/
theorem restrictedHolonomy_fam_skew_adjoint
    (emb : DerivationEmbedding k R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) =
      (emb.embed X) f • Y + f • conn_fam s X Y)
    (g_fam : Time → MetricDuality R V)
    (h_mc_fam : ∀ s, IsMetricCompatible emb (conn_fam s) (g_fam s))
    (s : Time) (L : Module.End R V)
    (hL : L ∈ restrictedHolonomyAlgebra_fam emb conn_fam ha_fam hal_fam hsl_fam hl_fam s)
    (X Y : V) :
    (g_fam s).g (L X) Y + (g_fam s).g X (L Y) = 0 :=
  restrictedHolonomy_skew_adjoint emb (conn_fam s)
    (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s)
    (g_fam s) (h_mc_fam s) L hL X Y

/-- Per-time skew-adjoint for the full holonomy family (Kotschwar Remark 5.2). -/
theorem holonomy_fam_skew_adjoint
    (emb : DerivationEmbedding k R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) =
      (emb.embed X) f • Y + f • conn_fam s X Y)
    (g_fam : Time → MetricDuality R V)
    (h_mc_fam : ∀ s, IsMetricCompatible emb (conn_fam s) (g_fam s))
    (s : Time) (L : Module.End R V)
    (hL : L ∈ holonomyAlgebra_fam emb conn_fam ha_fam hal_fam hsl_fam hl_fam s)
    (X Y : V) :
    (g_fam s).g (L X) Y + (g_fam s).g X (L Y) = 0 :=
  holonomy_skew_adjoint emb (conn_fam s)
    (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s)
    (g_fam s) (h_mc_fam s) L hL X Y

end SkewAdjointFam

-- ============================================================
-- Specializations to `IsRicciFlow`
-- ============================================================

section RicciFlow

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Under Ricci flow, holonomy is valued in `𝔰𝔬(V, g_t)` at every time. -/
theorem IsRicciFlow.holonomy_skew_adjoint
    {emb : DerivationEmbedding k R V}
    {td : TimeDerivativeData R A Time} [TimeRegularFam td]
    {atr : AbstractTrace R V}
    {g_fam : Time → MetricDuality R V}
    {h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs)}
    {conn_fam : Time → V → V → V}
    {ha_fam hal_fam hsl_fam hl_fam}
    (h : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (s : Time) (L : Module.End R V)
    (hL : L ∈ holonomyAlgebra_fam emb conn_fam ha_fam hal_fam hsl_fam hl_fam s)
    (X Y : V) :
    (g_fam s).g (L X) Y + (g_fam s).g X (L Y) = 0 :=
  holonomy_fam_skew_adjoint emb conn_fam ha_fam hal_fam hsl_fam hl_fam
    g_fam (fun s' => h.metric_compat s') s L hL X Y

/-- Under Ricci flow, restricted holonomy is valued in `𝔰𝔬(V, g_t)` at every time. -/
theorem IsRicciFlow.restrictedHolonomy_skew_adjoint
    {emb : DerivationEmbedding k R V}
    {td : TimeDerivativeData R A Time} [TimeRegularFam td]
    {atr : AbstractTrace R V}
    {g_fam : Time → MetricDuality R V}
    {h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs)}
    {conn_fam : Time → V → V → V}
    {ha_fam hal_fam hsl_fam hl_fam}
    (h : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (s : Time) (L : Module.End R V)
    (hL : L ∈ restrictedHolonomyAlgebra_fam emb conn_fam ha_fam hal_fam hsl_fam hl_fam s)
    (X Y : V) :
    (g_fam s).g (L X) Y + (g_fam s).g X (L Y) = 0 :=
  restrictedHolonomy_fam_skew_adjoint emb conn_fam ha_fam hal_fam hsl_fam hl_fam
    g_fam (fun s' => h.metric_compat s') s L hL X Y

end RicciFlow

end Synthetic
