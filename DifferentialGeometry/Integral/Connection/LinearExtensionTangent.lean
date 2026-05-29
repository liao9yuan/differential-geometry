import DifferentialGeometry.Integral.Connection.Curvature
import DifferentialGeometry.Integral.Connection.RicciIdentitySmoothFrame
import DifferentialGeometry.Integral.Connection.RiemannianFiberNormSq
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# A controlled linear smooth extension of a single tangent vector

For a smooth Riemannian metric `g` on the tangent bundle of `M`, a base point `x : M`, and a
fibre vector `w : TangentSpace I x`, this file builds a tangent-bundle section
`linearExtensionTangent x w : Π b : M, TangentSpace I b` with:

* `linearExtensionTangent x w x = w` (it extends `w`);
* `b ↦ linearExtensionTangent x w b` is `C^∞` as a tangent-bundle section;
* `w ↦ linearExtensionTangent x w` is `ℝ`-linear (`map_zero`, `map_smul`).

Unlike the choice-based `smoothExtensionTangent`, this extension is *controlled*: it is
the **chart-coordinate-constant** vector field built from `w`'s coordinate under the
tangent trivialization centred at `x`, cut off by a smooth bump supported in the chart
source.  Near `x` (where the bump equals `1`) the chart-trivialised representation is
literally the constant `w`-coordinate, so its chart-derivative vanishes; this is the
structural fact behind the covariant `1`-jet bound.

## Main definitions

* `coordExtensionTangent x w b` — the fibre value at `b` of the coordinate-constant field;
* `linearExtensionTangent x w` — the bump-cut-off coordinate-constant section.

## Main theorems

* `linearExtensionTangent_eq` — `linearExtensionTangent x w x = w`.
* `linearExtensionTangent_smooth` — `C^∞`-smoothness of the section.
* `linearExtensionTangent_map_zero`, `linearExtensionTangent_map_smul` — `ℝ`-linearity in `w`.
-/

noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The coordinate-constant vector field

The tangent trivialization centred at `x`, `triv := trivializationAt E (TangentSpace I) x`,
identifies the fibre `T_y M` with the model space `E` for `y` in its base set (which equals
`(chartAt H x).source`).  Reading off the `triv`-coordinate of `w` at `x` and re-injecting
that *constant* coordinate at every base point `y` produces the coordinate-constant field. -/

/-- The `triv`-coordinate of `w : T_x M` in the model space, where
`triv := trivializationAt E (TangentSpace I) x`. -/
def tangentCoord (x : M) (w : TangentSpace I x) : E :=
  (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x w

/-- `w ↦ tangentCoord x w` is `ℝ`-linear (it is the application of a continuous linear map). -/
@[simp] lemma tangentCoord_apply (x : M) (w : TangentSpace I x) :
    tangentCoord (I := I) x w =
      (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x w := rfl

lemma tangentCoord_zero (x : M) : tangentCoord (I := I) x 0 = 0 := by
  simp [tangentCoord]

lemma tangentCoord_smul (x : M) (c : ℝ) (w : TangentSpace I x) :
    tangentCoord (I := I) x (c • w) = c • tangentCoord (I := I) x w := by
  simp [tangentCoord]

/-- The fibre value at `b` of the coordinate-constant field attached to `(x, w)`:
re-inject the constant model coordinate `tangentCoord x w` into the fibre `T_b M`
through the tangent trivialization centred at `x`. -/
def coordExtensionTangent (x : M) (w : TangentSpace I x) (b : M) : TangentSpace I b :=
  (trivializationAt E (TangentSpace I) x).symmL ℝ b (tangentCoord (I := I) x w)

@[simp] lemma coordExtensionTangent_apply (x : M) (w : TangentSpace I x) (b : M) :
    coordExtensionTangent (I := I) x w b =
      (trivializationAt E (TangentSpace I) x).symmL ℝ b (tangentCoord (I := I) x w) := rfl

/-- At the base point `x` the coordinate-constant field recovers `w` itself. -/
lemma coordExtensionTangent_self (x : M) (w : TangentSpace I x) :
    coordExtensionTangent (I := I) x w x = w := by
  classical
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  simp only [coordExtensionTangent_apply, tangentCoord_apply]
  exact (trivializationAt E (TangentSpace I) x).symmL_continuousLinearMapAt hx w

/-- `w ↦ coordExtensionTangent x w b` sends `0` to `0`. -/
lemma coordExtensionTangent_map_zero (x : M) (b : M) :
    coordExtensionTangent (I := I) x (0 : TangentSpace I x) b = 0 := by
  rw [coordExtensionTangent_apply, tangentCoord_zero, map_zero]

/-- `w ↦ coordExtensionTangent x w b` commutes with scalar multiplication. -/
lemma coordExtensionTangent_map_smul (x : M) (c : ℝ) (w : TangentSpace I x) (b : M) :
    coordExtensionTangent (I := I) x (c • w) b =
      c • coordExtensionTangent (I := I) x w b := by
  simp only [coordExtensionTangent_apply, tangentCoord_smul, map_smul]

/-! ## Smoothness of the coordinate-constant field on the chart source

The argument mirrors `chartBasisVec_contMDiffOn`: viewed as a section, the coordinate-constant
field has constant `triv`-coordinate `tangentCoord x w`, so it is smooth on the base set of the
trivialization. -/

/-- The coordinate-constant field, as a total-space section, is `C^∞` on the base set of the
trivialization at `x`. -/
lemma coordExtensionTangent_contMDiffOn (x : M) (w : TangentSpace I x) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (coordExtensionTangent (I := I) x w))
      (trivializationAt E (TangentSpace I) x).baseSet := by
  classical
  have hiff :=
    ((trivializationAt E (TangentSpace I) x)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞)
      (s := fun b => coordExtensionTangent (I := I) x w b)
  refine hiff.mpr ?_
  -- The `triv`-coordinate is the constant `tangentCoord x w` on the base set.
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun _ : M => tangentCoord (I := I) x w)
      (trivializationAt E (TangentSpace I) x).baseSet :=
    contMDiffOn_const
  refine hconst.congr ?_
  intro b hb
  -- `(triv ⟨b, coordExtensionTangent x w b⟩).2 = tangentCoord x w` on the base set.
  change (trivializationAt E (TangentSpace I) x
      ⟨b, coordExtensionTangent (I := I) x w b⟩).2 = tangentCoord (I := I) x w
  have happ :
      (trivializationAt E (TangentSpace I) x
        ⟨b, (trivializationAt E (TangentSpace I) x).symm b
          (tangentCoord (I := I) x w)⟩).2
        = tangentCoord (I := I) x w := by
    have h := (trivializationAt E (TangentSpace I) x).apply_mk_symm hb
      (tangentCoord (I := I) x w)
    simpa using congrArg Prod.snd h
  -- `symmL ℝ b v = symm b v` definitionally (the `toFun` field of `symmL`).
  simpa [coordExtensionTangent, Trivialization.symmL_apply] using happ

/-! ## The bump function and the controlled extension -/

/-- A choice of smooth bump function centred at `x`, used to cut off the coordinate-constant
field to a globally smooth section.  Its support lies in the chart source, and it equals `1`
on a neighbourhood of `x`. -/
def linExtBump (x : M) : SmoothBumpFunction I x :=
  Classical.arbitrary (SmoothBumpFunction I x)

/-- **The controlled linear tangent extension.** The coordinate-constant field attached to
`(x, w)` multiplied by a smooth bump centred at `x` whose support lies in the chart source.
It extends `w`, is `C^∞`, and is `ℝ`-linear in `w`. -/
def linearExtensionTangent (x : M) (w : TangentSpace I x) :
    Π b : M, TangentSpace I b :=
  fun b => (linExtBump (I := I) x : M → ℝ) b • coordExtensionTangent (I := I) x w b

@[simp] lemma linearExtensionTangent_apply (x : M) (w : TangentSpace I x) (b : M) :
    linearExtensionTangent (I := I) x w b =
      (linExtBump (I := I) x : M → ℝ) b • coordExtensionTangent (I := I) x w b := rfl

/-! ### The extension recovers `w` at the base point -/

/-- The bump equals `1` at its centre `x`. -/
lemma linExtBump_eq_one (x : M) : (linExtBump (I := I) x : M → ℝ) x = 1 :=
  (linExtBump (I := I) x).eq_one

/-- **Extension property:** `linearExtensionTangent x w x = w`. -/
theorem linearExtensionTangent_eq (x : M) (w : TangentSpace I x) :
    linearExtensionTangent (I := I) x w x = w := by
  rw [linearExtensionTangent_apply, linExtBump_eq_one, one_smul,
    coordExtensionTangent_self]

/-! ### `ℝ`-linearity in `w` -/

/-- **Homogeneity:** `linearExtensionTangent x 0 = 0`. -/
theorem linearExtensionTangent_map_zero (x : M) :
    linearExtensionTangent (I := I) x (0 : TangentSpace I x) = 0 := by
  funext b
  rw [linearExtensionTangent_apply, coordExtensionTangent_map_zero, smul_zero]
  rfl

/-- **Scalar homogeneity:** `linearExtensionTangent x (c • w) = c • linearExtensionTangent x w`. -/
theorem linearExtensionTangent_map_smul (x : M) (c : ℝ) (w : TangentSpace I x) :
    linearExtensionTangent (I := I) x (c • w) =
      c • linearExtensionTangent (I := I) x w := by
  funext b
  rw [Pi.smul_apply, linearExtensionTangent_apply, linearExtensionTangent_apply,
    coordExtensionTangent_map_smul, smul_comm]

/-! ### `C^∞` smoothness -/

/-- **Smoothness:** `b ↦ linearExtensionTangent x w b` is a `C^∞` tangent-bundle section. -/
theorem linearExtensionTangent_smooth [T2Space M] (x : M) (w : TangentSpace I x) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (linearExtensionTangent (I := I) x w)) := by
  classical
  set u : Set M := (chartAt H x).source with hu_def
  set ψ : M → ℝ := (linExtBump (I := I) x : M → ℝ) with hψ_def
  -- The bump is `C^∞` on `u`.
  have hψ_smooth : ContMDiffOn I 𝓘(ℝ) ∞ ψ u :=
    (linExtBump (I := I) x).contMDiff.contMDiffOn
  -- `u` is open.
  have hu_open : IsOpen u := (chartAt H x).open_source
  -- `tsupport ψ ⊆ u`.
  have hψ_tsupport : tsupport ψ ⊆ u :=
    (linExtBump (I := I) x).tsupport_subset_chartAt_source
  -- The coordinate-constant field is `C^∞` on `u` (= base set).
  have hs_smooth : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => coordExtensionTangent (I := I) x w b)) u := by
    rw [show u = (trivializationAt E (TangentSpace I) x).baseSet from rfl]
    exact coordExtensionTangent_contMDiffOn (I := I) x w
  -- Combine via `ContMDiffOn.smul_section_of_tsupport`.
  have h := ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (n := ∞)
    (V := TangentSpace I) hψ_smooth hu_open hψ_tsupport hs_smooth
  -- Identify `(ψ • coordExtensionTangent x w)` with `linearExtensionTangent x w`.
  have h_eq : (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
        (linearExtensionTangent (I := I) x w b)) =
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
        ((ψ • fun b' : M => coordExtensionTangent (I := I) x w b') b)) := by
    funext b
    change TotalSpace.mk' E b (linearExtensionTangent (I := I) x w b) =
      TotalSpace.mk' E b ((ψ b) • coordExtensionTangent (I := I) x w b)
    rw [linearExtensionTangent_apply]
  rw [h_eq]
  exact h

end Connection
end Integral
end DifferentialGeometry
