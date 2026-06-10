import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedSlotwiseCurvature
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.ParsevalFrameField

/-!
# Parseval-frame = orthonormal-frame conversion for the differentiated-curvature diagonal trace

The differentiated `(0, s)`-tensor curvature `nablaTensor0SCurv g s X Y Z A x = (∇_X R^{(s)})(Y, Z) A`
is the Leibniz-contracted covariant derivative of the tensor Riemann curvature: although the leading
term differentiates the smooth field `X`, the total four-term Leibniz combination is
*extension-independent* and hence depends on `X, Y` only through their point values `X x, Y x`, and is
moreover additive and `ℝ`-homogeneous in each (`nablaTensor0SCurv` is value-bilinear in its two leading
slots, the defining tensoriality of `nablaCurvSec` / `nablaRiemannSec`). Consequently the diagonal trace
`∑ nablaTensor0SCurv g s (·)(·) Z A x`, with the *same* frame vector in the derivation slot and the first
antisymmetric slot, is the metric trace of a fixed value-bilinear form on `T_x M` and is therefore
**frame-independent**: a `g_x`-Parseval family and a `g_x`-orthonormal frame produce the same diagonal
sum.

This file packages that value-bilinearity as the bilinear map `nablaTensor0SCurvBilin g s Z A hA x`
(`T_x M →ₗ[ℝ] T_x M →ₗ[ℝ] Tensor0SSpace s I x`) through `smooth-extension` evaluation, and converts the
diagonal frame sum from a Parseval frame to the centre-adapted orthonormal frame `smoothOrthoFrame g x`
through the abstract bilinear conversion `parseval_family_sum_bilin_eq`.

## Main results

* `nablaTensor0SCurvBilin` — the value-bilinear form `(v, w) ↦ (∇_{ext v} R^{(s)})(ext w, Z) A` on `T_x M`.
* `nablaTensor0SCurvBilin_apply_smooth` — its evaluation on point values of smooth fields equals
  `nablaTensor0SCurv g s X Y Z A x`.
* `parsevalFrame_eq_orthoFrame_diag_nablaTensor0SCurv` — **the conversion**: the Parseval-frame diagonal
  differentiated-curvature trace equals the orthonormal-frame diagonal trace.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

/-- Smoothness predicate for a raw `(0, s)`-tensor section: the total-space map is `C^∞`. -/
private abbrev TensorSmooth (s : ℕ) (A : Π b : M, Tensor0SSpace s I b) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
    (fun b => TotalSpace.mk' (Tensor0SModel s ℝ E)
      (E := fun z : M => Tensor0SSpace s I z) b (A b))

/-! ### The value-bilinearity of the differentiated tensor curvature in its two leading slots

The differentiated tensor curvature `nablaTensor0SCurv g s X Y Z A x` depends on `X, Y` only through
their point values `X x, Y x` and is additive and `ℝ`-homogeneous in each.  This is the defining
tensoriality of the Leibniz-contracted differentiated curvature `(∇_X R^{(s)})(Y, Z) A`: the four-term
Leibniz combination cancels the extension-dependence of the leading `∇_X(R(Y,Z)A)` term.

These four facts (well-definedness, additivity and homogeneity in each leading slot) are the genuine
mathematical content; they reduce, through the differentiated slot-wise transfer
`nablaTensorCov_baseSlot_eval` and the multilinearity of `Tensor0SSpace.toModel`, to the corresponding
value-bilinearity of the tangent-level differentiated base-slot curvature `nablaBaseSlotCurv`, i.e. of
`nablaCurvSec (LeviCivita g)` in its derivation slot `X` and its first antisymmetric slot `Y`. -/

/-- **Additivity of the tangent-level differentiated curvature `nablaCurvSec` in its derivation
slot.** For the Levi-Civita connection of `g` and smooth fields `X, X', Y, Z, W`,
`(∇_{X+X'} R)(Y, Z) W = (∇_X R)(Y, Z) W + (∇_{X'} R)(Y, Z) W`.  Each of the four Leibniz terms of
`nablaCurvSec` splits: the leading connection-derivative term is additive in `(X + X') x` as a
continuous-linear-map application, and the three correction terms split through the section additivity
of `covApply` in `X` followed by the slot-wise additivity of `riemannSec`
(`riemannSec_add_left/_add_right/_add_third`). -/
private lemma nablaCurvSec_add_left
    (g : SmoothRiemannianMetric I M)
    (X X' Y Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaCurvSec (LeviCivita (I := I) g) (fun b => (X + X') b) (fun b => Y b) (fun b => Z b)
        (fun b => W b) x =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
          (fun b => W b) x
        + nablaCurvSec (LeviCivita (I := I) g) (fun b => X' b) (fun b => Y b) (fun b => Z b)
            (fun b => W b) x := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  have hX := X.contMDiff; have hX' := X'.contMDiff; have hY := Y.contMDiff
  have hZ := Z.contMDiff; have hW := W.contMDiff
  have hXX' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b => (X + X') b)) := (X + X').contMDiff
  rw [nablaCurvSec_def, nablaCurvSec_def, nablaCurvSec_def]
  -- T1: the leading connection-derivative term, additive in `(X + X') x`.
  have h1 : cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b) x
        ((fun b => (X + X') b) x) =
      cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b) x (X x)
        + cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b) x
            (X' x) := by
    have : ((fun b => (X + X') b) x) = X x + X' x := by
      simp only [ContMDiffSection.coe_add, Pi.add_apply]
    rw [this, map_add]
  -- T2: derivation slot enters the first antisymmetric slot via `covApply cov (X+X') Y`.
  have hcovT2 : covApply cov (fun b => (X + X') b) (fun b => Y b) =
      covApply cov (fun b => X b) (fun b => Y b) + covApply cov (fun b => X' b) (fun b => Y b) := by
    funext b
    simp only [covApply, ContMDiffSection.coe_add, Pi.add_apply, map_add]
  have h2 : riemannSec cov (covApply cov (fun b => (X + X') b) (fun b => Y b)) (fun b => Z b)
        (fun b => W b) x =
      riemannSec cov (covApply cov (fun b => X b) (fun b => Y b)) (fun b => Z b) (fun b => W b) x
        + riemannSec cov (covApply cov (fun b => X' b) (fun b => Y b)) (fun b => Z b)
            (fun b => W b) x := by
    rw [hcovT2]
    exact riemannSec_add_left (cov := cov)
      ((covApply_contMDiff (cov := cov) hX hY x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hX' hY x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov)
        (covApply_contMDiff (cov := cov) hX hY) hW x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov)
        (covApply_contMDiff (cov := cov) hX' hY) hW x).mdifferentiableAt (by simp))
  -- T3: derivation slot enters the second antisymmetric slot via `covApply cov (X+X') Z`.
  have hcovT3 : covApply cov (fun b => (X + X') b) (fun b => Z b) =
      covApply cov (fun b => X b) (fun b => Z b) + covApply cov (fun b => X' b) (fun b => Z b) := by
    funext b
    simp only [covApply, ContMDiffSection.coe_add, Pi.add_apply, map_add]
  have h3 : riemannSec cov (fun b => Y b) (covApply cov (fun b => (X + X') b) (fun b => Z b))
        (fun b => W b) x =
      riemannSec cov (fun b => Y b) (covApply cov (fun b => X b) (fun b => Z b)) (fun b => W b) x
        + riemannSec cov (fun b => Y b) (covApply cov (fun b => X' b) (fun b => Z b))
            (fun b => W b) x := by
    rw [hcovT3]
    exact riemannSec_add_right (cov := cov)
      ((covApply_contMDiff (cov := cov) hX hZ x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hX' hZ x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov)
        (covApply_contMDiff (cov := cov) hX hZ) hW x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov)
        (covApply_contMDiff (cov := cov) hX' hZ) hW x).mdifferentiableAt (by simp))
  -- T4: derivation slot enters the section slot via `covApply cov (X+X') W`.
  have hcovT4 : covApply cov (fun b => (X + X') b) (fun b => W b) =
      covApply cov (fun b => X b) (fun b => W b) + covApply cov (fun b => X' b) (fun b => W b) := by
    funext b
    simp only [covApply, ContMDiffSection.coe_add, Pi.add_apply, map_add]
  have hcXW := covApply_contMDiff (cov := cov) hX hW
  have hcX'W := covApply_contMDiff (cov := cov) hX' hW
  have h4 : riemannSec cov (fun b => Y b) (fun b => Z b)
        (covApply cov (fun b => (X + X') b) (fun b => W b)) x =
      riemannSec cov (fun b => Y b) (fun b => Z b) (covApply cov (fun b => X b) (fun b => W b)) x
        + riemannSec cov (fun b => Y b) (fun b => Z b)
            (covApply cov (fun b => X' b) (fun b => W b)) x := by
    rw [hcovT4]
    exact riemannSec_add_third (cov := cov)
      (Filter.Eventually.of_forall (fun b => (hcXW b).mdifferentiableAt (by simp)))
      (Filter.Eventually.of_forall (fun b => (hcX'W b).mdifferentiableAt (by simp)))
      ((covApply_contMDiff (cov := cov) hZ hcXW x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hZ hcX'W x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hZ (hcXW.add_section hcX'W) x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY hcXW x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY hcX'W x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY (hcXW.add_section hcX'W) x).mdifferentiableAt (by simp))
  rw [h1, h2, h3, h4]
  abel

/-- **`C^∞(M)`-linearity of the tangent-level differentiated curvature `nablaCurvSec` in its derivation
slot.** For the Levi-Civita connection of `g`, a smooth function `f`, and smooth fields `X, Y, Z, W`,
`(∇_{f·X} R)(Y, Z) W = f · (∇_X R)(Y, Z) W`.  Crucially there is **no `df`-correction**: the derivation
direction `f·X` enters each of the four Leibniz terms only *linearly* (never differentiated), so
`covApply cov (f·X) · = f · covApply cov X ·` cleanly, and the genuine-tensor `riemannSec`-slot
homogeneities `riemannSec_smul_left/_right/_third` (each itself `df`-free, the Riemann curvature being a
tensor) scale every term by `f x`. -/
private lemma nablaCurvSec_smul_left
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaCurvSec (LeviCivita (I := I) g) (f • fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => W b) x =
      f x • nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => W b) x := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  have hX := X.contMDiff; have hY := Y.contMDiff
  have hZ := Z.contMDiff; have hW := W.contMDiff
  have hfx : MDiffAt f x := (hf x).mdifferentiableAt (by simp)
  rw [nablaCurvSec_def, nablaCurvSec_def]
  -- T1: the leading connection-derivative term scales by `f x` (direction scaled, never differentiated).
  have h1 : cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b) x
        ((f • fun b => X b) x) =
      f x • cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b) x
            (X x) := by
    have hval : (f • fun b => X b) x = f x • X x := rfl
    rw [hval, map_smul]
  -- The derivation direction enters each correction slot linearly: `covApply cov (f•X) · = f • covApply cov X ·`.
  have hcovT2 : covApply cov (f • fun b => X b) (fun b => Y b) =
      f • covApply cov (fun b => X b) (fun b => Y b) := by
    funext b
    change cov.toFun (fun b => Y b) b ((f • fun b => X b) b) =
      f b • cov.toFun (fun b => Y b) b (X b)
    rw [show (f • fun b => X b) b = f b • X b from rfl, map_smul]
  have hcovT3 : covApply cov (f • fun b => X b) (fun b => Z b) =
      f • covApply cov (fun b => X b) (fun b => Z b) := by
    funext b
    change cov.toFun (fun b => Z b) b ((f • fun b => X b) b) =
      f b • cov.toFun (fun b => Z b) b (X b)
    rw [show (f • fun b => X b) b = f b • X b from rfl, map_smul]
  have hcovT4 : covApply cov (f • fun b => X b) (fun b => W b) =
      f • covApply cov (fun b => X b) (fun b => W b) := by
    funext b
    change cov.toFun (fun b => W b) b ((f • fun b => X b) b) =
      f b • cov.toFun (fun b => W b) b (X b)
    rw [show (f • fun b => X b) b = f b • X b from rfl, map_smul]
  -- T2: first antisymmetric slot scaled, `riemannSec_smul_left` (no `df`).
  have h2 : riemannSec cov (covApply cov (f • fun b => X b) (fun b => Y b)) (fun b => Z b)
        (fun b => W b) x =
      f x • riemannSec cov (covApply cov (fun b => X b) (fun b => Y b)) (fun b => Z b)
            (fun b => W b) x := by
    rw [hcovT2]
    exact riemannSec_smul_left (cov := cov) hfx
      ((covApply_contMDiff (cov := cov) hX hY x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov)
        (covApply_contMDiff (cov := cov) hX hY) hW x).mdifferentiableAt (by simp))
  -- T3: second antisymmetric slot scaled, `riemannSec_smul_right` (no `df`).
  have h3 : riemannSec cov (fun b => Y b) (covApply cov (f • fun b => X b) (fun b => Z b))
        (fun b => W b) x =
      f x • riemannSec cov (fun b => Y b) (covApply cov (fun b => X b) (fun b => Z b))
            (fun b => W b) x := by
    rw [hcovT3]
    exact riemannSec_smul_right (cov := cov) hfx
      ((covApply_contMDiff (cov := cov) hX hZ x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov)
        (covApply_contMDiff (cov := cov) hX hZ) hW x).mdifferentiableAt (by simp))
  -- T4: section slot scaled. Read both sides through the bundled value-trilinear form `riemannOp`
  -- (`riemannOp_apply_smooth`), where the third (fibre) slot is a continuous-linear map, hence scales
  -- by `f x` (`.map_smul`) with no `df`-correction (the Riemann curvature is a tensor in all slots).
  have hcXW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov (fun b => X b) (fun b => W b))) :=
    covApply_contMDiff (cov := cov) hX hW
  have hfcXW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (f • covApply cov (fun b => X b) (fun b => W b))) :=
    hf.smul_section hcXW
  have h4 : riemannSec cov (fun b => Y b) (fun b => Z b)
        (covApply cov (f • fun b => X b) (fun b => W b)) x =
      f x • riemannSec cov (fun b => Y b) (fun b => Z b)
            (covApply cov (fun b => X b) (fun b => W b)) x := by
    rw [hcovT4]
    rw [← riemannOp_apply_smooth (cov := cov) hY hZ hfcXW,
        ← riemannOp_apply_smooth (cov := cov) hY hZ hcXW]
    rw [show (f • covApply cov (fun b => X b) (fun b => W b)) x =
        f x • (covApply cov (fun b => X b) (fun b => W b)) x from rfl]
    rw [map_smul]
  rw [h1, h2, h3, h4]
  simp only [smul_sub]

/-- **Additivity of the tangent-level differentiated curvature `nablaCurvSec` in its first antisymmetric
slot.** For the Levi-Civita connection of `g` and smooth fields `X, Y, Y', Z, W`,
`(∇_X R)(Y + Y', Z) W = (∇_X R)(Y, Z) W + (∇_X R)(Y', Z) W`.  The first antisymmetric slot enters the
curvature section of the leading term and the first slot of the three correction-curvatures; each splits
through the slot-additivity of `riemannSec` (`riemannSec_add_left`) and the section additivity of the
connection. -/
private lemma nablaCurvSec_add_right
    (g : SmoothRiemannianMetric I M)
    (X Y Y' Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => (Y + Y') b) (fun b => Z b)
        (fun b => W b) x =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
          (fun b => W b) x
        + nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y' b) (fun b => Z b)
            (fun b => W b) x := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  have hX := X.contMDiff; have hY := Y.contMDiff; have hY' := Y'.contMDiff
  have hZ := Z.contMDiff; have hW := W.contMDiff
  rw [nablaCurvSec_def, nablaCurvSec_def, nablaCurvSec_def]
  -- T1: the curvature section `R(Y+Y', Z) W` splits in its first slot (section equality), then `cov.toFun`.
  have hsecYY' : (fun b => riemannSec cov (fun b => (Y + Y') b) (fun b => Z b) (fun b => W b) b) =
      (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b)
        + (fun b => riemannSec cov (fun b => Y' b) (fun b => Z b) (fun b => W b) b) := by
    funext b
    have heq : (fun b => (Y + Y') b) = (fun b => Y b) + (fun b => Y' b) := by
      funext b; simp only [ContMDiffSection.coe_add, Pi.add_apply]
    rw [heq]
    simp only [Pi.add_apply]
    exact riemannSec_add_left (cov := cov) ((hY b).mdifferentiableAt (by simp))
      ((hY' b).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY hW b).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY' hW b).mdifferentiableAt (by simp))
  have hRYsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b)) :=
    riemannSec_contMDiff (cov := cov) hY hZ hW
  have hRY'sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => riemannSec cov (fun b => Y' b) (fun b => Z b) (fun b => W b) b)) :=
    riemannSec_contMDiff (cov := cov) hY' hZ hW
  have h1 : cov.toFun (fun b => riemannSec cov (fun b => (Y + Y') b) (fun b => Z b) (fun b => W b) b)
        x (X x) =
      cov.toFun (fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b) x (X x)
        + cov.toFun (fun b => riemannSec cov (fun b => Y' b) (fun b => Z b) (fun b => W b) b) x
            (X x) := by
    rw [hsecYY', cov.isCovariantDerivativeOnUniv.add (hRYsm.mdifferentiableAt (by simp))
      (hRY'sm.mdifferentiableAt (by simp))]
    rfl
  -- T2: `covApply cov X (Y+Y')` splits in its section slot.
  have hcovT2 : covApply cov (fun b => X b) (fun b => (Y + Y') b) =
      covApply cov (fun b => X b) (fun b => Y b) + covApply cov (fun b => X b) (fun b => Y' b) := by
    funext b
    change cov.toFun (fun b => (Y + Y') b) b (X b) =
      cov.toFun (fun b => Y b) b (X b) + cov.toFun (fun b => Y' b) b (X b)
    have heq : (fun b => (Y + Y') b) = (fun b => Y b) + (fun b => Y' b) := by
      funext b; simp only [ContMDiffSection.coe_add, Pi.add_apply]
    rw [heq, cov.isCovariantDerivativeOnUniv.add ((hY b).mdifferentiableAt (by simp))
      ((hY' b).mdifferentiableAt (by simp))]
    rfl
  have h2 : riemannSec cov (covApply cov (fun b => X b) (fun b => (Y + Y') b)) (fun b => Z b)
        (fun b => W b) x =
      riemannSec cov (covApply cov (fun b => X b) (fun b => Y b)) (fun b => Z b) (fun b => W b) x
        + riemannSec cov (covApply cov (fun b => X b) (fun b => Y' b)) (fun b => Z b)
            (fun b => W b) x := by
    rw [hcovT2]
    exact riemannSec_add_left (cov := cov)
      ((covApply_contMDiff (cov := cov) hX hY x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hX hY' x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov)
        (covApply_contMDiff (cov := cov) hX hY) hW x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov)
        (covApply_contMDiff (cov := cov) hX hY') hW x).mdifferentiableAt (by simp))
  -- T3: first antisymmetric slot of the second correction-curvature.
  have h3 : riemannSec cov (fun b => (Y + Y') b) (covApply cov (fun b => X b) (fun b => Z b))
        (fun b => W b) x =
      riemannSec cov (fun b => Y b) (covApply cov (fun b => X b) (fun b => Z b)) (fun b => W b) x
        + riemannSec cov (fun b => Y' b) (covApply cov (fun b => X b) (fun b => Z b))
            (fun b => W b) x := by
    have heq : (fun b => (Y + Y') b) = (fun b => Y b) + (fun b => Y' b) := by
      funext b; simp only [ContMDiffSection.coe_add, Pi.add_apply]
    rw [heq]
    exact riemannSec_add_left (cov := cov) ((hY x).mdifferentiableAt (by simp))
      ((hY' x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY hW x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY' hW x).mdifferentiableAt (by simp))
  -- T4: first antisymmetric slot of the third correction-curvature.
  have hcXZ := covApply_contMDiff (cov := cov) hX hZ
  have h4 : riemannSec cov (fun b => (Y + Y') b) (fun b => Z b)
        (covApply cov (fun b => X b) (fun b => W b)) x =
      riemannSec cov (fun b => Y b) (fun b => Z b) (covApply cov (fun b => X b) (fun b => W b)) x
        + riemannSec cov (fun b => Y' b) (fun b => Z b)
            (covApply cov (fun b => X b) (fun b => W b)) x := by
    have heq : (fun b => (Y + Y') b) = (fun b => Y b) + (fun b => Y' b) := by
      funext b; simp only [ContMDiffSection.coe_add, Pi.add_apply]
    have hcXW := covApply_contMDiff (cov := cov) hX hW
    rw [heq]
    exact riemannSec_add_left (cov := cov) ((hY x).mdifferentiableAt (by simp))
      ((hY' x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY hcXW x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY' hcXW x).mdifferentiableAt (by simp))
  rw [h1, h2, h3, h4]
  abel

/-- Smoothness of `b ↦ extDerivFun f b (X b)` for a smooth function `f` and a smooth tangent section
`X`, as the second component of the composed tangent map `b ↦ Tf(b, X b)`. -/
private lemma extDerivFun_apply_smooth_aux
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {X : Π b : M, TangentSpace I b} (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b => extDerivFun f b (X b)) := by
  classical
  have htan : ContMDiff I.tangent (𝓘(ℝ, ℝ).tangent) ∞ (tangentMap I 𝓘(ℝ, ℝ) f) := by
    have h₁ : ContMDiff I 𝓘(ℝ, ℝ) ((∞ : WithTop ℕ∞) + 1) f := by simpa using hf
    exact h₁.contMDiff_tangentMap (le_refl _)
  have hXsec : ContMDiff I I.tangent ∞
      (fun b => (TotalSpace.mk' E b (X b) : TangentBundle I M)) := hX
  have hcomp : ContMDiff I (𝓘(ℝ, ℝ).tangent) ∞
      (fun b => tangentMap I 𝓘(ℝ, ℝ) f (TotalSpace.mk' E b (X b))) :=
    htan.comp hXsec
  have hsnd : ContMDiff (𝓘(ℝ, ℝ).tangent) 𝓘(ℝ, ℝ) ∞
      (fun p : TangentBundle 𝓘(ℝ, ℝ) ℝ => p.2) := contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)
  have hresult : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b => (tangentMap I 𝓘(ℝ, ℝ) f (TotalSpace.mk' E b (X b))).2) :=
    hsnd.comp hcomp
  refine hresult.congr fun b => ?_
  simp [extDerivFun, tangentMap_snd, NormedSpace.fromTangentSpace]

/-- **`C^∞(M)`-linearity of the tangent-level differentiated curvature `nablaCurvSec` in its first
antisymmetric slot.** For the Levi-Civita connection of `g`, a smooth function `f`, and smooth fields
`X, Y, Z, W`, `(∇_X R)(f·Y, Z) W = f · (∇_X R)(Y, Z) W`.  Unlike the derivation slot, the first
antisymmetric slot *is* differentiated, so two `df`-corrections arise — one from the leading term
(`∇_X(f · R(Y,Z)W)`) and one from the first-correction term (`R(∇_X(f·Y), Z) W`, whose inner
`∇_X(f·Y) = f·∇_X Y + (df·X)·Y` Leibniz produces `(df·X) · R(Y,Z)W`); they appear with opposite signs
in the four-term Leibniz formula and cancel exactly, the remaining terms scaling by `f x` through the
genuine-tensor `riemannSec`-slot homogeneity `riemannSec_smul_left`. -/
private lemma nablaCurvSec_smul_right
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (f • fun b => Y b) (fun b => Z b)
        (fun b => W b) x =
      f x • nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => W b) x := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  have hX := X.contMDiff; have hY := Y.contMDiff
  have hZ := Z.contMDiff; have hW := W.contMDiff
  have hfx : MDiffAt f x := (hf x).mdifferentiableAt (by simp)
  set R : Π b : M, TangentSpace I b :=
    fun b => riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b with hR
  have hRsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% R) :=
    riemannSec_contMDiff (cov := cov) hY hZ hW
  rw [nablaCurvSec_def, nablaCurvSec_def]
  -- T1: leading term. `R(f•Y, Z) W = f • R(Y, Z) W` (section), then the connection Leibniz produces
  -- the `df`-correction `extDerivFun f x (X x) • R x`.
  have hsecfY : (fun b => riemannSec cov (f • fun b => Y b) (fun b => Z b) (fun b => W b) b) =
      f • R := by
    funext b
    change riemannSec cov (f • fun b => Y b) (fun b => Z b) (fun b => W b) b =
      f b • riemannSec cov (fun b => Y b) (fun b => Z b) (fun b => W b) b
    exact riemannSec_smul_left (cov := cov) ((hf b).mdifferentiableAt (by simp))
      ((hY b).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY hW b).mdifferentiableAt (by simp))
  have h1 : cov.toFun (fun b => riemannSec cov (f • fun b => Y b) (fun b => Z b) (fun b => W b) b)
        x (X x) =
      f x • cov.toFun R x (X x) + extDerivFun f x (X x) • R x := by
    rw [hsecfY, cov.isCovariantDerivativeOnUniv.leibniz (hRsm.mdifferentiableAt (by simp)) hfx]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]
  -- T2: `∇_X(f•Y) = f•∇_X Y + (df·X)•Y` (section), splits into the scaled term plus the `df`-correction.
  set Xf : M → ℝ := fun b => extDerivFun f b (X b) with hXf
  have hcovfY : covApply cov (fun b => X b) (f • fun b => Y b) =
      f • covApply cov (fun b => X b) (fun b => Y b) + Xf • (fun b => Y b) := by
    funext b
    change cov.toFun (f • fun b => Y b) b (X b) =
      (f • covApply cov (fun b => X b) (fun b => Y b)) b + (Xf • fun b => Y b) b
    rw [cov.isCovariantDerivativeOnUniv.leibniz ((hY b).mdifferentiableAt (by simp))
      ((hf b).mdifferentiableAt (by simp))]
    simp [covApply, Xf, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hXfsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ Xf := extDerivFun_apply_smooth_aux hf hX
  have hcXY := covApply_contMDiff (cov := cov) hX hY
  have h2 : riemannSec cov (covApply cov (fun b => X b) (f • fun b => Y b)) (fun b => Z b)
        (fun b => W b) x =
      f x • riemannSec cov (covApply cov (fun b => X b) (fun b => Y b)) (fun b => Z b)
            (fun b => W b) x
        + extDerivFun f x (X x) • R x := by
    rw [hcovfY]
    rw [riemannSec_add_left (cov := cov)
      ((hf.smul_section hcXY x).mdifferentiableAt (by simp))
      ((hXfsm.smul_section hY x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) (hf.smul_section hcXY) hW x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) (hXfsm.smul_section hY) hW x).mdifferentiableAt (by simp))]
    rw [show (f • covApply cov (fun b => X b) (fun b => Y b)) =
        f • covApply cov (fun b => X b) (fun b => Y b) from rfl]
    rw [riemannSec_smul_left (cov := cov) hfx
        ((covApply_contMDiff (cov := cov) hX hY x).mdifferentiableAt (by simp))
        ((covApply_contMDiff (cov := cov)
          (covApply_contMDiff (cov := cov) hX hY) hW x).mdifferentiableAt (by simp))]
    rw [riemannSec_smul_left (cov := cov) ((hXfsm x).mdifferentiableAt (by simp))
        ((hY x).mdifferentiableAt (by simp))
        ((covApply_contMDiff (cov := cov) hY hW x).mdifferentiableAt (by simp))]
  -- T3, T4: clean slot-1 homogeneity (no `df`).
  have h3 : riemannSec cov (f • fun b => Y b) (covApply cov (fun b => X b) (fun b => Z b))
        (fun b => W b) x =
      f x • riemannSec cov (fun b => Y b) (covApply cov (fun b => X b) (fun b => Z b))
            (fun b => W b) x :=
    riemannSec_smul_left (cov := cov) hfx ((hY x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY hW x).mdifferentiableAt (by simp))
  have hcXW := covApply_contMDiff (cov := cov) hX hW
  have h4 : riemannSec cov (f • fun b => Y b) (fun b => Z b)
        (covApply cov (fun b => X b) (fun b => W b)) x =
      f x • riemannSec cov (fun b => Y b) (fun b => Z b)
            (covApply cov (fun b => X b) (fun b => W b)) x :=
    riemannSec_smul_left (cov := cov) hfx ((hY x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov) hY hcXW x).mdifferentiableAt (by simp))
  rw [h1, h2, h3, h4]
  simp only [hR]
  module

/-- Additivity of the differentiated base-slot curvature `nablaBaseSlotCurv` in its derivation slot,
read from `nablaCurvSec_add_left` through the definitional `nablaBaseSlotCurv_eq_nablaCurvSec`. -/
private lemma nablaBaseSlotCurv_add_left
    (g : SmoothRiemannianMetric I M)
    (X X' Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g (X + X') Y Z x u =
      nablaBaseSlotCurv (I := I) g X Y Z x u + nablaBaseSlotCurv (I := I) g X' Y Z x u := by
  rw [nablaBaseSlotCurv_eq_nablaCurvSec, nablaBaseSlotCurv_eq_nablaCurvSec,
      nablaBaseSlotCurv_eq_nablaCurvSec]
  exact nablaCurvSec_add_left (g := g) X X' Y Z
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u)) x

/-- `ℝ`-homogeneity of the differentiated base-slot curvature `nablaBaseSlotCurv` in its derivation
slot (constant scalar), read from `nablaCurvSec_smul_left` (with `f` the constant `c`) through
`nablaBaseSlotCurv_eq_nablaCurvSec`. -/
private lemma nablaBaseSlotCurv_smul_left
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g (c • X) Y Z x u =
      c • nablaBaseSlotCurv (I := I) g X Y Z x u := by
  rw [nablaBaseSlotCurv_eq_nablaCurvSec, nablaBaseSlotCurv_eq_nablaCurvSec]
  have hconst : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
  have hsmul := nablaCurvSec_smul_left (g := g) hconst X Y Z
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u)) x
  have hcoe : ((fun _ : M => c) • fun b => X b) = (fun b => (c • X) b) := rfl
  rw [hcoe] at hsmul
  exact hsmul

/-- `ℝ`-homogeneity of `nablaBaseSlotCurv` in its first antisymmetric slot (constant scalar), read from
`nablaCurvSec_smul_right` (with `f` the constant `c`) through `nablaBaseSlotCurv_eq_nablaCurvSec`. -/
private lemma nablaBaseSlotCurv_smul_right
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X (c • Y) Z x u =
      c • nablaBaseSlotCurv (I := I) g X Y Z x u := by
  rw [nablaBaseSlotCurv_eq_nablaCurvSec, nablaBaseSlotCurv_eq_nablaCurvSec]
  have hconst : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
  have hsmul := nablaCurvSec_smul_right (g := g) hconst X Y Z
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u)) x
  have hcoe : ((fun _ : M => c) • fun b => Y b) = (fun b => (c • Y) b) := rfl
  rw [hcoe] at hsmul
  exact hsmul

/-- Additivity of `nablaBaseSlotCurv` in its first antisymmetric slot, read from
`nablaCurvSec_add_right` through `nablaBaseSlotCurv_eq_nablaCurvSec`. -/
private lemma nablaBaseSlotCurv_add_right
    (g : SmoothRiemannianMetric I M)
    (X Y Y' Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X (Y + Y') Z x u =
      nablaBaseSlotCurv (I := I) g X Y Z x u + nablaBaseSlotCurv (I := I) g X Y' Z x u := by
  rw [nablaBaseSlotCurv_eq_nablaCurvSec, nablaBaseSlotCurv_eq_nablaCurvSec,
      nablaBaseSlotCurv_eq_nablaCurvSec]
  exact nablaCurvSec_add_right (g := g) X Y Y' Z
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u)) x

/-- **Well-definedness of the differentiated tensor curvature in its two leading slots, modulo pointwise
agreement at `x`** (posited deep leaf; the body is `sorry`). For smooth fields `X, X', Y, Y'` with
`X x = X' x` and `Y x = Y' x`, the values of `nablaTensor0SCurv` at `x` coincide: the four-term Leibniz
combination `(∇_X R^{(s)})(Y, Z) A` is the genuine differentiated curvature *tensor*, so it is
extension-independent in `X, Y` and depends on them only through `X x, Y x`.

This is the value-determination half of the tensoriality of `(∇R)^{(s)}` in its two leading slots; it
is independent of (and not derivable from) the value-additivity and `ℝ`-homogeneity proved above
(`nablaTensor0SCurv_add_left/_smul_left/_add_mid/_smul_mid`, together with the full `nablaCurvSec`
value-bilinearity `nablaCurvSec_add_left/_smul_left/_add_right/_smul_right`). The standard
value-determination route — Mathlib's `TensorialAt.pointwise`, a local-frame expansion with a bump
cutoff — is unavailable here: `TensorialAt` demands the tensoriality fields hold for sections merely
`MDifferentiableAt x`, but `nablaCurvSec` is a *second-order* operator (its `∇_X(R(Y,Z)A)` term and the
inner `∇_X A` correction each differentiate a section once *more*), so its value at `x` requires the
field to be `C^1` in a neighbourhood, not just differentiable at `x`. Discharging this leaf needs the
value-determination of the differentiated *bundle* curvature `nablaRiemannSec` as a genuine bundle map
(a localization staying within `C^∞` sections), which is missing from the library. -/
theorem nablaTensor0SCurv_eq_of_pointwise_eq_leftMid
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X X' Y Y' Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A)
    (x : M) (hX_eq : X x = X' x) (hY_eq : Y x = Y' x) :
    nablaTensor0SCurv (I := I) g s X Y Z A x = nablaTensor0SCurv (I := I) g s X' Y' Z A x := by
  sorry

/-- **Additivity of the differentiated tensor curvature in its derivation slot.** For smooth fields
`X, X', Y, Z` whose first slot is the sum `X + X'`, the differentiated tensor curvature splits
additively: `(∇_{X+X'} R^{(s)})(Y, Z) A = (∇_X R^{(s)})(Y, Z) A + (∇_{X'} R^{(s)})(Y, Z) A`.  This is
the additivity in `X x` of the value-bilinear differentiated curvature. -/
theorem nablaTensor0SCurv_add_left
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X X' Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A) (x : M) :
    nablaTensor0SCurv (I := I) g s
        (X + X') Y Z A x =
      nablaTensor0SCurv (I := I) g s X Y Z A x + nablaTensor0SCurv (I := I) g s X' Y Z A x := by
  classical
  apply Tensor0SSpace.toModel_injective
  simp only [Tensor0SSpace.toModel_add]
  apply ContinuousMultilinearMap.ext
  intro u
  rw [ContinuousMultilinearMap.add_apply,
      nablaTensorCov_baseSlot_eval (I := I) g s (X + X') Y Z A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s X Y Z A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s X' Y Z A hA x u]
  rw [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [nablaBaseSlotCurv_add_left (I := I) g X X' Y Z x (u k)]
  exact (Tensor0SSpace.toModel (A x)).map_update_add u k
    (nablaBaseSlotCurv (I := I) g X Y Z x (u k))
    (nablaBaseSlotCurv (I := I) g X' Y Z x (u k))

/-- **`ℝ`-homogeneity of the differentiated tensor curvature in its derivation slot.** For smooth fields
`X, Y, Z` and a scalar `c`, scaling the derivation slot by the constant `c` scales the differentiated
tensor curvature: `(∇_{c·X} R^{(s)})(Y, Z) A = c · (∇_X R^{(s)})(Y, Z) A`.  This is the `ℝ`-homogeneity
in `X x` of the value-bilinear differentiated curvature; the leading-term `d(c)`-correction vanishes
because `c` is constant. -/
theorem nablaTensor0SCurv_smul_left
    (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A) (x : M) :
    nablaTensor0SCurv (I := I) g s
        (c • X) Y Z A x =
      c • nablaTensor0SCurv (I := I) g s X Y Z A x := by
  classical
  apply Tensor0SSpace.toModel_injective
  simp only [Tensor0SSpace.toModel_smul]
  apply ContinuousMultilinearMap.ext
  intro u
  rw [ContinuousMultilinearMap.smul_apply,
      nablaTensorCov_baseSlot_eval (I := I) g s (c • X) Y Z A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s X Y Z A hA x u]
  rw [smul_neg, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [nablaBaseSlotCurv_smul_left (I := I) g c X Y Z x (u k)]
  exact (Tensor0SSpace.toModel (A x)).map_update_smul u k c
    (nablaBaseSlotCurv (I := I) g X Y Z x (u k))

/-- **Additivity of the differentiated tensor curvature in its first antisymmetric slot.** For smooth
fields `X, Y, Y', Z` whose second slot is the sum `Y + Y'`, the differentiated tensor curvature splits
additively: `(∇_X R^{(s)})(Y + Y', Z) A = (∇_X R^{(s)})(Y, Z) A + (∇_X R^{(s)})(Y', Z) A`.  This is the
additivity in `Y x` of the value-bilinear differentiated curvature. -/
theorem nablaTensor0SCurv_add_mid
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Y' Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A) (x : M) :
    nablaTensor0SCurv (I := I) g s
        X (Y + Y') Z A x =
      nablaTensor0SCurv (I := I) g s X Y Z A x + nablaTensor0SCurv (I := I) g s X Y' Z A x := by
  classical
  apply Tensor0SSpace.toModel_injective
  simp only [Tensor0SSpace.toModel_add]
  apply ContinuousMultilinearMap.ext
  intro u
  rw [ContinuousMultilinearMap.add_apply,
      nablaTensorCov_baseSlot_eval (I := I) g s X (Y + Y') Z A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s X Y Z A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s X Y' Z A hA x u]
  rw [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [nablaBaseSlotCurv_add_right (I := I) g X Y Y' Z x (u k)]
  exact (Tensor0SSpace.toModel (A x)).map_update_add u k
    (nablaBaseSlotCurv (I := I) g X Y Z x (u k))
    (nablaBaseSlotCurv (I := I) g X Y' Z x (u k))

/-- **`ℝ`-homogeneity of the differentiated tensor curvature in its first antisymmetric slot.** For
smooth fields `X, Y, Z` and a scalar `c`, scaling the first antisymmetric slot by the constant `c`
scales the differentiated tensor curvature: `(∇_X R^{(s)})(c·Y, Z) A = c · (∇_X R^{(s)})(Y, Z) A`.  This
is the `ℝ`-homogeneity in `Y x` of the value-bilinear differentiated curvature. -/
theorem nablaTensor0SCurv_smul_mid
    (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A) (x : M) :
    nablaTensor0SCurv (I := I) g s
        X (c • Y) Z A x =
      c • nablaTensor0SCurv (I := I) g s X Y Z A x := by
  classical
  apply Tensor0SSpace.toModel_injective
  simp only [Tensor0SSpace.toModel_smul]
  apply ContinuousMultilinearMap.ext
  intro u
  rw [ContinuousMultilinearMap.smul_apply,
      nablaTensorCov_baseSlot_eval (I := I) g s X (c • Y) Z A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s X Y Z A hA x u]
  rw [smul_neg, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [nablaBaseSlotCurv_smul_right (I := I) g c X Y Z x (u k)]
  exact (Tensor0SSpace.toModel (A x)).map_update_smul u k c
    (nablaBaseSlotCurv (I := I) g X Y Z x (u k))

/-! ### The bundled value-bilinear form and the frame conversion -/

/-- **The value-bilinear form of the differentiated tensor curvature in its two leading slots.** At a
point `x`, fixed first-antisymmetric/section data `Z, A`, this is the `ℝ`-bilinear map
`T_x M →ₗ[ℝ] T_x M →ₗ[ℝ] Tensor0SSpace s I x` whose value at `(v, w)` is the differentiated tensor
curvature `(∇_{ext v} R^{(s)})(ext w, Z) A` evaluated on smooth extensions `ext v, ext w` of `v, w`.
By the value-bilinearity of `nablaTensor0SCurv` (`nablaTensor0SCurv_add_left/_smul_left/_add_mid/_smul_mid`,
well-definedness `nablaTensor0SCurv_eq_of_pointwise_eq_leftMid`), this is well-defined and bilinear, and
agrees with `nablaTensor0SCurv g s X Y Z A x` on the point values of any smooth fields
(`nablaTensor0SCurvBilin_apply_smooth`). -/
def nablaTensor0SCurvBilin
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] Tensor0SSpace s I x :=
  LinearMap.mk₂ ℝ
    (fun v w => nablaTensor0SCurv (I := I) g s
      (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent_contMDiff (I := I) x v))
      (ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
        (smoothExtensionTangent_contMDiff (I := I) x w)) Z A x)
    (fun v v' w => by
      dsimp only
      have hadd : (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (v + v'))
            (smoothExtensionTangent_contMDiff (I := I) x (v + v'))) x =
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent_contMDiff (I := I) x v)
            + ContMDiffSection.mk (smoothExtensionTangent (I := I) x v')
              (smoothExtensionTangent_contMDiff (I := I) x v')) x := by
        simp only [ContMDiffSection.coeFn_mk, ContMDiffSection.coe_add, Pi.add_apply,
          smoothExtensionTangent_eq]
      rw [nablaTensor0SCurv_eq_of_pointwise_eq_leftMid (I := I) g s
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (v + v'))
            (smoothExtensionTangent_contMDiff (I := I) x (v + v')))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent_contMDiff (I := I) x v)
            + ContMDiffSection.mk (smoothExtensionTangent (I := I) x v')
              (smoothExtensionTangent_contMDiff (I := I) x v'))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent_contMDiff (I := I) x w))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent_contMDiff (I := I) x w)) Z A hA x hadd rfl]
      exact nablaTensor0SCurv_add_left (I := I) g s _ _ _ Z A hA x)
    (fun c v w => by
      dsimp only
      have hsmul : (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (c • v))
            (smoothExtensionTangent_contMDiff (I := I) x (c • v))) x =
          (c • ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent_contMDiff (I := I) x v)) x := by
        simp only [ContMDiffSection.coeFn_mk, ContMDiffSection.coe_smul, Pi.smul_apply,
          smoothExtensionTangent_eq]
      rw [nablaTensor0SCurv_eq_of_pointwise_eq_leftMid (I := I) g s
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (c • v))
            (smoothExtensionTangent_contMDiff (I := I) x (c • v)))
          (c • ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent_contMDiff (I := I) x v))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent_contMDiff (I := I) x w))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent_contMDiff (I := I) x w)) Z A hA x hsmul rfl]
      exact nablaTensor0SCurv_smul_left (I := I) g s c _ _ Z A hA x)
    (fun v w w' => by
      dsimp only
      have hadd : (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (w + w'))
            (smoothExtensionTangent_contMDiff (I := I) x (w + w'))) x =
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent_contMDiff (I := I) x w)
            + ContMDiffSection.mk (smoothExtensionTangent (I := I) x w')
              (smoothExtensionTangent_contMDiff (I := I) x w')) x := by
        simp only [ContMDiffSection.coeFn_mk, ContMDiffSection.coe_add, Pi.add_apply,
          smoothExtensionTangent_eq]
      rw [nablaTensor0SCurv_eq_of_pointwise_eq_leftMid (I := I) g s
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent_contMDiff (I := I) x v))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent_contMDiff (I := I) x v))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (w + w'))
            (smoothExtensionTangent_contMDiff (I := I) x (w + w')))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent_contMDiff (I := I) x w)
            + ContMDiffSection.mk (smoothExtensionTangent (I := I) x w')
              (smoothExtensionTangent_contMDiff (I := I) x w')) Z A hA x rfl hadd]
      exact nablaTensor0SCurv_add_mid (I := I) g s _ _ _ Z A hA x)
    (fun c v w => by
      dsimp only
      have hsmul : (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (c • w))
            (smoothExtensionTangent_contMDiff (I := I) x (c • w))) x =
          (c • ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent_contMDiff (I := I) x w)) x := by
        simp only [ContMDiffSection.coeFn_mk, ContMDiffSection.coe_smul, Pi.smul_apply,
          smoothExtensionTangent_eq]
      rw [nablaTensor0SCurv_eq_of_pointwise_eq_leftMid (I := I) g s
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent_contMDiff (I := I) x v))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent_contMDiff (I := I) x v))
          (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (c • w))
            (smoothExtensionTangent_contMDiff (I := I) x (c • w)))
          (c • ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent_contMDiff (I := I) x w)) Z A hA x rfl hsmul]
      exact nablaTensor0SCurv_smul_mid (I := I) g s c _ _ Z A hA x)

/-- The defining evaluation of `nablaTensor0SCurvBilin` on a pair of fibre vectors. -/
theorem nablaTensor0SCurvBilin_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A) (x : M)
    (v w : TangentSpace I x) :
    nablaTensor0SCurvBilin (I := I) g s Z A hA x v w =
      nablaTensor0SCurv (I := I) g s
        (ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent_contMDiff (I := I) x v))
        (ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent_contMDiff (I := I) x w)) Z A x := rfl

/-- **Application formula for `nablaTensor0SCurvBilin` on smooth fields.** On the point values of smooth
fields `X, Y`, the bilinear form returns the differentiated tensor curvature
`nablaTensor0SCurv g s X Y Z A x`: the smooth extensions of `X x, Y x` agree with `X, Y` at `x`, so
well-definedness `nablaTensor0SCurv_eq_of_pointwise_eq_leftMid` identifies the values. -/
theorem nablaTensor0SCurvBilin_apply_smooth
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A) (x : M) :
    nablaTensor0SCurvBilin (I := I) g s Z A hA x (X x) (Y x) =
      nablaTensor0SCurv (I := I) g s X Y Z A x := by
  rw [nablaTensor0SCurvBilin_apply]
  refine nablaTensor0SCurv_eq_of_pointwise_eq_leftMid (I := I) g s
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (X x))
      (smoothExtensionTangent_contMDiff (I := I) x (X x)))
    X
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (Y x))
      (smoothExtensionTangent_contMDiff (I := I) x (Y x)))
    Y Z A hA x ?_ ?_
  · simp only [ContMDiffSection.coeFn_mk, smoothExtensionTangent_eq]
  · simp only [ContMDiffSection.coeFn_mk, smoothExtensionTangent_eq]

/-- **The Parseval-frame = orthonormal-frame conversion for the differentiated-curvature diagonal
trace.** For a global smooth `g_x`-Parseval family `V` (reproducing every tangent vector at `x` through
the metric), the diagonal differentiated-curvature trace `∑_a (∇_{V a} R^{(s)})(V a, Z) A` over the
Parseval family equals the diagonal trace `∑_i (∇_{B_i} R^{(s)})(B_i, Z) A` over the centre-adapted
orthonormal frame `B_i := smoothOrthoFrame g x i`.

This is the diagonal trace of the value-bilinear form `nablaTensor0SCurvBilin g s Z A hA x` on `T_x M`,
so the abstract bilinear conversion `parseval_family_sum_bilin_eq` (a Parseval family and an orthonormal
basis compute the same diagonal sum for every `ℝ`-bilinear map) converts the frame.  It is the missing
converter between the fixed global Parseval-frame differentiated-curvature trace produced by the
Bochner-fold carriers and the orthonormal-frame differentiated-curvature trace consumed by the
contracted-second-Bianchi Ricci folds (`nablaCurvSec_diag_frame_trace_eq_nablaRicci_sub`,
`frame_sum_nablaTensor0SCurv_diag_baseSlot_eval`). -/
theorem parsevalFrame_eq_orthoFrame_diag_nablaTensor0SCurv
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x), (∑ a : Fin N, g.inner x (V a x) u • V a x) = u)
    (x : M) :
    (∑ a : Fin N, nablaTensor0SCurv (I := I) g s
        (ContMDiffSection.mk (V a) (hV a)) (ContMDiffSection.mk (V a) (hV a)) Z A x) =
      ∑ i : Fin (Module.finrank ℝ E),
        nablaTensor0SCurv (I := I) g s
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i)) Z A x := by
  classical
  have hconv := parseval_family_sum_bilin_eq (I := I) (M := M) g x
    (W := fun a : Fin N => V a x) (hW := fun u => hPar x u)
    (e := fun i : Fin (Module.finrank ℝ E) => smoothOrthoFrame (I := I) g x i x)
    (horth := fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)
    (B := nablaTensor0SCurvBilin (I := I) g s Z A hA x)
  rw [Finset.sum_congr rfl (fun a _ =>
        (nablaTensor0SCurvBilin_apply_smooth (I := I) g s
          (ContMDiffSection.mk (V a) (hV a)) (ContMDiffSection.mk (V a) (hV a)) Z A hA x).symm),
      Finset.sum_congr rfl (fun i _ =>
        (nablaTensor0SCurvBilin_apply_smooth (I := I) g s
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i)) Z A hA x).symm)]
  simp only [ContMDiffSection.coeFn_mk]
  exact hconv

end Connection
end Integral
end DifferentialGeometry

end
