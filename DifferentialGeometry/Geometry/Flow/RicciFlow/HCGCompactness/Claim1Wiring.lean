import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AkMFold
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricFlatBasis
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Claim 1 geometric wiring (plan: `Claim1Wiring.md`)

Discharges the hypotheses of `claim1` (AkMFold.lean) on the actual geometry.
Canonical setting (design D2b): a tangent-bundle trivialization `e₀` with
`frame := e₀.localFrame basisE`, `u := e₀.baseSet`.

SIGN CONVENTION (`Claim1Wiring.md` §1b): `A_k = ∇_k − ∇_ref`, so the `A_k`
component array is `chr(g_k) − chr(gRef)` and the lowered-Koszul coefficients
are `(+½, +½, −½)`.

This file so far: **B2** (smoothness inputs `hchr`, `hframe`, `hA`).
TODO (B2 tail): `hg` = smoothness of `frameComp0S (metricTensorField g) frame`
via `TensorMultilinear.contMDiffAt_section_apply_gen` (the (0,s) eval engine
inside `tensorRS_eval_contMDiffAt`, `Tensor/RSTensor/LocalFrameRegularity.lean`)
once the `metricTensorField`-as-smooth-section producer is located.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-! ## B2: the smoothness inputs of `claim1` on a trivialization domain -/

/-- **B2 `hchr`**: the Levi-Civita Christoffel array of `g` in the trivialization
frame is `C^∞` on the trivialization domain (the `ContMDiffOn` form the component
towers consume).  Analytic content = `lc_christoffel_contMDiffAt`
(`LeviCivita/Smooth/MetricFlatBasis.lean`, the `localFrame_coeff` form); here we
bridge `IsLocalFrameOn.coeff` to `localFrame_coeff` on the trivialization domain. -/
theorem lcChrist_e_mdiffOn
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    (d i j : Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y : M => christoffelSymbolInFrame
        (leviCivitaConnectionOfMetric (I := I) g)
        (fun a y' => e₀.localFrame basisE a y')
        (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y d i j)
      e₀.baseSet := by
  intro y hy
  refine ((lc_christoffel_contMDiffAt (I := I) e₀ basisE g hy d i j).congr_of_eventuallyEq
    ?_).contMDiffWithinAt
  filter_upwards [e₀.open_baseSet.mem_nhds hy] with z hz
  have hbasis : (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hz =
      e₀.basisAt basisE hz := by
    ext j'
    simp [IsLocalFrameOn.toBasisAt, Bundle.Trivialization.localFrame,
      Bundle.Trivialization.basisAt, hz]
  simp [christoffelSymbolInFrame, IsLocalFrameOn.coeff, hz,
    Bundle.Trivialization.localFrame_coeff, hbasis]

/-- **B2 `hframe`**: the trivialization frame vectors are smooth sections on the
trivialization domain (the `TotalSpace.mk'` form the tower machinery consumes). -/
theorem frame_e_mdiffOn
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (basisE : Module.Basis Idx Real E) (d : Idx) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (e₀.localFrame basisE d y))
      e₀.baseSet :=
  (e₀.isLocalFrameOn_localFrame_baseSet I ∞ basisE).contMDiffOn d

/-- The `A_k = ∇_k − ∇_ref` component field in the trivialization frame, with the
contracted UPPER slot LAST (`m 2`), as the towers and `claim1` consume it:
`A(m) = Γ(g_k)^{m 2}_{m 0, m 1} − Γ(gRef)^{m 2}_{m 0, m 1}`. -/
def akCompField
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (gK gRef : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E) :
    M → (Fin (2 + 1) → Idx) → Real :=
  fun y m =>
    christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gK)
      (fun a y' => e₀.localFrame basisE a y')
      (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y (m 0) (m 1) (m 2) -
    christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
      (fun a y' => e₀.localFrame basisE a y')
      (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y (m 0) (m 1) (m 2)

/-- **B2 `hA`**: the `A_k` component field is `C^∞` on the trivialization domain
(difference of the two smooth Christoffel arrays). -/
theorem akCompField_mdiffOn
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (gK gRef : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    (k : Fin (2 + 1) → Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => akCompField (I := I) e₀ gK gRef basisE y k) e₀.baseSet := by
  exact (lcChrist_e_mdiffOn e₀ gK basisE (k 0) (k 1) (k 2)).sub
    (lcChrist_e_mdiffOn e₀ gRef basisE (k 0) (k 1) (k 2))

set_option backward.isDefEq.respectTransparency false in
/-- **B2 `hg`**: the metric component field in the trivialization frame is `C^∞` on the
trivialization domain (the smooth `(0,2)` section `metricTensorField g` evaluated on the
smooth frame slots, via the `(0,s)` evaluation engine). -/
theorem gCompField_mdiffOn
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    (k : Fin (1 + 1) → Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => frameComp0S (I := I) (metricTensorField (I := I) g)
        (fun a y' => e₀.localFrame basisE a y') y k) e₀.baseSet := by
  intro y hy
  have hT : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun x : M => Tensor0SSpace 2 I x) b (metricTensorField (I := I) g b)) y :=
    (metricTensorField (I := I) g).contMDiff.contMDiffAt
  have hv : ∀ i : Fin 2,
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b
          (e₀.localFrame basisE (k i) b)) y :=
    fun i => (frame_e_mdiffOn e₀ basisE (k i)).contMDiffAt (e₀.open_baseSet.mem_nhds hy)
  have h := TensorMultilinear.contMDiffAt_section_apply_gen
    (T := fun b : M => metricTensorField (I := I) g b) hT
    (v := fun (i : Fin 2) (b : M) => e₀.localFrame basisE (k i) b) hv
  exact h.contMDiffWithinAt

/-! ## B3: the pointwise inverse metric array (`Ginv` + `hinv`)

No smoothness of the inverse is needed anywhere (the `claim1` engine never
differentiates `g⁻¹`) — only the pointwise inverse property and, later (B4), a
norm bound. -/

/-- The Gram matrix of `g` in the trivialization frame at `y`. -/
def gramE
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E) (y : M) :
    Matrix Idx Idx Real :=
  Matrix.of fun i j => g.inner y (e₀.localFrame basisE i y) (e₀.localFrame basisE j y)

theorem gramE_herm
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E) (y : M) :
    (gramE (I := I) e₀ g basisE y).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, gramE, Matrix.of_apply]
  exact g.symm y _ _

/-- Quadratic-form expansion of the Gram matrix: `c ⬝ᵥ (G *ᵥ c) = g(W, W)` with
`W = Σ cᵢ • frameᵢ`. -/
theorem gramE_dotVec
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E) (y : M)
    (c : Idx → Real) :
    c ⬝ᵥ (gramE (I := I) e₀ g basisE y).mulVec c =
      g.inner y (∑ i, c i • e₀.localFrame basisE i y)
        (∑ j, c j • e₀.localFrame basisE j y) := by
  have hexpand : g.inner y (∑ i, c i • e₀.localFrame basisE i y)
        (∑ j, c j • e₀.localFrame basisE j y) =
      ∑ i, ∑ j, c i * c j *
        g.inner y (e₀.localFrame basisE i y) (e₀.localFrame basisE j y) := by
    have hL : g.inner y (∑ i, c i • e₀.localFrame basisE i y) =
        ∑ i, c i • g.inner y (e₀.localFrame basisE i y) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => ContinuousLinearMap.map_smul _ _ _
    rw [hL, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  rw [hexpand]
  simp only [dotProduct, Matrix.mulVec, gramE, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The Gram matrix is positive-definite on the trivialization domain (the frame is a
basis there and `g` is positive). -/
theorem gramE_posDef
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    {y : M} (hy : y ∈ e₀.baseSet) :
    (gramE (I := I) e₀ g basisE y).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (gramE_herm (I := I) e₀ g basisE y) ?_
  intro c hc
  rw [show (star c : Idx → Real) = c from funext fun i => star_trivial _, gramE_dotVec]
  have hwnz : (∑ i, c i • e₀.localFrame basisE i y) ≠ 0 := by
    intro hw0
    have hli := (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).linearIndependent hy
    rw [Fintype.linearIndependent_iff] at hli
    exact hc (funext (hli c hw0))
  exact g.pos y _ hwnz

/-- The pointwise inverse-metric array in the `(Fin 2 → Idx)`-shape `claim1` consumes
(the matrix inverse of the Gram matrix; junk off the trivialization domain). -/
def ginvCompField
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E) :
    M → (Fin (1 + 1) → Idx) → Real :=
  fun y m => (gramE (I := I) e₀ g basisE y)⁻¹ (m 0) (m 1)

/-- **B3 `hinv`**: the defining inverse property, in the exact shape of `claim1`'s
`hinv` hypothesis. -/
theorem ginv_hinv
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    {y : M} (hy : y ∈ e₀.baseSet) (c e : Idx) :
    (∑ l : Idx,
      frameComp0S (I := I) (metricTensorField (I := I) g)
          (fun a y' => e₀.localFrame basisE a y') y (Fin.snoc (fun _ : Fin 1 => l) c) *
        ginvCompField (I := I) e₀ g basisE y (Fin.snoc (fun _ : Fin 1 => e) l)) =
      if c = e then 1 else 0 := by
  classical
  have hdet : IsUnit (gramE (I := I) e₀ g basisE y).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (gramE_posDef (I := I) e₀ g basisE hy).det_pos)
  have hentry := congrArg (fun A : Matrix Idx Idx Real => A e c)
    (Matrix.nonsing_inv_mul (gramE (I := I) e₀ g basisE y) hdet)
  simp only [Matrix.mul_apply, Matrix.one_apply] at hentry
  have hterm : ∀ l : Idx,
      frameComp0S (I := I) (metricTensorField (I := I) g)
          (fun a y' => e₀.localFrame basisE a y') y (Fin.snoc (fun _ : Fin 1 => l) c) *
        ginvCompField (I := I) e₀ g basisE y (Fin.snoc (fun _ : Fin 1 => e) l) =
      (gramE (I := I) e₀ g basisE y)⁻¹ e l * gramE (I := I) e₀ g basisE y l c := by
    intro l
    have h0 : (Fin.snoc (fun _ : Fin 1 => l) c : Fin 2 → Idx) 0 = l := by simp [Fin.snoc]
    have h1 : (Fin.snoc (fun _ : Fin 1 => l) c : Fin 2 → Idx) 1 = c := by simp [Fin.snoc]
    have h0' : (Fin.snoc (fun _ : Fin 1 => e) l : Fin 2 → Idx) 0 = e := by simp [Fin.snoc]
    have h1' : (Fin.snoc (fun _ : Fin 1 => e) l : Fin 2 → Idx) 1 = l := by simp [Fin.snoc]
    rw [frameComp0S_apply, metricTensorField_apply, h0, h1,
      show ginvCompField (I := I) e₀ g basisE y (Fin.snoc (fun _ : Fin 1 => e) l) =
        (gramE (I := I) e₀ g basisE y)⁻¹ e l from by
        rw [ginvCompField, h0', h1'],
      show g.inner y (e₀.localFrame basisE l y) (e₀.localFrame basisE c y) =
        gramE (I := I) e₀ g basisE y l c from rfl]
    ring
  rw [Finset.sum_congr rfl fun l _ => hterm l, hentry]
  rcases eq_or_ne e c with rfl | h
  · simp
  · rw [if_neg h, if_neg fun hce => h hce.symm]

end DifferentialGeometry.PDE.RicciFlow
