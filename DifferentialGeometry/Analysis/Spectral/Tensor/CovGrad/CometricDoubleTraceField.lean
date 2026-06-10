import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
import DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradParallelNaturality

/-! # The cometric raised-coframe double-trace / slot-0-raise smooth operator-field templates

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the metric-free C^∞ field-smoothness templates and the
intrinsic cometric `g₀⁻¹` double-trace operator-field constructions that feed both the curvature-trace
covariant-jet reduction of the Ricci–DeTurck curvature difference
(`SegmentMetricCurvatureDifferenceCovJet.lean`) and the cross-correction parallel two-section
contraction (`CrossCorrectionParallelContraction.lean`).

The C^∞ field-smoothness templates — the bundle interior product (`interiorProductField_contMDiff`),
the frame-free natural trace (`contractTraceField_contMDiff`), and the covariant-rank cast
(`tensor0SField_castRank_contMDiff`, through the fixed model isometry `modelRankCast`) — are the
smoothness-level analogues of the analytic `contract_*Field` lemmas, valid at every smoothness level
through the same model-bilinear `clm_apply` / `model_contract_trace`-composition arguments.

On top of them the file builds the genuine cometric `g₀⁻¹` double trace of the two leading covariant
slots: the model cometric raise `cometricLmodel` (the model reading of the smooth Hom-section sharp
`inverseMetricSharpField`), the frame-free model double trace `modelDoubleTrace` (the categorical
trace `E ⊗ E^* ≅ End E` of the cometric-raised slot with the original slot — ONE inverse,
`D : g₀⁻¹`), and their fibre realisations `ricciModelTrace42Fib`, `cometricRaiseSlot0Fib`, with the
base-point smoothness `ricciModelTrace42Fib_contMDiff` routed through the globally-smooth cometric
Hom-bundle section, with NO chart-selected non-`∇₀`-parallel ambient frame and NO single-trivialization
`symmL` factor. The model double trace is the natural trace of the cometric-raised slot
(`model_contract_trace_raiseSlot0ModelL`, `raiseSlot0ModelL`), and the bundle trace at the unit reads
as the model trace at the unit (`contract_trace_unitZero_toModel`). -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The model-fibre rank cast `Tensor0SModel m → Tensor0SModel n` along `h : m = n`.**  The
continuous-linear (isometric) reindex of the model multilinear fibre, via
`ContinuousMultilinearMap.domDomCongrₗᵢ (finCongr h)`.  Used to chain the two leading-slot interior
products of the model-basis double trace across the `Nat`-equalities `4 + a = (3 + a) + 1` and
`3 + a = (2 + a) + 1` (which hold by `omega` but not `rfl`, as `Nat.add` recurses on the right). -/
noncomputable def modelRankCast {m n : ℕ} (h : m = n) :
    Tensor0SBundle.Tensor0SModel m ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E :=
  (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
    (finCongr h)).toContinuousLinearEquiv.toContinuousLinearMap

set_option linter.unusedSectionVars false in
/-- The reflexive rank cast is the identity on the model fibre. -/
@[simp] theorem modelRankCast_refl {m : ℕ} (T : Tensor0SBundle.Tensor0SModel m ℝ E) :
    modelRankCast (E := E) (rfl : m = m) T = T := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [modelRankCast, finCongr_refl]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **C^∞ interior-product field smoothness.**  At the C^∞ smoothness level, the bundle interior
product of a smooth `(0, s + 1)`-tensor field `α` with a smooth vector field `X` — `x ↦ interior_product s
x (X x) (α x)`, reading `X x` into the leading covariant slot — is a smooth `(0, s)`-tensor field.  This is
the C^∞ analogue of `Tensor0SBundle.contract_Tensor0SField` (which is stated only for analytic `ω`
manifolds via its section variable, hence unusable in the C^∞ context here); its proof is the *same*
model-bilinear `clm_apply` argument (`model_interior_bilinear` is continuous, applied to the trivialised
smooth `X` and `α`), valid at every smoothness level.  It is **non-vacuous**: the genuine smooth interior
product, NOT the zero field. -/
theorem interiorProductField_contMDiff (s : ℕ)
    (α : ∀ x : M, Tensor0SBundle.Tensor0SSpace (s + 1) I x)
    (hα : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x (α x)))
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z) x
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x (X x) (α x))) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  intro x₀
  rw [Bundle.contMDiffAt_section (F := Tensor0SBundle.Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z)]
  have hα' := (Bundle.contMDiffAt_section (F := Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x₀).mp (hα x₀)
  have hX' := (Bundle.contMDiffAt_section (F := E) (E := TangentSpace I) x₀).mp (X.contMDiff x₀)
  have h_combine :
      ContMDiffAt I 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E) ∞
        (fun x => Tensor0SBundle.model_interior_bilinear ℝ E s
          ((trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
            (fun x => Tensor0SBundle.Tensor0SSpace (s + 1) I x) x₀ ⟨x, α x⟩).2)) x₀ :=
    ((contMDiffAt_const (c := Tensor0SBundle.model_interior_bilinear ℝ E s)).clm_apply hX').clm_apply hα'
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  -- equality of two model-fiber elements at `x` in the base set
  apply ContinuousMultilinearMap.ext
  intro v
  set symmL := (trivializationAt E (TangentSpace I) x₀).symmL ℝ x with hsymmL
  set gtilde : E := (trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2 with hgtilde
  change (α x) (@Fin.cons s (fun _ => E) ((X x : TangentSpace I x) : E) (fun i => symmL (v i))) =
    (α x) (fun i => symmL (@Fin.cons s (fun _ => E) gtilde v i))
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · change ((X x : TangentSpace I x) : E) = symmL gtilde
    have h := (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := ℝ) hx (X x)
    have hcl : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x (X x) = gtilde := by
      change (trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ x (X x) = _
      rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
    rw [hcl] at h
    exact h.symm
  · intro j
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **C^∞ natural-trace field smoothness.**  At the C^∞ smoothness level, the fibrewise
frame-free natural trace of a smooth `(1 + r, s + 1)`-tensor field `T` — `x ↦ contract_trace r s x (T x)`,
contracting the leading contravariant slot against the leading covariant slot — is a smooth `(r, s)`-tensor
field.  This is the C^∞ analogue of `Tensor0SBundle.contract_TensorRSField` (stated only for analytic `ω`
manifolds via its section variable); its proof is the *same* `model_contract_trace`-composition argument
(`model_contract_trace` is continuous-linear, composed with the trivialised smooth `T`), valid at every
smoothness level.  It is **non-vacuous** (the genuine smooth natural trace). -/
theorem contractTraceField_contMDiff (r s : ℕ)
    (T : ∀ x : M, Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I x)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) x (T x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x
        (Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x (T x))) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (1 + r) (s + 1)
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (1 + r)
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r
  intro x₀
  rw [Bundle.contMDiffAt_section (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)]
  have hT' := (Bundle.contMDiffAt_section (F := Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) x₀).mp (hT x₀)
  have hTrace : ContMDiffAt I 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E) ∞
      (fun x => Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s
        ((trivializationAt (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) x₀ ⟨x, T x⟩).2)) x₀ :=
    (Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s).contMDiffAt.comp x₀ hT'
  refine hTrace.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  -- inline `contract_trace_trivialization_eq` (the C^∞-valid frame-naturality of the trace, over the
  -- public model trace naturality `model_contract_trace_naturality`)
  set L : E →L[ℝ] E := (trivializationAt E (TangentSpace I) x₀).symmL ℝ x with hLdef
  set Linv : E →L[ℝ] E := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x with hLinvdef
  set Tx : Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E :=
    Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) (1 + r) (s + 1) x (T x) with hTxdef
  have hL : L.comp Linv = ContinuousLinearMap.id ℝ E := by
    ext z
    exact (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt (R := ℝ) hx z
  have hR : Linv.comp L = ContinuousLinearMap.id ℝ E := by
    ext z
    exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL (R := ℝ) hx z
  have h_cLMAt : ∀ (k : ℕ) (U : Tensor0SBundle.Tensor0SSpace k I x) (v : Fin k → E),
      (trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).continuousLinearMapAt ℝ x U v =
      U (fun i => L (v i)) := by
    intro k U v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).linearMapAt ℝ x) =
        fun y => (trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
    rfl
  have h_symmL : ∀ (k : ℕ) (U : Tensor0SBundle.Tensor0SModel k ℝ E) (u : Fin k → E),
      ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).symmL ℝ x U) u =
        U (fun i => Linv (u i)) := by
    intro k U u
    have h_inv : ∀ z : E, L (Linv z) = z := by
      intro z
      have h := congrArg (fun f : E →L[ℝ] E => f z) hL
      simpa [ContinuousLinearMap.comp_apply] using h
    have hu : u = fun i => L (Linv (u i)) := by
      funext i; exact (h_inv (u i)).symm
    calc
      ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).symmL ℝ x U) u
          = ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).symmL ℝ x U)
              (fun i => L (Linv (u i))) := by rw [← hu]
      _ = (trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).continuousLinearMapAt ℝ x
            ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).symmL ℝ x U)
            (fun i => Linv (u i)) := (h_cLMAt k _ _).symm
      _ = U (fun i => Linv (u i)) := by
            rw [(trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).continuousLinearMapAt_symmL
              (R := ℝ) hx]
  have h_input :
      ((trivializationAt (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) x₀ ⟨x, T x⟩).2) =
      (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (s + 1) L).comp
        (Tx.comp (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x₀).continuousLinearMapAt ℝ x
        ((T x) ((trivializationAt (Tensor0SBundle.Tensor0SModel (1 + r) ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace (1 + r) I z) x₀).symmL ℝ x β)) v =
      ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (s + 1) L)
        (Tx ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv) β))) v
    rw [h_cLMAt, Tensor0SBundle.model_covariantChange_apply]
    have hβ :
        (trivializationAt (Tensor0SBundle.Tensor0SModel (1 + r) ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace (1 + r) I z) x₀).symmL ℝ x β =
          (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      rw [h_symmL]; rfl
    rw [hβ]; rfl
  have h_output :
      (trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀
        ⟨x, Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x (T x)⟩).2 =
      (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) s L).comp
        ((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s Tx).comp
          (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace s I z) x₀).continuousLinearMapAt ℝ x
        ((Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x (T x))
          ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace r I z) x₀).symmL ℝ x β)) v =
      ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) s L)
        ((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s Tx)
          ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv) β))) v
    rw [h_cLMAt, Tensor0SBundle.model_covariantChange_apply]
    -- unfold `contract_trace` (def: `(equivRS r s).symm ∘ model_contract_trace ∘ (equivRS (1+r)(s+1))`);
    -- the inverse arrow-congr applied to a covector-tuple reads off the model element directly
    change ((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s
          ((Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) (1 + r) (s + 1) x) (T x)))
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r x)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace r I z) x₀).symmL ℝ x β))) (fun i => L (v i)) =
      (((Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) r s) Tx)
        ((Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv) β)) (fun i => L (v i))
    have hβ2 : (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r x)
          ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace r I z) x₀).symmL ℝ x β) =
          (Tensor0SBundle.model_covariantChange (𝕜 := ℝ) (E := E) r Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      rw [Tensor0SBundle.model_covariantChange_apply]
      exact h_symmL r β u
    rw [hβ2]
  rw [h_input, h_output]
  exact (Tensor0SBundle.model_contract_trace_naturality (𝕜 := ℝ) (E := E)
    r s L Linv hL hR Tx).symm

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **The covariant-rank cast of a smooth `(0, m)`-field is a smooth `(0, n)`-field.**  For a covariant-rank
equality `h : m = n` and a smooth `(0, m)`-tensor field `Y`, the fibrewise `modelRankCast`-reindexed field
`x ↦ ofModel (modelRankCast h (toModel (Y x)))` is a smooth `(0, n)`-tensor field.  Proved by transport
along `h` (the cast is the identity reindex when `m = n`).  The slot reindex is a fixed model isometry,
NOT a metric- or frame-dependent operation. -/
theorem tensor0SField_castRank_contMDiff {m n : ℕ} (h : m = n)
    (Y : ∀ x : M, Tensor0SBundle.Tensor0SSpace m I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel m ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace m I z) x (Y x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace n I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (modelRankCast (E := E) h (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
  subst h
  refine hY.congr (fun x => ?_)
  -- after `subst`, the cast is the reflexive reindex (identity) and `ofModel ∘ toModel = id`
  simp only [modelRankCast_refl, Tensor0SBundle.Tensor0SSpace.ofModel_toModel]

/-- **The model reading of the cometric index-raise `♯ : T^*_x M → T_x M`.**  The fibrewise
inverse-metric sharp `inverseMetricSharpFib g₀ x` conjugated through the model identification
`tensor0SSpace_continuousLinearEquiv 1 x`, read as a model-level continuous-linear map
`Tensor0SModel 1 → E`: a model covector `α` is sent to the `g₀`-raised tangent vector `♯α`.  This is the
SMOOTH `g₀`-raise (the model reading of the globally-smooth Hom-bundle section `inverseMetricSharpField`);
it is used to raise the leading covariant slot of a model `(0, s + 2)`-tensor before the FRAME-FREE
natural trace.  No chart-selected ambient basis enters: smoothness flows through
`inverseMetricSharpField_contMDiff`. -/
noncomputable def cometricLmodel (g₀ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E :=
  (inverseMetricSharpFib (I := I) g₀ x).comp
    (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm.toContinuousLinearMap

/-- **The model `g₀⁻¹` double trace of the two leading covariant slots, `(0, s + 2) → (0, s)`.**  Given
the model cometric raise `L : Tensor0SModel 1 → E` (`L := cometricLmodel g₀ x`), the genuine cometric
double trace of the two leading covariant slots: raise slot `0` via `L` against the model `cDualBasis`
covector `b^k`, contract the (new leading) slot against the dual model basis vector `b_k`, and sum over
the internal model basis:
```
modelDoubleTrace s L D (m) = ∑ₖ D(L b^k, b_k, m).
```
This is the FRAME-FREE natural trace of the cometric-raised slot with the original slot (the categorical
trace `E ⊗ E^* ≅ End E`, basis-independent by `model_contract_trace_naturality`): with `L = ♯` it is the
genuine cometric `g₀^{ij}`-trace (ONE inverse), `∑ₖ D(♯b^k, b_k) = D : g₀⁻¹`.  Crucially, the internal
basis `b_k, b^k` only enters the *frame-free* trace (where it cancels); the smoothness in `x` flows
through the smooth Hom-section `♯`, NOT through any non-`∇₀`-parallel ambient frame. -/
noncomputable def modelDoubleTrace (s : ℕ) (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) :
    Tensor0SBundle.Tensor0SModel (s + 2) ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel s ℝ E :=
  ∑ k : Fin (Module.finrank ℝ E),
    (Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s ((Module.finBasis ℝ E) k)).comp
      (Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) (s + 1)
        (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))))

set_option linter.unusedSectionVars false in
/-- **Defining evaluation of the model `g₀⁻¹` double trace.**  `modelDoubleTrace s L D` evaluated on a
`Fin s`-tuple `m` reads, for each internal model basis index `k`, the cometric-raised covector `L b^k`
into the leading model slot and the dual basis vector `b_k` into the new leading slot:
```
modelDoubleTrace s L D m = ∑ₖ D (Fin.cons (L b^k) (Fin.cons b_k m)).
```
Definitional, through the leading-slot interior-product evaluations (`model_interior_product` reads its
vector into the leading slot). -/
theorem modelDoubleTrace_apply (s : ℕ) (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel (s + 2) ℝ E) (m : Fin s → E) :
    modelDoubleTrace (E := E) s L D m =
      ∑ k : Fin (Module.finrank ℝ E),
        D (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) m)) := by
  classical
  rw [modelDoubleTrace]
  simp only [ContinuousLinearMap.sum_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousLinearMap.comp_apply]
  rfl

/-- **The fibrewise `−2` intrinsic `g₀⁻¹` double-trace fibre operator.**  At a base point `x`, the
`−2`-scaled genuine cometric double trace `modelDoubleTrace (2 + a) (cometricLmodel g₀ x)` of the two
leading covariant slots (raise slot `0` by the smooth cometric `♯`, then the FRAME-FREE natural trace
against the original slot — giving ONE inverse, `D : g₀⁻¹`), transported through the fibre/model
continuous-linear equivalence `tensor0SSpace_continuousLinearEquiv`: a continuous-linear map between
tensor fibres `Tensor0SSpace (4 + a) I x →L Tensor0SSpace (2 + a) I x`, i.e. a `(0, 4 + a) → (0, 2 + a)`
fibre map (the slot counts `4 + a = (2 + a) + 2` are definitional).  It reads only the fibre value `D(x)`
(value-local) and depends on the background metric `g₀` only through the SMOOTH cometric Hom-section
`inverseMetricSharpField`; NO chart-selected, non-`∇₀`-parallel ambient basis enters the smoothness. -/
noncomputable def ricciModelTrace42Fib (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    Tensor0SBundle.Tensor0SSpace (4 + a) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a) I x :=
  (-2 : ℝ) •
    (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (2 + a) x).symm.toContinuousLinearMap.comp
      ((modelDoubleTrace (E := E) (2 + a) (cometricLmodel (I := I) g₀ x)).comp
        ((modelRankCast (E := E) (by omega : (4 + a) = (2 + a) + 2)).comp
          (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (4 + a) x).toContinuousLinearMap))

set_option linter.unusedSectionVars false in
/-- **The model image of the fibre operator is the `−2` intrinsic cometric double trace.**  `toModel`
intertwines `ricciModelTrace42Fib` with the model-level `−2 • modelDoubleTrace` against the cometric
raise:
`toModel (ricciModelTrace42Fib g₀ a x D) = (-2) • modelDoubleTrace (2 + a) (cometricLmodel g₀ x) (toModel D)`.
Definitional, since `Tensor0SSpace.toModel = tensor0SSpace_continuousLinearEquiv` and the equivalence is
`id`. -/
@[simp] theorem ricciModelTrace42Fib_toModel (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace (4 + a) I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (ricciModelTrace42Fib (I := I) g₀ a x D) =
      (-2 : ℝ) • modelDoubleTrace (E := E) (2 + a) (cometricLmodel (I := I) g₀ x)
        (modelRankCast (E := E) (by omega : (4 + a) = (2 + a) + 2)
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := rfl

/-- **The model raise of the leading covariant slot by a cometric `L : Tensor0SModel 1 → E`,
`(0, s + 2) → (1, s + 1)`.**  Feeding a model covector `β` into the contravariant slot of
`raiseSlot0ModelL s L D` reads the `L`-raised vector `L β` into the leading covariant slot of the
`(0, s + 2)`-tensor `D`: `raiseSlot0ModelL s L D β = model_interior_product (s + 1) (L β) D`.  This
is the frame-free index-raise feeding the model double trace's natural contraction; no internal frame
enters (only the variable covector slot `β`). -/
noncomputable def raiseSlot0ModelL (s : ℕ) (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) :
    Tensor0SBundle.Tensor0SModel (s + 2) ℝ E →L[ℝ] Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E :=
  ContinuousLinearMap.flip
    ((Tensor0SBundle.model_interior_bilinear ℝ E (s + 1)).comp L)

set_option linter.unusedSectionVars false in
/-- Defining evaluation of `raiseSlot0ModelL`. -/
@[simp] theorem raiseSlot0ModelL_apply (s : ℕ) (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel (s + 2) ℝ E) (β : Tensor0SBundle.Tensor0SModel 1 ℝ E) :
    raiseSlot0ModelL (E := E) s L D β =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) (s + 1) (L β) D := rfl

set_option linter.unusedSectionVars false in
/-- **The model double trace is the natural trace of the cometric-raised slot.**  Evaluating the
frame-free natural trace `model_contract_trace 0 s` of the cometric-raised tensor `raiseSlot0ModelL s L D`
at the unit `(0, 0)`-tensor recovers the model double trace `modelDoubleTrace s L D`.  The two
expressions are termwise equal over the internal model basis: the trace's contravariant pre-contraction
against the dual basis covector `b^i` (tensored with the unit) selects `raiseSlot0ModelL s L D (b^i) =
model_interior_product (s + 1) (L b^i) D`, and the covariant post-contraction against `b_i` is the outer
`model_interior_product s (b_i)`. -/
theorem model_contract_trace_raiseSlot0ModelL (s : ℕ)
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel (s + 2) ℝ E) :
    (Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) 0 s (raiseSlot0ModelL (E := E) s L D))
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
      modelDoubleTrace (E := E) s L D := by
  classical
  apply ContinuousMultilinearMap.ext
  intro m
  rw [Tensor0SBundle.model_contract_trace_apply_basis (Module.finBasis ℝ E) 0 s
    (raiseSlot0ModelL (E := E) s L D)
    (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) m,
    modelDoubleTrace_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- unit reduction: model_tensorWithCovector_first 0 (covOf (coord i)) unit0 = covOf (coord i)
  have htw : Tensor0SBundle.model_tensorWithCovector_first (𝕜 := ℝ) (E := E) 0
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)))
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
      Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    rw [Tensor0SBundle.model_tensorWithCovector_first, LinearMap.coe_toContinuousLinearMap']
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Bundle.continuousMultilinearMap.modelProduct_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, mul_one,
      Tensor0SBundle.model_covectorOfCLM_apply, Tensor0SBundle.model_covectorOfCLM_apply]
    rfl
  rw [htw, raiseSlot0ModelL_apply]
  -- both sides are `D (Fin.cons (L (covOf …)) (Fin.cons (finBasis i) m))`, the interior products
  -- reading the inserted vectors into the two leading slots (definitional)
  rw [show ((Module.finBasis ℝ E).cDualBasis i) =
      LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i) from by
        rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
        congr 1
        exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) i]
  rfl

/-- **The fibrewise cometric raise of the leading covariant slot, `(0, s + 2) → (1, s + 1)`.**  At a base
point `x` the index-raise of the leading covariant slot by the cometric `♯ = inverseMetricSharpFib g₀ x`:
the model-level `raiseSlot0ModelL` against the cometric reading `cometricLmodel g₀ x`, transported through
the fibre/model continuous-linear equivalences.  Feeding a covector `β` into its contravariant slot reads
the raised vector `♯ β` into the leading slot of the `(0, s + 2)`-tensor.  It depends on `g₀` only through
the SMOOTH cometric Hom-section, NO chart-selected ambient frame. -/
noncomputable def cometricRaiseSlot0Fib (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    Tensor0SBundle.Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SBundle.TensorRSSpace 1 (s + 1) I x :=
  (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 1 (s + 1) x).symm.toContinuousLinearMap.comp
    ((raiseSlot0ModelL (E := E) s (cometricLmodel (I := I) g₀ x)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (s + 2) x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in
/-- The model image of `cometricRaiseSlot0Fib` is `raiseSlot0ModelL` against the cometric reading. -/
@[simp] theorem cometricRaiseSlot0Fib_toModel (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace (s + 2) I x) :
    Tensor0SBundle.TensorRSSpace.toModel (cometricRaiseSlot0Fib (I := I) g₀ s x D) =
      raiseSlot0ModelL (E := E) s (cometricLmodel (I := I) g₀ x)
        (Tensor0SBundle.Tensor0SSpace.toModel D) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The cometric raise of a fixed smooth `(0, s + 2)`-field is a smooth `(1, s + 1)`-field.**  For a
smooth `(0, s + 2)`-tensor field `Y` (presented as the smooth total-space map `hY`), the section
`x ↦ cometricRaiseSlot0Fib g₀ s x (Y x)` is a smooth section of the `(1, s + 1)`-tensor bundle.  By
`contMDiff_clm_section_of_pointwise` (over the contravariant covector slot `Tensor0SSpace 1`) it suffices
that for every smooth covector field `β` the section `x ↦ (cometricRaiseSlot0Fib g₀ s x (Y x)) (β x)` is
smooth; that value is the bundle interior product of `Y` with the smooth vector field `x ↦ ♯ (β x)`
(`contract_Tensor0SField`, smooth), where `♯` is the globally-smooth cometric Hom-section
`inverseMetricSharpField` applied to the *variable* covector `β` (`ContMDiff.clm_bundle_apply`), NEVER `♯`
of a constant frame. -/
theorem cometricRaiseSlot0Fib_section_contMDiff (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Y : ∀ x : M, Tensor0SBundle.Tensor0SSpace (s + 2) I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 2) I z) x (Y x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (s + 1) I z) x
        (cometricRaiseSlot0Fib (I := I) g₀ s x (Y x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel (s + 1) ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (s + 1) I x)
    (φ := fun x => (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + 1) I x from
      cometricRaiseSlot0Fib (I := I) g₀ s x (Y x)))
  intro β
  -- the smooth raised vector field x ↦ ♯ (β x)
  have hsharpβ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (inverseMetricSharpFib (I := I) g₀ x (β x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (inverseMetricSharpField_contMDiff (I := I) g₀) β.contMDiff
  let sharpβ : ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
    ⟨fun x : M => inverseMetricSharpFib (I := I) g₀ x (β x), hsharpβ⟩
  -- the interior product of Y with the smooth vector field ♯β is smooth (C^∞ interior-product field)
  have hcontract := interiorProductField_contMDiff (I := I) (s + 1) (fun x => Y x) hY sharpβ
  refine hcontract.congr (fun x => ?_)
  -- the fibre value (cometricRaiseSlot0Fib (Y x)) (β x) equals the interior product of Y with ♯β at x
  change TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) x (sharpβ x) (Y x)) =
    TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x
      ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + 1) I x from
        cometricRaiseSlot0Fib (I := I) g₀ s x (Y x)) (β x))
  -- the interior product fibre value equals the raise applied to `β x` (both are
  -- `model_interior_product (s+1) (♯(β x)) (toModel (Y x))`, definitional through the identity equivs)
  congr 1

set_option linter.unusedSectionVars false in
/-- **The bundle frame-free trace at the unit reads as the model trace at the unit.**  For a
`(1, s + 1)`-tensor `T` at `x`, the model image of the bundle natural trace `contract_trace 0 s x T`
evaluated at the unit `(0, 0)`-section is the model natural trace `model_contract_trace 0 s` of the model
image of `T`, evaluated at the unit `(0, 0)`-model-tensor.  This bridges the `(0, s)`-as-`Hom(scalar, ·)`
realisation of the bundle trace to the direct `(0, s)` model trace.  Definitional through the
`tensorRSSpace`/`tensor0SSpace` identity equivalences and `contract_trace_apply`. -/
theorem contract_trace_unitZero_toModel (s : ℕ) (x : M)
    (T : Tensor0SBundle.TensorRSSpace 1 (s + 1) I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 s x T)
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      (Tensor0SBundle.model_contract_trace (𝕜 := ℝ) (E := E) 0 s
          (Tensor0SBundle.TensorRSSpace.toModel T))
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) := by
  rw [Tensor0SBundle.contract_trace]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the intrinsic `g₀⁻¹` double-trace operator field, routed through
the smooth cometric Hom-section.**  The fibre field `x ↦ ricciModelTrace42Fib g₀ a x` is a smooth
section of the `(4 + a, 2 + a)`-tensor bundle.  The fibre map is the `−2`-scaled genuine cometric double
trace of the two leading covariant slots (raise slot `0` by the cometric `♯`, then the FRAME-FREE natural
trace against the original slot, `modelDoubleTrace`).

Its smoothness is genuinely intrinsic and routes through the **globally-smooth cometric Hom-bundle
section** `inverseMetricSharpField` (`inverseMetricSharpField_contMDiff`), with **NO** chart-selected,
non-`∇₀`-parallel ambient frame and **NO** single-trivialization `symmL` factor.  The route is the
structural raise-then-natural-trace: by `contMDiff_clm_section_of_pointwise` it suffices that for every
smooth `(0, 4 + a)`-field `Y` the section `x ↦ ricciModelTrace42Fib g₀ a x (Y x)` is smooth; that is
`(−2) •` the FRAME-FREE natural trace (`contract_TensorRSField`, smooth) of the smooth raised
`(1, 3 + a)`-field `x ↦ raise_♯ (slot 0) (Y x)` — and the raise is smooth because `♯` enters as the
smooth Hom-section `inverseMetricSharpField` applied to the *variable* slot argument (an inner
`contMDiff_clm_section_of_pointwise`, per smooth covector field `β`: the interior product
`contract_Tensor0SField` of `Y` against the smooth vector field `x ↦ ♯(β x)`, `ContMDiff.clm_bundle_apply`
of `inverseMetricSharpField` on `β`), NEVER as `♯` of a constant model frame.  It is **non-vacuous** (the
genuine cometric double-trace operator field, smooth, not the zero field). -/
theorem ricciModelTrace42Fib_contMDiff (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel (4 + a) (2 + a) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel (4 + a) (2 + a) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace (4 + a) (2 + a) I z) x
        (ricciModelTrace42Fib (I := I) g₀ a x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel (4 + a) ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace (4 + a) I x)
    (F₂ := Tensor0SBundle.Tensor0SModel (2 + a) ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (2 + a) I x)
    (φ := fun x => ricciModelTrace42Fib (I := I) g₀ a x)
  intro Y
  -- The rank-cast of `Y` to a `(0, (2 + a) + 2)`-field (a fixed model CLM, smoothness-preserving).
  let Y' : ∀ x : M, Tensor0SBundle.Tensor0SSpace ((2 + a) + 2) I x :=
    fun x => Tensor0SBundle.Tensor0SSpace.ofModel
      (modelRankCast (E := E) (by omega : (4 + a) = (2 + a) + 2)
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))
  have hY' : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel ((2 + a) + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel ((2 + a) + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace ((2 + a) + 2) I z) x (Y' x)) :=
    tensor0SField_castRank_contMDiff (I := I) (by omega : (4 + a) = (2 + a) + 2) (fun x => Y x) Y.contMDiff
  -- The smooth raise of `Y'`.
  have hraise := cometricRaiseSlot0Fib_section_contMDiff (I := I) g₀ (2 + a) Y' hY'
  -- The frame-free trace of the raise (smooth `(0, 2 + a)`-field), via the C^∞ trace-field smoothness.
  have htrace := contractTraceField_contMDiff (I := I) 0 (2 + a)
    (fun x => cometricRaiseSlot0Fib (I := I) g₀ (2 + a) x (Y' x)) hraise
  have htraceUnit : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (2 + a) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (2 + a) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (2 + a) I z) x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a) I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 (2 + a) x
            (cometricRaiseSlot0Fib (I := I) g₀ (2 + a) x (Y' x)))
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    ContMDiff.clm_bundle_apply (b := id) htrace
      (Integral.Connection.unitZeroSec (I := I) (M := M)).contMDiff
  -- Scale by `-2`.
  have hscaled : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (2 + a) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (2 + a) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (2 + a) I z) x
        ((-2 : ℝ) • ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (2 + a) I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 (2 + a) x
            (cometricRaiseSlot0Fib (I := I) g₀ (2 + a) x (Y' x)))
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) :=
    ContMDiff.const_smul_section (a := (-2 : ℝ)) htraceUnit
  refine hscaled.congr (fun x => ?_)
  -- the matching fibre identity: ricciModelTrace42Fib g₀ a x (Y x) = (-2) • trace(raise Y')(unit)
  congr 1
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [ricciModelTrace42Fib_toModel, Tensor0SBundle.Tensor0SSpace.toModel_smul]
  congr 1
  -- modelDoubleTrace (2+a) (cometricLmodel g₀ x) (modelRankCast (toModel (Y x)))
  --   = toModel ((contract_trace 0 (2+a) x (raise (Y' x))) (unit0))
  rw [← model_contract_trace_raiseSlot0ModelL (E := E) (2 + a) (cometricLmodel (I := I) g₀ x)
    (modelRankCast (E := E) (by omega : (4 + a) = (2 + a) + 2)
      (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))]
  -- relate the bundle-level trace-at-unit to the model-level trace-at-unit; the model image of the
  -- raise is `raiseSlot0ModelL` against the cometric reading on the rank-cast `toModel (Y x)`
  -- (`cometricRaiseSlot0Fib_toModel`, `Y'` definitional), closing the match.
  rw [contract_trace_unitZero_toModel (I := I) (2 + a) x
    (cometricRaiseSlot0Fib (I := I) g₀ (2 + a) x (Y' x))]
  congr 1

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
