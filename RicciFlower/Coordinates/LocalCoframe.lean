import RicciFlower.Coordinates.Tensor
import RicciFlower.VectorBundle.Frame
import RicciFlower.Tensor.RSTensor.LocalFrameRegularity

/-!
# Local coframes from tangent trivializations

This file records the small coordinate/tensor facts needed to turn a
trivialization-induced local frame into the corresponding smooth dual coframe.
It is kept below the HCG approximate-isometry layer.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace RicciFlower
namespace Coordinates

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- On the tangent-trivialization domain, a fixed tensor-bundle basis section
`Tensor0SSpace.constInChart` is the basis tensor of the local frame induced by
the same tangent trivialization and model basis. -/
theorem constInChart_eq_basis0S_trivFrame
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r : Nat}
    (x₀ : M) (b : Module.Basis Idx 𝕜 E)
    {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet)
    (slots : Fin r -> Idx) :
    Tensor0SBundle.Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) r x₀
        ((Tensor0SBundle.continuousMultilinearMapBasis
          (𝕜 := 𝕜) (V := E) b r) slots) x =
      Tensor0SBundle.basisTensor0S (I := I)
        ((trivializationAt E (TangentSpace I : M -> Type _) x₀).basisAt b hx)
        slots := by
  classical
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  rw [Tensor0SBundle.Tensor0SSpace.constInChart]
  rw [Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
    (F := E) (E := TangentSpace I) x₀ x hx]
  ext v
  have hlin (w : TangentSpace I x) :
      (Trivialization.linearMapAt 𝕜 (trivializationAt E (TangentSpace I) x₀) x) w =
        (trivializationAt E (TangentSpace I) x₀ ⟨x, w⟩).2 := by
    change (trivializationAt E (TangentSpace I) x₀).linearMapAt 𝕜 x w = _
    rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
  simp [Tensor0SBundle.basisTensor0S, Tensor0SBundle.tensor0SBasis,
    Tensor0SBundle.continuousMultilinearMapBasis_apply,
    Tensor0SBundle.continuousMultilinearMapBasisElem,
    Tensor0SBundle.coframeOfBasis,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Bundle.Trivialization.continuousLinearMapAt_apply,
    Bundle.Trivialization.basisAt, hlin]

/-- A chart-constant covector from the tangent trivialization is dual to the
local frame induced by the same trivialization and model basis. -/
theorem constInChart_one_eval_trivFrame
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (x₀ : M) (b : Module.Basis Idx 𝕜 E)
    {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet)
    (i j : Idx) :
    Tensor0SBundle.Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) 1 x₀
        ((Tensor0SBundle.continuousMultilinearMapBasis
          (𝕜 := 𝕜) (V := E) b 1) (fun _ : Fin 1 => i)) x
        (fun _ : Fin 1 =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).localFrame b j x)
      = if j = i then 1 else 0 := by
  classical
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  rw [constInChart_eq_basis0S_trivFrame (𝕜 := 𝕜) (I := I) (M := M)
    (Idx := Idx) (r := 1) x₀ b hx (fun _ : Fin 1 => i)]
  rw [Tensor0SBundle.basisTensor0S_apply]
  rw [e.localFrame_apply_of_mem_baseSet (b := b) (i := j) hx]
  have hround : (e ⟨x, e.symm x (b j)⟩ : M × E).2 = b j := by
    exact congrArg Prod.snd (e.apply_mk_symm hx (b j))
  simp [Bundle.Trivialization.basisAt, Finsupp.single_apply, hround, e]

/-- Eventual pairing form of `constInChart_one_eval_trivFrame`: if smooth
sections `Z j` realize the trivialization-induced local frame near `x₀`, then
the chart-constant dual covector pairs with them as the Kronecker delta. -/
theorem constInChart_one_pair_eventually_trivFrame
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (x₀ : M) (b : Module.Basis Idx 𝕜 E)
    (Z : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hZ : ∀ j : Idx,
      (fun y : M => Z j y) =ᶠ[𝓝 x₀]
        fun y : M =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).localFrame b j y)
    (i j : Idx) :
    (fun y : M =>
        Tensor0SBundle.Tensor0SSpace.constInChart
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1 x₀
          ((Tensor0SBundle.continuousMultilinearMapBasis
            (𝕜 := 𝕜) (V := E) b 1) (fun _ : Fin 1 => i)) y
          (fun _ : Fin 1 => Z j y)) =ᶠ[𝓝 x₀]
      fun _ : M => if j = i then (1 : 𝕜) else 0 := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hx₀ : x₀ ∈ e.baseSet := by
    exact mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x₀
  filter_upwards [hZ j, e.open_baseSet.mem_nhds hx₀] with y hZy hy
  rw [hZy]
  exact constInChart_one_eval_trivFrame
    (𝕜 := 𝕜) (I := I) (M := M) x₀ b (by simpa [e] using hy) i j

section Real

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    [FiniteDimensional Real F]
  {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners Real F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
    [T2Space N]

/-- The local frame induced by a tangent trivialization admits global smooth
section extensions which agree with it near the center. -/
theorem existsTrivFrameSec
    {Idx : Type*}
    (x₀ : N) (b : Module.Basis Idx Real F) :
    ∃ Z : Idx -> ContMDiffSection J F (∞ : WithTop ℕ∞)
        (TangentSpace J : N -> Type _),
      ∀ j : Idx,
        (fun y : N => Z j y) =ᶠ[𝓝 x₀]
          fun y : N =>
            (trivializationAt F (TangentSpace J : N -> Type _) x₀).localFrame b j y := by
  let e := trivializationAt F (TangentSpace J : N -> Type _) x₀
  have hx₀ : x₀ ∈ e.baseSet :=
    mem_baseSet_trivializationAt F (TangentSpace J : N -> Type _) x₀
  let hframe := e.isLocalFrameOn_localFrame_baseSet J (∞ : WithTop ℕ∞) b
  obtain ⟨Z, hZ⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet hx₀
  refine ⟨Z, fun j => ?_⟩
  exact hZ.mono fun _ hy => hy j

/-- Combined local-frame section and dual-pairing producer for a tangent
trivialization.  The one-form here is still the supplied chart-constant
covector; a later wrapper may extend that covector to a global tensor field. -/
theorem existsTrivFramePair
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (x₀ : N) (b : Module.Basis Idx Real F) :
    ∃ Z : Idx -> ContMDiffSection J F (∞ : WithTop ℕ∞)
        (TangentSpace J : N -> Type _),
      (∀ j : Idx,
        (fun y : N => Z j y) =ᶠ[𝓝 x₀]
          fun y : N =>
            (trivializationAt F (TangentSpace J : N -> Type _) x₀).localFrame b j y) ∧
      (∀ i j : Idx,
        (fun y : N =>
          Tensor0SBundle.Tensor0SSpace.constInChart
            (𝕜 := Real) (E := F) (H := G) (I := J) (M := N) 1 x₀
            ((Tensor0SBundle.continuousMultilinearMapBasis
              (𝕜 := Real) (V := F) b 1) (fun _ : Fin 1 => i)) y
            (fun _ : Fin 1 => Z j y)) =ᶠ[𝓝 x₀]
          fun _ : N => if j = i then (1 : Real) else 0) := by
  obtain ⟨Z, hZ⟩ := existsTrivFrameSec (J := J) x₀ b
  refine ⟨Z, hZ, fun i j => ?_⟩
  exact constInChart_one_pair_eventually_trivFrame
    (𝕜 := Real) (I := J) (M := N) x₀ b Z hZ i j

end Real

end

end Coordinates
end RicciFlower
