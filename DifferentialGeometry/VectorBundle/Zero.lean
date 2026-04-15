/-
Authors: Jack McCarthy
-/
import Mathlib.Topology.VectorBundle.Basic

/-!
# Continuity of the Zero Section

The zero section `zeroSection F E : B → TotalSpace F E` of a vector bundle is continuous.

## Main Results

* `continuous_zeroSection`: the zero section of a vector bundle is continuous.

## Tags

zero section, vector bundle, continuous
-/

open Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- The zero section of a vector bundle is continuous.

By `FiberBundle.continuousAt_totalSpace`, it suffices to check at each `x₀` that:
1. The projection `fun x => x` is continuous — trivial.
2. The fiber component `fun x => (trivializationAt F E x₀ ⟨x, 0⟩).2` is continuous at `x₀`.

For (2), `Trivialization.zeroSection` gives `(e ⟨x, 0⟩) = (x, 0)` for `x ∈ e.baseSet`,
so the fiber component is locally the constant `0`. -/
theorem continuous_zeroSection (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {B : Type*} [TopologicalSpace B]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] :
    Continuous (zeroSection F E) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  -- The fiber component (trivializationAt F E x₀ ⟨x, 0⟩).2 is locally 0, hence continuous
  set e := trivializationAt F E x₀
  have hmem : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F E x₀
  have hbase : e.baseSet ∈ nhds x₀ := e.open_baseSet.mem_nhds hmem
  -- Show the function is eventually equal to the constant function at its value at x₀
  apply Filter.Tendsto.congr'
  · change ∀ᶠ x in nhds x₀, (fun _ => (e (zeroSection F E x₀)).2) x =
        (fun x => (e (zeroSection F E x)).2) x
    filter_upwards [hbase] with x hx
    rw [e.zeroSection (R := 𝕜) hmem, e.zeroSection (R := 𝕜) hx]
  · exact tendsto_const_nhds
