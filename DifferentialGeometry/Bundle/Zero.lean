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

/-!

# Vector Bundle Charactarization Lemma

Let E₁, E₂ be two ContMDiffVector bundles over a smooth manifold M. Let Γ(E₁), Γ(E₂) denote the space of smooth sectons.
Claim: A map F : Γ(E₁) → Γ(E₂) is smooth is linear over C^n(M) if and only if there exists a ContMDiffVectorBundleMap f : E₁ → E₂ such that F(σ) = f ∘ σ

Proof: One direction is obvious. Any ContMDiffVectorBundleMap immediately induces a map on Γ(E₁) → Γ(E₂) which is linear over C^n(M).
Converselt, suppose F : Γ(E₁) → Γ(E₂) is linear over C^n(M)
1. F acts locally: If σ₁ = σ₂ in some open subset U ⊆ M, then F(σ₁) = F(σ₂) in U
  - Let τ = σ₁ - σ₂. By assumption, t vanishes in U and suffices to show that F(τ) vanishes in U.
  - Let p ∈ U, and choose ψ ∈ C^n(M) to be a smooth bump function supported in U and ψ(p) = 1.
  - Then ψ • τ = 0 on all of M, so ψ*F(τ) = F(ψ • τ) = F(0) = 0 by linearity.
  - Evaluating at p gives F(τ)(p) = ψ(p)*F(τ)(p) = 0, which proves F(τ) vanishes on U since this holds for any p ∈ U.
2. F acts pointwise: If σ₁(p) = σ₂(p) then F(σ₁)(p) = F(σ₂)(p).
  - Let τ = σ₁ - σ₂, and we assume that τ(p) = 0. We want to show that F(τ)(p) = 0
  - Let (σ₁, ..., σₖ) by a smooth local frame for E₁ on a neighborhood U of p, then. we can write τ = Σ uⁱ•σᵢ for some uⁱ ∈ C^n(M).
  - Since τ(p) = 0, we must have u¹(p) = ... = uᵏ(p) = 0.
  - By smooth extension to all of M, there exist smooth sections σᵢ' ∈ Γ(E₁) which agree with σᵢ on a neighborhood of p, and smooth functions uⁱ' which agree with uⁱ (Hint: Take a bump function at p).
  - In particular, each uⁱ'(p) = 0.
  - Then τ = ∑ uⁱ'•σᵢ' on a neighbordhood of p, and we have F(τ)(p) = F(∑ uⁱ'•σᵢ')(p) = ∑ uⁱ'(p)*F(σᵢ')(p) = 0.
3. We now finally define the required ContMDiffBundleMap f : E₁ → E₂ as follows:
  - For any ⟨p,v⟩ ∈ E₁, we define f(⟨p,v⟩) = F(v')(p) ∈ E₂, where v' ∈ Γ(E₁) any smooth global section with v'(p) = ⟨p,v⟩.
  - By part 2,the value F(v')(p) is independent of the particular choice of section.
  - The map f clearly satisfies π₂ ∘ f = π₁ and f ∘ σ = F(σ) by definition.
  - The map f is linear on fibers because F is linear on fibers, so it commutes with addition and scalar multiplication immediately.
4. f is smooth
  - Let p ∈ M and (σ₁, ..., σₖ) be a local frame for E₁ on a neighborhood of p.
  - As in step 2, we can extend this to glocal sections  σᵢ' ∈ Γ(E₁) with σᵢ' = σᵢ on a neighborhood U of p.
  - Shrinking U further if necessary, we may assume that there exists a local frame (τ₁, ..., τₘ) on E' over U.
  - Then since F(σᵢ') ∈ Γ(E₂), there must exist smooth function Aᵢʲ ∈ C^n(U) with F(σᵢ')(p) = ∑ i, Aᵢʲ•τⱼ on U.
  - Let ⟨q,v⟩ ∈ E₁ with q ∈ U, then ⟨q,v⟩ = ∑ vⁱ * σᵢ(q) for some v¹, ..., vᵏ ∈ 𝕜. Then,
  - F(⟨q,v⟩) = F(∑ vⁱ * σᵢ(q)) = F(∑ vⁱ * σᵢ'(q)) = ∑ vⁱ * F(σᵢ'(q)) = ∑ vⁱ * Aᵢʲ(q) * τⱼ(q)
  - Thus, if we tkae e₁, e₂ to be the local frames associated to (σ₁, ..., σₖ) and (τ₁, ..., τₘ) respectively, we get:
  - e₂ ∘ f ∘ e₁.symm (⟨q, (v¹, ..., vᵏ)⟩) = (q, (∑ Aᵢ¹(1)vⁱ, ..., ∑ Aᵢᵐ(q) vⁱ)) which is smooth since A is smooth.
  - Then since e₂ and e₁ are local diffeomorphisms, it follows that f is smooth on π₁⁻¹(U).
-/
