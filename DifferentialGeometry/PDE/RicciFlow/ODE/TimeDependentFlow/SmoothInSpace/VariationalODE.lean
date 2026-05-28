import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.BanachIC
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The Euclidean variational (linearized-flow) ODE from a jointly `C^∞` flow

For a time-dependent vector field `f : ℝ → E → E` on a finite-dimensional Banach
space `E`, jointly `C^∞` in `(t, x)`, `exists_isLocalFlow_contDiffOn_top`
(`SmoothInSpace/BanachIC.lean`) produces a local Picard–Lindelöf flow `Φ : E × ℝ → E`
together with a strictly interior open neighbourhood
`ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)` on which `Φ` is jointly `C^∞`.

This file extracts from that flow the **variational / linearized-flow ODE** for the
spatial Fréchet derivative `s ↦ D_x Φ(·, s)`.  Writing
`Dx s := fderiv ℝ (fun y => Φ (y, s)) x` and `A s := fderiv ℝ (f s) (Φ (x, s))`, the
result is

  `HasDerivAt (fun s => Dx s) ((A s).comp (Dx s)) s`

at every strictly interior `(x, s)`, i.e. `∂_s (D_x Φ) = (D_y f)(s, Φ) · (D_x Φ)`.

## Proof idea

The flow ODE clause of `IsLocalFlow` gives `∂_s Φ(x, s) = f(s, Φ(x, s))`.  Since `Φ`
is jointly `C^∞` (hence `C^2`), its second Fréchet derivative is symmetric (Clairaut,
`ContDiffAt.isSymmSndFDerivAt`).  Symmetry swaps a spatial derivative past a temporal
one:

* `∂_s (D_x Φ · δ) = fderiv (fderiv Φ) (x,s) (inl δ) (inr 1)` (differentiate the
  spatial slice in time);
* `fderiv (fderiv Φ) (x,s) (inr 1) (inl δ) = D_x (∂_s Φ) · δ
    = D_x (f(s, Φ)) · δ = (A s) (Dx s δ)` (differentiate the flow ODE in space, chain
  rule on the moving point `Φ`).

Clairaut equates the two, giving the per-direction variational ODE; a
`ContinuousLinearMap.ext` over `δ` repackages it as the operator-valued statement.

The only joint-`C^∞` hypothesis is `ContDiff ℝ ∞ (uncurry f)` on the **model space**
`E`; this is exactly the input consumed by `exists_isLocalFlow_contDiffOn_top`.

## Main results

* `IsLocalFlow.hasDerivAt_partial_spatial_fderiv_apply`: the per-direction (`δ`)
  variational ODE.
* `IsLocalFlow.hasDerivAt_partial_spatial_fderiv`: the operator-valued variational ODE
  (the headline).

## Status of the manifold lift

The manifold-level identity `RawVariationalIdentity` (in
`TimeDependentFlow/VariationalFlow.lean`) is *not* derived here; the precise chart-lift
and connection-reconciliation that would close that gap are documented at the end of
this file.
-/

noncomputable section

namespace DifferentialGeometry.Analysis.ODE.Flow

open Set Metric Function ContinuousLinearMap
open scoped Topology NNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-! ## Partial-derivative bookkeeping

Two elementary identities relate the partial Fréchet derivatives of `Φ` to the joint
derivative `fderiv ℝ Φ (x, s)` and to the vector field `f`. -/

/-- The affine line `r ↦ x + r • δ` has derivative `δ` at `0`. -/
private theorem hasDerivAt_line (x δ : E) :
    HasDerivAt (fun rr : ℝ => x + rr • δ) δ 0 := by
  have h1 : HasDerivAt (fun rr : ℝ => rr • δ) δ 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const δ
  have h2 : HasDerivAt (fun rr : ℝ => x + rr • δ) (0 + δ) 0 :=
    (hasDerivAt_const (0 : ℝ) x).add h1
  simpa using h2

/-- **Spatial partial derivative as the joint derivative precomposed with `inl`.**

Wherever `Φ` is differentiable at `(x, s)`, the Fréchet derivative of the spatial slice
`fun y => Φ (y, s)` at `x` is `(fderiv ℝ Φ (x, s)).comp (inl ℝ E ℝ)`. -/
theorem partial_spatial_fderiv_eq_comp_inl
    {x : E} {s : ℝ} (hΦdiff : DifferentiableAt ℝ Φ (x, s)) :
    fderiv ℝ (fun y => Φ (y, s)) x
      = (fderiv ℝ Φ (x, s)).comp (ContinuousLinearMap.inl ℝ E ℝ) := by
  have hslice : HasFDerivAt (fun y => Φ (y, s))
      ((fderiv ℝ Φ (x, s)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x :=
    hΦdiff.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x s)
  exact hslice.fderiv

/-- **Joint derivative on the time direction equals the vector field along the orbit.**

At an interior time `s ∈ Ioo tmin tmax` and a spatial point `x ∈ closedBall x₀ r`, the
joint Fréchet derivative of `Φ` evaluated on the unit time direction `(0, 1) = inr 1`
equals `f s (Φ (x, s))`, by the flow-ODE clause of `IsLocalFlow`. -/
theorem flow_joint_fderiv_inr_eq
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {x : E} {s : ℝ} (hx : x ∈ closedBall x₀ r) (hs : s ∈ Ioo tmin tmax)
    (hΦdiff : DifferentiableAt ℝ Φ (x, s)) :
    fderiv ℝ Φ (x, s) (ContinuousLinearMap.inr ℝ E ℝ 1) = f s (Φ (x, s)) := by
  -- The orbit `s ↦ Φ (x, s)` has the joint-derivative description of its time slope.
  have hcurve : HasDerivAt (fun u => Φ (x, u))
      (fderiv ℝ Φ (x, s) (ContinuousLinearMap.inr ℝ E ℝ 1)) s := by
    have hcomp : HasDerivAt (fun u : ℝ => (x, u)) (ContinuousLinearMap.inr ℝ E ℝ 1) s := by
      have : HasDerivAt (fun u : ℝ => (x, u)) ((0 : E), (1 : ℝ)) s := by
        simpa using (hasDerivAt_const s x).prodMk (hasDerivAt_id s)
      simpa [ContinuousLinearMap.inr_apply] using this
    exact hΦdiff.hasFDerivAt.comp_hasDerivAt s hcomp
  -- The flow-ODE clause gives the orbit derivative as `f s (Φ (x, s))`.
  have hflow : HasDerivAt (fun u => Φ (x, u)) (f s (Φ (x, s))) s := by
    have hwithin := hΦ.hasDerivWithinAt x hx s (Ioo_subset_Icc_self hs)
    exact hwithin.hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  exact hcurve.unique hflow

/-! ## The per-direction variational ODE (Clairaut step)

The genuine analytic content: differentiating the spatial slice in time and applying
the symmetry of the second derivative converts the time-derivative of `Dx · δ` into the
spatial derivative of the flow ODE, i.e. `(A s) (Dx s δ)`. -/

/-- Joint `C^∞` of `Φ` at every point of an open set `U` on which `Φ` is `C^∞`. -/
private theorem contDiffAt_of_mem {U : Set (E × ℝ)} (hUopen : IsOpen U)
    (hΦsmooth : ContDiffOn ℝ ∞ Φ U) {q : E × ℝ} (hq : q ∈ U) :
    ContDiffAt ℝ ∞ Φ q :=
  hΦsmooth.contDiffAt (hUopen.mem_nhds hq)

section PerDirection

variable (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
  (hf : ContDiff ℝ ∞ (uncurry f))
  {U : Set (E × ℝ)} (hUopen : IsOpen U)
  (hΦsmooth : ContDiffOn ℝ ∞ Φ U)

include hΦ hf hUopen hΦsmooth in
/-- **Per-direction variational ODE.**

Let `Φ` be a local flow of `f`, jointly `C^∞` on an open set `U`, with `(x, s) ∈ U`
strictly interior to the flow domain (`x ∈ ball x₀ r`, `s ∈ Ioo tmin tmax`).  Then for
every fixed direction `δ : E`, the path `u ↦ fderiv ℝ (fun y => Φ (y, u)) x δ` has
time-derivative
`fderiv ℝ (f s) (Φ (x, s)) (fderiv ℝ (fun y => Φ (y, s)) x δ)` at `s`. -/
theorem IsLocalFlow.hasDerivAt_partial_spatial_fderiv_apply
    {x : E} {s : ℝ} (hxsU : (x, s) ∈ U)
    (hx : x ∈ ball x₀ r) (hs : s ∈ Ioo tmin tmax) (δ : E) :
    HasDerivAt (fun u : ℝ => fderiv ℝ (fun y => Φ (y, u)) x δ)
      (fderiv ℝ (f s) (Φ (x, s)) (fderiv ℝ (fun y => Φ (y, s)) x δ)) s := by
  -- `Φ` is `C^∞` at every point of `U`; differentiable there.
  have hΦ_at : ∀ q ∈ U, ContDiffAt ℝ ∞ Φ q := fun q hq => contDiffAt_of_mem hUopen hΦsmooth hq
  have hΦ_xs : ContDiffAt ℝ ∞ Φ (x, s) := hΦ_at _ hxsU
  have hΦ_diffOn : ∀ q ∈ U, DifferentiableAt ℝ Φ q := fun q hq =>
    (hΦ_at q hq).differentiableAt (by simp)
  -- `fderiv ℝ Φ` is differentiable at `(x, s)`.
  have hone_one_le : (1 + 1 : WithTop ℕ∞) ≤ ∞ := by decide
  have hsndDiff : DifferentiableAt ℝ (fderiv ℝ Φ) (x, s) :=
    (hΦ_xs.fderiv_right (m := 1) hone_one_le).differentiableAt (by simp)
  have hsndHas : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) (x, s)) (x, s) :=
    hsndDiff.hasFDerivAt
  set B := fderiv ℝ (fderiv ℝ Φ) (x, s) with hB
  -- Clairaut: the second derivative is symmetric at `(x, s)`.
  have hsymm : IsSymmSndFDerivAt ℝ Φ (x, s) := by
    refine hΦ_xs.isSymmSndFDerivAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]; decide
  -- The two coordinate directions.
  set eX : E × ℝ := ContinuousLinearMap.inl ℝ E ℝ δ with heX
  set eT : E × ℝ := ContinuousLinearMap.inr ℝ E ℝ 1 with heT
  -- LHS: `∂_s (D_x Φ · δ)` via the time curve and the eval-at-`eX` CLM.
  have hcurveT : HasDerivAt (fun u : ℝ => (x, u)) eT s := by
    have : HasDerivAt (fun u : ℝ => (x, u)) ((0 : E), (1 : ℝ)) s := by
      simpa using (hasDerivAt_const s x).prodMk (hasDerivAt_id s)
    simpa [heT, ContinuousLinearMap.inr_apply] using this
  have hfderivCurve : HasDerivAt (fun u : ℝ => fderiv ℝ Φ (x, u)) (B eT) s :=
    hsndHas.comp_hasDerivAt s hcurveT
  have hslopeApply : HasDerivAt (fun u : ℝ => fderiv ℝ Φ (x, u) eX) (B eT eX) s := by
    have := (ContinuousLinearMap.apply ℝ E eX).hasFDerivAt.comp_hasDerivAt s hfderivCurve
    simpa [ContinuousLinearMap.apply_apply] using this
  -- The time path equals the spatial-slice path near `s` (on the open `u`-fibre of `U`).
  have hUx_open : IsOpen {u : ℝ | (x, u) ∈ U} := hUopen.preimage (by fun_prop)
  have hEvEq : (fun u : ℝ => fderiv ℝ Φ (x, u) eX)
      =ᶠ[𝓝 s] (fun u : ℝ => fderiv ℝ (fun y => Φ (y, u)) x δ) := by
    filter_upwards [hUx_open.mem_nhds (show s ∈ {u : ℝ | (x, u) ∈ U} from hxsU)] with u hu
    rw [partial_spatial_fderiv_eq_comp_inl (hΦ_diffOn _ hu)]
    simp [heX, ContinuousLinearMap.comp_apply]
  have hLHS :
      HasDerivAt (fun u : ℝ => fderiv ℝ (fun y => Φ (y, u)) x δ) (B eT eX) s :=
    hEvEq.hasDerivAt_iff.mp hslopeApply
  -- RHS: identify `B eT eX` with the variational right-hand side.
  -- Clairaut swaps `eT` and `eX`.
  have hswap : B eT eX = B eX eT := hsymm eT eX
  -- `B eX eT = ∂_x (q ↦ fderiv Φ q eT) · δ`.  Compute via the line `r ↦ x + r δ`.
  -- On a neighbourhood of `x`, `x + r δ ∈ ball x₀ r`, so the flow-ODE identity holds
  -- and `fderiv Φ (x + r δ, s) eT = f s (Φ (x + r δ, s))`.
  -- Curve `r ↦ (x + r δ, s)`, derivative `eX = inl δ`.
  have hlineCurve : HasDerivAt (fun rr : ℝ => (x + rr • δ, s)) eX 0 := by
    have : HasDerivAt (fun rr : ℝ => (x + rr • δ, s)) (δ, (0 : ℝ)) 0 := by
      simpa using (hasDerivAt_line x δ).prodMk (hasDerivAt_const (0 : ℝ) s)
    simpa [heX, ContinuousLinearMap.inl_apply] using this
  -- The composite `r ↦ fderiv Φ (x + r δ, s) eT` has derivative `B eX eT` at `0`.
  have hcompLine :
      HasDerivAt (fun rr : ℝ => fderiv ℝ Φ (x + rr • δ, s) eT) (B eX eT) 0 := by
    have h1 : HasDerivAt (fun rr : ℝ => fderiv ℝ Φ (x + rr • δ, s)) (B eX) 0 :=
      hsndHas.comp_hasDerivAt_of_eq 0 hlineCurve (by simp)
    have := (ContinuousLinearMap.apply ℝ E eT).hasFDerivAt.comp_hasDerivAt 0 h1
    simpa [ContinuousLinearMap.apply_apply] using this
  -- Near `r = 0`, `fderiv Φ (x + r δ, s) eT = f s (Φ (x + r δ, s))`.
  -- `r ↦ x + r δ` is continuous and `= x` at `0 ∈ ball x₀ r`, so stays in `ball` near 0.
  have hball_open : IsOpen {rr : ℝ | (x + rr • δ) ∈ ball x₀ (r : ℝ)} :=
    (isOpen_ball).preimage (by fun_prop)
  have hball_mem : (0 : ℝ) ∈ {rr : ℝ | (x + rr • δ) ∈ ball x₀ (r : ℝ)} := by
    simpa using hx
  -- Also need `(x + r δ, s) ∈ U` near `0` (so `Φ` is differentiable there).
  have hUline_open : IsOpen {rr : ℝ | (x + rr • δ, s) ∈ U} :=
    hUopen.preimage (by fun_prop)
  have hUline_mem : (0 : ℝ) ∈ {rr : ℝ | (x + rr • δ, s) ∈ U} := by simpa using hxsU
  have hEqLine : (fun rr : ℝ => fderiv ℝ Φ (x + rr • δ, s) eT)
      =ᶠ[𝓝 0] (fun rr : ℝ => f s (Φ (x + rr • δ, s))) := by
    filter_upwards [hball_open.mem_nhds hball_mem, hUline_open.mem_nhds hUline_mem]
      with rr hrr hrrU
    have hxb : (x + rr • δ) ∈ closedBall x₀ (r : ℝ) := ball_subset_closedBall hrr
    have hdiff : DifferentiableAt ℝ Φ (x + rr • δ, s) := hΦ_diffOn _ hrrU
    simpa [heT] using flow_joint_fderiv_inr_eq hΦ hxb hs hdiff
  -- Transport the derivative to the `f`-form.
  have hRHSline :
      HasDerivAt (fun rr : ℝ => f s (Φ (x + rr • δ, s))) (B eX eT) 0 :=
    hEqLine.hasDerivAt_iff.mp hcompLine
  -- Independently compute that derivative by the chain rule:
  -- `r ↦ f s (Φ (x + r δ, s))` = `(f s) ∘ (spatial slice) ∘ (line)`.
  have hRHSchain :
      HasDerivAt (fun rr : ℝ => f s (Φ (x + rr • δ, s)))
        (fderiv ℝ (f s) (Φ (x, s)) (fderiv ℝ (fun y => Φ (y, s)) x δ)) 0 := by
    -- `f s` is `C^∞`, differentiable at `Φ (x, s)`.
    have hfs_diff : DifferentiableAt ℝ (f s) (Φ (x, s)) := by
      have : ContDiffAt ℝ ∞ (f s) (Φ (x, s)) := by
        have hcd : ContDiffAt ℝ ∞ (uncurry f) (s, Φ (x, s)) :=
          hf.contDiffAt
        exact hcd.comp _ (contDiffAt_const.prodMk contDiffAt_id)
      exact this.differentiableAt (by simp)
    -- inner: `r ↦ Φ (x + r δ, s)` has derivative `Dx s δ` at `0`.
    have hinner : HasDerivAt (fun rr : ℝ => Φ (x + rr • δ, s))
        (fderiv ℝ (fun y => Φ (y, s)) x δ) 0 := by
      -- via the slice `y ↦ Φ (y, s)` composed with `r ↦ x + r δ`.
      have hsliceDiff : DifferentiableAt ℝ (fun y => Φ (y, s)) x :=
        (hΦ_diffOn _ hxsU).comp x (differentiableAt_id.prodMk (differentiableAt_const s))
      have hsliceHas : HasFDerivAt (fun y => Φ (y, s))
          (fderiv ℝ (fun y => Φ (y, s)) x) x := hsliceDiff.hasFDerivAt
      have := hsliceHas.comp_hasDerivAt_of_eq 0 (hasDerivAt_line x δ) (by simp)
      simpa using this
    have := hfs_diff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hinner (by simp)
    simpa using this
  -- Two computations of the same derivative agree.
  have hBval : B eX eT
      = fderiv ℝ (f s) (Φ (x, s)) (fderiv ℝ (fun y => Φ (y, s)) x δ) :=
    hRHSline.unique hRHSchain
  -- Conclude: `B eT eX = B eX eT = RHS`.
  rw [hswap, hBval] at hLHS
  exact hLHS

end PerDirection

/-! ## The operator-valued variational ODE (headline)

Bundling the per-direction statement over all `δ` gives the linearized-flow ODE for the
full spatial derivative operator. -/

/-- **Operator-valued variational / linearized-flow ODE (Euclidean core).**

For the jointly-`C^∞` local flow `Φ` of `f` on an open set `U`, at a strictly interior
point `(x, s)` (`x ∈ ball x₀ r`, `s ∈ Ioo tmin tmax`), the spatial Fréchet derivative
`u ↦ fderiv ℝ (fun y => Φ (y, u)) x` satisfies the linearized-flow ODE

  `HasDerivAt (fun u => fderiv ℝ (fun y => Φ (y, u)) x)
      ((fderiv ℝ (f s) (Φ (x, s))).comp (fderiv ℝ (fun y => Φ (y, s)) x)) s`,

i.e. `∂_s (D_x Φ) = (D_y f)(s, Φ) · (D_x Φ)`.

This is derived entirely from the existing `C^∞`-flow theorem and the flow-ODE clause of
`IsLocalFlow`; no variational identity is assumed. -/
theorem IsLocalFlow.hasDerivAt_partial_spatial_fderiv
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiff ℝ ∞ (uncurry f))
    {U : Set (E × ℝ)} (hUopen : IsOpen U) (hΦsmooth : ContDiffOn ℝ ∞ Φ U)
    {x : E} {s : ℝ} (hxsU : (x, s) ∈ U)
    (hx : x ∈ ball x₀ r) (hs : s ∈ Ioo tmin tmax) :
    HasDerivAt (fun u : ℝ => fderiv ℝ (fun y => Φ (y, u)) x)
      ((fderiv ℝ (f s) (Φ (x, s))).comp (fderiv ℝ (fun y => Φ (y, s)) x)) s := by
  -- `Φ` is `C^∞` on `U`; the spatial-derivative curve `u ↦ fderiv (slice) x` is `C^∞` in `u`,
  -- hence differentiable.  We then identify its derivative operator via the per-direction ODE.
  have hΦ_at : ∀ q ∈ U, ContDiffAt ℝ ∞ Φ q := fun q hq => contDiffAt_of_mem hUopen hΦsmooth hq
  have hΦ_xs : ContDiffAt ℝ ∞ Φ (x, s) := hΦ_at _ hxsU
  have hΦ_diffOn : ∀ q ∈ U, DifferentiableAt ℝ Φ q := fun q hq =>
    (hΦ_at q hq).differentiableAt (by simp)
  -- The CLM curve `u ↦ Lsp (x, u)` where `Lsp q = (fderiv Φ q).comp inl`.
  set Lsp : E × ℝ → (E →L[ℝ] E) :=
    fun q => (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ) with hLsp
  -- `Lsp` is `C^∞` at `(x, s)`: `fderiv Φ` is `C^∞`, post-composed with a fixed CLM.
  have hfderivSmooth : ContDiffAt ℝ ∞ (fderiv ℝ Φ) (x, s) :=
    hΦ_xs.fderiv_right (m := ∞) (by simp)
  have hLspSmooth : ContDiffAt ℝ ∞ Lsp (x, s) := by
    have hpost : ContDiffAt ℝ ∞
        (fun L : E × ℝ →L[ℝ] E => L.comp (ContinuousLinearMap.inl ℝ E ℝ)) (fderiv ℝ Φ (x, s)) :=
      (ContinuousLinearMap.compL ℝ E (E × ℝ) E |>.flip
        (ContinuousLinearMap.inl ℝ E ℝ)).contDiff.contDiffAt
    exact hpost.comp _ hfderivSmooth
  -- The time slice `u ↦ Lsp (x, u)` is `C^∞` in `u`, hence differentiable; get its `HasDerivAt`.
  have hLspTime : ContDiffAt ℝ ∞ (fun u : ℝ => Lsp (x, u)) s :=
    hLspSmooth.comp s (contDiffAt_const.prodMk contDiffAt_id)
  have hLspTimeDiff : DifferentiableAt ℝ (fun u : ℝ => Lsp (x, u)) s :=
    hLspTime.differentiableAt (by simp)
  set D' : E →L[ℝ] E := deriv (fun u : ℝ => Lsp (x, u)) s with hD'
  have hLspDeriv : HasDerivAt (fun u : ℝ => Lsp (x, u)) D' s := hLspTimeDiff.hasDerivAt
  -- Identify `Lsp (x, u) = fderiv (slice) x` near `s` (eventual equality of the curves).
  have hUx_open : IsOpen {u : ℝ | (x, u) ∈ U} := hUopen.preimage (by fun_prop)
  have hSliceEq : (fun u : ℝ => Lsp (x, u))
      =ᶠ[𝓝 s] (fun u : ℝ => fderiv ℝ (fun y => Φ (y, u)) x) := by
    filter_upwards [hUx_open.mem_nhds (show s ∈ {u : ℝ | (x, u) ∈ U} from hxsU)] with u hu
    rw [hLsp, partial_spatial_fderiv_eq_comp_inl (hΦ_diffOn _ hu)]
  have hSliceDeriv : HasDerivAt (fun u : ℝ => fderiv ℝ (fun y => Φ (y, u)) x) D' s :=
    hSliceEq.hasDerivAt_iff.mp hLspDeriv
  -- Per-direction: apply the curve at each `δ` and match against the variational RHS.
  set RHS : E →L[ℝ] E :=
    (fderiv ℝ (f s) (Φ (x, s))).comp (fderiv ℝ (fun y => Φ (y, s)) x) with hRHS
  -- Show `D' = RHS` by `ext` over `δ`.
  have hDeq : D' = RHS := by
    apply ContinuousLinearMap.ext
    intro δ
    -- `u ↦ (fderiv (slice) x) δ` has derivative `D' δ` (eval CLM applied to `hSliceDeriv`).
    have hcurveδ : HasDerivAt (fun u : ℝ => fderiv ℝ (fun y => Φ (y, u)) x δ) (D' δ) s := by
      have := (ContinuousLinearMap.apply ℝ E δ).hasFDerivAt.comp_hasDerivAt s hSliceDeriv
      simpa [ContinuousLinearMap.apply_apply] using this
    -- Per-direction variational ODE gives the same path's derivative as the RHS applied to δ.
    have hvarδ := IsLocalFlow.hasDerivAt_partial_spatial_fderiv_apply hΦ hf hUopen hΦsmooth
      hxsU hx hs δ
    have := hcurveδ.unique hvarδ
    rw [this, hRHS, ContinuousLinearMap.comp_apply]
  rw [← hDeq]
  exact hSliceDeriv

end DifferentialGeometry.Analysis.ODE.Flow

/-!
## Toward the manifold identity `RawVariationalIdentity` (documented remaining gap)

The Euclidean variational ODE proved above is the concrete linearized-flow equation in a
single Banach/chart model.  Connecting it to the manifold predicate
`RawVariationalIdentity` (file `TimeDependentFlow/VariationalFlow.lean`), namely

  `HasDerivAt (fun s => (mfderiv I I (Φ_fam s) x v : E))
      (-(LeviCivita g) X (Φ_fam s) x (mfderiv I I (Φ_fam s) x v)) t`,

requires three further steps, none of which is carried out here:

1. **Chart identification of `mfderiv` with the chart-flow spatial `fderiv`.**  In a chart
   `(chartAt H α)`, the manifold flow `Φ_fam` reads off as the Euclidean flow `Φ` of the
   chart-coordinate vector field `f_chart t y = (X t ((chartAt H α).symm (I.symm y)) : E)`
   (this is exactly the `f` consumed by `ChartLocalPicardData.contDiffOn_top` in
   `SmoothInSpace/BanachIC.lean`).  Under the chart, `mfderiv I I (Φ_fam s) x v` becomes
   `fderiv ℝ (fun y => Φ (y, s)) (chart x) (chart-coords of v)` up to the chart
   differentials of source and target.  The required lemma transports the operator-valued
   `HasDerivAt` of this file through those (time-independent) chart differentials —
   composition with fixed CLMs preserves `HasDerivAt`, so this is mechanical once the
   `mfderiv`/chart-`fderiv` dictionary is written.

2. **Flat-to-covariant reconciliation of the right-hand side.**  The Euclidean RHS is the
   *flat* chart derivative `(fderiv ℝ (f_chart s) (Φ (x,s))).comp (D_x Φ)`, i.e. the
   coordinate derivative `∂_j (f_chart)^i`.  The target RHS is the *covariant* derivative
   `(LeviCivita g) X` along the pushforward.  The two differ by the Christoffel correction
   `Γ^i_{jk} X^k`; the identity `∂_j X^i = (∇ X)^i_j - Γ^i_{jk} X^k` (the chart formula for
   the Levi-Civita covariant derivative of a vector field) is the bridge.  The needed
   chart-Christoffel infrastructure already exists under `Integral/Connection/` and
   `Geometry/` (e.g. the chart Levi-Civita connection and its component formula); the lift
   composes that component identity with step 1.

3. **Sign / generator bookkeeping.**  `RawVariationalIdentity` uses the flow of `-X` (the
   `-` in `-(LeviCivita g) X`), so the chart vector field is `f_chart = -X` in coordinates;
   the minus sign threads through linearly from `fderiv ℝ (f_chart s) = -fderiv ℝ (X-chart)`.

Because steps 1–2 require a precise `mfderiv`-in-chart dictionary and the chart-Christoffel
component identity wired to `LeviCivita`, they constitute a separate, non-trivial body of
work and are left as the documented gap.  The present file removes the analytic obstruction
(no smooth-in-IC theory existed before): the variational ODE is now a *theorem* derived from
the `C^∞` flow, not an assumption.
-/
