import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueClosure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ForwardUniqueRmDot

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Forward uniqueness from the black box (B) interface (Route-K brick K6a)

`Evolution/ForwardUniqueClosure.lean` (K5) proves the Route-K capstone `metrics_eq_ico` in the
currency of the energy machinery: it consumes the K3 differentiation package, the K4 rate
package, and the closed-edge inputs, all quantified over compact subslabs.  This file plugs
the **black box (B) hypothesis interface** of `Evolution/ExtendViaUniqueness.lean` into that
capstone and records, in one named bundle, exactly what is still missing.

`forward_unique_of_inputs` has (B)'s own signature — two flows, the four chart-Gram fields on
the `Ico`-slab, the two Ricci-flow PDE fields in `HasDerivWithinAt … (Ici a)` form, and
`g₁ a = g₂ a` — plus one residual `ForwardUniqueInputs` bundle, and concludes `g₁ = g₂` on
`Ico a b`.  **It does not discharge `ricci_flow_forward_unique`**: the bundle is the honest
remaining frontier, and `ExtendViaUniqueness.lean` is untouched.

## What (B)'s own fields buy

* `hgram` (K3) — `h1smooth` restricted from `Ico a b` to the open subslab `Ioo a c`.
* `hPDE₁`, `hPDE₂` (K3) — `pde_hasDerivAt`: at an interior time `Ici a` is a neighbourhood, so
  the one-sided `HasDerivWithinAt` upgrades to `HasDerivAt`; `metricRicciAt_apply_eq_ricciTensor`
  converts the endpoint's `ricciTensor` currency to the lane's `metricRicciAt` currency.
* `hinit` (K5) — literally `h0`.
* the Young parameters — `ε := 1/2`, `δ := 1/(2(C_A + 1))` with `C_A` normalised to be
  nonnegative, so K4's side condition `δ·C_A + ε ≤ 1` is pure arithmetic and never an input.
* the continuation — `metrics_eq_ico`, every `t ∈ Ico a b` sitting in `Icc a ((t+b)/2)`.

## What the banked chains buy

* `connSpeed_hasDerivAt` (K1C, `ForwardUniqueConnDot.lean`) turns the *frame-component*
  Christoffel-difference derivative into K3's invariant `hA`, adding the moving-carrier
  reaction term `−2Ric₁((∇¹−∇²)·,·)` itself.  The residual input is the component fact.
* `rmSpeed_hasDerivAt` (K2.1, `ForwardUniqueRmDot.lean`) does the same one rank up: the raised
  curvature-difference derivative becomes K3's invariant `hS`.

## The residual bundle

`ForwardUniqueInputs` collects the sixteen facts that today's producer chains cannot supply
from (B)'s fields.  Every field carries its provenance label in its docstring:

* **K2-B** — the per-flow Christoffel/Uhlenbeck evolution interfaces and their consequences.
  These are the recorded standing inputs of planner ruling R1 (`ShortTime/FORWARD_UNIQUE_PLAN.md`
  №2), to be discharged by the dedicated second-Bianchi brick.
* **hdens-tower** — joint `(t,x)`-regularity of the energy density and the integrability of the
  rate integrands, plus the slab-uniform background constants.  These come from the chart-Gram
  → Γ → Rm joint smoothness tower (K3's recorded debt (i)) and from compactness of the closed
  subslab.
* **realization** — which intrinsic object a supplied smooth field realizes.

`ForwardUniqueSlab` is separate for one reason only: K4's six constants must be chosen **per
compact subslab**, never once for the whole half-open window (the ruling's "constants
slab-local" discipline), so the bundle quantifies it as `∀ c ∈ Ioo a b, ∃ constants, …`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]

section ChartFrame

/-! ## The canonical chart frame at a point

The frame-level producers (`connDiffLow_hasDerivAt_frame`) need *one* local frame around each
point, not an atlas.  The canonical choice is the frame of the tangent-bundle trivialization
centred at that very point, which is a `C^n` local frame on its own base set for every `n`.
Fixing it here keeps the residual Christoffel input as weak as possible: it is required in this
one frame per point, not in every frame. -/

variable (I) in
/-- The chart frame attached to `x₀`: the local frame of the tangent-bundle trivialization at
`x₀` associated with the model basis. -/
def chartFrame (x₀ : M) : Fin (Module.finrank Real E) → (y : M) → TangentSpace I y :=
  (trivializationAt E (TangentSpace I) x₀).localFrame (chartModelBasis E)

variable (I) in
/-- `chartFrame I x₀` is a `C¹` local frame on the base set of the trivialization at `x₀`. -/
theorem chartFrame_isFrame (x₀ : M) :
    IsLocalFrameOn I E 1 (chartFrame I x₀) (trivializationAt E (TangentSpace I) x₀).baseSet :=
  (trivializationAt E (TangentSpace I) x₀).isLocalFrameOn_localFrame_baseSet I 1
    (chartModelBasis E)

variable (I) in
/-- The centre of a chart frame lies in its domain. -/
theorem chartFrame_mem (x₀ : M) :
    x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
  FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀

end ChartFrame

section Speeds

/-! ## The two invariant speeds

The energy machinery consumes *invariant* `(0,3)` and `(0,4)` speeds.  The banked adapters
produce them from the raised (index-up) speeds of `∇¹ − ∇²` and of the curvature difference,
adding the terms created by the moving lowering carrier `g₁(t)`. -/

/-- The invariant speed of the connection-difference carrier `A₀₃`, built from a raised speed
`Avec` of `∇¹ − ∇²`.  This is `connDiffDot`, i.e. `−2Ric₁((∇¹−∇²)·,·) + g₁(Avec ·,·)`. -/
def connSpeed (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Avec : Real → (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y) :
    Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  fun t x => connDiffDot (I := I) g₁ g₂ (Avec t) t x

/-- The invariant speed of the curvature-difference carrier `S₀₄`, built from a raised speed
`Svec` of `rmDiffVec`.  This is `rmDiffDot`. -/
def rmSpeed (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Svec : Real → (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y →L[Real]
        TangentSpace I y) :
    Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  fun t x => rmDiffDot (I := I) g₁ g₂ (Svec t) t x

/-- **K3's `hA` from frame components.**  The chart-frame Christoffel-difference derivative
plus the Ricci-flow equation of the *lowering* flow `g₁` give the invariant derivative of the
connection-difference carrier.  The second flow's PDE is not needed (only `g₁` lowers). -/
theorem connSpeed_hasDerivAt (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Avec : Real → (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    {t : Real} {x : M}
    (hPDE₁ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun i : Fin 2 => if i = 0 then X else Y)) t)
    (hgamma : ∀ i j k : Fin (Module.finrank Real E),
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k)
        ((chartFrame_isFrame I x).coeff k x
          ((Avec t x (chartFrame I x j x)) (chartFrame I x i x))) t)
    (v : Fin 3 → TangentSpace I x) :
    HasDerivAt (fun r : Real => connDiffLowAt (I := I) (g₁ r) (g₂ r) x v)
      (connSpeed (I := I) g₁ g₂ Avec t x v) t :=
  connDiffLow_hasDerivAt_frame (I := I) g₁ g₂ (chartFrame I x) (chartFrame_isFrame I x)
    (trivializationAt E (TangentSpace I) x).open_baseSet (chartFrame_mem I x) (Avec t)
    hPDE₁ hgamma v

/-- **K3's `hS` from the raised curvature difference.**  The derivative of the raised
curvature-difference operator plus the Ricci-flow equation of the lowering flow `g₁` give the
invariant derivative of `S₀₄`. -/
theorem rmSpeed_hasDerivAt (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Svec : Real → (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y →L[Real]
        TangentSpace I y)
    {t : Real} {x : M}
    (hPDE₁ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun i : Fin 2 => if i = 0 then X else Y)) t)
    (hrm : ∀ X Y Z : TangentSpace I x,
      HasDerivAt (fun r : Real => ((rmDiffVec (I := I) (g₁ r) (g₂ r) x X) Y) Z)
        (((Svec t x X) Y) Z) t)
    (v : Fin 4 → TangentSpace I x) :
    HasDerivAt (fun r : Real => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x v)
      (rmSpeed (I := I) g₁ g₂ Svec t x v) t :=
  rmDiffLow_hasDerivAt (I := I) g₁ g₂ (Svec t) hPDE₁ hrm v

end Speeds

section PDEUpgrade

/-! ## The endpoint's PDE field in the lane's currency

Black box (B) states the Ricci-flow equation as a one-sided derivative within `Ici a`, with the
`ricciTensor` curvature representative.  The energy machinery works at interior times with a
two-sided derivative and the `metricRicciAt` representative.  Both conversions are free:
`Ici a` is a neighbourhood of every `t > a`, and the two Ricci representatives agree pointwise
(`metricRicciAt_apply_eq_ricciTensor`). -/

/-- **Interior upgrade of the (B) PDE field.**  At an interior time of the window the one-sided
Ricci-flow equation of black box (B) is an honest two-sided derivative in the lane's currency. -/
theorem pde_hasDerivAt (g : Real → SmoothRiemannianMetric I M) {a b : Real}
    (hpde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (g s).inner x v w)
        ((-2 : Real) * DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g t) x v w) (Ici a) t)
    {t : Real} (ht : t ∈ Ioo a b) (x : M) (X Y : TangentSpace I x) :
    HasDerivAt (fun r : Real => (g r).inner x X Y)
      ((-2 : Real) * metricRicciAt (I := I) (g t) x
        (fun i : Fin 2 => if i = 0 then X else Y)) t := by
  have hbridge : metricRicciAt (I := I) (g t) x (fun i : Fin 2 => if i = 0 then X else Y) =
      DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g t) x X Y :=
    metricRicciAt_apply_eq_ricciTensor (I := I) (g t) x X Y
  rw [hbridge]
  exact (hpde t ⟨ht.1.le, ht.2⟩ x X Y).hasDerivAt (Ici_mem_nhds ht.1)

end PDEUpgrade

section Inputs

/-! ## The residual standing inputs

Two records.  `ForwardUniqueSlab` is the K4 pointwise-bound package for ONE compact subslab and
ONE choice of constants; `ForwardUniqueInputs` is the whole residual bundle, quantifying the
constants existentially per subslab.  Nothing here is data: both are `Prop`. -/

/-- **K4's six pointwise bounds on the open subslab `Ioo a c`, with explicit constants.**

Provenance: all six are **hdens-tower** debt — slab-uniform background bounds that the
compactness of `Icc a c` plus the chart-Gram → Γ → Rm regularity tower will produce, and that
are *false* as constants uniform over the whole half-open window `Ico a b`.  Two of them are
additionally **composable-later**: `ricciLe` from `ricciDiffSq_le` (`ForwardUniqueRateLe.lean`)
once the tensor-level `Ric = tr_g(Rm₀₄)` slot bridge lands, and `reactLe` from the
`movingReact0S` micro-bound named as OWED by K4. -/
structure ForwardUniqueSlab (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Sfield : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Uflux : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (rem : Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (a c C_A C_R C_Ric C_V C_U C_rem : Real) : Prop where
  /-- The K2 divergence flux is controlled by the energy density. -/
  fluxLe : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 5 (Uflux t x) ≤
    C_U * forwardUniqueDensity (I := I) g₁ g₂ t x
  /-- The K2 remainder is controlled by the energy density. -/
  remLe : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 4 (rem t x) ≤
    C_rem * forwardUniqueDensity (I := I) g₁ g₂ t x
  /-- The moving-norm reaction of the three carriers is controlled by the energy density. -/
  reactLe : ∀ t ∈ Ioo a c, ∀ x,
    movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
        (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
      movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
        (connDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
      movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
    C_R * forwardUniqueDensity (I := I) g₁ g₂ t x
  /-- The Ricci difference is controlled by the energy density. -/
  ricciLe : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 2
      (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) ≤
    C_Ric * forwardUniqueDensity (I := I) g₁ g₂ t x
  /-- The connection-difference speed is controlled by the density plus the dissipation. -/
  adotLe : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 3 (Adot t x) ≤
    C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
      normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) (Sfield t) x))
  /-- The volume-form drift is bounded above. -/
  volLe : ∀ t ∈ Ioo a c, ∀ x, (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V

/-- **The residual standing-input bundle of the (B) endgame.**

Everything black box (B)'s own fields plus the banked Route-K chains cannot supply.  The
provenance label of each field is in its docstring; the summary is:

* `gamma`, `rm`, `sdec` — **K2-B**: the per-flow Christoffel and Uhlenbeck evolution
  interfaces, and the divergence-form curvature-difference equation they feed.
* `car` — **realization**: which intrinsic tensor the supplied smooth `S₀₄` field is.
* `bounds` — **hdens-tower**, slab-local (see `ForwardUniqueSlab`).
* `dens`, `energyCont`, `densInt`, `densCont` and the seven integrability fields —
  **hdens-tower**: joint `(t,x)`-regularity of the energy density and integrability of the
  rate integrands. -/
structure ForwardUniqueInputs (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Avec : Real → (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    (Svec : Real → (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y →L[Real]
        TangentSpace I y)
    (Sfield : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Uflux : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (rem : Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (a b : Real) : Prop where
  /-- **K2-B.**  The Christoffel-difference evolution in the chart frame at each point, with its
  right-hand side realized by the raised speed `Avec`.  Producer:
  `christoffelEvolutionDiffInFrameOn` (`ForwardUniqueConnectionDiff.lean`) applied to the two
  per-flow `ChristoffelEvolutionEquationInFrameOn` interfaces, with `Avec := bilinOfComp` of the
  two component right-hand sides (`coeff_bilinOfComp` discharges the coefficient identity).
  Still missing between here and there: the `SolutionOn`-package bridge from (B)'s chart-Gram
  fields (`christoffelInFrame_sol` is the definitional half). -/
  gamma : ∀ t ∈ Ioo a b, ∀ x : M, ∀ i j k : Fin (Module.finrank Real E),
    HasDerivAt
      (fun r : Real =>
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (metricCov (I := I) (g₁ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k -
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (metricCov (I := I) (g₂ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k)
      ((chartFrame_isFrame I x).coeff k x
        ((Avec t x (chartFrame I x j x)) (chartFrame I x i x))) t
  /-- **K2-B.**  The time derivative of the raised curvature difference, realized by `Svec`.
  Producer: `rmDiffVec_deriv` (`ForwardUniqueRmBridge.lean`) from the two own-lowered Uhlenbeck
  interfaces `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` plus time-continuity of
  `riemannOp`.  Still missing between here and there: the frame → invariant lift of that
  pointwise conclusion into a trilinear bundled speed (the quadrilinear analogue of
  `bilinOfComp`). -/
  rm : ∀ t ∈ Ioo a b, ∀ (x : M) (X Y Z : TangentSpace I x),
    HasDerivAt (fun r : Real => ((rmDiffVec (I := I) (g₁ r) (g₂ r) x X) Y) Z)
      (((Svec t x X) Y) Z) t
  /-- **Realization.**  The supplied smooth `(0,4)` field is the curvature-difference carrier. -/
  car : ∀ t ∈ Ioo a b, ∀ x, Sfield t x = rmDiffLowAt (I := I) (g₁ t) (g₂ t) x
  /-- **K2-B.**  The Kotschwar `S`-equation in divergence form: the invariant speed of `S₀₄`
  splits into the rough Laplacian of `g₁`, the divergence of the K2 flux, and a remainder.
  Producer: `rmLowComp_deriv` (`ForwardUniqueRmDot.lean`) composed with the concrete
  divergence-form commutator `lapComm_reLower_flux` (`ForwardUniqueReLower.lean`) and
  `lapDiff_eq_div_flux` (`ForwardUniqueRmDiff.lean`).  Still missing between here and there:
  the componentwise → invariant lift, and the planner decision on the mixed-lowering carrier
  gap recorded in `ForwardUniqueRmDot.md`. -/
  sdec : ∀ t ∈ Ioo a b, ∀ x, rmSpeed (I := I) g₁ g₂ Svec t x =
    roughLap0SField (I := I) (g₁ t) (Sfield t) x +
      covDiv0SField (I := I) (g₁ t) (Uflux t) x + rem t x
  /-- **hdens-tower, slab-local.**  K4's six pointwise bounds, with constants chosen per compact
  subslab — never once for the whole half-open window. -/
  bounds : ∀ c ∈ Ioo a b, ∃ C_A C_R C_Ric C_V C_U C_rem : Real,
    ForwardUniqueSlab (I := I) g₁ g₂ (connSpeed (I := I) g₁ g₂ Avec) Sfield Uflux rem
      a c C_A C_R C_Ric C_V C_U C_rem
  /-- **hdens-tower.**  Joint `(t,x)`-smoothness of the energy density on the open window; K3's
  recorded debt (i), the chart-Gram → Γ → Rm joint tower. -/
  dens : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
    (fun p : Real × M => forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
    (Ioo a b ×ˢ (univ : Set M))
  /-- **hdens-tower.**  Continuity of the energy up to the closed edge — the input that lets the
  Grönwall closure reach the initial time without differentiating there. -/
  energyCont : ContinuousOn (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (Ico a b)
  /-- **hdens-tower.**  Integrability of the energy density, up to the closed edge. -/
  densInt : ∀ t ∈ Ico a b, Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
    (riemannianMeasureFamily (I := I) (M := M) g₁ t)
  /-- **hdens-tower.**  Space-continuity of the energy density, up to the closed edge — this is
  what turns "a.e. zero" into "everywhere zero" against the Riemannian volume measure. -/
  densCont : ∀ t ∈ Ico a b, Continuous (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
  /-- **hdens-tower.**  Integrability of the non-principal part of the rate integrand. -/
  restInt : ∀ t ∈ Ioo a b, Integrable
    (fun x => rateRest (I := I) g₁ g₂ (connSpeed (I := I) g₁ g₂ Avec) t x)
    (riemannianMeasureFamily (I := I) (M := M) g₁ t)
  /-- **hdens-tower.**  Integrability of the `S`-pairing. -/
  pairInt : ∀ t ∈ Ioo a b, Integrable
    (fun x => 2 * inner0S (I := I) (g₁ t) x 4 (rmSpeed (I := I) g₁ g₂ Svec t x)
      (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))
    (riemannianMeasureFamily (I := I) (M := M) g₁ t)
  /-- **hdens-tower.**  Integrability of the rough-Laplacian pairing. -/
  lapInt : ∀ t ∈ Ioo a b, Integrable (fun x => inner0S (I := I) (g₁ t) x 4
      (roughLap0SField (I := I) (g₁ t) (Sfield t) x) (Sfield t x))
    (riemannianMeasureFamily (I := I) (M := M) g₁ t)
  /-- **hdens-tower.**  Integrability of the divergence pairing. -/
  divInt : ∀ t ∈ Ioo a b, Integrable (fun x => inner0S (I := I) (g₁ t) x 4
      (covDiv0SField (I := I) (g₁ t) (Uflux t) x) (Sfield t x))
    (riemannianMeasureFamily (I := I) (M := M) g₁ t)
  /-- **hdens-tower.**  Integrability of the remainder pairing. -/
  remInt : ∀ t ∈ Ioo a b, Integrable
    (fun x => inner0S (I := I) (g₁ t) x 4 (rem t x) (Sfield t x))
    (riemannianMeasureFamily (I := I) (M := M) g₁ t)
  /-- **hdens-tower.**  Integrability of the flux–gradient pairing. -/
  nabInt : ∀ t ∈ Ioo a b, Integrable (fun x => inner0S (I := I) (g₁ t) x 5
      (metricNabla0S (I := I) (g₁ t) (Sfield t) x) (Uflux t x))
    (riemannianMeasureFamily (I := I) (M := M) g₁ t)
  /-- **hdens-tower.**  Integrability of the dissipation density. -/
  disInt : ∀ t ∈ Ioo a b, Integrable (fun x => normSq0S (I := I) (g₁ t) x 5
      (metricNabla0S (I := I) (g₁ t) (Sfield t) x))
    (riemannianMeasureFamily (I := I) (M := M) g₁ t)

end Inputs

section Assembly

/-! ## The endgame assembly

`forward_unique_of_inputs` is black box (B)'s statement with the residual bundle added.  The
proof picks, for each `t ∈ Ico a b`, the compact subslab `Icc a c` with `c := (t+b)/2`, and
calls `metrics_eq_on` there. -/

-- `hab`, `h1cont`, `h2smooth` and `h2cont` are deliberately unused: the statement reproduces
-- black box (B)'s interface verbatim, and the smooth class makes the two C⁰ fields redundant
-- while only the lowering flow's chart-Gram smoothness is consumed.  Renaming them would break
-- the interface fidelity that is the whole point of this theorem.
set_option linter.unusedVariables false in
/-- **Forward uniqueness of the Ricci flow, modulo the residual standing inputs.**

This is exactly the hypothesis interface of black box (B) — `ricci_flow_forward_unique` in
`Evolution/ExtendViaUniqueness.lean` — together with the residual bundle `ForwardUniqueInputs`
and the two raised speeds it realizes.  Discharging the bundle (K2-B for the evolution
interfaces, the hdens tower for the density regularity and slab constants) discharges the black
box: this theorem is the last wiring step of Route K.

Everything (B)'s own fields can supply is supplied here and appears in NO hypothesis of the
bundle: the chart-Gram smoothness restriction, both interior PDE upgrades, the closed-edge
initial equality, K4's Young parameters (`ε = 1/2`, `δ = 1/(2(C_A+1))`, whose side condition is
proved, not assumed), and the compact-subslab continuation. -/
theorem forward_unique_of_inputs
    (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (Avec : Real → (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    (Svec : Real → (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y →L[Real]
        TangentSpace I y)
    (Sfield : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Uflux : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (rem : Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (h1smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h1cont : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h2smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h2cont : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M => chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h1pde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (h2pde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    (h0 : g₁ a = g₂ a)
    (hin : ForwardUniqueInputs (I := I) g₁ g₂ Avec Svec Sfield Uflux rem a b) :
    ∀ t ∈ Ico a b, g₁ t = g₂ t := by
  refine metrics_eq_ico (I := I) g₁ g₂ ?_
  intro c hc t ht
  -- the open subslab sits inside the open window
  have hsub : Ioo a c ⊆ Ioo a b := fun s hs => ⟨hs.1, lt_trans hs.2 hc.2⟩
  have hsubIcc : Icc a c ⊆ Ico a b := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 hc.2⟩
  -- K4's constants for THIS subslab, normalised so that the `A`-constant is nonnegative
  obtain ⟨C_A, C_R, C_Ric, C_V, C_U, C_rem, hb⟩ := hin.bounds c hc
  have hCA : (0 : Real) ≤ max C_A 0 := le_max_right _ _
  -- the Young parameters are CHOSEN, and K4's side condition is arithmetic
  have hyoung : (1 / (2 * (max C_A 0 + 1))) * max C_A 0 + (1 / 2 : Real) ≤ 1 := by
    have he : (1 / (2 * (max C_A 0 + 1))) * max C_A 0
        = max C_A 0 / (2 * (max C_A 0 + 1)) := by ring
    have hdiv : max C_A 0 / (2 * (max C_A 0 + 1)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    rw [he]; linarith
  -- (B)'s chart-Gram field, restricted to the subslab
  have hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ioo a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := fun x₀ i j =>
    (h1smooth x₀ i j).mono
      (Set.prod_mono (fun s hs => ⟨hs.1.le, lt_trans hs.2 hc.2⟩) (subset_refl _))
  -- (B)'s two PDE fields, upgraded at interior times
  have hPDE₁ : ∀ t ∈ Ioo a c, ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun i : Fin 2 => if i = 0 then X else Y)) t :=
    fun s hs x X Y => pde_hasDerivAt (I := I) g₁ h1pde (hsub hs) x X Y
  have hPDE₂ : ∀ t ∈ Ioo a c, ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : Real => (g₂ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₂ t) x
          (fun i : Fin 2 => if i = 0 then X else Y)) t :=
    fun s hs x X Y => pde_hasDerivAt (I := I) g₂ h2pde (hsub hs) x X Y
  -- the two invariant speeds, from the banked chains
  have hA : ∀ t ∈ Ioo a c, ∀ (x : M) (v : Fin 3 → TangentSpace I x),
      HasDerivAt (fun r : Real => connDiffLowAt (I := I) (g₁ r) (g₂ r) x v)
        (connSpeed (I := I) g₁ g₂ Avec t x v) t := fun s hs x v =>
    connSpeed_hasDerivAt (I := I) g₁ g₂ Avec (fun X Y => hPDE₁ s hs x X Y)
      (fun i j k => hin.gamma s (hsub hs) x i j k) v
  have hS : ∀ t ∈ Ioo a c, ∀ (x : M) (v : Fin 4 → TangentSpace I x),
      HasDerivAt (fun r : Real => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x v)
        (rmSpeed (I := I) g₁ g₂ Svec t x v) t := fun s hs x v =>
    rmSpeed_hasDerivAt (I := I) g₁ g₂ Svec (fun X Y => hPDE₁ s hs x X Y)
      (fun X Y Z => hin.rm s (hsub hs) x X Y Z) v
  -- the `A`-speed bound, with the normalised constant
  have hAdot : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 3
      (connSpeed (I := I) g₁ g₂ Avec t x) ≤
      max C_A 0 * (forwardUniqueDensity (I := I) g₁ g₂ t x +
        normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) (Sfield t) x)) := by
    intro s hs x
    refine (hb.adotLe s hs x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact add_nonneg (density_nonneg (I := I) g₁ g₂ s x)
      (normSq0S_nonneg (I := I) (g₁ s) x 5 _)
  exact metrics_eq_on (I := I) (ε := 1 / 2) (δ := 1 / (2 * (max C_A 0 + 1)))
    (C_A := max C_A 0) g₁ g₂ (connSpeed (I := I) g₁ g₂ Avec)
    (rmSpeed (I := I) g₁ g₂ Svec) Sfield Uflux rem hc.1 hgram
    (hin.dens.mono (Set.prod_mono hsub (subset_refl _))) hPDE₁ hPDE₂ hA hS
    (by norm_num) (by positivity) hyoung
    (fun s hs => hin.car s (hsub hs)) (fun s hs => hin.sdec s (hsub hs))
    (hb.fluxLe) (hb.remLe) (hb.reactLe) (hb.ricciLe) hAdot (hb.volLe)
    (fun s hs => hin.restInt s (hsub hs)) (fun s hs => hin.pairInt s (hsub hs))
    (fun s hs => hin.lapInt s (hsub hs)) (fun s hs => hin.divInt s (hsub hs))
    (fun s hs => hin.remInt s (hsub hs)) (fun s hs => hin.nabInt s (hsub hs))
    (fun s hs => hin.disInt s (hsub hs)) (fun s hs => hin.densInt s (hsubIcc hs))
    (fun s hs => hin.densCont s (hsubIcc hs)) h0
    (hin.energyCont.mono hsubIcc) t ht

end Assembly

end DifferentialGeometry.PDE.RicciFlow

end
