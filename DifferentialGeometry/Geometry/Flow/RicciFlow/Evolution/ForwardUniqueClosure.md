# ForwardUniqueClosure.lean — Route-K brick K5 (scalar closure)

**Status (2026-07-26): OUTCOME (A) — 480 lines, 8 public theorems + 3 private helpers,
0 `sorry`, all 8 public declarations axiom-clean (`propext, Classical.choice, Quot.sound`
only).  Focused check green; targeted build green (authoritative, `8881/8881`, fresh olean);
hardened hygiene sweep clean (no `instance`/`axiom`/`notation`/`macro`/`elab`/`syntax` in any
modifier-prefixed form).**

The measure-positivity producer that outcome (B) would have had to `sorry` **already exists**
(`riemannianVolumeMeasure_isOpenPosMeasure`), so no measure theory was built and no frontier
was left.

## What this file is

The closure half of `ShortTime/FORWARD_UNIQUE_PRO_RULING.md` §6: given K3's exact first
variation and K4's rate estimate, conclude that the two Ricci flows coincide.

```
E' ≤ K·E − D ≤ K·E on Ioo a c   (K4 + dissipation_nonneg)
E(a) = 0                        (h0 : g₁ a = g₂ a)
E ≥ 0, E continuous on Icc a c
        ⟹ E ≡ 0 on Icc a c      (gronwall_zero_on)
        ⟹ density ≡ 0           (nonneg + zero integral + IsOpenPosMeasure + continuity)
        ⟹ h₀₂ = 0               (fibre positive-definiteness)
        ⟹ g₁ t = g₂ t           (metric extensionality)
        ⟹ ∀ t ∈ Ico a b         (sup over subslabs c < b)
```

## Public API

| theorem | content |
| --- | --- |
| `gronwall_zero_on` | closed-edge Grönwall on `Icc a c` (scalar, pure ℝ) |
| `energy_nonneg` | `0 ≤ forwardUniqueEnergy` |
| `density_eq_zero_of_eq` | `g₁ t = g₂ t ⟹ density t x = 0` |
| `energy_eq_zero_of_eq` | `g₁ t = g₂ t ⟹ E(t) = 0` (the `E(a) = 0` input) |
| `energy_zero_on` | **step 1**: combined K3+K4 slab package ⟹ `∀ t ∈ Icc a c, E t = 0` |
| `metric_eq_of_energy_zero` | **step 2**: `E t = 0 ⟹ g₁ t = g₂ t` |
| `metrics_eq_on` | **capstone**: `∀ t ∈ Icc a c, g₁ t = g₂ t` |
| `metrics_eq_ico` | **continuation**: per-subslab conclusion ⟹ `∀ t ∈ Ico a b, g₁ t = g₂ t` |

Private helpers: `normSq0S_zero`, `eq_zero_of_normSq0S` (both one-liners off
`MetricFiberData.inner_self_eq_zero_iff`), `metricExtInner` (metric extensionality).

## K6's input inventory (the capstone's hypothesis package)

`metrics_eq_on` takes, besides the six carrier arguments
(`Adot`, `Sdot`, `Sfield : ℝ → Tensor0SField … 4`, `Uflux : ℝ → Tensor0SField … 5`,
`rem : ℝ → (x : M) → Tensor0SSpace 4 I x`) and the slab-uniform reals
`ε δ C_A C_R C_Ric C_V C_U C_rem`:

* `hac : a < c`;
* **K3 package on `U := Ioo a c`** — `hgram` (chart-Gram joint smoothness of the carrier
  `g₁`), `hdens` (joint smoothness of the scalar density on `Ioo a c ×ˢ univ`), and the four
  `∀ t ∈ Ioo a c`-quantified pointwise facts `hPDE₁`, `hPDE₂`, `hA`, `hS`;
* **K4 package, `∀ t ∈ Ioo a c`** — `hε`, `hδ`, `habs` (Young smallness `δC_A + ε ≤ 1`),
  `hcar`, `hSdec`, `hUb`, `hrem`, `hreact`, `hRic`, `hAdot`, `hvol`, and the seven
  integrability side conditions `hirest`, `hipair`, `hilap`, `hidiv`, `hirem`, `hinab`,
  `hidis`;
* **closed-slab regularity** — `hidens` and `hdcont` quantified over `Icc a c`
  (not `Ioo a c`: step 2 needs the density at the *closed* right edge);
* **edge/continuity** — `hinit : g₁ a = g₂ a` and
  `hcont : ContinuousOn (forwardUniqueEnergy g₁ g₂) (Icc a c)`.

Only **two** inputs here are new relative to K3+K4, and both are honest analytic regularity,
not new mathematics:

1. `hdcont : ∀ t ∈ Icc a c, Continuous (fun x => forwardUniqueDensity g₁ g₂ t x)` — the
   space-continuity that upgrades "a.e. zero" to "everywhere zero".  On `Ioo a c` it is
   implied by K3's `hdens` (compose `ContMDiffOn.continuousOn` with `x ↦ (t, x)`); it was
   NOT derived that way because the capstone also needs it at `t = c`, where `hdens` says
   nothing.  This is the same `hdens`-tower debt already recorded at K3 dispatch №6(i).
2. `hcont : ContinuousOn (forwardUniqueEnergy g₁ g₂) (Icc a c)` — closed-edge continuity of
   the energy.  Same debt family; it is exactly `MovingEdgeEnergy.lean:932`'s remark that
   this follows from the two chart-Gram towers.

`hidens` was extended from `Ioo a c` to `Icc a c` rather than duplicated: `energy_zero_on`
receives it through `Ioo_subset_Icc_self`.

## Route decisions and why

* **`edgeGronwall_zero` was NOT imported.**  It lives in
  `Analysis/Spectral/Intrinsic/DeTurck/EdgeStrongData.lean`, whose olean does not exist in
  this checkout (its only consumer `MovingEdgeEnergy.lean` is the un-compilable file of
  dispatch №6), and it is stated for the left edge `0` of `Icc 0 T` while the
  forward-uniqueness slab starts at an arbitrary `a`.  `gronwall_zero_on` restates it on
  `Icc a c` directly off Mathlib's `le_gronwallBound_of_liminf_deriv_right_le`, with no
  `DifferentialGeometry` import at all.  **Ledger item**: merge the two into one statement
  under `Analysis/ODE/`, next to `IntegralGronwall.lean` — 2 occurrences now.
* **`metricExtInner` is the third local copy** of smooth-metric extensionality
  (`SmoothRiemannianMetric.ext'` in `Geometry/Metric/Sphere/QuotientDescent.lean:110`,
  `smoothRiemannianMetric_ext_inner` in `ShortTime/DeTurckRealizedSolutionFamily.lean:96`).
  Neither is an admissible import for the `Evolution` layer (Sphere/quotient tree; ShortTime
  is *above* Evolution).  Both existing copies already carry a "canonical home is
  `Geometry/Metric/Basic.lean`" note.  **Ledger item**: promote it, 3 occurrences now.
* **Positive-definiteness of the fibre norm** went through the public
  `MetricFiberData.inner_self_eq_zero_iff` (`Geometry/Metric/TensorInner/MetricFiberData.lean:90`),
  not through a new `normSq0S_eq_zero_iff`.  There is no such public wrapper in
  `Tensor0SMetric.lean`/`Tensor0SMetricIneq.lean`; **ledger item**: `normSq0S` positive-
  definiteness is the natural missing companion of `normSq0S_nonneg` and belongs in
  `Tensor/RSTensor/FiberMetric/Tensor0SMetric.lean`.
* **Plain hypothesis lists, no bundling structure.**  `metrics_eq_on` repeats
  `energy_zero_on`'s ~30 hypotheses.  A `structure`+`Is…` package would be the Mathlib answer,
  but K4 itself carries 25 plain named hypotheses and its docstring makes the "nothing hidden
  in an instance" discipline explicit, so consistency with the lane won.  If K6 finds the
  signature unwieldy, the right refactor is one data/predicate pair covering K3+K4+K5 at
  once, not a K5-only bundle.
* **No borel `private local instance` block was needed.**  `riemannianMeasureFamily` bakes
  its `MeasurableSpace M` into the term, so `Integrable … (riemannianMeasureFamily g₁ t)` and
  `integral_eq_zero_iff_of_nonneg` elaborate without re-declaring the instances (same as
  `ForwardUniqueRateLe.lean` / `ForwardUniqueIBP.lean`, unlike `ForwardUniqueEnergy.lean`).
  `Continuous.ae_eq_iff_eq` needs only `IsOpenPosMeasure`, not `BorelSpace`.

## Lean lessons (durable)

* **`ge_of_tendsto`, not `le_of_tendsto`.**  The edge-Grönwall closure has
  `E(t) ≤ E(ε)·exp(K(t−ε))` eventually and `E(ε)·exp(…) → 0`, i.e. the *bound* is on the
  left of the limiting family — that is `ge_of_tendsto`.  The `Icc 0 T` copy in
  `EdgeStrongData.lean:118` uses `le_of_tendsto` at the corresponding step and fails to
  elaborate here; that file has no olean, so its "green" status is not verified in this
  checkout.  **Do not copy proofs out of unbuilt files without re-checking them.**
* **`le_gronwallBound_of_liminf_deriv_right_le` needs `(ε := 0)` named explicitly.**  Its
  `bound` field is `f' x ≤ K * f x + ε`; handing it a proof of `f' x ≤ K * f x` does not
  unify (`K * f x + ?ε =?= K * f x` has different head symbols and Real addition will not
  reduce).  Pass `(ε := 0)` and close the field with `linarith`.
* **`gronwallBound_ε0`** is the rewrite that turns the Grönwall bound into
  `δ * Real.exp (K * (x − a))`; `simpa only [gronwallBound_ε0]` after the application.
* **`Continuous.ae_eq_iff_eq` takes the measure as its first explicit argument**
  (`variable (μ) in` in `Mathlib/MeasureTheory/Measure/OpenPos.lean:140`), and needs only
  `[μ.IsOpenPosMeasure]` plus a T2 codomain — no `OpensMeasurableSpace`/`BorelSpace`.
* **`Tensor0SSpace` evaluation of `0`** is `Tensor0SSpace.zero_apply` (`@[simp]`,
  `Tensor/RSTensor/Defs.lean:161`, proved by `rfl`).  Pairing it with `metricDiffAt_apply`
  and `norm_num` discharges the `if i = 0 then X else Y` slot vector without `fin_cases`.
* **`normSq0S g x s A` is `rfl`-equal to `(tensor0SMetricData g x s).inner A A`**, so both
  directions of positive-definiteness are one-liners:
  `((tensor0SMetricData g x s).inner_self_eq_zero_iff A).1 h` / `.2 rfl`.

## What is NOT done

K5 is the *scalar* closure only.  The endpoint `ricci_flow_forward_unique`
(`ExtendViaUniqueness.lean:201`) is **not** touched: K6 must still (a) manufacture the K3+K4
slab package for each `c ∈ Ioo a b` from the endpoint's own hypotheses, (b) discharge the two
regularity inputs `hdcont`/`hcont` from the chart-Gram tower (the `hdens` debt of №6(i)),
and (c) wire `metrics_eq_ico` into the endpoint statement.  Nothing in this file makes the
endpoint's remaining frontier smaller — it only makes the last mile mechanical.
