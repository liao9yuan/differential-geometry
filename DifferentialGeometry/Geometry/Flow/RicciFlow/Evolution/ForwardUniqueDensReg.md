# ForwardUniqueDensReg — the `hdens` joint-regularity tower (brick TOWER)

Companion note for `ForwardUniqueDensReg.lean`.  Status **2026-07-26 (second pass)**: outcome
**(A) — the tower is CLOSED**.  All five deliverables are unconditional modulo the two honest
chart-Gram packages of `g₁` and `g₂`; the §3 frontier of the first pass (chart-frame components
of `A₀₃` and `S₀₄`) is discharged, and the closed-edge (`Ioo` vs `Icc`) gap is discharged too.

Verification: focused check GREEN and warning-free; targeted module build GREEN.  No `sorry`,
no new instances, axioms or notation.  Axioms of every endpoint:
`[propext, Classical.choice, Quot.sound]`.  File length 950 lines.

---

## 2026-07-26 (third pass, SLAB-2): the closed-edge upgrade

**What changed.**  The brick `normSq0S_jointContMDiffOn` and its two chart-component
producers no longer require `IsOpen J`; every joint statement in the file now holds for an
**arbitrary** time set `J`, so `J := Icc a c` (the closed initial edge) is admissible.  This is
the step `RicciDifferenceMeanValueWithin.md` §"The remaining step to a background sup" names,
and it is what turns black box (B)'s one-sided `Ico a b` chart-Gram field into slab-uniform
sups and into edge continuity of the Kotschwar energy.

Signature changes (hypothesis WEAKENING; downstream call sites drop an argument):

| declaration | before | after |
| --- | --- | --- |
| `normSq0S_jointContMDiffOn` | `(hJ : IsOpen J)`, `hA` a `ContMDiffAt` | no `hJ`, `hA` a `ContMDiffWithinAt … (J ×ˢ univ)` |
| `connChartJoint` / `rmChartJoint` | `(hJ : IsOpen J)`, conclusion `ContMDiffAt` | no `hJ`, conclusion `ContMDiffWithinAt … (J ×ˢ univ)` |
| `metricChartComp_jointContMDiffOn` | `Ioo a b` | arbitrary `J` (and the proof collapsed to `hgram x₀ i j` — the chart-frame component *is* the chart-Gram entry) |
| `metricDiffSq_/connDiffSq_/rmDiffSq_/dens_jointContMDiffOn` | `{a b}` on `Ioo a b` | `{J}` on arbitrary `J` |

**Why openness was never needed.**  `hJ` was used in exactly two places, both to produce
`J ×ˢ baseSet ∈ 𝓝 (t, x₀)`.  The base set of the trivialization at `x₀` is a *spatial*
neighbourhood of the chart centre, so `J ×ˢ baseSet` is a neighbourhood of `(t, x₀)`
**within** `J ×ˢ univ` for any `J` whatsoever.  That one-line observation is the new private
`prodOpen_nhdsWithin`; `ContMDiffWithinAt.mono_of_mem_nhdsWithin` then replaces every
`.contMDiffAt hnhd`, and `filter_upwards [hnhd]` becomes an eventual equality along
`𝓝[J ×ˢ univ]` closed by `ContMDiffWithinAt.congr_of_eventuallyEq` (which additionally wants
the value at the point — `EventuallyEq.self_of_nhdsWithin`).

**What was deleted.**  The four `private` helpers `genGram_of_joint`, `jointOnM`, `christJoint`,
`riemJoint` are gone: their `ContDiffWithinAt` replacements `genGramOn_of_field`,
`jointOnMWithin`, `christWithinM`, `riemWithinM` are public in
`Analysis/Parabolic/RicciLinearization/RicciDifferenceMeanValueWithin.lean`, which this file
now imports in place of `RicciDifferenceMeanValue.lean`.  No duplication remains.

**What was added.**

* `rm04ChartMap` — `rm04ChartComp` with the four slots given by an index map `K : Fin 4 → …`
  instead of `vec4`; the shape the brick consumes.
* `rm04ChartJoint` — the background-curvature component input, with the three metric roles
  independent: the *lowering* metric supplies the Gram factor, the *connection* metric supplies
  the chart Riemann coefficients (`riemWithinM`).  `(gL, gC) = (g₂, g₂)` is `Rm₂`;
  `(g₁, g₂)` is the cross-lowered `P` of `sdecFlux`'s re-lowering defect.
* `metricChartJoint` — the `(0,2)` carrier `metricTensorField (g t)`, whose chart-frame
  components are literally the chart-Gram entries.

**Lean lessons (this pass).**

* A `private` helper whose *statement* mentions neither `I` nor anything needing an
  `I`-dependent instance does **not** get `I` as a parameter, even though the proof body uses
  it.  The tell is `error: Invalid argument name 'I' for function …` at the call site with a
  hint listing the parameters.  `prodOpen_nhdsWithin` is such a helper — call it **without**
  `(I := I)`; `good_nhdsWithin` mentions `chartLeviCivitaGoodSet (I := I)` and therefore does
  take `I`.  (Same family as the `slabBound (M := M)` lesson in `ForwardUniqueSup.md`.)
* `ContMDiffWithinAt.prod` / `.sum` / `.mul` / `.mono_of_mem_nhdsWithin` /
  `.congr_of_eventuallyEq` all exist with the same shapes as their `ContMDiffAt` counterparts;
  the only extra argument anywhere is `congr_of_eventuallyEq`'s point-value side condition.
* `chartGramMatrix_apply` and `metricTensorField_apply` are both `rfl`, but `rw`'s closing
  `rfl` does not fire through the `Fin 2` slot map — write
  `rw [metricTensorField_apply, chartGramMatrix_apply]` explicitly.

**Verification.**  Focused check GREEN and warning-free; targeted module build GREEN; 0 `sorry`.
All endpoints (including the three new ones) 3-axiom clean.

---

## 1. Recon result — the "chart-Gram → Γ → Rm joint tower does NOT exist" debt is WRONG

Dispatch №6 recorded the `hdens` debt as: *"the chart-Gram → Γ → Rm joint tower does NOT
exist"*.  That is **false**.  A complete, **generic** joint tower already exists in

`Analysis/Parabolic/RicciLinearization/RicciDifferenceMeanValue.lean`

quantified over an arbitrary family `gfam : ℝ → SmoothRiemannianMetric I M`:

| decl | line | gives |
|---|---|---|
| `GenJointGram` | 401 | the hypothesis bundle (joint chart-Gram `C∞` on `ℝ × E` + Gram det positivity) |
| `genGram_of_family` | 417 | `MetricFamilySmoothOn` ⟹ `GenJointGram` (the `ℝ × M → ℝ × E` transport, reusable verbatim) |
| `gen_joint_invGram` | 476 | joint `C∞` of `chartInvGramOnE` |
| `gen_joint_gramBracket` | 600 | joint `C∞` of the Koszul bracket |
| `gen_joint_christoffel` | 619 | **joint `C∞` of `chartChristoffel`** |
| `gen_joint_partial_christoffel` | 673 | one more spatial derivative |
| `gen_joint_riemann` | 683 | **joint `C∞` of the chart Riemann coefficients** |
| `christ_of_family` | 640 | the same, transported back to `M × ℝ` (template for the transport direction) |

Plus the **intrinsic** bridges, which are the pieces that actually matter:

* `LeviCivita_chartBasisVec_alpha_basis_apply` (`Geometry/Connection/ChartBridge/Hessian.lean:1293`) —
  `(LC g) ∂_k (∂_l) (b) = ∑_m Γ(g, α)^m{}_{lk}(ϕ_α b) • ∂_m b`, on `chartLeviCivitaGoodSet α`.
* `riemannOp_chartBasisVec_alpha_eq`
  (`Geometry/Connection/ChartBridge/RiemannBasisIdentityOffCentre.lean:426`) — the **off-centre**
  Riemann analogue: `riemannOp (LeviCivita g) x (e_j)(e_k)(e_i) = ∑_l R(g,α)^l{}_{ijk}(ϕ_α x) • e_l x`,
  on `chartLeviCivitaGoodSet α`.  This was NOT in the first-pass inventory and is what made
  step 4 cheap.
* `riemannCurvatureAux_tangentConst_eq_riemannOp`
  (`Geometry/Curvature/MetricLeviCivitaReconcile.lean:111`) — the tensoriality bridge from the
  raw curvature on chart-constant extensions to the bundled `riemannOp`.

This is the **fourth** confirmed false wall in this project (cf. the memory entries on
BBS/Bochner over-counting, the A0′ L1 wall, and the P1.3 iterated-tangent-bundle wall).
Rule reconfirmed: grep for a *generic* producer before recording a layer as missing.

**Import surprise.** `RicciDifferenceMeanValue` (and `RiemannBasisIdentityOffCentre`, and
`MetricLeviCivitaReconcile`) are **already in the transitive closure** of the four original
imports of this file — the first-pass worry that using them "would drag the whole
`Analysis/Parabolic/RicciLinearization` subtree into `Evolution/`" was unfounded.  The R6 ruling
was exercised by adding `RicciDifferenceMeanValue` as an *explicit* import (honest dependency,
zero new modules in the closure); no other import was added.  Consequently
`chartInvGram_jointContMDiffOn` was **kept**, not retired in favour of `gen_joint_invGram`:
the local Cramer chain lives on `ℝ × M`, needs no `interior (extChartAt).target` membership and
no transport, and is strictly shorter at the call site.

Other inventory used:

* `ExtendedSolutionRegularity.lean:53` `metricCLMSection_jointContMDiffOn_of_chartGram_Ioo`
  and `:687` `metricFrameComp_jointContMDiffOn_of_chartGram`.  Consumed directly.
* `Geometry/Operator/Gradient.lean:252` `chartInvGramMatrix_entry_contMDiffOn` — the *spatial*
  Cramer proof, transcribed to the product source.
* `Geometry/Metric/ChartGram.lean:328` `chartGramMatrix_entry_contMDiffOn` — the *spatial*
  chart-Gram smoothness.  This is what makes the closed-edge producer unconditional (§3b).
* `Tensor/RSTensor/MetricTrace/Connection.lean:~700` `normSq0S_smooth`.
* `Analysis/Integration/Measure/Properties.lean`
  `riemannianVolumeMeasure_isFiniteMeasureOnCompacts` — the integrability producer.

## 2. What was proved (first pass, unchanged)

**The structural brick.**  `normSq0S_jointContMDiffOn`: for a metric family `g` with jointly
`C∞` chart-Gram entries and a `(0,s)`-tensor family `A` with jointly `C∞` chart-frame
components, `(t, x) ↦ |A t x|²_{g t}` is jointly `C∞` on `J ×ˢ univ` (`J` open).  Proved by the
`normSq0S_eq_coord` expansion against `chartBasisFamily`, with `chartInvGramMatrix` supplying
the inverse metric so that `chartInvGram_inverse` applies verbatim.

Supporting it, the **joint Cramer chain** on the product source `ℝ × M`:
`chartGramDet_jointContMDiffOn` → `chartGramAdj_jointContMDiffOn` →
`chartInvGram_jointContMDiffOn`.

**Deliverable 1 — `metricDiffSq_jointContMDiffOn`, unconditional** via
`metricFrameComp_jointContMDiffOn_of_chartGram` on `g₁` and `g₂`.

**Deliverable 2 — integrability.**  `integrable_of_continuous` plus the new `inner0S_smooth`
(polarization off `normSq0S_smooth`) discharge four of K5's eight `Integrable` slots with no
hypothesis: `hilap`, `hidiv`, `hinab`, `hidis`.  Reason: `metricNabla0S`, `covDiv0SField` and
`roughLap0SField` all return `Tensor0SField … ∞`, i.e. are **smooth by type**.

## 3. The former frontier — DISCHARGED

### 3a. Chart-frame components of `A₀₃` and `S₀₄` (steps 1–4 of the recorded route)

The one API change that made the composition painless: the brick's component hypothesis `hA`
was **weakened** from `ContMDiffOn … (J ×ˢ (trivializationAt …).baseSet)` to the pointwise
`∀ x₀ K {t}, t ∈ J → ContMDiffAt … (t, x₀)`.  That is exactly what the brick's proof uses (it
only ever evaluates `hA` at the diagonal point `(t, x₀)` with the chart centred at `x₀`), and it
dissolves the domain mismatch flagged in the first-pass plan: producers valid only on
`chartLeviCivitaGoodSet x₀` — a nbhd of the chart centre, strictly inside `baseSet` — now feed
the brick with no restriction juggling and no intersection bookkeeping.  Consumers of the old
shape only had to add `.contMDiffAt hnhd`.

* **Step 1 — `GenJointGram` from `hgram`.**  `genGram_of_joint` (private).  The second half of
  `genGram_of_family` was reused essentially verbatim, with `D.regular ↦ J` and
  `D.regular_isOpen ↦ hJ`, and `hsmooth` replaced by the `hgram` hypothesis itself.  The Gram
  determinant positivity conjunct is unconditional (`chartGramMatrix_det_pos`).
* **Step 2 — transport `ℝ × E → ℝ × M`.**  `jointOnM` (private), a *generic* helper taking any
  `F : ℝ → E → ℝ` with `ContDiffAt` at `(t, ϕ_α x)` and returning `ContMDiffAt` of
  `(t, x) ↦ F t (ϕ_α x)`.  Written in the `ℝ × M` factor order directly rather than adapting
  `christ_of_family`'s `M × ℝ` order; the only borrowed step is the model-space normalization
  `rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]`.  Specialized by `christJoint` and
  `riemJoint` (both private) to `gen_joint_christoffel` / `gen_joint_riemann`.
* **Step 3 — the `A₀₃` chart reading.**  `connChartComp`:
  `A₀₃(e_{K0}, e_{K1}, e_{K2}) = ∑_m (Γ¹ − Γ²)^m{}_{K0 K1}(ϕ_α x) · G¹_{m, K2}(x)` on
  `chartLeviCivitaGoodSet α`.  Route: `connDiffLowAt_apply`, then
  `IsCovariantDerivativeOn.difference_apply` on the section `b ↦ e^α_{K1} b` (differentiable at
  good-set points by `chartBasisVec_alpha_mdifferentiableAt`), then
  `LeviCivita_chartBasisVec_alpha_basis_apply` twice, then `sub_smul` + `inner_sum_left`.
* **Step 4 — the `S₀₄` chart reading.**  `rmChartComp`, on top of the genuinely new
  `rm04ChartComp` (below).  Slot bookkeeping: with `v = fun a => e^α_{K a} x`,
  `vec4 X Y Z W` has `X = e_{K0}, Y = e_{K1}, Z = e_{K2}, W = e_{K3}`, and matching
  `riemannOp cov x X Y Z` against `riemannOp cov x (e_j)(e_k)(e_i)` gives
  `j = K0, k = K1, i = K2`; hence the Riemann index pattern `R^l{}_{(K2)(K0)(K1)}`.
* **Joint upgrade.**  `connChartJoint` / `rmChartJoint`: the chart component is a finite
  polynomial in `Γ`/`R` (jointly `C∞` by steps 1–2) and the chart Gram (jointly `C∞` by
  `hgram₁`); the identity holds on the whole nbhd `univ ×ˢ chartLeviCivitaGoodSet x₀` of
  `(t, x₀)`, so `ContMDiffAt.congr_of_eventuallyEq` finishes.

### The mixed-object lemma (the one genuinely new statement)

```lean
theorem rm04ChartComp (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i j k n : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
        (metricCov_smooth (I := I) g₂) x
        (vec4 (I := I) (e^α_j x) (e^α_k x) (e^α_i x) (e^α_n x)) =
      ∑ l, chartRiemannTensor (I := I) g₂ α i j k l (extChartAt I α x) *
             chartGramMatrix (I := I) g₁ α x n l
```

i.e. the Riemann tensor of the **second** metric's Levi-Civita connection, lowered by the
**first** metric.  It was expected to be the risk of the whole pass; it took **11 lines** and
three rewrites:

1. `riemannCurvature04At_apply_const` — peel the lowering: `= g₁.inner x W (riemannCurvatureAux …)`.
2. `riemannCurvatureAux_tangentConst_eq_riemannOp` — chart-constant extensions ⟹ bundled
   `riemannOp`.  Needs the instance `ContMDiffCovariantDerivative (metricCov g₂) ∞`, supplied by
   `LeviCivita_isContMDiff g₂` (accepted by defeq).
3. `riemannOp_chartBasisVec_alpha_eq` on `g₂` — the off-centre chart reading of `riemannOp`.
   Reachable because `metricCov g = LeviCivita g` is **`rfl`** (the Koszul collapse); the
   `show … from rfl` bridge is copied from `Geometry/Curvature/CoordRm04Bridge.lean:48`.

Then `inner_sum_right` + `chartGramMatrix_apply`.  Taking `g₂ := g₁` gives the diagonal case,
so `rmChartComp` needs no separate treatment of `metricRm04At g₁` beyond the definitional
`metricRm04At g₁ x = riemannCurvature04At g₁ (metricCov g₁) _ x` (`rfl`).

**Why the first-pass estimate (250–450 lines, step 4 "the risk") was too pessimistic**: the
off-centre Riemann basis identity `riemannOp_chartBasisVec_alpha_eq` was missed in the recon —
only its *centred* sibling in `RiemannBasisIdentity.lean` had been noticed.  Total new content
≈ 340 lines including docstrings, of which the mixed object is 11.

### 3b. The closed-edge gap (`Ioo` vs `Icc`) — also DISCHARGED

The first pass recorded a "second, smaller gap": `dcont_idens_of_joint` covered `Ioo a b` while
K5/the assembly want `hdcont`/`hidens` on `Ico a b`, and the direct spatial route looked blocked
on the absence of a bundled smooth section for the connection difference.

That is now unnecessary.  At a **fixed** time the density depends only on the two static metrics
`g₁ t`, `g₂ t`, so the joint theorem applied to the two **constant** families
`fun _ => g₁ t`, `fun _ => g₂ t` on any window `Ioo (t−1) (t+1)` needs no time-regularity input
at all: the chart-Gram hypothesis degenerates to the purely spatial
`chartGramMatrix_entry_contMDiffOn`, composed with `contMDiffOn_snd`.  This gives

* `dens_continuous g₁ g₂ t : Continuous (fun x => forwardUniqueDensity g₁ g₂ t x)` — **for every
  `t : ℝ`, unconditionally**, and
* `dcont_idens g₁ g₂ t` — the `Continuous ∧ Integrable` pair, unconditionally.

`dcont_idens_of_joint` was **removed** (strictly subsumed); `dens_continuous_of_joint` is kept
because `dens_continuous` uses it.

### Assembly interface

Checked by construction against `ForwardUniqueAssembly.lean`'s `ForwardUniqueInputs`:

The `hdens`-tower group of `ForwardUniqueInputs` has **11** fields; **7** are now produced from
this file (the first four were the target of this pass, the last three were already banked):

| field | producer | status |
|---|---|---|
| `dens` (`Ioo a b ×ˢ univ`) | `dens_jointContMDiffOn g₁ g₂ hgram₁ hgram₂` | exact match |
| `densCont` (`Ico a b`) | `fun t _ => dens_continuous g₁ g₂ t` | exact match, **unconditional** |
| `densInt` (`Ico a b`) | `fun t _ => (dcont_idens g₁ g₂ t).2` | exact match, **unconditional** |
| `lapInt` | `fun t _ => ilap_integrable g₁ t (Sfield t)` | exact match, unconditional |
| `divInt` | `idiv_integrable` | exact match, unconditional |
| `nabInt` | `inab_integrable` | exact match, unconditional |
| `disInt` | `idis_integrable` | exact match, unconditional |

(`dens`, `densCont`, `densInt` and `lapInt` were checked by construction in a scratch probe
importing both modules; `divInt`/`nabInt`/`disInt` are the same pattern as `lapInt`.)

The **4** remaining `hdens`-tower fields are *not* chart-Gram/Γ/Rm regularity questions:

| field | why it is out of scope here |
|---|---|
| `energyCont` (`ContinuousOn (forwardUniqueEnergy g₁ g₂) (Ico a b)`) | a `t`-continuity / dominated-convergence statement about the *integral*, not about the density |
| `pairInt` | pairs `rmSpeed g₁ g₂ Svec t x`, built from the **bare pointwise** family `Svec` — no smoothness by type |
| `restInt` | pairs `rateRest … (connSpeed g₁ g₂ Avec)`, likewise bare pointwise (`Avec`) |
| `remInt` | pairs the **bare pointwise** remainder family `rem t x` |

All four need a continuity input on a bare pointwise speed family (or a convergence argument),
which is a K2-B/realization question, not a density-regularity one.

## 4. Lean lessons

* `metricDiffSq` / `connDiffSq` / `rmDiffSq` are plain `def`s over `normSq0S`; `simp only
  [connDiffSq_def]` first makes the unification robust and the proof readable.
* `ContMDiffAt.prod` is the `Finset.prod` lemma (the pair constructor is `prodMk`).
* `ContMDiff.div_const` does not exist at the manifold level; use `.mul contMDiff_const`.
* `normSq0S_eq_coord` wants `MetricInverseInBasis`, `chartInvGram_inverse` supplies
  `MetricInverseInBasis_gen` — definitionally equal, the mismatch elaborates away silently.
* `fun t ht => …` where the theorem's `t` is implicit trips the unused-variable linter — write `_t`.
* **New: do not ascribe a `T%`-notation type to a `MDiffAt` hypothesis.** Writing
  `have hσ : MDiffAt (T% fun b => chartBasisVecFiber α j b) x := …` fails with a bogus
  `failed to synthesize ChartedSpace (ModelProd H (ModelProd H E)) (TotalSpace E (TangentSpace I))`
  — the notation elaborates the total-space charts wrongly without an expected type.  Pass the
  term **directly** as the argument of the consuming lemma (here `difference_apply`) so the
  expected type drives elaboration.
* **New: destructure the product point at the start.** The brick previously did
  `rintro q ⟨hqJ, -⟩; set x₀ := q.2`, which then needs `Prod.mk.eta` juggling to feed a
  hypothesis stated at `(t, x₀)`.  `rintro ⟨t, x₀⟩ ⟨htJ, -⟩` removes the problem entirely.
* **New: `contMDiffAt_fst` has non-obvious implicit argument names** (`I`, `J`, not `I'`).  Do
  not use named arguments; state the instance you want with a `have … : ContMDiffAt … := contMDiffAt_fst`.
* **New: `metricCov g = LeviCivita g` is `rfl`** (post-collapse).  A local
  `have hLC : metricCov g = LeviCivita g := rfl` makes `rw` work where the chart bridges are
  stated in the `LeviCivita` spelling; for `riemannOp` the `show … from rfl` form is needed
  because the connection sits in an instance-implicit position.
* **New: pointwise-`ContMDiffAt` hypotheses beat `ContMDiffOn`-on-a-named-set hypotheses** when
  the consuming proof is local and the producers' natural domains differ (here `baseSet` vs
  `chartLeviCivitaGoodSet`).  Weakening the hypothesis was cheaper than intersecting domains.
* Stack-wide rules that applied unchanged: never `rw` on `Tensor0SSpace` FunLike coercions (use
  the term-form `Tensor0SSpace.sub_apply`); `omit [Inst] in` precedes docstrings.

## 5. Relocation TODOs (campaign end, not now)

* `inner0S_smooth` / `inner0S_continuous` / `normSq0S_continuous` belong next to
  `normSq0S_smooth` in `Tensor/RSTensor/MetricTrace/Connection.lean`; they are general
  `(0,s)`-field facts with nothing Ricci-flow about them.
* `inner_sum_left` / `inner_sum_right` are pure fibre-metric linearity; they belong in the
  `SmoothRiemannianMetric` / `PointwiseInner` layer, not here.  They are `private` for now.
* `integrable_of_continuous` duplicates the intent of the two existing copies of
  `Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure`
  (`Analysis/Integration/DivergenceTheorem/IntegrationByParts.lean:59` and
  `…/WithBoundary/Divergence/IntegrationByParts.lean:76` — **two identically-named lemmas in
  the same namespace**, which is itself a defect worth cleaning).  The family-level wrapper
  belongs in `Analysis/Integration/Measure/`.
* `chartGramDet_jointContMDiffOn` / `chartGramAdj_jointContMDiffOn` /
  `chartInvGram_jointContMDiffOn` belong beside their spatial counterparts in
  `Geometry/Operator/Gradient.lean`, or in a new `Geometry/Metric/ChartGramJoint.lean`.
* `connChartComp` / `rm04ChartComp` / `rmChartComp` are generic chart readings of intrinsic
  curvature/connection objects with nothing forward-uniqueness-specific about them.  Canonical
  home: `Geometry/Connection/ChartBridge/` (next to `RiemannBasisIdentityOffCentre`) for
  `rm04ChartComp`, and the connection-difference chart layer for `connChartComp`.  `rmChartComp`
  is the only one that mentions a `ForwardUnique*` carrier and may stay.
* `genGram_of_joint` / `jointOnM` / `christJoint` / `riemJoint` belong next to their `ℝ × E`
  originals in `Analysis/Parabolic/RicciLinearization/RicciDifferenceMeanValue.lean` (or a
  `…/JointChartTransport.lean` split), as the `ℝ × M`-order companions of `christ_of_family`.
* `normSq0S_jointContMDiffOn` — canonical home is the metric-trace/fibre-norm layer, once a
  second consumer appears.
