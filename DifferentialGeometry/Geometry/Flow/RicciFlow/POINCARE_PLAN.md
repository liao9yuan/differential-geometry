# POINCARÉ PROGRAM PLAN — Perelman's proof as the project endpoint

Written 2026-07-05 (planning lane), at the user's request: a detailed plan for
taking **Perelman's proof of the Poincaré conjecture, excluding its topological
part**, as the long-range endpoint.  Anchor text: **Morgan–Tian** (local LaTeX
under `RicciFlow/Morgan-Tian/`) — the only complete Poincaré-only writeup, and
the project rule is to follow the book's structure exactly.  Chapter names
below refer to its files (`prelim` (two chapters), `flowbasics`, `maxprin`,
`converge2`, `newcompar`, `newcomp2`, `noncoll`, `temp2kappa`, `bddcurvbdddist`,
`singlimit2`, `stdsoln`, `surgery` (4 chapters), `energy1`, `canonnbhd`).
There is no `nonnegcurv.tex` in this snapshot: that chapter (`Manifolds of
non-negative curvature`, label `nonnegcurv`) is the second chapter of
`prelim.tex`, starting at `prelim.tex:1068`.

Live status refreshed 2026-08-29.  The current companion sources are:

* `DimensionThree/PositiveRicci/AxiomCheck.lean` for the checked Hamilton
  endpoint (Phase P0);
* `Compactness/` for the provider-native Hamilton compactness implementation;
* `../../../Comparison/P1_COMPARISON_PLAN.md` for the ordered P1a--P1c
  comparison-geometry campaign;
* `Perelman/L_GEOMETRY_PLAN.md` for the active P2 execution lane.

The former `DimensionThree/HAM3_BLACKBOX_PLAN.md` and
`HCGCompactness/PROJECT_MAP.md` paths no longer exist in this checkout and must
not be used as live status sources.  Older dated entries in this document are
historical snapshots; the inventory, phase annotations, execution order, and
scale estimate below are the current authority.

## 0. Scope ruling and the endpoint statement

**Scope ruling — CORRECTED 2026-08-29, superseding the 2026-07-05 reading.**
The GEOMETRIC/ANALYTIC surgery construction (δ-necks, the surgery metric, Ricci
flow with surgery as an analytic object, its noncollapsing and
canonical-neighborhood induction) is IN scope, unchanged.  What changed: the
earlier reading of "除拓扑 surgery 部分" — that the topological inputs T1–T4 are
permanently CITED — was a misreading, withdrawn at the user's instruction.
**T1, T2, T3 and T4 are all in scope and must end as Lean theorems.**  Their
execution plan is the T-lane, `../../../Topology/T_TOPOLOGY_PLAN.md`; this
document keeps the P-phase analytic content only, and the two lanes meet at P9.

`PoincareTopologyInputs` survives only as a temporary STAGING bundle, so that
the analytic lane is never blocked by the T-lane: each field states exactly one
T-target, the T-lane discharges the fields one at a time, and the bundle must be
EMPTY by program end (the same standing requirement `PerelmanAnalyticInputs`
already carries).  The four fields, with their Morgan–Tian usage:

* T1 — a closed simply-connected 3-manifold has `π₃ ≠ 0` (homotopy-sphere
  facts: Hurewicz + Poincaré duality; not in Mathlib);
* T2 — reconstruction after extinction: if the Ricci flow with surgery on `M`
  goes extinct in finite time, `M` is a connected sum of space-form quotients
  and `S²×S¹`-pieces (the topological bookkeeping of surgeries);
* T3 — the final identification: a simply-connected such connected sum is `S³`
  (uses T2's pieces + elementary 3-manifold topology);
* T4 — every time-slice component of the Ricci flow with surgery started from a
  closed simply-connected `M` is again closed and simply connected, hence has
  `π₂ = 0`.  It splits into T4(a), the flow-free statement that a closed
  simply-connected 3-manifold has `π₂ = 0` (same Hurewicz + duality engine as
  T1), and T4(b), the surgery-stability statement, which is GATED on the P6b
  RFWS object.  T4 is what lets P8 run in the Poincaré-only form that skips
  Morgan–Tian's π₂ section; the alternative is to build the Sacks–Uhlenbeck
  minimal-2-sphere layer (P8a).  Now that T4 is a proof obligation rather than a
  citation, the P8 ruling is a workload choice between two proved routes, not
  between a proof and an axiom.  See P8 in §2 and §3 items 11–13.

**Endpoint (staging form, during the program):**
`poincare_of_inputs : Closed3Manifold M → SimplyConnected M →
PoincareTopologyInputs M → PerelmanAnalyticInputs M → HomeomorphicToSphere M`
— both bundles EMPTY by program end.  If any analytic item is later demoted to a
citation, it moves into an explicit bundle field, never a hidden wrapper
(2026-07-05 audit rule).

**Endpoint (final, unconditional).**  Mathlib already carries the target as a
`proof_wanted` in `Mathlib/Geometry/Manifold/PoincareConjecture.lean`:
`SimplyConnectedSpace.nonempty_diffeomorph_sphere_three`, i.e.
`[T2Space M] [ChartedSpace ℝ³ M] [IsManifold (𝓡 3) ∞ M] [SimplyConnectedSpace M]
[CompactSpace M] : Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ 𝕊³)`.  Adopting that exact shape as
the joint P-lane/T-lane endpoint is free and removes later restatement risk.

## 1. What the tree already has (live inventory, 2026-08-27)

| Layer | State |
|---|---|
| Tensor/curvature calculus, evolution equations | mature (`Evolution/` 51 files; Uhlenbeck/BBS bricks) |
| Weak maximum principles (scalar + tensor) | in-tree (`MaximumPrinciple/`) |
| Dimension-3 pinching (Hamilton §9/§10), compact smooth flow | checked (`DimensionThree/`) |
| Short-time existence (DeTurck) | checked on the P0 path; included in the direct axiom audit |
| Extension/maximal time | checked on the P0 path through `exists_max_flow` and `rmUnbounded_of_maximal` |
| **Riemannian volume, divergence thm, IBP, L², volume variation** | **0-sorry** (`Analysis/Integration/`) |
| W/F entropy definitions + first-variation lane | started (`Entropy/`) |
| Comparison geometry: geodesics, Jacobi, Gauss lemma, index form, convexity, Bonnet–Myers, Hopf–Rinow(proper), injectivity radius | substantial; the Bishop–Gromov/CGT producers used by P0 are checked |
| Hamilton compactness (M–T Ch `converge2` ≈ MSM135 3.9/3.10) | provider-native endpoint checked under `RicciFlow/Compactness/` |
| Hamilton positive-Ricci endpoint | `hamilton_positive_ricci` checked and direct-axiom audited |
| Fixed-manifold L-geometry | monotonicity, zero-time limit, uniform ball upper bound, and the compact smooth-flow `smooth_nlc` capstone are checked and direct-axiom audited |
| Smooth gluing / jet splice (surgery seed) | engine built, 2 gates (`hglue` lane) |
| Space forms / quotients | active lane |
| Curvature *pinched toward positive* for generalized flows / RFWS | **absent** — the checked pinching is the compact smooth-flow version only (§3 item 11) |
| Shi derivative estimates | compact whole-manifold and P2 ball-local `shiRm1_ball` are checked; `movingShi_complete` is the focused-green complete bounded-curvature solution endpoint (§3 item 12) |
| Parabolic rescaling formalism, pointed flow sequences | in-tree |
| Final Poincaré assembly | `poincare_of_inputs` is not yet declared |

Missing layers are the subject of §3.

Two traps for future agents (2026-08-27 audit).
`Compactness/CheegerGromov/Pointed/Compactness.lean:1321` defines
`metricCompactness` as `by sorry`; it is dead legacy code superseded by the
live producer of the SAME NAME at `Compactness/Metric/Endpoint.lean:48`, which
is the one P0 actually routes through. The former
`BernsteinTower.estimate_complete` was also off the audited P0 path: its
arbitrary-metric statement lacked the Kato and cutoff inputs used by the proof.
It and its sole unused private caller were removed on 2026-08-30; the actual
complete bounded-curvature solution endpoint is `movingShi_complete`.

## 2. Phase plan (mapped to Morgan–Tian)

**P0 — Hamilton positive Ricci endpoint (complete).**  The provider-native
chain through short-time existence, maximal extension, volume/injectivity,
Hamilton compactness, and space forms closes
`HamiltonPositiveRicci.hamilton_positive_ricci`.  The dedicated
`PositiveRicci/AxiomCheck.lean` audit reports only `propext`, classical choice,
and quotient soundness.  P0 is **100%** as a theorem and remains the program's
completed toolchain validator.  This does not complete any later Poincaré
phase automatically.

**P1 — Comparison-geometry and volume upgrades** (M–T `prelim`, both chapters).
1. P1a Bishop–Gromov relative volume comparison.  Route: polar-coordinates
   Jacobian along radial geodesics + Riccati comparison; below-injectivity
   version needs NO cut locus, and upper bounds extend past `inj` via
   `vol(exp(B)) ≤ ∫_B Jac` (surjectivity onto balls from Hopf–Rinow).  Assets:
   `JacobiFormula`, Jacobi-field ODE bricks, `riemannianVolumeMeasure`.
   **Live status:** the comparison/packing producers consumed by the P0
   compactness route are checked.  Any broader Morgan–Tian use must still be
   audited against its exact hypotheses rather than inferred from P0.
2. P1b Cheeger–Gromov–Taylor injectivity-radius decay (volume ⟹ inj via
   Cheeger's lemma / short geodesic loops).  **Live status:** the P0/Hamilton
   producer is checked (`intrInj_ge_cgt` through `injDecay_of_bg`).
3. P1c Laplacian comparison + Busemann functions + Cheeger–Gromoll splitting
   + the **Cheeger–Gromoll soul theorem** (needed by P3's asymptotic-soliton
   argument; M–T `prelim.tex` ch. 2, `soul` stated at `prelim.tex:1304`).
   The soul theorem is a separate classical endpoint, not a corollary of
   splitting, and the 2026-08-27 audit found it consumed in two different
   ways: `temp2kappa.tex:2293` uses “positive curvature ⇒ the soul is a
   point”, while `temp2kappa.tex:3581/3612/3714/3727` use soul POINTS `p_k`
   of noncompact κ-solutions as the basepoints of a blow-up sequence.  Both
   uses belong in the frozen P1c consumer list.  (~3–4 months.)
4. P1d Toponogov comparison, the M–T-used statements only.  Hardest classical
   item; audit `temp2kappa`/`bddcurvbdddist` first for the exact list actually
   consumed and prove only those.  (~3–6 months, deferrable until P3.)

**P2 — Perelman reduced geometry (L-length) + κ-noncollapsing** (M–T
`newcompar`, `newcomp2`, `noncoll`).
L-geodesics, L-exponential, L-Jacobi/index comparison, reduced length/volume,
monotonicity (Jacobian route, no PDE existence), κ-noncollapsing of smooth
flows, and the bounded-curvature-complete-flow chapter (`newcomp2`) it leans
on.  This layer is mandatory here even though P0 fills `ham3_noncollapse` via
the W-route: **surgery-stable noncollapsing (P6) is L-length-based.**
Measure-theoretic pole: integrating over the L-exponential domain with a
measurable cut-type decomposition.  (~8–12 months.)

Execution plan: `Perelman/L_GEOMETRY_PLAN.md`.  The fixed-manifold ordinary
flow layer is built first; generalized surgery-space-time paths are a later
extension and must not contaminate the basic L-length API.

**Live status:** the compact fixed-manifold L0–L7 core and ordinary smooth-flow
L9 capstone are checked.  `redVolume_anti`, `redVolume_zero_lim`,
`exists_redLen_le`, `redVolume_late_low`, `redVolume_ball_unif`, and
`smooth_nlc` are stated and proved; the last two and the capstone pass the P2
direct axiom audit with only the standard three axioms.  The completed producer
chain is

```text
shiRm1_ball -> lGrad_ball -> lRegSpeed_unif
  -> lMetric_ball + lRegRange_unif -> lExp_ball_unif
  -> redVolume_ball_unif
  + redVolume_late_low -> IsKappaNoncollapsed -> smooth_nlc.
```

Here `redVolume_ball_unif` chooses its short-scale threshold before the flow,
terminal time, center, and actual radius, and the dimension-generic
`smooth_nlc` converts the late reduced-volume floor into the canonical
`NoLocalCollapsing` predicate while using the initial small-ball volume estimate
for early times.  The theorem
`smooth_nlc` and its dedicated compact ordinary-flow assembly are **100%**.
The remaining complete bounded-curvature L8 refinements and surgery/eventwise
L9 extension stay separate later endpoints; the latter cannot begin until the
P6b RFWS event/seam object exists.

**P3 — κ-solutions** (M–T `temp2kappa`).  Ancient κ-noncollapsed solutions:
Hamilton's Li–Yau–Hamilton Harnack inequality (new tensor-MP computation, big
but native to the tree's strengths), strong maximum principle (scalar Hopf
lemma + tensor kernel-holonomy splitting — NEW layer, see §3-6), asymptotic
shrinking soliton via reduced volume (consumes P2), classification of 3d
shrinking solitons, compactness of κ-solutions, universal κ, the
`canonnbhd` appendix vocabulary.  The heaviest pure-geometry phase.
(~6–10 months.)

**P4 — Bounded curvature at bounded distance + limits of generalized flows**
(M–T `bddcurvbdddist`, `singlimit2`).  Blow-up arguments against κ-solution
structure; extends the HCG compactness interface to generalized (space-time)
flows and partial/local convergence.  Depends: P2, P3, HCG done.  (~4–6 months.)
**Prerequisite added by the 2026-08-27 audit:** essentially every statement of
`bddcurvbdddist` and `singlimit2` is hypothesized on flows whose curvature is
*pinched toward positive* (`bddcurvbdddist.tex:22`, `:65`, `:140`, weak form at
`:709`) — the Hamilton–Ivey estimate in its GENERALIZED-flow form, preserved by
surgery and stable under blow-up limits.  The checked `DimensionThree/`
pinching is the compact smooth-flow version and does not supply this.

**P5 — The standard solution** (M–T `stdsoln`).  Existence + uniqueness +
canonical-neighborhood structure of the standard flow on ℝ³.  Noncompact
existence/uniqueness is genuinely hard analysis; M–T's own route keeps it
semi-self-contained.  Needs the linear parabolic layer (§3-1) at full strength.
(~4–6 months.)  Execution plan: `P5_STANDARD_SOLUTION_PLAN.md`.

**Live ruling (2026-08-29):** P5 may start now with its standard initial metric,
compact-double existence, scoped noncompact parabolic, symmetry, and uniqueness
lanes.  Its terminal `T=1` and canonical-neighborhood package remains gated by
the complete-flow P2 bridge and the P3/P4 kappa-limit inputs.  P5 is therefore
open for implementation but remains 0% as a completed theorem.

**P6 — Surgery** (M–T `surgery.tex` chapters 13–15: δ-neck surgery, Ricci flow
with surgery as a formal object, controlled RFWS).  Two distinct workloads:
1. P6a the surgery METRIC: δ-neck recognition + the gluing construction —
   direct continuation of the live `hglue` lane (jet splice engine done).
2. P6b the RFWS FORMAL OBJECT: space-time generalized flows, surgery times,
   parameter sequences `(r_i, δ_i, κ_i)`.  This is the largest formalization
   DESIGN problem of the program (manifold changes at surgery times); M–T's
   space-time formulation is the design template.  Prototype the object early
   (see execution order).  (~6–9 months combined.)

**P7 — Noncollapsing and canonical neighborhoods for RFWS + existence of the
controlled flow** (M–T `surgery.tex` ch. 16 + completion chapter).  The grand
induction on surgery times: L-length arguments crossing surgery regions
(consumes P2 hard), canonical neighborhoods propagate, parameters can be
chosen.  The assembly summit of the program.  (~5–8 months.)

**P8 — Finite-time extinction** (M–T `energy1`).  The 2026-08-27 audit found
the previous entry described only the second of TWO analytically different
halves, and mislabelled `W₂`:

1. P8a, the π₂ half (`energy1.tex:280` ff.).  `W₂(t)` is the minimal AREA of a
   homotopically non-trivial 2-sphere in a component; it is used to prove that
   after a finite time every component has trivial π₂.  Its existence theory is
   harmonic-map / minimal-sphere theory: `energy1.tex:597` cites Sacks–Uhlenbeck
   Theorem 3.3 directly, and the α-energy / Palais–Smale / bubbling argument is
   reproduced at `energy1.tex:597-636`.  This layer is not in the tree.
2. P8b, the π₃ half (`energy1.tex:93` ff.).  A non-trivial element of `π₃(M)`
   is represented in `π₂(ΛM)`, the width `W` of a loop sweepout is estimated
   under curve-shortening plus ramps, and the derivative estimate forces
   extinction (input T1).  This is the Altschuler–Grayson-grade
   curve-shortening layer of §3-7.  It consumes P8a: the loop-width argument
   runs on components with trivial π₂.

**Open ruling, required before P8 starts** (restated 2026-08-29).  Either
(a) build the Sacks–Uhlenbeck minimal-2-sphere layer — a genuine new analytic
frontier, comparable in size to §3-7 — or (b) take the Poincaré-only route and
skip P8a, which is legitimate exactly when T4 is available.  Since T4 is now a
T-lane proof obligation rather than a citation (§0), route (b) is no longer a
shortcut past a proof: it is a choice to spend the work in the T-lane
(T4(b), gated on P6b) instead of in a new analytic layer.  Recommendation
unchanged in direction, now honest in cost: prefer (b).  Do not reinstate the
pre-audit situation, in which the plan assumed (b)'s conclusion while §3
declared harmonic-map machinery out of scope and §0 carried no T4.

Dependency correction: P8's statement consumes Theorem `MAIN`, the RFWS defined
for all `t ∈ [0,∞)` (`energy1.tex:7`).  P8 may therefore be DEVELOPED against
the RFWS interface as soon as P6b exists, but it is not provable before P7.
(~5–8 months for P8b, plus a comparable block for P8a under ruling (a).)

**P9 — Assembly.**  `poincare_of_inputs` from P6–P8 + T1–T3, plus T4 if P8
took ruling (b); then the T-lane's discharge of the four bundle fields turns it
into the unconditional endpoint of §0.  (~1–2 months for the P-side wiring; the
T-side is `Topology/T_TOPOLOGY_PLAN.md`.)

## 3. Infrastructure gap list (the direct answer to "还需要哪些东西")

Ordered by how many phases consume them:

1. **Linear parabolic PDE on closed manifolds** (existence, uniqueness,
   regularity/Schauder-or-L² for scalar and tensor equations with
   time-dependent smooth coefficients).  Consumers: P0/A1 (conjugate heat),
   P5, P8.  **Current ruling:** the P0-required closed-manifold path is checked;
   noncompact standard-solution and curve-shortening variants remain future
   scope and must be audited separately.
2. **Volume comparison package** (P1a/P1b): Bishop–Gromov + Cheeger lemma +
   CGT.  Consumers: P0, P2, P3.  **Current ruling:** the P0/Hamilton uses are
   discharged; audit any stronger P2/P3 use before declaring the whole package
   complete.
3. **L-geometry layer** (P2): L-geodesics through reduced volume.  The compact
   fixed-manifold monotonicity, zero-time normalization, uniform controlled-ball
   route, and `smooth_nlc` are checked.  Remaining work is the distinct L8
   complete bounded-curvature refinement and, after P6b supplies an RFWS
   event/seam object, the surgery/eventwise extension used by P7.
4. **Splitting/Busemann + the Cheeger–Gromoll soul theorem + Toponogov
   (used-statements-only)** (P1c/P1d).  Consumers: P3, P4.  The soul theorem
   (`prelim.tex:1304`) is a separate endpoint from splitting and is consumed
   by `temp2kappa` both as “soul is a point” (2293) and as soul BASEPOINTS of
   noncompact κ-solutions (3581, 3612, 3714, 3727).
5. **Hamilton's Harnack inequality** (matrix LYH).  Consumer: P3.
6. **Strong maximum principles** (scalar Hopf lemma; tensor strong MP with
   kernel holonomy/splitting).  Consumers: P3 (soliton classification), P5.
7. **Curve-shortening flow in evolving backgrounds** (existence, curvature
   bounds, Grayson-type behavior as M–T uses it).  Consumer: P8b only.  The
   analytic LAYER is self-contained and delegable; the P8 endpoint it feeds is
   not (it consumes item 13 or T4, and Theorem `MAIN` from P7).
8. **Generalized/space-time flows + the RFWS object** (P6b).  Consumers:
   P4, P6, P7, P8.  Design-heavy; prototype early, freeze late.
9. **Compactness extensions** (P4): Hamilton compactness for generalized flows
   and local limits.  Build on the checked `RicciFlow/Compactness/` machinery,
   not the removed `HCGCompactness/PROJECT_MAP.md` path.
10. **Noncompact uniqueness** (standard solution scope only; M–T's argument,
    not full Chen–Zhu).  Consumer: P5.
11. **Hamilton–Ivey pinching for generalized flows and RFWS** (“curvature
    pinched toward positive”): preserved by surgery, stable under blow-up
    limits, including the weak form at `bddcurvbdddist.tex:709`.  Consumers:
    P4, P6, P7.  Not supplied by the checked compact smooth-flow pinching.
12. **Shi derivative estimates beyond the compact whole-manifold case.** The
    local controlled-ball theorem `shiRm1_ball` used by `smooth_nlc` is checked.
    `movingShi_complete` is the native complete bounded-curvature solution
    endpoint, assembling the existing barrier, Kato, and cutoff producers. The
    obsolete under-specified generic declaration and its dead caller have been
    removed. Focused regression is green, and the 32-endpoint direct audit shows
    only `propext`, `Classical.choice`, and `Quot.sound`. Remaining P2b gaps are
    reduced-geometry consumers, not another Shi wrapper.
13. **(Conditional on the P8 ruling) minimal 2-spheres / Sacks–Uhlenbeck.**
    Needed iff P8a is proved rather than replaced by T4.  Consumer: P8.
14. **3-manifold topology T1–T4 — IN SCOPE as of 2026-08-29**, no longer an
    excluded citation bundle.  Engines: singular homology with excision and
    Mayer–Vietoris, cellular/Morse comparison, Hurewicz in degrees 2–3,
    Poincaré duality for closed 3-manifolds, Seifert–van Kampen, connected sum,
    and the surgery bookkeeping gated on P6b.  None of it is in Mathlib
    `v4.29.0` (audited 2026-08-29) — but most of it EXISTS, sorry-free and
    axiom-clean, in the Lean 4.33 extraction at
    `E:/testdifferential-geometry-t1-433` (singular homology + Mayer–Vietoris,
    Hurewicz 1–6, sphere homology, Seifert–van Kampen, Morse/handle machinery),
    which is derived from this repo's own root `Solution.lean`.  What is still
    missing for T1 is the handle chain complex computing `H_*` plus `χ(M³) = 0`;
    Poincaré duality turned out NOT to be required.  Consumers: P8 (via T4), P9.
    Full plan: `../../../Topology/T_TOPOLOGY_PLAN.md`.

Explicitly NOT needed (avoid scope creep): full Alexandrov-space theory
(M–T avoids it; only Toponogov-level statements), prime decomposition and
geometrization-grade topology, Perelman's §8–§10 function theory beyond what
`noncoll` uses.  The former fourth entry, “harmonic-map spectral machinery
(M–T's extinction is curve-shortening based)”, was WRONG and is withdrawn
(2026-08-27 audit): M–T's extinction chapter uses Sacks–Uhlenbeck minimal
2-spheres for its π₂ half.  Whether that layer is in or out of scope is the
open P8 ruling above, not a settled exclusion.

## 4. Execution order, parallel lanes, and the first quarter

Dependency spine:
```
P0 Hamilton positive Ricci ───────────────────────────── complete
P2 smooth_nlc ───────────────┐
P1c/P1d ─────────────────────┴──→ P3 ──→ P4 ──┐
P5 standard solution ──────────────────────────┼──→ P6/P7 ──┐
P6b RFWS object ────────────────────────────────┘            ├──→ P9
P6b RFWS object ────────────────────────────────→ P8 ────────┘
```

The last row means P8 can be DEVELOPED against the RFWS interface as soon as
P6b exists; its final statement still consumes P7's Theorem `MAIN`, and its
π₂ half additionally consumes §3 item 13 or input T4.

Recommended immediate order:

1. **Audit and start P1c/P1d** against the exact P3 consumers: splitting/
   Busemann first, and only the Toponogov statements Morgan–Tian actually uses.
2. **Design P6b early but do not contaminate P2:** write and review the RFWS
   event/seam object before P4–P8 depend on it.
3. **Continue the distinct L8 complete bounded-curvature refinement** from the
   actual `movingShi_complete` solution endpoint; only after the P6b event/seam
   object exists should the surgery/eventwise L-length extension begin.
4. **Two rulings that must be made before their phases open, not during
   them:** the P8a/T4 ruling of §2, and how “pinched toward positive” will be
   carried by the P6b RFWS object (it is a hypothesis of nearly every P4/P6/P7
   theorem, so the object must be able to state it from day one).
5. **Open the T-lane in parallel** (`../../../Topology/T_TOPOLOGY_PLAN.md`).  It
   shares essentially no code with the analytic tree, its first two stages
   (statement file, Seifert–van Kampen) are unblocked today, and its long pole
   — the singular-homology core — is the item most likely to become the
   program's critical path if it starts late.

## 5. Honest scale estimate

Use two separate denominators:

* final theorem `poincare_of_inputs`: **0%**, because it is not yet declared;
* P0 theorem `hamilton_positive_ricci`: **100%**, direct-axiom audited;
* compact ordinary-flow L-geometry through `smooth_nlc`: **100%** dedicated
  machinery for that scoped stage, with `redVolume_anti` and `smooth_nlc`
  each **100%** and direct-axiom audited;
* complete bounded-curvature L8 refinements and surgery/eventwise
  noncollapsing: separate incomplete stages, not counted in `smooth_nlc`;
* full P0–P9 ANALYTIC program infrastructure: approximately **15–25%**, with an
  explicitly unreliable denominator (see the warning below);
* T-lane (T1–T4, in scope since 2026-08-29): each target **0%**, dedicated
  machinery **~5–10%** (Morse/handle/cell attachment, covering spaces, de Rham
  complex exist; homology, duality, Hurewicz, van Kampen, connected sum do not).
  The T-lane is roughly **20–30% of the remaining total work**, so the whole
  project including topology is approximately **12–20%**.

The last range uses the phase workload, not file or lemma counts, and avoids
double-counting infrastructure shared by P0, P1, and P2.  The old **3–5%**
snapshot is superseded: it predates the axiom-clean P0 endpoint and both
reduced-volume capstones.  The former 2.5–4 year calendar estimate is also not
treated as current until the P3–P6 design work is re-estimated.

**Denominator warning (2026-08-27 audit).**  P3–P8 have never been scoped at
file level, and this audit found three consumed layers the plan had not counted
at all (§3 items 11–13).  Any single percentage here is a guess about work that
has not been decomposed: treat the phase ordering and the gap list as the real
content, and the number as an upper-bounded guess.  The per-phase month
estimates are stale for the opposite reason — they predate the observed lane
throughput (the P2 lane went from kickoff on 2026-08-15 to a checked L0–L7 core
plus most of L8 within two weeks, at 153 files and ~63k lines) — so they should
be re-derived from measured lane velocity or dropped, not cited as planning
input.

## Status log

- 2026-07-05: plan written (with `HAM3_BLACKBOX_PLAN.md`).  Decisions OPEN for
  the user: (i) adopt the program (this document is a plan, not a commitment);
  (ii) `ham3_noncollapse` Route A vs B (recommendation: A); (iii) green-light
  the two immediate new lanes (P1a Bishop–Gromov, §3-1 parabolic scalar layer).
- 2026-07-05 (later): user reports §3-1 (linear parabolic PDE) is essentially
  done by a collaborator, pending merge — gap list item 1 becomes an
  integration task, and NLC Route A's pole shrinks accordingly.  **P1a volume
  comparison green-lit and planned**: `Geometry/Comparison/
  VOLUME_COMPARISON_PLAN.md` (asset audit + stages V1–V3; V1 needs no new
  foundations — the integration layer and the Jacobi/Grönwall/Bonnet–Myers
  engines are all in-tree and 0-sorry).
- 2026-08-21 (P2 ordinary L-geometry): the fixed-manifold L0--L2 layer and the
  current L3 regularized-ODE layer are migrated and focused-green.  Local phase
  and intrinsic solutions have existence and arbitrary-base-time germ
  uniqueness.  In `Perelman/LGeometry/Exp.lean`, witness independence now
  propagates across connected overlap domains, the totalized maximal curve
  agrees with every witness, and a jointly smooth local phase flow produces
  regularized families for nearby initial tangent vectors.  Thus the
  regularized family is jointly smooth at `s=0`, and `lExp` is jointly smooth
  on a uniform short positive-time interval, with the correct `A(0)=2Z`
  normalization.

  The exact next P2 producer is `lRegFamily_extend`, which must continue the
  smooth parameter family across compact subintervals of a witnessed maximal
  solution before full-domain positive-time smoothness is claimed.  The
  capstone `redVolume_anti` remains **0%**; dedicated L-geometry is about
  **22--24%**, reusable generic prerequisites about **65--75%**, P2 remains
  below **1%**, and the whole program estimate remains **3--5%**.
- 2026-08-27 (live status supersedes the earlier snapshots): the dedicated
  Hamilton axiom check is green for short-time existence, the provider-native
  compactness route, and `hamilton_positive_ricci`; P0 is therefore 100% as a
  theorem.  `redVolume_anti` and `redVolume_zero_lim` are each stated, proved,
  and focused-check green. The later `exists_redLen_le`, `redVolume_late_low`,
  and fixed-terminal `redVolume_ball_eta` are also checked and pass the P2
  standard-axiom audit. `smooth_nlc` remains unstated and unproved. Its exact
  lowest missing producer is `shiRm1_ball`, because all current checked Shi
  theorems require whole-manifold curvature control. The final
  `poincare_of_inputs` theorem remains 0%; full-program infrastructure is
  estimated at 15–25% with the overlap caveat in §5.
- 2026-08-28 (plan audit against the Morgan–Tian source, performed 2026-08-27;
  read-only review, no code changed):
  three substantive plan defects and two smaller ones were fixed in this
  document.  (i) P8 described only its curve-shortening half and mislabelled
  `W₂`; the π₂ half needs Sacks–Uhlenbeck minimal 2-spheres, so the old
  “harmonic-map machinery not needed” exclusion is withdrawn and an explicit
  ruling — build P8a, or add T4 to the topology bundle — is now required before
  P8 starts.  (ii) P1c was missing the Cheeger–Gromoll soul theorem, which
  `temp2kappa` uses as basepoint data for noncompact κ-solutions.  (iii)
  “curvature pinched toward positive” for generalized flows/RFWS is consumed
  throughout P4/P6/P7 but was listed nowhere; the checked `DimensionThree/`
  pinching is only the compact smooth-flow version.  Also added: Shi beyond the
  compact whole-manifold case as a named gap (`estimate_complete` is a `sorry`,
  `shiRm1_ball` does not exist), the `nonnegcurv.tex` file correction
  (`prelim.tex:1068`), and the dead `metricCompactness := by sorry` name clash.
  Scale estimate lowered to 10–18% with an explicit denominator warning.  No
  theorem status changed by this audit: `smooth_nlc` and `poincare_of_inputs`
  both remain 0%, and P0 remains 100% and axiom-clean.
- 2026-08-29 (compact ordinary-flow P2 capstone): the full local producer chain
  `shiRm1_ball -> lGrad_ball -> lRegSpeed_unif -> lMetric_ball ->
  lRegRange_unif -> redVolume_ball_unif` is checked.  Together with the checked
  half-open floor `redVolume_late_low`, it proves the public theorem
  dimension-generic `smooth_nlc : NoLocalCollapsing S rho` for compact
  connected boundaryless smooth flows, in particular the three-dimensional
  Poincare consumer.  The theorem and its uniform ball producer
  pass the direct P2 axiom audit with only `propext`, `Classical.choice`, and
  `Quot.sound`.  This makes the compact ordinary-flow P2 capstone 100%; it does
  not complete the separate complete-bounded-curvature L8 refinements or the
  surgery/eventwise extension, which must wait for the absent P6b RFWS
  event/seam presentation.  `poincare_of_inputs` remains 0%, and whole P0--P9
  infrastructure remains approximately 15--25%.
- 2026-08-29 (P5 phase audit): `P5_STANDARD_SOLUTION_PLAN.md` freezes the
  standard initial metric, compact-double existence, complete-flow geometry,
  scoped noncompact uniqueness, and surgery-facing canonical-neighborhood
  packages.  P5 can start at its initial-geometry and compact-approximation
  gates without waiting for P3/P4, but its final canonical-neighborhood and
  `T=1` endpoints consume complete-flow P2 plus P3/P4 limit results.  The P5
  theorem remains 0%; no standard-solution theorem was claimed by this audit.
- 2026-08-29 (scope correction, no code changed): the §0 ruling that T1–T4 are
  cited inputs was withdrawn at the user's instruction.  T1–T4 are now proof
  obligations with their own lane and plan
  (`../../../Topology/T_TOPOLOGY_PLAN.md`), `PoincareTopologyInputs` is demoted
  to a temporary staging bundle that must be empty by program end, and the final
  endpoint is aligned with Mathlib's `proof_wanted`
  `SimplyConnectedSpace.nonempty_diffeomorph_sphere_three`.  The T-lane audit
  (same day, against the Mathlib `v4.29.0` pin) found no Hurewicz, no Poincaré
  duality, no excision or Mayer–Vietoris, no cellular homology, no van Kampen
  and no connected sum in Mathlib, and confirmed that this tree's ~63k-line
  sorry-free `Topology/Morse` + `Topology/Handle` layer, its covering-space
  layer and its de Rham complex are the lane's real starting assets.  No P-phase
  status changed: P0 stays 100%, the compact ordinary-flow P2 capstone stays
  100%, `poincare_of_inputs` stays 0%.  Whole-project estimate restated as
  ~12–20% once the topology lane is inside the denominator.
- 2026-08-29 (T-lane, second pass): the Lean 4.33 extraction at
  `E:/testdifferential-geometry-t1-433` was audited and its `AxiomCheck` re-run
  (sixteen endpoints, only the standard three axioms).  It supplies singular
  homology with Mayer–Vietoris, Hurewicz 1–6, `H_{n+1}(Sⁿ⁺¹) ≅ ℤ`,
  Seifert–van Kampen, Morse-function existence and handle cancellation, so the
  T-lane's planned homology/Hurewicz/van-Kampen builds are cancelled and the
  Poincaré-duality requirement for T1 is withdrawn.  Remaining T1 frontier: the
  handle chain complex computes `H_*`, plus `χ(M³) = 0`.  New open ruling R5
  (stay on 4.29 vs use the 4.33 project vs bump the tree) is in the T-lane plan.
  No P-phase status changed.
