# T-LANE PLAN — T1–T4 (the topological inputs) as PROVED theorems

Written 2026-08-29 at the user's instruction: the earlier reading of
"除拓扑 surgery 部分" as *"T1–T4 are cited, never proved"* is withdrawn.
**T1, T2, T3 and T4 are all in scope and must end as Lean theorems.**
This document is the execution plan for that lane; `POINCARE_PLAN.md` §0 now
points here and keeps the P-phase (analytic) content.

Anchor text is Morgan–Tian (`RicciFlow/Morgan-Tian/`), same as the analytic
plan.  Every asset claim below was greped against this checkout and the pinned
Mathlib `v4.29.0` on 2026-08-29; nothing here is inherited from an older audit.

---

## 0. What changed, and what the endpoint becomes

Old ruling: `PoincareTopologyInputs` is a permanent citation bundle carrying
T1–T3 (and T4 under the P8 shortcut), and `poincare_of_inputs` consumes it.

New ruling: the bundle survives only as a **staging device**.  Each field is a
`Prop` that states exactly one T-target; the T-lane discharges the fields one at
a time; when the last field is discharged the endpoint becomes unconditional and
is restated in Mathlib's own shape, which already exists as a `proof_wanted`:

```lean
-- Mathlib/Geometry/Manifold/PoincareConjecture.lean (proof_wanted, v4.29.0)
SimplyConnectedSpace.nonempty_diffeomorph_sphere_three
    [T2Space M] [ChartedSpace ℝ³ M] [IsManifold (𝓡 3) ∞ M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ 𝕊³)
```

Adopting that exact statement as the T-lane + P-lane joint endpoint is free and
removes any later restatement risk.  `PerelmanAnalyticInputs` stays empty by
design; `PoincareTopologyInputs` is now *also* required to be empty by program
end.  Nothing else in `POINCARE_PLAN.md` §1–§4 changes: this lane is additive.

---

## 1. The four targets, with book anchors and Lean-facing statements

| | Morgan–Tian anchor | Content |
|---|---|---|
| T1 | `intro.tex:293`, `energy1.tex:565-575` | closed simply-connected `M³` has `π₃ ≠ 0` |
| T2 | `intro.tex:240-262` | extinction ⟹ `M₀` is recovered as an iterated connected sum of the removed pieces |
| T3 | `intro.tex:280-292` (Cor. `corequiv`) | a simply-connected such connected sum is `S³` |
| T4 | `intro.tex:320-323` (Remark (ii)) | every component of every time-slice of an RFWS started from a closed simply-connected `M` is again closed and simply connected (hence `π₂ = 0`) |

Draft statements (shapes, not final names; final names obey the 20-letter rule):

```lean
-- T1
theorem pi3_ne_one {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℝ³ M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M] (x : M) : Nontrivial (π_ 3 M x)

-- T4(a), the pointwise half of T4 (no flow, no surgery)
theorem pi2_trivial  (same hypotheses) (x : M) : Subsingleton (π_ 2 M x)

-- T4(b), the flow half; stated against the P6b RFWS interface
theorem slice_sc (S : RicciFlowWithSurgery …) (h₀ : SimplyConnectedSpace S.M₀)
    (t : ℝ) (C : ConnectedComponent (S.slice t)) :
    CompactSpace C ∧ SimplyConnectedSpace C

-- T2 (Poincaré-only form; see §6 ruling R3)
theorem recon_of_ext (S : RicciFlowWithSurgery …) (hext : S.Extinct) :
    Nonempty (S.M₀ ≃ₘ⟮𝓡 3, 𝓡 3⟯ iteratedConnSum S.removedPieces)

-- T3 (Poincaré-only form)
theorem sphere_of_sc_sum (X : …) (hX : IsIteratedConnSum X pieces)
    (hsc : SimplyConnectedSpace X) : Nonempty (X ≃ₘ⟮𝓡 3, 𝓡 3⟯ 𝕊³)
```

The T1, T4(a) and endpoint shapes above were elaboration-checked against this
checkout on 2026-08-29 (scratch file, not committed): `π_ 3 M x` with
`Nontrivial`, `π_ 2 M x` with `Subsingleton`, and
`Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ 𝕊³)` all elaborate under
`[T2Space M] [ChartedSpace ℝ³ M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M]
[ConnectedSpace M] [SimplyConnectedSpace M]`, with only the expected `sorry`
warnings.  T2, T3 and T4(b) cannot be stated yet: they need the P6b RFWS object
and the E7 connected-sum definition.

**The Poincaré-only collapse.**  Once T4(b) is available, T2 and T3 shrink
enormously: every time-slice component is simply connected, so no `S²×S¹`, no
non-orientable `S²`-bundle and no non-trivial space form ever appears, every
removed piece is `S³`, and every connected sum in the reverse induction is a
connected sum with `S³`.  T3 then needs only `X # S³ ≃ₘ X`, and T2 becomes pure
bookkeeping over the surgery times.  The general Morgan–Tian Theorem 1 form
(free products, space forms, `S²`-bundles) needs full Seifert–van Kampen plus
free-product theory and is **not** proposed here — see ruling R3.

---

## 2. Asset audit (greped 2026-08-29; Mathlib pin `v4.29.0`, rev `8a178386ffc0`)

**Mathlib HAS**
* `Topology/Homotopy/HomotopyGroup.lean` — `π_ n X x` with its group structure,
  `π_ 1 ≃ FundamentalGroup`.  Definitions only: no computation, no functorial
  long exact sequences, no fibration sequence.
* `AlgebraicTopology/FundamentalGroupoid/` — groupoid, `FundamentalGroup`,
  `SimplyConnectedSpace`, induced maps, products.
* `Topology/Homotopy/Lifting.lean` — path lifting, homotopy lifting, monodromy
  theorem, unique lifting for covering maps.
* `Topology/CWComplex/Classical/` — `RelCWComplex`/`CWComplex`, skeleta,
  subcomplexes, finiteness.  Structure only: **no cellular homology**.
* `AlgebraicTopology/SingularHomology/` — `singularChainComplexFunctor`,
  `singularHomologyFunctor`, homotopy invariance.  Nothing else.
* `Algebra/Homology/HomologySequence.lean` (+ snake lemma, `ExactSequence`) —
  the LES machinery for short exact sequences of complexes is in place.
* `GroupTheory/CoprodI.lean`, `GroupTheory/PushoutI.lean` — free products and
  amalgamated pushouts of groups.
* `Geometry/Manifold/PoincareConjecture.lean` — the target statement as
  `proof_wanted` (see §0), plus `Geometry/Manifold/Instances/Sphere`.

**Mathlib LACKS** (each verified by name grep, not assumed)
Hurewicz; Poincaré duality; relative singular homology; excision; barycentric
subdivision; Mayer–Vietoris for singular homology; `H_*(Sⁿ)`; degree;
cellular homology; Euler characteristic of a CW complex; Seifert–van Kampen
(`CategoryTheory/Limits/VanKampen` is the categorical notion, unrelated);
`π₁(S¹) ≅ ℤ`; orientation / fundamental class of a manifold; connected sum.

**This tree HAS** (all sorry-free unless noted)
* `Topology/Morse/` + `Topology/Handle/` — ≈ 63k lines: Morse lemma, level
  sets, regular sublevels, handle attachment, `ManifoldCellAttachment.lean`
  (20.4k lines), `Handle/Duality.lean`, collars, gluing, retractions.
  This is the largest single asset of the lane and it is exactly the CW /
  handle-decomposition input that E3 and E5 need.
* `Topology/Covering/` — covering manifolds, deck actions, simply-connected
  covers, `CountablePi1`, lifted metrics; `Topology/FiniteSubdivision.lean`
  (`exists_strict_subdiv`) and `CurveChartCover.lean` — the Lebesgue-number
  path-subdivision machinery van Kampen needs.
* `Topology/Homotopy/` — deformation retracts, closed cells, `EquivUnder`.
* `Tensor/Exterior/` — de Rham cochain complex, `deRhamCohomology`, pullback
  functoriality, `exteriorDerivative_pullback`, wedge; 0 sorries.
* `Analysis/Integration/` — Riemannian volume, divergence theorem with
  boundary, IBP.
* `Geometry/Metric/Sphere/` — the round-metric / space-form quotient lane.

**This tree LACKS** — any homology of spaces, any degree, orientation of a
manifold, integration of differential forms, van Kampen, connected sum.

**THE 4.33 TOOLBOX — the decisive asset (added 2026-08-29, second pass).**
`E:/testdifferential-geometry-t1-433` is an isolated Lean/mathlib **v4.33.0**
project that extracts reusable topology from this repo's own root file
`Solution.lean` (248,818 lines; snapshot `Upstream/Mathoverflow1973.lean`, an
`S⁶`-complex-structure development).  ~6,400 declarations in ten generated
parts, no `sorry`.  Its public entry points are `T1Topology433/T1Topology.lean`
and `T1Topology433/TopologyToolbox.lean`.  Verified here on 2026-08-29 by
running its own `AxiomCheck` (the project is already built): **all sixteen
audited endpoints depend only on `propext`, `Classical.choice`, `Quot.sound`.**

What it actually provides, checked at the statement level:

* genuine integral singular homology — `SingularHomology X n :=
  (FirstHurewicz.singularComplex X).homology n` where `singularComplex X =
  (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℤ ℤ)`, i.e.
  Mathlib's singular chain complex — with functoriality and a full
  **Mayer–Vietoris** package (short exact sequences, connecting maps,
  exactness at each spot);
* **Hurewicz in degrees 1–6**: `firstHurewiczEquiv` / `singularH1EquivOfPi1`
  (`H₁ ≅ π₁^{ab}`), and `hurewiczPi2Equiv` … `hurewiczPi6Equiv` as
  `π_ k X x ≃* Multiplicative (SingularHomology X k)` under
  `SimplyConnectedSpace` plus vanishing of the lower groups;
* `sphereTopEquiv : SingularHomology (UnitSphere (n+1)) (n+1) ≃ₗ[ℤ] ℤ`;
* **Seifert–van Kampen** as a pushout equivalence for a two-open cover
  (`FundamentalGroupVanKampen.TwoOpenCover`, `pushoutEquiv`), plus
  simply-connected covers and covering composition/quotients;
* differential topology: `ManifoldMorse.exists_morse_function`, tubular
  neighborhoods, supported isotopy extension, regular values, smooth Morse
  lemma, retractions;
* high-dimensional topology: Morse handles, handle cancellation (`MorseCancel`,
  including `sublevelHomologyMap_comp`), surgery boundary pairs, general
  position, disk doubles, `ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points`
  (Reeb), `Smale.TwoDiskDecomposition → M ≃ₜ Sⁿ`, and the homotopy-6-sphere
  endpoint.

What it does **not** contain (greped by name, 0 hits): Poincaré duality,
fundamental class, manifold orientation, relative homology, excision, cellular
homology, connected sum.  Its own README states the same missing set for T1:
orientability, duality, top homology.

This replaces most of §4's E1, E4 and E6 with a **port/bump problem** instead of
a build problem — see ruling R5.

**External reference** — `frenzymath/Poincare-Conjecture` (memory note
`frenzymath-poincare-reference`) has a Hatcher track that stops at Ch. 0.

---

## 3. Feasibility ruling (mathematics first, per the plan-mode rule)

**Corrected 2026-08-29 (second pass), after the 4.33 toolbox was found.**  The
first pass ruled that ℤ-coefficient Poincaré duality is unavoidable.  With
Hurewicz 1–6, Mayer–Vietoris, sphere homology, Morse-function existence and
handle cancellation all available and axiom-clean, **duality is avoidable for T1
and T4(a)**.  The recommended route is the Morse/handle chain complex:

1. `H₀(M) = ℤ` (connected) and `H₁(M) = 0` (simply connected, via
   `firstHurewiczEquiv`);
2. a Morse function exists (`exists_morse_function`) and can be arranged with a
   single maximum (handle rearrangement/cancellation of index-`n` against
   index-`n−1` extrema);
3. the handle/Morse chain complex `C_k = ℤ^{c_k}` computes `H_*(M)` — proved by
   induction over handle attachments with Mayer–Vietoris and sphere homology
   (both present);
4. `χ(M) = Σ(−1)^k c_k(f) = Σ(−1)^k c_{n−k}(−f) = (−1)^n χ(M)`, so `χ = 0` in
   dimension 3 — no duality theorem needed, only `f ↔ −f` on the same
   decomposition;
5. `H₃ = ker ∂₃ ⊆ C₃` and `C₃/ker` embeds in the free `C₂`, so `H₃` is `0` or
   `ℤ`; `χ = 1 − 0 + rank H₂ − rank H₃ = 0` forces `rank H₃ = 1 + rank H₂ ≥ 1`,
   hence `H₃ ≅ ℤ ≠ 0` — which is **T1** through `hurewiczPi3Equiv`;
6. with a single 3-handle, `C₃ = ℤ` and `H₃ = ℤ` forces `∂₃ = 0`, so
   `H₂ = ker ∂₂` is a subgroup of a free group, hence free, and of rank 0 by
   step 4 — so `H₂ = 0`, which is **T4(a)** through `hurewiczPi2Equiv`.

Steps 2, 3 and 6 are the real work and are not yet verified against the
toolbox's actual handle API; step 6's single-3-handle arrangement is the most
fragile point, and classical Poincaré duality plus UCT remains the fallback for
the `H₂`-torsion step.  Orientability of a simply-connected manifold (via the
orientation double cover and the existing covering-space theory) is the other
available fallback.

The following three shortcuts were checked in the first pass and still fail;
they are recorded so nobody re-tries them:

1. **de Rham / analytic degree.**  The tree's de Rham complex plus an
   integration layer would give the *detection* half for free: a smooth map of
   non-zero degree is not null-homotopic, because `∫ f*ω` is a homotopy
   invariant and vanishes on constants.  It does **not** construct a map
   `S³ → M` — that construction is precisely Hurewicz's content — and real
   coefficients cannot see torsion, so it cannot prove `π₂ = 0`.
2. **Morse handle cancellation.**  Cancelling the 1-handles of a
   simply-connected closed 3-manifold *is* the Poincaré conjecture; circular.
3. **Euler characteristic via `f ↔ −f`.**  Morse duality gives `χ(M³) = 0` and
   hence `rank H₂ = 0`, but not torsion-freeness; that still needs UCT plus
   duality.

**Ruling:** the lane is a genuine algebraic-topology core build.  The
mathematics is standard and carries no research risk; the risk is volume.  It
is highly parallelizable and shares almost no code with the analytic tree,
so it should run as its own lane (see §6, R4).

---

## 4. Engine stack

Status marks are post-4.33-find: **[have]** = exists and is axiom-clean in the
4.33 toolbox (port/bump problem, ruling R5); **[build]** = must be written.

```
E1 homology core + Mayer–Vietoris        [have]  ─┐
E4 Hurewicz 1–6                          [have]  ─┤
E3 handle/Morse chain complex = H_*      [build] ─┼─→ T1, T4(a)
E9 χ(M³)=0 via f ↔ −f, single top handle [build] ─┘
E5 Poincaré duality (3-manifolds)        [build, FALLBACK only]
E2 de Rham degree (independent, optional)
E6 Seifert–van Kampen                    [have]  ─┬─→ T4(b)
E7 connected sum                         [build] ─┴─→ T3
E8 surgery bookkeeping (GATED on P6b RFWS object) ─→ T2
```

**E1 — Homology core.  [have]**  Singular homology, functoriality,
Mayer–Vietoris and `H_*(Sⁿ)` are all in the 4.33 toolbox and axiom-clean, so the
build that the first pass planned here (subdivision, excision, MV from scratch)
is cancelled.  What remains is R5: bump, port, or develop against it in place.
Relative homology and excision are still absent, but the Morse/χ route of §3
does not need them — if the duality fallback is ever taken, they come back.

**E2 — Degree, two flavors.**  (a) homological degree from E1;
(b) smooth degree `∫_N f*ω / ∫_N ω` from `Tensor/Exterior/` once top forms can
be integrated (needs manifold orientation + a `∫ω` layer, which the Riemannian
volume machinery makes short).  E2(b) is **not** on the critical path but is
cheap, self-contained, reusable elsewhere in the tree, and gives an early
independent check on E1's degree.

**E3 — Handle/Morse chain complex computes `H_*`.  [build]**  The one real new
algebraic-topology brick of the lane.  Induct over handle attachments,
using Mayer–Vietoris plus `H_*(Sⁿ)` at each attachment.  Two independent
geometric inputs are already available: this tree's
`Topology/Morse/ManifoldCellAttachment.lean` (v4.29) and the toolbox's own
handle/`MorseCancel` layer (v4.33, includes `sublevelHomologyMap_comp`).  Which
one is used follows from R5.

**E9 — `χ(M³) = 0` and the single top handle.  [build]**  `c_k(f) = c_{n−k}(−f)`
plus E3 gives `χ = (−1)^n χ`; the single-maximum arrangement is index-`n`
cancellation.  Small, but the fragile step of §3.

**E4 — Hurewicz.  [have]**  Degrees 1–6 exist in the toolbox
(`firstHurewiczEquiv`, `hurewiczPi2Equiv` … `hurewiczPi6Equiv`), well beyond the
degrees 2–3 this lane needs.  Nothing to build.

**E5 — Poincaré duality for closed 3-manifolds.  [build — FALLBACK ONLY]**
Demoted 2026-08-29: the §3 Morse/χ route reaches T1 and T4(a) without it.  Build
it only if step 6 of that route (the `H₂`-torsion step) fails.  Two candidate
routes, ruling R2 below:
  (i) classical: orientation / fundamental class, cohomology, cup and cap
      products, `H^k ≅ H_{n−k}`;
  (ii) native: handle-decomposition duality (`f ↔ −f`, index `k ↔ n−k`) on the
      existing `Handle/Duality.lean` + `ManifoldCellAttachment` assets, giving
      duality of the *Morse/cellular* complexes over ℤ, transported to singular
      homology by E3.
Route (ii) reuses ~63k lines of finished work and avoids building a whole
cup/cap-product layer; route (i) is the textbook route and is what a later
general-3-manifold statement would want.  Recommendation: scout (ii) first,
decide at T-E exit.

**E6 — Seifert–van Kampen.  [have]**  The toolbox has it as a pushout
equivalence for a two-open cover (`FundamentalGroupVanKampen.TwoOpenCover`,
`pushoutEquiv`), axiom-clean.  The first pass planned to build it from
`PushoutI` + `Topology/FiniteSubdivision.lean`; that build is cancelled, subject
to R5.  Consumers: T3 (via E7) and T4(b).

**E7 — Connected sum of smooth 3-manifolds.**  Remove two balls, glue along
`S² × I` by an orientation-reversing diffeomorphism; then `X # S³ ≃ₘ X`,
`π₁(X # Y) ≅ π₁X * π₁Y` (from E6), and cutting along a separating `S²`.  Built
on `Handle/Gluing.lean`, `Handle/Collar.lean` and the `hglue` jet-splice engine.
Note: "an embedded `S²` in a simply-connected 3-manifold separates" needs
`H₂`/Mayer–Vietoris, i.e. it is an E1 consumer, not an E7 primitive.

**E8 — Surgery bookkeeping.**  The reverse induction of `intro.tex:240-262`
against the P6b RFWS object: each surgery time is a cut along an embedded `S²`
plus two 3-ball caps; each disappearance removes a component.  **Gated on P6b.**
The *geometric* half of T2 — that a disappearing component is diffeomorphic to
a space form / `S³` — is NOT this lane's work: it belongs to P7 (canonical
neighborhoods) and enters E8 as a named interface, so that the two lanes never
double-count it.

---

## 5. Stage plan (rewritten 2026-08-29 after the 4.33 find)

Each stage lists its entry gate, its first concrete brick, and its exit test.

**T-A — Decide R5 and open the working surface.**  Entry: none.  Two artefacts:
the R5 decision (bump / port / develop-in-place), and a `Targets` module stating
T1, T4(a), T4(b), T2, T3 with `sorry` plus `PoincareTopologyInputs` as the
4-field staging bundle whose fields are literally those statements.  T1 and
T4(a) are already known to elaborate (§1); on the 4.33 side they can be stated
directly against `T1Topology433.t1_hurewicz`, which reduces T1 to
`∃ c : SingularHomology M 3, c ≠ 0` and `Subsingleton (SingularHomology M 2)`.
Exit: the two homology facts are the ONLY open obligations behind T1 and T4(a).

**T-B — the handle induction and `χ = 0` (critical path).**  Entry: T-A.
Audited 2026-08-29; the toolbox turns out to carry the whole *geometric* and
*exactness* half already:

* `Smale.ManifoldMorse.exists_morse_function` — Morse functions on a closed
  smooth manifold, under exactly the T-A hypothesis bundle;
* `Smale.ManifoldMorse.exists_morseSurgeryData_lt` + `MorseSurgeryData` — the
  data of a single critical passage, with
  `attachmentHomeomorph : {f ≤ c−r²} ∪ handle ≃ₜ {f ≤ c+r²}`;
* `MorseSurgeryData.cellOldHomologyEquiv` / `cellTotalHomologyEquiv` — that
  passage rewritten as an `EmbeddedCellAttachment` in homology;
* `Smale.EmbeddedCellAttachment.cell_exact_at_sphere` / `_at_old` / `_at_ambient`
  — the three exactness spots of the Mayer–Vietoris sequence of a cell
  attachment, with `attachingHomologyMap`, `oldHomologyMap`, `cellConnectingMap`;
* `MorseCancel.regular_sublevel_inclusion_bijective` — sublevel inclusion is a
  homology isomorphism across an interval with no critical values;
* `MorseSurgeryData.indexThreeBoundaryEquiv` — `H₂(S²) ≅ ℤ` at an index-3
  passage, and `attachingHomology_subsingleton_of_index` for the vanishing
  degrees.

**What is NOT there, and is therefore the real T-B work:** finite generation and
rank bookkeeping.  `Module.Finite ℤ` / `Module.finrank ℤ` of a singular homology
group is proved in the toolbox only for the product torus.  Decomposition:

* **T-B1** — `Module.Finite ℤ (H_k(sublevel))` by induction over critical
  passages.  Recipe found 2026-08-29: Mathlib's
  `Module.Finite.of_exact (h_exact : Function.Exact f g) (h_surj)` with `M`, `P`
  finite gives `N` finite; bridge the toolbox's `range = ker` statements with
  `LinearMap.exact_iff`, and take `P := LinearMap.range (cellConnectingMap …)`
  (finite because ℤ is Noetherian and the sphere homology is finite), so
  `H_k(X)` is finite whenever `H_k(old)` and `H_{k-1}(Sᵏ)` are.
* **T-B2** — rank additivity along the cell LES, giving
  `χ(upper) = χ(lower) + (−1)^λ` for a passage of index `λ`.
* **T-B3** — `χ(M) = Σ (−1)^k c_k(f)`, then `c_k(f) = c_{n−k}(−f)` and hence
  `χ(M³) = 0`.
* **T-B4** — conclude `H₃ ≠ 0` from `χ = 0`, `H₀ ≅ ℤ`, `H₁ = 0`
  (`Poincare/LowDegree.lean`, already proved), and then `H₂ = 0` from the
  single-maximum arrangement.

`h3_ne_zero` (T-B4 first half) discharges T1 on its own and should be finished
before the `H₂` half.  Exit: both obligations in `Poincare/Targets.lean` closed.

**T-C — T1 and T4(a).**  Entry: T-B.  Pure composition with
`hurewiczPi2Equiv` / `hurewiczPi3Equiv`; the algebra is already written in
`T1Topology433.t1_hurewicz`.  Exit: two of the four bundle fields discharged.

**T-D — E7 connected sum, and T4(b).**  Entry: T-A (van Kampen is already
available).  First brick: the connected-sum construction and `X # S³ ≃ₘ X`, on
`Handle/Gluing.lean` + `Handle/Collar.lean` or the toolbox's disk-double and
surgery-boundary-pair layer.  Then `π₁(A # B) ≅ π₁A * π₁B` from the toolbox van
Kampen, and T4(b) modulo P6b.  Exit: `IsIteratedConnSum` exists and T3 is
reduced to the surgery bookkeeping.

**T-E — E8 surgery bookkeeping ⟹ T2, T3.**  Entry: P6b RFWS object.  Gated;
nothing to do before P6b exists.

**T-F — E5 duality (contingency only).**  Entry: T-B step 6 fails.  Do not open
speculatively.

Work location (ruling R5 answered by the user on 2026-08-29: option (a), with
an eventual migration of the whole project to 4.33): the lane is developed in
`E:/testdifferential-geometry-t1-433` under `T1Topology433/Poincare/`, umbrella
`T1Topology433/Poincare.lean`, deliberately NOT imported by the extraction's
root module so that the placeholder-free umbrella stays placeholder-free.

Recommended immediate order: **T-A, then T-B.**  T-B is now the whole lane's
critical path, and it is one well-scoped algebraic-topology theorem plus a
Morse-theoretic arrangement — not the multi-quarter homology build the first
pass planned.

---

## 6. Rulings needed from the user

* **R1 — staging bundle.**  Keep `PoincareTopologyInputs` as a temporary
  4-field bundle so the analytic lane is never blocked by this one, with the
  standing requirement that it must be empty at program end.
  *Recommendation: yes.*
* **R2 — E5 route.**  Handle/Morse duality (native, reuses the 63k-line asset)
  vs classical cap-product duality (textbook, needed by any later general
  3-manifold statement).  *Recommendation: scout native first, decide at T-E
  exit; do not build a cup/cap layer speculatively.*
* **R3 — T2/T3 generality.**  Poincaré-only collapse (every piece is `S³`) vs
  Morgan–Tian Theorem 1 in full (space forms, `S²×S¹`, non-orientable
  `S²`-bundles, free products).  *Recommendation: Poincaré-only.*  The general
  form multiplies T2/T3 several times over and is not needed for the endpoint.
* **R5 — 4.29 vs 4.33 (NEW, now the most consequential ruling).**  The toolbox
  targets Lean/mathlib `v4.33.0`; this tree is pinned at `v4.29.0`.  Three
  options: (a) **develop the T-lane inside the 4.33 project** and join only at
  P9 — T1/T4(a) are pure topology of a smooth 3-manifold and need nothing from
  `DifferentialGeometry/`; (b) port the toolbox back to 4.29 — ~6,400 generated
  declarations, and the generated files must not be hand-edited; (c) bump the
  whole tree to 4.33 — note the recorded 4.30 defeq-transparency break of the
  `TangentSpace I x = E` idiom (memory `frenzymath-poincare-reference`), which
  makes this a large, risky operation for the 250k-line analytic tree.
  *Recommendation: (a) now, (c) later on its own schedule, never (b).*
* **R4 — lane parallelism.**  This lane shares essentially no code with the
  analytic tree.  *Recommendation: run it as a separate branch/lane with its
  own agents, and do not interleave it with P2/P1c work.*

---

## 7. Honest scale

Report the theorem and its machinery separately, per the project rule.

* **T1, T2, T3, T4: 0% each** — none of them is stated in Lean today.  A
  theorem that is not stated is 0% regardless of how much machinery stands
  behind it.
* **Machinery, restated 2026-08-29 after the 4.33 find.**  For T1 and T4(a):
  **~60–75%** — singular homology, Mayer–Vietoris, sphere homology, Hurewicz
  1–6, Morse-function existence and handle cancellation all exist and are
  axiom-clean; what is missing is E3 (handle complex computes `H_*`), E9
  (`χ = 0`, single top handle), and the R5 port decision.  For T3: **~30–40%**
  (van Kampen have, connected sum build).  For T2/T4(b): **~10%** and gated on
  P6b regardless.
* **Program effect.**  The analytic estimate is unchanged (P0–P9 infrastructure
  ~15–25%).  The T-lane is smaller than the first pass feared — call it
  **10–15% of the remaining total work** rather than 20–30% — so the whole
  project including topology is approximately **14–22%**.  Same denominator
  warning as `POINCARE_PLAN.md` §5.
* No calendar estimate is offered.  The per-phase month figures in the analytic
  plan are already flagged stale; this lane has no measured velocity at all yet.

---

## Status log

- 2026-08-29 (lane opened): the scope ruling of `POINCARE_PLAN.md` §0 was
  corrected at the user's instruction — T1–T4 are in scope as proof
  obligations, not citations.  Asset audit performed against Mathlib `v4.29.0`
  and this checkout on the same day; the results in §2 are current.  Feasibility
  ruling recorded in §3: no route avoids ℤ-coefficient Poincaré duality for
  closed 3-manifolds plus Hurewicz in degrees 2 and 3; the de Rham/degree,
  handle-cancellation and Euler-characteristic shortcuts were each checked and
  each fails, for the reasons given.  Nothing is implemented yet: all four
  targets are 0%, dedicated machinery ~5–10%.  Next concrete target is **T-A**
  (`Topology/AlgTop/Targets.lean`, the four statements plus the staging bundle),
  then **T-B** (Seifert–van Kampen) and **T-D1** (relative singular homology)
  in parallel.  Open rulings R1–R4 in §6 are with the user.

- 2026-08-29 (second pass, the 4.33 toolbox): the user pointed at
  `E:/testdifferential-geometry-t1-433`.  It is an isolated Lean/mathlib 4.33
  project extracting ~6,400 sorry-free declarations from this repo's own
  `Solution.lean`, and it **already contains** integral singular homology with
  Mayer–Vietoris, Hurewicz in degrees 1–6, `H_{n+1}(Sⁿ⁺¹) ≅ ℤ`,
  Seifert–van Kampen as a pushout, Morse-function existence, tubular
  neighborhoods, isotopy extension, handle cancellation, Reeb's two-critical-
  point sphere theorem and a two-disk decomposition theorem.  Its `AxiomCheck`
  was re-run here: sixteen endpoints, only `propext`, `Classical.choice`,
  `Quot.sound`.  Consequences recorded above: E1, E4 and E6 are cancelled as
  builds; §3's "Poincaré duality is unavoidable" ruling is CORRECTED — the
  Morse/handle chain complex plus `χ(M³) = 0` reaches `H₃ ≅ ℤ` and `H₂ = 0`
  without duality, which is now the recommended route, with duality kept as the
  fallback for the `H₂`-torsion step only.  New critical path = T-B (E3 + E9).
  New ruling R5 (4.29 vs 4.33) is the most consequential open question; the
  recommendation is to develop the T-lane inside the 4.33 project and join at
  P9.  Machinery estimates raised accordingly; all four targets remain 0%.

- 2026-08-29 (T-lane execution starts on 4.33): the user chose R5 option (a) —
  build the T-lane inside the 4.33 project, migrate the whole tree later.
  Landed there: `T1Topology433/Poincare/Targets.lean` (focused-green, exactly
  two named `sorry`s) proving **T1 and T4(a) from `h2_zero` and `h3_ne_zero`**
  through the extracted Hurewicz interfaces, so the entire homotopy-side bridge
  is done and the frontier is now two integral-homology statements; and
  `T1Topology433/Poincare/LowDegree.lean` (focused-green, sorry-free) giving
  `H₀ ≅ ℤ` for path-connected and `H₁ = 0` for simply connected spaces.  Notes
  are in the same-name `.md` files next to them.  The T-B audit is recorded in
  §5: the geometric and exactness halves of the handle induction all exist in
  the toolbox; the missing engine is finite generation and rank bookkeeping of
  homology, decomposed as T-B1–T-B4.  T1, T2, T3, T4 all remain 0% as theorems.

- 2026-08-29 (T-B1 first two steps): `T1Topology433/Poincare/CellRank.lean` is
  sorry-free and lane-green.  `finite_cell` carries `Module.Finite ℤ` of integral
  homology across a cell attachment (old piece + attaching sphere ⟹ result), and
  `finite_regular` carries it across an interval of regular values.  The lane
  umbrella `T1Topology433.Poincare` now builds (`lake build`, 8723 jobs), with
  only the two expected `sorry` warnings from `Targets.lean`.  Lesson recorded in
  `CellRank.md`: `Module.Finite.of_exact` cannot be used here because
  `↥(LinearMap.range g)` gets `AddCommGroup.toIntModule` from typeclass search
  while the term carries `Submodule.module`; work with `.FG` of submodules and
  `Submodule.fg_of_fg_map_of_fg_inf_ker` instead.  Still open in T-B1: ordering
  of critical values, the empty base case, and finite generation of
  `H_k(Metric.sphere (0 : N) 1)` for a general finite-dimensional `N` (transport
  from the toolbox's `SphereHomology.UnitSphere`).  T1 remains 0%.

