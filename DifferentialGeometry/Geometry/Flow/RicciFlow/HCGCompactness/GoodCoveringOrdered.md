# GoodCoveringOrdered.lean — faithful (book-ordered) Step A redo

Decision (2026-06-08, user): redo Step A faithfully to MSM135 Ch4, using the book's
**distance-ordered greedy net** (not the Zorn packing), by **black-boxing HopfRinow**.
Vetted: `Comparison/HopfRinow.lean`'s minimizing-geodesic / exp-surjectivity theorems
are correctly stated (section vars `[PseudoEMetricSpace M][IsRiemannianManifold I M]
[CompleteSpace M]`), so their conclusions are honest true Hopf–Rinow facts; black-boxing
them = honest deferral (downstream inherits `sorryAx`, disclosed).

## Reuse (verified, correct) from `GoodCovering.lean`
λ (A1), `lambda_ratio_le`, the dist=pseudometric bridge (`RealizesEdist`), `lambdaBall`,
`lambdaBallC`, `mem_lambdaBallC_dist`, `PackingBound`. Only the NET and the cover/count
built on it change to the ordered version.

## Plan (faithful, book-exact)
1. **Keystone** `exists_min_edist_base` — HopfRinow-backed (sorry): complete ⟹ the
   distance-to-O minimum over a nonempty closed set is attained. (Properness.)
2. **`S^α` closed** — the varying-radius λ-ball disjointness set is closed (book: "balls
   open ⟹ S^α closed"; really a lower-semicontinuity lemma).
3. **Ordered net** (book L897–955): greedy `Nat.rec` with `r^α = d(S^α,O)` the attained
   min (keystone); prove `r^α↗`, pairwise-disjoint `B(x^α,λ[r^α])`, and the minimality
   used in the cover.
4. **Book theorems**: lbl387 (cover `B(O,r)⊂⋃_{α≤A(r)}B(x^α,2λ[r^α])` + A(r)), lbl388,
   **lbl389** (`r^α≤2αλ[0]`), lbl390 (K'(r)), lbl391 (5 radii), lbl383 (7 properties).

## Honest scope
This is the largest single piece of Step A; (2)+(3) are intricate (dependent recursion +
topology). Building methodically, verified per step. The keystone + any §5-convexity for
lbl383 item 3 stay HopfRinow/§5 black boxes.

## Status — abstract net FOUNDATION DONE + verified + sorry-free (2026-06-08)
**Architecture revised:** build abstractly in `[MetricSpace M][ProperSpace M]` (Mathlib metric API); the
minimiser is then a GENUINE theorem (no black box) — only "complete pointed Riemannian manifold ->
ProperSpace under its Riemannian distance" (Hopf-Rinow) stays a black box, isolated to instantiation.
The earlier emetric keystone was the wrong abstraction; dropped. Done + sorry-free: `availSet` (S^alpha),
`isClosed_availSet` (closed via `isClosed_le` + `infDist`), `exists_min_dist_base` (greedy minimiser of
`d(.,O)` over a closed nonempty set, from `ProperSpace` + `IsCompact.exists_isMinOn` on the compact slice
`S inter closedBall O (d s0 O)`).

**NET RECURSION + PACKING also DONE + sorry-free (2026-06-09):** `forbidden` (prior balls' union),
`netList` (greedy net as accumulator List via clean STRUCTURAL recursion — `netList 0 = [O]`, each step
appends the `availSet` minimiser, stops when empty), `O_mem_netList`, `netList_succ_spec` (the appended
center is in `availSet` and minimises `d(.,O)` there), and **`netList_ballsDisjoint`** (the λ-balls of the
net are pairwise disjoint — the packing). KEY: accumulator List ⟹ plain `Nat.rec`, no strong recursion;
the appended center's `availSet`-membership gives ball-vs-prior disjointness (`Set.disjoint_iUnion_right`).

**REMAINING (book theorems on the verified net):**
1. `r^α` monotone (`S^α ⊆ S^{α-1}` ⟹ min over smaller set is larger).
2. lbl387 cover (minimality reductio) + A(r) count; lbl389 (`r^α≤2αλ[0]`); lbl391 radii; lbl383.
3. Instantiation: manifold → `[ProperSpace]` (Hopf-Rinow black box) + `lam := GoodCovering.lambda`.
