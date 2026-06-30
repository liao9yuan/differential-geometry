# ExtendViaUniqueness — interior-restart + uniqueness route for `extends_of_rmBounded`

## Why this route (user's insight, 2026-06-20)

The current route restarts short-time existence **at ω** from the BBS limit `g(ω)`, which forces
the C∞-glue *across* the seam ω → Gate-R (DeTurck C∞-**up-to-the-initial-time**, blocked: the PDE
black box `deturck_ricci_flow_parabolic_short_time_existence` caps endpoint regularity at C² / `k≤2`)
+ Gate-L + the jet-matching (corollary a + Lemma 3 + splice).

**Better route:** restart from an *interior* time `t* < ω` (where `g_fam` is genuinely C∞), get a
flow `r̃` whose existence interval `[0, T̃)` reaches past `ω` (i.e. `ω < t* + T̃`). Then `ω` is an
**interior** time of `r̃(·−t*)`, so C∞-at-ω is FREE (interior regularity, which the black box DOES
give). Forward uniqueness patches `r̃(·−t*) = g_fam` on the overlap `[t*, ω)`, so the seam dissolves.

## Construction (provable; reuses the `gluedFamily` machinery)

`g_ext := gluedFamily g_fam (fun u => r̃ (u + (ω − t*))) ω` `= fun s => if s < ω then g_fam s else r̃ (s − t*)`.
Key fact `hext_eq_r`: for `s ≥ t*`, `g_ext s = r̃ (s − t*)` (uniqueness below ω + def above) — so
`g_ext = r̃(·−t*)` on `[t*, ω+ε)`, with `ω−t* ∈ (0, T̃)` interior to `r̃`.

Output tuple = same as `ricci_flow_extends_construction` (ε, g_ext, agree, Ioo-C∞, Ico-C⁰, PDE), then
fed to the banked `isSolutionOn_of_extendData`. ε := t* + T̃ − ω > 0.
- **agree** below ω: `gluedFamily_eq_left`. ✓ reuse.
- **PDE** on `Ico α (ω+ε)`: `gluedFamily_pde` + `gluedFamily_pde_cross_of_matching`. ✓ reuse, with
  `metric_match` (`g_fam s → r 0`) and `ricci_match` derived from **uniqueness + r̃ continuity** (NOT
  from BBS): `g_fam s = r̃(s−t*) → r̃(ω−t*) = r 0`. `r`'s PDE on `Ico 0 ε` = `r̃`'s PDE shifted.
- **gram_smooth** (Ioo α (ω+ε)) + **gram_cont** (Ico): NEW. `Ioo α (ω+ε) = Ioo α ω ∪ Ioo t* (ω+ε)`;
  on `Ioo α ω` use `g_fam` interior C∞ (from `_hS.smoothMetric`); on `Ioo t* (ω+ε)` use `hext_eq_r`
  + `r̃` interior C∞ shifted (`ContMDiffOn.comp` with `(s,x)↦(s−t*,x)`); `ContMDiffOn.union` (both
  open). Similarly C⁰ via `ContinuousOn`.

## The two NEW obligations (the route's frontiers; replace Gate-R/L + jet-matching)

- **(A) `ricci_flow_interior_restart`**: bounded-curvature solution on `[α,ω)` ⇒ `∃ t* ∈ [α,ω), T̃`,
  `ω < t*+T̃`, and a restart `r̃` from `g_fam t*` (interior C∞ on `Ioo 0 T̃`, C⁰ `Ico`, PDE `Ico`).
  Needs a **uniform/stable existence time** (existence time from `g(t*)` doesn't collapse as `t*→ω`):
  cleanest via `g(t*) → g(ω)` C∞ (BBS) + lower-semicontinuity of the short-time existence time, OR a
  quantitative-in-curvature short-time existence. **Not in the project.**
- **(B) `ricci_flow_forward_unique`**: two flows with the same PDE + interior C∞ + C⁰ + equal initial
  value agree forward. Standard (DeTurck), **not in the project**. ← the main new ingredient / block.

## PAUSED (user, 2026-06-20): (A) is not generally true — wait for revised short-time existence

(A) "interior restart reaches past ω" is FALSE in general: at a genuine maximal/singular time ω the
existence time from `g(t*)` collapses to 0 as `t* → ω`. (A) holds ONLY under bounded curvature, and
ONLY via a **uniform/stable existence time** (existence time ≥ `T₀(|Rm| bound)`, or lower-
semicontinuity of the existence time). The current short-time existence (`∃ T` per `g₀`, no
uniformity) does NOT give this, so (A) is **not dischargeable from it**. Decision: PAUSE the route;
once the short-time-existence theorem is obtained/revised in a form that yields the uniform/stable
existence time, REVISE (A) (its hypotheses must thread the curvature bound through the existence
theorem — `CinftyLimitData` alone is not obviously enough; the uniformity is the real content).
`Evolution/ExtendViaUniqueness.lean` keeps (A) + (B) as stated typecheck-verified obligations
(sorry); do not attempt to discharge (A) until short-time existence is settled.

## Status / block
The construction (given A, B) is provable assembly. The block to report: (B) forward uniqueness is a
substantial theorem absent from the project; (A) needs a uniform/stable existence time also absent.
Both are more standard / cleaner than the blocked C∞-up-to-initial-time (Gate-R). Decision needed:
cite as black boxes (consistent with short-time existence already being a `sorry`) vs prove.
Corollary (a) + Lemma 3 become unnecessary for `hglue` under this route (clean, but sidelined).
