# `StarSum2` — design + brick status

Goal is the five BBS bricks: `StarSum2` predicate + `.add`, `.bound`, `.nabla`, the `E_k`
recursion, and the `IteratedRmTowerOn` wiring.

## ✅ BRICK 2 DONE (2026-06-11, GREEN — `StarSum2.bound` proved)

**`StarSum2.bound : StarSum2 S t k T → ∃ C ≥ 0, ∀ x basis (horth) m, |T(basis-comps)| ≤
C·Σ_{j∈range(k+1)} √(stNormSq j)·√(stNormSq (k−j))`** — the Cauchy–Schwarz extraction, 0 sorry.
`stNormSq S t j x basis := compNormSqMulti (basis-components of ∇ʲRm)` (= `wⱼ`); `horth` is the
folder-standard inner-product form `g.inner x (basis i) (basis j) = δᵢⱼ` over an abstract
`{Idx}[Fintype][DecidableEq]` (matching the tower's index style; `C` is uniform in `(x, basis, m)`,
only `card Idx` enters). Constants: zero→0, add→C₁+C₂, smul c→|c|·C, base→card² (one `card` per
metric trace, then per-component CS).

New supporting API (same file): `sumIdentityDiag` (δ double-sum collapse), `mtInputBasis`
(∃-form: a trace input of basis vectors IS `basis ∘ mIdx` — dite index tuple), `mtfOrthoBd`
(**the reusable orthonormal trace bound**: per-component bound c on X ⟹ per-component bound
card·c on `metricTraceFirstTwoField g X`, via `metricInverseInBasis_identity_of_orthonormal` +
`metricTraceFirstTwo0SAt_eq_sum_basis` + δ-collapse). Base case: a+b=k extracted from σ via
`Fintype.card_congr`; lands on the j:=a summand via `Finset.single_le_sum`.

**Lean lessons (brick 2):** (1) `abs_le_sqrt_compNormSqMulti` (NablaRiemannHeat.lean) carries a
DIFFERENT ℝ-lattice/AddGroup instance path than this file's `|·|` (`Real.lattice` vs
`instDistribLatticeOfLinearOrder`) → "Application type mismatch" even under respectTransparency;
WORKAROUND: use instance-clean `sq_le_compNormSqMulti` + Mathlib's `Real.abs_le_sqrt`. (2) `abs_add`
is GONE (renamed `abs_add_le`). (3) `Fin.cases`-style tuple lemmas: state as ∃ index tuple (dite
form) + `simp only [metricTraceInput_apply]` (simp beta-reduces; `rw` doesn't) + `split_ifs <;> rfl`.
(4) `Finset.single_le_sum` leaves `(fun j => …) a` un-beta-reduced — `simp only [hb] at` both
beta-reduces and rewrites. (5) induction @-binders: index k is consumed — `| @add A B hA hB ihA ihB`.

## ✅ CLASS EXTENSION DONE (2026-06-11, GREEN build 3705): metric factors + iterated traces

The g-factor extension below is **fully implemented and verified** (0 errors/warnings in
`StarSum2.lean`; bricks 1–3 and 2 re-proved in the extended setting):
- `starProd S t a b r` (g's right-appended, all rank steps defeq), `mtIter` (τ-fold trace),
  `mtIter_add`; `starBaseField S t k a b r σ = mtIter (2+r) (ddc σ (starProd a b r))`,
  `σ : Fin (((4+a)+(4+b))+2r) ≃ Fin ((4+k)+2(2+r))`; `base` ctor gains `r`.
- `.nabla` (re-proved): `starProdNabla` (r-induction; g-branch vanishes via
  `zero_realizes_metric` + `product_zero` + `domDomCongr_zero` + the NEW
  `product_add_left`/`product_domDomCongr_left`); `stNablaMtIter` (τ-induction of the keystone,
  ∃ρ-form, massage = `← metricTraceFirstTwoField_domDomCongr` + `domDomCongr_trans`);
  `stNabla_starBase` witnesses right-assoc + `Equiv.trans_assoc` in the final simp.
- `.bound` (re-proved): `starProdBd` (r-induction; metric components `δ ≤ 1` via
  `metricTensorField_apply` + horth), `mtIterOrthoBd` (τ-induction over `mtfOrthoBd`),
  base constant `card^{2+r}`.
- NEW light-layer (Tensor.lean / DomDomCongrSection.lean): `product_add_left`,
  `product_domDomCongr_left` (the `finSumFinEquiv`-conjugated `e ⊕ refl` block equiv).
- Lean traps hit: `rw [product_fun_apply]` fails on rank-index mismatch (`2*(r+1)` vs
  `(…+2r)+2`) → use `le_trans (le_of_eq (congrArg abs hpf)) …` (exact-mode defeq) instead;
  `Fin.natAdd _ 0`'s `_`/Fin-rank metavars underdetermined in `show` → write
  `Fin.natAdd <explicit> (0 : Fin 2)`.

### (historical) the discovery record

⚠️ BRICK 4 DESIGN DISCOVERY (2026-06-11): the class needs METRIC FACTORS

Feasibility check of `E_0 = (∂ₜ−Δ)Rm = −2B# − drift` against the class exposed a REAL
design gap: the dim-3 reaction contains terms with **free metric factors** — `bsharp_eq_knC`
gives `B# = KN(C, −|R|², δ)` with `C = 2R²−(3S/2)R+(S²/2−|R|²)δ` (UhlReaction3), so
`R²⊙δ`, `S·R⊙δ`, `(S²/2−|R|²)δ⊙δ` terms appear.  A pure double trace of `∇ᵃRm⊗∇ᵇRm`
leaves its 4 free slots ON THE Rm FACTORS — it can never produce free `g`-slots.  Hamilton's
`∗`-algebra always allowed `g`/`g⁻¹` factors; the class must too.

**EXTENSION (in progress):** generator `starProd a b r` = `∇ᵃRm ⊗ ∇ᵇRm ⊗ g^{⊗r}` with the
`g`'s appended ONE AT A TIME on the right (`| r+1 => product (starProd r) (metricTensorField g)`)
— this keeps every rank step `(R+2r)+2 ≡ R+2(r+1)` DEFEQ (the existing `metricPow` has a
`2+2r ≠defeq 2(r+1)` cast in its successor — avoid it as the generator; its parallelism lemma
`nabla_metricPow_zero` shows the proof pattern).  `base k a b r σ` = `mtIter (2+r)` traces of
`ddc σ (starProd a b r)`, `σ : Fin (((4+a)+(4+b))+2r) ≃ Fin ((4+k)+2(2+r))` (cardinality still
forces `a+b=k`; rank still pinned by σ).  Brick-3 adaptation: `∇(starProd) ` by r-induction —
the `g`-branch of Leibniz VANISHES (`zero_realizes_metric` + `product_zero`), so `∇base` is
STILL two daughters.  Brick-2 adaptation: `g`-components are `δᵢⱼ ≤ 1` at orthonormal bases;
each extra trace costs one `card` → base constant `card^{2+r}`.  New light-layer needs:
`product_add_left`, `product_domDomCongr_left` (block equiv via `finSumFinEquiv`-conjugated
`Equiv.sumCongr e (refl)`), `mtIter` + `mtIter_add` + iterated keystone (`τ`-induction) +
iterated `mtfOrthoBd`.

**REMAINING bricks: 4–5 (E_k recursion + tower wiring).**  NOTE for brick 5: the tower's
`starBound` has the FIXED constant card² per j-bucket, but bucket term-counts grow with k (Leibniz
iterations), so the reshape will either carry the ∃C into a k-dependent tower constant (the
Bernstein stage already digests `c = 2·card^{6+k}`) or restate `IteratedRmTowerOn.starBound` with
`∃ c`, — an interface decision to make at wiring time.

## ✅ BRICK 3 DONE (2026-06-11, GREEN — `StarSum2.nabla` proved)

**`StarSum2.nabla : StarSum2 S t k T → StarSum2 S t (k+1) (stNabla S t T)`** — the inductive
heart — is proved, 0 sorry.  One analytic hypothesis: `hcov1 : ContMDiffCovariantDerivativeLocally
(S.family.connection t) 1` (discharge at consumers via `connSmoothOfSol S hS t (D.regular_subset t.2)`,
the `IntrinsicDerivation.lean:345` pattern; no ∞→1 mono lemma exists in the codebase).

**KEY DESIGN CHANGE — `starBaseField` rank decoupling.**  `starBaseField S t k a b σ` now takes
the level `k` SEPARATELY from `a, b`, with `σ : Fin ((4+a)+(4+b)) ≃ Fin (((4+k)+2)+2)` pinning
the output rank `4+k` (σ's cardinality forces `a+b=k` semantically).  This is what makes `.nabla`'s
base case cast-free: `(a+1)+b` and `(a+b)+1` are NOT defeq for open `a b` (`Nat.succ_add` is not
rfl), so the old `base (a b) : StarSum2 (a+b) …` design would hit dependent-rank cast hell; with
`k` decoupled, `base k a b ↦ base (k+1) (a+1) b + base (k+1) a (b+1)` typechecks on the nose
(`leibnizLeftEquiv` internally absorbs the succ_add bridge).

New in `StarSum2.lean` (all GREEN): `stMetricCompat` (local solution-compat handle);
`stNabla` (canonical `totalNabla0S` + `totalNabla0S_reg`/`connSmoothInf` auto-reg);
`stNabla_realizes`; `stNabla_zero/add/smul` (via `totalNabla0SRealizes_unique` against
`.add`/`.smul` realizer closures — zero via the `0 • 0` trick); `stNabla_starBase`
(∃-form: `∇(base k a b σ) = base (k+1) (a+1) b σL + base (k+1) a (b+1) σR`); `StarSum2.nabla`
(four-case induction).  New in `Tensor/Multilinear/DomDomCongrSection.lean`:
`domDomCongr_trans`/`_add`/`_smul`.

**Proof shape of `stNabla_starBase` (worked first try once assembled):** realizes chain
`nabla0S_product_realizes` (+`nablaKRm04Field_realizes` ×2) → `totalNabla0SRealizes_domDomCongr`
→ keystone `nablaRealizes_metricTraceFirstTwo` ×2 → `totalNabla0SRealizes_unique` vs
`stNabla_realizes` ⟹ `heq : stNabla(base) = chain-realizer`; then `rw [heq]` + ONE
`simp only [domDomCongr_add, metricTraceFirstTwoField_add, ← metricTraceFirstTwoField_domDomCongr,
domDomCongr_trans, Equiv.trans_assoc, starBaseField]` normalizes both sides to the two-base form.
Explicit witnesses (right-assoc): `σL = lle.trans ((feq σ).trans ((tns ((4+k)+2)).trans (feq²(tns (4+k)))))`.
**Lean lessons:** (1) `refine ⟨_, _, ?_⟩` with ∃-witness metavars FAILS ("don't know how to
synthesize") — give explicit witnesses + let `Equiv.trans_assoc` in the simp set reconcile the
trans-association; (2) `induction hT with` case binders do NOT re-bind the family index `k`
(`| zero =>`, `| base a b σ =>`); (3) `import ProductNablaLeibniz` was missing (only
UhlenbeckBaseProducer imported it).

**REMAINING bricks: 2 (.bound) and 4–5 (E_k recursion + tower wiring).**

## ✅ BRICK 1 DONE (2026-06-11, GREEN — `StarSum2.lean` committed)

The brick-1 blocker (generic-rank `0`/`+`/`•` synthesis on `Tensor0SField (4+k)` timing out at
`whnf`) is **RESOLVED by one line**: `set_option backward.isDefEq.respectTransparency false in`
before each declaration that writes those ops.  This is the codebase's OWN established
workaround — every theorem in `MetricTrace/NablaTraceGen.lean` that writes `0`/`+`/`•` on a
generic-rank `Tensor0SField` is prefixed with it (`metricTraceFirstTwoField_add/_smul/_zero`).
The prior 5 attempts (raw inductive, `include`, letI helpers, +smooth-bundle letI, plain def)
never tried the set_option; route (a) [low-level host file] was a red herring — `Coordinates.Field`
(the type's OWN home) also fails the bare `(0 : Tensor0SField (4+k))`, and also COMPILES with the
set_option.  So the fix is per-declaration, import-independent.

`StarSum2.lean` (ns `DifferentialGeometry.PDE.RicciFlow`, imports `StarSum/NablaReactionAllK`) now has:
- `starBaseField S t a b σ` — the `base` term `metricTrace₁₂²(domDomCongr σ (∇ᵃRm ⊗ ∇ᵇRm))`,
  rank `4+(a+b)`, `σ : Fin ((4+a)+(4+b)) ≃ Fin (((4+(a+b))+2)+2)`; built from
  `MultilinearSection.product`/`domDomCongr` + `metricTraceFirstTwoField` ×2, mirroring `knRicT`.
- `inductive StarSum2 S t : (k) → Tensor0SField (4+k) → Prop` with `zero`/`add`/`smul`/`base`.
  (Dropped `reindex` — subsumed by `base`'s `σ`; `.nabla` of a `base` lands back in `base`.)
- `.add` = the `add` constructor (free).  **Brick 1 (predicate + `.add`) complete.**

## ✅ Keystone API `nablaRealizes_metricTraceFirstTwo` — DONE (2026-06-11, GREEN in `NablaTraceGen.lean`)

The field-level ∇–trace realizer is **proved and committed** to `NablaTraceGen.lean` (the
core Tensor-layer file stays `sorry`-free; `lake env lean` clean). It is the gateway for brick 3
`.nabla`. Added alongside: `traceNablaShuffle` (the 3-cycle perm) + its value lemmas
(`_zero/_one/_two/_val_ge/_val`), `consPredVal` (the single-cons evaluator), and
`traceNablaShuffle_metricTraceInput` (the slot identity).

**The Fin-mechanics lessons that cracked the slot lemma (reuse these):**
1. **Bare `Fin.cons`'s dependent motive is NOT inferred in `rw`/statement position** → write
   `@Fin.cons n (fun _ => V) c f q` with the explicit constant motive (this was THE blocker —
   the error is `Fin.cons ?m ?m q has type ?m q but expected V`). `consPredVal` uses
   `Fin.cons_succ (α := fun _ => V)`.
2. For a goal whose conses come from a typed wrapper (`metricTraceInput`/`mtInput`), use a
   `show (Fin.cons … : Fin n → V) …` ascription (or `simp only [mtInput]`) to expose the
   conses in *typed* form, so `consPredVal`/`Fin.cons_zero` fire.
3. Literal `Fin` vals: `((2 : Fin (s+2+1)) : ℕ) = 2` closes by **`by simp`** (NOT
   `Nat.mod_eq_of_lt`, which doesn't unify the OfNat coercion); the `≠` facts follow via
   `rw [Ne, Fin.ext_iff, <val-lemma>]; omega`.
4. `pred` chains: `Fin.val_pred` (NOT deprecated `Fin.coe_pred`); the final tail-index match is
   `congr 1; rw [Fin.ext_iff]; simp only [Fin.val_pred, hval]` with
   `hval : (shuf p).val = p.val`.
5. The keystone's last step is `exact congrArg _ (traceNablaShuffle_metricTraceInput …)` (NOT
   `rw`, because the goal's composition `v ∘ ⇑(traceNablaShuffle s)` from
   `ContinuousMultilinearMap.domDomCongr_apply` doesn't match `rw`'s pattern — mirrors
   `metricTraceFirstTwoField_domDomCongr_gen`'s `congrArg` at NablaTraceGen.lean:737).

(The slot lemma was first cracked in a throwaway Mathlib-only `ShuffleTest.lean`, then ported.)

### (historical) the design + obstruction record

**Statement (correct, type-checks):**
```
theorem nablaRealizes_metricTraceFirstTwo {s} [T2Space M][CompleteSpace E][I.Boundaryless]
    [IsManifold I 1 M][IsManifold I (∞+1) M]
    (cov)(hcov : cov.ContMDiffCovariantDerivativeLocally 1)(g)(hmc : IsMetricCompatible_gen cov g)
    (A : Tensor0SField (s+2))(nablaA : Tensor0SField (s+2+1))
    (hnablaA : TotalNabla0SRealizes (s+2) cov A nablaA) :
  TotalNabla0SRealizes s cov (metricTraceFirstTwoField g A)
    (metricTraceFirstTwoField g (MultilinearSection.domDomCongr ∞ (traceNablaShuffle s) nablaA))
```
where `traceNablaShuffle s : Equiv.Perm (Fin (s+2+1))` is the 3-cycle `0↦2,1↦0,2↦1` (id on tail).

**Main proof (VALIDATED — compiled modulo the slot lemma):**
```
intro X x slots
set basis := coordinateFrameAt_toBasis x; set gInv := inverseMetricFlatModelInChart_component … (extChartAt x x)
have hinv := inverseMetricFlatModelInChart_metricInverseInBasis_center g x
rw [← totalNabla0SFun_apply_section s cov X (metricTraceFirstTwoField g A) x slots,
    nabla_metricTraceFirstTwo0S cov hcov g hmc A basis gInv hinv (X x) slots]   -- RHS = Σ gInv·∇A(cons X (mtInput …))
rw [metricTraceFirstTwoField_eq_sum g (domDomCongr (traceNablaShuffle s) nablaA) x (cons (X x) slots)]
rw [← hbasis, ← hgInv]; unfold metricTrace0S2InBasis
refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; congr 1
rw [MultilinearSection.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    totalNabla0SFun_apply_section (s+2) cov X A x (mtInput (basis i)(basis j) slots),
    ← hnablaA X x (mtInput (basis i)(basis j) slots)]
rw [traceNablaShuffle_metricTraceInput (basis i) (basis j) (X x) slots]   -- ← THE GAP
```
Ingredients all verified to exist: `totalNabla0SFun_apply_section` (HigherOrder.lean:230),
`nabla_metricTraceFirstTwo0S` (NablaTraceGen.lean:504), `metricTraceFirstTwoField_eq_sum`
(NablaTraceGen:623, uses `coordinateFrameAt_toBasis`+`inverseMetricFlatModelInChart_component`),
`inverseMetricFlatModelInChart_metricInverseInBasis_center` (Inverse.lean:581), `metricTrace0S2InBasis`
def (RoughLaplacian.lean:316 = `Σ gInv·T(metricTraceInput basis_i basis_j tail)`), product-Leibniz
`nabla0S_product_realizes` (ProductNablaLeibniz:55), `totalNabla0SRealizes_domDomCongr` (NablaDomDomCongr:152).
The value lemmas `traceNablaShuffle_zero/_one/_two/_val_ge/_val` (3-cycle vals) ALL COMPILE.

**THE ONE BLOCKER = `traceNablaShuffle_metricTraceInput`** (a *trivially-true* slot-permutation fact):
```
metricTraceInput a b (Fin.cons Z tail) ∘ traceNablaShuffle s = Fin.cons Z (metricTraceInput a b tail)
```
i.e. `[a,b,Z,tail…] ∘ shuffle = [Z,a,b,tail…]`.  Resisted 4 tactic iterations — the warned-about
generic-`Fin` trap (`fin_cases` needs a concrete rank; `Fin.cases` breaks the dependent-`dite`
motive when substituting `q`; `(2 : Fin (s+3))` is `⟨2 % (s+3),_⟩`, not defeq `⟨2,_⟩` or `succ¹`,
so `Fin.cons_succ`/`Fin.cons_zero` don't fire on `OfNat` indices).  The recurring sub-problem is a
`val`-based single-cons evaluator `cons_val_apply : Fin.cons c f q = dite ((q:ℕ)=0) c (f ⟨(q:ℕ)-1,_⟩)`
whose *statement* hits a stubborn "Type mismatch" (the dependent `⟨(q:ℕ)-1, by omega⟩` index).
**Next attempt:** either (a) a hypothesis-form `cons_val_apply (hq : q ≠ 0) : Fin.cons c f q = f (q.pred hq)`
(clean statement, no dependent nat index) applied per-case with `Fin.cons_zero`, tracking
`Fin.pred`-vals via `Fin.coe_pred`+`tns_c1`/`tns_c2`; or (b) a short GPT-Pro/Lean-expert consult on
the single goal "prove `metricTraceInput a b (cons Z tail) ∘ <3-cycle perm> = cons Z (metricTraceInput a b tail)`
for generic `Fin (s+3)`".  Pure Lean-tactics; no math risk.

## (after keystone) brick 3 `.nabla` — full plan

`.nabla : StarSum2 k T → StarSum2 (k+1) (totalNabla0S … T)`, induction on the derivation.
zero→zero, add→add, smul→smul are immediate.  The **`base` case** needs:
`totalNabla0S (starBaseField a b σ) = starBaseField (a+1) b σ₁ + starBaseField a (b+1) σ₂`,
proved via `totalNabla0SRealizes_unique` (the canonical `∇` = any realizer) by building the
RHS as a realizer of `∇(base a b σ)`.  Composes: `nabla0S_product_realizes` (A⊗B Leibniz) +
`totalNabla0SRealizes_domDomCongr` (DONE, NablaDomDomCongr.lean:152, gives `domDomCongr (frontExtendEquiv e)`)
+ **a MISSING field-level trace-commute realizer** `nablaRealizes_metricTraceFirstTwo`:
`TotalNabla0SRealizes (s+2) cov A nablaA →
  TotalNabla0SRealizes s cov (metricTraceFirstTwoField g A)
    (metricTraceFirstTwoField g (domDomCongr σ_move nablaA))`
where `σ_move : Fin ((s+2)+1) ≃ Fin ((s+1)+2)` moves the new ∇-slot (position 0) past the trace
pair (orig slots 0,1 → positions 1,2 of nablaA) to the back.  The EVALUATED form exists
(`nabla_metricTraceFirstTwo0S`, NablaTraceGen.lean:504, the gInv-weighted sum); the field-level
realizer must be lifted from it (instantiate a basis + metric inverse at each x, match the
`metricTraceFirstTwoField_eq_sum` gInv-sum to the `nabla_metricTraceFirstTwo0S` RHS).
**Flagged as a known TODO at `UhlenbeckBaseProducer.md:503`.**  Build it in `NablaTraceGen.lean`
next to `nabla_metricTraceFirstTwo0S`.  RISK: generic-`p` `metricTraceInput`/`Fin.cons` whnf
timeouts + rw-rematching traps (route-status lessons) — `funext`+`Fin.cases`, not raw defeq.

---
## (historical) brick-1 blocker diagnosis — kept for the lesson

**Returned after 5 attempts stuck on brick 1** in the prior session.  The math design is sound;
the blocker was purely Lean instance plumbing.

## The intended design (sound — keep for next attempt)

Inductive family on `(k : ℕ) → Tensor0SField (4+k)`:
```
inductive StarSum2 (S t) : (k:ℕ) → Tensor0SField (4+k) → Prop
  | zero (k)                : StarSum2 k 0
  | add  {k} {A B}          : StarSum2 k A → StarSum2 k B → StarSum2 k (A + B)
  | smul {k} (c) {A}        : StarSum2 k A → StarSum2 k (c • A)
  | reindex {k} (σ) {A}     : StarSum2 k A → StarSum2 k (domDomCongr σ A)
  | base (a b) (σ)          : StarSum2 (a+b) (starBaseField a b σ)
```
`starBaseField a b σ := metricTraceFirstTwoField g (metricTraceFirstTwoField g
  (domDomCongr σ (product (∇ᵃRm) (∇ᵇRm))))` — the double metric trace of a slot-reindexed
`∇ᵃRm ⊗ ∇ᵇRm`, rank `4+(a+b)`, `σ : Fin ((4+a)+(4+b)) ≃ Fin ((4+(a+b)+2)+2)`.

- **brick 1 `.add`** = the `add` constructor (free once it elaborates).
- **brick 2 `.bound`**: induct on the derivation → `∃ C ≥ 0, ∀ x (g-orthonormal), ‖T‖ ≤
  C·Σⱼ √(wⱼ)√(w_{k−j})` (`wⱼ = |∇ʲRm|²`).  zero→C=0, add→C_A+C_B, smul c→|c|·C, reindex→C,
  base→`card²` via `abs_curvatureAction0SAt_orthoBasis_le` (done). The existential `C`
  absorbs coefficient/term-count growth cleanly.
- **brick 3 `.nabla`** = `StarSum2 k T → StarSum2 (k+1) (totalNabla0S T)`, induct on the
  derivation; the `base` case commutes `∇` through both traces (`nabla_metricTraceFirstTwo0S`,
  done) + `domDomCongr` (`totalNabla0SRealizes_domDomCongr`) + product Leibniz
  (`nabla0SFun_product_eval`) ⟹ `base (a+1) b σ' + base a (b+1) σ''` (the slot-algebra is the
  same shape as the verified `traceRicWit` in `UhlenbeckBaseProducer.lean`).
- **brick 4 `E_k ∈ StarSum2 k`**: one-step peeling `E_k = ∇E_{k-1} + (∂ₜΓ)∗T_{k-1} −
  [Δ,∇]T_{k-1}`, base `E_0 = Rm∗Rm` (Uhlenbeck), close by induction using brick 3 + the done
  single-step commutator `spatialComm_nablaKRm_split`.
- **brick 5 wiring**: feed brick 2's bound into `IteratedRmTowerOn.starBound`, and (with
  `nablaKRm04Reaction_orthoBasis_eq_compContract`) the reaction into `heatEq`.

## THE BLOCKER (brick 1 — Lean instance synthesis, NOT math)

`0`/`+`/`•` (`OfNat`/`HAdd`/`HSMul`) on the **generic-rank** `Tensor0SField (4 + k)` fail to
synthesize their `ContMDiffVectorBundle ∞` module instance in this file's context.  Error:
`failed to synthesize OfNat (Tensor0SField ∞ (4 + k)) 0` (and `HAdd`/`HSMul`).

Five attempts, all the same failure:
1. raw `inductive … (A + B)` / `… 0`;
2. `include hMinf hM1 hM2 hMinf1 hEc` to force the manifold instances in;
3. `stZeroField`/`stAddField`/`stSmulField` `def` wrappers with `letI := tensor0SBundle_topology`;
4. + `letI := TangentBundle.contMDiffVectorBundle` + `letI := tensor0SBundle_smooth`;
5. plain `def` bodies (no `letI`), mirroring `TotalNabla0SRealizes.add` which *does* compile
   with generic-`s` `α + β`.

Diagnostic facts:
- the SAME ops work at **concrete** rank (`knField` at `2+2` in `UhlenbeckBaseProducer.lean`);
- they work for **generic `s`** in the lighter `Tensor/` layer
  (`TotalNabla0SRealizes.add`, `metricTraceFirstTwoField_add/_zero`, `NablaTraceGen.lean`);
- they fail for **generic `4+k` in this heavy RicciFlow import context**.
- `Tensor0SField` is an `abbrev` carrying `letI := tensor0SBundle_topology s` internally; the
  module also needs `tensor0SBundle_smooth` (needs `[IsManifold I (∞+1) M]`, present).

**ROOT CAUSE — fully isolated by minimal repros (2026-06-10).** Throwaway test files (deleted)
walked it down to the real cause.  WRONG guesses, each ruled out by repro:
- `[InnerProductSpace Real E]` diamond — removing it does NOT fix it;
- rank shape `s+2` vs `4+k` — both fail equally;
- instances-in-scope — explicit `[IsManifold I 1/2/(∞+1) M]` in the signature does NOT fix it;
- theorem-vs-def — a *theorem* with `(0 : Tensor0SField (s+2))` ALSO fails in the importing file
  (while the identical `metricTraceFirstTwoField_zero` compiles *inside* `NablaTraceGen`);
- `open`s — adding `open DifferentialGeometry.Tensor.Coordinates` does NOT fix it.

**CONFIRMED CAUSE = instance-synthesis PERFORMANCE pathology.** With `set_option maxHeartbeats
1000000` + `synthInstance.maxHeartbeats 1000000`, synthesizing `OfNat (Tensor0SField (s+2)) 0`
gives **`(deterministic) timeout at whnf, maximum number of heartbeats (1000000)`** — i.e. the
search does *pathologically expensive `whnf` reductions* (unfolding the bundle/`ContMDiffSection`
definitions) and runs out of fuel; it is NOT a missing instance.  Inside `NablaTraceGen` (low in
the import tree) the same search is fast; once the BBS chain (`RmRealizationBridgeAllK` and below)
is imported, some candidate instance makes the search explode.  A bigger heartbeat is not a real
fix (1M already overshoots; `maxHeartbeats 4000000` per declaration would make the file
uncompilable).

## Fix routes for next attempt (in priority order)
A. **Find & fix the pathological instance.** In a file importing `RmRealizationBridgeAllK`, run
   `set_option trace.Meta.synthInstance true in example : Tensor0SField (s+2) := 0` and read the
   trace to see which candidate instance the search keeps unfolding (the loop/blowup).  Likely a
   bundle `local instance`/`letI` that escaped a section and now offers a non-canonical
   `TopologicalSpace`/`VectorBundle` path the synthesizer keeps trying.  Fix = scope it, lower its
   priority, or give the canonical one higher priority.  This is the clean root fix and likely helps
   the whole BBS layer's compile times.
B. **Bypass synthesis: provide the module instance explicitly.** `letI : Zero (Tensor0SField (4+k))
   := <explicit ContMDiffSection zero>` (and similarly `AddCommGroup`/`Module`) so the `0`/`+`/`•`
   never trigger the expensive search.  Needs the exact instance path written by hand once; reusable
   via the `stZeroField`/`stAddField`/`stSmulField` helpers.
C. **Avoid raw module ops entirely.** Carry the closures through the realizer `TotalNabla0SRealizes`
   (already elaborated in the healthy `HigherOrder` layer) so `StarSum2` never writes `0`/`+`/`•` on
   `Tensor0SField` in the heavy context.

This is a Lean-environment performance bug, separable from the (sound) math design above — a good
candidate for a focused `trace.Meta.synthInstance` session or a Lean-expert/Pro consult.

## MECHANISM + AUTHORITATIVE FIX (user-confirmed, 2026-06-11)

`Tensor0SField` is an **abbrev carrying `letI := tensor0SBundle_topology … s`** internally.  So
`(0 : Tensor0SField (s+2))` is NOT a plain zero: synthesizing `OfNat (Tensor0SField (s+2)) 0`
forces the search to find `ContMDiffSection`'s `Zero`/`OfNat` AND unfold the bundle
topology/smooth-bundle instances.  In the heavy RicciFlow import context (post
`RmRealizationBridgeAllK`) that `whnf` unfolding becomes huge → `synthInstanceFailed` / `whnf`
timeout.  `metricTraceFirstTwoField_zero`'s own note in `NablaTraceGen.lean` already records this
exact class: *generic `domDomCongr e 0 = 0` / `product A 0 = 0` jam `OfNat 0` at statement time;
low-level files can only pin the instance at concrete ranks or inside a proof.*  **Take that note
as the answer — do NOT re-run `letI`/extra-`IsManifold`/def-wrapper variations; the repro proves
they all hit the same synthesis path.**

**Do (in priority):**
1. **Never** write generic `0`/`+`/`•` on `Tensor0SField (4+k)` in a heavy RicciFlow/StarSum file.
2. Put the canonical `stZeroField`/`stAddField`/`stSmulField` (and any generic-rank field algebra)
   in a **low-level tensor file** that does NOT import the BBS chain, where they compile to
   `def`/`theorem`; then `import` and *apply* them (a function application does not re-trigger the
   search).  (NB: even importing `NablaTraceGen` already broke the repro, so the helper file must
   sit low — at/near the `Tensor/RSTensor/…` Multilinear/Coordinates layer, not above it.)
3. Or bypass raw `Tensor0SField` algebra entirely: state `StarSum2`'s closures through an
   already-compilable realization API (`TotalNabla0SRealizes`-style closures in the healthy
   `HigherOrder` layer), so no raw `0`/`+`/`•` appears in the heavy context.

The verified upstream pieces (`traceRicWit`-style slot algebra, `nabla_metricTraceFirstTwo0S`,
`spatialComm_nablaKRm_split`, `abs_curvatureAction0SAt_orthoBasis_le`, the orthonormal collapse)
all remain ready; only the predicate's hosting layer is the open question.
