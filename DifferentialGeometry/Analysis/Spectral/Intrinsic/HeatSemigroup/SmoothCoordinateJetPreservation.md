# SmoothCoordinateJetPreservation.lean — notes

## 2026-08-03 — F1 (FORCEJETMASS_PLAN §9): `ha_super` deleted; the jet layer is order-free — GREEN

**Outcome: GREEN.**  The supercriticality gate `2 * Module.finrank ℝ E + 10 ≤ a` was
vestigial in this file's time-jet layer.  Deletion-only surgery, no proof body touched:

* `deTurckRemainder_path_timeJet_section` — dropped **both** `(a : ℕ)` and `ha_super`.
  The conclusion names only `deTurckSmoothRemainder`, which carries no order, and the
  body delegates to `deTurckRemainder_path_coeff_timeJet_withMass`, which never took `a`.
* `deTurckSmoothN_path_coeff_jetSpectralMass` (private) — dropped `ha_super` only.
  `(a : ℕ)` stays: its conclusion names `deTurckSmoothN g₀ g_bg a (F t) …`, so the order
  is genuine *data* here, but never a *hypothesis*.
* Two in-file call sites updated (inside `deTurckSmoothN_path_coeff_jetSpectralMass`
  and `deTurckSobolevNHa2_jetSpectralMass_preserving`) by argument removal only.

`deTurckSobolevNHa2_jetSpectralMass_preserving` keeps its `ha_super` legitimately — it
feeds `deTurckRealizabilityRadius`, which is a genuine consumer of supercriticality.
That is the boundary: **realizability radius is order-gated, the time-jet layer is not.**

Focused check passed.  Targeted module build passed.  No `sorry`/`admit`/`axiom` in the
file; no heartbeat options changed.  Only pre-existing warnings.

**Mathematical content of the result.**  The chart-level chain rule producing finite-order
time-jets of the Ricci–DeTurck remainder along a smooth path is available at *every* base
order, in particular at `a = 2`.  Nothing in the jet construction — the coefficient
extension, the `iteratedDerivWithin` transfer, or the `iteratedCovGrad` mass bound — sees
the Sobolev exponent; the mass bound is produced from `hmodemass` at an arbitrary `σ`
chosen *inside* the proof (`σ' = 2k ≥ q`), so the supercritical embedding is never used.
That was the whole hypothesis F1 tested, and it holds.

**Reusable lesson.**  `set_option linter.unusedVariables false in` immediately above a
declaration is a reliable marker for a vestigial binder: it exists precisely because Lean
had already noticed the variable was unused.  Both declarations here carried it (as do the
two counterparts in `ForcingFiniteOrderTimeRegularity.lean`).  Grep for that `set_option`
next to an order/regularity gate before assuming an estimate is order-dependent.
