# LocalNemytskii

## 2026-07-19

This file is focused-check green, warning-free, and its named `.olean` has
been refreshed.  It supplies the measurable state-set lift `aeSetLift`, the
local linear-growth integrability lemma `memLp_on`, and `nemytskiiOn` for a
nonlinearity defined only on a state subtype.

The construction is genuine local machinery: outside the almost-everywhere
state set it uses the supplied zero member only to choose a total measurable
representative.  It does not assume a global extension or add a PDE
hypothesis.

Endpoint accounting: this producer is verified, but both
`ricci_flow_unif_existence` and `ricci_flow_forward_unique` remain 0% until
their exact declarations are proved and checked.

## 2026-08-04 — the TAME sibling of `nemytskiiOn` is now public here

Added, focused-check green and axiom-clean:

* `timeL2_norm_le_four` — the four-term `L²` Minkowski estimate.  It was a
  `private l2_four` inside `TameForcingFixedPoint.lean`; it is abstract
  time-`L²` algebra with no geometric content, so it belongs at this layer
  beside the other `timeL2_norm_le_*` bounds it generalises.  The private copy
  was deleted, not duplicated.
* `memLp_tame` — the tame counterpart of `memLp_on`: a *continuous* state-set
  map obeying the three-arm estimate
  `‖N u − N v‖ ≤ A·R‖u−v‖ + B‖J(u−v)‖ + C(‖u‖+‖v‖)‖J(u−v)‖`
  sends state-set-valued time-`L²` fields to `L²`.  Also formerly `private` in
  `TameForcingFixedPoint.lean`; its explicit argument order was preserved
  verbatim so that file's two call sites needed no edit.
* `nemytskiiTameOn`, `nemytskiiTameOn_coeFn` — the tame Nemytskii operator and
  its representation lemma, mirroring `nemytskiiOn` / `nemytskiiOn_coeFn`.

**Why a second Nemytskii operator is not a parallel hierarchy.**  `nemytskiiOn`
needs `LipschitzWith L N` merely to build the `L²` field.  At critical
regularity no such `L` exists: the state set bounds only `‖J u‖ ≤ R`, i.e. the
*lower* norm, while the tame arm carries the ambient top norm of the endpoints.
The two operators have the same underlying function whenever both are defined
(both are `MemLp.toLp` of `fun t => N (aeSetLift hzero f t)`), so no downstream
statement has to choose between them; only the *hypothesis* differs.

Lesson: `memLp_tame` needs `omit [InnerProductSpace ℝ Y] [CompleteSpace Y]`
exactly as `memLp_on` does; `nemytskiiTameOn` does not (its codomain is
`timeL2 Y T`).
