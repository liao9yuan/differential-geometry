# SourceMaster

## Goal

`src_master_nonsmooth` converts an actual local scalar-source `H₀¹` weak
equation into the raw nonsmooth Nirenberg master bound, while returning the same
whole-space solution witness and coefficient-room agreement as the homogeneous
producer.

## Route

1. Globalize the local solution witness with `DeGiorgi.exists_global_wit`.
2. Use `srcSol_substOn` to obtain the unexpanded local standard-test identity.
3. Feed that identity to the shared `subst_expand_on` theorem in
   `HomogeneousMaster.lean`; no part of its coefficient-scaling or discrete
   integration-by-parts proof is copied here.
4. Identify the standard tests built from the local and global witnesses on
   the cutoff room, extend the scalar source pairing to the whole space, and
   scale it by `-rho⁻¹`.
5. Invoke `master_raw_nonsmooth` unchanged and rewrite its source term back to
   the original local pairing.

The last rewrite first normalizes the raw theorem's
`NirenbergTestFunction.nirenbergTestFunction` spelling to the definitionally
equal `NirenbergStandardTest.standardNirenbergTest` spelling used by the local
source theorem. This is only a namespace/definition-shape adapter.

The theorem consumes the actual `H₀¹` weak equation directly. It adds no weak
solution predicate, no extra source regularity assumption, and no expanded
substitution-identity hypothesis.

## Verification

The shared `HomogeneousMaster` refactor passed focused verification and its
explicit named refresh. The first `SourceMaster` check exposed only the final
standard-test namespace rewrite shape; after the minimal adapter, the focused
recheck passed without warnings. Once a real downstream consumer existed, the
explicit `SourceMaster` named refresh also passed.

## Progress estimate

- `src_master_nonsmooth`: 100% at this focused producer boundary.
- The scalar-source raw master assembly: 100% source-written and focused-verified.
- The local scalar-source `W²` theorem remains unstated/unproved, 0%; this is its
  master-inequality producer only.
- The all-order `MemWkp` bootstrap and P1c smooth-representative theorem remain
  unstated/unproved, 0%; their dedicated local elliptic machinery remains roughly
  65–70% complete.
- The final P1 splitting theorem remains unstated/unproved, 0%.
