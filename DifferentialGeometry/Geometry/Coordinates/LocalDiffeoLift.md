# LocalDiffeoLift

## 2026-07-27 compact-fenced lift API

`IsLiftOn` is the generic continuous interval lift predicate for a local
diffeomorphism.  Its values are constrained to the local-diffeomorphism
source, and its off-interval values are intentionally unspecified.

`IsLiftOn.contDiffOn` upgrades such a lift to `C¹` whenever the base path is
`C¹`.  This keeps the compact-continuation argument topological while giving
the CGT specialization the differentiability needed by the intrinsic Gauss
length fence.

`IsLiftOn.eqOn_of_eq` proves the canonical uniqueness statement from equality
at any prescribed time in the closed interval.  It restricts the local
diffeomorphism to the open source subtype, applies local injectivity plus the
separated-map equality-locus theorem on the preconnected closed interval, and
returns `Set.EqOn` rather than the false literal uniqueness of total functions.
`IsLiftOn.eqOn` is the left-endpoint compatibility wrapper.

`IsLiftOn.extend` glues an existing lift to a selected local inverse branch.
The branch-source condition and the requirement that inverse-branch values stay
in the ambient source `U` are separate on purpose: a witness selected from
`IsLocalDiffeomorphOn ... U` need not have its entire partial-diffeomorphism
source contained in `U`.

`IsLiftOn.exists_of_compact` is the compact-fenced continuation theorem.  It
uses the supremum of reachable times, a compact convergent subsequence of
partial-lift endpoints, Hausdorff uniqueness of the two endpoint limits, and
the selected local inverse branch to close and then extend the reachable set.
It assumes neither a covering map nor properness of the full local
diffeomorphism.  The fixed compact fence need only contain the terminal value
of every partial lift.

Focused verification and the targeted artifact refresh are green.  Compact-
fenced lift existence and arbitrary-time uniqueness are theorem 100%, and
their generic dedicated machinery is 100%.  They are consumed by
`CGTExpLift.lean` and the right-cancellation proof in
`CGTHomotopyLift.lean`.
