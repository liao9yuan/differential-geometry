# ForwardUniqueQuad

## Scope

This file is the generic, coordinate-free quadratic-curvature layer for the
forward-uniqueness remainder.  It deliberately does not import or mention the
solution-specific `fu*` fields or the wiring module.

## Source state

- `bPair` packages a routed tensor product followed by the two metric traces
  used by the Uhlenbeck quadratic term.
- `bPairSq_le` applies the two trace estimates to the routed product norm,
  giving the dimension cost `n^14`.
- `bPair_sub` records the exact polarization identity
  `Q(A)-Q(B)=B(A-B,A)+B(B,A-B)`.
- `bMetSq_le` now expands the two-contraction metric variation as
  `tr₁((tr₁-tr₂)X) + (tr₁-tr₂)(tr₂ X)`.  Applying
  `traceDiffNormSq_le` at ranks six and four gives
  `(6 n^18 Λ^2 + 4 n^22 Λ^4 BH) |h|^2 |A|^2 |B|^2`.
- `bDiffSq_le` combines that metric estimate with the fixed-metric
  polarization bound.  It controls a simultaneous change in both rank-four
  inputs and in the two contractions, with no new analytic assumption.
- `bPerm` is the canonical Uhlenbeck routing
  `![4,0,5,2,6,1,7,3]`; `bPair_comp` expands its two intrinsic traces in an
  arbitrary basis and recovers the expected double inverse-metric
  contraction.
- `bPerm2`/`bPerm3`/`bPerm4` are the three output-slot variants already used
  by the evolution algebra.  Their component lemmas, together with
  `bComb_comp`, identify `bComb` in an arbitrary basis with the exact signed
  combination `B_abcd - B_abdc + B_acbd - B_adbc`.
- `bCombSq_le` bounds this four-term combination by
  `16 n^14 |A|^4`, so the solution-specific speed estimate does not need to
  reconstruct the elementary four-term norm argument.
- `bCombDiffSq_le` combines four copies of `bDiffSq_le`.  Pairing the four
  summands in two differences keeps the elementary norm cost at `16` times
  the single-pair estimate.
- The routed-product fibre norm bridge is reconstructed locally from a
  metric-orthonormal basis, `normSq0S_domDomCongr`, and
  `normSq0S_product`.  This also lets `bPairSq_le` avoid inheriting the
  unrelated positive-dimension assumption carried by `traceProdSq_le`.

The focused check and targeted export refresh pass without errors or warnings.
The local rewrite-shape
and algebraic-normalization issues exposed by the first pass were repaired by
making the slot compositions explicit and proving the polarization identity
at the evaluated tensor-product level before applying the two trace-linearity
lemmas.

## Remaining frontier

The coordinate-free generic layer is source-complete.  The next layer belongs
in the solution-specific wiring file: instantiate `bComb` with each flow's
own lowered curvature field and use `bComb_comp` to identify its
coordinate-frame components with the existing
`uhlenbeckBTensorInFrame` combination.  That bridge should consume the
existing curvature realization and inverse-Gram hypotheses; it must not be
added here as a new analytic assumption.

This remaining work looks like routine component identification.  The generic
file is now verified and exports the exact component and norm interfaces that
the solution-specific layer needs.

## Honest progress

- Generic quadratic API planned in this file: theorem-level complete and
  focused-check verified (100%).
- The single-pair metric/input Lipschitz brick (`bMetSq_le` and
  `bDiffSq_le`): theorem-level complete and focused-check verified (100%).
- The four-term Uhlenbeck combination (`bComb_comp`, `bCombSq_le`, and
  `bCombDiffSq_le`): theorem-level complete and focused-check verified (100%).
- The solution-specific `fu`/component instantiation: not started in this file
  (0% theorem-level); its generic machinery is source-complete.
- The target `ricci_flow_forward_unique` theorem: unchanged by this file; its
  proof replacement is not part of this isolated producer brick.
