# DeTurckRemainderLowBaseA2

## Role

This module supplies the compatible completed high and low realizations of
the canonical smooth second-order action.  It is independent of the
geometric producer that proves the concrete coefficient is small.

## Current state

Focused verification and the targeted exact refresh are GREEN with no local
warnings or proof placeholders.
The endpoint `a2_pair` gives
`H4 -> H2` and `H3 -> H1` operator bounds, smooth-core identities, and the
adjacent-scale commuting square from one pointwise/two-jet coefficient
envelope.

The companion theorem `a2_diff` applies the same constant to a coefficient
difference.  A pointwise/two-jet bound for `A.C2 - B.C2` now gives operator
norm bounds for both `A.a2Hi - B.a2Hi` and `A.a2Lo - B.a2Lo`.  This is the
generic bridge needed after the geometric `C2` coefficient-difference
producer and before time measurability.

The public `a2Hi_core` and `a2Lo_core` read off both completions on the
smooth dense core without a small-radius hypothesis.  The public `a2_comm`
then proves their canonical Sobolev commuting square for every
`LowBaseActionData`, independently of any particular coefficient envelope.
These additions are focused GREEN and their targeted export refresh is
GREEN.

## Project position

- compatible generic A2 completion and coefficient-to-operator difference
  transfer: 100%;
- canonical low-base C2 pointwise/two-jet smallness producer: 100%;
- canonical pairwise C2 coefficient difference: separate active frontier;
- `ricci_flow_unif_existence`: unstated/unproved, 0%;
- dedicated uniform-existence machinery: approximately 98%.
