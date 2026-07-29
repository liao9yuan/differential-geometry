# DeTurckRemainderLowBaseAction

## Role

This module constructs the small low-base second-order action and the exact
smooth-core remainder split. It also packages the pair-reduced second-order
and lower actions used by the adjacent Sobolev scales.

## Verified state

The source is focused and exact GREEN. It contains no `sorry`, `admit`, axiom
declaration, or `whnf`. The public API includes `extraA2Act`, its high/low
bounds and compatibility, `lowA1Act`, `remainder_split`, `pairRedA2Act`,
`pairRedA1Act`, and `remainder_pair_split`.

These results are operator machinery. They do not prove the final
`LowBaseActionSplit`: that theorem remains unstated and therefore 0%.

