# MinMaxSplit

## Role

`lRegSpeed_split` is the reusable two-coefficient form of the regularized
L-speed Gronwall estimate.  It keeps the scalar-gradient coefficient separate
from the Ricci quadratic coefficient, which is necessary for parabolic scaling:
on a radius-`r` ball the two coefficients have orders `r^-3` and `r^-2`.

## Status

Warning-free focused verification and the named artifact refresh passed.  The
ball-local speed module consumes the exported theorem.
