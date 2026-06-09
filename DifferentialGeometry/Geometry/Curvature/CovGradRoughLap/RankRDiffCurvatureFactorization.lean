import DifferentialGeometry.Geometry.Connection.TensorNabla.FullHomCovariantCalculusRS

/-!
# (Superseded) the full Hom-bundle operator-field `(∇R)·` factorisation at valence `r`

The full Hom-bundle operator-field action `appFullRS`, the slot extension `slotExtendFull`, the
second-order Hom-bundle section covariant gradient field, the section-level covariant product rule
`covGrad_appFullRS_eq`, the value-local fibre-operation full-Hom factorisation engine
`exists_value_local_appFullSec`, the per-point fibrewise Cauchy–Schwarz / uniform contraction envelope,
and the full Hom-bundle operator-field **normal-form engine** (`NormalFormFull` /
`normalFormFull_of_base` / `exists_jet_bound_of_normalFormFull`) now all live in their proper
**curvature-free** topic home `Geometry.Connection.TensorNabla.FullHomCovariantCalculusRS`, which imports
only the second-order Hom-bundle and its Riemannian / codomain-only operator-field calculus — *not* the
rank-`r` curvature towers.  That cycle-free placement is what lets the rank-`r` pure-Riemann and
differentiated-curvature towers (`RankRPureRCurvatureTower`, `RankRDiffCurvatureTower`) consume the engine
to express their value-local order-`0` curvature bases as fixed-field full Hom actions and run the
single-index telescoping normal-form induction.

The earlier draft homed here pinned the differentiated-curvature carrier to the order-`1` moving-centre
pure-Riemann trace `genuinePureRDiffOpRS g r 1 rr` and demanded its value-locality (the tensor
differential-Bianchi `∇W`-cancellation) as a posited child `genuinePureRDiffOpRS_one_valueLocal`.  That
requirement was a self-inflicted design artifact: the *proved* rank-`0` design carries the `(∇R)·` field as
a manifestly value-local fixed-field action `appCc (covGrad (curvOpField g s)) S`
(`MovingFrameDiffCurvTraceSection`), never proving "the order-`1` trace is value-local".  The redesigned
rank-`r` tower mirrors that: its order-`0` `(∇R)·` carrier is the value-local-by-construction full Hom
action `appFullSec (homTensorRSCovGradSec (curvOpFieldRS g r rr))` of the section covariant gradient of the
fixed order-`0` curvature operator field (`RankRDiffCurvatureTower`), so value-locality holds by
construction and `genuinePureRDiffOpRS_one_valueLocal` is eliminated entirely.

This file is retained only as the navigation pointer to that relocation; it carries no declarations.
-/
