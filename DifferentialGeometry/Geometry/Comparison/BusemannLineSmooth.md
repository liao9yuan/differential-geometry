# Busemann chart smoothness

## Role

This file is the P1c bridge from the checked homogeneous all-order interior
regularity producer to the actual chart expression of a line Busemann function.
It deliberately reruns the chart PDE data and does not infer higher regularity
from the opaque local `W^{2,2}` endpoint.

## Mathematical route

- `busemann_chart_wkp` reuses `busemann_chart_data`.  Around the chart center it
  places a compact closed ball inside both the original weak-solution ball and
  the Euclidean chart target, extends the metric coefficient smoothly, and
  restricts the homogeneous solution to an outer ball of radius `δ / 2`.
- `homSol_memWkp_on` is then applied at every order on the same inner ball of
  radius `δ / 4`.  Its `W^{k+2,2}` output is downgraded to `W^{k,2}`; no new
  source equation or recursive compact exhaustion is introduced here.
- `busemann_chart_cdiff` first shrinks once more so that its ball lies in the
  chart target.  The all-order Sobolev embedding supplies a smooth almost-
  everywhere representative.  The one-Lipschitz continuity of the Busemann
  function and continuity of the inverse chart make the actual raw chart
  function continuous, so equality almost everywhere on the open ball upgrades
  to pointwise equality and transfers smoothness to the actual function.
- The private center bridge `contMDiffAt_of_raw` composes the smooth raw chart
  function with `toEuclidean ∘ extChartAt`, then uses the defining chart identity
  near the chart center.  Applying this bridge at every point to
  `busemann_chart_cdiff` gives the global endpoint `busemann_smooth`.

## Native reuse

- `busemann_chart_data`
- `DeGiorgi.IsSolution.restrict_ball`
- `exists_smooth_metric_extension`
- `NirenbergHomogeneous.homSol_memWkp_on`
- `MemWkp.le_of_le` and `MemWkp.mono_set`
- `EuclideanIteratedEmbedding.contDiffOn_of_forall_memWkp_two`
- `Measure.eqOn_open_of_ae_eq`

No reference-tree import, new assumption, auxiliary predicate, or theorem-shaped
frontier is used.

## Verification and accounting

After making the infinite smoothness grade explicit, the second focused check
passed without warnings.  Thus `busemann_chart_wkp` and
`busemann_chart_cdiff` are verified.  The newly written global endpoint
`busemann_smooth` and its two chart producers now pass the focused check without
warnings.  The module's explicit named refresh also passed, so the exported
declarations are current for downstream consumers.  All three public endpoints
in this file are **100% verified**, and their dedicated chart regularity
machinery is verified.  The file is a local
smoothness producer inside the Busemann-to-splitting lane and does not by itself
complete Cheeger--Gromoll splitting or change the whole Poincare endpoint.

There is no remaining local mathematical, API, elaboration, or artifact blocker
for the global Busemann smoothness statement.  Hessian vanishing and the
parallel-gradient step remain separate downstream P1c frontiers.
