# LowRegBgGalerkinIdent.lean

## Role

This module is the minimal arbitrary-background Galerkin identification layer.
It keeps `timeL2EigenProj`, `projNfun`, the heat/Duhamel solution, mode
coefficients, and every Sobolev space on the state metric `g₀`.  Only the
nonlinearity is widened to `lowregNfun g₀ g_bg`.

## Production API

- `lowreg_proj_atBg` consumes one `IsBgSolveAt g₀ g_bg K` package and returns
  a projected forcing sequence converging to its forcing, together with the
  fixedness, state-ball, background Nemytskii identity, trace, PDE, and forcing
  ball needed by the energy route.
- `lowreg_projMode_atBg` adds pointwise convergence of every state-metric
  eigenmode and retains the same projected trajectory package.

The proofs mirror `lowreg_proj_at` and `lowreg_projMode_at`.  The scalar tuple
is read directly from `K`; the continuity, tame, zero-state, horizon, forcing
ball, and Nemytskii facts are the corresponding `IsBgSolveAt` projections.
No compactness or new nonlinear identity is introduced.

The compatibility endpoints `lowreg_proj_tendsto` and
`lowreg_projMode_tendsto` were deliberately not ported because the route-(c)
production chain consumes the explicit packet APIs.

## Verification

Source review passed: there is no diagonal `g₀ g₀` nonlinearity, proof
placeholder, heartbeat override, or compatibility endpoint.  Lean verification
passed in the focused file check.  The exact module was then refreshed
successfully with a single Lean worker, so the exported declarations are fresh
for downstream importers.

## Accounting

The background Galerkin-identification brick is complete (100%).  It is one
input to the still-partial higher-rung/mass phase, not the mass theorem itself:
`lowreg_loMassBg` remains unstated (0%), as does headline
`ricci_flow_unif_existence` (0%).
