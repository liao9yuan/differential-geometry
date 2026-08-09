# EdgePathPairing

## Purpose

`EdgePathPairing.lean` is the path-integrated formal-partner layer for the
complete polarized raw Riemann--Lie top pair.  It keeps four roles separate:

- `T` fixes the realized radial metric path;
- `U` supplies the Hessian in the pair coefficient;
- `P` is the independent coefficient passenger; and
- `V` is the Hilbert-space test tensor.

The module does not state an arbitrary-passenger identity for the full
low-base operator.  It also deliberately exports no complete-top Green
theorem: the intended downstream test is `V = L² T`, and moving a spatial
derivative onto that test would charge `H5`.

## Public API

- `edgeTopPairInt` is the path integral of `edgeTopPairBi`, the raw pair
  coefficient `Q(U)`.
- `edgeTopPair_joint` exports the joint-smoothness witness for this polarized
  pair family.
- `edgeTopPairInt_apply` commutes the path integral with application to an
  arbitrary fixed passenger.
- `edgeTopPartnerInt` is the path integral of `edgeTopPartnerBi`, the explicit
  partner `Z(P,V)`.
- `edgePath_inner_bi` proves the exact non-Green identity
  `<V, app (Q(U)) P> = <Z(P,V), nabla² U>`.

Only the complete pair-family joint witness is public; the monomial assembly
and the generic path/application proof remain private implementation
machinery.  They use `edgePairMono_joint`, inverse-metric sharp joint
smoothness, slot-insertion joint smoothness, and fixed
permutation/application algebra.  No metric fourth jet, `H4`/`H5` radius, or
differentiated curvature coefficient enters this layer.

## B02 seam

For the downstream diagonal residual, this theorem covers each oriented term
once the exact B02 normal form has exposed it: use `(U,P)=(LT,T)` for
`app (Q(LT)) T`, `(U,P)=(T,LT)` for `app (Q(T)) LT`, and `(U,P)=(T,T)` for a
diagonal anchor.  These are exact formal-partner substitutions; this file does
not claim that the whole low-base operator refolds for arbitrary `U`, nor does
it assert that the three terms already form B02.  The remaining theorem must
first produce their signed combination together with the raw order-zero and
top commutators from `lowBase_L_nf`, and then prove the quantitative estimate.

## Verification

The complete path-pairing API, including the public joint/application seam,
passed focused verification and exact targeted refresh.  The focused check
reported no local warning.  There are no `sorry`, `admit`, or axiom
declarations in this file.

## Progress accounting

- `edgePath_inner_bi`: **100% as the exact theorem stated here**; its dedicated
  path-integral and joint-smoothness machinery is also **100% verified**.
- `edgeTopPairInt_apply`: **100% as the exact application theorem**.
- The combined quantitative B02 estimate: **0% as a theorem**; its dedicated
  exact normal-form and partner infrastructure are substantial but separate.
- `ricci_flow_unif_existence`: **0% as a theorem**.  This file is one algebraic
  producer inside the Route-(c) low-base energy phase, not an existence proof.
