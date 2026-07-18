# RadialGram.lean

## 2026-07-17 radial Wronskian producer

Added `radial_wronsk_zero`.  On one common positive radial scale, two
packaged radial Jacobi fields whose launch directions are small have zero
Wronskian on every `Icc 0 b` with `0 < b < 1`.  The proof combines the existing
radial differentiability, interior and centre Jacobi equations, centre
vanishing, and the pointwise-regularity theorem `wronskian_zero_on`.

The proof body passed focused verification and the explicitly named module
build.  The declaration was then mechanically shortened from a 21-character
name to the project-compliant `radial_wronsk_zero`; a post-rename source check
was blocked by the active object refresh chain, whose next missing dependency
was `LeviCivita.Curvature.Realized.olean`.  No proof body changed during the
rename.  This is a radial symmetry producer, not a Bishop--Gromov theorem.

A follow-up API audit found that linear independence below the selected normal
radius is not a new no-conjugate-points theorem: `expMapDiffeo` already makes
its differential invertible on its source.  The remaining local bridge is the
scaling identity `J_{x,w}(t) = J_{t*x,t*w}(1)` and transport of that injectivity
to the radial family.  An attempted implementation was not retained because an
active upstream `.olean` refresh chain prevented verification.  The genuinely
geometric frontier begins with the shape operator and trace Riccati inequality
from the Ricci lower bound.  Polar integration and cut-locus transfer remain
later frontiers.
