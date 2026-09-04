# Localization

## 2026-08-29: compact local-to-global witness

- Added `exists_global_wit`, the canonical compact localization producer for a
  local `W^{1,2}` witness. It returns a whole-space witness whose function and
  selected weak-gradient representative agree pointwise on the given compact
  subset.
- The construction uses a cutoff equal to one on a compact buffer around the
  target, multiplication in `W^{1,2}`, compact-support promotion to
  `W_0^{1,2}`, zero extension, and explicit witness transport across the
  `ENNReal.ofReal 2 = 2` boundary. Local constancy of the cutoff supplies exact
  gradient agreement.
- The theorem itself is source-complete (100%). Its dedicated localization
  machinery is complete (100%). This is one producer for the P1c weak-solution
  lane, whose downstream theorem completion is tracked separately in the
  comparison plan; no downstream completion percentage is inferred here.
- Focused elaboration required only the local notation repair from `𝒩 x` to
  `nhds x`; the proof route and theorem statement were unchanged.
- Focused verification passed without warnings.
