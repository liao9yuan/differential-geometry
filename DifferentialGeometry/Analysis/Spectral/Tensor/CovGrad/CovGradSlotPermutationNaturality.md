# CovGradSlotPermutationNaturality

## 2026-07-27 dependency split

`unitTensor` and `unitModel` moved to `UnitModel.lean`, their lower natural
home.  This module imports that leaf and retains the same public declarations
through the same namespace, so downstream theorem statements do not change.

Focused verification is pending while another lane's targeted build is active.

