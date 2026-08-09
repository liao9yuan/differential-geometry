# Slot-insertion covariant naturality

## 2026-07-14 cotangent evaluation

The fully applied theorem `cotangent_slot_apply` now states that inserting an
endomorphism into the unique covector slot is precomposition of the associated
cotangent functional. The result replaces private copies in higher DeTurck
files and keeps downstream proofs scalar-valued before unfolding slot
insertion.

Focused verification and the producer refresh passed.

## 2026-07-27 operator algebra

The public API now also contains additivity, scalar compatibility,
composition, and identity for `slotInsertEndoCc`.  These are the canonical
field-level laws used by the low-regularity DeTurck principal coefficient;
the higher inverse-metric module no longer carries private duplicates.

Focused verification and the named producer refresh passed.
