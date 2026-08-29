# CompactVolumeEquiv

## Set-local chart integral bridge

`chart_lint_le_on` is the set-local core of `chart_lintegral_le`.  It assumes
the density comparison only at points of a measurable set and compares the
corresponding local chart integrals restricted to that set.  Outside the set,
the indicator factor makes both integrands zero.  The existing whole-space
theorem is retained as the `s = univ` compatibility form, so existing callers
and its public statement are unchanged.

This refactoring moves no determinant or manifold-volume mathematics and does
not duplicate the local-coordinate proof.  Focused verification now passes
without warnings or placeholders.  The set-local chart-integral theorem and
its dedicated implementation are complete (**100%**); its downstream volume
measure consumer remains a separate verification stage.
