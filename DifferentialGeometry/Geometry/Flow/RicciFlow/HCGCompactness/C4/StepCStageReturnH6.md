# H6 stage return

`H6NormalData.mapsTo_tail` and `return_tail` construct the approximate reverse
stage control with the same H6 provider used by the forward map. Focused and
exact verification pass (`4144/4144`).

The return brick is complete and is used only for injectivity control; the
exact inverse metric carrier still uses `Function.invFunOn`.
