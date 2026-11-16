import LeanModels.Sv.Observe

/-!
# E observation compatibility import

`Observe.lean` is the single declaration site for the observation interface,
its run2 backend, and the `Obs_E` signature.  This module name is retained as
an import-stable compatibility layer for the E bridge (`ObserveResolve`), so
that the two observation backends cannot drift into duplicate structures.
-/
