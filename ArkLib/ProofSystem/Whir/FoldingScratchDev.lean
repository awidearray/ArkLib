import ArkLib.ProofSystem.Whir.Folding

/-!
Compatibility shim for the Finding-19 repair of `folding_preserves_listdecoding_base`
(WHIR Lemma 4.21).

The production theorem now lives in `Folding.lean` as
`Fold.folding_preserves_listdecoding_base_of_mca_bridge`. This scratch file intentionally exports
no declarations, avoiding a duplicate-definition race with the production namespace.
-/
