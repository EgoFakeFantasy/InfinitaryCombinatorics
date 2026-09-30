# Third-party notice

`FIMADModels/CheckedBooleanZFC.lean` adapts the proof in
`YesMetaZFC/Model/Boolean/ZFC.lean` from public revision
`51c348a593e41ef9e158d45c69b33d66c432a9b9`:
https://github.com/lanxinge/YesMetaZFC/blob/51c348a593e41ef9e158d45c69b33d66c432a9b9/YesMetaZFC/Model/Boolean/ZFC.lean

Copyright 2026 lanxinge and the YesMetaZFC contributors.
Licensed under the Apache License, Version 2.0. See `LICENSE-YesMetaZFC`.

Modifications: the namespace and theory are changed to the local `CheckedZFC`
presentation; the ZF/choice constructor split is flattened; and the model
certificate targets the local translated theory. All underlying Boolean-name
lemmas continue to come from the pinned upstream dependency.
The source definitions use identical ZFC formulas with kernel closure proofs.

`dependency-patches/kernel-checked-axioms.patch` adapts
`YesMetaZFC/SetTheory/Axioms/Common.lean` at revision
`a4903d2054085db0b454363a5fb15f1a3e1f9eab`, under the same Apache-2.0 license.
It preserves the eight fixed axiom formulas and replaces only their closure
certificates with kernel proofs, with increased elaboration limits. No mathematical
axiom is added or removed. The preparation script verifies the exact patch and
source hashes before building.

The upstream NOTICE is preserved in `NOTICE-YesMetaZFC`. This notice does not
assign a new license to the other original material in this repository.
