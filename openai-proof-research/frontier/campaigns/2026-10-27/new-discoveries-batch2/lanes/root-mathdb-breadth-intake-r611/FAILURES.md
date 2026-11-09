# Root reconciliation failures

Initial administrative schema inspection assumed flat-bindings.json was a list; it is an object. KeyError 0 stopped that helper (guard exit 1). All inputs had already been frozen; no scientific conclusions or ledger updates used the failed inspection. Corrected parser inspects the actual object schema.

The subsequent administrative binding-key inventory display was truncated. No conclusion depended on the truncated inventory; the verifier iterates every mapping entry directly.
