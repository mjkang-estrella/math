Author-side candidate packet for structuralr44. Read original-scope.txt then
candidate.md; operation/history and reading limits are separate. This is not
an acceptance or independent gate. Verify with:

python -B verify.py --expected-manifest-sha256 CALLER_SUPPLIED_EXTERNAL_ANCHOR

The required anchor must come from the parent handoff, not from a self-reported
file. The verifier is read-only and checks exact file AND directory inventory,
source/primary identities, frozen scope, and rejects links/hardlinks/nonregular
nodes. It does not verify the mathematical proof. private/ is ignored and not
for publication. Original prose CC BY4.0; code MIT; third-party rights unchanged.
