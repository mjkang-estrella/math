# PerSupport remains incomplete; zero credit

The required `per_support : Nut8.PerSupport` endpoint has not been obtained.
The root-fixed interface has not been changed or shown false. No acceptance or
count change is claimed. This lane does not prove Coverage8.

## Remaining obligations

1. Prove a finite enumeration of signed, positive-tree representatives, using
   each checked permutation and parent tree. The existing unsigned enumeration
   must be carried through the same permutation. Parameterize non-tree edge
   signs, loop signs, and the shared semi-edge sign; prove every normalized
   structural matrix is literally an image member. Preserve a single sign for
   each double edge and a single shared sign for all magnitude-one diagonals.
2. The r2 certificate matrices use different support labels and trees. The
   diagnostic `reconciliation.json` records equality of the 9,172 matrix sets
   only AFTER relabelling and switching. `support-transport.json` supplies
   untrusted permutation witnesses, not Lean certificates. Either check these
   witnesses and prove exact image membership after the extra switching, or
   regenerate certificates in the new catalogue normalization. Raw list lookup
   into the inherited r2 certificates is not justified: none of those literal
   matrices equals a literal matrix in the new normalized enumeration.
3. Only the inherited first 32 certificate records are kernel checked. The
   other 9,140 have not been compiled in this lane. The inherited pilot checks
   can overlap those 32 and are not additional coverage. No unsigned spectral
   pretest is used. The Python diagnostic confirms 8,208 nonsingular and 964
   singular records, but it is not a proof of their certificates.
4. Compose exact signed enumeration membership, all determinant/cofactor
   certificates, and obstruction_of_switch / obstruction_of_relabel to prove
   PerSupport for all 194 supports. No hypothesis replacing this obligation
   has been asserted universally.

See SUMMARY.md and results.json for the final validation state. A successful
partial replay checks only delivered declarations; it cannot establish PerSupport.
