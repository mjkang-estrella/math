# H030 storage candidate: paid index recovery survives, numerical gains unproved

2026-10-08. Raw Factory Fable memo in H030-storage-fable-raw.md. Native Astra
/root/h007_additive_relations independently reviewed mathematics; root checked
the signed interval construction below. Claude Opus primary filter/prior-art
review is still RUNNING. No experiment or Lean theorem; improvement NONE.

## A: a concrete conditional construction

A filter pass on x(R) need not reveal whether R=iG or -iG. Resolve over
[-b,b], with b<q/2, not only [1,b]. Exact subtable stores x(uG),1<=u<=beta,
and u; handle O separately. Put D=2beta+1, T=ceil(b/D). Query R-tDG for
t=-T,...,T. Each match gives w=tD+u or tD-u; verify the full point and
signed range 1<=|w|<=b, then perform the outer scalar recovery/verification.
The intervals [tD-beta,tD+beta] are contiguous and cover [-b,b]. Thus a
nonmember is rejected after at most2T+1 exact lookups, O(b/beta+1) group
operations with sequential shifted-point generation and paid initial shift.
Prepare DG/initial shift, table, full R, lookup and final checks explicitly.
Point sign can instead be checked using stored full points; nothing is free.

False positives require this full unsuccessful signed search. The memo's
rough b^delta/4 successful positive-interval average cannot price that work.
Its15–20 bits,13x density, crossover values and <1M construction-per-entry
price are therefore NOT accepted. Hash seeds/directories/slack, failure and
rebuild work, and peak construction storage remain unresolved.

There is nevertheless a useful conditional asymptotic bridge. Assume a real
approximate-membership implementation with no false negatives, false-positive
bound epsilon for every fixed nonmember query independent of its random seed,
and the declared construction/space costs. Then

    W = W_filter(b,epsilon) + W_exact(beta) + W_construction,
    C <= C_generate/build + g*C_probe
         + g*epsilon*C_unsuccessful_resolve
         + C_successful_resolve + C_verify

for a fixed full-cap g-query schedule independent of filter randomness, with
nonnegative costs. Early stopping does not increase that full-cap bound. The
query-independence premise must be checked, not inferred for arbitrary walks.

If W_filter=O(b log(1/epsilon)), beta~b/log b, epsilon~1/log b and
log p=O(log b), stored filter plus exact subtable occupy O(b loglog b) bits,
before unresolved construction overhead. False resolutions use O(g) EXPECTED
GROUP operations, since each costs O(log b). This does not bound all bit/RAM
work: sorted exact lookup adds comparisons, hashing requires its own guarantees,
and filtering/build operations and seed storage still count. It is not a
complete-cost improvement or interval-DLP oracle; the subtable is paid.

Next gate is an explicit primary-supported filter and exact-table layout with
its real successful/unsuccessful resolver and construction cost. Compare equal
total bytes against competent compression; novelty and effectiveness are
different questions. If known, give the comparison baseline that capability.
No curve run justified by the raw numerical tables.

## C: withdraw the overbroad optimality claim

Realized labels chosen from target coordinates are not a precommitted candidate
secret set. Their realized equation count alone gives no uniform-secret bound.
Also, signed equality can be useful WITHIN a Q-coefficient class:

    bQ+a_i G = -(bQ+a_j G) implies 2b*k=-(a_i+a_j) modq.

For b!=0 and odd prime q this can determine k; arbitrary offsets need not
have only linearly many pair sums. Therefore the raw class includes mechanisms
its f-class count does not account for. No universal record-tradeoff theorem,
GWZ optimality over that entire class, or compression endpoint is accepted.
Recalled preprocessing lower bounds require actual theorem/hypotheses review.
This correction does not assert a faster algorithm from those comparisons.

## B and D

The rho-plus-table survival formula is conditional on an ideal uniform-sampling
model and useful labels, not an actual walk theorem. Filter false positives
occur on all nonmember probes, not just the successful table channel. No6%
ceiling or0.35M kill threshold is accepted without complete optimized costs.
Keep B lower priority. External sort/merge remains a known comparator, not a
new discovery; its stated bandwidth ledger also depends on its chosen layout.

Main result: retain A for corrected paper costing, reject C's broad proof,
preserve B as conditional. Generic exponent reference1/2 remains unchanged.
