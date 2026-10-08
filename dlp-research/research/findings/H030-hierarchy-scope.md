# H030 hierarchy: repairable conditional space bound, no solver gain

2026-10-08. Opus proposed recursive extension; root raised interval-boundary
and leaf-cost objections. Native Astra independently checked the repair below.
Known public filter/recovery hierarchy is recorded in storage-priorart
disposition. This is paper scope clarification, not novelty or a numerical run.

Choose fixed odd r, D_l=2b_l+1, D_l=r*D_(l+1), D_0<q. Then integer intervals

    [-b_l,b_l] = disjoint union_(t=-(r-1)/2)^((r-1)/2)
                  (t*D_(l+1)+[-b_(l+1),b_(l+1)]).

Query full points R-t*D_(l+1)*G. Handle O by exact identity dispatch at every
level. A true parent has exactly one true child, and a false parent has none.
No modular alias occurs inside the full width D_0<q. Arbitrarily rounded
tables do not have this property: parent[-2,2], child[-1,1], centers -3,0,3
give a false parent3G with a true child (e.g. prime orderq>7). Final parent
range rejection does not undo that extra true child's resolution cost.

Given a fixed false root passing its own filter, seeds independent between
levels and fixed nonmember pass bound epsilon suffice. Full exploration gives
expected queries at depth j<=L at most r*(r*epsilon)^(j-1). No independence
between different queries within a level is needed. If r*epsilon<=1/2, their
sum<=2r. This counts queries, not their complete group/bit costs. Identity,
offset generation, hash/lookup, comparisons and traversal still count.

At an exact sorted leaf of size beta, comparisons contribute

    O(r*(r*epsilon)^(L-1)*log beta).

With L~log_r(log p+log b), epsilon=1/(2r) alone need not make this constant.
One repair uses an independently seeded exact chained hash table, including
its allocation/pointers and expected-cost assumptions. Another uses the sorted
leaf with epsilon<=1/r²; at that depth the extra decay controls its logarithmic
comparison cost. Do not silently choose the better of incompatible layouts.

For aligned widths, fixed r/epsilon and r^L>=w=log p+log b, internal filter
entries form a geometric series; exact leaf occupies O(beta*w)=O(b) bits.
Add seeds O(L log p), offsets, traversal and index metadata. These terms fit
O(b) in the intended regime log p=O(log b); do not assert that for arbitrary
tiny b versus huge p. Alignment changes finite parameters and must be charged.
The accepted partitioned filter supplies one concrete internal implementation
when2b_0<=p, using a constant number of field hashes per entry. Build work is
paid, and a successful path adds O(rL) queries plus final verification.

Disposition: the raw constant-false-work argument was incomplete but can be
repaired under explicit conditions. No15–17-bit constant, cache price, overall
rho advantage or lower-bound contradiction follows. This is a competent known-
class comparator, not a reason to build another generic engine or run a sweep.
No numerical test admitted; C2 remains the leading active experiment candidate.
