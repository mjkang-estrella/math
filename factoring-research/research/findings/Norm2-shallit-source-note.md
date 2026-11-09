# Norm2 — bounded follow-up to Shallit's cited sum-of-squares method

2026-10-08. **Source limitation retained; no new theorem or factoring
improvement accepted.** This parent source check is independent of W004's
live packet review and changes none of its frozen inputs or algorithms.

The accepted norm-gate review left open the different method referenced on
page 7 of Shallit's Pollard exposition. Its bibliography identifies the source
precisely as J. Shallit, *Random polynomial time algorithms for sums of squares*,
University of Chicago, Department of Computer Science, Technical Report
85-001, January 1985. The Chicago
[historical report index](https://newtraell.cs.uchicago.edu/files/Technical_Reports_1983-1995.html)
also lists this title and number in the search engine's indexed result.
The underlying index could not be downloaded here; no full TR85-001 text
was obtained.

Page 7 distinguishes two matters: representing a suitable prime as two
squares, and obtaining a modular solution without an unproved fast search
for that prime in a prescribed progression. Its reference to a different
method is a lead. It does not supply that method's input domain, success law,
bit-cost proof or repeated-prime-power handling in the inspected passage.
The already accepted qualification therefore remains in force.

The author's [publication list](https://cs.uwaterloo.ca/~shallit/papers.html)
also links Michael O. Rabin and Jeffrey O. Shallit, *Randomized algorithms in
number theory*, CPAM 39 (1986), S239–S256,
[DOI 10.1002/cpa.3160390713](https://doi.org/10.1002/cpa.3160390713).
The publisher's retrieved page contains bibliographic information and
references to the 1984 exposition and TR85-001, but no pertinent full theorem
or algorithm. This establishes a related primary-source lead, not equivalence
of the reports or verification of a Norm2 complexity guarantee.

Five focused queries were used. The author bibliography and directory HTML
were archived. The Chicago index gave a web-fetch 502; direct HTTPS and one
ordinary HTTP attempt failed certificate verification. TLS verification was
not disabled. The Wiley PDF endpoint returned HTTP403 on direct retrieval.
The [web ledger](Norm2-shallit-source/web-ledger.json),
[direct-access ledger](Norm2-shallit-source/access.json) and
[legacy-index attempt](Norm2-shallit-source/legacy-index-access.json) preserve
these scopes and failures. This was not a new AEM search, and none of its
previously failed endpoints was retried.

No abstract, citation or missing manuscript is treated as a checked algorithm.
The accepted fully specified Norm2 reference still costs O(N n^2) time and
O(N n) working bits on fixed multitapes. A faster contract remains unverified
in this lab; this is not evidence that one does not exist. Even verification
of such a known subroutine would not prove useful mixed-target generation
or a complete factoring speedup for W004.

This bounded source attempt is complete without resolving the source gate.
Do not automatically repeat the same failed retrievals. Resume W004's live
independent review from its saved handle. No mathematical execution, numerical
example, experiment, implementation or Lean work occurred in this follow-up.
