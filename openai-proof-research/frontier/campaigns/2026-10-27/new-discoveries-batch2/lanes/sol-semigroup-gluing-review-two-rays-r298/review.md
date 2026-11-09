# Independent ordinary review of r297 exclusions

Verdict: mathematical PASS for both 4a=3b and4a=3d, within a>=12,a<b<d<2a,gcd(a,b,d)=1. No repair required. Author code was read as an input, but check.py imports or executes none of it and computes actual membership by the independent recurrence v[n]=OR(v[n-g]). Earlier AP/r296 universal arguments were not re-audited.

Every integer has a unique jm+kz representation with 0<=j<k; m-coefficient reduction adds a nonnegative multiple of m to <3,4>, which is closed because m>=13 belongs to it. This proves the claimed equivalence and not just one inclusion. Missing z values are5,2,1 and all negatives; reflecting about (k-1)m+5k gives exactly offsets im+kh, h in <3,4>. The Apéry values jm+k{0,4,8} are distinct modulo3k and minimal by subtraction of3k. The rank formula counts every nonnegative member once and subtracts0. Independent checks cover complete membership, every positive gap, full Apéry tables and ranks, not only obstruction windows.

On 4a=3b, m>4k, so the first offsets are0,3k,4k. F and F-3k have two-member neighborhoods; k>=4 ensures spacing and positivity. Exactly3k-1 members lie between them. Since this is2 modulo3, both boundary ranks cannot be0. The isolated-gap argument yields the claimed successive aligned failure.

On 4a=3d, m=3k+e,0<e<k. If e>=3 the same two boundaries work. If e=1 or2, offsets through4k are exactly0,3k,m,4k, and the next offset is6k. F-4k has upper distance k-e and lower distance2k. For e=1, k-e>=3. For e=2, gcd(k,m)=gcd(k,2)=1 makes k odd and at least5, again k-e>=3. The lower gap and both lower neighbors are positive. The interval to F contains exactly three gaps including its lower endpoint, giving4k-3 members. Initial distinctness forces k!=0 modulo3 (3k,4k,m are the first three members). Thus the boundary ranks cannot both vanish. The initial-repeat case supplies a rank1 witness directly. This also checks the smallest k and e edge cases.

All32 source equations were independently regenerated from frozen page2, with source q>=1 except H5 q>=2, exact rational roots, integral/domain/multiplicity/ordering/primitivity tests. None persists or has an admissible retained triple. checks.json is the machine-readable table. No reliance on an author's finite parameter assertion is needed for the universal proof.

The new 3a=2d theorem in discovery.md is this reviewer's additional deduction; it has not received a separate independent ordinary reviewer. Root alone may adopt it. Nothing here changes acceptance,9/39/next40, shared files, Lean or manuscripts.
