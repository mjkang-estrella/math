# 348407: bounded comparison, stopped for source-subsumption

Primary: dela Cruz–Kurz, arXiv:2010.10762v1 (21 October 2020), Conjecture 4.10; retained HTML identifies this version. Retrieved 2026-10-31 UTC, exact bytes and derivative bindings in source-provenance.json and derivative-bindings.json. Selected passages only; no whole-paper or full dependency audit.

For every t>=2 and k, the conjecture says that a nonnegative vector of total mass k supported equally on a projective basis maximizes the displayed homogeneous polynomial F. There is also an integer balanced-support assertion. The exact literal formula is retained in dispositions.json and the primary passage is in projective.txt around lines1170–1192.

An ordered independent t-tuple can be chosen in product(i=0..t-1)(2^t-2^i) ways: at step i its span has 2^i vectors. Its sum is nonzero and distinct from each chosen vector for t>=2. Each projective circuit of size t+1 has (t+1)! such ordered bases. Thus uniform weights k/(2^t-1) give

F = product(i=0..t-1)(2^t-2^i) / (t+1)! * (k/(2^t-1))^(t+1).

On the proposed support, the only contributing circuit is the full projective basis, so F=(k/(t+1))^(t+1). Exact rational arithmetic executed for t=2..12 gives first strict improvement within that bounded range at t=7. This does not assert minimal dimension among arbitrary supports. At k=1 the ratio is 536836552261632/532875860165503 >1. An integral witness uses all127 nonzero binary7-vectors with weight8, total1016, versus eight support weights127; exact integer values are in bounded-checks.json. No large enumeration or optimizer was run. A certificate needs only span counting and one integer inequality; formal burden is finite-vector-space counting plus polynomial support combinatorics, not127-variable optimization.

The decisive objection is source-internal, stronger than method similarity. Section2 of the same source prints the random-coding lower bound attributed to Ashikhmin–Barg1998. Take q=2,n=k+t and only its j=t+1 term. For fixed t, its leading coefficient in k is

L_t = product(j=1..t)(1-2^(-j)) / (2^t*(t+1)!).

At t=8, exact computation gives L_8 / (1/9^9) = 2722614920369505/2251799813685248 >1. Proposition4.9 and Conjecture4.10 imply instead M_2(k+8,k)=k^9/9^9+O(k^8). These are incompatible for sufficiently large k. All omitted lower-bound summands are nonnegative through j=t+1; no cancellation is used. The source's preceding general leading-term upper framework is Proposition4.9, whose local proof was read. Its coding-theoretic dependencies are accepted as printed here, not independently audited.

This is already a direct source-printed bound defeating the general conjectured consequence. A smaller explicit optimizer witness does not create a separate eligible discovery under the task's exclusion rules. Therefore no proposal, no manuscript/formal investment, no credit. This is a screening exclusion risk, not a root adjudication of historical priority.

Closest retrieved prior body: arXiv:1201.6043v2, Section2 known-bound discussion. Its inspected random-coding discussion concerns fixed-rate asymptotics; it does not supply the exact fixed-codimension calculation above. The exact printed bound's original1998 proof was not fetched or audited. A bounded public search located the original institutional manuscript and older coding papers, but no successor-body clearance. Search results and abstracts do not certify absence of prior counterexamples. No current proof registry was available. Those obligations remain HOLD even though the printed-bound objection suffices to stop this route.
