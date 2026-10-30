# Fresh directed Toeplitz Hamiltonicity: unresolved

## Source and selection

Primary: Shabnam Malik and Ahmad Mahmood Qureshi, *Hamiltonicity in directed Toeplitz graphs with s1=1 and s2=3*, Discrete Mathematics Letters 16 (2025), 35–42, DOI 10.47443/dml.2025.109. Published online 17 September 2025. Publisher PDF retrieved 2026-10-30T00:46:34.164431+00:00, SHA256 d2987b614fb057b10c4f36d48d7db2aa248fac85658e00f4e575e88f6ae0b37c. Its introduction imposes n>max(sp,tq). Here vertices are 1,...,n and directed edges have differences +1,+3,+7,-t. This standing order restriction is essential; small n<=t are not counterexamples to the conjecture.

Conjecture 5.1 on journal p41 asks, for **every even integer t>=16**, (i) Hamiltonicity for **every admissible n=1,2 mod4**, and (ii) when **t=2 mod4**, Hamiltonicity for **every admissible n=3 mod4**. Both branches remain the target. Source Theorem 5.2 treats n=0 mod4; Theorem 5.3 treats n=3 mod4 when t=0 mod4. Those are not new targets. Theorem 5.1 treats the excluded n=t+2 when t=0 mod4.

The predecessor is Malik–Ramezani, J. Prime Research Math. 20(2) (2024), 64–76. Its p76 conjecture asks all n except t+2 for t=0 mod4 and all n for t=2 mod4. Actual original bytes, Section 3 and the final conjecture were checked; the selected 2025 source retains the unsolved branches rather than answering them.

Three leads were considered: Kurşungöz 367260/arXiv2502.17117 was rejected as an old r40 question after reopening original SUMMARY/discovery (r92 also records it); Brenner–Fink–Hoang–Merino–Pilaud 2502.09968 was only an abstract-level lead, whose stated matching asymptotic is already proved and whose symmetric-chain direction is not selected; the third lead is the precise published Toeplitz conjecture above. No proof work or source downloads on the first two. Exact title/author/ID/alias screening preceded the Toeplitz download. The retained r150 original-role index was refreshed for changed/new records, not replaced by a generated-echo inventory. See history-receipt.json for all 1,487 paths/hashes and 24 deltas. Scoped nonmatches are not global novelty evidence.

## Exact reformulation

Delete all backward edges of a directed Hamilton cycle. What remains is a partition into increasing directed paths, each with successive differences in {1,3,7}. If the backward heads form S, the path starts are exactly S and their ends are exactly S+t. Thus 1 belongs to S and n-t belongs to S: vertex 1 has no increasing incoming edge and vertex n has no increasing outgoing edge. Label paths by their starts. Their endpoint-to-head links must form **one** permutation cycle, not an arbitrary permutation. Conversely, any such increasing path partition with one-cycle links closes to a Hamilton cycle by adding the -t edges. This proves the equivalence, including the connectivity condition which a mere cycle cover loses.

If there are r backward edges and a,b forward edges of lengths 3,7 respectively, summing increments around the cycle gives

    n + 2a + 6b = r(t+1).

Indeed the n-r forward edges contribute (n-r)+2a+6b, and the backwards contribute -rt. In particular, for even t, r and n have the same parity. If r=1, the single increasing path must visit all vertices in increasing order, so all its steps are 1 and n=t+1. These are universal helper facts, not conjecture resolutions.

## Complete two-backward-edge analysis

For even t and even n with t<n<=2t, a Hamilton cycle using exactly two backwards edges exists **if and only if n=0 mod4**.

Proof. Put s=n-t. The heads are necessarily {1,s} and the ends {t+1,n}. Connectivity forces the path A starting at 1 to end at n and the path B starting at s to end at t+1: the other pairing closes two separate cycles. Color each vertex by its path. Before s every color is A; after t+1 every color is A. Every intervening maximal monochromatic run has length 2 or 6, because the other path jumps over it, and an increasing edge can skip only 0,2 or6 vertices. In particular the color word on [s,t+1] starts and ends B and has an odd number of runs. Each run has length 2 modulo4. Consequently t-s+2=2 modulo4. Since t-s+2=2t-n+2 and t is even, n=0 modulo4.

Conversely, suppose n=0 mod4. Then s is even, 2<=s<=t, and L=t-s+2 is positive and 2 modulo4. Color 1,...,s-1 by A, color [s,t+1] by consecutive length-two runs B,A,B,...,B (there are L/2 odd runs), and color t+2,...,n by A. Consecutive vertices of either color differ by 1 or3. A starts at 1 and ends at n; B starts at s and ends at t+1. Add n->s and t+1->1. The result is a single Hamilton cycle. QED.

This is a complete bridge for the known source subcase, not an exclusion of the full conjecture. It shows why a two-path argument cannot prove its n=2 mod4 branch. Parity forces at least four backward edges there. No new discovery credit is requested for this helper or classical/source construction.

## Stronger route and exact finite evidence

For prescribed S, scanning vertices in numerical order gives a finite-state search for the increasing paths. The state records each path's distance from its last vertex, its end-to-head link if ended, and the current vertex. A path can continue exactly at distances 1,3,7; an unended distance exceeding 7 is impossible. A start must open its own new label. An end must close its label and record the appropriate -t target. At termination the links must form a single cycle. These conditions prove soundness and completeness for the **prescribed S**; they do not guarantee any acceptable S exists. Memoization discards only equal future states.

checks.py tries S={1,...,r-1,n-t}, r=3 for odd n and r=4 for even n, throughout even t=16,...,48, t<n<=2t+1, omitting s<r and restricting to the selected branches. It yields 174 verified cycles and many failures. Those failures are failures of that exact ansatz, not non-Hamiltonicity.

The first expanded exploration allowed interior heads among 2,...,8, still with r=3 for odd n. Its failures are preserved/reproduced in explore-initial.json. The next trial incorrectly chose five for every n=1 mod4 and three for n=3 mod4, independently of t; its 56 records and 11 failed cases remain in explore.json. The corrected trial uses r=3 when n-t=3 mod4 and r=5 when n-t=1 mod4, with r=4 for n even. The choice is an experimental construction rule, **not a proved invariant or necessary minimum**. It verifies 323 cases, all with distinct complete vertex lists and exact allowed increments, in explore-corrected.json; total 88,178 visited states. No uniform pumping argument has been supplied.

At (n,t)=(21,16), the three possible three-head sets {1,a,5}, a=2,3,4, all fail. A five-head cycle exists. The odd parity condition and r=1 characterization prove that this example really requires at least five backwards edges. It satisfies the conjecture and is only a construction obstruction. control.py compares the path-cover solver with an independent literal directed-cycle DFS on small graphs, for every prescribed head set in the stated control range. No floating-point arithmetic or probabilistic evidence enters these checks.

## Why the full proof is missing

The source's Remark 2.1 replaces an edge (n-2,n-1) by (n-2,n+1,n+2,...,n+t-1,n-1), increasing order by t-1. Its jumps are +3, then +1, then -t; the new path includes the new distinguished edge (n+t-3,n+t-2). Thus the extension is rigorous but requires that distinguished edge in the old cycle. Arbitrary finite witnesses above do not certify it. Even a uniform family of lower-strip witnesses would need this property, or another verified extension, with all residue seeds covered. The nonuniform original source patterns do not supply the missing new branches. Neither a parameter slice nor finite witnesses constitute a resolution.

A plausible route is a finite set of path-color templates admitting simultaneous changes of t and n. But an insertion must preserve all backward lengths, every forward gap, and the single-cycle endpoint permutation. Merely repeating a short color word can change the endpoint permutation or create a gap of length 5, which is forbidden. No closure lemma for such templates was proved. Full all-t seed existence and an all-n extension remain the precise gaps.

## Current public-body screen and eligibility

Inherited fixed registry observations: Omega 490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c; OpenAI 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. Two inherited comparisons aa026->a19a and a19a->490f each stop at 300 changed paths. They cannot establish absence. Cached complete named tree scopes and the fixed Problems scope were screened without a global output cutoff. Source-facing actual bodies were retrieved early: Omega FiskToeplitzRefutation is about polynomial minors; Toeplitz/FactorizationRefutation is about complex matrix factor counts (actual claim and result read); the Malik problem concerns a different author's falling-factorial moment bound. None is this graph statement. The current public graph-theory proof verification SUMMARY was also retrieved and read for this family; no matching title/author/claim occurs there. That file is a bounded secondary screen, not an audit of all public proof bodies. Other path hits and semantic/history gaps remain; no full registry clearance is claimed.

Public title/author/claim queries located the source and its predecessor, not a demonstrated full resolution in searched scope. Search results are not proof of absence. The strongest eligibility objection to a future candidate would be a routine extension of the existing source's explicit path constructions or an already public general Toeplitz Hamiltonicity theorem. This lane establishes neither full resolution nor a complete prior subsumption bridge. No independent eligibility review has occurred. No Lean or manuscript investment is authorized by these partial results.
