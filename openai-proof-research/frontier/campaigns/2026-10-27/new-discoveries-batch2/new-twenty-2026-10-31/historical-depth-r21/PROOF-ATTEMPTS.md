# Second-pass mathematical attempts (zero proposed credit)

These are two sustained routes with explicit unresolved lemmas, not resolutions. The 40 reservation IDs were already literal-reviewed. Raw bytes, literal quantifiers, old reasons and primary-body depth are separate fields in results.json. Neither a table nor a finite search is a Lean endpoint.

## Rank 1: 348873 — folded-cube augmentation

Read Lu–Ye arXiv:2012.00396v2 definitions on pp1–3, Conjecture7.1/Table5 p14, and the proof bodies of Lemmas4.1–4.6 and Theorem4.7 (pp7–9). Fn means antipodal quotient of Qn, with 2^(n-1) vertices, not Qn with added antipodal edges. Its distance is min(Hamming(u,v),n-Hamming(u,v)). A resolving set has injective distance vectors. A doubly resolving set has injective vectors modulo addition of a constant vector. This checks the semantic bridge underlying the diagnostics directly.

The known odd-n equality beta(Fn)=beta(Qn) does not yield the desired double-resolving bound: the proof distinguishes equality of two distance vectors, not a nonzero constant difference. The published phi bounds add (n+1)/2 or n-1 vertices. They therefore do not settle the requested +1. The paper's refutation of its Conjecture1.1 is a different claim; it is not a refutation of Conjecture7.1.

First mechanism: choose an optimal resolving set S, translate a member to 0, collect all distinct pairs (u,v) whose distance difference is a nonzero constant c on S. One new vertex t works exactly when d(u,t)-d(v,t) != c for every collected pair. This is an exact hitting problem; checking only pairwise resolving is insufficient. We tested this criterion rather than a surrogate dimension bound.

Second mechanism: can a neighbor of 0 always be chosen as t? For n=2k+1 choose representatives of weight at most k. If u has weight r then

    d(u,e_i)-d(u,0) = -1 if u_i=1;
                         +1 if u_i=0 and r<k;
                          0 if u_i=0 and r=k.

This follows directly by toggling one bit and applying the minimum distance formula. For an offset pair with |u|=r, |v|=r+1 and c=-1, if r+1<k then neighbor e_i breaks the constant offset exactly on supp(u) symmetric-difference supp(v). If r=k-1, it breaks the offset except when both bits are 1. This gives a concrete finite-set intersection formulation and treats the folding boundary, which a hypercube-only argument misses.

Exact exhaustive check at n=5: all 455 size4 sets containing0; 20 resolve, all20 fail to double-resolve, and each admits a neighbor augmentation. Deterministic sample at n=7: 5000 size6 sets containing0; 1098 resolve, 486 fail to double-resolve, every one admits a neighbor augmentation. Maximum observed offset magnitude1 and at most3 bad pairs. These are evidence only; optimality at n=7 is inherited from the source table, not established by this sample. No size8 resolving set was found in the small random n=6 sample, so no conclusion on its augmentation is drawn.

**Unproved core:** for every n there exists an optimal S whose constant-offset bad pairs admit a common additional vertex. The stronger neighbor-intersection statement and the restriction |c|<=1 are not proved, even for all odd n. A family of individually nonempty good-neighbor sets need not have nonempty intersection. Even dimensions have an additional middle layer and cannot be inferred from the odd case. No Lean endpoint or novelty clearance. Formalization would require the antipodal quotient, actual graph-distance bridge, minima over finite vertex sets, and the uniform augmentation proof; finite diagnostics omit all of these proof obligations.

## Rank 2: 348788 — sublinear boundary cost for square reductions

Read Grytczuk–Stankiewicz arXiv:2011.12822v1 definitions and Conjecture2 (discussion p9), plus Theorems2,4,5 and their proofs. Read Alon–Bruck–Farnoud–Jain's actual Theorem9 proof in the retained author PDF pp4–5. Their f(n+m)<=f(n)+f(m)+2 proof reduces the two blocks separately; binary square-free reducts each have length<=3, so their concatenation has length<=6 and needs at most2 additional steps. Thus f+2 is subadditive. For k>=3 reduct lengths are unbounded. Theorem5 of the ternary paper gives finite connected components only in the UNDIRECTED reduction/duplication graph: its proof first duplicates to Si then reduces to Yi. That cannot be inserted into a directed reduction-length proof.

First attempted extension: retain the binary +2 boundary cost. Rejected by exact diagnostics: A=012, B=212012 are square-free but d(AB)=3. Second attempted extension: a fixed +3 cost. Also fails for A=0102, B=2021020102, with d(AB)=4. The memoized recurrence enumerates every contiguous square and recurses to strictly shorter words. All ternary words through length10 and all 199161 ordered square-free factor pairs with each factor length<=10 and total length<=18 were tested. This is exact finite arithmetic but is not formally certified; it proves no asymptotic statement. Full outputs retained.

A more useful target is a uniform logarithmic joining lemma: for fixed k, square-free A,B can be reduced to a square-free word in at most C_k log(|A|+|B|)+D_k steps. It would imply

    d_k(n+m) <= d_k(n)+d_k(m)+C_k log(n+m)+D_k.

Here is why that would suffice, rather than merely suggesting Fekete with an unbounded error. Partition a word into blocks of length m plus a remainder. Reduce each block, then merge in a balanced binary tree. At merge level j the blocks have length at most 2^j m (reductions only shorten), and there are at most N/2^j such merges among N blocks. The extra cost per original letter is bounded, in the large-N limit, by

    (1/m) sum_{j>=1} (C_k log(2^j m)+D_k)/2^j
      = (C_k(log m+2 log2)+D_k)/m.

For a non-power-of-two block count, first merge dyadic blocks; combining the at most log2 N leftover blocks costs O((log N)^2), negligible per letter. A remainder of length<m costs at most m-1 reductions. Therefore limsup d_k(n)/n is at most d_k(m)/m plus the displayed vanishing error. Taking m along a liminf sequence would prove convergence.

**Unproved core:** the logarithmic joining lemma itself. A reduction can cross the old boundary and create new squares; neither an internal reduction path nor the source's undirected connectivity proof controls the number of such later reductions. Tracking two square-free factors is not by itself a scale-decrease proof. A valid amortized argument would need to show geometric growth of deleted blocks or some comparable potential drop; none is established here. A logarithmic bound observed at short lengths is not that lemma. No generic-k proof, no full Lean endpoint and no new result proposed. Lean cost would include literal words/reductions/minimal directed distance plus the uniform joining and analytic-limit bridges. This route ranks behind folded cubes because even its decisive combinatorial lemma lacks a proof strategy that closes.

## Prior-art retirement: 348207

Read original arXiv:2010.03151v2 Definitions2.1–3.2, Lemma4.1 proof, phi definitions, entire Section7 proof and Conjecture8.1. The primary domain is 10 NOT DIVIDING n, not merely n!=10. Preserve the defective MathDB literal text, but use the primary domain. No credit for this repair.

Read Tsai's PUBLISHED Integers22(2022)#A77, Section9 pp19–21, and Theorem15 proof/Corollary4 pp16–17. Its n126 calculation uses 126=2*3^2*7, reverse621=3^3*23. The only nondegenerate characteristic solution gives I=I154-I3542. Corollary4 gives fundamental period3542, whereas the original constructed period is31878. Thus neither1 nor31878. This exactly refutes the intended dichotomy with a number in the primary domain. The published source explicitly identifies the old conjecture. This is known since2022, not new. Not all dependencies of Theorem14/Fourier theory were read; no claim of full independent proof audit. No formalization warranted.

## Prior-resolution gap: 342062

Read original arXiv:1903.03197v2 induced-matching definitions and Conjecture1, and the published 2023 AJC85(1)61–81 introduction plus its minimal-girth11 result/Corollary4.1. The published introduction explicitly says Finbow–Hartnell–Plummer settle the full girth11 conjecture (DAM321(2022)261–271, DOI10.1016/j.dam.2022.06.041). The publisher's publicly accessible introduction independently confirms this claim and supplies the same definitions. But the actual successor girth11 theorem and proof body were NOT obtained/read. Do not label this proof-body-confirmed. Retain a published-resolution lead / source gap, no new-investment priority, no novelty clearance. Minimal graph uniqueness alone still does not imply connected graph uniqueness; the old objection remains valid.
