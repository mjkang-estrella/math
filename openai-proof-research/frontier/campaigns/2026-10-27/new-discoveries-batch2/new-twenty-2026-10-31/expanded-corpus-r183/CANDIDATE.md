# r183 candidate audit

No candidate is proposed for campaign acceptance. No Lean endpoint is claimed and no dummy Lean packet is supplied. Two complete ordinary arguments were found, but both run directly into the binding exclusion of short bridges from classical constructions/theorems. Root alone adjudicates credit. The third sustained route, 346742, remains unresolved after exact computation.

## 345906 — ordinary proof, very high routine-bridge risk

Target: Mammez, arXiv:2003.09142v3, Conjecture 17 (journal Conjecture 3.15): for every positive n,p, the degree-n elements u satisfying u^p=0 in the C9 weak shuffle algebra are zero. The ground field has characteristic zero. The source verifies all p for n<=3 and p=2 through n=7. The source has C9=(1,0,1,1,1,1). In particular, equal heads have both shuffle branches; unequal heads allow only the a-headed branch.

Here is a full ordinary argument, depending on the classical shuffle polynomial theorem. It proves a stronger statement: the whole C9 algebra has no zero divisors.

Write every word uniquely as a^i (b a^s1)...(b a^sr), with i,sj nonnegative integers. Let Sh_K(N) be the ordinary shuffle algebra on the alphabet of nonnegative integers. Define the K-linear map

    Phi(a^i (b a^s1)...(b a^sr)) = (t^i/i!) tensor [s1,...,sr]

into K[t] tensor Sh_K(N). It is a vector-space isomorphism, since factorials are invertible and both displayed families are bases.

For words a^i U and a^j V whose U,V are empty or begin with b, the initial a's are consumed before any b: at unequal heads only an a can be taken, and at equal a heads either branch is available. The number of ways to consume them is binomial(i+j,i). After this, when both inputs begin with b, either b may be selected. Once selected, every a immediately following that b must be consumed before another b can be selected, because the other input still begins with b. Thus each entire block b a^s is selected as a unit. Continuing recursively shows that the block lists are shuffled in the ordinary sense, with multiplicity one per interleaving. This is also an induction on the number of remaining blocks; the empty-list cases give the unit. Therefore

    (a^i U) star_9 (a^j V)
      = binomial(i+j,i) a^(i+j) decode(blocks(U) shuffle blocks(V)).

This identity includes the cases of empty U or V and extends bilinearly. Since binomial(i+j,i)/(i+j)! = 1/(i!j!), Phi respects multiplication and the unit.

The classical Radford shuffle theorem says that in characteristic zero the ordinary shuffle algebra is a polynomial algebra on its Lyndon words. A primary proof and its triangular integral basis are in Melancon–Reutenauer (1989), section 4, pp. 589–590, downloaded as sources/radford1989.pdf. Its rational theorem and integral triangular basis extend by scalar extension to any characteristic-zero field. Every element uses finitely many alphabet symbols, so passage to the countable alphabet causes no gap. Consequently the target algebra is a polynomial algebra K[t,L], hence an integral domain. If u^p=0 and p>=1, then u=0. This gives precisely the source's universal vanishing-kernel claim, with no homogeneity restriction needed.

Validation: the exact integer coefficient identity was checked on all 3969 ordered word pairs with each length at most 5 (scripts/block_identity.py). The source's sufficient strict leading-square criterion was checked on every pair through length 14 (scripts/shuffle.c, full logs and capped receipts). At length 14 this covers 16384 words and 134209536 distinct unordered pairs. These diagnostics are not Lean proofs.

Credit objection: after the elementary block recoding, all remaining mathematics is the classical polynomial structure of a shuffle algebra. The source already prints the C9 recursion, initial-a rule and block-run calculations (pp. 13–15). This is the short classical/source-ingredient bridge profile explicitly excluded by the brief. No assertion of worldwide novelty is made. The live Omega proof from the same source, WeakShuffleNormalization.result, is about normalization of coefficient systems; its claim/result and normalization construction were inspected and do not themselves assert reducedness. This distinction does not rescue substantive credit.

Lean cost if root independently elects to pursue: literal definitions of C9 multiplication on finitely supported words, the block isomorphism, and a formal shuffle reducedness theorem are all needed. Merely certifying finite maximal terms or declaring an abstract integral-domain structure would be a surrogate. No Lean formalization was started because this route does not survive the binding credit screen.

## 345919 — complete DFS proof, routine classical construction

Use a depth-first spanning forest. Orient every tree edge away from its root. Each non-tree edge of an undirected graph joins a descendant to an ancestor; orient it from descendant to ancestor. Its fundamental cycle consists of the directed tree path from ancestor to descendant followed by this edge. Thus every fundamental cycle is directed. The corresponding 0/1 circulation vectors are in ker(D*), the source's representative of H^1 (section 1), and form a basis: each has exactly one non-tree-edge coordinate, unique to it; there are m-n+c such vectors. Alternatively subtract the combination matching all non-tree coordinates from any circulation; a circulation supported on a forest is zero, by deleting leaves. This proves spanning as well as independence, including disconnected graphs and graphs with bridges. The source uses finite simple graphs; no multigraph convention is exploited.

All labelled simple graphs on orders 1 through 6 were enumerated (33867 graphs in total), checking the directed fundamental cycles and m-n+c count. The argument is a direct use of the classical DFS fundamental-cycle construction and has essentially no new mathematical content. It is therefore not a qualifying discovery under this brief. No Lean work was spent on it.

## 346742 — unresolved, no candidate

The correct poset is V times [n]. Promotion is the Bender–Knuth product from section 4.1 of Hopkins's survey, and has order dividing 6n. The polynomial's nonnegative integral coefficients are already proved by Gatzweiler–Krattenthaler, arXiv:2502.06032, Corollary 10. The full cyclic-sieving assertion remains beyond this pass.

Exact orbit enumeration was carried out at n=5,6,7 in Python. A separate C implementation using a dynamic-programming rank and a bitset agreed with the Python orbit histogram at n=7, then enumerated all 315031552 linear extensions at n=8. The n=8 histogram is 112 orbits of length 16 and 6563120 of length 48. The sum of orbit sizes is the exact product-formula cardinality. The polynomial reduced modulo q^(6n)-1 agrees coefficientwise with the orbit-character polynomial, at every tested n. The coefficient identity is exact, not floating-point evaluation at roots of unity.

No explicit verified range was found in the inspected Conjecture 6.2 discussion of Hopkins–Rubey's primary paper; this is not claimed as a first computation at these sizes. The source's web rotation theorem controls the order but does not supply the fixed-point counts. The remaining lemma is a uniform enumeration of rotationally fixed coloured Kreweras webs/linear extensions for each divisor of 6n. Guessing the observed orbit counts or certifying n=8 cannot replace that lemma. A January 2026 primary seminar abstract reports ongoing Gatzweiler–Krattenthaler work, so this route also has material unpublished-prior-work risk.
