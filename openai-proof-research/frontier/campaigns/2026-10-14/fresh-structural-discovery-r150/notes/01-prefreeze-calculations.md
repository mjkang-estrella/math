# Live feasibility calculations — no freeze

ONE selected family: arbitrary-degree connected switch mixing/sampling (Source131). Required r149 overlap reads are not further screens. The initial hope of an underexplored family was corrected by actual r30 and r139 body reads BEFORE mathematical development: they already own the full arbitrary-degree question and sharp local comparison. No relabeling of those targets or supporting results is proposed.

Exploratory scope retained: every n>=4 and every labeled degree sequence admitting a connected simple graph; the half-lazy uniform-four-vertex switch rejects disconnected outcomes. A uniform polynomial worst-start mixing bound is sought, with no leaf, density, regularity, or fixed-surplus restriction. Efficient exact sampling is a consequence to investigate, not a substitute nominee. No theorem is feasible/frozen yet.

## Prior operations credited

r30's deleted-union pair fibers, failure of matroid exchange, exponential rarity for degree3/degree1 tree sequences, and impossibility of a polynomial-max-fiber all-state retraction with leaves are read and credited. r139's sharp local Johnson deletion estimate, H_c<=L_c<=floor((n-1)^2/4)H_c/2, exact conditioned three-row description and seven-state triangle obstruction are read and credited. Their remaining global Poincare inequality is not new to r150.

All eight Source131 mathematical sections are now read in full, including row-count coupling, triple encoding, rank-one disjoint dependence, equality-indicator Gram comparison, global square identity, deterministic connectivity, multiplicity-two comparison and exact rare-mixture sampling. The entire bibliography was displayed. Pin and proofs stipulated true. No source truth audit.

FGMS Lemma1/Section3.1 cycle joining and reconstruction, including cases9/17/14/12 and Theorem2, were read in full after recovering a truncated first display. They pay a connected-state comparison for minimum degree>=2. CDGH Section4 chaining Lemmas4.1–4.2 read; remaining operative simulation/counting to be read. Forest/core route below is not justified by merely saying a tree component lacks a cycle edge.

## Exact 2-core/forest reduction

Let E=sum d_i/2 and ell=E-n+1. If ell=0 every connected realization is a tree, with classical Prufer count (n-2)!/prod(d_i-1)!. This pays tree sampling, not mixing of the specified switch chain and not the full variable-ell scope.

For ell>=1, a connected graph has a unique nonempty connected2-core C. Write k=|C|, m=n-k, H=G[C], s_i=deg_H(i)>=2. Then |E(H)|=k-1+ell and every outside component is a tree attached to exactly one core vertex. Orient these trees away from C. Their child counts are
 c_i=d_i-s_i (i in C), c_j=d_j-1 (j outside C).
They are nonnegative and sum c=m. Let A=sum_(i in C)c_i.

For m>=1, Pitman's classical rooted-forest polynomial gives the exact forest count
 F(C,s)=(m-1)! A / prod_v c_v!.
For m=0 the forest count is1 exactly when s=d. If m>0 and A=0 there is no such forest. The coefficient formula follows by extracting x^c from (sum_C x_i)(sum_V x_i)^(m-1). This identity and its operative primary proof were read before extended drafting; it is not claimed as new.

A stronger compatible consequence removes forest sampling as an exponential rejection obstacle. Uniformly assign to the m labeled nonroots a multiset of parent labels with multiplicities c_v, allowing loops/cycles initially. There are m!/prod c_v! such functions. Keep exactly those whose forward orbits reach C. They are precisely the oriented forests and acceptance probability is A/m>=1/m. Thus fixed C,s forest sampling is exact expected polynomial, by unbiased multiset permutation and cycle testing. This is a direct classical coefficient consequence, not substantial evidence.

For fixed C,s, core and forest are independent under the uniform conditional law. The unrestricted core has minimum degree>=2, so source exact sampling followed by connected-core rejection uses expected at most2k trials by FGMS's fiber bound. Variable forest degrees do not invalidate this fixed-fiber composition.

The macrostate measure is proportional to N_conn(C,s) F(C,s), where N_conn counts connected core realizations. Replacing N_conn by N_all yields a distribution whose subsequent connected-core rejection accepts with probability at least1/(2n), uniformly even after mixing over C,s. This is stronger than the original all-graph rejection route: forests have already been integrated and cyclic cores retain the paid polynomial connected fraction. What is not yet paid is drawing the macrostate with those weights, or proving controlled transitions between such macrostates for the specified switch chain. An exponential number of macrostates is not itself an impossibility argument.

## Stronger primary alternatives being checked

Bhamidi–Sen1608.07153v3 Section3 constructs a tilted plane tree plus admissible leaf pairs, preserving graph multiplicity. Its explicit fixed-complexity polynomial discussion does not by itself furnish a uniform polynomial when ell grows. Horvat–Modes2009.03747v2 Section4 is an exact BIASED sampler with computable weights; its title does not assert uniform polynomial sampling. Neither operation is dismissed: their full relevant construction/proof interfaces are being read and compared.
