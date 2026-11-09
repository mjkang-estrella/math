# Statement correspondence

Source: Defant and Propp, Quantifying Noninvertibility in Discrete Dynamical Systems, arXiv:2002.07144v4, Definition 1.1, section 2.3, inequality (1), Conjecture 4.4. Cached source text was read. The EJC numbering is Conjecture 23; the conjecture is numbered in v3/v4, not v1/v2.

The literal conjecture says: “The value of the limit lim deg(s : S_n → S_n)^{1/n} lies in the interval (1.68, 1.73).” The frozen Conj uses an existential real limit in that open interval. deg is P/n!, where P counts every equal-output pair of permutation words, matching the average fibre multiplicity in Definition 1.1. The frozen source map is precisely s(LmR)=s(L)s(R)m at the largest label; the supplied source example 416352 maps to 143256. Its zero-based labels are related to the source's positive labels by proved increasing relabelling.

Round3.doublingInjection_proved is inequality (1) at m=n=a+1 in integer form: choose(2a,a) P(a)^2 ≤ P(2a+1). Unlike the round-2 fixed-label inequality, its domain includes all a-element label subsets. Round3.doubling_proved is its factorial conversion to the literal degree. Round3.rootSplit_proved is the review's elementary lower inequality, including both cross-end families; it is not quoted as a source theorem.

The Round3 source endpoints mathdb_345545, limit_ge, nonvacuity and subsequence_companion still have AdditiveRecursion as an explicit hypothesis. They use the literal source definitions and explicit subsequence index(130,k)+1=131*2^k. They are not unconditional resolutions. AdditiveRecursion is stated for literal tuple counts, not a numerical recurrence table asserted to count P.

The MathDB maximum-fibre paraphrase is a distinct reading. Round3.mathdb_345545_max and max_companion re-export the already unconditional frozen proofs for ConjMax and maxRoots. This reading earns no credit on its own.

# Round 4 extension

The source map, literal permutation-word domain, pair count, real degree, source conjecture and maximum-fibre reading are unchanged. All 66 round-3 source files are byte-identical. The new modules add proofs about the same literal tuple definitions; they introduce no alternative degree or restricted permutation family.

StackSort.Round4.mathdb_345545, limit_ge, nonvacuity and subsequence_companion remain CONDITIONAL on both StackSort.Round3.CommonCutCount and StackSort.Round3.MaximumFinalCount. These are equivalent jointly to the inherited AdditiveRecursion. The dyadic subsequence is still index(130,k), with index(130,k)+1=131*2^k. The maximum-fibre refutation and max_companion remain unconditional.

The new FinalBlock theorem uses the last proper common output boundary, matching the frozen correction's arbitrary-prefix / irreducible-final-block convention. The literal labelled family theorems include surjectivity, so their cardinalities refer to all tuples over the prescribed labels. Tuple deletion is proved at the output and arity levels only. No missing finite counting bijection is claimed to follow merely from these output identities.
