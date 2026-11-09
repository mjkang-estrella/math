# Statement correspondence

Frozen definitions and source correspondence are inherited byte-identically from round 1; see the original packet with SHA256 67a3893f3a08616fe9d4480ce28b166cbf410df5d9edf4ca5ccb054340253dde.

Source: Defant and Propp, Quantifying Noninvertibility in Discrete Dynamical Systems, arXiv:2002.07144v4, Definition 1.1, Section 2.3, Theorem 2.5 and Conjecture 4.4. The supplied cached text was read. The conjecture appears in v3/v4 and as Conjecture 23 in EJC 27(3), P3.51; it is absent as a numbered conjecture in v1/v2.

The literal source sentence is: “The value of the limit lim deg(s : S_n → S_n)^{1/n} lies in the interval (1.68, 1.73).” StackSort.Conj is its existential limit formulation. StackSort.deg is the Definition 1.1 average multiplicity, with literal P counting equal-output pairs over all permutation words. The map is precisely s(LmR)=s(L)s(R)m at the maximum m, with the supplied example s(416352)=143256. Values 0..n-1 replace 1..n by the proved increasing-relabelling equivariance.

The source inequality (1) is d_(m-1)d_(n-1)≤(m+n-1)d_(m+n-1). The integer target DoublingInjection is exactly its m=n=a+1 case. fixed_split_bound proves the fixed-label-subset subinjection only. doubling_of_injection proves the factorial conversion only. Neither is described as the full source inequality.

RootSplit is the review's elementary lower bound, not a quotation from the source. four_mul_P_le verifies its four boundary/cross families. G uses its exact remaining interior sum and the frozen seeds. G_130_eq_lower130 links the literal round-1 constant to that recursion without assuming anything about P. G_le_P needs both RootSplit and ExactSeeds20.

The MathDB paraphrase calls deg the “maximum fiber size.” Frozen ConjMax and mathdb_345545_max address that distinct reading unconditionally, as does max_companion. This earns no credit by itself. The new Inj2 source endpoints carry DoublingInjection, RootSplit and ExactSeeds20 explicitly, and include the limit bound and frequent-event companion with explicit subsequence index(130,k)+1=131*2^k. Limit existence is not asserted; the companion rules out a merely vacuous refutation mechanism.
