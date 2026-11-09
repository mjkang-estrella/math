# Proof content and remaining work

The finite domain is the finset of all permutations of the list range n. `mem_words` identifies this domain with the usual list-permutation predicate, and `words_card` gives n!. Thus no restriction to a special family enters the source-reading count. Using values 0 through n−1 instead of 1 through n is justified by the proved order-equivariance.

`sortFuel` is structurally fuelled max-split sorting. `fuel_independent` proves independence whenever both fuels exceed the input length. `s_split` is the exact source equation, and `s_perm` proves the output stays in the literal domain. `s_map_orderEmbedding` proves standardisation. The result is a map on one-line permutation words, as explicitly permitted in TASK.txt, without converting to Equiv.Perm.

`P_eq_sum` and `fibre_square_identity` prove both source formulas. Division by n! yields the literal Definition 1.1 degree.

For a nonnegative sequence d satisfying d_n² ≤ (2n+1)d_(2n+1), `iteration` proves

    4 (a_k+1) c^(2^k) ≤ d_(a_k),

provided 4(a+1)c ≤ d_a, where a_0=a and a_(k+1)=2a_k+1. It uses only polynomial inequalities. Taking c=1.73^(a+1) and a>0 gives d_(a_k)>1.73^(a_k), hence a strict root bound. The index is strictly increasing. `ge_of_tendsto` on this subsequence gives the lower limit bound; its unboundedness gives the frequent-event companion. No existence theorem is assumed or claimed.

`certificate130` is closed natural arithmetic: 4·131·130!·173^131 < lower130·100^131. `base130_of_lower` derives the needed real bound from `Lower130`. The certificate does not prove `Lower130`.

For maximum fibres, family 0={[]} and family(n+1) consists of prepending or appending n. Every word is a permutation word and sorts to range(n+1). For n>0 the halves are disjoint, since the old words do not contain n and are nonempty. Their cardinalities double, giving family(n+1).card=2^n. The fibre embeds into the finset defining the maximum. A rational induction proves 1.73^n < 2^(n−1) for n≥5. This yields `max_companion`, `max_limit_ge`, and `mathdb_345545_max` without hypotheses.

Next round:

1. Use the proved standardisation and split equation to build the labelled subset doubling injection, prove `DoublingInjection`, then cancel factorials to obtain `Doubling`.
2. Build the root-split injection, prove `RootSplit`, define the lower table as a structural fold or literal rows with checks, and prove monotonic domination from exact seeds. Do not assume that the untrusted lower130 literal has this meaning.
3. Define tuples of nonempty words and their literal counts. Prove T1 common-cut decomposition and shuffle count, T2 maximum at the end of an irreducible output, T3 maximum deletion with weights 1,2,1, and T4 additive identities. Prove exact seeds through 20 by row checks, obtaining `ExactSeeds20`.
4. Discharge `Lower130` from steps 2–3. The current source-reading endpoint arguments then disappear. Optimize literal regressions for P 5 and P 6 using a checked table of sorted outputs rather than repeatedly sorting every pair.
5. Repeat strict fresh extraction, checker and closure audit after those proof changes; obtain independent fidelity review from root.

The polynomial-time recursion is not claimed essential to the bare refutation: as the review points out, exact seeds through 13 and the root-split inequality would suffice at a larger base. This round uses the proposed 20/130 split for future kernel work.
