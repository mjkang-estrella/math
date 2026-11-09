# Formal refutation of Smyth Conjecture 1.5

This lane formalizes the discovery lane's certificate for MathDB 332037. It makes no acceptance or novelty decision.

The source is Clifford Smyth, *A Probabilistic Characterization of the Dominance Order on Partitions*, arXiv:1512.04084v1, Conjecture 1.5. All source access for this lane was to existing local files; no network was used. The published journal body was not checked here.

For A = 3, a = 20, B = 2, b = 19, write X = U³₁₉ × U²₂₀ and Y = U³₂₀ × U²₁₉. Let G be the eight lists in Base.lean, and let D consist of sorted lists dominated by a member of G. S consists of pairs in X whose sorted concatenation lies in D; T is defined similarly in Y.

The structural composition enumerator contains each list of the prescribed length and sum exactly once. The bridge theorems prove both completeness and absence of duplicates for all lengths and sums. Lists are realized as Fin-indexed functions using getD, with ofFn and sum round trips proved. Concatenation is Fin.append, and its ofFn list is the append of the two lists.

Dominance explicitly asserts equality of sums and all prefix inequalities, in the direction that the domain composition dominates its image. The finite Boolean test checks prefixes 0 through 5. For length-five lists this is equivalent to all prefixes: every later prefix is the total sum. The proof of this equivalence and dominance transitivity is ordinary Lean.

Kernel decide proves each row count, grouping by the first entry of the three-part composition. Python generates the proposed numerals only; every numeral is independently checked in Lean. The sums of the S rows and T rows are respectively 1137 and 1134. CountBase.count_rows proves that these row sums are the lengths of the literal filtered enumerations. Counts.lean combines the checked equations without recomputing the complete count in one kernel invocation.

If the conjectured injection existed, its dominance condition and transitivity would map S into T. The list realization and ofFn injectivity give an injective map on S.toFinset. Thus its cardinality is at most that of T.toFinset. S has no duplicates, so its cardinality is 1137; T.toFinset.card is at most T.length = 1134. This is impossible. Endpoint.lean proves Smyth1512.not_conjecture15 : ¬ Smyth1512.Conjecture15.

Controls.lean proves that rearrangement is a permutation and is pairwise non-increasing. It also supplies the conjectured injection for A = B = a = b = 1, using the identity, and a concrete inhabitant of that domain. Thus the literal definitions have a nonempty true instance.

The formal statement does not depend on the discovery script, max-flow output, conjectured infinite family, journal-version status, or any novelty claim. Only root may accept this result.
