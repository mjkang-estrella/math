# Statement correspondence

Source: Defant and Propp, Quantifying Noninvertibility in Discrete Dynamical Systems, arXiv:2002.07144v4, section 2.3: “Then s(π) = s(L)s(R)m.” The frozen rootWord, rootParts and sort_rootWord implement this maximum split. The new code retains those definitions unchanged. Literal labels use range M, that is 0 through M-1; maximum deletion is therefore parameterized by m on a domain of size m+1.

Definition 1.1 uses average multiplicity, deg(f) = |X|⁻¹ Σ_x |f⁻¹(f(x))|. The frozen P and deg implement literal collision cardinality divided by factorial. Conjecture 4.4 says the limit lies in (1.68, 1.73). StackSort.Conj is the existential limit statement for that quantity. MathDB 345545 instead says maximum fiber size; the frozen ConjMax and its unconditional refutation cover that reading separately. This lane changes neither reading nor the analytic endpoints.

The implementation target is the exact frozen StackSort.Round3.MaximumFinalCount. Its left side is the irreducible count plus the proper final-block correction restricted to label subsets containing the maximum. Its right side is the nine-term deletion sum with multiplicities mu = (1,2,1). MaximumPairs is exactly the literal maximum-final collision subfamily. ReducedPairs is its proved deletion domain, retaining unary orientation. deletionEquiv proves domain correspondence; childChoices_card proves the local multiplicities; deletion_eq_raw proves clipping compatibility for the deletion terms. The finite cardinality assembly and the fixed-maximum final-block count remain explicit unproved Props. The source-reading refutation remains conditional upstream.

No claim of a new mathematical discovery, acceptance, or independent statement-fidelity review is made here. Root decides.
