.nr PO 0.7i
.nr LL 6.8i
.nr PS 11
.nr VS 15
.nr HM 0.65i
.nr FM 0.6i
.ds LH INTERNAL DRAFT - 340110
.ds RH Independent review pending
.ds LF Credit 0 - campaign 55/60
.ds RF Page %
.TL
A periodic-coset obstruction to unit acyclic matchings
.AU
Internal research draft
.PP
INTERNAL DRAFT - independent certificate, source and significance review pending. MathDB 340110. Acceptance CLOSED; credit 0. Campaign remains 55/60 additional outcomes, beyond 39 previous outcomes.
.NH 2
1. Exact claim and source
.PP
Aliabadi and Soleimany Dizicheh, A note on matchings in abelian groups, arXiv:1808.04975v3 (20 February 2020), Conjecture 3.7, asks whether every pair of finite subsets A,B of an abelian group G with A intersect (A+B) empty admits an acyclic matching whose acyclicity sequence contains only ones. Section 2 also assumes A,B nonempty, equally sized and 0 outside B. All these standing assumptions are retained here. The copied MathDB record has the same strengthening; its historical open label is not novelty evidence.
.NH 2
2. Objects and quantifiers
.PP
A matching is a bijection f:A -> B with a+f(a) outside A for every a. For every x in the entire ambient group, define m_f(x) to be the number of a in A with a+f(a)=x. Acyclic means: for every admissible bijection g:A -> B, equality m_g=m_f as functions on ALL G implies g=f. Equality merely of sorted sequences is insufficient.
.PP
The support consists of the x with positive multiplicity. The sequence lists m_f(x) once per support point and sorts these entries in decreasing order. Equal fibre sizes at different labels therefore occur with repetition in the list. Its length is the support cardinality and its underlying multiset is exactly this mapped support. Unit means every entry is 1, equivalently the list is a repetition of 1 of that length.
.PP
Generic bridge: x is in the support exactly when its fibre is nonempty. If all positive fibres have size 1, two arguments with the same sum lie in one singleton fibre and coincide. Conversely injectivity makes every nonempty fibre a singleton. Hence unit sequence is equivalent to injectivity of a -> a+f(a). No finiteness of the ambient G is assumed in this bridge. Every finite source set S has the Finset representation supplied by S.Finite.toFinset, whose coercion equals S; subtype equivalences are genuine bijections of these sets.
.bp
.NH 2
3. Witness and full translation proof
.PP
Let K=Z/3Z, G=K x Z/2Z, A=B=K x {1}, H0=K x {0}, and t=(1,0). These are actual additive abelian groups and finite subsets. The group has six elements and each coset has three. A,B are nonempty and 0 is outside B. Every sum from A+B has second coordinate 0. Conversely (u,0)=(u,1)+(0,1), so A+B=H0. The two cosets are disjoint. Thus all standing assumptions hold and every bijection A -> B is admissible.
.PP
Fix ANY bijection f:A -> A with unit sequence. Its sum map is injective by the generic bridge. Identify A with K through u -> (u,1). The first coordinate of the sum map is an injection K -> K: equality of first coordinates gives equality of the sums because both second coordinates are zero, then injectivity gives equality of the arguments. An injection of a finite type into itself is surjective. Consequently the sum map is a bijection A -> H0.
.PP
It follows for every x in G that m_f(x)=1 if x has second coordinate 0 and m_f(x)=0 otherwise. In the first case surjectivity supplies a preimage and injectivity makes its fibre a singleton. In the second case no argument can sum to x. This is the full labelled indicator formula, not only a claim about the three support points.
.PP
Define the actual output equivalence T:A -> A by T(b)=b+t with inverse b -> b-t, and let g=T composed with f. Its values stay in A because the second coordinate is unchanged. Therefore g is a bijection and is admissible. If g=f, evaluating at (0,1) and cancelling f(0,1) forces t=0, contrary to 1 nonzero in Z/3Z. Thus g differs from f.
.PP
For every x in G and every a in A, a+g(a)=x if and only if a+f(a)=x-t. The two fibres are exactly the same subset of A, so m_g(x)=m_f(x-t). Subtraction of t preserves the second coordinate. The indicator formula therefore gives m_g(x)=m_f(x) for every ambient x. Acyclicity of f would force g=f, a contradiction. This excludes EVERY unit matching, and supplies a counterexample to the literal universally quantified conjecture. No matching or permutation enumeration is used.
.bp
.NH 2
4. Both existence controls and the extra subgroup hypothesis
.PP
Unit existence is nonvacuous. The identity matching has sum (2u,0) at (u,1). Doubling is injective on K because 2*2=1 there: multiply an equality 2u=2v by 2. Thus identity is unit by the generic bridge. Identity and its output translation are distinct admissible bijections with equal full multiplicity. In particular identity is not acyclic.
.PP
For each c in K define h_c(u,1)=(c-u,1). Applying h_c twice returns the argument, so this is a bijection, and it is admissible. Every sum equals (c,0). Its full multiplicity is 3 at (c,0) and 0 at every other ambient point. Its support is the singleton {(c,0)}, so its sequence is [3] and is not unit.
.PP
To prove acyclicity, let g be an admissible bijection with m_g=m_hc. For any a, the fibre at a+g(a) is nonempty and has positive multiplicity. The displayed full formula for m_hc forces a+g(a)=(c,0). Also a+h_c(a)=(c,0). Cancellation gives g(a)=h_c(a) at every argument. Therefore g=h_c. This proves actual weak acyclic existence for this pair; the weaker source Conjecture 2.1 is not refuted.
.PP
B union {0} is not an additive subgroup: it contains (0,1) and (1,1), whose sum is (1,0), which is neither in B nor zero. Hence the additional subgroup assumption of source Theorem 3.5 fails. The witness does not contradict that theorem.
.NH 2
5. Strong inverse-lemma adaptation objection
.PP
There is a COMPLETE alternate reduction from a known inverse-matching ingredient. For any admissible self-bijection f, inverse is admissible and has the same full multiplicity, by reindexing b=f(a) and commutativity. Acyclicity forces f=f inverse. If f is also unit, a nonfixed two-cycle gives two distinct arguments with the same sum, impossible. Thus any acyclic unit self-matching must be identity. The present coset identity collision then excludes it. This materially strengthens the routine-adaptation objection and must be reconsidered at independent significance review and root adjudication.
.PP
The documented inverse ingredient does not itself certify an earlier printed refutation with this coset and all the target hypotheses. This draft makes no worldwide novelty claim and does not treat formalization as significance evidence. Root has granted only bounded prospective qualification; final acceptance remains unpaid.
.bp
.NH 2
6. Prior comparisons and limits
.PP
The supplied qualification compares the actual 2019 companion, Aliabadi and Janardhanan, On matchable subsets in abelian groups and their linear analogues, arXiv:1808.01376v3 (6 August 2019), LAA 582, 138-155. Its matching-matrix determinant condition concerns ordinary acyclic existence. Specializing to one constant-sum label gives a permutation matrix for this pair; it does not exclude all unit matchings. This is distinct from the cached file named matching-companion, which is Aliabadi-Filom, arXiv:2103.11432v2 (2022). The inverse method in that paper is an applicable ingredient, as explicitly discussed above.
.PP
The supplied 2024 classification (2402.08008v3) concerns ordinary acyclic matching; its compared prime examples have full sumset and violate target disjointness. The supplied 2025 SLC 91 B91b weak-existence construction specializes to h_c with sequence [3], not a unit sequence. Original Remark 3.6 exhibits bad unit matchings but does not exclude every unit matching for its pair. No assertion is made that an earlier source already printed the coset refutation.
.PP
Prior coverage is bounded to copied primary bodies, supplied targeted search evidence and dated registry-root observations. Separately typeset journal-final versions, corrections and worldwide unpublished knowledge were not exhaustively audited. Supplied 55 full statements and prior 39 metadata support bounded distinct-scope clearance, not revalidation of their certificates. Only ONE outcome is proposed, absorbing witness, helpers, controls and any family formulation.
.NH 2
7. Formal certificate and reproduction
.PP
Pins: Lean 4.34.1; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. Production modules in dependency order: Matching, Bridges, Coset, Controls, Sequence. Endpoint: UnitCoset.refutation : not UnitCoset.Conjecture. Conjecture quantifies over arbitrary abelian G, decidable equality and finite A,B satisfying Standing, and asks for an admissible subtype equivalence which is both UnitSequence and Acyclic. Decidable equality is supplied classically for arbitrary groups, not an extra mathematical restriction.
.PP
Strict production builds and leanchecker passes are recorded per module. The environment audit inventories every declaration of these modules by module origin, including private/generated declarations, saves typed expression bodies and a dependency DAG, traverses dependencies and checks safety and axioms. Only propext, Classical.choice and Quot.sound occur. Audit metaprograms themselves are outside the production proof closure.
.PP
Genuinely failing controls retain exit 1: wrong zero multiplicity for identity at (0,0), wrong [1] constant-sum sequence, and reversal of the proved nonacyclicity. Reproduction extracts only production sources, audit sources and runner/pin helpers to an empty build directory. Every module is rebuilt and checked with cleanroom/build plus upstream pins only. Final results/340110.json, receipts, audit inventory and hash manifest carry exact replay/QA status and any deviations; they are the authoritative verification ledger.
.PP
Resource receipts use two-core affinity, CPU 120 seconds, AS 12 GiB, sampled group RSS 6 GiB, devguard 130 seconds and wall cap 140 seconds. Sampling can miss transients. First broad Mathlib import failed on memory and was replaced by narrow imports. Independent certificate/source/significance review and root acceptance remain unpaid, regardless of green implementation checks.
