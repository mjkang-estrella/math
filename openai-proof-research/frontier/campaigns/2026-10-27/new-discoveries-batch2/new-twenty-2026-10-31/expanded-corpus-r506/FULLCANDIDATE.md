# 343508: full ordinary deduction, author only, NOT qualified

Exact literal and original bindings: original-objects.json, ID343508. This document records a complete source-dependent deduction in the conventional fixed-integer t,l, q tending to infinity through all prime powers interpretation. It is not an independent PASS, novelty clearance, formal dispatch or credit. A joint varying-t,l interpretation is not silently asserted.

Source: Bayer--Meszaros--Ronyai--Szabo, Exploring Projective Norm Graphs, 1908.05190v1, definitions pp3--5, Theorem1(a) p5, actual proof p10 and Conjecture2 p36. Short published companion Acta Math Univ Comenianae88(3)(2019)437--441, Theorem2(a) p439 corroborates the pair formula. Its theorem statements are not a full proof of the companion's other results. The source's graph includes loops. The following proof applies to it and also after removing loops.

Put Q=q^(t-1), n=Q(q-1), d=Q-1, c=(Q-1)/(q-1), and fix 4<=l<t. Each vertex has exactly d neighbours when a loop counts once. Two distinct vertices with equal first coordinate have no common neighbour: their second coordinates differ, whereas dividing their common-neighbour norm equations would force them equal. For two distinct first coordinates the exact codegree is c-xi, xi in {0,1}, by Theorem1(a). This theorem is valid in every characteristic, unlike the source's triple formula.

For completeness the pair formula is immediate from norm fibres, with its algebra paid here. For u=(A,a),v=(B,b), A!=B, a common neighbour (X,x) has X!=-B and x=N(X+B)/b. The fractional-linear coordinate z=(X+A)/(X+B) is a bijection from X in F_Q excluding -B onto z in F_Q excluding 1. The remaining equation is N(z)=a/b. As a/b!=0, z!=0 automatically, so X!=-A too. Each nonzero norm fibre has c elements, and z=1 is excluded precisely when a=b. Reversing X=(A-zB)/(z-1) and x=N(X+B)/b proves both directions. Norm-fibre cardinality follows from cyclicity of F_Q^*: norm is exponent (Q-1)/(q-1), has image of order q-1 and kernel of size c. These are standard finite-field facts used here explicitly, not numerical evidence. They coincide with the source's Lemma1/Appendix Lemma14(f).

Choose uniformly an unordered l-subset S of the n vertices. Let X(S) be its common-neighbour count. For a vertex v define I_v(S)=1 if S subset N(v), zero otherwise. Then X=sum_v I_v. Double counting, valid also for symmetric adjacency with loops, gives
 E X = n binom(d,l)/binom(n,l) =: mu,
 E[X(X-1)] = sum_(v!=w) binom(codeg(v,w),l)/binom(n,l).
There are n(Q-1)(q-1) ordered pairs with distinct first coordinates, and n(q-2) ordered distinct pairs with equal first coordinates. Only the first type contributes to the second factorial moment. For each contributing pair c-1<=codeg<=c. Hence
 n(Q-1)(q-1) binom(c-1,l)/binom(n,l)
 <= E[X(X-1)] <= n(Q-1)(q-1) binom(c,l)/binom(n,l).
No enumeration was used.

For fixed l,t and q->infinity, binom(m,l)=m^l/l! (1+O_l(1/m)) whenever m->infinity; this follows by expanding the finite product product_(j=0)^(l-1)(1-j/m). Therefore
 mu = n(d/n)^l (1+O_l(1/d)) = q^(t-l)(1+O_l(1/q)),
 E[X(X-1)] = n^2(c/n)^l (1+O_l(1/c+1/Q))
              = q^(2(t-l))(1+O_l(1/q)).
Since mu^2 has the same leading term and E X^2=E[X(X-1)]+mu, Var(X)/mu^2=O_l(1/q+q^(-(t-l)))=O_l(1/q).
The implied constants can depend on the fixed integers; there is no characteristic restriction. For large q, set epsilon_q=q^(-1/4). Chebyshev, or summing the nonnegative squared deviations directly, shows
 #{S: |X(S)/mu-1|>epsilon_q}/binom(n,l)=O_l(q^(-1/2)).
Together with mu/q^(t-l)=1+O_l(1/q), outside o(n^l) subsets the count is (1+o(1))q^(t-l). This pays the shrinking error as well as the shrinking exceptional fraction, not just concentration at each fixed tolerance. For any finite initial q the asymptotic assertion imposes no separate equality. The endpoint l=t is deliberately not claimed: mu then stays bounded and the diagonal term does not vanish. l<t ensures mu>=order q.

Removing loops changes the common neighbourhood of a fixed l-set in at most l vertices, since a deleted loop can only remove a common neighbour which belongs to S. As l/q^(t-l)->0 this preserves the conclusion. Unordered sets rather than ordered tuples were used throughout, so no distinctness or l! bridge is missing.

Second route / cross-check. Treat the same identities as homomorphism counts: the first moment is the labelled K_(1,l) count and the second factorial moment the injective right-pair K_(2,l) count. Pairwise codegrees calculate the latter directly. Their quotient tends to one, which is exactly the vanishing L2 error above. This is an independent organization of the deduction, not an independent review or another family. Expander-mixing alone is an inferior route here: it supplies additive errors whose relative scale for small intersections needs an extra argument. The exact pair formula avoids that unpaid step. Trying to solve all l norm equations pointwise is unnecessarily stronger and the source's exceptional triples warn against claiming every generic l-set is typical.

Significance adjudication. The strongest positive case is that the actual source explicitly states exactly this all-but-o(n^l) conclusion as Conjecture2, not merely a neighbouring uniform statement, and this deduction works for every fixed l<t and every characteristic. Smallness/standard Chebyshev alone is no exclusion. The strongest exclusion case is COMPLETE: the already-public exact pair formula, the already-public degree formula, the two double-count identities, finite-product estimates and Chebyshev above supply the entire source-result-to-target bridge with no residual mathematical lemma. I recommend ROOT assess this as a source-own routine adaptation rather than significant-discovery credit; no claim that an earlier exact proof was printed is authenticated. Search no-matches do not establish novelty. The ACTUALBRIEF retains the source explicit-conjecture contrary case. No family credit is assigned by the author.

Qualification still unpaid: independent fidelity/proof/significance review; visual glyph check; full final/corrections investigation (current arxiv metadata displays v1 only, not proof of absence of a journal/correction); current registry heads are inherited unavailable, so no refresh or worldwide clearance; no full pinned upstream audit or formal endpoint. Search excerpts are navigation only.
