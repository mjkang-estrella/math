# Sustained ordinary routes, r358

Discovery and ordinary ideation only. No mathematical enumeration, solver, CAS or Lean execution occurred. These arguments are written deductions; they do not certify novelty. All three routes earn zero credit. No route qualifies for Pi execution.

## 331098: replace representative matching by a common valuation model

**Literal endpoint.** For two UFDs and the two displayed unions of principal ideals with matching factor counts and exponents, prove that their compressed zero-divisor graphs are isomorphic. The source is Alvir, arXiv:1508.02432v1, Conjecture 14, PDF pp. 7–8. The graph identifies nonzero zero divisors by equality of annihilator ideals. Edges mean product zero; the paper also discusses allowing loops. Both conventions must be kept separate.

**First failed approach.** Extending Theorem 5 by replacing the generator with the gcd of *all* ideal generators is false. In D=F[x,y], I=(x,y)^2, the nonzero class x has nonzero annihilator, while gcd(x,x^2,xy,y^2)=1 and the class of 1 has zero annihilator. In fact x^2 is in I, x is not, and x annihilates itself; no nonzero class annihilates 1. This disproves that proposed bridge (source Conjecture 12), not Conjecture 14. It cannot be used as a solution of the assigned problem. No search was used to obtain the example.

**Second failed approach.** Matching the divisors in each principal piece separately does not produce a map on annihilator classes. The same irreducible can occur in several pieces, and products of divisors from different pieces matter. Even the generalized zero-divisor basis need not give distinct annihilator classes. One must retain the entire global pattern of associates across pieces, not only a list of local exponent multisets.

**A complete ordinary theorem under an explicit coherent-pattern hypothesis.** Let P be a set indexing pairwise nonassociate irreducibles p_i in D_1 and pairwise nonassociate irreducibles q_i in D_2. For each alpha let e_alpha:P→N have finite support, and suppose

I_1 = union_alpha (product_i p_i^(e_alpha(i))),
I_2 = union_alpha (product_i q_i^(e_alpha(i))).

Assume these really are proper nonzero ideals. Put M=N^(P), the additive monoid of finitely supported exponent vectors, and U={v in M: some e_alpha≤v coordinatewise}. For nonzero a in D_j let v_j(a) be its valuations on the indicated primes. Unique factorization gives

a in I_j iff v_j(a) in U,
v_j(ab)=v_j(a)+v_j(b).

Primes outside P do not affect either assertion. Every v in M is realized by the nonzero product of the indicated prime powers. Define R_v={w in M:v+w in U}. The preimage in D_j of the annihilator of a+I_j is (I_j:a). It consists of 0 and exactly those nonzero b with v_j(b) in R_(v_j(a)). Consequently, by realization of every w,

ann(a+I_j)=ann(b+I_j) iff R_(v_j(a))=R_(v_j(b)).

The nonzero quotient condition is v notin U. Such a class is a zero divisor exactly when R_v differs from U. To prove this equivalence, U is always a subset of R_v, because each I_j is an ideal and multiplication by a preserves I_j. A witness w in R_v\U realizes a nonzero quotient element annihilating a. Conversely every nonzero annihilating quotient element supplies such w. Thus the graph in either ring has the same abstract vertex set

{R_v:v notin U and R_v≠U}.

For vertices represented by v,z, an edge is equivalent to v+z in U. This is independent of the chosen representatives: R_v=R_v' implies that v+z in U iff v'+z in U; R_z=R_z' then implies v'+z in U iff v'+z' in U. Equality of classes is equality of R sets. If loops are excluded, additionally require the vertices to differ. If loops are admitted, leave this additional condition out. In both conventions the identity on the displayed abstract vertex set is a bijection preserving and reflecting edges. This proves the theorem for arbitrary, even infinite, families of generators, without a principal-ideal or Noetherian assumption.

**Comparison and novelty gate.** For one generator, U is the principal upper set e+M; R_v is the upper set with threshold max(e-v,0). Removing zero and regular classes recovers exactly the truncated-divisor model of Alvir Theorems 5, 6 and 8. For general U the proof merely uses the same divisibility test together with the classical annihilator quotient construction. Spiroff–Wickham's actual journal Definition 1.1 and preceding argument identify the graph as the graph on annihilator classes and explain its multiplicative-semigroup origin. Therefore this route is a complete elementary multiplicative reduction, not evidence of significant novelty. The 2024/2026 cochordal papers concern uncompressed graphs and restricted ring families; their introductory statements have been read, not their entire proof bodies. They do not establish worldwide absence of a stronger semigroup theorem.

**Separate gates.** Ordinary coherent-pattern theorem: complete. Exact literal/source fidelity: HOLD, since the source's notation does not explicitly state the global associate-incidence bijection needed here; matching numbers of factors and exponents alone cannot silently be strengthened. Literature/subsumption: HOLD, including general semigroup precedents cited by Spiroff–Wickham. Significance: elementary classical reduction, zero credit. Formal endpoint, independent review, extracted replay: not attempted. No CANDIDATE.md or Pi dispatch.

## 328918: digit products give the entire corrected polynomial, not only one divisibility factor

**Source.** Byszewski–Ulas, arXiv:1409.8118v1, Section 2 (recurrence (2), Proposition 2.4, Theorem 2.5, Proposition 2.6, Corollaries 2.12–2.14), and Conjecture 4.3, PDF pp. 14–15. The current arXiv page lists only v1. The journal is Acta Mathematica Hungarica 147 (2015), 438–456, DOI 10.1007/s10474-015-0547-0; the public journal landing response was acquired, but the final journal proof body was not read. No journal-version equivalence or corrections clearance is claimed.

**Semantic defects to preserve.** The printed source and literal record say a_1,...,a_k while using a_m; the last summation index is i_k while the expression uses all i_j for j≤m; the second conclusion uses undefined n_j. Thus no literal full formal endpoint can be obtained by silently correcting notation. The following theorem is for explicitly corrected m-tuples, all m indices, and n_j=a_j. It does not receive credit for repairing the statement.

**Full corrected theorem.** Work in C[x_1,...,x_m,y_1,...,y_m], with k≥2 and a_j≥0, and choose a nontrivial kth root zeta. Set N=sum_j a_j, L_(j,r)=x_j+k^r y_j, and define G by the m independent sums 0≤i_j<k^(a_j), weighted by zeta^(sum_j s_k(i_j)), with power N. Then, more strongly than just the proposed divisibility,

G = N! (k/(zeta-1))^N product_(j=1..m) product_(r=0..a_j-1) L_(j,r).

For k=2, zeta=-1, this is the claimed (-1)^N N! product.

**Complete proof.** The base-k digit expansion gives a bijection between each i_j and digits d_(j,r) in {0,...,k-1}, with i_j=sum_r k^r d_(j,r) and s_k(i_j)=sum_r d_(j,r). Hence the exponential generating series of the weighted sums is

E(t)=product_(j,r) (sum_(d=0..k-1) zeta^d exp(t d L_(j,r))).

This is a formal power series identity over the polynomial coefficient ring; all products and coefficient sums used at degree N are finite. Each factor has constant term sum_d zeta^d=0. Its coefficient of t is L sum_d d zeta^d. Differentiate (1-z^k)/(1-z)=sum_d z^d formally in z and evaluate at nontrivial zeta: sum_d d zeta^d=k/(zeta-1). There are exactly N factors. Therefore the coefficient of t^N in E(t) is exactly (k/(zeta-1))^N product L: every factor must contribute its linear term, since every constant term vanishes. The same coefficient from the defining weighted exponential sum is G/N!. Equate them. If N=0, every range is {0}, the zeroth power is 1, and both sides are 1, so the empty-product case is also covered. Equality implies the whole divisibility product at once, including specializations where some factors coincide or vanish; no coprimeness assumption is needed.

**Sustained alternate route and earlier-result bridge.** A tempting specialization argument setting L_(j,r)=0 proves vanishing at each hyperplane but does not by itself prove divisibility by a product with repeated factors. The digit-factor proof avoids this missing multiplicity step. Independently, expand the Nth power into block powers d_j. The corresponding single-block sum vanishes for d_j<a_j by source Proposition 2.4 applied to u(i)=s_k(i)x_j+i y_j, V with basis x_j,y_j, P diagonal(1,k), q=x_j+y_j. Since sum d_j=sum a_j, only d_j=a_j survives. Source Corollary 2.12 gives that block sum as a_j!(k/(zeta-1))^(a_j) product_r(x_j+k^r y_j). The multinomial coefficient N!/product a_j! cancels the block factorials and gives exactly the displayed formula. Proposition 2.6 additionally gives the source's divisibility mechanism for arbitrary block power. This is a full explicit reduction to results already present in the same paper, not an exclusion based on ease or small size.

**Gates.** Corrected ordinary theorem: complete by two arguments. Literal full statement: ill-formed without authorized corrections. Significant novelty: fails the complete source-reduction standard. Journal/corrections and full citing-body coverage: incomplete, no absence claim. Lean, independent review, replay: not attempted. Zero credit; no dormant implementation is recommended for acceptance.

## 330993: distinguish pointwise root continuity from a global modulus

**Source reading.** Cooper, arXiv:1507.07118: Conjecture 1 read in v1, v2 and latest v3, plus the author's January 8, 2018 PDF. The early versions call it a vague conjecture. The wording does not specify the dependence of f on the base tensor, dimension or size bound. Section 2 defines eigenvalues as characteristic-resultant roots; for order 2 these are exactly ordinary matrix eigenvalues counted algebraically. The proof program later specializes to real symmetric tensors. The 2020 journal article, Linear Algebra and its Applications 596, 184–202, DOI 10.1016/j.laa.2020.03.013, was located, but its final proof body and possible later corrections were not read. This remains a distinct gate.

**Failed affirmative shortcut.** Continuity of roots of a fixed-degree monic polynomial in its coefficients gives a matching with multiplicities locally near a fixed matrix/tensor. It does not give a modulus independent of an unbounded base point. Compactness can promote local continuity to uniform continuity only on a fixed compact coefficient/tensor set; boundedness and fixed dimension cannot simply be dropped. Also, spectral radius is not a norm.

**Complete elementary obstruction for the unrestricted uniform reading.** For every delta>0 take order-2 real hypermatrices

A_delta = [[0,1/delta],[0,0]],
B_delta = [[0,1/delta],[delta,0]].

Their difference has exactly one nonzero entry of modulus delta. In the Frobenius norm its norm is delta, and in any fixed norm it is c delta for the constant c=norm(E_21). Characteristic polynomials are respectively t^2 and t^2-1. Both eigenvalues of A are 0, while B has eigenvalues 1 and -1. Thus every multiplicity-respecting bijection moves both roots by exactly 1. For any common f(epsilon) tending to zero, choose epsilon>0 with f(epsilon)<1 and put delta=epsilon/c. The hypothesis norm(A-B)≤epsilon holds, but the strict conclusion 1<f(epsilon) fails. This is a family defined by a formula, not an enumerated experiment. The same matrices have spectral radius(A-B)=0, so any interpretation allowing spectral radius as distance on all matrices fails even with a fixed pair as epsilon tends to zero.

**Second obstruction checked and rejected as a solution.** A fixed real-symmetric order-2 example cannot use the preceding nilpotent off-diagonal construction, because symmetry forces both off-diagonal entries to change. Classical Weyl bounds then apply. The source's intended symmetric higher-order homogeneous spectrum needs separate treatment; changing to H-eigenvalues, E-eigenvalues or variational maxima would not settle its complex resultant spectrum. No claim about that intended restricted class follows here.

**Gates.** Global uniform claim on unrestricted hypermatrices: elementary classical counterexample complete. Pointwise/modulus-dependent reading: this argument does not refute it. Intended real symmetric higher-order problem: HOLD. Novelty/significance: unrestricted nonnormal matrix instability is classical; a domain/quantifier correction earns zero credit. Full journal/citing proof coverage: incomplete. No candidate and no Pi execution.

## Additional exact reductions and source warnings

**326288.** In the source, a weight assigns a real value to every one-dimensional subspace of an n-dimensional F_q space, and the sum of these weights is zero; a subspace weight is the sum over its one-dimensional subspaces. Source Theorem 1.3 uses exactly these definitions and concludes the required Gaussian-binomial lower bound whenever n≥3k. For positive k, n≥4k implies n≥3k. A fixed line L has k-subspaces through it in bijection with (k-1)-subspaces of V/L, so the source's star count is exactly [n-1 choose k-1]_q. Substitution proves every literal positive-dimensional instance; it is already public in the supplied source. Section 5's actual proof was read: either the entire star at a maximum-weight intersection line is nonnegative, or Lemmas 3.7 and 4.5 give disjoint collections through that line and disjoint from a negative k-subspace whose summed bounds contradict the assumed count; k=2 is handled separately and n=3k by the divisibility case. These dependency lemmas were not independently audited, nor all six historical versions acquired, and no such audit is required to recognize the theorem's direct subsumption. Zero credit.

**333165.** The literal record assigns n≥1 to inequalities (2),(3),(7), whereas the actual source assigns it to (2),(5),(6). At n=0 in literal inequality (6), partitions of 2 with no repeated odd part consist only of (2): (1,1) is disallowed. Its M_2 rank is ceil(2/2)-1=0. Therefore both sides of (6) count no allowed ranks, giving 0>0, false. This uses a direct classification by the two possible partitions of 2, not a computational enumeration. It is an endpoint transcription correction, explicitly zero credit. It does not resolve the seven corrected source inequalities. The source proves only a restricted residue class of (7), and cites other work for the first four.

**323383.** The later Mayhew–Newman–Whittle arXiv:1412.8399v3 theorem and its actual proof of Theorem 1.1 were read. Its MS_0 language has only subsets and independence, unlike the earlier rank/arithmetic language. The authors explicitly say the results are independent. Thus it is a material public counterpart, not a justified exact subsumer of arbitrary rank/arithmetic MSOL. The proof uses finitely many k-equivalence classes to choose projective planes over distinct characteristics that cannot be distinguished after direct summing a copy of one of them; representability of the two direct sums differs. The crucial finiteness lemma is language-specific. Missing bridge: prove that every finite set of allowed rank/arithmetic MSOL sentences can be translated into that MS_0 language, or prove the desired finite-variable indistinguishability directly in the richer language. Neither has been established here. HOLD; do not count this as either a new proof or an exact public resolution without that bridge.

**325464.** The corpus references say “refuted,” but the acquired thesis actually states the assigned codegree decomposition bound as Conjecture 9.6 and proves weaker bounds/special cases in the read section. The counterexample found by a text locator concerns a different core/depth statement, not Conjecture 9.6. Do not turn that reference annotation into a rejection proof.

**381178.** The printed source and literal statement define k* as a maximum of two *prices*, then use it as an integer parameter of H_n(k*). This is not an argmax and need not be a valid integer. Replacing max of values by a choice of maximizing index is a wording repair, not a solution of the all-digraph extremal conjecture. No tournament-state artifacts or protected paths were accessed for this record.
