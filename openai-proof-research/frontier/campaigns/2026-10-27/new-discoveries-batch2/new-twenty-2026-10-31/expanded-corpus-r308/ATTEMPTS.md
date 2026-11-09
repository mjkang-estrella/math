# Ordinary mathematical investigation — no execution authorization

All three sustained routes below concern the exact assigned statements. No finite sweep, solver, numerical root search, Lean execution or child agent was used. These are ordinary deductions and failed mechanisms, not claimed resolutions. The source gates remain incomplete as detailed in results.json.

## 362469: polar-space symmetry

Write F = F_(q²), e=(q+1)/2, A=s²-u²-w² and B=b²+1. Homogenizing the literal equation on the projective line gives

H(X,T)=(wX+T)(bT+uX)^q-(wX+T)^q(bT+uX),

Q(X,T)=BT²+AX², and H=κ Q^e. Both sides have degree q+1. Consequently rescaling a projective representative multiplies both by the same nonzero factor; infinity is evaluated at (1,0). This supplies the semantic interpretation absent from the literal affine formula, without choosing an arbitrary value at infinity.

First route: Frobenius. H has H^q=-H, whereas the q-th power of the right side involves Q^q. Replacing λ by λ^q also conjugates the coefficients b,u,w,s, so it compares different parameter tuples. It does not provide n(κ)=n(-κ) for fixed parameters. Merely observing that κ belongs to F_q cannot repair this.

Second route: sign reversal. In homogeneous coordinates,

H=(wu^q-w^qu)X^(q+1)+(wb^q-u)XT^q+(u^q-w^qb)X^qT+(b^q-b)T^(q+1).

Q(-X,T)=Q(X,T), but H(-X,T) retains both pure terms and reverses only the mixed terms. Thus λ↦-λ proves the desired reversal only when wu^q=w^qu and b^q=b (or after an additional special cancellation). The norm condition b^(q+1)=-1 does not imply b^q=b. This invalidates the tempting universal involution.

Third route: simultaneous projective isometries. A sufficient certificate would be a matrix R∈GL₂(F), a≠0, such that Q∘R=aQ and H∘R=-a^e H. Such R induces a bijection on the whole projective line, including poles and common zeros. The Hermitian relation on s,u,w is not yet shown to force these simultaneous identities. An isometry of Q alone is insufficient, and a parameter-dependent conjugation must still preserve H with the indicated multiplier. Degenerate Q requires separate treatment. This is the precise missing full-scope lemma; no matrix or classification proving it was obtained.

There is a complete *scope correction*, not an eligible candidate. In F₉=F₃[i]/(i²+1), put b=1+i and s=u=w=0. Then b^4=2=-1, b³-b=i, B=1-i, B²=i. For every finite λ, the equation is i=κi. Hence κ=1 has all nine finite solutions and κ=-1 has none. At infinity both homogeneous sides vanish, adding one solution to each count. Thus n(1)=10 and n(-1)=1. No enumeration is needed: the equation is constant. Even without fixing infinity semantics, the finite count difference is nine and one extra point cannot cancel it.

Both inspected arXiv versions print the unrestricted triple. However the proof of conditional Theorem 4.2 constructs a geometric line using a nonzero direction (-w,-u,t,u,w). The zero triple supplies no such direction. This identifies an omitted nondegeneracy restriction, not a substantive refutation of the intended construction; credit is zero. No CANDIDATE.md or Pi request is justified. For example the nonzero specialization w=0,u=s=1 in the same field has H=i+λ³-λ and constant right side κi; the trace-zero linear map has equal-sized fibers, so the constant-example mechanism does not persist. This fiber argument does not solve general nonzero parameters.

## 371578: exchange with an exact intersection and adaptive rank bound

The v1 Conjecture 1.7 is exactly the reserved assertion. The v2 and v3 papers substantially reorganize and strengthen the representable theory. A missing conjecture label in v3 is not evidence of a general resolution. Theorems for characteristic zero retain representability hypotheses; the ordinary Theorem 1.6 for arbitrary matroids fixes whole subsets rather than the prescribed intermediate p.

Contract A∩B and restrict to A∪B. We may then regard A,B as disjoint complementary bases of a rank-r matroid on 2r elements; exchanges preserve the contracted part and ranks of subsets of the remaining ground set. Let S=A-U+V. Its complement is B+U-V, so feasible S are common bases of M and M*. The constraint Y⊆V forces Y⊆S, and |U∩X|=p is equivalent to |S∩X|=|X|-p. This is an exact cardinality slice of a matroid intersection, not simply an unconstrained basis optimization.

Route 1: choose P⊆X of size p and apply source Theorem 1.6 to P,Y. It returns P⊆U, Y⊆V and |U|≤r(P∪Y). This is exactly the required rank bound **if** U∩X=P. The source theorem does not prevent U from containing extra members of X. Minimizing |U| among these exchanges does not prove that none of those extras is needed. A proof of that assertion would settle the missing exact-slice lemma, so it cannot be assumed.

Route 2: interpolate between zero exchange and full exchange. At the endpoints, |U∩X| runs from zero to |X|; one would like adjacent feasible common bases to change this number by at most one while keeping Y in V. Ordinary exchange in M does not preserve being a basis of M*. General common-basis exchange can change several elements simultaneously. Even existence of a cardinality slice would still leave the adaptive bound |U|≤r((U∩X)∪Y). Connectivity of the union of all exchangeable pairs therefore is not enough. Serial exchange conjectures and the source's reconfiguration results must not be silently strengthened.

Route 3: optimize a weighted matroid intersection with a large weight for Y and a Lagrange multiplier for X. Weighted intersection solves the supported optimization problem, but a multiplier can jump over p. An integral polytope need not have every integer slice integral: an extra cardinality equation is a third constraint family. The existing source proof of Theorem 1.6 uses rank submodularity to bound a minimum cost, but does not establish integrality of that slice. No valid min-max theorem filling this gap was obtained.

In a characteristic-zero representation the Grassmann–Plücker identities provide nonzero exchange terms, while v1 Corollary 1.9 alone only gives |U|≤p+|Y|. Since r((U∩X)∪Y) can be smaller, that corollary by itself is not the literal target even on its restricted class. v3 improves the representable rank estimates; its harmonic-function framework still does not supply the corresponding function for arbitrary matroids. No counterexample, full ordinary proof or executable Pi problem was obtained.

## 363319: root simplicity

The source defines subtraction moves k₁<⋯<k_t, d_i=k_t-k_i for i<t, and d_t=k_t, so 0<d_i<d_t and the d_i are distinct (their indexing need not be increasing). The parity conditions correspond to all moves odd. The earlier credited nonconvergence result is a different endpoint; none of it proves squarefreeness of χ.

Put m=d_t, P(z)=tz^m+Σ_(i<t) z^d_i+1. A root with |z|>1 is impossible: t|z|^m≤1+Σ|z|^d_i<t|z|^m. If |z|=1, equality in the triangle inequality forces z^d_i=1 and z^m=-1. At such a root,

zP'(z)=tm z^m+Σd_i z^d_i=-tm+Σd_i<0.

Thus **every unit-modulus root is simple**, including -1; with the source gcd normalization it is the only unit-modulus root. This conclusion does not address roots strictly inside the disk.

For a repeated root z≠0, eliminating the leading term from mP-zP' yields

m+Σ_(i<t)(m-d_i)z^d_i=0.

If Σd_i≥(t-2)m, then Σ(m-d_i)≤m. For |z|<1 the modulus of the sum is strictly less than m (when t>1); hence repeated roots are impossible in this extra parameter regime. Together with the preceding argument this proves simplicity there. The inequality is not forced by parity or distinctness: an arbitrary odd m can be much larger than a collection of small even d_i. For t=1 the derivative is separately nonzero at roots. The partial criterion is not counted.

Route 2: Perron–Frobenius / renewal recurrences. After z↦-z the polynomial has a unique positive root at 1, but irreducibility of its nonnegative companion matrix proves simplicity only at the spectral radius. Nonperipheral eigenvalues can have Jordan blocks; one cannot infer global squarefreeness.

Route 3: factor arithmetic. A repeated integral factor of P has nonzero constant term dividing 1. Since all its roots would be strictly inside the unit disk, its leading coefficient has modulus >1. Squared factors therefore force square divisors in the leading coefficient t. In particular a squarefree t rules out a repeated nonconstant integral factor after taking a primitive irreducible factor in Z[x]: its constant term is ±1, its leading coefficient has absolute value at least 2, and that coefficient squared divides t. This is another sufficient regime, not a proof for arbitrary t. The residual case allows t with square factors and small Σd_i. No argument excluding repeated factors in that regime was found. Neither an exact repeated-factor witness nor a general nonvanishing resultant identity was obtained. No numerical or symbolic search was run.

No full endpoint survives source/semantic/significance qualification in this lane. All implementation plans remain absent rather than disguising these missing lemmas as finite execution tasks.
