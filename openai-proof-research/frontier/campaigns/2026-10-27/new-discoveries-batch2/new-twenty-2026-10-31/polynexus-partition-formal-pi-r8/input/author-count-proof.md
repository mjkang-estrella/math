# 352496: ordinary interval proof, not an accepted discovery

Credit 0. Research candidate only. All n are positive integers. The source is Fikioris–Fikioris, *A subsemigroup of the rook monoid*, arXiv:2111.01863, §4 (17)–(24), §8 (53)–(55). The downloaded body and hash are in access-primary.json. The MathDB full original statement and its binding are in raw-provenance.json.

## Exact semantics

The source M_n is the contiguous-single-diagonal submonoid, not the entire rook monoid R_n. Its nonzero matrices have entries x_ij=1 precisely when k<=i<=m and j=i+d, with 1-min(0,d)<=k<=m<=n-max(0,d). Equivalently a matrix is uniquely an ordered pair (I,J) of nonempty integer intervals in [n] of equal length, with the unique increasing translation I->J. This equivalence follows by I=[k,m], J=[k+d,m+d]; conversely d=min J-min I and k=min I,m=max I satisfy every printed inequality. Distinct pairs yield distinct matrices by their row and column supports.

The source counts ordered operand pairs (x,y) with xy nonzero, not distinct output matrices. Equation (53), the literal sextuple sum, makes this binding explicit. If 'products' instead means distinct outputs, the identity already gives every nonzero element as an output and the claimed polynomial is not that count. That alternative is a wording issue and earns no credit. Here the intended source binding is retained without changing the raw record.

For x=(I,J) and y=(K,L), matrix multiplication is nonzero iff J intersects K. Indeed a nonzero summand x_ij*y_jh requires j in J intersect K; conversely any such j gives i in I,h in L and a positive product entry. This also reproduces source Theorem 3: max(k,k'-d)<=min(m,m'-d). No drawing is needed for these algebraic definitions.

## Complete count

There are T_n=sum_{a=1}^n(n-a+1)^2=n(n+1)(2n+1)/6 nonzero operands. A proof of the square sum is induction: the displayed polynomial vanishes at 0 and its difference at consecutive integers is n^2.

Let D_n count zero pairs for which J lies strictly to the left of K. The opposite ordering contributes exactly D_n, by exchanging the lengths and the supports; every disjoint pair has exactly one ordering. Fix |J|=a, |K|=b with a,b>=1 and put t=n-a-b>=0. The numbers of unused positions before J, between J and K, and after K are three nonnegative integers summing to t. Thus there are binom(t+2,2) placements (bijection with two separators among t+2 positions). For each placement I can be any of n-a+1 intervals, and L can be any of n-b+1 intervals, independently. Consequently

D_n=sum_{a,b>=1,a+b<=n} binom(n-a-b+2,2)(n-a+1)(n-b+1).

This is an exact bijective reduction of the source's six summations, including the sign constraints on d,d'. Neither identity removal nor distinct-output quotienting is performed.

All following power series are formal over Q, so each coefficient has finitely many contributors. Set A(z)=sum_{a>=1}z^a=z/(1-z), B(z)=sum_{a>=1}a*z^a=z/(1-z)^2. For t>=0 let
U_0=sum binom(t+2,2)z^t=(1-z)^(-3),
U_1=sum (t+1)binom(t+2,2)z^t=(1+2z)/(1-z)^4,
U_2=sum (t+1)^2 binom(t+2,2)z^t=(1+7z+4z^2)/(1-z)^5.

The first identity follows by cubing the geometric series (the same three-gap bijection); B follows by formal differentiation. Applying z*d/dz+1 once and twice to U_0 proves U_1 and U_2 explicitly. Since (n-a+1)(n-b+1)=(b+t+1)(a+t+1)=ab+(a+b)(t+1)+(t+1)^2, multiplication gives

sum_{n>=0}D_n*z^n=B^2 U_0+2AB U_1+A^2 U_2
=z^2(4+11z+4z^2)/(1-z)^7.

By seven geometric factors, [z^r](1-z)^(-7)=binom(r+6,6) for r>=0, and zero for r<0. Therefore
D_n=4 binom(n+4,6)+11 binom(n+3,6)+4 binom(n+2,6).
For n>=1 the falling-product expressions still give zero at all the boundary cases with upper entry below 6 (each has a zero factor). Expanding those six-factor products gives
720 D_n=19n^6+57n^5+25n^4-45n^3-44n^2-12n.
Meanwhile 36 T_n^2=4n^6+12n^5+13n^4+6n^3+n^2. Subtracting twice D_n yields
120(T_n^2-2D_n)=7n^6+21n^5+35n^4+35n^3+18n^2+4n
=(n+1)^7-n^7-(n+1)^3+n^3.
Thus the exact source pair count is the proposed Polynexus formula for every positive n. The source defines its nontrivial monoids for n>=2; the same printed matrix definition at n=1 has just zero and identity, giving one nonzero pair, as does the formula. No n=0 assertion is needed (source N is positive).

## Source, novelty and significance limits

This proves the ordinary count under the explicit source semantics. It does not prove novelty. The source itself leaves this exact sum as Conjecture 1, verified computationally through 70; those computations were not rerun or used. The 2023 companion arXiv:2302.09496 extends parameters to real numbers and has no Polynexus/conjecture text match, but only selected substantive passages were read; absence of a term is not an exhaustive subsumption audit. The final original journal body has not been correctly located/read. An attempted DOI returned an unrelated monoid paper; that response is preserved and excluded as evidence. Indexed public and GitHub-oriented searches did not identify a matching proof, but no current registry head or full registry body audit was established. These remain HOLDs. A classical convolution is used explicitly, but familiarity of that tool alone is not a complete prior-result-to-target novelty exclusion. Independent review must determine significance and whether the full reduction is already routine in a concrete applicable earlier result.

## Dormant formal plan — no execution or dispatch

Only if root resolves prior/significance and statement fidelity: define integer intervals by endpoints in Fin n, nonzero operands as equal-length pairs, and multiplication via partial translations. Prove the matrix/source binding and the intersection criterion first. Count disjoint pairs by a finite gap-composition equivalence with independent I,L choices. Replace formal generating functions by finite binomial convolutions or prove those identities inside Lean. Establish the three weighted convolutions, the closed D_n expression, and the displayed polynomial identity, including positive-n boundaries. Final theorem must state the ordered operand-pair cardinality for the exact source M_n and the multiplied-by-120 integer identity; derive the rational formula without truncated division. Every bridge is required, not a count for a surrogate interval model alone. Pin Lean/mathlib; no sorry/admit/axioms/unsafe/native_decide/oracles; only propext, Classical.choice, Quot.sound allowed transitively. Independent fidelity review, ordinary proof review, significance/prior review, full endpoint, axiom audit, extracted strict replay, manuscript and root acceptance remain unpaid. No Pi, compiler, mathematical program, enumeration, solver or CAS was run here.
