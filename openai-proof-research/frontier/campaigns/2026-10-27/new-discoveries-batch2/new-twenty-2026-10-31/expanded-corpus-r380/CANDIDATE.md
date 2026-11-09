# Ordinary candidates, dormant only — r380

Credit 0; accepted total remains root-provided 52/60 beyond 39 prior. Neither candidate has an independent review, formal endpoint, complete current-registry check, worldwide novelty clearance, manuscript or acceptance. No execution or dispatch is authorized by this file.

## 345451: full-scope Genius linearity ordinary proof

Literal statement and all quantifiers are in raw-provenance.json[345451]. Primary source: Federbush, arXiv:2002.03814v1, 4 February 2020, Sections 1–3, Theorem 1.1 and Conjecture 1, equations (1),(2). Entire six-page extracted manuscript was read, including the different Chapman theorem in the appendix. Acquired PDF hash in access.json. No journal or later companion body was acquired.

Work over any commutative Q-algebra, with formal variables u_1=1,u_2,...,u_p and d_1,...,d_p, subject to [x^p]D(x)=0, where D(x)=exp(sum d_i x^i). All statements are universal identities on this constraint. Set U(x)=sum u_i x^i, D_j=[x^j]D(x). The case p=1 has D_1=0 and the assertion is vacuous. Suppose p>=2.

Define A(x)=sum_{j=0}^{p-1} p D_j x^j/(p-j), and z(x)=x A(x)^(-1/p), using the formal binomial series with constant term 1. This definition depends only on d and p, never on u. It has leading coefficient 1 and therefore a unique compositional inverse X(z)=z+O(z^2). Define

F_i = [z^i] U(X(z)) = sum_{k=1}^i u_k [z^i] X(z)^k, 1<=i<=p.

Thus F_1=1 and every F_i is linear in all the u_k, treating u_1 as the fixed constant 1 (equivalently affine in the remaining u variables). It remains to prove that these are exactly the functions of the literal coefficient equation.

Differentiating z(x)^(-p)=x^(-p)A(x) gives the exact Laurent identity

z(x)^(-p-1) z'(x) = x^(-p-1) sum_{j=0}^{p-1} D_j x^j.

Indeed each summand differentiates with factor j-p, which cancels its denominator and the -p from differentiation of z^(-p). Since D_p=0, the difference from x^(-p-1)D(x) has nonnegative valuation. Multiplication by exp(y U(x)) cannot introduce a negative power. Taking formal residues and then changing variable z=z(x) yields

[x^p] D(x) exp(yU(x))
 = Res_x exp(yU(x)) z(x)^(-p-1) z'(x) dx
 = Res_z exp(yU(X(z))) z^(-p-1) dz
 = [z^p] exp(y sum_{i=1}^p F_i z^i).

Terms of U(X(z)) of degree greater than p cannot affect the last coefficient. These equalities hold coefficientwise in y, so no analytic convergence is assumed.

For completeness the formal residue change used above follows on Laurent monomials: for integer k != -1, z(x)^k z'(x) is the derivative of z(x)^(k+1)/(k+1), whose residue is zero; for k=-1, write z=x v(x), v(0)=1, so z'/z=1/x+v'/v has residue 1. By linearity and valuation, this proves the identity for the Laurent series in question over a Q-algebra. Existence of the inverse X follows recursively from its linear term 1; binomial powers are valid in a Q-algebra even if the constraint quotient has zero divisors.

Finally uniqueness can be justified without assuming the source's Theorem 1.1: with F_1=1 fixed, the coefficient of y^(p-i+1) in [x^p]exp(y sum F_j x^j) is F_i/(p-i)! plus a polynomial in F_2,...,F_{i-1}. An index larger than i cannot occur among p-i+1 positive indices summing to p, and an index i forces all the others to equal 1. Hence triangular recursion uniquely determines F_2,...,F_p. The constructed functions are therefore exactly the literal functions. This closes the ordinary proof for every p, not a finite sample.

Prior comparison: the primary source explicitly labels this Conjecture 1. Its Theorems 1.1 and 3.1 establish existence/uniqueness, not linearity. Equation (6), the Bell addition formula, expands D exp(yU), but does not itself identify the F_i as linear; the residue transport above supplies that missing bridge. The appendix Chapman theorem concerns a weighted sum of Stirling-polynomial evaluations and is not a stated theorem about these F_i. A full derivation from Chapman or other named classical results was not recovered, so this file does not assert either a routine exclusion or new-to-literature status. The formal residue and inverse-series tools are classical; their use alone is not a significance exclusion. Three bounded search batches included title/linearity and GitHub proof queries; no exact counterpart was identified, but current registry heads and complete theorem bodies were NOT cleared. Latest journal/companion coverage is incomplete. Root must decide significance and bounded prior qualification before any formal slot.

DORMANT Pi plan: formulate p>=1 over a universal rational coefficient algebra modulo D_p, or prove the stronger Q-algebra identity; formalize truncated exponential coefficients, binomial series/inverse composition and the residue transport with all bridges. Prove triangular uniqueness and the displayed explicit linear formula as the literal endpoint. No finite-p theorem suffices. Use pinned Lean/mathlib, audit only propext/Classical.choice/Quot.sound, independent statement review and fresh extracted strict replay. This plan has not been run and estimates no verified certificate size.

## 350365: ordinary refutation of the literal Sylow generator formula

Primary source: Gligoroski, arXiv:2104.05598, Definition 10 (generator means all bracketed powers, equation (13)), Definition 12 equation (22), Definition 15 equation (32), Definition 16, and Conjecture 2 equation (59), surrounding safe-prime context. These actual passages were read. Equation (70)'s proof, extracted lines 2705–2716, explicitly uses the particular entropoid with a3=0,a8=1,b2=0,b7=1 and operation

(a,b)*(c,d)=(bc,ad).

Thus this is a source-chosen member of the family, not an invented extension. Its maximal multiplicative quasigroup is (F_p^*)^2 by Definition 15. The source has inconsistent general 'entropic' wording in Definition 2: that conditional identity is not used as an extra axiom here. Fidelity review must retain this discrepancy and assess the explicit Definition 12/equation (70) model used by the conjecture, rather than exploit vacuity of the erroneous conditional definition. No correction of the conjectured bracket expression is being made.

Choose the safe prime p=11=2*5+1, so q=5, and g=(2,1). The element 2 has order 10 in F_11^*: its order divides 10; 2^2=4 !=1 and 2^5=32=-1 !=1 exclude all proper divisors 1,2,5. Hence its powers cover F_11^*.

To verify the generator hypothesis without enumeration, for every n>=2 every pair of integers i,j>=1 with i+j=n occurs as the exponent pair of a bracketed n-fold product of g, with value (2^i,2^j). For n=2 use g*g=(2,2). If every pair (i,n-i), 1<=i<=n-1, occurs, multiplying that term on the left by g gives exponent pair (n-i,i+1), and on the right by g gives (n-i+1,i). Their first exponents cover respectively 1,...,n-1 and 2,...,n, proving the induction. Every ordered pair of nonzero field elements has exponents i,j in {1,...,10}, so it occurs. This proves <g>=(F_11^*)^2, exactly 100 elements, in the source Definition 10 sense.

For any g=(a,b), successively evaluating the exact bracket in MathDB and source equation (59) gives

g*g=(ab,ab),
(g*g)*g=(a^2 b,a b^2),
g*((g*g)*g)=(a^2 b^2,a^2 b^2),
g*(g*((g*g)*g))=(a^2 b^3,a^3 b^2),
g*(g*(g*((g*g)*g)))=(a^3 b^3,a^3 b^3).

For our g the proposed g_q is (8,8). All bracketed powers of a diagonal element remain diagonal, since (t,t)*(s,s)=(ts,ts). Every bracketed n-fold power is therefore (8^n,8^n). There are at most 10 possible values, strictly fewer than q^2=25, so this element cannot generate any 25-element Sylow q-subquasigroup. In fact 8 has order 10: 8=2^3 and gcd(3,10)=1. The subgroupoid generated has exactly 10 elements. Nonvacuity of the desired 25-element subgroupoid can also be shown: replace g with (4,1); 4 has order 5, and the preceding induction gives the closed quasigroup QR(11)^2 with 25 elements. Hence the failure is genuine generation failure, not a missing Sylow object.

Optional stronger bridge: the affine bijection T(x1,x2)=(b7(x1+a3/a8),a8(x2+b2/b7)) maps Definition 12's maximal quasigroup to this model, and direct expansion of equation (22) gives T(x*y)=(T(x)_2 T(y)_1,T(x)_1 T(y)_2). Thus the diagonal obstruction is intrinsic to the exact bracket across the explicit family. The concrete source-approved model already suffices to refute the universal statement.

Prior/significance HOLD: Lorenz Panny, Entropoids: Groups in Disguise, ePrint 2021/583, is a concrete named relevant comparator. The source author's 2021/896 rebuttal acknowledges the attack on these concrete instances at abstract/search depth, but neither full body was accessible: both public file GETs returned 403, no retries. A group-disguise theorem alone is not a completed comparison to this particular Sylow-generator formula until its actual hypotheses/consequences and chronology are read. Therefore do not label this new, routine-excluded, accepted, or independently qualified. Completed allowlisted history contains adjacent entropoid IDs 350366/350367/350368 with their correction/hardness holds, preserved in historical-family-matches.json; no automatic family exclusion. Smallness/standard tools alone are not the reason for HOLD.

DORMANT Pi plan: if root first resolves the named prior and semantic holds, use ZMod 11 nonzero pairs, the exact binary operation, bracket trees, the universal exponent-pair induction and the diagonal invariant; prove generator g and impossibility of cardinal 25 for its proposed image. Include transport to literal source definitions. Avoid computational enumeration/native_decide. No formal work, dispatch or acceptance has occurred.
