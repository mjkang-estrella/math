# Independent ordinary proof and authenticated prior bridge: MathDB 326886

## Exact scope
Let p be any odd prime, k any positive integer, r=p-1, q=p^k, Q=q^r, E a field with Q elements, and a in E nonzero with a^(q-1)=-1. Set N=(Q-1)/(q-1)=1+q+...+q^(r-1), d=N+1. The assertion is that f(x)=a^(-1)x^d and f(x)+x are both bijections E to E. Positive k is the standing finite-field convention, not an added restriction on meaningful database instances. There is no gcd(k,r)=1 assumption, no k=1 restriction, and no existential weakening of the universal admissible-a quantifier.

## Independent full derivation
The q-Frobenius on E fixes a subfield K of q elements. Here k divides rk; equivalently X^q-X divides X^Q-X, and its q distinct roots are in E and are closed under the field operations. Thus K is an actual subfield, not an unrelated field of characteristic p. The q-Frobenius has r-th power the identity. Define n(x)=x^N. This equals the product of the r q-conjugates, including at x=0; n(x)^q=n(x), so n maps E into K, is multiplicative, and n(0)=0.

The hypothesis gives a^q=-a. Applying q-Frobenius again gives a^(q^2)=a because q is odd. Also a is not in K: otherwise a=-a, forcing a=0 since p is odd. Put b=a^2. Then b^q=b, so b belongs to K and is nonzero. It is nonsquare in K. Indeed c^2=b with c in K would give (a-c)(a+c)=0 in E and hence a=c or a=-c, each contradicting a outside K. The even number r=p-1 of alternating conjugates is consistent for all odd p, including p=3.

Put m=(p-1)/2. We first prove H(t)=t(t^2-b)^m is a bijection of K. Every t^2-b is nonzero. Consequently H(t)=0 if and only if t=0. Suppose H(x)=H(y). The zero-input cases therefore give x=y=0. Otherwise let U=x^2-b, V=y^2-b and z=U/V, each nonzero. Squaring H(x)=H(y) and dividing V^(p-1) gives x^2 z^(p-1)=y^2. The definition of z also gives x^2=z y^2+b(1-z). Substitution and rearrangement yield

y^2(z^p-1)=b(z-1)z^(p-1).

In characteristic p, z^p-1=(z-1)^p. If z is not 1, division by the nonzero (z-1)z^(p-1) gives

b=y^2((z-1)/z)^(p-1)=[y((z-1)/z)^m]^2,

a contradiction to nonsquareness in K. Hence z=1 and U=V. Returning to the original unsquared equality and cancelling nonzero U^m yields x=y; no sign is lost. Finite injectivity proves H bijective.

Next the d-th power map permutes E. We have gcd(N,N+1)=1. Removing the coprime factor N shows gcd(N+1,(q-1)N)=gcd(N+1,q-1). Since q=1 modulo q-1, N+1=r+1=p modulo q-1. Since p is coprime to p^k-1, this gcd is 1. On E nonzero, Bezout gives an inverse exponent for the d-th power map (reduce it modulo Q-1); zero has exactly the zero preimage. Multiplication by nonzero a^(-1) preserves bijectivity, proving that f permutes E.

For t in K, the conjugates of t+a are alternately t+a and t-a. Therefore

n(t+a)=product_(i=0)^(r-1)(t+a^(q^i))=(t^2-b)^m.

Define F(x)=x^d+ax=x(n(x)+a), where the identity uses d=N+1 and remains valid at zero. Multiplicativity of n gives n(F(x))=n(x)(n(x)^2-b)^m=H(n(x)). If F(x)=F(y), injectivity of H gives n(x)=n(y)=t. Cancelling t+a in (t+a)x=(t+a)y then gives x=y, since t is in K and a is outside K, so t+a cannot vanish. Finite injectivity proves F bijective. Finally a^(-1)F(x)=f(x)+x is bijective. This proves both exact CPP maps for all admissible p,k,a, without a norm-surjectivity assumption, numerical test or formal API.

## Distinct primary source authenticated
Jingxue Ma, Tao Zhang, Tao Feng and Gennian Ge, *New results on permutation polynomials over finite fields*, arXiv:1506.05525v2, PDF dated 23 June 2015. The initial search calls it *Some new results...* and gives a first version date of 18 June 2015; the acquired v2's own title and date are the controlling bibliographic evidence here. Public exact proof existed no later than 23 June 2015, long before this 2026 review. No claim about the final journal version or an earlier first-proof date is necessary.

Acquired primary PDF: sources/ma-1506.05525v2.pdf, SHA256 e495cb7ab11dfa424f535fdf2cbfd83363e3d6ae57d7901c7c9d1e723815cefa. Full extracted text saved alongside it. Read front matter and CPP definition, Conjecture 1 on printed p.2, norm definitions and Lemmas 2.2-2.3 on p.3, entire Lemma 3.1 proof and Theorem 3.2 on p.4, complete Theorem 3.2 proof on p.5, and bibliography [24]. Other sections merely present in extraction are not claimed audited.

Theorem 3.2 has exactly: p odd prime, r+1=p, d=(p^(rk)-1)/(p^k-1)+1, a nonzero in F_(p^(rk)), a^(p^k-1)=-1; conclusion a^(-1)x^d CPP on that same field. Positive k is made explicit in Lemma 3.1 and the proof says any k. Parameter identification is the identity p->p, r->p-1, k->k, a->a, with the identical exponent and identical definition of CPP. Finite-field isomorphisms preserve the polynomial maps and hypotheses if different models of the finite field are used. There is no residual subfamily left outside Theorem 3.2.

## Independent audit of the actual Ma proof
Ma Lemma 3.1 states exactly the nonsquare H lemma above and supplies an AGW argument, rather than merely reporting a conjecture solved. Here is its full argument with all restrictions made explicit. On A=K nonzero, define lambda(x)=x^2-c, barlambda(x)=x^2, S=lambda(A), T=barlambda(A), and h(s)=(s+c)s^(p-1), where c is a nonsquare in K. S and T both have (q-1)/2 elements; S contains no zero. The map H sends A into A. For x in A, barlambda(H(x))=x^2(x^2-c)^(p-1)=h(lambda(x)). H is injective on every lambda fiber: those fibers consist of the two elements x,-x, and H(-x)=-H(x) differs from H(x), since p is odd and H(x) nonzero.

To prove h injective, fix b in T, a nonzero square. Any s in S with h(s)=b is nonzero and satisfies s^p+c s^(p-1)=b. Put y=1/s; this gives y^p-(c/b)y-1/b=0. Two different roots would have nonzero difference w satisfying w^(p-1)=c/b. The left side is a square since p-1 is even, whereas c/b is a nonsquare because b is a nonzero square. Contradiction. Thus h is injective, hence bijective S to T. If H(x)=H(y), the commutative relation and injective h give lambda(x)=lambda(y); fiber injectivity gives x=y. H permutes A; H(0)=0 is the only zero, proving the whole-field assertion. This verifies the finite-set criterion directly, without reliance on an unread upstream AGW proof. The printed last reference to S causes no scope problem: the argument proves at most one root in the entire nonzero field.

Theorem 3.2 then uses gcd(d,Q-1)=1, a^q=-a, b=a^2 nonsquare in K, and the conjugate-product reduction in Lemma 2.2 to this very Lemma 3.1. The independent norm-fiber proof above supplies the entire applied direction of Lemma 2.2 and the otherwise compressed gcd and nonsquare steps. Thus this exclusion is based on an actual applicable primary theorem AND a read, independently checked proof. It does not rely on the unavailable Feng article, its references, or a search excerpt authenticating Ma.

## Strongest contrary assessment
For a positive qualification case, the author's ratio argument closes the real k>1 issue uniformly and repairs the invalid shortcut (t^2-b)^((p-1)/2) in {1,-1}, which only follows over F_p. The proof is correct and not disqualified merely for shortness or standard tools. It could be an independently found alternate exposition of the nonsquare lemma.

Against exclusion, one might ask whether Ma only proves existence of a, only treats k=1, assumes gcd(k,r)=1, or proves only one of the two permutation maps. The actual theorem and complete proof exclude all four objections: a is universally constrained as here, Lemma 3.1 covers positive arbitrary k, no such gcd restriction occurs in this subsection, and their CPP definition requires both maps, with the first handled by the gcd and the second by the norm reduction. The original 2015 Wu final body and the later 2019 extension remain unread, but cannot undo the authenticated 2015 exact public theorem. No new theorem, helper, parameter, alternative proof, normalization or formalization receives discovery credit for this family.
