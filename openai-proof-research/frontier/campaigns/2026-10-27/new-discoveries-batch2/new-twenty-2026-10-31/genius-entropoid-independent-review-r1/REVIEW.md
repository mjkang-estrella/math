# Independent review: 345451 and 350365

Review date: 2026-11-07 UTC. GPT-6.1 Sol, high effort/default speed; no children. This is an ordinary mathematical/source review, not acceptance or formal validation. Credit 0; root-provided 52/60 beyond 39 remains unchanged. Recommendations are ID-specific HOLDs.

## 345451 — Genius linearity

**Recommendation: HOLD for endpoint wording, substantive qualification and bounded prior completion. Ordinary all-p argument PASS with the explicit affine interpretation below.** No all-p mathematical defect was found. The strongest routine-corollary objection is now fully bridged to an actually read classical theorem; root should adjudicate that objection before assigning formal work. Neither the open database label nor the absence of a retrieved proof establishes novelty.

### Literal source and parameters

The exact raw record and result for 345451 were read. Federbush, *The Genius Conjectures (via Bell Polynomials)*, arXiv:2002.03814v1 (submitted 4 February 2020; manuscript heading February 11), six-page body read completely. Equations (1),(2), Theorem 1.1 and Conjecture 1 agree with the record: positive integer p; u1=F1=1; u2,...,up and d1,...,dp variable; D=exp(sum d_j x^j); D_p=[x^p]D=0; coefficient identity as a polynomial in y. These are identities on the constraint locus, not identities for unconstrained independent d_p. Source Theorem 3.1 is the same uniqueness statement after multiplication by p!, and equation (6) is Bell addition. Neither states linearity. This review does not claim Conjecture 2 or the Awesome conjecture.

Use any commutative Q-algebra R and the x-adic formal series ring. A universal model is Q[d1,...,dp,u2,...,up]/(D_p). Since D_p=d_p plus a polynomial in earlier d's, this particular universal quotient is actually a polynomial ring after eliminating d_p. Nonetheless the proof below works after every specialization, including Q-algebras with zero divisors. Only nonzero rational scalars are inverted. No d_j, u_j or arbitrary nonzero ring element is divided by.

### All-p audit, independently checked

Fix p>=1. Write D_j=[x^j]D, D_0=1, and

A(x)=sum_{0<=j<p} p D_j x^j/(p-j),   z(x)=x A(x)^(-1/p).

All denominators p-j are positive integers. A(0)=1, so its rational binomial power is well-defined coefficientwise. Binomial identities and termwise differentiation are rational polynomial identities, valid over R; the chain rule yields the stated derivatives even with zero divisors. z=x+O(x^2) has a unique two-sided compositional inverse X=z+O(z^2): at each recursive degree the new coefficient has coefficient 1, so this construction divides by no ring element. X and A depend only on d and p.

Differentiating z^(-p)=x^(-p)A gives

z^(-p-1)z'=x^(-p-1)(A-xA'/p)
             =x^(-p-1)sum_{j<p}D_j x^j.

This is an exact Laurent identity. The difference between x^(-p-1)D and its right side has valuation at least 0, precisely because D_p=0; terms j>p give exponents j-p-1>=0. Without this constraint there would be a D_p/x obstruction. Multiplying by any H in R[[x]] preserves regularity and hence cannot alter residue. In particular take H=exp(yU), U=sum_{1<=k<=p}u_k x^k. This series can be regarded in R[y][[x]]: for any fixed x-degree only finitely many powers U^m contribute (m<=degree). Thus all y-coefficients and the residues used below are finite in the relevant degree; no convergence, infinite unbounded negative support, or unsupported exchange of sums occurs.

Residue invariance under z=xv with v(0)=1 follows on a Laurent monomial t^k. For k!=-1, z^k z'=(z^(k+1))'/(k+1) and every Laurent derivative has zero residue. For k=-1, z'/z=1/x+v'/v and v'/v is regular. A bounded-below Laurent series reduces to finitely many potentially contributing terms; positive valuation of z ensures composition is locally finite. These facts prove the substitution rule over R, not just over a field.

Let V(z)=U(X(z)) and F_i=[z^i]V for i<=p. Apply that rule to exp(yV(z))z^(-p-1), whose substitution is exp(yU(x))z(x)^(-p-1)z'(x). It follows that

[x^p]D(x)exp(yU(x))
 =Res_x exp(yU(x))z(x)^(-p-1)z'(x)
 =Res_z exp(yV(z))z^(-p-1)
 =[z^p]exp(y sum_{i=1}^p F_i z^i).

Deleting V's terms of degree >p changes the exponential only in degree >p. Also F1=u1=1 and

F_i=sum_{k=1}^i u_k [z^i]X(z)^k.

The coefficients contain only d,p, so no hidden u-dependence enters the change of variable.

Uniqueness is independent of upstream truth. For i=2,...,p set m=p-i+1. In [y^m z^p]exp(y sum F_j z^j), an index exceeding i would force total degree >p, while an index i forces all other m-1 indices to be 1. Its contribution is m/m! F_i=F_i/(p-i)!, including i=p (m=1). All other terms involve only F_1,...,F_{i-1}. The inverse factorial is a unit, so triangular recursion uniquely fixes F_i. The y^p term agrees because F1=1 and D0=1; y^0 agrees because Dp=0. Existence was already proved for every y coefficient. For p=1, D1=0 and both sides have x-coefficient y; there are no F_i with i>=2. This also checks the endpoint case without division by p-1.

### Linearity versus affine: endpoint must say what it means

The formula is homogeneous linear in the full list (u1,...,up) before restricting to u1=1; its restriction is affine in the genuinely free variables u2,...,up, of total u-degree <=1. The source explicitly lists u1=1 and uses the unqualified word linear, without defining a vector-space domain for the free variables. Therefore a formal endpoint should state the displayed coefficient formula or total degree <=1, not silently assert preservation of zero in the free variables.

This is a substantive wording distinction, not a defect in the residue argument. At p=2 the constraint is d2=-d1^2/2. Direct coefficient comparison gives F2=u2+d1. For d1=1,d2=-1/2 this does not vanish at u2=0. Thus strict homogeneous linearity in u2,...,up alone is false. Source usage of the full list including the fixed u1 supports the affine reading, but does not license pretending the two meanings coincide. Literal-semantic gate: qualified PASS for affine/full-list meaning, HOLD for an unspecified Lean endpoint; FAIL for strict homogeneous-free-variable meaning.

### Exact prior bridges and substantive objection

Current primary arXiv abstract page was fetched at 2026-11-07T05:38:52Z: only v1 is listed, no journal reference or correction shown. This verifies the current page's version list, not worldwide publication absence. The cached PDF is the same v1 text. Search located the later companion arXiv:2012.10927; current page lists v8, 8 May 2022. Its acquired PDF is v8. Relevant Theorem 3.1 and Appendices A,B,C were read as inventoried (not the whole 18-page proof).

The companion's Theorems A.1–A.4 transport Chapman's weighted Stirling identity into a degree bound for [j^k n^(-h)]log of normalized matching coefficients. Theorem A.2 has g>=2, 0<=w<=g-2, weighted ordered partitions, and evaluations from Stirling polynomials P_w(sum c). Appendix C proves the integer-set formulation and accounts for ordered/unordered r! factors. This controls the degree of a logarithmic coefficient; it does not exhibit the d-dependent substitution or the u-linear coefficients of F_i. The companion Lemma B.1 obtains an O(1/j) correction only through s<=27 by Maple, expressly leaving the unrestricted Genius consequence conjectural. Thus no all-p Genius linearity resolution follows merely by citing this companion or Chapman. A full Chapman-to-F transport has not been recovered, and no exclusion on that basis is claimed. The companion additionally names mp_arc 22-22, *Extension of Range of Validity of Pernici's 1/n Conjecture* (2022), not acquired here; its title alone cannot resolve or exclude Genius.

A stronger, completed routine objection does exist from classical Lagrange inversion. Gessel, *Lagrange Inversion*, arXiv:1609.05988 (2016), Section 1.1, Theorem 2.1.1, equation (2.1.7), and Theorem 4.1.1 with proof were actually read. In Gessel's inverse notation set g(t)=t/A(t)^(1/p), f=X, n=p, phi(t)=exp(yU(t)). Equation (2.1.7) gives

[z^p]phi(X(z))=Res_t phi(t)g'(t)/g(t)^(p+1).

Here g'(t)/g(t)^(p+1)=t^(-p-1)(A-tA'/p). The linear operator A -> A-tA'/p sends t^j to (1-j/p)t^j; its sole resonant coefficient through degree p is degree p. Consequently Dp=0 is exactly the compatibility condition for solving this operator equation through degree p, and the unique degree<p solution with constant 1 is the displayed A. Substitution into Gessel's formula proves the candidate identity; the triangular uniqueness and F_i formula above identify the source functions. This is a complete old-theorem-to-constraint-to-linearity bridge, not just a mention of residues. Gessel's source coefficient ring is an integral domain containing Q; apply it first to the universal quotient (which is such a domain by eliminating d_p), then specialize the resulting finite polynomial identities into arbitrary R. Alternatively the independent residue proof above gives the ring extension directly.

Gessel's equation (2.2.1), also read, gives the explicit version

F_i=sum_{k=1}^i (k/i) u_k [t^(i-k)] A(t)^(i/p).

Indeed X=z A(X)^(1/p), so insert R(t)=A(t)^(1/p), n=i into that formula. Each displayed coefficient uses finitely many d's. Thus the entire construction, including its linear dependence, reduces to solving a diagonal linear coefficient operator and applying an existing inversion formula. This is the strongest substantive routine-corollary objection. It is complete as a mathematical derivation; whether recognizing the resonant normal form is sufficient significance for this campaign is root's substantive decision, not evidence that an exact public Genius solution already exists. I recommend HOLD pending that decision rather than claim either worldwide novelty or an automatic exclusion from standard tools alone.

Current proof registries: bounded exact-ID/title/GitHub searches found no concrete matching current proof body. No current registry head or theorem body was acquired. No root README absence is used as clearance. Coverage remains incomplete; no novel-to-literature assertion.

## 350365 — Sylow generator formula

**Recommendation: HOLD. Explicit Definition-12-family mathematics PASS after the parameter repair below; literal conditional-entropic endpoint FAIL for this witness, hence literal fidelity HOLD. Named prior remains material.**

The exact raw record and result were read. Cached Gligoroski arXiv:2104.05598v1 (12 April 2021; manuscript April 13), selected actual Definitions 2,3,10–16; equations (13),(22),(28),(32),(59),(70) and surrounding safe-prime context were read. The exact six-leaf term is g*(g*(g*((g*g)*g))); its placement was visually verified on page 18. Definition 10 quantifies over all binary bracketings and degrees, not merely one fixed associating convention or a list of computed powers. The context is p=2q+1 a safe prime, p>=11. Definition 16 calls a subquasigroup Sylow q when its cardinality is the full q-primary factor, here q^2.

### Model, generator and cardinality proof

In the explicit parameter choice a3=b2=0,a8=b7=1, equation (22) is (a,b)*(c,d)=(bc,ad). Equation (70)'s proof explicitly uses that model. Its maximal domain from (32) is H=(F_p^*)^2. Closure is immediate. For fixed c=(c1,c2), c*x=d has unique solution x=(d1/c2,d2/c1), and x*c=d has unique solution x=(d2/c2,d1/c1). Thus H is a quasigroup, not just a closed magma.

For p=11,q=5 let h=(2,1). Eleven and five are primes and 11=2*5+1. In F11, 2^5=32=-1 and 2^2=4!=1. Since its order divides 10, exclusion of the proper divisors 1,2,5 proves order 10, so its powers exhaust the ten nonzero elements. This uses group order, not programmed enumeration.

For each n>=2, every pair (2^i,2^j) with i,j>=1,i+j=n is realizable by a bracketed n-fold h. Base n=2: h*h=(2,2). If a legal term has exponent pair (i,j), prefixing h yields (j,i+1), suffixing h yields (j+1,i). As i runs 1,...,n-1, the first exponents in these two constructions cover respectively 1,...,n-1 and 2,...,n. Both preserve positive exponents and give total n+1. This proves the universal induction. Choose positive representatives i,j in 1,...,10 for any two nonzero field elements; the induction supplies a term evaluating to their pair. All terms remain in H by closure. Hence h generates all 100 elements in the exact Definition 10 sense.

For general h=(a,b) the successive values along the literal expression are

h*h=(ab,ab);
(h*h)*h=(a^2 b,a b^2);
h*((h*h)*h)=(a^2 b^2,a^2 b^2);
h*(h*((h*h)*h))=(a^2 b^3,a^3 b^2);
h*(h*(h*((h*h)*h)))=((ab)^3,(ab)^3).

The leaf counts are 2,3,4,5,6 respectively; no associativity was used. At h=(2,1) the last is (8,8). For diagonal elements (r,r)*(s,s)=(rs,rs), so structural induction on any binary tree gives every n-leaf power equal to (8^n,8^n). It has exactly ten values, since 8=2^3 and gcd(3,10)=1, so 8 has order 10. In particular it cannot generate ANY 25-element subquasigroup; this is a cardinality invariant over all bracketings, not failure of one enumerated power sequence.

The desired 25-element object is nonvacuous. The subgroup K=<4> of F11* has order 5 because 4=2^2, so K is exactly QR(11). K^2 is closed and all the division formulas above stay in K. It is a quasigroup with 25 elements. Apply the same positive-exponent induction with 4 in place of 2: (4,1) generates K^2. This verifies existence without invoking questionable source divisibility claims.

### Parameter repair and literal axiom failure

The author relied on equation (70)'s model, but source lines 405–407 say that subsequently a3!=0 and b2!=0 are assumed. Thus the zero-parameter witness alone leaves a genuine scope objection. It is repairable inside the explicit family: choose a3=a8=b2=b7=1 and define T(x1,x2)=(x1+1,x2+1). Then (22) becomes

x*y=(x2+y1+x2 y1, x1+y2+x1 y2),
T(x*y)=(T(x)_2 T(y)_1,T(x)_1 T(y)_2).

T is bijective from (F11\{-1})^2 onto H, and from the full additive group defined by (28) onto the usual additive F11^2. Thus the explicit finite-ringoid conditions and every bracketed power transport. Take g=T^(-1)(2,1)=(1,0). It generates the maximal 100-element quasigroup in the source's nonzero-parameter family. The literal six-leaf term is T^(-1)(8,8)=(7,7); it has ten generated elements. The Sylow object T^(-1)(K^2) has 25 elements, generated by T^(-1)(4,1)=(3,0). All claimed maximal-domain exclusions hold because none of the transported coordinates is -1. This repairs the additional nonzero-parameter restriction, with no change to the conjectured bracket.

More generally the author's proposed T=(b7(x1+a3/a8),a8(x2+b2/b7)) is valid. Multiplying (22)'s first coordinate plus a3/a8 by b7 gives (a8 x2+a8 b2/b7)(b7 y1+b7 a3/a8), and the second coordinate plus b2/b7 times a8 gives the reverse component product. This checks the transport, rather than assuming it.

It does NOT repair literal Definition 2. That definition asserts x*y=z*w implies x*z=y*w. In H set x=z=(1,1),y=w=(2,1). The antecedent is true by reflexivity, while x*z=(1,1) and y*w=(2,2) are unequal. Therefore this model fails the literal conditional law. T transfers this failure to the nonzero-parameter model too. The standard medial identity (x*y)*(z*w)=(x*z)*(y*w) DOES hold: its coordinates on (a,b),(c,d),(e,f),(g,h) are (adfg,bceh) on both sides. It is not the conditional identity printed in Definition 2 and Design criterion 1. Noncommutativity and nonassociativity hold explicitly: with e=(1,1),h=(2,1), e*h=h whereas h*e=(1,2); also (h*e)*e=h whereas h*(e*e)=(1,2). Nonlinearity and distributivity follow from the displayed bilinear model, transported along the additive affine bijection.

Definition 14 names the explicit equation-(22) ringoid an entropoid, whereas Definition 11 requires the failed conditional criterion. Both facts must be retained. The counterexample refutes Conjecture 2 on the concrete family that the source itself constructs and uses, including its nonzero-parameter restriction. It has NOT exhibited a witness satisfying every literal conditional axiom simultaneously. A formal negation of the latter endpoint would be unsound. No vacuous argument from inconsistent definitions, and no silent replacement of conditional by medial, is acceptable. Source semantic adjudication is required before any literal MathDB certificate is proposed.

### Named material priors and exact mismatch

Panny, ePrint 2021/583, and Gligoroski's rebuttal ePrint 2021/896 remain body-unread. The author recorded 403 for both exact PDF URLs. No direct retry, mirror/cache/proxy variant or TLS bypass was made. Search batch 2 unsolicited indexed excerpts from those URLs; these are logged only as search excerpts, not independently fetched full bodies or permission to retry. They identify the rebuttal's acknowledgement of the concrete-instance cryptanalysis; no exact Sylow-formula conclusion was cleared there.

A concretely found independent author-hosted primary document was legally acquired: https://yx7.cc/docs/misc/entropoid_mathcrypt_slides.pdf, Lorenz Panny, MathCrypt 15 August 2021. Entire extracted text, including overlays, was read; structure theorem slide visually checked. It uses standard medial entropic quasigroups, states the Murdoch/Toyoda/Bruck abelian-group representation with commuting automorphisms, and describes the concrete abelian group as (F_p*)^2. These slides predate this candidate and are material.

Complete concrete bridge to that normal form: put the ordinary componentwise abelian group law on H, let sigma swap the two coordinates, tau be the identity, and c=(1,1). Then x*y=sigma(x)·y. Sigma and tau commute and are automorphisms. Every bracket-tree exponent is a polynomial in sigma, and the six-leaf term reduces by sigma^2=1 to 3(1+sigma), so it sends (a,b) to ((ab)^3,(ab)^3). Its image is fixed by sigma; on the fixed subgroup the operation is the ordinary diagonal group product. The generator induction above proves h=(2,1) is a full magma generator; the fixed subgroup has only ten elements at p=11; the transported q-primary object has 25. This supplies the exact model/normal-form-to-formula obstruction rather than claiming that a cryptanalytic reduction automatically refutes Sylow generation.

However, the acquired slides do not state this six-leaf formula or this counterexample. The concrete group identification is stated, not the detailed affine transport from equation (22). The bridge just given contains independent reasoning. The unread paper/rebuttal may already contain an equally direct or exact result; that material comparison is unresolved. Therefore neither exact historical duplication nor worldwide novelty nor a blanket family exclusion is established. Adjacent IDs 350366–350368 were read only through the permitted historical-family inventory and do not decide this ID's gates. Standard tools, small p, and size of the witness are not exclusion reasons.

## Operational record and handback

First and second commands were the exact requested bootstrap and before verifier. The first receipt was preserved. Before check: 60 inputs, zero mismatches. First substantive source reading was job source_read_01 through the supplied run.py. No guessed TASK.md or local AGENTS path was used; bootstrap printed TASK.txt. Bootstrap console initially truncated a small part of the campaign AGENTS; that complete file was read through source_read_01. Initial helper inspection and the PDF skill read were ordinary direct shell reads, outside run.py; these were instruction/harness reads, not substantive source reads, and no resource attestation is invented for them. No harness was recreated.

Source/read/access/search/resource inventories accompany this report. Acquisition is not synonymous with reading. Several large console outputs were truncated; focused jobs and final_scope_read_11 recovered the entire Genius body and all passages used in the conclusions. Entropoid tables/appendix code and the whole companion/Gessel proofs were not read. The wrong Panny overlay page selected for rendering was page 15 (structure plus power form), which is still relevant and was actually inspected; page 16's text was read, not visually inspected. No generated paper, Lean, compiler, solver, mathematical program/enumeration, Pi, API, delegate, git, external mutation, browser or install occurred. All mathematical verification above is ordinary reasoning and hand algebra.

Three search batches (12 query strings); six distinct direct GET attempts, five successes and one TLS failure. Of those GETs, Genius used five (its abstract, companion abstract/PDF, Gessel PDF and failed Gessel slides), Entropoid one (independent Panny slides). Search-service internal HTTP counts, CPU, statuses and result-body hashes are unavailable; six is the direct acquisition count, not a fabricated service-inclusive count. No further searches or GETs. Failed TLS URL not retried. No denied ePrint GETs. Current registry heads and journal-wide searches remain incomplete. Access logs preserve UTC, status/final URL/hash/bytes on success and error on failure.

run.py enforces two-CPU affinity, 115s child CPU, 120s supervisor CPU, 6GiB AS, arena2, sampled process-group RSS guard, 130s supervisor deadline under outer timeout140 and communicates/reaps its child. Resource receipts are contemporary actual results, including zeros where sampling missed a short child. These are not aggregate CPU enforcement or cgroup evidence; writer RSS is separately unmeasured, service CPU unknown. One acquisition returned a session after the exec yield and its session id was not printed by that call; acquire_read_06 subsequently read its completed exit-0 receipt/output. The other acquisition session was explicitly reaped via write_stdin. No live job is intentionally left.

No dormant Pi brief is issued: neither candidate's unresolved source/substantive/prior gates justify dispatch. Root alone adjudicates acceptance, and the review supplies evidence rather than doing root integration. The after verifier and final hash manifest seal this lane. Manifest explicitly excludes itself and the final verification job's own output/receipt (a finite self-reference boundary); all preceding receipt JSONs are hashed, including the manifest-generation receipt once it exists. See verification output for actual hash equality. No protected body/path was read, hashed, searched, globbed or polled; only own lane and the authorized completed source inventory were accessed.
