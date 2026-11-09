# Ordinary proof attempts and exact gaps

These are discovery notes, not acceptance certificates. Credit is zero throughout. All sums below are symbolic ordinary arguments; no mathematical enumeration, solver, numerical evaluation, Lean execution or child task was run.

## 357167: complete source-to-recurrence bridge; exclude

The source defines signed permutations as words selecting exactly one of i,-i for each i in [n], with pinnacles the values at internal strict local maxima. Its Theorem 3.12 counts the set of attainable pinnacle sets, not the permutations attaining them. Its proof chooses a positive pinnacle subset P of size j, then an admissible negative subset on the remaining n-j labels, using Theorem 3.9 and Proposition 3.11. The resulting count is
S(n,h)=sum(j=0..h) binom(n,j) binom(n-1-j,h-j), h=floor((n-1)/2).
We read the complete Theorem 3.12 proof, its surrounding semantic explanation, the printed Table 1 and Conjecture 5.1. No table is treated as proof.

First route: a direct bijection between signed pinnacle sets and objects satisfying the T recursion would require controlling how inserting the largest absolute label changes admissibility. The source's characterization permits changes in the negative part, so a naive insertion bijection is not justified. We replaced this incomplete mechanism with an exact algebraic bridge, valid for every n, not a finite table.

Define c(n,k)=[z^k](1+2z)^n/(1+z) in Q[[z]]. For k<n,
S(n,k)=[z^k] sum(j=0..n) binom(n,j) z^j (1+z)^(n-1-j)
       =[z^k](1+2z)^n/(1+z).
The j=n term has valuation n and cannot affect k<n. Thus the use of the formal inverse of 1+z introduces no issue with the finite binomial sum.
Now c(n,0)=1 and
c(n,n)=sum(j=0..n) binom(n,j)2^j(-1)^(n-j)=(2-1)^n=1.
Also multiplication by 1+2z gives
c(n,k)=c(n-1,k)+2c(n-1,k-1) for 0<k<n.
Induction on n proves c(n,k)=T(n,k) for every 0<=k<=n. For n>=2, h<n, so Theorem 3.12 gives precisely the assigned equality. At n=1, both sides are 1: the only attainable pinnacle set is empty and T(1,0)=1.

This is a complete reduction to an already proved counting theorem and the binomial theorem. Exclusion is based on that complete bridge, not ease or family resemblance. No residual mathematical lemma remains in the bridge. A new formalization of it would earn zero discovery credit. Latest journal/correction coverage was not completed; that limitation cannot turn this complete old source bridge into novelty.

## 368847: exact later public proof, plus independently reconstructed bridge; exclude

Crucial semantic distinction: phi is an ordered SET partition of [n] into odd-sized nonempty blocks, not an integer composition. The source's Remark 12.2 gives mu_(2r+2)=(-1)^r Cat_r. Conjecture 12.7 is the exact assigned endpoint. The source also cites Zhao-Lin-Zang arXiv:2507.20965. We read the companion's definition, Conjecture 1.1, Remark 1.2, Lemma 5.1 and complete Section 5 proof. Remark 1.2 explicitly identifies the Eulerian-number form with the signed tangent-number form. This is an actual exact proof body, not an abstract-only resolution claim.

First mechanism: ordinary composition generating functions would use z/(1-4z^2). That ignores labelled block choices and is semantically wrong. We discarded it before making any claim. The correct exponential generating function for one odd block weighted by 2^(size-1) is B(z)=sinh(2z)/2. An ordered list of k such blocks has EGF B(z)^k: the coefficient multiplied by n! is exactly the multinomial sum over ordered disjoint blocks covering [n]. For odd n the number k of odd blocks is odd. Thus the complete left side's EGF is
F(B(z)), F(u)=sum(r>=0)(-1)^r Cat_r u^(2r+1).
Catalan's equation implies F(u)+u F(u)^2=u. Uniqueness in u Q[[u]] is coefficientwise. With u=sinh(2z)/2, tanh(z) solves this equation, since sinh(2z)=2sinh(z)cosh(z) and cosh(z)^2-sinh(z)^2=1. Hence F(B(z))=tanh(z).
For A_n(t)=sum_k E(n,k)t^k (A_0=1), the Eulerian EGF is (1-t)/(exp((t-1)z)-t). At t=-1 it is 2/(1+exp(-2z))=1+tanh(z). Its positive odd coefficients therefore agree exactly with the left side. This proves the full assigned identity, with all labelled-set and sign bridges explicit. It is also precisely the mechanism in the already public companion proof, so no credit.

Latest arXiv source metadata: original v1 2025-06-15, v2 2025-07-21, v3 2025-09-27; older versions fetched, but not read in full. Companion submitted 2025-07-28, before this work. Search locates European Journal of Combinatorics 132 (2026), 104283; publisher final full proof/corrections not read, so no exhaustive version audit is claimed. An already read complete earlier exact proof suffices to reject novelty.

## 359028: determinant mechanism pursued to the exact old endpoint; exclude

The matrix and product in the assigned record coincide literally with source Conjecture 1. The same source then proves it in Theorem 4.1. We read Theorem 3.1's condensation argument, Corollary 3.2, and the complete constant-term proof of Theorem 4.1. The attempted direct condensation on the original Toeplitz-minus-Hankel matrix has shifted minors outside the one displayed family; treating it as a closed one-parameter recurrence would be a gap.

The successful old mechanism introduces
B(n,m,x)[i,j]=binom(x+m+2i,i-j+m)-binom(x+m+2i,i-j+m-1).
Theorem 3.1 evaluates D_n(a,b) with entries binom(2i+2a,i-j+a-b)-binom(2i+2a,i-j+a-b-1). Substituting a=(x+m)/2,b=(x-m)/2 gives exactly B and exactly the assigned product (Corollary 3.2).
For completeness the bridge to T is not an analogy: expressing each row as a constant term, using the alternating Vandermonde determinant and averaging over permutations of the row variables yields, for BOTH T and B, the same expression
(1/n!) CT_(t_0,...,t_(n-1)) [ product_i ((1+t_i)^(x+m)(t_i-1)t_i^(-x-2n+1)) product_(i<j) (t_i-t_j)^2(1-t_it_j) ].
For T the alternating factor comes from t_i^j-t_i^(-j-1); for B it comes from powers of 2+t_i+t_i^(-1). Their pairwise differences factor as (t_j-t_i)(1-1/(t_it_j)); after averaging, the same squared Vandermonde and monomial powers result. Thus det T=det B, followed by Corollary 3.2's identical product. This is the exact full source bridge. At singular written rational factors the statement requires the usual polynomial/rational-identity cancellation interpretation, not a new refutation by division by zero.

Source v1 July 4 2023, v2 July 10, v3 September 9. Older versions fetched, not fully read. Journal metadata is A case study in determinant evaluations, SLC 89 B89a (2023). The independently searched ETH journal PDF URL returned 404; not retried. Full final journal body and correction audit remain unavailable here. The read arXiv proof already excludes novelty. No holonomic package or computation from the paper was executed.

## 375978: full finite-set refutation of transcribed endpoint only; zero

Source Conjecture 6.3 says |S^2|<=3|S|-4, whereas the assigned record says -3. Work in the explicit group Z semidirect Z with
(x,y)(u,v)=(x+(-1)^y u,y+v).
Associativity follows because y -> (-1)^y is an automorphism action on Z; identity (0,0), inverse (-(-1)^y x,-y). It is torsion-free: if a positive power of (x,y) is identity its second coordinate forces y=0, then its first coordinate forces x=0.
Let e=(0,0), a=(0,1), b=(1,1), S={e,a,b}. The complete product set is
{(0,0),(0,1),(1,1),(0,2),(-1,2),(1,2)}.
Indeed a^2=b^2=(0,2), ab=(-1,2), ba=(1,2), and identity products give the first three. These six pairs are distinct; ab != ba. Thus |S|=3, |S^2|=6=3|S|-3, and <S> is nonabelian. This answers the literal erroneous bound, but does not meet the actual source bound 5. It is explicitly excluded as a transcription correction, not a significant solution of intended Conjecture 6.3. The source itself uses this semidirect-product family in Example 6.2 without e. No dormant Pi request.

## 360388: complete reduction to source's own locality theorem; zero

We read Theorem 1.1 and its precise topology/non-one-dimensional definitions, Reformulation 1, and the complete equivalence argument. Theorem 1.1 already asserts continuity of critical probability on the same class. The displayed assigned criterion is Reformulation 1 of that theorem, not the still-open unsprinkled continuity problem.
Assume the criterion false for fixed d,epsilon,delta. Choose counterexamples G_r,p_r with connection to distance r at least delta but no infinite cluster at p_r+epsilon. If p_r+epsilon>=1 the conclusion is automatic (the paper defines probabilities at p>1 as at 1), so counterexamples have p_r+epsilon<=1. Compactness of the degree-d non-one-dimensional transitive class supplies a locally convergent subsequence and p_r -> p. For any fixed R, finite-radius continuity and monotonicity yield P_p^G(o<->S_R)>=delta; letting R grow gives theta_G(p)>=delta, so p_c(G)<=p. Meanwhile failure of percolation implies p_c(G_r)>=p_r+epsilon. Continuity of p_c gives p_c(G)>=p+epsilon, a contradiction. This is the source's complete equivalence bridge. The long multiscale proof of its locality theorem was NOT fully reviewed here; we rely only for rejection on its explicit already published exact result and read bridge, not claim an independent new theorem.

## Other exact endpoints: failed routes and missing lemmas

359199: source Definition 6.7 requires NONZERO polynomials with ZERO constant term; record omits those restrictions. Allowing zero makes the all-zero monochromatic realization trivial, but this is a scope correction, zero credit. With intended scope, coloring by degree/parity does not supply one fixed n defeating all d. Missing uniform finite-color obstruction. Integer Hindman theorem in current OpenAI catalogue is not automatically a polynomial zero-constant-term result; no such transfer is claimed.
359203: a finite graph cannot refute a conditional all-algorithms lower bound. Source Conjecture 47 and its following discussion require a SAT reduction preserving the sharp pathwidth constant or a uniformly faster algorithm. No such reduction/algorithm obtained. The record's opening misdescription of SETH is not a mathematical solution.
359276: a facet height argument suggests negative-height vanishing via vector-partition reciprocity, but needs an exact non-unimodular chamber-extension reciprocity theorem on the requisite strip and lattice cosets. External-chamber negative-binomial theorem covers fewer chambers. The fetched HTML omits the advertised later semi-external sections; do not invent the missing definition or claim the conjecture proved. Journal/full-source hold.
359643: equal-rank cyclic windows imply density necessity by double-counting windows. Sufficiency needs a simultaneous exchange ordering when gcd(rank,ground-size)>1; source's paving and coprime cases do not establish arbitrary matroids. No counterexample in hand; park.
360806: source Conjecture 5.12 is coefficientwise h* monotonicity. Proposition 5.13 only gives top intersection-number monotonicity. Increasing the sum of coefficients cannot prove every coefficient increases; missing a coefficientwise effective decomposition of Snapper series. No exact object computed.
361031: source Conjecture 1, examples 9-10 read. Positive trace/eigenvalue conditions for three holonomies prove the supplied sufficient cases, not gauge-class necessity for every web. A single positive web is not an all-web counterexample. Missing complete characterization or an assignment with certified positivity of every web outside the classes.
372758: fixed assignment was metadata-tagged as an accepted-family duplicate, but no complete exact previous-result bridge was found in the permitted bounded history/ledger check; do not elevate tag to proved exclusion. Source Section 5 distinguishes L-D positivity from ordered spectral sums and defines L,D; no exact spectral counterexample or dominance proof produced. Park with duplicate/source hold, not a new credited variant.
368748: source Conjecture 1.6 inspected with Theorems 1.7/1.8. The proven p^(floor(e/f)) and p^(e-(f-1)(q-2)) divisibility are weaker than p^(e+1-f). Residual-code induction requires a stronger uniform weight-divisibility lemma; a small code not meeting the Griesmer equality cannot refute the statement. No construction or theorem closing that gap.
374767: source Conjecture 2 and its following four-edge-support discussion inspected. Cubic inversion does not reconstruct all embedded forest counts. Missing injectivity of the universal support-count-to-moment transformation in every degree, or a pair with certified equality of the FULL two spectra. No tree enumeration run.
371208: source equivalence compares permutations of the same length, so length-dependent statistics are not a new class. First prime-power nontrivial degree is not ruled out by propagation at non-prime-powers or finite checks through six. Missing all-degree classification or a complete bicompatible construction outside the four classes. No SAT run.
363661: source Conjecture 11 explicitly leaves criteria unspecified. The product of two existing annihilators is a common annihilator, but this says nothing about finding them by the specified procedure or for which graph families it terminates. Missing exact family criterion plus closure/termination proof; not a well-defined universal finite-certificate target as transcribed.
372608: source Conjecture 1.1 and surrounding special cases inspected. Maximal independent sets need not dominate outward in two steps while meeting n/2. Missing a size-reducing exchange preserving two-step reachability for all sourceless digraphs. Park flagship; no claimed route from the tournament/split cases.
373504: source's exact final conjectural congruence and 72-class modulus statement inspected. Missing a modular-form identity with correct level, weight, cusp holomorphy and applicable finite bound, or an exact counterexample. A generic appeal to Sturm checking without these ingredients is not a full proof; no coefficient search executed.
374164: source Conjecture 3.6 inspected. Mod-4 information in Theorem 3.7 cannot force the sign of an even difference. Missing a weight-preserving injection with strict surplus for all n>27 or a signed q-series positive expansion. No partition enumeration run.
374793: source Conjecture 5.3 and Remark 5.4 inspected. Exhibited palindromic factors supply an upper bound, not a universal lower bound across every factor length. Missing the exact first-difference/minimizer classification; finite samples cannot prove the infinite constant. Park.

## Formalization routing

No source-qualified NEW full ordinary endpoint survives. Therefore no CANDIDATE.md and no Pi task were created. Excluded known identities or the bound-transcription refutation are not routed to formalization. Any future candidate needs a separate root-authorized semantic endpoint, definitions, bridges, independent review and full replay; none is claimed here.
