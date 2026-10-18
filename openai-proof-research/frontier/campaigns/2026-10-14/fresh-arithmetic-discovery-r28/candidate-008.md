# T008M: compressed matrices for weight-truncated Grothendieck–Teichmüller Lie algebras

Myeongjin Kang. No affiliation. Original prose CC BY4.0. Author-side proof; no independent proof, contribution, or acceptance verdict.

The scope in scope-008.md is unchanged. Let rho>1 solve rho³=rho+1. For every characteristic-zero field F, put g_N=W_F/W_{>N}. We prove absolute c,C,N0 such that

    c rho^(N/2)/sqrt(N) ≤ mu_F(g_N) ≤ mu_nil,F(g_N) ≤ C rho^(N/2)

for N≥N0. Thus both Nth-root limits equal sqrt(rho). The representation is explicit in any homogeneous free-generator system supplied by the stipulated source; no canonical generator choice or efficient conversion from Ihara coordinates is asserted.

## 1. Source interface and associative reduction

The pinned family008 introduction, Theorem thm:main, identifies the rational Ihara Lie algebra W with the free graded Lie algebra L on one letter e_d of weight d for each odd d≥3. It identifies weight completions as well. The same source's Lemma lem:lie-lattice states the weighted Hall/PBW embedding in the free associative algebra. We use these statements, not their proofs as new contributions. Scalar extension gives the identical interface over F.

Let A=F<e_3,e_5,e_7,...>. A word has the sum of its letter weights, and the empty word has weight0. There are finitely many words in each bounded weight. Let A_N=A/(words of weight>N). The image of L in A is graded and injective, so L/(L intersect A_{>N}) embeds in A_N. Hence a faithful representation of A_N restricts to one of g_N.

## 2. A block detecting the top weight

Fix integers T≥1 and 1≤m≤T, and set b=T-m. Define a finite state set consisting of two disjoint parts:

    P_m = {(a,r): a a word, r≥1, wt(a)+r≤m},
    Q_b = {(v,s): v a word, s≥0, wt(v)+s≤b}.

Give P_m-state(a,r) the integer level -wt(a)-r, and Q_b-state(v,s) the level wt(v)+s. Order all states by increasing level, breaking ties arbitrarily. For every odd d≥3 define a matrix X_d whose rows and columns are indexed by these states. An entry is1 precisely for one of the following transitions, and0 otherwise:

1. Prefix deletion: P(e_d a,r) -> P(a,r).
2. Crossing: P(empty,r) -> Q(empty,s) when r+s=d.
3. Suffix creation: Q(v,s) -> Q(v e_d,s), provided the target is in Q_b.

All transitions increase the level by d. The three types have disjoint source/target configurations, so no entry accumulates multiplicities. Each X_d is strictly upper triangular and has entries0 or1. If d>T it is zero.

The universal property of A defines an algebra homomorphism Phi_T:A->Mat(D_T,F), e_d->X_d. We use ordinary matrix multiplication; the(i,j) entry of a product is a sum over paths read from row-state i to column-state j in the displayed word order. Since every level is between -m and b, any word of weight>T maps to zero. Thus Phi_T factors through A_T.

**Top-weight detection lemma.** Phi_T is injective on the homogeneous word space A[T].

**Proof.** If this word space is zero the assertion is immediate. Otherwise, for a word w of weight T, take its first letter at which accumulated weight reaches or exceeds m. There is a unique decomposition

    w=a e_d v,  wt(a)<m≤wt(a)+d.

Set r=m-wt(a)≥1 and s=b-wt(v)≥0. Since wt(w)=T, r+s=d. Both p=P(a,r) and q=Q(v,s) are states, at levels -m and b. The path which deletes a, crosses on e_d, and creates v has weight word w and goes from p to q. Conversely every path from p to q must delete all of a, cross exactly once when the prefix word is empty, and then create precisely v. The crossing letter is determined by r+s because there is only one generator in each allowed weight. Therefore this matrix entry is1 for w and0 for every other word. It extracts the coefficient of w from every element of A[T]. Distinct words have distinct extracting entries: equality of p,q fixes a,r,v,s and hence d,w. All coefficients are consequently detected. QED.

This proof includes crossings inside generators of arbitrarily large weight. Assuming that m lies between letters would be invalid. The integer gap markers are essential for this version of the construction.

## 3. Three caps give a faithful representation

For N≥3 take the direct sum of the blocks Phi_T for T=N,N-1,N-2. Use m=floor(T/2) when T≥2, and m=1 when T=1. All these homomorphisms annihilate words of weight>N, so they define an algebra homomorphism

    Phi:A_N -> direct sum_{T=N-2}^N Mat(D_T,F).

It is faithful. To see this first consider a nonzero homogeneous f of weight k≤N. Choose j≥0 such that T=k+3j belongs to {N-2,N-1,N}. Right multiplication by e_3^j is injective on the free associative word space, so f e_3^j≠0 has weight T. Top-weight detection implies Phi_T(f e_3^j)≠0, and hence Phi_T(f)≠0.

For a nonhomogeneous f, each homogeneous degree k in each block occupies only entries whose target level minus source level is k. Different k have disjoint sets of entries. Therefore cancellation between different weights is impossible. If all blocks of Phi(f) vanished then all blocks of every homogeneous component would vanish, contradicting the preceding paragraph. The constant component is covered too: multiply it by a suitable power of e_3 to reach one of the three caps. Thus Phi is an injective unital algebra homomorphism.

The block diagonal matrices of positive-weight elements are simultaneously strictly upper triangular, after concatenating the chosen state orders. Restricting along g_N -> A_N proves the required nilrepresentation. Everything is defined with integer0/1 generator entries, so this construction in fact works for the associative algebra over every field. Only the identification with W_F uses characteristic zero.

## 4. Dimension bound

Let a_j be the number of associative words of weight j. Its generating series is

    A(z)=1/(1-(z³+z⁵+...))=(1-z²)/(1-z²-z³).

Here a_0=1,a_1=a_2=0 and a_j=a_(j-2)+a_(j-3) for j≥3, using zero for negative subscripts. Induction and rho^j=rho^(j-2)+rho^(j-3) give a_j≤rho^j for all j≥0.

The two exact state counts are

    |P_m|=sum_{j=0}^{m-1}(m-j)a_j,
    |Q_b|=sum_{j=0}^b(b-j+1)a_j.

Consequently

    |P_m| ≤ rho^m * rho/(rho-1)²,
    |Q_b| ≤ rho^b * rho²/(rho-1)².

For T≥2, m=floor(T/2), b=ceil(T/2), so

    D_T ≤ K rho^(T/2), K=(rho+rho^(5/2))/(rho-1)².

For N≥4 all three caps have T≥2. Summing gives D≤C rho^(N/2), for example C=3K. The finite case N=3 can be absorbed by increasing C if desired. This is a uniform constant, independent of F,N, generator coordinates, and nilpotency class. Enumerating the finite state lists and the three types of transitions is a terminating exact matrix construction. No scalar-field root extraction or random specialization is needed.

## 5. Dimension lower bound and the limit

Write l_n=dim_F L[n], which is field-independent in characteristic zero. PBW gives

    A(z)=product_{n≥1}(1-z^n)^(-l_n).

Taking formal logarithms gives, with q_n=n[z^n]log A(z),

    q_n=sum_{d|n}d l_d,
    n l_n=sum_{d|n}mobius(d) q_(n/d).

These are the classical weighted Witt identities, not a new operation.

Let rho,alpha,conjugate(alpha) be the roots of t³-t-1. The cubic has exactly one real root: its two stationary values are negative, so both real turning points lie below zero. Its product of roots is1; hence |alpha|=rho^(-1/2)<1. The factorization

    1-z²-z³=(1-rho z)(1-alpha z)(1-conjugate(alpha)z)

yields

    q_n=rho^n+alpha^n+conjugate(alpha)^n-(1+(-1)^n).

Thus |q_n-rho^n|≤4. In the Möbius formula every proper divisor argument n/d is at most n/2 and there are at most n such terms, so

    n l_n ≥ rho^n - 4 - n(rho^(n/2)+4).

The subtracted terms are o(rho^n). Hence for all sufficiently large n,

    l_n ≥ rho^n/(2n).

Any faithful m-dimensional representation embeds g_N into Mat_m(F), so m²≥dim_F g_N≥l_N. Therefore

    mu_F(g_N) ≥ rho^(N/2)/sqrt(2N)

for sufficiently large N. Combined with the explicit upper bound and mu≤mu_nil, this proves the frozen inequalities with c=1/sqrt2. Taking Nth roots proves both limits. No classification of minimal representations, exact center formula, algebraic closure of F, or nilpotence of an arbitrary faithful representation is required. QED.

## 6. Claim limits

The proof does not determine the optimal polynomial factor between the two bounds, much less an exact leading constant. It does not claim that the matrices respect a canonical depth filtration or give an efficient conversion from the defining pentagon equations. It does not infer anything about finite-dimensional representations of the untruncated completed algebra beyond these finite quotients. The construction is elementary enough that equivalent prior art must be checked carefully; the author does not certify novelty or substantiality.

Source/primary attribution, prior-history limits and parent author-side assistance are recorded in source-and-credit.md. Exact reading limits are in reading-limits.md; formal-interfaces.md proposes support only and makes no formal-verification claim.
